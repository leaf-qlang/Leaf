#!/usr/bin/env python3
"""Generate the Unicode tables Leaf's lexer needs to normalize identifiers to NFC.

Like Rust, Leaf normalizes identifiers to Unicode Normalization Form C (NFC,
Unicode Standard Annex #15). This script reads the Unicode Character Database
and writes src/Compiler/Frontend/Lexer/UnicodeNormalizationData.idr with three
tables, each a string of ';'-separated entries of hexadecimal code points:

  * canonical combining classes: "first last class" for every range of code
    points with a nonzero canonical combining class;
  * full canonical decompositions: "codePoint decomposition..." for every code
    point whose canonical decomposition differs from itself, with the mappings
    applied recursively (Hangul syllables are decomposed algorithmically by the
    lexer and are left out);
  * primary composites: "first second composite" for every code point with a
    two-code-point canonical decomposition that is not excluded from
    composition (Full_Composition_Exclusion).

Usage:
  python3 tools/generate_unicode_normalization_data.py [UCD_DIRECTORY]

UCD_DIRECTORY defaults to /usr/share/unicode (Debian/Ubuntu package
unicode-data) and must contain UnicodeData.txt and
DerivedNormalizationProps.txt. The output depends on the Unicode version of
those files, which the generated module records. To regenerate the tables for
a specific version, download both files from
https://www.unicode.org/Public/<version>/ucd/ (for example 15.1.0) into a
directory and pass that directory.
"""

import os
import re
import sys

OUTPUT_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "..", "src", "Compiler", "Frontend", "Lexer", "UnicodeNormalizationData.idr")

HANGUL_SYLLABLE_FIRST = 0xAC00
HANGUL_SYLLABLE_LAST = 0xD7A3
ENTRIES_PER_LINE = 8


def read_unicode_data(ucd_directory):
    canonical_combining_classes = {}
    canonical_decomposition_mappings = {}
    with open(os.path.join(ucd_directory, "UnicodeData.txt"), encoding="utf-8") as unicode_data:
        range_first = None
        for line in unicode_data:
            fields = line.rstrip("\n").split(";")
            code_point = int(fields[0], 16)
            name = fields[1]
            combining_class = int(fields[3])
            decomposition = fields[5]
            if name.endswith(", First>"):
                range_first = code_point
                continue
            if name.endswith(", Last>"):
                covered = range(range_first, code_point + 1)
                range_first = None
            else:
                covered = [code_point]
            for covered_code_point in covered:
                if combining_class != 0:
                    canonical_combining_classes[covered_code_point] = combining_class
            # Compatibility mappings start with a <tag>; only canonical ones matter for NFC.
            if decomposition and not decomposition.startswith("<"):
                canonical_decomposition_mappings[code_point] = [int(part, 16) for part in decomposition.split()]
    return canonical_combining_classes, canonical_decomposition_mappings


def read_full_composition_exclusions(ucd_directory):
    excluded = set()
    pattern = re.compile(r"^([0-9A-F]+)(?:\.\.([0-9A-F]+))?\s*;\s*Full_Composition_Exclusion\b")
    with open(os.path.join(ucd_directory, "DerivedNormalizationProps.txt"), encoding="utf-8") as properties:
        for line in properties:
            match = pattern.match(line)
            if match:
                first = int(match.group(1), 16)
                last = int(match.group(2), 16) if match.group(2) else first
                excluded.update(range(first, last + 1))
    return excluded


def unicode_version(ucd_directory):
    with open(os.path.join(ucd_directory, "DerivedNormalizationProps.txt"), encoding="utf-8") as properties:
        match = re.search(r"DerivedNormalizationProps-([0-9.]+)\.txt", properties.readline())
    return match.group(1) if match else "unknown"


def full_decomposition(code_point, canonical_decomposition_mappings):
    mapping = canonical_decomposition_mappings.get(code_point)
    if mapping is None:
        return [code_point]
    expanded = []
    for mapped_code_point in mapping:
        expanded.extend(full_decomposition(mapped_code_point, canonical_decomposition_mappings))
    return expanded


def combining_class_ranges(canonical_combining_classes):
    ranges = []
    for code_point in sorted(canonical_combining_classes):
        combining_class = canonical_combining_classes[code_point]
        if ranges and ranges[-1][1] == code_point - 1 and ranges[-1][2] == combining_class:
            ranges[-1][1] = code_point
        else:
            ranges.append([code_point, code_point, combining_class])
    return ranges


def hexadecimal(value):
    return "%04X" % value


def idris_string_table(name, documentation, entries):
    lines = [";".join(entries[index:index + ENTRIES_PER_LINE]) for index in range(0, len(entries), ENTRIES_PER_LINE)]
    rendered_lines = []
    for line_index, line in enumerate(lines):
        separator = ";" if line_index + 1 < len(lines) else ""
        prefix = "  [ " if line_index == 0 else "  , "
        rendered_lines.append(prefix + '"' + line + separator + '"')
    return "\n".join(
        ["||| " + documentation_line for documentation_line in documentation]
        + ["export", name + " : String", name + " =", "  fastConcat"]
        + ["  " + rendered_line for rendered_line in rendered_lines]
        + ["    ]"])


def main():
    ucd_directory = sys.argv[1] if len(sys.argv) > 1 else "/usr/share/unicode"
    canonical_combining_classes, canonical_decomposition_mappings = read_unicode_data(ucd_directory)
    full_composition_exclusions = read_full_composition_exclusions(ucd_directory)

    combining_class_entries = [
        "%s %s %X" % (hexadecimal(first), hexadecimal(last), combining_class)
        for first, last, combining_class in combining_class_ranges(canonical_combining_classes)]

    decomposition_entries = []
    composite_entries = []
    for code_point in sorted(canonical_decomposition_mappings):
        if HANGUL_SYLLABLE_FIRST <= code_point <= HANGUL_SYLLABLE_LAST:
            continue
        decomposition = full_decomposition(code_point, canonical_decomposition_mappings)
        decomposition_entries.append(" ".join(hexadecimal(part) for part in [code_point] + decomposition))
        mapping = canonical_decomposition_mappings[code_point]
        if len(mapping) == 2 and code_point not in full_composition_exclusions:
            composite_entries.append(" ".join(hexadecimal(part) for part in mapping + [code_point]))

    version = unicode_version(ucd_directory)
    module_text = "\n".join([
        "-- Generated by tools/generate_unicode_normalization_data.py from the Unicode",
        "-- Character Database " + version + " (UnicodeData.txt, DerivedNormalizationProps.txt).",
        "-- Do not edit by hand: rerun the script instead.",
        "module Compiler.Frontend.Lexer.UnicodeNormalizationData",
        "",
        "%default total",
        "",
        "||| The version of the Unicode Character Database the tables come from.",
        "export",
        "unicodeNormalizationDataVersion : String",
        'unicodeNormalizationDataVersion = "' + version + '"',
        "",
        idris_string_table(
            "canonicalCombiningClassRanges",
            ["Ranges of code points with a nonzero canonical combining class, as",
             "\"first last class\" entries in hexadecimal separated by ';'."],
            combining_class_entries),
        "",
        idris_string_table(
            "fullCanonicalDecompositions",
            ["Full canonical decompositions, as \"codePoint decomposition...\" entries",
             "in hexadecimal separated by ';'. Hangul syllables are not listed: their",
             "decompositions are computed."],
            decomposition_entries),
        "",
        idris_string_table(
            "primaryComposites",
            ["Primary composites, as \"first second composite\" entries in hexadecimal",
             "separated by ';': the code points with a two-code-point canonical",
             "decomposition that are not excluded from composition. Hangul syllables",
             "are not listed: their compositions are computed."],
            composite_entries),
        "",
    ])
    with open(OUTPUT_PATH, "w", encoding="utf-8") as output:
        output.write(module_text)
    print("wrote %s: %d combining class ranges, %d decompositions, %d composites (Unicode %s)" % (
        os.path.normpath(OUTPUT_PATH), len(combining_class_entries), len(decomposition_entries),
        len(composite_entries), version))


if __name__ == "__main__":
    main()
