module Compiler.Frontend.Lexer.UnicodeNormalization

import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.String

import Compiler.Frontend.Lexer.UnicodeNormalizationData

%default total

--------------------------------------------------------------------------------
-- Unicode Normalization Form C (NFC).
--
-- Like Rust, Leaf normalizes identifiers to NFC (Unicode Standard Annex #15),
-- so canonically equivalent spellings, such as a composed `é` and `e`
-- followed by U+0301, are the same identifier. NFC is the canonical
-- decomposition of a string, put in canonical order, followed by canonical
-- composition. The tables come from `UnicodeNormalizationData`, generated from
-- the Unicode Character Database; Hangul syllables are decomposed and composed
-- arithmetically, as the standard specifies.
--------------------------------------------------------------------------------

-- The tables are strings of ';'-separated entries of hexadecimal code points.
hexadecimalValue : String -> Int
hexadecimalValue hexadecimalDigits =
  foldl (\valueSoFar, digit => valueSoFar * 16 + digitValue digit) 0 (unpack hexadecimalDigits)
  where
    digitValue : Char -> Int
    digitValue digit =
      if isDigit digit
        then ord digit - ord '0'
        else ord (toUpper digit) - ord 'A' + 10

tableEntries : String -> List (List Int)
tableEntries table =
  map (map hexadecimalValue . words) (filter (/= "") (forget (split (== ';') table)))

canonicalCombiningClasses : SortedMap Int Int
canonicalCombiningClasses =
  fromList (concatMap expandRange (tableEntries canonicalCombiningClassRanges))
  where
    expandRange : List Int -> List (Int, Int)
    expandRange [firstCodePoint, lastCodePoint, combiningClass] =
      map (\codePoint => (codePoint, combiningClass)) [firstCodePoint .. lastCodePoint]
    expandRange _ = []

decompositionsByCodePoint : SortedMap Int (List Int)
decompositionsByCodePoint =
  fromList (mapMaybe decompositionEntry (tableEntries fullCanonicalDecompositions))
  where
    decompositionEntry : List Int -> Maybe (Int, List Int)
    decompositionEntry (codePoint :: decomposition@(_ :: _)) = Just (codePoint, decomposition)
    decompositionEntry _ = Nothing

-- A pair of code points as one key; code points are below 0x110000.
codePointPairKey : Int -> Int -> Int
codePointPairKey firstCodePoint secondCodePoint = firstCodePoint * 0x110000 + secondCodePoint

compositesByCodePointPair : SortedMap Int Int
compositesByCodePointPair =
  fromList (mapMaybe compositeEntry (tableEntries primaryComposites))
  where
    compositeEntry : List Int -> Maybe (Int, Int)
    compositeEntry [firstCodePoint, secondCodePoint, composite] =
      Just (codePointPairKey firstCodePoint secondCodePoint, composite)
    compositeEntry _ = Nothing

canonicalCombiningClass : Int -> Int
canonicalCombiningClass codePoint = fromMaybe 0 (lookup codePoint canonicalCombiningClasses)

--------------------------------------------------------------------------------
-- Hangul syllables (Unicode Standard, section 3.12).
--
-- A syllable is a leading consonant jamo, a vowel jamo, and an optional
-- trailing consonant jamo; syllable code points enumerate these combinations.
--------------------------------------------------------------------------------
hangulSyllableBase : Int
hangulSyllableBase = 0xAC00

leadingJamoBase : Int
leadingJamoBase = 0x1100

vowelJamoBase : Int
vowelJamoBase = 0x1161

-- One before the first trailing consonant: index 0 means no trailing consonant.
trailingJamoBase : Int
trailingJamoBase = 0x11A7

leadingJamoCount : Int
leadingJamoCount = 19

vowelJamoCount : Int
vowelJamoCount = 21

trailingJamoCount : Int
trailingJamoCount = 28

syllablesPerLeadingJamo : Int
syllablesPerLeadingJamo = vowelJamoCount * trailingJamoCount

hangulSyllableCount : Int
hangulSyllableCount = leadingJamoCount * syllablesPerLeadingJamo

isHangulSyllable : Int -> Bool
isHangulSyllable codePoint =
  hangulSyllableBase <= codePoint && codePoint < hangulSyllableBase + hangulSyllableCount

hangulSyllableDecomposition : Int -> List Int
hangulSyllableDecomposition syllable =
  let syllableIndex = syllable - hangulSyllableBase
      leadingJamo = leadingJamoBase + syllableIndex `div` syllablesPerLeadingJamo
      vowelJamo = vowelJamoBase + (syllableIndex `mod` syllablesPerLeadingJamo) `div` trailingJamoCount
      trailingIndex = syllableIndex `mod` trailingJamoCount
  in if trailingIndex == 0
       then [leadingJamo, vowelJamo]
       else [leadingJamo, vowelJamo, trailingJamoBase + trailingIndex]

-- The syllable composed of a leading and a vowel jamo, or of a syllable without
-- a trailing consonant and a trailing jamo.
hangulComposite : Int -> Int -> Maybe Int
hangulComposite firstCodePoint secondCodePoint =
  let leadingIndex = firstCodePoint - leadingJamoBase
      vowelIndex = secondCodePoint - vowelJamoBase
      syllableIndex = firstCodePoint - hangulSyllableBase
      trailingIndex = secondCodePoint - trailingJamoBase
  in if 0 <= leadingIndex && leadingIndex < leadingJamoCount && 0 <= vowelIndex && vowelIndex < vowelJamoCount
       then Just (hangulSyllableBase + (leadingIndex * vowelJamoCount + vowelIndex) * trailingJamoCount)
       else if isHangulSyllable firstCodePoint && syllableIndex `mod` trailingJamoCount == 0
                 && 0 < trailingIndex && trailingIndex < trailingJamoCount
         then Just (firstCodePoint + trailingIndex)
         else Nothing

--------------------------------------------------------------------------------
-- Decomposition, canonical ordering, and composition.
--------------------------------------------------------------------------------
fullCanonicalDecomposition : Int -> List Int
fullCanonicalDecomposition codePoint =
  if isHangulSyllable codePoint
    then hangulSyllableDecomposition codePoint
    else fromMaybe [codePoint] (lookup codePoint decompositionsByCodePoint)

-- Sorts every run of code points with a nonzero combining class by that class,
-- keeping code points with equal classes in their order (a stable sort).
canonicallyOrdered : List Int -> List Int
canonicallyOrdered = orderRuns [<]
  where
    -- `sortBy` from Data.List is a stable merge sort, so code points with an
    -- equal class keep their order, and a run of n code points is sorted in
    -- O(n log n) time. Each code point's class is looked up once, before
    -- sorting, rather than at every comparison.
    sortedByCombiningClass : List Int -> List Int
    sortedByCombiningClass run =
      map snd
        (sortBy
           (\(firstCombiningClass, _), (secondCombiningClass, _) => compare firstCombiningClass secondCombiningClass)
           (map (\codePoint => (canonicalCombiningClass codePoint, codePoint)) run))

    -- `pendingRun` holds the current run of non-starters, in order.
    orderRuns : SnocList Int -> List Int -> List Int
    orderRuns pendingRun [] = sortedByCombiningClass (pendingRun <>> [])
    orderRuns pendingRun (codePoint :: laterCodePoints) =
      if canonicalCombiningClass codePoint == 0
        then sortedByCombiningClass (pendingRun <>> []) ++ codePoint :: orderRuns [<] laterCodePoints
        else orderRuns (pendingRun :< codePoint) laterCodePoints

primaryComposite : Int -> Int -> Maybe Int
primaryComposite firstCodePoint secondCodePoint =
  case hangulComposite firstCodePoint secondCodePoint of
    Just syllable => Just syllable
    Nothing => lookup (codePointPairKey firstCodePoint secondCodePoint) compositesByCodePointPair

-- Canonical composition of a canonically ordered decomposition: each code point
-- combines with the last starter before it unless a code point between them
-- blocks it, that is, has a combining class of zero or not below its own.
canonicallyComposed : List Int -> List Int
canonicallyComposed [] = []
canonicallyComposed (firstCodePoint :: laterCodePoints) =
  case canonicalCombiningClass firstCodePoint == 0 of
    True => composeAfterStarter [<] firstCodePoint [<] laterCodePoints
    False => firstCodePoint :: canonicallyComposed laterCodePoints
  where
    -- `composed` precedes `starter`; `uncombined` follows it and holds only
    -- non-starters, in order, that did not combine with it.
    composeAfterStarter : (composed : SnocList Int) -> (starter : Int) -> (uncombined : SnocList Int) -> List Int -> List Int
    composeAfterStarter composed starter uncombined [] = composed <>> starter :: (uncombined <>> [])
    composeAfterStarter composed starter uncombined (codePoint :: laterCodePoints) =
      let combiningClass : Int
          combiningClass = canonicalCombiningClass codePoint
          isBlocked : Bool
          isBlocked =
            case uncombined of
              [<] => False
              _ :< lastUncombined => combiningClass == 0 || canonicalCombiningClass lastUncombined >= combiningClass
          unblockedComposite : Maybe Int
          unblockedComposite = if isBlocked then Nothing else primaryComposite starter codePoint
      in case unblockedComposite of
           Just composite => composeAfterStarter composed composite uncombined laterCodePoints
           Nothing =>
             if combiningClass == 0
               then composeAfterStarter ((composed :< starter) <>< (uncombined <>> [])) codePoint [<] laterCodePoints
               else composeAfterStarter composed starter (uncombined :< codePoint) laterCodePoints

||| The Normalization Form C of a string.
export
nfcNormalized : String -> String
nfcNormalized text =
  pack $ map chr $ canonicallyComposed $ canonicallyOrdered $ concatMap fullCanonicalDecomposition $ map ord $ unpack text
