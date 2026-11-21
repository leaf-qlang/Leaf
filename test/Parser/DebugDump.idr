||| Read structural debug output without invoking the parser or either printer.
module Parser.DebugDump

import Data.String

%default total

||| The lines of a debug dump that hold nodes. Each starts with `#<id>`; the
||| only other line is the leading `phase=... file=...` line.
export
debugNodeLines : String -> List String
debugNodeLines = filter (isPrefixOf "#") . map trim . lines

||| One heading per node, in dump order. A line holding a chain of nodes
||| separates them with ` > #`; its span and snippet stay with the last.
||| Payloads escape `#` and backticks, so only a bare ` > #` joins nodes, and
||| the first bare backtick opens the snippet, whose text is never split.
export
debugNodeHeaders : String -> List String
debugNodeHeaders = concatMap (map pack . splitChain [<] . unpack) . debugNodeLines
  where
    splitChain : SnocList Char -> List Char -> List (List Char)
    splitChain currentHeader ('\\' :: character :: remainingCharacters) = splitChain (currentHeader :< '\\' :< character) remainingCharacters
    splitChain currentHeader ('`' :: remainingCharacters) = [currentHeader <>> ('`' :: remainingCharacters)]
    splitChain currentHeader (' ' :: '>' :: ' ' :: '#' :: remainingCharacters) = (currentHeader <>> []) :: splitChain [< '#'] remainingCharacters
    splitChain currentHeader (character :: remainingCharacters) = splitChain (currentHeader :< character) remainingCharacters
    splitChain currentHeader [] = [currentHeader <>> []]

||| A node line without the ID of any of its nodes, for tests about the rest of
||| the line, which the parser's numbering should not break.
export
withoutNodeIds : String -> String
withoutNodeIds = joinBy " > " . map withoutId . debugNodeHeaders
  where
    withoutId : String -> String
    withoutId header = pack (drop 1 (dropWhile (/= ' ') (unpack header)))

||| The label after a heading's ID: the node's constructor or token type.
export
headerLabel : String -> String
headerLabel header = case words header of
  _ :: label :: _ => label
  _ => ""

||| The label of each node, in dump order.
export
debugNodeLabels : String -> List String
debugNodeLabels = map headerLabel . debugNodeHeaders

||| The surface ID that opens each node heading. Later `#` characters, in names,
||| literals or snippets, are ignored. Nothing if a heading has no ID, so a
||| malformed dump fails the test instead of reading as node 0.
export
debugNodeSurfaceIds : String -> Maybe (List Nat)
debugNodeSurfaceIds = traverse surfaceId . debugNodeHeaders
  where
    surfaceId : String -> Maybe Nat
    surfaceId header = case takeWhile isDigit (drop 1 (unpack header)) of
      [] => Nothing
      digits => Just (stringToNatOrZ (pack digits))
