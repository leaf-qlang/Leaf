module Compiler.Frontend.Helper

import Data.SortedMap
import Data.List

%default total

public export
maxKey : Ord k => SortedMap k v -> Maybe k
maxKey sortedMap = map fst (rightMost sortedMap)   -- SortedMap keeps keys ordered, so the rightmost key is the largest

public export
maxValue : Ord v => SortedMap k v -> Maybe v
maxValue sortedMap =
  case values sortedMap of
    [] => Nothing
    firstValue :: remainingValues => Just (foldl max firstValue remainingValues)

public export
keyWithMaxValue : Ord v => SortedMap k v -> Maybe k
keyWithMaxValue sortedMap =
  case Data.SortedMap.toList sortedMap of
    [] => Nothing
    firstEntry :: remainingEntries => Just (fst (foldl keepEntryWithLargerValue firstEntry remainingEntries))
  where
    keepEntryWithLargerValue : (k, v) -> (k, v) -> (k, v)
    keepEntryWithLargerValue bestEntry candidateEntry =
      if snd candidateEntry > snd bestEntry
         then candidateEntry
         else bestEntry

