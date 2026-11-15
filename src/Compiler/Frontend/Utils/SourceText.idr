module Compiler.Frontend.Utils.SourceText

import Data.Maybe
import Data.String

%default total

public export
data SourceText
  = Chunk String
  | Append (Lazy SourceText) (Lazy SourceText)

public export
FromString SourceText where
  fromString = Chunk

export
infixr 6 <+>

public export
(<+>) : Lazy SourceText -> Lazy SourceText -> SourceText
(<+>) = Append

export
text : String -> SourceText
text = Chunk

chunks : SourceText -> List String -> List String
chunks (Chunk value) rest = value :: rest
chunks (Append left right) rest = chunks left (chunks right rest)

export
renderSource : SourceText -> String
renderSource document = fastConcat (chunks document [])

-- Consume whole escape sequences until their combined length reaches `room`.
escapePrefix : (Char -> List Char) -> Nat -> List Char ->
               (Nat -> List (List Char)) -> List (List Char)
escapePrefix _ Z _ _ = []
escapePrefix escape room [] rest = rest room
escapePrefix escape room (c :: cs) rest =
  let sequence = escape c in
  sequence :: (if length sequence >= room
    then []
    else escapePrefix escape (minus room (length sequence)) cs rest)

-- Escape sequences for the first `limit` escaped characters of a document.
prefixEscapes : (Char -> List Char) -> Nat -> SourceText ->
                (Nat -> List (List Char)) -> List (List Char)
prefixEscapes _ Z _ _ = []
prefixEscapes escape (S remaining) (Chunk value) rest =
  -- Nonempty escapes mean we need at most this many raw characters. Slice
  -- before unpacking so even a very large leaf takes bounded work.
  escapePrefix escape (S remaining) (unpack (substr 0 (S remaining) value)) rest
prefixEscapes escape (S remaining) (Append left right) rest =
  prefixEscapes escape (S remaining) left
    (\available => prefixEscapes escape available right rest)

export
sourceFirstChar : SourceText -> Maybe Char
sourceFirstChar document = case prefixEscapes (\c => [c]) 1 document (const []) of
  [c] :: _ => Just c
  _        => Nothing

export
sourceIsEmpty : SourceText -> Bool
sourceIsEmpty = isNothing . sourceFirstChar

export
sourceStartsWith : Char -> SourceText -> Bool
sourceStartsWith c document = sourceFirstChar document == Just c

-- Returns at most `limit` escaped characters, including an ellipsis if needed.
export
renderSourcePreview : (escape : Char -> List Char) -> (limit : Nat) -> SourceText -> String
renderSourcePreview escape Z _ = ""
renderSourcePreview escape (S limit) document =
  let escaped = prefixEscapes escape (S (S limit)) document (const []) in
  if sum (map length escaped) <= S limit
    then pack (concat escaped)
    else pack (fitting limit escaped) ++ "…"
  where
    -- Whole escape sequences, in order, while they fit in `room` characters.
    fitting : Nat -> List (List Char) -> List Char
    fitting _ [] = []
    fitting room (sequence :: rest) =
      if length sequence <= room
        then sequence ++ fitting (minus room (length sequence)) rest
        else []
