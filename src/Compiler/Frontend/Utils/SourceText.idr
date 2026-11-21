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

-- The document's chunks in order, followed by `laterChunks`.
collectChunks : SourceText -> (laterChunks : List String) -> List String
collectChunks (Chunk chunkText) laterChunks = chunkText :: laterChunks
collectChunks (Append firstPart secondPart) laterChunks = collectChunks firstPart (collectChunks secondPart laterChunks)

export
renderSource : SourceText -> String
renderSource document = fastConcat (collectChunks document [])

-- Consume whole escape sequences until their combined length reaches `room`.
escapePrefix : (Char -> List Char) -> Nat -> List Char ->
               (Nat -> List (List Char)) -> List (List Char)
escapePrefix _ Z _ _ = []
escapePrefix escapeCharacter room [] continueWithRoom = continueWithRoom room
escapePrefix escapeCharacter room (character :: remainingCharacters) continueWithRoom =
  let escapeSequence = escapeCharacter character in
  escapeSequence :: (if length escapeSequence >= room
    then []
    else escapePrefix escapeCharacter (minus room (length escapeSequence)) remainingCharacters continueWithRoom)

-- Escape sequences for the first `limit` escaped characters of a document.
prefixEscapes : (Char -> List Char) -> Nat -> SourceText ->
                (Nat -> List (List Char)) -> List (List Char)
prefixEscapes _ Z _ _ = []
prefixEscapes escapeCharacter (S remainingLimit) (Chunk chunkText) continueWithRoom =
  -- Nonempty escapes mean we need at most this many raw characters. Slice
  -- before unpacking so even a very large leaf takes bounded work.
  escapePrefix escapeCharacter (S remainingLimit) (unpack (substr 0 (S remainingLimit) chunkText)) continueWithRoom
prefixEscapes escapeCharacter (S remainingLimit) (Append firstPart secondPart) continueWithRoom =
  prefixEscapes escapeCharacter (S remainingLimit) firstPart
    (\availableRoom => prefixEscapes escapeCharacter availableRoom secondPart continueWithRoom)

export
sourceFirstChar : SourceText -> Maybe Char
sourceFirstChar document = case prefixEscapes (\character => [character]) 1 document (const []) of
  [firstCharacter] :: _ => Just firstCharacter
  _                     => Nothing

export
sourceIsEmpty : SourceText -> Bool
sourceIsEmpty = isNothing . sourceFirstChar

export
sourceStartsWith : Char -> SourceText -> Bool
sourceStartsWith expectedCharacter document = sourceFirstChar document == Just expectedCharacter

-- Returns at most `limit` escaped characters, including an ellipsis if needed.
export
renderSourcePreview : (escape : Char -> List Char) -> (limit : Nat) -> SourceText -> String
renderSourcePreview escape Z _ = ""
renderSourcePreview escape (S limit) document =
  let escapeSequences = prefixEscapes escape (S (S limit)) document (const []) in
  if sum (map length escapeSequences) <= S limit
    then pack (concat escapeSequences)
    else pack (wholeSequencesFitting limit escapeSequences) ++ "…"
  where
    -- Whole escape sequences, in order, while they fit in `room` characters.
    wholeSequencesFitting : (room : Nat) -> List (List Char) -> List Char
    wholeSequencesFitting _ [] = []
    wholeSequencesFitting room (escapeSequence :: remainingSequences) =
      if length escapeSequence <= room
        then escapeSequence ++ wholeSequencesFitting (minus room (length escapeSequence)) remainingSequences
        else []
