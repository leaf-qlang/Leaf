module Compiler.Frontend.Syntax.ParseRules

import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Token
import Compiler.Frontend.Syntax.AST

%default total

--------------------------------------------------------------------------------
-- How the parser reads Leaf source
--------------------------------------------------------------------------------

public export
isBlockLikeExpression : ExpressionNode phase -> Bool
isBlockLikeExpression expressionNode =
  case expressionNode of
    ExprBlock _                      => True
    ExprIf _                         => True
    ExprQIf _                        => True
    ExprSIf _                        => True
    ExprMatch _                      => True
    ExprQMatch _                     => True
    ExprSMatch _                     => True
    ExprLoop _                       => True
    ExprWhile _ _                    => True
    ExprFor _ _ _                    => True
    ExprCtrl (ControlledBlock _ _ _) => True
    ExprAdjoint (AdjointBlock _)     => True
    _                                => False

||| Whether the parser reads an identifier as the name of a struct literal when
||| `{` follows it: one starting with an ASCII uppercase letter. As in Rust,
||| this does not apply in the head of `if`, `while` or `for`, which does not
||| allow struct literals: in `if FLAG { }` the block follows the name `FLAG`.
public export
readsAsStructLiteralName : String -> Bool
readsAsStructLiteralName identifierText =
  case unpack identifierText of
    firstCharacter :: _ => firstCharacter >= 'A' && firstCharacter <= 'Z'
    []     => False

||| Tokens before which `..` ends a range with no upper bound, as in `a..`.
public export
isOpenRangeTerminator : Token -> Bool
isOpenRangeTerminator (TokSym SymSemi)     = True
isOpenRangeTerminator (TokSym SymComma)    = True
isOpenRangeTerminator (TokSym SymRParen)   = True
isOpenRangeTerminator (TokSym SymRBracket) = True
isOpenRangeTerminator (TokSym SymRBrace)   = True
isOpenRangeTerminator _                    = False

||| Tokens before which `return` and `break` take no value. Before any other
||| token they read one, so `(return)` does not parse.
public export
isOptionalValueTerminator : Token -> Bool
isOptionalValueTerminator (TokSym SymSemi)   = True
isOptionalValueTerminator (TokSym SymComma)  = True
isOptionalValueTerminator (TokSym SymRBrace) = True
isOptionalValueTerminator _                  = False
