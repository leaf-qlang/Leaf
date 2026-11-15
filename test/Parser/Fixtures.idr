||| Builders for surface ASTs written directly in tests, for the syntax the
||| parser does not accept yet and for exact control over node IDs. Builders
||| ending in `At` take the node's surface ID; the others use ID 0.
module Parser.Fixtures

import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import public Parser.FixtureSource

%default total

export
surfaceAt : Nat -> a -> SurfaceAstNode a
surfaceAt number = surfaceAstNode (fixtureInfo number)

export
surface : a -> SurfaceAstNode a
surface = surfaceAt 0

export
nameAt : Nat -> String -> SurfaceName
nameAt number text = surfaceAt number (MkNameNode text)

export
name : String -> SurfaceName
name = nameAt 0

||| A one-segment path; the segment's ID follows the path's.
export
pathAt : Nat -> String -> SurfacePath
pathAt number text = surfaceAt number (MkPathNode (surfaceAt (S number) (PathSegmentName text)) [])

||| An integer literal expression; the literal's ID follows the expression's.
export
integerAt : Nat -> String -> SurfaceExpr
integerAt number raw = surfaceAt number (ExprLiteral (surfaceAt (S number) (LiteralIntegerRaw raw)))

export
integer : String -> SurfaceExpr
integer = integerAt 0

||| A name expression; the name's ID follows the expression's.
export
nameExprAt : Nat -> String -> SurfaceExpr
nameExprAt number text = surfaceAt number (ExprName (nameAt (S number) text))

export
nameExpr : String -> SurfaceExpr
nameExpr = nameExprAt 0

||| A block with no statements whose value is the given expression.
export
valueBlockAt : Nat -> SurfaceExpr -> SurfaceBlock
valueBlockAt number value = surfaceAt number (MkBlockNode [] [] (Just value))

export
valueBlock : SurfaceExpr -> SurfaceBlock
valueBlock = valueBlockAt 0

export
emptyBlock : SurfaceBlock
emptyBlock = surface (MkBlockNode [] [] Nothing)

||| A block expression whose value is the given expression.
export
blockOf : SurfaceExpr -> SurfaceExpr
blockOf value = surface (ExprBlock (valueBlock value))

export
negated : SurfaceExpr -> SurfaceExpr
negated operand = surface (ExprUnary (surface UnaryNegate) operand)

export
plus : SurfaceExpr -> SurfaceExpr -> SurfaceExpr
plus left right = surface (ExprBinary (surface BinaryAdd) left right)

export
returning : SurfaceExpr -> SurfaceExpr
returning value = surface (ExprReturn (Just value))

||| A quantum if whose branches may each be an expression or a block.
export
qifWithBranches : SurfaceExpr -> QuantumBranchNode SurfaceAstPhase -> Maybe (QuantumBranchNode SurfaceAstPhase) ->
                  SurfaceExpr
qifWithBranches condition yes no = surface (ExprQIf (MkQuantumIfNode condition yes no))

||| A quantum if whose branches are expressions.
export
qif : SurfaceExpr -> SurfaceExpr -> Maybe SurfaceExpr -> SurfaceExpr
qif condition yes no = qifWithBranches condition (QuantumBranchExpression yes) (map QuantumBranchExpression no)

export
sif : SurfaceExpr -> SurfaceExpr -> SurfaceExpr -> SurfaceExpr
sif condition yes no = surface (ExprSIf (MkStateIfNode condition yes no))

export
innerDocAt : Nat -> DocCommentKind -> String -> SurfaceDocComment
innerDocAt number kind raw = surfaceAt number (MkDocCommentNode kind DocCommentInner raw)

export
innerDoc : DocCommentKind -> String -> SurfaceDocComment
innerDoc = innerDocAt 0
