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
surfaceAt surfaceId = surfaceAstNode (fixtureInfo surfaceId)

export
surface : a -> SurfaceAstNode a
surface = surfaceAt 0

export
nameAt : Nat -> String -> SurfaceName
nameAt surfaceId nameText = surfaceAt surfaceId (MkNameNode nameText)

export
name : String -> SurfaceName
name = nameAt 0

||| A one-segment path; the segment's ID follows the path's.
export
pathAt : Nat -> String -> SurfacePath
pathAt surfaceId segmentText = surfaceAt surfaceId (MkPathNode (surfaceAt (S surfaceId) (PathSegmentName segmentText)) [])

||| An integer literal expression; the literal's ID follows the expression's.
export
integerAt : Nat -> String -> SurfaceExpr
integerAt surfaceId rawSpelling = surfaceAt surfaceId (ExprLiteral (surfaceAt (S surfaceId) (LiteralIntegerRaw rawSpelling)))

export
integer : String -> SurfaceExpr
integer = integerAt 0

||| A name expression; the name's ID follows the expression's.
export
nameExprAt : Nat -> String -> SurfaceExpr
nameExprAt surfaceId nameText = surfaceAt surfaceId (ExprName (nameAt (S surfaceId) nameText))

export
nameExpr : String -> SurfaceExpr
nameExpr = nameExprAt 0

||| A block with no statements whose value is the given expression.
export
valueBlockAt : Nat -> SurfaceExpr -> SurfaceBlock
valueBlockAt surfaceId finalExpression = surfaceAt surfaceId (MkBlockNode [] [] (Just finalExpression))

export
valueBlock : SurfaceExpr -> SurfaceBlock
valueBlock = valueBlockAt 0

export
emptyBlock : SurfaceBlock
emptyBlock = surface (MkBlockNode [] [] Nothing)

||| A block expression whose value is the given expression.
export
blockOf : SurfaceExpr -> SurfaceExpr
blockOf finalExpression = surface (ExprBlock (valueBlock finalExpression))

export
negated : SurfaceExpr -> SurfaceExpr
negated operand = surface (ExprUnary (surface UnaryNegate) operand)

export
plus : SurfaceExpr -> SurfaceExpr -> SurfaceExpr
plus leftOperand rightOperand = surface (ExprBinary (surface BinaryAdd) leftOperand rightOperand)

export
returning : SurfaceExpr -> SurfaceExpr
returning returnValue = surface (ExprReturn (Just returnValue))

||| A quantum if whose branches may each be an expression or a block.
export
qifWithBranches : SurfaceExpr -> QuantumBranchNode SurfaceAstPhase -> Maybe (QuantumBranchNode SurfaceAstPhase) ->
                  SurfaceExpr
qifWithBranches condition thenBranch elseBranch = surface (ExprQIf (MkQuantumIfNode condition thenBranch elseBranch))

||| A quantum if whose branches are expressions.
export
qif : SurfaceExpr -> SurfaceExpr -> Maybe SurfaceExpr -> SurfaceExpr
qif condition thenBranch elseBranch = qifWithBranches condition (QuantumBranchExpression thenBranch) (map QuantumBranchExpression elseBranch)

export
sif : SurfaceExpr -> SurfaceExpr -> SurfaceExpr -> SurfaceExpr
sif condition thenBranch elseBranch = surface (ExprSIf (MkStateIfNode condition thenBranch elseBranch))

export
innerDocAt : Nat -> DocCommentKind -> String -> SurfaceDocComment
innerDocAt surfaceId commentKind rawText = surfaceAt surfaceId (MkDocCommentNode commentKind DocCommentInner rawText)

export
innerDoc : DocCommentKind -> String -> SurfaceDocComment
innerDoc = innerDocAt 0
