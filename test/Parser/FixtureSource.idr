||| Source metadata shared by parsed fixtures and directly constructed ASTs.
module Parser.FixtureSource

import Compiler.Frontend.ASTData
import Compiler.Frontend.Source

%default total

||| The file name used in fixture diagnostics and debug dumps.
export
fixtureFile : String
fixtureFile = "test-fixture.lf"

||| Every directly constructed node spans 2:3-9 of the fixture file.
export
fixtureInfo : Nat -> AstInfo
fixtureInfo surfaceId = MkAstInfo (MkNodeId surfaceId 0)
  (MkSourceSpan fixtureFile (MkSourcePos 2 3) (MkSourcePos 2 9))
