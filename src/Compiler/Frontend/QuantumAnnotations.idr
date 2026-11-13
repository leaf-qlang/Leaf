module Compiler.Frontend.QuantumAnnotations

import Compiler.Frontend.Syntax.Common

%default total

public export
data QuantumCleanup
  = NoAutomaticCleanup
  | ScratchCleanup
  | UncomputeOnReturn

public export
record QuantumStorageProperties where
  constructor MkQuantumStorageProperties
  cleanup : QuantumCleanup
