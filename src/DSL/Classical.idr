module DSL.Classical

%default total

public export
data ClassicalType = UnitType | BitType

public export
ClassicalContext : Type
ClassicalContext = List ClassicalType
