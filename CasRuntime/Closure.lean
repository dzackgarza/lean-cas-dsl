module

public import CasRuntime.PreparedRequest

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Operational code of a kernel closure. The value node retains the actual captures.
Source: data model §5, ComputationalClosure, lean-cas-dsl#66 comment 6664275536. -/
inductive ClosureCode
  /-- A checked source term. A field or application demand lowers that eliminator on it. -/
  | term (source : ClosedTerm)
  /-- A published family at its prepared parameters, with the fields already selected.
  Its realization is selected when an action reaches actual arguments
  (execution contract v2 §5.2, lean-cas-dsl#69 comment 6664277464). -/
  | family (request : PreparedRequest) (path : Array FieldLayout)

end CasRuntime
