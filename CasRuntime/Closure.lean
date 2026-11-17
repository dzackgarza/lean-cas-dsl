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

private def valueKey : Name := `CasCompiler.lower.value

def markedKey? (data : MData) : Option Nat :=
  match data.find valueKey with
  | some (.ofNat key) => some key
  | _ => none

/-- Associate an actual retained value with one occurrence of its checked source term.
Reuse: Lean MData, preserved by closure and ignored by kernel conversion, as sourceReference. -/
def markValue (marks : IO.Ref (Array ValueBinding)) (value : ValueBinding) (expression : Expr) :
    BaseIO Expr := do
  let key ← marks.modifyGet fun values => (values.size, values.push value)
  return .mdata (KVMap.empty.setNat valueKey key) expression

end CasRuntime
