/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.DirectConstruction
public import CasCatalogue.CategoryContext
public import CasCatalogue.Admission

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.DeclaredAdmission

/-- A declared record projection, with no choice of mathematical structure. -/
structure Projection where
  structureName : Name
  field : Nat

/-- One registered domain at its complete dependent arguments and an optional
data-only record projection to the independently demanded type. -/
structure Plan where
  entry : ObjectEntry
  application : DirectConstruction.Application
  expected : Expr
  projections : Array Projection

/-- A checked path through single-data-field records of the supplied full type. -/
partial def projectionPath? (target expected : Expr) (allowProjection : Bool)
    (seen : Array Name := #[]) : TermElabM (Option (Array Projection)) := do
  if ← withoutModifyingState (withTransparency .all <| isDefEq target expected) then
    unless ← withTransparency .all <| isDefEq target expected do unreachable!
    return some #[]
  unless allowProjection do return none
  let target ← withTransparency .all <| whnf target
  let .const name levels := target.getAppFn | return none
  unless isStructure (← getEnv) name && !seen.contains name do return none
  let .inductInfo info ← getConstInfo name | return none
  unless !info.isRec && info.numIndices == 0 && target.getAppNumArgs == info.numParams do
    return none
  let [constructor] := info.ctors | return none
  let constructor := mkAppN (mkConst constructor levels) target.getAppArgs
  forallTelescope (← inferType constructor) fun fields _ => do
    let mut dataFields : Array (Nat × Expr) := #[]
    for index in [:fields.size] do
      let type ← inferType fields[index]!
      unless ← isProp type do dataFields := dataFields.push (index, type)
    let #[(field, dataType)] := dataFields | return none
    if dataType.hasFVar then return none
    let some tail ← projectionPath? dataType expected true (seen.push name) | return none
    return some (#[{ structureName := name, field }] ++ tail)

/-- Only the declaration's original complete result may determine admission.
Each candidate is checked independently; declaration order supplies no preference.
An optional wrapper projection is inspected structurally and introduces no law. -/
def resolve? (category : CategoryId) (expected : Expr) (allowProjection : Bool := false) :
    TermElabM (Option Plan) := do
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar || expected.hasFVar || expected.hasLooseBVars then
    throwStratum .invalid "a registered admission requires its complete demanded type"
  let state ← registryState
  let mut candidates : Array Plan := #[]
  for entry in state.objects do
    unless entry.category == category && entry.admission.isSome && entry.evidence.isSome do
      continue
    let candidate ← withoutModifyingState do
      try
        let application ← DirectConstruction.instantiate entry.declaration #[]
        let direct ← withoutModifyingState do
          return (← projectionPath? application.value expected allowProjection).isSome
        unless direct do
          CategoryContext.exposeStructureParameters application.value
        let some projections ← projectionPath? application.value expected allowProjection
          | return none
        let application ← DirectConstruction.close application
        return some ({ entry, application, expected, projections } : Plan)
      catch error =>
        if Exception.interpretationKind error == .invalid then return none
        throw error
    if let some candidate := candidate then candidates := candidates.push candidate
  match candidates with
  | #[] => return none
  | #[candidate] => return some candidate
  | _ => throwSemanticAmbiguity m!"several registered admissions have this complete demanded type: \
      {candidates.map (·.entry.id.raw)}"

/-- Extract only the retained declared data fields after the actual admission.
The result must inhabit the independently fixed full type. -/
def project (plan : Plan) (admitted : Expr) : TermElabM Expr := do
  unless ← withTransparency .all <| isDefEq (← inferType admitted) plan.application.value do
    throwStratum .invalid "the admitted value changed its complete registered domain"
  let mut result := admitted
  for projection in plan.projections do
    result := mkProj projection.structureName projection.field result
  result ← instantiateMVars result
  unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) &&
      (← withTransparency .all <| isDefEq (← inferType result) plan.expected) do
    throwStratum .invalid "the registered admission changed its demanded data type"
  return result

/-- The public codec omits proposition fields and unwraps a record with one data
field. Its checked formal projection therefore retains precisely the same data.
Only the actual supplied value and independently demanded type fix this path. -/
def projectedValue? (value expected : Expr) : TermElabM (Option Expr) := do
  let some projections ← projectionPath? (← inferType value) expected true | return none
  let mut result := value
  for projection in projections do
    result := mkProj projection.structureName projection.field result
  result ← instantiateMVars result
  unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) &&
      (← withTransparency .all <| isDefEq (← inferType result) expected) do return none
  return some result

end CasCatalogue.DeclaredAdmission
