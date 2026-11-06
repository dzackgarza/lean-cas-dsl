module

import CasCompiler.Program
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import Lean.Elab.Command
meta import CasCompiler.Program
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations

open Lean Meta CasCompiler CasRuntime CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let programs ← SourceProgram.forTarget (.operation ⟨"op.rings.mul"⟩)
  let some family := programs[0]? | throwError "the published family is unavailable"
  let context ← ContextTelescope.capture #[]
  let targetRole ← SourceLayout.ofTerm (← context.close family.source.target)
  let planRole ← SourceLayout.ofTerm (← context.close family.source.plan)
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, input) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := targetRole } (.closure program #[])
  let .ok alias := graph.rebind input planRole | throwError "the input role could not be retained"
  let request ← PreparedRequest.forBoundary program occurrence (.target family)
    context #[] #[input, alias]
  let some first := request.scope[0]? | throwError "the first scope slot is missing"
  let some second := request.scope[1]? | throwError "the second scope slot is missing"
  unless request.reference == family.source.entry.target && request.scope.size == 2 &&
      first.value == second.value do
    throwError "request preparation changed an exact family reference or aliased scope slots"
  unless first.role.source.expression == targetRole.source.expression &&
      second.role.source.expression == planRole.source.expression do
    throwError "request preparation merged distinct consuming roles"
  unless request.outputs.size == 1 && request.source.kind == .function do
    throwError "the whole source family lost its callable result role"
  unless ← isDefEq request.source.source.expression family.source.target do
    throwError "request preparation changed the checked source family"
  for index in [:family.source.prerequisites.size] do
    if bound : index < family.source.prerequisites.size then
      let slot ← PreparedRequest.forBoundary program occurrence
        (.prerequisite family ⟨index, bound⟩) context #[] #[]
      unless slot.reference == family.source.prerequisites[index].reference do
        throwError "request preparation changed an ordered primitive reference"
    else throwError "the prerequisite index is outside the checked family"
  let other ← liftM (m := IO) OwnerRegistry.new
  let foreignProgram ← liftM (m := BaseIO) (other.identities.fresh .program)
  let rejected ← try
    discard <| PreparedRequest.forBoundary foreignProgram occurrence (.target family)
      context #[] #[]
    pure false
  catch _ => pure true
  unless rejected do throwError "request preparation mixed worker identities"

example (request : PreparedRequest) : Type := OperationalSignature.B request

example (request : PreparedRequest) : OperationalProgram (Vector ValueBinding request.outputs.size) :=
  PFunctor.FreeM.lift request
