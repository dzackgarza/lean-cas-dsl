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
      { program, occurrence, role := targetRole, parameters := #[] } (.closure program #[])
  let .ok retained := graph.rebind input planRole | throwError "the input role could not be retained"
  let request ← PreparedRequest.forBoundary program occurrence (.target family)
    (family.source.universeParams.map Level.param) context #[] #[input, retained] #[]
  let some first := request.scope[0]? | throwError "the first scope slot is missing"
  let some second := request.scope[1]? | throwError "the second scope slot is missing"
  unless request.reference == some family.source.entry.target && request.scope.size == 2 &&
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
        (.prerequisite family ⟨index, bound⟩) (family.source.universeParams.map Level.param)
        context #[] #[] #[]
      unless slot.reference == some family.source.prerequisites[index].reference do
        throwError "request preparation changed an ordered primitive reference"
    else throwError "the prerequisite index is outside the checked family"
  let other ← liftM (m := IO) OwnerRegistry.new
  let foreignProgram ← liftM (m := BaseIO) (other.identities.fresh .program)
  let rejected ← try
    discard <| PreparedRequest.forBoundary foreignProgram occurrence (.target family)
      (family.source.universeParams.map Level.param) context #[] #[] #[]
    pure false
  catch _ => pure true
  unless rejected do throwError "request preparation mixed worker identities"

example (request : PreparedRequest) : Type := OperationalSignature.B request

example (request : PreparedRequest) : OperationalProgram (CandidateResponse request.source) :=
  PFunctor.FreeM.lift (P := OperationalSignature) request

run_cmd Lean.Elab.Command.liftTermElabM do
  let reference : ComputationRef := .operation ⟨"op.monoids.mul"⟩
  let family ← SourceFamily.forReference reference
  let context ← ContextTelescope.capture #[]
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let request ← PreparedRequest.forBoundary program occurrence (.registered family)
    (family.universeParams.map Level.param) context #[] #[] #[]
  unless request.reference == some reference && family.source.reference == reference do
    throwError "direct source intake changed the registered primitive address"
  forallTelescope family.source.familyType fun arguments _ => do
    let declarations := (← getLCtx).foldl (fun result declaration => result.push declaration) #[]
    let bindings := declarations.mapIdx fun index declaration => ({
      id := ⟨"primitive-application", index⟩, role := .parameter,
      expression := mkFVar declaration.fvarId } : LocalBinding)
    let context ← ContextTelescope.capture bindings
    let specified ← arguments.mapM context.close
    let applied ← PreparedRequest.forBoundary program occurrence (.registered family)
      (family.universeParams.map Level.param) context specified #[] #[]
    let some layout := applied.application
      | throwError "registered source application lost its native argument telescope"
    unless layout.arguments.size == arguments.size &&
        layout.arguments.map (·.sourceIndex) == Array.range arguments.size &&
        layout.resultDependencies.contains 0 do
      throwError "registered source application changed its complete formal dependency slots"
    let resultFamily ← layout.resultTypeFamily.inContext context
    let actual ← applied.source.source.inContext context
    unless ← isDefEq (mkAppN resultFamily arguments).headBeta (← inferType actual) do
      throwError "registered source application changed the original result-type family"
  unless ← isDefEq request.source.source.expression family.source.family do
    throwError "direct request preparation changed the published family"
  unless ← isDefEq (← inferType family.source.family) family.source.familyType do
    throwError "direct source intake changed the complete family type"
  if family.source.family.hasFVar || family.source.family.hasExprMVar ||
      family.source.family.hasLevelMVar || family.source.family.hasLooseBVars then
    throwError "direct source intake retained an unresolved or free parameter"
  let info ← getConstInfo family.source.declaration
  unless family.universeParams == info.levelParams do
    throwError "direct source intake dropped rigid declaration universes"
  let rejected ← try
    discard <| SourceFamily.forReference (.operation ⟨s!"unregistered.{owners.worker}"⟩)
    pure false
  catch _ => pure true
  unless rejected do throwError "direct source intake accepted an unregistered address"
  let polymorphic ← SourceFamily.forReference (.functor FunctorId.ringsMultiplicative)
  unless !polymorphic.universeParams.isEmpty do
    throwError "the polymorphic source control has no universe parameter"
  let renamed := polymorphic.universeParams.map fun name => Level.param (name.str "actual")
  let specialized ← PreparedRequest.forBoundary program occurrence (.registered polymorphic)
    (universeArguments := renamed) context #[] #[] #[]
  let expected := polymorphic.source.family.instantiateLevelParams polymorphic.universeParams renamed
  unless ← isDefEq specialized.source.source.expression expected do
    throwError "request preparation lost the explicit universe substitution"
  unless specialized.universeArguments == some renamed do
    throwError "request preparation lost its original-to-actual universe correspondence"
  let some output := specialized.outputs[0]?
    | throwError "the source functor field is missing"
  unless specialized.source.kind == .record && specialized.outputs.size == 1 &&
      output.address == #[``CategoryTheory.Cat.Hom.toFunctor] do
    throwError "the record response lost its exact source projection address"
  let badArity ← try
    discard <| PreparedRequest.forBoundary program occurrence (.registered polymorphic)
      (renamed ++ [.zero]) context #[] #[] #[]
    pure false
  catch _ => pure true
  unless badArity do throwError "request preparation accepted the wrong universe arity"
  let unresolved ← mkFreshLevelMVar
  let rejectedUniverse ← try
    discard <| PreparedRequest.forBoundary program occurrence (.registered polymorphic)
      (polymorphic.universeParams.map fun _ => unresolved) context #[] #[] #[]
    pure false
  catch _ => pure true
  unless rejectedUniverse do throwError "request preparation retained an unresolved universe"
