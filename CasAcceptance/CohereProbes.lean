/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-cohere` (CC-COHERE, CC-RESOLVE's ring diamond)

With the comparison `cmp.rings.carrier` registered (the identity natural isomorphism between the
multiplicative and additive routes from rings to sets):

* `cardinality` on rings resolves, and its provenance names the comparison;
* the call runs on the comparison's source route (the multiplicative one), whatever the order of
  rows; reversing the comparison's direction designates the other route: the direction, a
  registered datum, designates the route, not an order; two registered comparisons between the
  same two routes are an ambiguity;
* the ports stay distinct where they carry different structure: a method owned at magmas is still
  ambiguous on rings, since the comparison covers only the route to sets;
* registration rejects a comparison whose evidence is about other functors or whose sides are not
  composites between its endpoints; a cell from a route to itself identifies nothing.

`ResolveProbes` shows the same call ambiguous without the comparison row.
-/

open Lean Meta Elab Term Command

namespace CasCatalogue.CohereProbes

#resolve cardinality in "cat.rings"

/-- An isomorphism about the wrong functors. -/
noncomputable def unrelatedIso :=
  CategoryTheory.Iso.refl LeanCategories.Modules.ModulesOverRings.underlying.{0, 0}

run_cmd liftTermElabM do
  let state ← registryState
  let some rings := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "cat.rings is not registered"
  let some magmas := state.categories.find? (·.id.raw == "cat.magmas")
    | throwError "cat.magmas is not registered"
  let some carrier := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "cmp.rings.carrier is not registered"
  -- The comparison identifies the two routes at sets, and the provenance says so.
  match state.resolveMethod rings.expression "cardinality" with
  | .ok r =>
      unless r.comparisons.map (·.raw) == #["cmp.rings.carrier"] do
        throwError "the resolution does not carry its comparison: {state.renderResolution r}"
  | .error e => throwError e.render state
  -- A single route needs no comparison: the formed-module route carries none.
  let some bilin := state.categories.find? (·.id.raw == "cat.bilin_module")
    | throwError "cat.bilin_module is not registered"
  match state.resolveMethod bilin.expression "cardinality" with
  | .ok r => unless r.comparisons.isEmpty do throwError "a unique route carries a comparison"
  | .error e => throwError e.render state
  -- The call runs on the comparison's source route, whatever the order of rows.
  let runsOn (s : RegistryState) : MetaM (Option FunctorId) :=
    match s.resolveMethod rings.expression "cardinality" with
    | .ok r => pure r.route.functorIds[0]?
    | .error e => throwError e.render s
  unless (← runsOn state) == some FunctorId.ringsMultiplicative do
    throwError "the call does not run on the comparison's source route"
  let reordered := { state with cells := state.cells.reverse, methods := state.methods.reverse }
  unless (← runsOn reordered) == some FunctorId.ringsMultiplicative do
    throwError "the executed route depends on the order of rows"
  -- Reversing the comparison's direction designates the other route.
  let reversed := { state with cells := state.cells.map fun c =>
      if c.id == carrier.id then { c with left := c.right, right := c.left } else c }
  unless (← runsOn reversed) == some FunctorId.ringsAdditive do
    throwError "the comparison's direction does not designate the route"
  -- Two comparisons between the same routes are an ambiguity.
  let twice := { state with cells := state.cells.push { carrier with id := ⟨"cmp.probe.twice"⟩ } }
  match twice.resolveMethod rings.expression "cardinality" with
  | .error (.ambiguousComparison _ _ _ cells) =>
      unless cells.size == 2 do throwError "expected both comparisons, got {cells.size}"
  | _ => throwError "two comparisons between the same routes were not an ambiguity"
  -- The ports stay distinct at magmas: a method owned there is ambiguous on rings.
  let magmaMethod : MethodEntry :=
    { id := ⟨"meth.probe.magma_method"⟩, name := "probe_magma_method", owner := magmas.expression
      functor := ⟨"fun.probe.magma_method"⟩, shape := .object }
  let probe := { state with methods := state.methods.push magmaMethod }
  match probe.resolveMethod rings.expression "probe_magma_method" with
  | .error (.ambiguous _ candidates) =>
      unless candidates.size == 2 do throwError "expected the two ports, got {candidates.size}"
  | _ => throwError "the carrier comparison identified the ports at magmas"
  -- Registration rejects bad comparisons.
  let rejects (entry : RegistryEntry) : MetaM Bool := do
    try
      validateRegistryEntryDeclaration entry
      pure false
    catch _ => pure true
  let multiplicative : Array EdgeRef := #[.functor FunctorId.ringsMultiplicative,
    .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  let additive : Array EdgeRef := #[.functor FunctorId.ringsAdditive,
    .functor FunctorId.additiveGroupsToGroups, .functor FunctorId.groupsMonoid,
    .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  let comparison (id : String) (left right : Array EdgeRef) (evidence : Name) : RegistryEntry :=
    .cell
      { id := ⟨id⟩
        source := rings.expression
        target := Foundation.Sets
        left := left
        right := right
        declaration := evidence
        invertible := true }
  let carrierDeclaration := `LeanCategories.Algebra.ringCarrierComparison
  if !(← rejects (comparison "cmp.probe.unrelated" multiplicative additive ``unrelatedIso)) then
    throwError "a comparison with unrelated evidence was accepted"
  if !(← rejects (comparison "cmp.probe.not_a_route"
      #[.functor FunctorId.ringsMultiplicative] additive carrierDeclaration)) then
    throwError "a comparison whose side is not a route to its target was accepted"
  -- A cell from a route to itself is an automorphism, never an identification of routes.
  let multiplicativeRoute : Route :=
    { source := rings.expression, target := Foundation.Sets
      steps := (state.routeEdges? rings.expression Foundation.Sets multiplicative).getD #[] }
  let selfCell : CellEntry :=
    { id := ⟨"cmp.probe.self"⟩, source := rings.expression, target := Foundation.Sets
      left := multiplicative, right := multiplicative, declaration := carrierDeclaration
      invertible := true }
  unless ({ state with cells := state.cells.push selfCell }).comparisonsFrom
      multiplicativeRoute multiplicativeRoute |>.isEmpty do
    throwError "a cell of a route to itself identified routes"
  if ← rejects (comparison "cmp.probe.control" multiplicative additive carrierDeclaration) then
    throwError "the carrier comparison was rejected"

end CasCatalogue.CohereProbes
