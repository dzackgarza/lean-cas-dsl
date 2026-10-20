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

The registered ring-to-set routes form the directed comparison chain
additive commutative monoid → multiplicative → additive group. Its cells are
`cell.rings.additive_monoid_carrier` and `cmp.rings.carrier`.

* `cardinality` on rings resolves, and its provenance retains both comparisons;
* the call runs on the chain's source route, whatever the order of rows; reversing both cells
  reverses that source, whereas reversing only the second leaves two sources and is ambiguous;
* removing the ring-carrier comparison leaves the original multiplicative and additive routes
  unresolved; two registered comparisons between the same routes are also an ambiguity;
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
  let some monoidCarrier := state.cells.find? (·.id.raw == "cell.rings.additive_monoid_carrier")
    | throwError "cell.rings.additive_monoid_carrier is not registered"
  let multiplicative : Array EdgeRef := #[.functor FunctorId.ringsMultiplicative,
    .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  let additive : Array EdgeRef := #[.functor FunctorId.ringsAdditive,
    .functor FunctorId.additiveGroupsToGroups, .functor FunctorId.groupsMonoid,
    .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  let additiveMonoid : Array EdgeRef := #[.functor FunctorId.ringsAdditiveCommutative,
    .functor FunctorId.additiveCommutativeMonoidsAdditiveMonoid,
    .functor FunctorId.additiveMonoidsUnderlying]
  unless carrier.left == multiplicative && carrier.right == additive &&
      monoidCarrier.left == additiveMonoid && monoidCarrier.right == multiplicative do
    throwError "the registered comparisons do not form the stated three-route chain"
  -- Both independently declared cells are needed to identify the full current diagram.
  match state.resolveMethod rings.expression "cardinality" with
  | .ok r =>
      unless r.comparisons.size == 2 && r.comparisons.contains carrier.id &&
          r.comparisons.contains monoidCarrier.id do
        throwError "the resolution does not carry both comparisons: {state.renderResolution r}"
  | .error e => throwError e.render state
  let withoutCarrier := { state with cells := state.cells.filter (·.id != carrier.id) }
  match withoutCarrier.resolveMethod rings.expression "cardinality" with
  | .error (.ambiguous _ candidates) =>
      unless candidates.size == 3 && candidates.any (·.route.refs == multiplicative) &&
          candidates.any (·.route.refs == additive) &&
          candidates.any (·.route.refs == additiveMonoid) do
        throwError "removing the comparison lost one of the three unresolved routes"
  | _ => throwError "the ring diamond resolved without its registered comparison"
  -- A single route needs no comparison: the method's own set category has no prefix.
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "cat.sets is not registered"
  match state.resolveMethod sets.expression "cardinality" with
  | .ok r => unless r.route.refs.isEmpty && r.comparisons.isEmpty do
      throwError "the method's own category acquired a route or comparison"
  | .error e => throwError e.render state
  -- Formed modules now have two published carrier routes. Preserve their comparison.
  let some bilin := state.categories.find? (·.id.raw == "cat.bilin_module")
    | throwError "cat.bilin_module is not registered"
  match state.resolveMethod bilin.expression "cardinality" with
  | .ok r => unless r.comparisons.any (·.raw == "cell.bilin_module.carrier_routes") do
      throwError "the formed-module carrier routes lost their registered comparison"
  | .error e => throwError e.render state
  -- The complete route is fixed by the directed chain, independently of storage order.
  let runsOn (s : RegistryState) : MetaM (Array EdgeRef) :=
    match s.resolveMethod rings.expression "cardinality" with
    | .ok r => pure r.route.refs
    | .error e => throwError e.render s
  unless (← runsOn state) == additiveMonoid do
    throwError "the call does not run on the comparison chain's source route"
  let reordered := { state with
    cells := state.cells.reverse
    methods := state.methods.reverse
    functors := state.functors.reverse
    classifiers := state.classifiers.reverse }
  unless (← runsOn reordered) == additiveMonoid do
    throwError "the executed route depends on the order of rows"
  match reordered.resolveMethod rings.expression "cardinality" with
  | .ok r =>
      unless r.comparisons.size == 2 && r.comparisons.contains carrier.id &&
          r.comparisons.contains monoidCarrier.id do
        throwError "reordering the registry changed the comparison provenance"
  | .error e => throwError e.render reordered
  -- Reversing the whole chain designates the original additive-group route.
  let reversed := { state with cells := state.cells.map fun (c : CellEntry) =>
      if c.id == carrier.id || c.id == monoidCarrier.id then
        { c with left := c.right, right := c.left } else c }
  unless (← runsOn reversed) == additive do
    throwError "the comparison chain's direction does not designate the route"
  let twoSources := { state with cells := state.cells.map fun (c : CellEntry) =>
      if c.id == carrier.id then { c with left := c.right, right := c.left } else c }
  match twoSources.resolveMethod rings.expression "cardinality" with
  | .error (.noSourceRoute _ sources) =>
      unless sources.size == 2 && sources.any (·.refs == additive) &&
          sources.any (·.refs == additiveMonoid) do
        throwError "reversing one comparison did not retain both source routes"
  | _ => throwError "two source routes were resolved by an implicit choice"
  -- Two comparisons between the same routes are an ambiguity.
  let twice := { state with cells := state.cells.push { carrier with id := ⟨"cmp.probe.twice"⟩ } }
  match twice.resolveMethod rings.expression "cardinality" with
  | .error (.ambiguousComparison _ _ _ cells) =>
      unless cells.size == 2 && cells.contains carrier.id &&
          cells.contains ⟨"cmp.probe.twice"⟩ do
        throwError "expected exactly the two competing direct comparisons"
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
