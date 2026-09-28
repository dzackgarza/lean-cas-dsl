/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Standard
public import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-cohere` (CC-COHERE, CC-RESOLVE's ring diamond)

With the comparison `cmp.rings.carrier` registered (the identity natural isomorphism between the
multiplicative and additive routes from rings to sets):

* `cardinality` on rings resolves, and its provenance names the comparison;
* the ports stay distinct where they carry different structure: a method owned at magmas is still
  ambiguous on rings, since the comparison covers only the route to sets;
* registration rejects a comparison whose evidence is about other functors, whose sides are not
  structural routes between its endpoints, or which compares a route with itself.

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
    .comparison
      { id := ⟨id⟩
        source := rings.expression
        target := Foundation.Sets
        left := left
        right := right
        evidence := evidence }
  let carrier := `LeanCategories.Algebra.ringCarrierComparison
  if !(← rejects (comparison "cmp.probe.unrelated" multiplicative additive ``unrelatedIso)) then
    throwError "a comparison with unrelated evidence was accepted"
  if !(← rejects (comparison "cmp.probe.not_a_route"
      #[.functor FunctorId.ringsMultiplicative] additive carrier)) then
    throwError "a comparison whose side is not a route to its target was accepted"
  if !(← rejects (comparison "cmp.probe.self" multiplicative multiplicative carrier)) then
    throwError "a comparison of a route with itself was accepted"
  if ← rejects (comparison "cmp.probe.control" multiplicative additive carrier) then
    throwError "the carrier comparison was rejected"

end CasCatalogue.CohereProbes
