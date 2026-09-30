/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasLeaves.Algebra.RelabeledRings
public import CasCatalogue.CellCall
public import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.Standard
public meta import CasLeaves.Algebra.RelabeledRings
public meta import CasCatalogue.CellCall
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-cohere-exec` (CC-COHERE)

The ring diamond, over the relabeled-rings leaf (`CasLeaves.Algebra.RelabeledRings`, in the leaf
repository), which presents a ring's additive group with its elements relabeled (`Fin.rev`): the realized additive port is the Lean-native one followed by the relabeling, and its
square is the relabeling isomorphism. So the two routes from rings to sets, identified by the
registered comparison `cmp.rings.carrier` (the identity natural isomorphism between their
composites), give different presentations of the underlying set: element `e` of the ring is `e`
along the multiplicative route and `rev e` along the additive one.

* The comparison, applied to data, is its realized component: `rev`, not the identity, although
  the semantic comparison is the identity natural isomorphism.
* `cardinality` has the same value along either route; the call runs on the source route of the
  comparison (the multiplicative one), and reversing the comparison's direction moves the call to
  the other route: the direction, a registered datum, designates the route, not an order.
* Two registered comparisons between the same two routes are an ambiguity.
-/

open CategoryTheory Lean Meta Elab Term Command
open CasCatalogue.Algebra.Actions CasCatalogue.Algebra.RingTables CasCatalogue.Foundation.Actions
open CasCatalogue.Foundation.Cardinality

namespace CasCatalogue

open CasCatalogue.Algebra.RelabeledRings

namespace CohereExecProbes

/-- `𝔽₉ = 𝔽₃[x]/(x² + 1)`, presented by the relabeled-rings leaf. -/
def f9 : RelabeledRing := ⟨f9a⟩

/- The comparison applied to data is not the identity: element `e` along the multiplicative route
is `rev e` along the additive one. -/
#guard (List.finRange 9).all fun e =>
  (show Fin 9 from (cell% "cmp.rings.carrier" at (f9) in "cat.rings").hom e) == e.rev
#guard (show Fin 9 from (cell% "cmp.rings.carrier" at (f9) in "cat.rings").hom (0 : Fin 9)) != 0
#guard (List.finRange 9).all fun e =>
  (show Fin 9 from (cell% "cmp.rings.carrier" ≫ "cmp.rings.carrier"⁻¹
    at (f9) in "cat.rings").hom e) == e

/- The same value along either route. -/
#guard method% cardinality (f9) in "cat.rings" == ⟨CardinalHandle.finite 9⟩
#guard method% cardinality (f9) in "cat.rings" via "fun.rings.additive_group" ==
  method% cardinality (f9) in "cat.rings" via "fun.rings.multiplicative_monoid"

run_cmd liftTermElabM do
  let state ← registryState
  let some rings := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "cat.rings is not registered"
  let some carrier := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "cmp.rings.carrier is not registered"
  let runsOn (s : RegistryState) : MetaM (Option FunctorId) :=
    match s.resolveMethod rings.expression "cardinality" with
    | .ok r => pure r.route.functorIds[0]?
    | .error e => throwError e.render s
  -- The call runs on the comparison's source route, whatever the order of rows.
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

end CohereExecProbes

end CasCatalogue
