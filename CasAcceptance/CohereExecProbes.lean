/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.CellCall
public import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.CellCall
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-cohere-exec` (CC-COHERE)

The ring diamond, with a backend that presents a ring's additive group with its elements relabeled
(`Fin.rev`): the realized additive port is the Lean-native one followed by the relabeling, and its
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

namespace CasCatalogue.CohereExecProbes

/-! ### The backend's presentation of additive groups -/

/-- The additive-group table with its elements relabeled by `Fin.rev`. -/
def relabel (t : AddGroupTable) : AddGroupTable where
  size := t.size
  add x y := (t.add x.rev y.rev).rev
  zero := t.zero.rev
  neg x := (t.neg x.rev).rev
  add_assoc a b c := by simp [t.add_assoc]
  zero_add a := by simp [t.zero_add]
  neg_add_cancel a := by simp [t.neg_add_cancel]

/-- The relabeling, as an additive isomorphism onto the original table's group. -/
def relabelEquiv (t : AddGroupTable) : (relabel t).Carrier ≃+ t.Carrier where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev
  map_add' x y := by
    change (t.add x.rev y.rev).rev.rev = t.add x.rev y.rev
    exact Fin.rev_rev _

/-- Relabeling, on additive-group tables. -/
def relabelFunctor : AddGroupTables ⥤ AddGroupTables where
  obj := relabel
  map {t s} f := InducedCategory.homMk (AddGrpCat.ofHom
    ((relabelEquiv s).symm.toAddMonoidHom.comp (f.hom.hom.comp (relabelEquiv t).toAddMonoidHom)))
  map_id t := by
    apply InducedCategory.hom_ext; apply AddGrpCat.hom_ext; ext x
    exact Fin.rev_rev x
  map_comp f g := by
    apply InducedCategory.hom_ext; apply AddGrpCat.hom_ext; ext x
    change ((g.hom.hom (f.hom.hom x.rev)).rev) = ((g.hom.hom (f.hom.hom x.rev).rev.rev).rev)
    exact congrArg (fun y => (g.hom.hom y).rev) (Fin.rev_rev _).symm

/-- The relabeled presentation denotes the same group, up to the relabeling. -/
noncomputable def relabelIso : relabelFunctor ⋙ additiveGroupDenotation ≅ additiveGroupDenotation :=
  NatIso.ofComponents (fun t => (relabelEquiv t).toAddGrpIso) fun {t s} f => by
    apply AddGrpCat.ext
    intro x
    change (f.hom.hom x.rev).rev.rev = f.hom.hom x.rev
    exact Fin.rev_rev _

/-! ### The backend's rings -/

/-- A backend's ring: a ring table, reported by the backend. -/
structure BackendRing where
  table : RingTable

abbrev BackendRings : Type :=
  InducedCategory RingCat.{0} fun b : BackendRing => RingCat.of b.table.Carrier

def backendDenotation : BackendRings ⥤ LeanCategories.Algebra.Rings.{0} := inducedFunctor _

/-- The multiplicative port, as the Lean-native tables have it. -/
def backendToMonoid :
    RealizedAction (Algebra.Ports.ringsMultiplicative.{0}).toFunctor backendDenotation
      monoidDenotation :=
  RealizedAction.induced _ (fun b => b.table.toMonoidTable) fun _ => rfl

/-- The additive port, reported with relabeled elements: the Lean-native additive group followed
by the relabeling, with the pasted square. -/
noncomputable def backendToAdditiveGroup :
    RealizedAction (Algebra.Ports.ringsAdditive.{0}).toFunctor backendDenotation
      additiveGroupDenotation :=
  let native : RealizedAction (Algebra.Ports.ringsAdditive.{0}).toFunctor backendDenotation
      additiveGroupDenotation :=
    RealizedAction.induced _ (fun b => b.table.toAddGroupTable) fun b =>
      ringToAdditiveGroup_obj b.table
  ⟨native.action ⋙ relabelFunctor,
    ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft native.action relabelIso ≪≫
      native.square.iso⟩⟩

end CasCatalogue.CohereExecProbes

namespace CasCatalogue

register_leaf
  { backend := "probe-backend"
    contributions := [
  .realizer
  { id := ⟨"rz.rings.probe_backend"⟩, category := ⟨"cat.rings"⟩, backend := "probe-backend"
    denotation := `CasCatalogue.CohereExecProbes.backendDenotation },
  .action
  { id := ⟨"act.rings.multiplicative_monoid.probe_backend"⟩
    edge := .functor FunctorId.ringsMultiplicative
    realization := `CasCatalogue.CohereExecProbes.backendToMonoid },
  .action
  { id := ⟨"act.rings.additive_group.probe_backend"⟩, edge := .functor FunctorId.ringsAdditive
    realization := `CasCatalogue.CohereExecProbes.backendToAdditiveGroup }] }

namespace CohereExecProbes

/-- `𝔽₉ = 𝔽₃[x]/(x² + 1)`, reported by the backend. -/
def f9 : BackendRing := ⟨f9a⟩

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
