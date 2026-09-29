/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-props` (CC-PROP, CC-DECIDE)

* Commutativity is owned by the classifier `clf.magmas.commutative`. `is_abelian` on a group is
  that classifier reached along the multiplicative route `Grp → Mon → Semigrp → Magma` and decided
  by the one registered procedure: `ℤ/3` is abelian, `S₃` is not.
* On rings `is_commutative` stays ambiguous (additive vs multiplicative port) although the carrier
  comparison identifies the ports at sets; `is_abelian` is not available on rings at all.
* Registration rejects an "abelian groups" category introduced as an atom (it is a property
  subcategory of groups), a decider for a different property, and a property with no classifier.
* Decisions are three-valued with evidence: undecided never becomes a refutation under
  conjunction; equality of free-module maps given by differently computed but equal matrices is
  decided `true`, never `false`.
-/

open CategoryTheory Lean Meta Elab Command
open CasCatalogue.Algebra.Actions CasCatalogue.Modules.Actions

namespace CasCatalogue.PropsProbes

/-- `ℤ/3`, by its addition table read multiplicatively. -/
def z3 : GroupTable :=
  { size := 3, mul := fun a b => a + b, assoc := by decide, one := 0, one_mul := by decide
    mul_one := by decide, inv := fun a => -a, inv_mul := by decide }

/-- Multiplication in `S₃ = D₃`: index `i + 3j` is `rⁱ sʲ`, and `s rᵏ = r⁻ᵏ s`. -/
def s3mul (a b : Fin 6) : Fin 6 :=
  let i := a.val % 3
  let j := a.val / 3
  let k := b.val % 3
  let l := b.val / 3
  let i' := if j = 0 then (i + k) % 3 else (i + 3 - k) % 3
  ⟨(i' + 3 * ((j + l) % 2)) % 6, Nat.mod_lt _ (by decide)⟩

/-- Inverses in `S₃`: rotations invert, reflections are involutions. -/
def s3inv (a : Fin 6) : Fin 6 :=
  if a.val / 3 = 0 then ⟨(3 - a.val % 3) % 3, by omega⟩ else a

/-- The symmetric group `S₃`, by its multiplication table. -/
def s3 : GroupTable :=
  { size := 6, mul := s3mul, assoc := by decide, one := 0, one_mul := by decide
    mul_one := by decide, inv := s3inv, inv_mul := by decide }

/- `is_abelian` is commutativity of the multiplicative port, decided from the table. -/
#guard (ask% is_abelian (z3) in "cat.groups").answer == some true
#guard (ask% is_abelian (s3) in "cat.groups").answer == some false
#guard (ask% is_commutative (s3) in "cat.groups").answer == some false
#guard (ask% is_commutative (z3.toMagmaTable) in "cat.magmas").answer == some true

/- CC-DECIDE: undecided is never turned into a refutation. -/
#guard ((Decision.undecided : Decision (1 = 1)).and (Decision.undecided : Decision (2 = 2))).answer
  == none
#guard ((Decision.proved rfl : Decision (1 = 1)).and (Decision.undecided : Decision (2 = 2))).answer
  == none

/-- The swap of the two coordinates of `ℤ²`. -/
def swap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/- Pointwise-equal maps built differently (`swap ∘ swap` and `id`) are decided equal; distinct
maps are decided distinct. -/
#guard (decideMapEq (swap * swap) 1).answer == some true
#guard (decideMapEq swap 1).answer == some false

/-- An "abelian groups" category introduced as an atom: a property subcategory of groups. -/
noncomputable def abelianGroupsAtom : LeanCategories.ObjCat.{1, 0} :=
  Cat.of (ObjectProperty.FullSubcategory (C := GrpCat.{0}) fun G => ∀ a b : G, a * b = b * a)

noncomputable def abelianGroupsAtomRealization :
    CategoryRealization (.atom ⟨"cat.probe.abelian_groups"⟩) abelianGroupsAtom :=
  { familyFibre := none }

run_cmd liftTermElabM do
  let state ← registryState
  let category (id : String) : TermElabM CategoryExpr := do
    let some entry := state.categories.find? (·.id.raw == id)
      | throwError "{id} is not registered"
    pure entry.expression
  let rings ← category "cat.rings"
  let groups ← category "cat.groups"
  -- is_abelian on a group: the multiplicative route to magmas.
  match state.resolveProperty groups "is_abelian" with
  | .ok r =>
      unless r.route.refs == #[.functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
          .classifierForget ClassifierId.magmasAssociative] &&
          r.classifier.id == ClassifierId.magmasCommutative do
        throwError "unexpected: {state.renderPropertyResolution r}"
  | .error e => throwError e.render state
  -- The ports stay distinct for commutativity, even with the carrier comparison registered.
  match state.resolveProperty rings "is_commutative" with
  | .error (.ambiguousProperty _ candidates) =>
      unless candidates.size == 2 do throwError "expected the two ports"
  | .ok r => throwError "ring commutativity resolved: {state.renderPropertyResolution r}"
  | .error e => throwError "unexpected: {e.render state}"
  -- The alias is available on groups only.
  match state.resolveProperty rings "is_abelian" with
  | .error (.notApplicable ..) => pure ()
  | _ => throwError "is_abelian applied to rings"
  let failure (check : MetaM Unit) : MetaM (Option String) := do
    try check; pure none
    catch err => pure (some (← err.toMessageData.toString))
  -- An "abelian groups" atom is rejected: the property belongs to a classifier.
  match ← failure (validateRegistryEntryDeclaration (.category
      { id := ⟨"cat.probe.abelian_groups"⟩, declaration := ``abelianGroupsAtom
        expression := .atom ⟨"cat.probe.abelian_groups"⟩
        realization := ``abelianGroupsAtomRealization })) with
  | some message =>
      unless message.contains "property subcategory of cat.groups" do
        throwError "unexpected rejection: {message}"
  | none => throwError "an abelian-groups atom was accepted"
  -- A decider is accepted only for the property it decides.
  if (← failure (validateRegistryEntryDeclaration (.decider
      { id := ⟨"dec.probe.wrong"⟩, classifier := ClassifierId.magmasAssociative
        realization := ``commutativeDecider }))).isNone then
    throwError "a commutativity decider was accepted for associativity"
  if (← failure (validateRegistryEntryDeclaration (.property
      { id := ⟨"prop.probe.unowned"⟩, name := "is_abelian"
        classifier := ⟨"clf.probe.unregistered"⟩ }))).isNone then
    throwError "a property without a registered classifier was accepted"
  -- Controls.
  for decider in state.deciders do
    if let some message ← failure (validateRegistryEntryDeclaration (.decider decider)) then
      throwError "registered decider {decider.id.raw} fails re-validation: {message}"

end CasCatalogue.PropsProbes
