/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.Semantic
public meta import CasAcceptance.Standard
public meta import CasCatalogue.Semantic

@[expose] public section

/-!
# Acceptance for `cc-props` (CC-PROP)

* Commutativity is owned by the classifier `clf.magmas.commutative`. `is_abelian` on a group is
  that classifier reached along the multiplicative route `Grp → Mon → Semigrp → Magma`; the
  semantic reading of `G.is_abelian()` is `Classifier.Holds` of the classifier at the image of
  `G` along that route, recorded as the property after its route.
* On rings `is_commutative` stays ambiguous (additive vs multiplicative port) although the carrier
  comparison identifies the ports at sets; `is_abelian` is not available on rings at all.
* Registration rejects an "abelian groups" category introduced as an atom (it is a property
  subcategory of groups), and a property with no classifier.

Whether a property holds of a value is a statement of the language: decided in Lean, or answered
three-valued by an admitted registration and compared, never supplied with evidence by a leaf.
-/

open CategoryTheory Lean Meta Elab Command

namespace CasCatalogue.PropsProbes

/-- An "abelian groups" category introduced as an atom: a property subcategory of groups. -/
noncomputable def abelianGroupsAtom : LeanCategories.ObjCat.{1, 0} :=
  Cat.of (ObjectProperty.FullSubcategory (C := GrpCat.{0}) fun G => ∀ a b : G, a * b = b * a)

noncomputable def abelianGroupsAtomRealization :
    CategoryRealization (.atom ⟨"cat.probe.abelian_groups"⟩) abelianGroupsAtom :=
  { familyFibre := none }

run_cmd liftTermElabM do
  let state ← registryState
  let category (id : String) : TermElabM NamedCategoryEntry := do
    let some entry := state.categories.find? (·.id.raw == id)
      | throwError "{id} is not registered"
    pure entry
  let rings ← category "cat.rings"
  let groups ← category "cat.groups"
  -- is_abelian on a group: the multiplicative route to magmas.
  match state.resolveProperty groups.expression "is_abelian" with
  | .ok r =>
      unless r.route.refs == #[.functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
          .classifierForget ClassifierId.magmasAssociative] &&
          r.classifier.id == ClassifierId.magmasCommutative do
        throwError "unexpected: {state.renderPropertyResolution r}"
  | .error e => throwError e.render state
  -- The ports stay distinct for commutativity, even with the carrier comparison registered.
  match state.resolveProperty rings.expression "is_commutative" with
  | .error (.ambiguousProperty _ candidates) =>
      unless candidates.size == 2 do throwError "expected the two ports"
  | .ok r => throwError "ring commutativity resolved: {state.renderPropertyResolution r}"
  | .error e => throwError "unexpected: {e.render state}"
  -- The alias is available on groups only.
  match state.resolveProperty rings.expression "is_abelian" with
  | .error (.notApplicable ..) => pure ()
  | _ => throwError "is_abelian applied to rings"
  -- The semantic reading of `is_finite` of a named set: `Holds` of the classifier at the set,
  -- recorded as the property after its (empty) route.
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "cat.sets is not registered"
  let some integers := state.objects.find? (·.id.raw == "obj.sets.integers")
    | throwError "obj.sets.integers is not registered"
  let trace ← (Trace.new : IO _)
  let Z ← Semantic.object integers #[] (some trace)
  let holds ← Semantic.property "is_finite" Z sets (some trace)
  unless holds.isAppOf ``CasCatalogue.Classifier.Holds do
    throwError "the property is not `Classifier.Holds`"
  let some (.property id route _) ← (trace.node? holds : IO _)
    | throwError "the property is not recorded"
  unless id.raw == "prop.is_finite" && route.isEmpty do
    throwError "recorded as {id.raw} after {route.size} steps"
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
  if (← failure (validateRegistryEntryDeclaration (.property
      { id := ⟨"prop.probe.unowned"⟩, name := "is_abelian"
        classifier := ⟨"clf.probe.unregistered"⟩ }))).isNone then
    throwError "a property without a registered classifier was accepted"
  -- Controls: the registered properties re-validate.
  for property in state.properties do
    if let some message ← failure (validateRegistryEntryDeclaration (.property property)) then
      throwError "registered property {property.id.raw} fails re-validation: {message}"

end CasCatalogue.PropsProbes
