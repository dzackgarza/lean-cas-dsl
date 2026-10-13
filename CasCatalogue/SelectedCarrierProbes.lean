module

import CasCatalogue.Language
import Mathlib.Algebra.Algebra.Bilinear
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Reader mechanics only. The probe uses an accepted group-valued construction, then reads
inversion at its generic element. It adds no operation row or mathematical expected answer. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some construction := state.functors.find? (·.id == FunctorId.coreSetsAutomorphisms)
    | throwError "selected-carrier probe has no accepted group-valued construction"
  let some groups := state.categories.find? (·.id == CategoryId.groups)
    | throwError "selected-carrier probe has no registered target category"
  let finite ← (object state "Fin" #[.nat 3] none).run {}
  let coreObject ← mkAppM ``CategoryTheory.Core.mk #[← (semanticObject finite).run {}]
  let formed ← Semantic.objOf (← registeredFunctorInstance construction) coreObject
  let selected := Value.object formed groups none none none
  let carrier ← (carrierObject selected).run {}
  let .object _ _ none (some retained) _ := carrier
    | throwError "an anonymous construction lost its selected structure at its carrier"
  unless retained.terms == selected.terms do
    throwError "taking a carrier replaced its selected construction"
  let identity ← (identityAt carrier).run {}
  let inverse ← (applyOperation "⁻¹" #[.element identity carrier] carrier).run
    { stage := some carrier }
  let .element inverseMap result := inverse
    | throwError "the constructed group did not inherit inversion"
  unless result.terms == carrier.terms && !(inverseMap.hasMVar) do
    throwError "inversion erased the selected carrier or retained unresolved parameters"
  unless ← isTypeCorrect inverseMap do
    throwError "the constructed group's inverse was outside its declared map type"

/- An indexed generator's bound comes from its instantiated signature, after all parameters. -/
run_cmd liftTermElabM do
  let signature ← elabTermAndSynthesize
    (← `(fun (_first second : Nat) (index : Fin second) => index)) none
  let applied := Lean.mkAppN signature #[Lean.mkNatLit 2, Lean.mkNatLit 5]
  let indexSyntax ← (generatorIndex applied 4).run {}
  let index ← elabTermAndSynthesize indexSyntax none
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType index)
      (Lean.mkApp (Lean.mkConst ``Fin) (Lean.mkNatLit 5)) do
    throwError "a generator index used an unrelated numerical parameter"
  let rejected ← try
      discard <| (generatorIndex applied 5).run {}
      pure false
    catch error =>
      if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "an out-of-bound declared generator index was admitted"

/- b0-selected-structure: the named map space and vector space have the same function
carrier, but each declaration retains its own identity in either candidate order. -/
run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let domain ← (object state "Fin" #[.nat 3] (some sets)).run {}
  let target ← (object state "Fin" #[.nat 5] (some sets)).run {}
  let maps ← (object state "Maps" #[domain, target] (some sets)).run {}
  let vectors ← (object state "Vec" #[target, .nat 3] (some sets)).run {}
  let mapsHandle ← (semanticObject maps).run {}
  let vectorsHandle ← (semanticObject vectors).run {}
  unless ← withTransparency .all <| isDefEq mapsHandle vectorsHandle do
    throwError "the map/vector probe does not have a shared carrier"
  let bare ← withTransparency .all <| whnf mapsHandle
  let rejected ← try
    discard <| (recognize state bare sets).run {}
    pure false
  catch error =>
    if Exception.isSemanticAmbiguity error || Exception.stratum? error == some .invalid then
      pure true
    else throw error
  unless rejected do
    throwError "a bare function carrier recovered an unselected named object"
  let anonymous := Value.object bare sets none none none
  let .object _ _ absentOrigin absentSelection _ ← (carrierObject anonymous).run {}
    | throwError "the anonymous carrier was not an object"
  unless absentOrigin.isNone && absentSelection.isNone do
    throwError "an unwitnessed carrier acquired a chosen presentation"
  for (source, identity) in #[(maps, "obj.sets.maps"), (vectors, "obj.sets.vectors")] do
    let witnessed := Value.object bare sets none none
      (some (#[source], source, #[], #[], #[]))
    let .object actual _ (some (origin, _)) _ _ ← (carrierObject witnessed).run {}
      | throwError "the recorded identity view lost its actual declared source"
    unless origin.id.raw == identity && (← isDefEq actual bare) do
      throwError "a recorded source view selected a different same-carrier declaration"
  unless (← (coercionMap vectors anonymous).run {}).isSome do
    throwError "the declared vector object cannot expose its supplied carrier"
  if (← (coercionMap anonymous vectors).run {}).isSome then
    throwError "the reverse carrier view recovered a vector declaration"
  let point := Value.element (← (identityAt vectors).run {}) vectors
  let .element _ retained ← (coerceTo point anonymous).run {}
    | throwError "the anonymous view discarded its supplied point"
  unless retained.declarations == vectors.declarations && retained.terms == vectors.terms do
    throwError "viewing a supplied carrier erased its declared vector provenance"
  for candidates in #[#[maps, vectors], #[vectors, maps]] do
    for (handle, identity) in #[(mapsHandle, "obj.sets.maps"),
        (vectorsHandle, "obj.sets.vectors")] do
      let recognized ← (recognize state handle sets candidates).run {}
      let .object actual _ (some (entry, _)) _ _ := recognized
        | throwError "a declared map/vector object lost its identity"
      unless entry.id.raw == identity && (← isDefEq actual handle) do
        throwError "candidate order replaced the declared map/vector object"
    let bare ← withTransparency .all <| whnf mapsHandle
    let ambiguous ← try
      discard <| (recognize state bare sets candidates).run {}
      pure false
    catch error =>
      if Exception.isSemanticAmbiguity error then pure true else throw error
    unless ambiguous do
      throwError "the shared function carrier selected a map/vector declaration"

/- b0-selected-structure: the existing zero and multiplication bilinear maps define
two complete forms on the same module. Taking their carriers must retain both choices. -/
run_cmd liftTermElabM do
  let state ← registryState
  let forms ← categoryNamed state "Bil"
  let sets ← categoryNamed state "Sets"
  let zeroForm ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ ℤ ℤ))) none
  let multiplicationForm ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (LinearMap.mul ℤ ℤ))) none
  let leftModule ← mkAppM
    ``LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.carrierObj #[zeroForm]
  let rightModule ← mkAppM
    ``LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.carrierObj #[multiplicationForm]
  unless ← withTransparency .all <| isDefEq leftModule rightModule do
    throwError "the chosen forms do not have the same complete module"
  if ← withTransparency .all <| isDefEq zeroForm multiplicationForm then
    throwError "the probe did not retain two distinct complete forms"
  let left := Value.object zeroForm forms none none none
  let right := Value.object multiplicationForm forms none none none
  let leftCarrier ← (carrierObject left).run {}
  let rightCarrier ← (carrierObject right).run {}
  for (carrier, selected) in #[(leftCarrier, zeroForm), (rightCarrier, multiplicationForm)] do
    let .object _ _ _ (some (.object actual category ..)) _ := carrier
      | throwError "taking a carrier erased its selected form"
    unless category.id == forms.id && (← isDefEq actual selected) do
      throwError "taking a carrier replaced its selected form"
  if (← (coercionMap leftCarrier rightCarrier).run {}).isSome ||
      (← (coercionMap rightCarrier leftCarrier).run {}).isSome then
    throwError "a carrier-only coercion identified distinct chosen forms"
  for candidates in #[#[left, right], #[right, left]] do
    for original in #[zeroForm, multiplicationForm] do
      let retained ← (recognize state original forms candidates).run {}
      unless ← isDefEq (← (semanticObject retained).run {}) original do
        throwError "recognition replaced the complete selected form"
    let bare ← (semanticObject leftCarrier).run {}
    let ambiguous ← try
      discard <| (recognize state bare sets candidates).run {}
      pure false
    catch error =>
      if Exception.isSemanticAmbiguity error then pure true else throw error
    unless ambiguous do
      throwError "the common carrier chose a bilinear form"

/- A dependent result retains the ambient prescribed by its input's registered inclusion.
The raw result carrier alone is not used to recover its named element presentation. -/
run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let some rings := state.categories.find? (·.id == CategoryId.commutativeRings)
    | throwError "the registered coefficient category is absent"
  let R ← (object state "ℂ" #[] (some rings)).run {}
  let D ← (object state "Poly∖0" #[R] (some sets)).run {}
  let some (_, ambient) ← (inclusionOut? D).run {}
    | throwError "the domain lost its declared inclusion"
  let polynomial ← (inclusionTargetValue D ambient sets).run {}
  let .object _ _ (some (expected, _)) _ _ := polynomial
    | throwError "the declared ambient is not its named presentation"
  let one ← (toElement (.nat 1) polynomial).run {}
  let admitted ← (admit D one).run {}
  let result ← (applyNamed state "factors" #[admitted]).run {}
  let .element _ (.object _ _ (some (_, #[elementSet])) _ _) := result
    | throwError "the dependent result lost its element-set parameter"
  let .object actual _ (some (entry, _)) _ _ := elementSet
    | throwError "the dependent result lost its prescribed ambient presentation"
  unless entry.id == expected.id && (← isDefEq actual ambient) do
    throwError "the dependent result substituted an unrelated same-carrier presentation"
  let numeral ← (toElement (.nat 1) elementSet).run {}
  for term in numeral.terms do
    unless !term.hasMVar && !term.hasLevelMVar && (← isTypeCorrect term) do
      throwError "the retained result presentation produced an ill-typed numeral"
