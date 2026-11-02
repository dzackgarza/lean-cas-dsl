/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Command Term CategoryTheory
open CasCatalogue CasCatalogue.Language

/- Engineering checks of complete inclusion selection. Every map and proof below is an
existing upstream declaration or its direct specialization. Local row copies exercise the
reader only; no mathematical row, assertion or leaf is registered or changed. -/

private def readInclusionValue (text : String) : TermElabM Value := do
  let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the inclusion control did not parse: {text}"
  (eval {} term).run {}

private def inclusionInvalid (action : TermElabM Unit) : TermElabM Bool := do
  try
    action
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error

private def inclusionAmbiguous (action : TermElabM Unit) : TermElabM Bool := do
  try
    action
    pure false
  catch error =>
    if Exception.isSemanticAmbiguity error then pure true else throw error

run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["Fin(2) ⊆ Fin(2)", "Fin(2) ⊆ ZMod(2)",
      "(1 in Fin(2)) ∈ ZMod(2)", "ℕ ⊆ ℂ"] do
    withCurrHeartbeats do
      let .judged _ proposition ← readInclusionValue text
        | throwError "the applicable inclusion did not retain its question: {text}"
      unless proposition.isConstOf ``True do
        throwError "the applicable inclusion was not established: {text}"
  for text in #["Fin(2) ⊆ ZMod(3)", "(1 in Fin(2)) ∈ ZMod(3)",
      "Fin(2) ⊆ Fin(3)", "(1 in Fin(2)) ∈ Fin(3)"] do
    withCurrHeartbeats do
      unless ← inclusionInvalid (discard <| readInclusionValue text) do
        throwError "family reachability erased a concrete parameter: {text}"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let source ← readInclusionValue "Fin(2)"
  let target ← readInclusionValue "ZMod(2)"
  let other ← readInclusionValue "ZMod(3)"
  let point ← readInclusionValue "1 in Fin(2)"
  discard <| (coerceTo point target).run {}
  let .object _ sets .. := source | throwError "the selected finite source is not an object"
  let inferredParameter ← mkFreshExprMVar (mkConst ``Nat)
  let inferredCarrier ← mkAppM ``Foundation.Objects.fin #[inferredParameter]
  let expected := Value.object inferredCarrier sets none none none
  discard <| (coerceTo point expected).run {}
  unless (← instantiateMVars inferredParameter) == mkNatLit 2 do
    throwError "a successful identity coercion discarded its target-parameter inference"
  unless (← (coercionMap source other).run {}).isNone do
    throwError "an inapplicable inclusion supplied an element coercion"
  discard <| (complementOf target source).run {}
  unless ← inclusionInvalid (discard <| (complementOf other source).run {}) do
    throwError "a complement formed an image at the wrong target parameters"

/- These aliases specialize existing maps and their existing Mono proofs verbatim.
They introduce no mathematical proof or global registry entry. -/
private abbrev aliasResidues (n : Nat) := Foundation.Objects.integersMod n
private abbrev aliasFinInclusion (n : Nat) : Foundation.Objects.fin n ⟶ aliasResidues n :=
  Algebra.NumberSystems.finIntegersMod n
private abbrev aliasFinInclusionMono (n : Nat) : Mono (aliasFinInclusion n) :=
  Algebra.NumberSystems.finIntegersMod_mono n
private abbrev fixedFinInclusion := Algebra.NumberSystems.finIntegersMod 3
private abbrev fixedFinInclusionMono := Algebra.NumberSystems.finIntegersMod_mono 3
private abbrev finIdentity (n : Nat) := 𝟙 (Foundation.Objects.fin n)
private abbrev finIdentityMono (n : Nat) : Mono (finIdentity n) := inferInstance
private abbrev fixedFinIdentity := finIdentity 3
private abbrev fixedFinIdentityMono := finIdentityMono 3
private abbrev conditionalFinIdentity (n : Nat) (_h : n = 3) := finIdentity n
private abbrev conditionalFinIdentityMono (n : Nat) (h : n = 3) :
    Mono (conditionalFinIdentity n h) := finIdentityMono n
private abbrev finReversalMono (n : Nat) : Mono (Foundation.Morphisms.finRev n) :=
  Algebra.NumberSystems.mono_of_injective _ Fin.rev_injective
private abbrev finOneToThree := Foundation.Morphisms.finPoint 3 0 (Nat.zero_lt_succ 2)
private abbrev finOneToThreeMono : Mono finOneToThree :=
  Algebra.NumberSystems.mono_of_injective _ (Function.injective_of_subsingleton _)
private abbrev oneToPositiveFin (n : Nat) (h : 0 < n) :=
  Foundation.Morphisms.finPoint n 0 h
private abbrev oneToPositiveFinMono (n : Nat) (h : 0 < n) : Mono (oneToPositiveFin n h) :=
  Algebra.NumberSystems.mono_of_injective _ (Function.injective_of_subsingleton _)

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some general := state.inclusions.find? (·.id.raw == "incl.sets.fin_integers_mod")
    | throwError "the registered finite-position inclusion is absent"
  let fixed : InclusionEntry := { general with
    id := ⟨"engineering.inclusion.fixed_three"⟩, parameterization := .dependent
    declaration := ``fixedFinInclusion, mono := ``fixedFinInclusionMono }
  validateInclusion state.toSemanticState fixed
  let source ← readInclusionValue "Fin(2)"
  let target ← readInclusionValue "ZMod(2)"
  let targetTerm ← (semanticObject target).run {}
  let impossibleCycle : InclusionEntry := { general with
    id := ⟨"engineering.inclusion.fixed_identity_three"⟩, super := general.sub
    parameterization := .dependent, declaration := ``fixedFinIdentity
    mono := ``fixedFinIdentityMono }
  validateInclusion state.toSemanticState impossibleCycle
  let falsePremiseCycle : InclusionEntry := { impossibleCycle with
    id := ⟨"engineering.inclusion.conditional_identity"⟩
    declaration := ``conditionalFinIdentity, mono := ``conditionalFinIdentityMono }
  validateInclusion state.toSemanticState falsePremiseCycle
  for rows in #[#[fixed, impossibleCycle, falsePremiseCycle, general],
      #[general, falsePremiseCycle, impossibleCycle, fixed]] do
    let localState : RegistryState := { state with inclusions := rows }
    let trace ← Trace.new
    let some (path, arrow) ← (selectedInclusion? localState source general.super
        (some targetTerm)).run { trace := some trace }
      | throwError "an inapplicable first row suppressed the applicable inclusion"
    let #[selected] := path | throwError "the complete inclusion did not retain its one step"
    unless selected.id == general.id && (← isTypeCorrect arrow) do
      throwError "candidate order changed the complete selected inclusion"
    let nodes := (← trace.get).toArray.filterMap fun (_, node) => match node with
      | .namedInclusion id _ parameters _ _ => some (id, parameters)
      | _ => none
    let #[(id, parameters)] := nodes
      | throwError "speculative inclusion paths leaked into the selected trace"
    unless id == general.id && parameters == #[mkNatLit 2] do
      throwError "the inclusion trace lost its exact selected parameter"
    let parameter ← mkFreshExprMVar (mkConst ``Nat)
    let inferredTarget ← mkAppM ``Foundation.Objects.integersMod #[parameter]
    let some _ ← (selectedInclusion? localState source general.super
        (some inferredTarget)).run {}
      | throwError "the inclusion did not infer the complete dependent target"
    unless (← instantiateMVars parameter) == mkNatLit 2 do
      throwError "a discarded inclusion changed the selected operation parameter"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some general := state.inclusions.find? (·.id.raw == "incl.sets.fin_integers_mod")
    | throwError "the registered inclusion is absent"
  let aliasRow : InclusionEntry := { general with id := ⟨"engineering.inclusion.alias"⟩ }
  validateInclusion state.toSemanticState aliasRow
  let transparentRow : InclusionEntry := { general with
    id := ⟨"engineering.inclusion.transparent_alias"⟩
    declaration := ``aliasFinInclusion, mono := ``aliasFinInclusionMono }
  validateInclusion state.toSemanticState transparentRow
  let source ← readInclusionValue "Fin(2)"
  let target ← (semanticObject (← readInclusionValue "ZMod(2)")).run {}
  let mut selected : Array (Array InclusionId) := #[]
  for rows in #[#[general, aliasRow, transparentRow], #[transparentRow, aliasRow, general]] do
    let localState : RegistryState := { state with inclusions := rows }
    let some (path, _) ← (selectedInclusion? localState source general.super
        (some target)).run {}
      | throwError "the identical whole-map aliases were lost"
    selected := selected.push (path.map (·.id))
  unless selected[0]! == selected[1]! do
    throwError "storage order selected the representative of identical whole maps"
  let third ← readInclusionValue "Fin(3)"
  let identity ← (identityAt third).run {}
  let reversal ← elabTermAndSynthesize (← `(Foundation.Morphisms.finRev 3)) none
  unless ← sameInclusionMap identity identity do
    throwError "whole-map agreement rejected reflexivity"
  let unrelatedType ← mkFreshTypeMVar
  withLocalDeclD `unrelated unrelatedType fun _ => do
    unless ← sameInclusionMap identity identity do
      throwError "an unrelated unfinished local changed equality of closed maps"
  if (← sameInclusionMap identity reversal) || (← sameInclusionMap reversal identity) then
    throwError "a shared source and target erased different complete maps"

/- Sharing an equal intermediate prefix must not make the final route trace depend on
registry order. The two natural-to-integer rows consume the same upstream map and proof. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some first := state.inclusions.find? (·.id.raw == "incl.sets.naturals_integers")
    | throwError "the registered natural-to-integer inclusion is absent"
  let some second := state.inclusions.find? (·.id.raw == "incl.sets.integers_rationals")
    | throwError "the registered integer-to-rational inclusion is absent"
  let aliasRow : InclusionEntry := { first with id := ⟨"engineering.inclusion.middle_alias"⟩ }
  validateInclusion state.toSemanticState aliasRow
  let source ← readInclusionValue "ℕ"
  let target ← (semanticObject (← readInclusionValue "ℚ")).run {}
  let mut paths : Array (Array InclusionId) := #[]
  for rows in #[#[first, aliasRow, second], #[second, aliasRow, first]] do
    let localState : RegistryState := { state with inclusions := rows }
    let some (path, _) ← (selectedInclusion? localState source second.super (some target)).run {}
      | throwError "an equal intermediate prefix lost its complete continuation"
    paths := paths.push (path.map (·.id))
  unless paths[0]! == paths[1]! do
    throwError "registry order changed the representative of an equal intermediate prefix"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let first ← elabTermAndSynthesize (← `(Function.const Nat True.intro 0)) none
  let second ← elabTermAndSynthesize (← `(Function.const Nat True.intro 1)) none
  bindInclusionEndpoint first second
  let differentFirst ← elabTermAndSynthesize (← `(Nat.le_refl 0)) none
  let differentSecond ← elabTermAndSynthesize (← `(Nat.le_refl 1)) none
  unless ← inclusionInvalid (bindInclusionEndpoint differentFirst differentSecond) do
    throwError "proof irrelevance erased a complete independently fixed proposition"

/- Reflexive identity uses the same complete selected object. A same-family arrow with
different concrete endpoints remains a candidate, and an incompatible repetition terminates
its branch. These use only existing identities and the registered finite point. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let self : InclusionEntry := {
    id := ⟨"engineering.inclusion.identity"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.fin"⟩, super := ⟨"obj.sets.fin"⟩
    declaration := ``finIdentity, mono := ``finIdentityMono }
  validateInclusion state.toSemanticState self
  let localState : RegistryState := { state with inclusions := #[self] }
  let source ← readInclusionValue "Fin(2)"
  let target ← (semanticObject source).run {}
  let other ← (semanticObject (← readInclusionValue "Fin(3)")).run {}
  let some (path, _) ← (selectedInclusion? localState source self.super (some target)).run {}
    | throwError "the complete same-family identity was lost"
  unless path.any (·.id == self.id) do
    throwError "a same-family inclusion was discarded before checking its whole map"
  unless (← (coercionMap source source).run {}) matches some none do
    throwError "an explicitly reflexive coercion lost its identity"
  unless (← (selectedInclusion? localState source self.super (some other)).run {}).isNone do
    throwError "same-family identity changed its concrete parameter"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let point : InclusionEntry := {
    id := ⟨"engineering.inclusion.one_to_three"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.fin"⟩, super := ⟨"obj.sets.fin"⟩, parameterization := .dependent
    declaration := ``finOneToThree, mono := ``finOneToThreeMono }
  validateInclusion state.toSemanticState point
  let localState : RegistryState := { state with inclusions := #[point] }
  let source ← readInclusionValue "Fin(1)"
  let target ← (semanticObject (← readInclusionValue "Fin(3)")).run {}
  let some (path, _) ← (selectedInclusion? localState source point.super (some target)).run {}
    | throwError "a direct same-family inclusion with different parameters was discarded"
  unless path.map (·.id) == #[point.id] do
    throwError "a dependent same-family inclusion changed its selected route"
  let some general := state.inclusions.find? (·.id.raw == "incl.sets.fin_integers_mod")
    | throwError "the registered finite-position inclusion is absent"
  let residues ← (semanticObject (← readInclusionValue "ZMod(3)")).run {}
  let twoSteps : RegistryState := { state with inclusions := #[point, general] }
  let some (path, _) ← (selectedInclusion? twoSteps source general.super (some residues)).run {}
    | throwError "a repeated family hid the concrete intermediate parameter"
  unless path.map (·.id) == #[point.id, general.id] do
    throwError "the dependent two-step inclusion changed its selected path"
  let delayed : InclusionEntry := { point with
    id := ⟨"engineering.inclusion.positive_finite_point"⟩
    declaration := ``oneToPositiveFin, mono := ``oneToPositiveFinMono }
  validateInclusion state.toSemanticState delayed
  let arrow ← (inclusionMap #[delayed, general] source (some residues)).run {}
  unless ← isTypeCorrect arrow do
    throwError "the final target did not determine the earlier parameter and obligation"

/- Existing reversal and finite-position maps give different complete paths into the same
residue object. Both row orders must expose that choice before following further cycles. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some general := state.inclusions.find? (·.id.raw == "incl.sets.fin_integers_mod")
    | throwError "the registered inclusion is absent"
  let reversal : InclusionEntry := { general with
    id := ⟨"engineering.inclusion.reverse"⟩, super := general.sub
    declaration := ``Foundation.Morphisms.finRev, mono := ``finReversalMono }
  validateInclusion state.toSemanticState reversal
  let source ← readInclusionValue "Fin(3)"
  let target ← (semanticObject (← readInclusionValue "ZMod(3)")).run {}
  for rows in #[#[reversal, general], #[general, reversal]] do
    let localState : RegistryState := { state with inclusions := rows }
    for (targetId, selectedTarget) in #[(general.sub, ← (semanticObject source).run {}),
        (general.super, target)] do
      unless ← inclusionAmbiguous (discard <|
          (selectedInclusion? localState source targetId (some selectedTarget)).run {}) do
        throwError "a different applicable complete inclusion map was selected by row order"

/- The existing punctured-line inclusion carries a=0 as an explicit proof parameter.
The same family row at a=1 is inapplicable; no false premise is manufactured. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the registered category of sets is absent"
  let some domain := state.objects.find? (·.id.raw == "obj.sets.punctured_line")
    | throwError "the registered punctured-line family is absent"
  let some inclusion := state.inclusions.find? (·.id.raw == "incl.sets.punctured_units")
    | throwError "the registered conditional inclusion is absent"
  let reals ← readInclusionValue "ℝ"
  let target ← elabTermAndSynthesize (← `(Algebra.Units.units (MonCat.of ℝ))) none
  for (pointSyntax, applicable) in #[
      ((← `(Algebra.RealLimits.zeroPoint)), true),
      ((← `(Algebra.NamedRings.ringNumeral Algebra.NumberSystems.ringReals 1)), false)] do
    let point ← elabTermAndSynthesize pointSyntax none
    let sourceTerm ← mkAppM ``Algebra.RealLimits.puncturedLine #[point]
    let source := Value.object sourceTerm sets
      (some (domain, #[.element point reals])) none none
    let actual ← (selectedInclusion? state source inclusion.super (some target)).run {}
    unless actual.isSome == applicable do
      throwError "a conditional inclusion ignored its independently fixed premise"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let power ← powerObjectIn state CategoryId.sets
  let aliasRow : PowerObjectEntry := { power with id := ⟨"engineering.power.alias"⟩ }
  validatePowerObject state.toSemanticState aliasRow
  let ambient ← (semanticObject (← readInclusionValue "Fin(3)")).run {}
  let empty ← mkAppM power.empty #[ambient]
  let extent ← mkAppM power.extent #[ambient, empty]
  for rows in #[#[power, aliasRow], #[aliasRow, power]] do
    let localState : RegistryState := { state with powerObjects := rows }
    for accepts in #[(fun row : PowerObjectEntry => row.object == power.object),
        (fun row => row.omega == power.omega), (fun row => row.extent == power.extent)] do
      unless ← inclusionAmbiguous (discard <| selectedPowerObject? localState accepts
          "the unchanged selected structure") do
        throwError "power-object storage order chose one of two accepted structures"
    unless ← inclusionAmbiguous (discard <| Realize.extentOf? localState extent) do
      throwError "the extent reader selected a power-object row by storage order"
  let unique : RegistryState := { state with powerObjects := #[power] }
  let some selected ← selectedPowerObject? unique (·.object == power.object) "the selected family"
    | throwError "the unique selected power-object structure was lost"
  unless selected.id == power.id do throwError "the power-object selection changed its address"
  let some (selectedExtent, _, _) ← Realize.extentOf? unique extent
    | throwError "the unique complete extent lost its power-object structure"
  unless selectedExtent.id == power.id do throwError "the extent changed its selected address"
