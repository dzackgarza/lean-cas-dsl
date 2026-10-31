/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

/-! Complete-family data recovery controls. These do not execute a mathematical
oracle, alter the selected formal object, or assert a backend answer. -/

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Harness.empty
  let some ringRow := state.objects.find? (·.id.raw == "obj.rings.integers_mod")
    | throwError "the existing ring family is absent"
  let some coefficientRow := state.objects.find? (·.id.raw == "obj.commutative_rings.integers_mod")
    | throwError "the existing coefficient family is absent"
  let some mapRow := state.morphisms.find? (·.id.raw == "mor.modules.matrix_linear_map")
    | throwError "the existing map family is absent"
  for modulus in #[5, 7] do
    let coefficients ← Semantic.object coefficientRow #[← exprToSyntax (mkNatLit modulus)] (some trace)
    let formalMap ← instantiateMVars (← elabTermAndSynthesize
      (← `(CasCatalogue.Algebra.LinearAlgebra.matrixLinearMap 2
        $(← exprToSyntax coefficients)
        (fun (i j : Fin 2) => if i = 0 ∧ j = 0 then 1 else 0))) none)
    Semantic.namedMorphism mapRow formalMap (some trace)
    let some (source, _) := Language.homEnds? (← inferType formalMap)
      | throwError "the original map lost its complete source"
    let scalar := source.getAppArgs[0]!
    let some recovered ← completeObjectFamilyApplication? ringRow.declaration scalar coefficients
      | throwError "the original published family lost its complete parameters"
    unless recovered.getAppArgs == coefficients.getAppArgs do
      throwError "whole-family recovery replaced the original parameter expressions"
    let scalarData := node ringRow.id.raw #[toJson modulus]
    unless (← parameterData trace scalar) == scalarData do
      throwError "parameter recovery lost the complete named family data"
    let actual ← realize harness trace "the original named map" formalMap
    let endpoint ← realizeCallableEndpoint harness trace actual source true
    unless endpoint.value == source && endpoint.owner?.isNone &&
        endpoint.json == node "obj.modules.vectors" #[scalarData, toJson (2 : Nat)] do
      throwError "the map endpoint lost its original full module and scalar parameter"

run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some ringRow := state.objects.find? (·.id.raw == "obj.rings.integers_mod")
    | throwError "missing ring family"
  let some coefficientRow := state.objects.find? (·.id.raw == "obj.commutative_rings.integers_mod")
    | throwError "missing coefficient family"
  let some finRow := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "missing finite-set family"
  let coefficients ← Semantic.object coefficientRow #[← `(5)] (some trace)
  let other ← Semantic.object coefficientRow #[← `(7)] (some trace)
  let action ← Semantic.edgeFunctor state (.functor FunctorId.commutativeRingsRings)
  let scalar ← whnfR (← Semantic.objOf action coefficients)
  let carrier ← mkAppM ``CommRingCat.carrier #[coefficients]
  let finite ← Semantic.object finRow #[← `(5)] none
  unless ← withTransparency .all <| isDefEq carrier finite do
    throwError "the equal-carrier control no longer separates an accidental point match"
  if (← completeObjectFamilyApplication? finRow.declaration carrier coefficients).isSome then
    throwError "agreement at one carrier selected an unrelated finite-set family"
  if (← completeObjectFamilyApplication? ringRow.declaration scalar other).isSome then
    throwError "a source absent from the original expression supplied its parameters"
  let pair ← mkAppM ``Prod.mk #[coefficients, other]
  let selected ← mkAppM ``Prod.fst #[pair]
  let selectedPair ← whnfR (← Semantic.objOf action selected)
  unless (← completeObjectFamilyApplication? ringRow.declaration selectedPair coefficients).isSome do
    throwError "the exact contributing occurrence was lost inside the full object"
  if (← completeObjectFamilyApplication? ringRow.declaration selectedPair other).isSome then
    throwError "an unrelated occurrence supplied parameters by a match at one value"

run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some ringRow := state.objects.find? (·.id.raw == "obj.rings.integers_mod")
    | throwError "missing ring family"
  let some coefficientRow := state.objects.find? (·.id.raw == "obj.commutative_rings.integers_mod")
    | throwError "missing coefficient family"
  let coefficients ← Semantic.object coefficientRow #[← `(5)] (some trace)
  let action ← Semantic.edgeFunctor state (.functor FunctorId.commutativeRingsRings)
  let original ← whnfR (← Semantic.objOf action coefficients)
  let named ← Semantic.object ringRow #[← `(5)] (some trace)
  let harness ← Harness.empty
  let foreign : Wire := {
    form := .object ringRow
    payload := .computed named (.owned "unrelated-parameter" 601
      (node "opaqueData" #[toJson "separately computed equal ring"])) }
  harness.results.modify (·.insert named foreign)
  let observed ← realizeEndpoint harness trace "the exact original parameter" original
  unless observed.value == original && observed.owner?.isNone &&
      observed.json == node ringRow.id.raw #[toJson (5 : Nat)] do
    throwError "whole-family recovery borrowed an equal cached object's data or owner"
  let actual := { foreign with payload := .computed original (.owned "actual-parameter" 602
    (node "opaqueData" #[toJson "actual retained parameter"])) }
  harness.results.modify (·.insert original actual)
  let retained ← realizeEndpoint harness trace "the retained actual parameter" original
  unless retained.value == original && retained.json == actual.json && retained.owner? == actual.owner? do
    throwError "whole-family recovery replaced actual retained data"
