/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

/-! Engineering checks for computational dependency and projection machinery. The deliberately
invented returned fields below test data flow only; they assert no mathematical correctness. -/

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the registered set category is unavailable"
  let formal ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let input : Realize.Wire := {
    form := .diagrams sets
    payload := .computed formal (.owned "probe" 17 (toJson "actual returned data")) }
  let forwarded : Realize.Wire := {
    form := input.form
    payload := (← Realize.combinedPayload formal (toJson "dependent request") #[input]) }
  unless forwarded.owner? == some ("probe", 17) do
    throwError "combining a dependent request lost its live owning session"
  let portable : Realize.Wire := {
    form := input.form, payload := .computed formal (.inline (toJson "portable result")) }
  let combined ← Realize.combinedPayload formal (toJson "composed data") #[portable]
  unless (match combined with | .computed _ (.inline _) => true | _ => false) do
    throwError "a portable computation was reclassified as a formal input"
  let foreign : Realize.Wire := {
    form := input.form, payload := .computed formal (.owned "probe" 18 (toJson "foreign")) }
  let mixed ← try
    discard <| Realize.combinedPayload formal (toJson "mixed") #[input, foreign]
    pure false
  catch _ => pure true
  unless mixed do throwError "data from different live sessions was combined"

run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "the registered pullback constructor is unavailable"
  let object ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let diagram ← mkAppM ``CategoryTheory.Limits.cospan #[identity, identity]
  let left ← elabTermAndSynthesize (← `(CategoryTheory.Limits.WalkingCospan.left)) none
  let right ← elabTermAndSynthesize (← `(CategoryTheory.Limits.WalkingCospan.right)) none
  let centre ← elabTermAndSynthesize (← `(CategoryTheory.Limits.WalkingCospan.one)) none
  let first := toJson "actual first returned leg"
  let second := toJson "actual second returned leg"
  let answer := Json.mkObj [("ctor", "cone"),
    ("args", Json.arr #[toJson "actual returned apex", first, second])]
  for (index, expected) in #[(left, first), (right, second)] do
    let .ok actual ← StructuredResult.projectData row diagram answer index
      | throwError "the complete constructor did not project a direct leg"
    unless actual == expected do
      throwError "equal formal endpoints conflated distinct returned defining maps"
  let input := toJson "independently retained diagram arrow"
  let .ok composite ← StructuredResult.projectData row diagram answer centre
      (fun _ => pure (.ok input))
    | throwError "the constructor's composite defining leg could not reuse its returned field"
  let .ok "compose" := composite.getObjValAs? String "ctor"
    | throwError "the composite defining leg lost categorical composition"
  let .ok #[actualFirst, actualInput] := (composite.getObjVal? "args").bind (·.getArr?)
    | throwError "the composite defining leg lost an operand"
  unless actualFirst == first && actualInput == input do
    throwError "the composite defining leg substituted a canonical map for returned data"

run_elab do
  let state ← registryState
  let some kernel := state.functors.find? (·.id.raw == "fun.arrows_groups.kernel")
    | throwError "the published kernel action is unavailable"
  let some domain := state.functors.find? (·.id.raw == "fun.subobjects_groups.domain")
    | throwError "the published subobject domain is unavailable"
  let some inclusion := state.functors.find? (·.id.raw == "fun.subobjects_groups.inclusion")
    | throwError "the published complete inclusion is unavailable"
  let sign ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.FiniteGroups.sign 3)) none
  let source ← mkAppM ``CategoryTheory.Arrow.mk #[sign]
  let fixed ← Semantic.objOf (← instantiateFresh kernel.declaration) source
  let trace ← Trace.new
  let data := #[toJson "actual apex", toJson "actual ambient", toJson "actual inclusion"]
  let packet := Json.mkObj [("ctor", "subobject"), ("args", Json.arr data)]
  let some apex ← Realize.projectObjectAction trace domain.source (.functor domain.id)
      (← instantiateFresh domain.declaration) fixed packet
    | throwError "the generic domain action did not recognize its structural projection"
  unless apex == data[0]! do throwError "the domain action lost the returned apex"
  let some arrow ← Realize.projectObjectAction trace inclusion.source (.functor inclusion.id)
      (← instantiateFresh inclusion.declaration) fixed packet
    | throwError "the generic inclusion action did not recognize its structural projection"
  unless arrow == Json.mkObj [("ctor", "arrow"), ("args", Json.arr data)] do
    throwError "the complete inclusion action lost a returned endpoint or defining map"
