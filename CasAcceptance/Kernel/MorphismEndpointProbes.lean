/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering checks of exact selected endpoints and callable dependencies.
The opaque token below supplies no mathematical value or proof. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_elab do
  for (field, objectText) in #[("source", "Fin(2)"), ("target", "Fin(3)")] do
    let text := "({0 ↦ 1, 1 ↦ 2} : Fin(2) → Fin(3))." ++ field ++ "()"
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the typed-map endpoint selector did not parse"
    let .ok expectedSyntax := Parser.runParserCategory (← getEnv) `cas_term objectText
      | throwError "the endpoint control did not parse"
    let trace ← Trace.new
    let selected ← (eval {} parsed).run { trace := some trace }
    let expected ← (eval {} expectedSyntax).run {}
    let selectedObject ← (semanticObject selected).run {}
    unless ← withTransparency .all <|
        isDefEq selectedObject (← (semanticObject expected).run {}) do
      throwError "the selector changed its original typed-map endpoint"
    let some (.structuredProjection receiver actualField none) ← trace.node? selectedObject
      | throwError "the endpoint discarded its original callable projection"
    let some (.contextualArrow ..) ← trace.node? receiver
      | throwError "the endpoint did not retain the complete Arrow construction"
    unless actualField == field do throwError "source and target endpoint ports were interchanged"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is absent"
  let object ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let base ← CategoryContext.ofNamed sets object
  let #[constructor] := state.constructors.filter
      (·.semantics == `CasCatalogue.Constructors.arrow)
    | throwError "the accepted Arrow constructor is not unique"
  let context ← CategoryContext.construct base constructor.id
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let source ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context)]
  let hom ← mkAppOptM ``CategoryTheory.CategoryStruct.id
    #[some (← CategoryContext.carrier context), some categoryStructure, some source]
  let endpoint : Value := .derivedObject source context #[]
  let receiver : Value := .derivedMorphism hom source source context (endpoint, endpoint)
  for field in #["source", "target"] do
    let trace ← Trace.new
    let some selected ← (structuredField receiver field).run { trace := some trace }
      | throwError "the derived complete morphism has no endpoint selector"
    let actualContext ← (objectContext selected).run {}
    unless actualContext.expression.syntacticEq context.expression &&
        (← withTransparency .all <| isDefEq actualContext.bundle context.bundle) do
      throwError "endpoint selection changed its complete derived category dictionary"
    let formal ← (semanticObject selected).run {}
    let harness ← Harness.empty
    let callable : Wire := {
      form := contextualForm state context (.diagrams sets) true
      payload := .computed hom (.opaque "endpoint-owner" 71 "retained callable")
      categoryContext := some context }
    harness.results.modify (·.insert hom callable)
    let projected ← realize harness trace "the unnamed selected endpoint" formal
    unless projected.owner? == callable.owner? &&
        (projected.json.compress.splitOn "retained callable").length > 1 do
      throwError "the unnamed endpoint lost its actual callable or owning session"
    unless ← withTransparency .all <| isDefEq projected.value source do
      throwError "the endpoint computation changed its formal selected object"
