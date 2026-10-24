/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering checks of complete public field and family-transport interfaces.
The opaque fields exercise ownership and framing; they claim no mathematical answers. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue CasCatalogue.Language

private def parse (text : String) : TermElabM Syntax := do
  let .ok result := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the public structured execution form did not parse: {text}"
  return result

private def opaqueField (name : String) : Json :=
  Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #[toJson name])]

private def valueTerm : Value → TermElabM Expr
  | .object value .. | .derivedObject value .. | .morphism value .. |
      .derivedMorphism value .. => pure value
  | _ => throwError "the structured field did not retain a whole typed value"

run_elab do
  let state ← registryState
  let mut checked := false
  for row in state.presentations do
    if checked then break
    let declaration ← mkConstWithFreshMVarLevels row.declaration
    if (← inferType declaration).isForall then continue
    let source := state.objects.find? (·.id == row.source)
    unless source.any (·.category == CategoryId.sets) do continue
    let trace ← Trace.new
    let forward ← (eval {} (← parse s!"presentation(«{row.id.raw}»())")).run { trace := some trace }
    let backward ← (eval {} (← parse s!"inverse_presentation(«{row.id.raw}»())")).run
      { trace := some trace }
    let (f, source, target, _, _, _) ← (morphismContext forward).run {}
    let (g, reverseSource, reverseTarget, _, _, _) ← (morphismContext backward).run {}
    unless ← isDefEq source reverseTarget <&&> isDefEq target reverseSource do
      throwError "the public presentation selectors changed a complete directed endpoint"
    for (hom, inverse) in #[(f, false), (g, true)] do
      let some (.presentation id _ direction) ← trace.node? hom
        | throwError "a whole public presentation lost its accepted comparison"
      unless id == row.id && direction == inverse do
        throwError "a whole public presentation changed its accepted direction"
    let mapped ← (eval {} (← parse "map selected along Aut()")).run
      { trace := some trace, bound := [(`selected, forward)] }
    let (hom, _, _, _, _, _) ← (morphismContext mapped).run {}
    unless ← isTypeCorrect hom do
      throwError "the registered core construction did not consume the whole selected isomorphism"
    checked := true
  unless checked do throwError "no accepted closed set presentation exercised the complete public selectors"

run_elab do
  let trace ← Trace.new
  let receiver ← (eval {} (← parse "kernel(sign(3))")).run { trace := some trace }
  let object ← valueTerm receiver
  let context ← (objectContext receiver).run {}
  let some plan ← StructuredProjection.construction? object context (some trace)
    | throwError "the ordinary result lost its complete accepted universal presentation"
  let ports ← plan.dataPlan
  let data := Json.mkObj [("ctor", if plan.row.colimit then "cocone" else "cone"),
    ("args", Json.arr (ports.ports.map fun port => opaqueField s!"returned port {port.index}"))]
  let .ok result ← StructuredResult.complete plan.row plan.diagram (opaqueField "input diagram")
      (.direct data) plan.presentation (fun data => StructuredResult.validateData
        plan.row plan.diagram plan.presentation data ComputationalData.validatePort)
    | throwError "the complete engineering packet failed its independent framing"
  let harness ← Realize.Harness.empty
  harness.results.modify (·.insert object {
    form := .limitApex plan.row
    payload := .construction result (.owned "structured-probe" 37)
    categoryContext := some context })
  let objectValue ← (eval {} (← parse "K.obj()")).run
    { trace := some trace, bound := [(`K, receiver)] }
  unless ← isDefEq object (← valueTerm objectValue) do
    throwError "ordinary obj() changed the complete constructed apex"
  let selected ← (eval {} (← parse "K.hom()")).run
    { trace := some trace, bound := [(`K, receiver)] }
  let hom ← valueTerm selected
  let port ← plan.selectPort none
  let firstKey ← StructuredProjection.retainPortValue object port.formalField 0
  let secondKey ← StructuredProjection.retainPortValue object port.formalField 1
  unless firstKey != secondKey && (← withTransparency .all <| isDefEq firstKey secondKey) do
    throwError "equal formal fields erased their distinct retained data-port addresses"
  unless ← withTransparency .all <| isDefEq hom port.formalField do
    throwError "ordinary hom() changed its unique declared morphism port"
  let wire ← Realize.realize harness trace "the ordinary defining map" hom
  unless wire.owner? == some ("structured-probe", 37) do
    throwError "the ordinary defining map discarded its original owning session"
  let .ok ("constructionField", #[id, _, packet, index]) := ComputationalData.envelope wire.json
    | throwError "the ordinary field lost its complete construction packet"
  unless id.getStr? == .ok plan.row.id.raw && packet == result.json &&
      index.getNat? == .ok port.index do
    throwError "the ordinary field changed its construction or exact port address"
  let explicit ← (eval {} (← parse s!"K.field({port.index})")).run
    { trace := some trace, bound := [(`K, receiver)] }
  unless ← withTransparency .all <| isDefEq (← valueTerm explicit) hom do
    throwError "explicit data-port selection changed its actual formal field"
  let refused ← try
    discard <| (eval {} (← parse s!"K.field({ports.ports.size})")).run
      { trace := some trace, bound := [(`K, receiver)] }
    pure false
  catch error =>
    if Exception.interpretationKind error == .invalid then pure true else throw error
  unless refused do throwError "an out-of-range declared structured field was admitted"

run_elab do
  let trace ← Trace.new
  let receiver ← (eval {} (← parse "Alt(3)")).run { trace := some trace }
  let object ← valueTerm receiver
  let context ← (objectContext receiver).run {}
  let some plan ← StructuredProjection.arrow? object context
    | throwError "the ordinary subobject lost its full declared interface"
  let some category := CategoryContext.named? (← registryState) context.expression
    | throwError "the selected complete category is absent"
  let data := Json.mkObj [("ctor", "subobject"), ("args", Json.arr #[
    opaqueField "returned source", opaqueField "returned ambient", opaqueField "returned inclusion"])]
  let harness ← Realize.Harness.empty
  harness.results.modify (·.insert object {
    form := .subobject category
    payload := .computed object (.owned "structured-probe" 38 data)
    categoryContext := some context })
  for field in #["obj", "source", "target", "hom", "inclusion"] do
    let selected ← (eval {} (← parse s!"K.{field}()")).run
      { trace := some trace, bound := [(`K, receiver)] }
    let formal ← valueTerm selected
    let (expected, target, morphism) ← plan.field field
    unless ← withTransparency .all <| isDefEq formal expected do
      throwError "a structured field changed its accepted projection"
    if !morphism then CategoryContext.checkObject target formal
    let wire ← Realize.realize harness trace "the ordinary subobject field" formal
    unless wire.owner? == some ("structured-probe", 38) do
      throwError "a subobject projection discarded its original owning session"
  let action ← plan.projectionFunctor "source"
  let (parameters, _) ← Realize.realizedParameters harness trace #[plan.base.bundle]
  let categoryData := Json.mkObj [("ctor", "constructedCategory"),
    ("args", Json.arr #[toJson ConstructorId.subobjects.raw, Json.arr parameters])]
  let actionData := Json.mkObj [("ctor", "structuredProjectionAction"),
    ("args", Json.arr #[categoryData, toJson "source"])]
  if let .error message ← ComputationalData.validateAction action actionData then
    throwError "the complete structured projection action failed validation: {message}"

run_elab do
  let state ← registryState
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the accepted family schema is absent"
  let receiver ← elabTermAndSynthesize (← `(ModuleCat.of (ZMod 2) (ZMod 2))) none
  let base ← elabTermAndSynthesize (← `(RingCat.ofHom (Int.castRingHom (ZMod 2)))) none
  let context ← CategoryContext.ofNamed modules receiver
  let plan ← ReindexAction.resolve base context
  let image ← ReindexAction.object plan receiver
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[receiver]
  let imageMap ← ReindexAction.map plan identity
  CategoryContext.checkMorphism plan.target imageMap image image
  let (cartesian, source, target) ← ReindexAction.cartesian plan receiver
  CategoryContext.checkMorphism plan.total cartesian source target
  let trace ← Trace.new
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the base category is absent"
  let some (baseSource, baseTarget) := homEnds? (← inferType base)
    | throwError "the selected original base map has no categorical endpoints"
  let moduleValue : Value := .object receiver modules none none none
  let baseValue : Value := .morphism base baseSource baseTarget rings none
  for (text, expected) in #[("reindex(M, phi)", image),
      ("reindex(id(M), phi)", imageMap), ("cartesian(M, phi)", cartesian),
      (s!"view M along «{plan.entry.id.raw}»(phi)", image),
      (s!"map id(M) along «{plan.entry.id.raw}»(phi)", imageMap)] do
    let value ← (eval {} (← parse text)).run
      { trace := some trace, bound := [(`M, moduleValue), (`phi, baseValue)] }
    unless ← withTransparency .all <| isDefEq (← valueTerm value) expected do
      throwError "the public family selector changed its complete accepted transport"
  for (formal, field) in #[(cartesian, "hom"), (source, "source"), (target, "target")] do
    Trace.record (some trace) formal (.cartesian plan.entry.id plan.parameters base receiver field)
  let harness ← Realize.Harness.empty
  harness.results.modify (·.insert receiver {
    form := .diagrams modules
    payload := .computed receiver (.owned "family-probe" 41 (opaqueField "original fibre object"))
    categoryContext := some context })
  harness.results.modify (·.insert base {
    form := .canonicalMorphism rings
    payload := .computed base (.owned "family-probe" 41 (opaqueField "original nonidentity base map")) })
  let selectedMap ← Realize.realize harness trace "the explicit complete family map action" imageMap
  unless selectedMap.owner? == some ("family-probe", 41) do
    throwError "the explicit functor map discarded its original owners"
  let .ok ("map", #[descriptor, _]) := ComputationalData.envelope selectedMap.json
    | throwError "the explicit functor map lost its full public action descriptor"
  let .ok (id, arguments) := ComputationalData.envelope descriptor
    | throwError "the selected functor descriptor is incomplete"
  unless id == plan.entry.id.raw && arguments == #[opaqueField "original nonidentity base map"] do
    throwError "the explicit action erased its complete original base-morphism parameter"
  for formal in #[cartesian, source, target] do
    let wire ← Realize.realize harness trace "the canonical cartesian selection" formal
    unless wire.owner? == some ("family-probe", 41) do
      throwError "the cartesian map or endpoint discarded its original owner dependencies"
  let wire ← Realize.realize harness trace "the full cartesian callable" cartesian
  if let .error message ← ComputationalData.validateCallableAt #[] (← inferType cartesian) wire.json then
    throwError "the cartesian callable lost its full typed interface: {message}"
  let some operation := state.operation? plan.entry.cartesianAddress
    | throwError "the cartesian callable lost its declared operation address"
  let some form := state.cartesianForm? plan.entry.cartesianAddress
    | throwError "the cartesian callable lost its declared full input form"
  unless (state.rejects operation form).isNone do
    throwError "the cartesian operation rejected its complete accepted family invocation"

run_elab do
  let trace ← Trace.new
  let receiver ← (eval {} (← parse "Fin(2) in FiniteSets")).run { trace := some trace }
  let object ← valueTerm receiver
  let context ← (objectContext receiver).run {}
  let .classifierTotal classifier := context.expression
    | throwError "the accepted proof refinement lost its classifier total category"
  let edge := EdgeRef.classifierForget classifier
  let action ← Semantic.edgeFunctor (← registryState) edge
  let expected ← Semantic.objOf action object
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
  let expectedMap ← Semantic.mapOf action identity
  for (written, formal) in #[(s!"view X along «{classifier.raw}»()", expected),
      (s!"map id(X) along «{classifier.raw}»()", expectedMap)] do
    let selected ← (eval {} (← parse written)).run
      { trace := some trace, bound := [(`X, receiver)] }
    unless ← withTransparency .all <| isDefEq (← valueTerm selected) formal do
      throwError "the exact classifier selector changed its accepted action"
  let some category := CategoryContext.named? (← registryState) context.expression
    | throwError "the accepted proof refinement category is absent"
  let harness ← Realize.Harness.empty
  harness.results.modify (·.insert object {
    form := .diagrams category
    payload := .computed object (.owned "classifier-probe" 43 (opaqueField "complete classified object"))
    categoryContext := some context })
  for formal in #[expected, expectedMap] do
    let wire ← Realize.realize harness trace "the complete selected classifier action" formal
    unless wire.owner? == some ("classifier-probe", 43) do
      throwError "a classifier action discarded its original complete object's owner"

run_elab do
  let state ← registryState
  let some row := state.binders.find? (·.id.raw == "bind.sets.real_series")
    | throwError "the accepted binder is absent"
  let index ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let operation ← mkAppM row.operation #[index]
  let some (source, target) := homEnds? (← inferType operation)
    | throwError "the accepted binder lost its whole family signature"
  let some sets := state.categories.find? (·.id == row.category)
    | throwError "the accepted binder category is absent"
  let family ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let input : Value := .object source sets none none none
  let whole : Value := .morphism family source source sets (some (input, input))
  let trace ← Trace.new
  let result ← (eval {} (← parse s!"binder(«{row.id.raw}»(Fin(2)), A)")).run
    { trace := some trace, bound := [(`A, whole)] }
  let (hom, domain, actualTarget, _, _, _) ← (morphismContext result).run {}
  unless ← isDefEq domain source <&&> isDefEq actualTarget target do
    throwError "the explicit binder changed its original generalized domain or result"
  let some (.binder id parameters declaredIndex _ admitted) ← trace.node? hom
    | throwError "the explicit binder lost its exact accepted family invocation"
  unless id == row.id && parameters.size == 1 &&
      (← isDefEq declaredIndex index) && (← isDefEq admitted family) do
    throwError "the explicit binder changed its selected parameters or complete admitted family"
