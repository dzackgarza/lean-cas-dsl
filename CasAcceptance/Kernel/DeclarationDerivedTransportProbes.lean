/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Bounded engineering controls derived from the loaded mathematical declarations.
The sample domain is closed, parameter-free registered objects and morphisms;
route applications retain all parameters inferred from their actual full source.
No route inventory, mathematical row, default parameter or backend is supplied.
Opaque/portable packets below witness data flow only. No process is started and
no packet establishes a mathematical value, equation or isofibration property. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasCatalogue.DeclarationDerivedTransportProbes
meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def closedDeclaration? (declaration : Name) : TermElabM (Option Expr) := do
  let info ← getConstInfo declaration
  -- Do not choose a universe, a declaration parameter or a typeclass instance.
  if !info.levelParams.isEmpty || info.type.isForall then return none
  let value := Lean.mkConst declaration
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do
    throwError "a closed registered declaration is not well typed: {declaration}"
  return some value

private def same (left right : Expr) : TermElabM Bool := do
  withoutModifyingState <| withTransparency .all <|
    isDefEq (← inferType left) (← inferType right) <&&> isDefEq left right

private def reject (fragment : String) (work : TermElabM α) : TermElabM Unit := do
  let refused ← withoutModifyingState do
    try
      discard <| work
      return false
    catch error =>
      let message ← error.toMessageData.toString
      unless (message.splitOn fragment).length > 1 do throw error
      return true
  unless refused do throwError "a declaration-derived negative control accepted: {fragment}"

private def report (kind : String) (fields : List (String × Json)) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_DECLARATION_DERIVED_REPORT" then
    let data := Json.mkObj (("case", toJson kind) ::
      ("scope", toJson "Engineering retention controls; no computational or mathematical acceptance") :: fields)
    IO.FS.withFile path .append fun output => output.putStrLn data.compress

private def routeData (route : Route) (applications : Array Expr) : Json :=
  Json.mkObj [("steps", toJson (route.refs.map EdgeRef.label)),
    ("applications", toJson (applications.map reprStr))]

private structure ImageCase where
  route : Route
  applications : Array Expr
  image : Expr
  operation : Expr

private def selectedProduct (entry : OperationEntry) (image : Expr)
    (context : CategoryContext) : TermElabM Expr := do
  let receiver ← (objectInContext image context).run {}
  let #[(application, sources)] ← (selectedOperationApplicationsWithSources
      entry.declaration entry.category receiver #[] (some entry.name)).run {}
    | throwError "the complete selected monoid did not retain one published multiplication"
  unless sources.any (fun source => source.receiver == image) do
    throwError "the selected operation discarded its exact complete receiver"
  return application

-- Equal returned packets never select a whole action, source occurrence or endpoint.
-- The portable marker is a deliberately untrusted valueData payload, not an answer.
private def checkReuse (record : ActionExecution) (otherAction : Expr) : TermElabM Unit := do
  let harness ← Harness.empty
  retainActionResult harness record
  let find (action : Expr) (input : Wire) (parameters : Array Json)
      (dependencies images : Array Wire) :=
    retainedActionResult? harness record.operation action input parameters dependencies images
  let some actual ← find record.action record.input record.parameters
      record.parameterInputs record.imageEndpoints
    | throwError "the exact live-declaration action receipt was not reusable"
  unless actual.value == record.result.value && actual.json == record.result.json do
    throwError "reusing untrusted data changed its original formal question or returned packet"
  unless (← find otherAction record.input record.parameters
      record.parameterInputs record.imageEndpoints).isNone do
    throwError "equal returned data identified two complete selected actions"
  let foreignPayload := WirePayload.computed record.input.value
    (.owned "different-original-session" 92 record.input.json)
  let foreign := { record.input with payload := foreignPayload }
  unless (← find record.action foreign record.parameters
      record.parameterInputs record.imageEndpoints).isNone do
    throwError "the action receipt ignored the original supplier occurrence"
  let changed := { record.input with
    payload := .computed record.input.value (.inline (toJson "a different actual input packet")) }
  unless (← find record.action changed record.parameters
      record.parameterInputs record.imageEndpoints).isNone do
    throwError "the action receipt substituted another actual packet of the same formal value"
  unless (← find record.action record.input (record.parameters.push (toJson "extra data"))
      record.parameterInputs record.imageEndpoints).isNone do
    throwError "the action receipt ignored a changed complete parameter vector"
  if !record.imageEndpoints.isEmpty then
    unless (← find record.action record.input record.parameters
        record.parameterInputs #[]).isNone do
      throwError "a map action receipt omitted its selected image endpoints"
    let reversed := record.imageEndpoints.reverse
    unless sameActionOperands reversed record.imageEndpoints do
      unless (← find record.action record.input record.parameters
          record.parameterInputs reversed).isNone do
        throwError "a map action receipt exchanged its actual image endpoints"

private def diamond : TermElabM Unit := do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the published ring boundary is absent"
  let some monoids := state.categories.find? (·.id == CategoryId.monoids)
    | throwError "the published monoid boundary is absent"
  let #[direct] := state.operations.filter (fun row => row.category == rings.id && row.name == "·")
    | throwError "the direct ring multiplication binding is absent or ambiguous"
  let #[product] := state.operations.filter (fun row => row.category == monoids.id && row.name == direct.name)
    | throwError "the monoid multiplication binding is absent or ambiguous"
  let routes := state.routes rings.expression monoids.expression
  let mut separated := false
  for row in state.objects.filter (·.category == rings.id) do
    let some source ← closedDeclaration? row.declaration | continue
    let sourceContext ← CategoryContext.ofNamed rings source
    let receiver ← (objectInContext source sourceContext).run {}
    let #[selectedOwner] ← (selectedOperationApplications direct.declaration direct.category
        receiver #[] (some direct.name)).run {}
      | throwError "the live ring object lost its direct operation owner"
    unless (← (selectedOperationApplications product.declaration product.category
        receiver #[] (some product.name)).run {}).isEmpty do
      throwError "a farther same-name binding bypassed the selected direct owner"
    let mut images : Array ImageCase := #[]
    for route in routes do
      unless !route.steps.isEmpty && !state.isFirstOperationBindingRoute direct.name route do
        throwError "a farther live route ignored the direct registered binding"
      let (composite, applications) ← Semantic.routeFunctorWithApplications state route.refs
      let image ← Semantic.objOf composite source
      let applications ← applications.mapM instantiateMVars
      unless applications.all FunctorActionData.closedParameter do
        throwError "a discovered ring route requires an unprovided complete parameter"
      let context ← CategoryContext.ofNamed monoids image
      let operation ← selectedProduct product image context
      images := images.push { route, applications, image, operation }
    for i in [:images.size] do
      for j in [i+1:images.size] do
        let some left := images[i]? | unreachable!
        let some right := images[j]? | unreachable!
        let leftCarrier ← mkAppM ``MonCat.carrier #[left.image]
        let rightCarrier ← mkAppM ``MonCat.carrier #[right.image]
        unless (← same leftCarrier rightCarrier) && !(← same left.image right.image) do continue
        separated := true
        for ordered in #[#[left, right], #[right, left]] do
          let operations ← ordered.mapM fun image => do
            selectedProduct product image.image (← CategoryContext.ofNamed monoids image.image)
          if ← (sameOperationApplication operations[0]! operations[1]!).run {} then
            throwError "same-carrier additive and multiplicative operation owners were merged"
        let marker := node "valueData" #[toJson (73 : Nat)]
        unless (Backend.ComputationalValue.decode marker).isOk do
          throwError "the arbitrary returned marker lost its public computational framing"
        let output : Wire := {
          form := .diagrams monoids
          payload := .computed left.image (.inline marker)
          categoryContext := some (← CategoryContext.ofNamed monoids left.image) }
        let last := left.applications.back!
        let mut previous := source
        for action in left.applications.pop do previous ← Semantic.objOf action previous
        let trace ← Trace.new
        let harness ← Harness.empty
        let (descriptor, dependencies) ← realizedEdgeDescriptor harness trace left.route.refs.back! last
        let (operation, parameters) ← edgeActionInvocation state left.route.refs.back! descriptor false
        let (sourceBundle, _) ← functorCategoryBundles (← Semantic.asFunctor last)
        let some lastEdge := left.route.steps.back? | unreachable!
        let inputContext : CategoryContext := {
          expression := lastEdge.source, bundle := sourceBundle }
        let input : Wire := {
          form := contextualForm state inputContext (.object row)
          payload := .computed previous (.inline marker), categoryContext := some inputContext }
        checkReuse {
          operation, action := ← Semantic.asFunctor last, input, parameters
          parameterInputs := dependencies, result := output }
          (← Semantic.compositeOfApplications right.applications)
        -- The computational result is deliberately arbitrary. Installing it cannot
        -- turn the farther multiplication into the original ring's selected owner.
        harness.results.modify (·.insert left.image output)
        let observed ← realize harness trace "the selected image with arbitrary returned data" left.image
        unless observed.value == left.image && observed.json == marker do
          throwError "ordinary result reuse replaced the selected image or its actual data"
        let consumed ← selectedProduct product observed.value
          (← CategoryContext.ofNamed monoids observed.value)
        unless (← (sameOperationApplication consumed left.operation).run {}) &&
            !(← (sameOperationApplication consumed right.operation).run {}) do
          throwError "the next operation chose its owner from the untrusted returned packet"
        let #[stillSelected] ← (selectedOperationApplications direct.declaration direct.category
            receiver #[] (some direct.name)).run {}
          | throwError "untrusted data changed the direct selected owner"
        unless ← (sameOperationApplication selectedOwner stillSelected).run {} do
          throwError "untrusted data changed the complete operation declaration application"
        report "distinct-selected-images" [
          ("object", toJson row.id.raw), ("declaration", toJson row.declaration.toString),
          ("directOwner", toJson direct.id.raw), ("selectedOperation", toJson (reprStr selectedOwner)),
          ("left", routeData left.route left.applications), ("right", routeData right.route right.applications),
          ("leftImage", toJson (reprStr left.image)), ("rightImage", toJson (reprStr right.image)),
          ("sameReturnedPacket", marker), ("selectionOrdersChecked", toJson (2 : Nat))]
  unless separated do
    throwError "no closed live declaration separates same-carrier additive and multiplicative images"

private def composites : TermElabM Unit := do
  let state ← registryState
  let mut separated := false
  for row in state.morphisms do
    let some originalMap ← closedDeclaration? row.declaration | continue
    let some category := state.categories.find? (·.id == row.category)
      | throwError "a closed registered morphism lost its owner category"
    let some (sourceObject, targetObject) := homEnds? (← inferType originalMap)
      | throwError "a closed registered morphism lost its complete Hom interface"
    -- A map between these distinct selected endpoints cannot be the typed identity
    -- used as a vacuous original-map control. No representative parameter is chosen.
    if ← same sourceObject targetObject then continue
    let sourceContext ← CategoryContext.ofNamed category sourceObject
    for first in state.edgesFrom category.expression do
      if first.source.syntacticEq first.target then continue
      for second in state.edgesFrom first.target do
        if second.source.syntacticEq second.target || second.target.syntacticEq first.source then continue
        let route : Route := { source := first.source, target := second.target, steps := #[first, second] }
        let (composite, applications) ← Semantic.routeFunctorWithApplications state route.refs
        let imageSource ← Semantic.objOf composite sourceObject
        let imageTarget ← Semantic.objOf composite targetObject
        let applications ← applications.mapM instantiateMVars
        unless applications.all FunctorActionData.closedParameter do
          throwError "a discovered two-step action requires an unprovided complete parameter"
        let nonidentity ← applications.allM fun application => do
          let action ← Semantic.asFunctor application
          return !(← same action (← identityOnSourceOf action))
        unless nonidentity do continue
        for (edge, application) in route.refs.zip applications do
          checkExecutableEdgeAction state edge (← Semantic.asFunctor application)
        let (_, targetBundle) ← functorCategoryBundles (← Semantic.asFunctor applications.back!)
        let targetContext : CategoryContext := { expression := second.target, bundle := targetBundle }
        let mut nested := originalMap
        for application in applications do nested ← Semantic.mapOf application nested
        let whole ← Semantic.mapOf (← Semantic.compositeOfApplications applications) originalMap
        unless ← same nested whole do throwError "the two retained map actions changed the formal composite"
        CategoryContext.checkMorphism targetContext whole imageSource imageTarget
        let trace ← Trace.new
        let harness ← Harness.empty
        let sourceData := node "opaqueData" #[toJson "the original full source packet"]
        let targetData := node "opaqueData" #[toJson "the original full target packet"]
        let mapData := Backend.TypedMap.encode {
          source := sourceData, target := targetData
          callable := node "opaqueData" #[toJson "the original nonidentity map packet"] }
        let original : Wire := {
          form := .canonicalMorphism category
          payload := .computed originalMap (.owned "original-map-supplier" 41 mapData)
          categoryContext := some sourceContext, morphismFramed := true }
        harness.results.modify (·.insert originalMap original)
        -- The pure packet slice has no external parameter supplier. Keep the
        -- formal composite check above even when its exact fixed parameter needs
        -- actual returned data rather than a named portable presentation. Report
        -- that dependency explicitly; never choose a replacement parameter.
        let encodable ← try
          for (edge, application) in route.refs.zip applications do
            discard <| realizedEdgeDescriptor harness trace edge application
          pure true
        catch error =>
          unless Exception.stratum? error == some .noImplementation do throw error
          report "retained-parameter-data-required" [
            ("morphism", toJson row.id.raw), ("declaration", toJson row.declaration.toString),
            ("route", routeData route applications), ("formalCompositeChecked", toJson true),
            ("dependency", toJson (← error.toMessageData.toString))]
          pure false
        unless encodable do continue
        let actual ← contextualAction harness trace whole originalMap sourceContext targetContext
          route.refs applications true
        unless actual.value == whole && actual.owner? == original.owner? do
          throwError "two live map actions changed the selected composite or actual source supplier"
        let mut packet := actual.json
        for (edge, application) in (route.refs.zip applications).reverse do
          let .ok ("map", #[descriptor, child]) := ComputationalData.envelope packet
            | throwError "the composite map discarded a nonidentity action factor"
          let (expected, _) ← realizedEdgeDescriptor harness trace edge application
          unless descriptor == expected && descriptorEdge? state descriptor == some edge do
            throwError "the composite map changed a complete ordered action descriptor"
          packet := child
        unless packet == original.json do
          throwError "the composite map reconstructed or replaced the original returned packet"
        reject "omitted a complete selected application" <|
          contextualAction harness trace whole originalMap sourceContext targetContext
            route.refs applications.pop true
        reject "differs from its exact accepted declaration" <|
          contextualAction harness trace whole originalMap sourceContext targetContext
            route.refs applications.reverse true
        reject "fixed result or full target bundle" <|
          contextualAction harness trace whole originalMap sourceContext sourceContext
            route.refs applications true
        -- The same full selected applications also retain the source object's
        -- original packet. This is the framing path, not a claim of native execution.
        let sourceWire : Wire := {
          form := .diagrams category
          payload := .computed sourceObject (.owned "original-map-supplier" 41 sourceData)
          categoryContext := some sourceContext }
        harness.results.modify (·.insert sourceObject sourceWire)
        let image ← contextualAction harness trace imageSource sourceObject sourceContext targetContext
          route.refs applications false
        unless image.value == imageSource && image.owner? == sourceWire.owner? do
          throwError "the composite object action lost its complete source or supplier"
        let middleMap ← Semantic.mapOf applications[0]! originalMap
        let middleSource ← Semantic.objOf applications[0]! sourceObject
        let middleTarget ← Semantic.objOf applications[0]! targetObject
        let (_, middleBundle) ← functorCategoryBundles (← Semantic.asFunctor applications[0]!)
        let middleContext : CategoryContext := { expression := first.target, bundle := middleBundle }
        let (descriptor, dependencies) ← realizedEdgeDescriptor harness trace second.ref applications[1]!
        let (operation, parameters) ← edgeActionInvocation state second.ref descriptor true
        let marker := node "valueData" #[toJson (73 : Nat)]
        let input : Wire := { original with
          form := contextualForm state middleContext original.form true
          payload := .computed middleMap (.owned "original-map-supplier" 41 mapData)
          categoryContext := some middleContext }
        let beforeSource : Wire := { sourceWire with
          form := contextualForm state middleContext sourceWire.form
          payload := .computed middleSource (.owned "original-map-supplier" 41 sourceData)
          categoryContext := some middleContext }
        let beforeTarget : Wire := { sourceWire with
          form := contextualForm state middleContext sourceWire.form
          payload := .computed middleTarget (.owned "original-map-supplier" 41 targetData)
          categoryContext := some middleContext }
        let afterSource : Wire := { sourceWire with
          form := contextualForm state targetContext sourceWire.form
          payload := .computed imageSource (.inline (toJson "actual source image"))
          categoryContext := some targetContext }
        let afterTarget : Wire := { afterSource with
          payload := .computed imageTarget (.inline (toJson "actual target image")) }
        let result : Wire := { actual with payload := .computed whole (.inline marker) }
        checkReuse {
          operation, action := ← Semantic.asFunctor applications[1]!, input, parameters
          parameterInputs := dependencies ++ #[beforeSource, beforeTarget]
          imageEndpoints := #[afterSource, afterTarget], result }
          (← Semantic.asFunctor applications[0]!)
        separated := true
        report "two-selected-actions" [
          ("morphism", toJson row.id.raw), ("declaration", toJson row.declaration.toString),
          ("route", routeData route applications), ("originalMap", toJson (reprStr originalMap)),
          ("compositeMap", toJson (reprStr whole)), ("source", toJson (reprStr sourceObject)),
          ("target", toJson (reprStr targetObject)), ("actualMapPacket", actual.json),
          ("actualObjectPacket", image.json)]
  unless separated do
    throwError "no closed live morphism supplies two nonidentity selected actions with distinct original endpoints"

-- Use a literal admitted at the actual published result interface, without
-- asserting that its number is the answer. Even a coincidentally correct reply
-- must remain data attached to the original selected method application.
private def untrustedResult : TermElabM Unit := do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the live cardinality source category is absent"
  let #[method] := state.methods.filter (fun row =>
      row.name == "cardinality" && row.owner.syntacticEq sets.expression)
    | throwError "the live cardinality owner is absent or ambiguous"
  let mut separated := false
  for row in state.objects.filter (·.category == sets.id) do
    let some source ← closedDeclaration? row.declaration | continue
    let trace ← Trace.new
    let (formal, context) ← Semantic.methodIn method.name source sets.expression (some trace)
    let some category := CategoryContext.named? state context.expression
      | throwError "the selected cardinality result has no published literal category"
    let #[literal] := state.literals.filter (·.category == category.id)
      | throwError "the selected result has no unique public literal interface"
    let value ← elabTermAndSynthesize (← `(73)) (some (← mkConstWithFreshMVarLevels literal.type))
    let .ok packet ← Codec.encode value
      | throwError "the arbitrary numeric reply is not a published literal packet"
    if let .error message ← ComputationalData.validatePort formal (← inferType formal) packet then
      throwError "the untrusted reply does not have the complete selected result interface: {message}"
    let some (.method owner route receiver comparisons) ← trace.node? formal
      | throwError "the live method lost its original formal provenance"
    unless owner == method.id && receiver == source do
      throwError "the selected method changed its published owner or complete receiver"
    let harness ← Harness.empty
    let supplied : Wire := {
      form := .literal literal, payload := .computed formal (.inline packet)
      categoryContext := some context }
    harness.results.modify (·.insert formal supplied)
    let retained ← realize harness trace "the independently selected method with an untrusted reply" formal
    unless retained.value == formal && retained.json == packet do
      throwError "a well-framed numerical reply replaced its original formal question"
    let some (.method afterOwner afterRoute afterReceiver afterComparisons) ← trace.node? retained.value
      | throwError "a well-framed reply erased the selected method's formal provenance"
    unless afterOwner == owner && afterRoute == route && afterReceiver == receiver &&
        afterComparisons == comparisons do
      throwError "a numerical reply bypassed its exact formal owner, route or accepted comparisons"
    separated := true
    report "untrusted-result-keeps-formal-owner" [
      ("object", toJson row.id.raw), ("declaration", toJson row.declaration.toString),
      ("owner", toJson owner.raw), ("route", toJson (route.map EdgeRef.label)),
      ("selectedFormalResult", toJson (reprStr formal)), ("literalInterface", toJson literal.id.raw),
      ("validatedUntrustedPacket", packet), ("mathematicalAnswerAsserted", toJson false)]
  unless separated do
    throwError "no closed live declaration supplies the untrusted-result owner control"

run_elab diamond
run_elab composites
run_elab untrustedResult

end
end CasCatalogue.DeclarationDerivedTransportProbes
