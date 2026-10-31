module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering probes for kernel-owned framing and request selection. They execute no leaf,
register no mathematical rows and admit no mathematical expected answers. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert |sign(3).ker()| = 3"
    | throwError "the arrow request did not parse"
  let question ← interpret {} parsed
  let state ← registryState
  let trace ← IO.mkRef question.trace
  let harness ← Harness.empty
  let mut checked := false
  for (value, node) in question.trace.toArray do
    let .arrow category hom source target := node | continue
    let some base := state.categories.find? (·.id == category)
      | throwError "the traced arrow has no base category"
    let some expected := state.arrowsOf? base.expression
      | throwError "the arrow constructor is absent"
    let actual ← realize harness trace "the complete arrow receiver" value
    let .arrow form := actual.form
      | throwError "the arrow did not retain its structural form"
    unless form.expression.syntacticEq expected do
      throwError "an Arrow receiver was framed as its base category"
    let sourceWire ← realize harness trace "the retained source endpoint" source
    let targetWire ← realize harness trace "the retained target endpoint" target
    let homWire ← realize harness trace "the retained defining map" hom
    let .ok fields := (actual.json.getObjVal? "args").bind (·.getArr?)
      | throwError "the Arrow request lost its complete fields"
    unless fields == #[sourceWire.json, targetWire.json, homWire.json] do
      throwError "the Arrow request changed an endpoint or its defining map"
    let normalized ← IO.mkRef (question.trace.insert value (.arrow form.id hom source target))
    let cold ← Harness.empty
    let same ← realize cold normalized "the already registered Arrow context" value
    unless same.form.id == actual.form.id && same.json == actual.json do
      throwError "an already registered Arrow context was wrapped a second time"
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the independent wrong-source category is absent"
    let wrong ← IO.mkRef (question.trace.insert value (.arrow sets.id hom source target))
    let cold ← Harness.empty
    let rejected ← try
        discard <| realize cold wrong "an Arrow with a contradictory source context" value
        pure false
      catch error =>
        if (CasCatalogue.Exception.stratum? error).isNone then pure true else throw error
    unless rejected do throwError "an Arrow accepted a contradictory complete source category"
    checked := true
  unless checked do throwError "the request did not exercise an Arrow receiver"

run_elab do
  let state ← registryState
  let harness ← Harness.empty
  let mut propertyRequests : Array Wire := #[]
  let mut refined := false
  for text in #["assert (ZMod(3) in Groups).is_abelian()",
      "assert (ZMod(5) in Groups).is_abelian()",
      "assert (Sym(3) in Groups).is_abelian() = false",
      "assert |Sym(3) in Groups| = 6"] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "the request-selection probe did not parse"
    let question ← interpret {} parsed
    let trace ← IO.mkRef question.trace
    let mut checked := false
    for (value, node) in question.trace.toArray do
      let operation ← match node with
        | .method id route receiver _ application =>
            pure (some (id.raw, route, receiver, false, some application))
        | .property id route receiver _ => pure (some (id.raw, route, receiver, true, none))
        | _ => pure none
      let some (id, route, receiver, isProperty, application?) := operation | continue
      let original ← realize harness trace "the actual operation receiver" receiver
      let .object entry := original.form
        | throwError "the request-selection probe lost its named source form"
      let (expected, _) := state.transport entry route
      let (request, image) ← operationReceiver trace original route
      unless request.form.id == expected.id.raw do
        throwError "the request did not stop at its catalogue refinement prefix"
      if expected.id == entry.id then
        unless request.json == original.json do
          throwError "a source composite changed its original input data"
      else
        let .ok originalArgs := original.json.getObjVal? "args"
          | throwError "the original source parameters are absent"
        let .ok requestArgs := request.json.getObjVal? "args"
          | throwError "the canonical request parameters are absent"
        unless requestArgs == originalArgs do
          throwError "canonical refinement changed the ordered full source parameters"
        refined := true
      let operation ← if isProperty then do
        let some property := state.properties.find? (·.id.raw == id)
          | throwError "the recorded property is absent"
        let some classifier := state.classifier? property.classifier
          | throwError "the recorded classifier is absent"
        propertyRequests := propertyRequests.push request
        let classifier ← classifierInstance classifier
        elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
          $(← exprToSyntax classifier) $(← exprToSyntax image))) none
      else do
        let some method := state.methods.find? (·.id.raw == id)
          | throwError "the recorded method is absent"
        let some application := application?
          | throwError "the recorded method lost its complete selected application"
        unless ← withTransparency .all <| isDefEq application.input
            (← methodArgument method image) do
          throwError "the request changed the retained complete method input"
        Semantic.objOf application.application application.input
      unless ← withTransparency .all <| isDefEq operation value do
        throwError "request selection changed the full independently read semantic operation"
      checked := true
    unless checked do throwError "the probe did not reach an actual operation receiver"
  let #[three, five, symmetric] := propertyRequests
    | throwError "source/parameter discrimination did not exercise all requests"
  unless three.form.id == five.form.id && three.json != five.json do
    throwError "the same source family lost its distinct actual parameters"
  unless three.form.id != symmetric.form.id && three.json != symmetric.json do
    throwError "different source structures collapsed to a shared request"
  unless refined do throwError "no complete catalogue refinement prefix was exercised"

run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "(3 in ℚˣ)⁻¹"
    | throwError "the unchanged rational inverse term did not parse"
  let trace ← CasCatalogue.Trace.new
  discard <| (eval {} parsed).run { trace := some trace }
  let snapshot ← trace.get
  let mut checked := false
  for (representative, node) in snapshot.toArray do
    let .parameterEquivalence expected recorded sources := node | continue
    unless sources.size >= 2 do throwError "the actual parameter lost its independent origins"
    let some chosen := sources[0]? | throwError "the actual parameter has no source"
    let mut encoded ← parameterData trace representative
    for index in (List.range chosen.route.size).reverse do
      let .ok args := LiftedSubobjectData.fields "functorAction" 2 encoded
        | throwError "the serializer discarded a selected structural application"
      let action ← edgeDescriptor trace chosen.route[index]! chosen.applications[index]!
      unless args[0]! == action do
        throwError "the serializer changed a full selected application or its parameters"
      encoded := args[1]!
    unless encoded.getObjValAs? String "ctor" == .ok chosen.source.raw do
      throwError "the serializer changed the independently selected named source"
    let some other := sources[1]? | throwError "the protected nonchosen origin is absent"
    let forged := sources.set! 1 { other with sourceCategory := CategoryId.sets }
    let wrong ← IO.mkRef (snapshot.insert representative
      (.parameterEquivalence expected recorded forged))
    let rejected ← try
        discard <| parameterData wrong representative
        pure false
      catch error =>
        if (CasCatalogue.Exception.stratum? error).isNone then pure true else throw error
    unless rejected do throwError "the serializer skipped a contradictory nonchosen origin"
    checked := true
  unless checked do throwError "the actual inverse did not retain a parameter identity class"

/- Replay the actual native product packet at method receiver selection, without
asserting that its apex or legs satisfy the product law. -/
run_elab do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the released product declaration is absent"
  let left ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let right ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.integersMod 3)) none
  let formal ← mkAppM row.declaration #[left, right]
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[formal]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let .ok packet := Json.parse r#"{"ctor":"cone","args":[{"ctor":"finiteData","args":[{"ctor":"obj.sets.fin","args":[6]},[0,1,2,3,4,5]]},{"ctor":"finiteGraph","args":[[0,1,2,3,4,5],[[0,0],[1,0],[2,0],[3,1],[4,1],[5,1]]]},{"ctor":"finiteGraph","args":[[0,1,2,3,4,5],[[0,0],[1,1],[2,2],[3,0],[4,1],[5,2]]]}]}"#
    | throwError "the recorded native packet is not JSON"
  let .ok fields := (packet.getObjVal? "args").bind (·.getArr?)
    | throwError "the recorded native packet lost its fields"
  let apexJson := fields[0]!
  let wire := fun (tag : String) (args : Array Json) => Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let trace ← CasCatalogue.Trace.new
  let original : Wire := { form := .limitApex row, payload := .computed apex (.owned "engineering-owner" 17 packet) }
  let check := fun input => do
    let actual ← computationalApexReceiver trace input
    unless actual.form.id == "obj.sets.fin" && actual.json == apexJson &&
        actual.value == apex && actual.owner?.isNone do
      throwError "apex receiver changed actual form, complete finiteData payload, formal value or portability"
    unless actual.payload matches .computed _ (.inline _) do
      throwError "the portable apex stopped being computational data"
  check original
  let descriptor := fun name => wire name #[toJson (6 : Nat)]
  for wrong in #[
      wire "finiteData" #[descriptor "obj.groups.symmetric", fields[0]!],
      wire "finiteData" #[descriptor "not.a.registered.object", fields[0]!],
      wire "finiteData" #[descriptor "obj.sets.fin"],
      wire "finiteData" #[wire "finiteData" #[descriptor "obj.sets.fin", Json.arr #[]], Json.arr #[]]] do
    let candidate := { original with payload := .computed apex (.owned "engineering-owner" 17
      (wire "cone" (fields.set! 0 wrong))) }
    let actual ← computationalApexReceiver trace candidate
    unless actual.form.id == candidate.form.id && actual.json == candidate.json &&
        actual.value == candidate.value && actual.owner? == candidate.owner? do
      throwError "apex receiver selected a nearby form for a contradictory or malformed descriptor"
