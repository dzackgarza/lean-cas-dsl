/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.QuestionComparison
meta import CasCatalogue.QuestionComparison
import CasCatalogue.FileItems
meta import CasCatalogue.FileItems
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Optional execution conditions for the unchanged independently supplied RX10 question.
One complete question is interpreted before selecting any computational environment.
The conditions are manifests and an external protocol fault proxy; no mathematical
assertion or kernel operation is altered. The `internal` control is a normal Lean
resource fault during execution, outside any computation's reply protocol.

Set `CAS_FROZEN_LEAF_MANIFEST` to the independently supplied public manifest and
`CAS_FIXED_QUESTION_REPORT` to the result path. The default fault-proxy directory is
`CasAcceptance/Strata`; `CAS_CONDITION_PROTOCOL_DIR` can select an isolated checkout. -/

open Lean Meta Elab Term Command CategoryTheory CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private partial def containsData (data expected : Json) : Bool :=
  data == expected || match data with
    | .arr children => children.any (containsData · expected)
    | .obj fields => fields.any fun _ child => containsData child expected
    | _ => false

private def typedTerms (values : Array Expr) (labels : Array String) : TermElabM Json := do
  let table ← TermTable.new
  let types ← QuestionIdentity.questionTypes values #[]
  let values ← values.mapM table.encode
  let types ← types.mapM table.encode
  let text ← table.finish (Json.mkObj [
    ("values", toJson values), ("types", toJson types), ("labels", toJson labels)])
  let .ok result := Json.parse text | throwError "the complete control observation did not encode"
  return result

private structure FixedQuestion where
  source : String
  line : Nat
  id : String
  question : TypedQuestion
  independentlyRead : TypedQuestion
  callable : Expr
  context : CategoryContext
  domain : Expr
  target : Expr
  operation : OperationId
  independentOperands : Json

/-- Match the production file reader: each original binding and complete reading
gets a fresh term-elaboration scope and heartbeat budget. A single engineering
command must not accumulate the cost of all independent source statements. -/
private def readFixedQuestion : CommandElabM FixedQuestion := do
  let source := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx10-fixed-execution-question.cas"
  let items := itemsWithLocations (← IO.FS.readFile source)
  let mut scope : Language.Scope := {}
  let mut assertion : Option (String × Syntax × Nat) := none
  for item in items do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_item item.text source
      | throwError "the unchanged fixed question failed to parse at {source}:{item.line}"
    match parsed with
    | `(cas_item| test $name:ident $_:str : $statement:cas_stmt) =>
        unless assertion.isNone do throwError "the fixed-question input has more than one assertion"
        assertion := some (name.getId.toString, statement, item.line)
    | `(cas_item| $statement:cas_stmt) =>
        let some (name, term) ← liftTermElabM <| letBinding? statement
          | throwError "the fixed-question source contains an unexpected unnamed assertion"
        try
          liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
            let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
            discard <| (claim scope statement).run { closedTerms := some closedTerms }
        catch error =>
          throwError "the unchanged prerequisite at {source}:{item.line} failed: {item.text}\n{error.toMessageData}"
        scope := scope.insert name term
    | _ => throwError "the fixed-question source changed its public item shape"
  let some (id, statement, line) := assertion
    | throwError "the unchanged fixed-question assertion is absent"
  let question ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
    interpret scope statement
  let independentlyRead ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
    interpret scope statement
  liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
    unless ← QuestionIdentity.equivalentTypedQuestion question independentlyRead do
      throwError "independent readings of the original complete question are not equivalent"
    let .homs left right _ _ _ _ := question.claim
      | throwError "the fixed equality lost its independently specified actual map operands"
    let independent := (← getConstInfo
      ``CasCatalogue.Modules.IntegerResidueModules.reindex_double_three).type
    let some (_, expectedLeft, expectedRight) := independent.eq?
      | throwError "the independent source theorem changed its specified equality"
    let state ← registryState
    let leftValue ← pointResultValue state left
    let rightValue ← pointResultValue state right
    unless ← withTransparency .all <|
        isDefEq leftValue expectedLeft <&&> isDefEq rightValue expectedRight do
      throwError "the fixed question changed an independent equality operand"
    let .ok callableSyntax := Parser.runParserCategory (← getEnv) `cas_term "restrictedMap"
      | throwError "the independent selected callable name did not parse"
    let trace ← IO.mkRef question.trace
    let selected ← (eval scope callableSyntax).run { trace := some trace }
    let (callable, domain, target, context) ← match selected with
      | .derivedMorphism value source target context _ => pure (value, source, target, context)
      | .morphism value source target category _ =>
          pure (value, source, target, ← CategoryContext.ofNamed category source)
      | _ => throwError "the independently selected reindexed callable did not remain a whole map"
    unless question.trace.contains callable do
      throwError "the original question did not retain its actual selected reindexed map"
    let expectedCallable ← elabTermAndSynthesize (← `(
      (CasCatalogue.Modules.CatalogueRegistration.modulesFamilyRealization.reindex
        (RingCat.ofHom (Int.castRingHom (ZMod 5)))).map
        (ModuleCat.ofHom
          (X := CasCatalogue.Modules.CatalogueRegistration.regularModule (RingCat.of (ZMod 5)))
          (Y := CasCatalogue.Modules.CatalogueRegistration.regularModule (RingCat.of (ZMod 5)))
          ((2 : ZMod 5) • LinearMap.id)))) none
    unless ← withTransparency .all <| isDefEq callable expectedCallable do
      throwError "the selected complete reindexed map changed the independent source's full arrow"
    let mut operations : Array OperationId := #[]
    for (value, node) in question.trace.toArray do
      let .operationApply operation _ _ _ _ := node | continue
      let some (input, _) := homEnds? (← inferType value) | continue
      if ← withTransparency .all <| isDefEq input (← closedElementDomain state) then continue
      unless operations.contains operation do operations := operations.push operation
    let #[operation] := operations
      | throwError "the fixed map did not retain one complete generalized registered operation"
    return {
      source, line, id, question, independentlyRead, callable, context, domain, target, operation
      independentOperands := ← typedTerms
        #[leftValue, expectedLeft, rightValue, expectedRight, callable, expectedCallable]
        #["actualLeftValue", "independentLeftValue", "actualRightValue", "independentRightValue",
          "actualCompleteCallable", "independentCompleteCallable"] }

private def conditionManifest (base : Manifest) (root directory proxy : System.FilePath)
    (condition : String) (operation : OperationId) : IO Manifest := do
  if condition == "holds" || condition == "internal" then return base
  if condition == "gap" then
    return { base with registrations := base.registrations.filter (·.operation != operation.raw) }
  let mut backends := #[]
  for (backend, index) in base.backends.zipIdx do
    let configuration := directory / s!"{condition}-{index}.json"
    let delegate := Json.mkObj [("command", toJson backend.command), ("args", toJson backend.args),
      ("root", toJson root.toString)]
    let common := [("operation", toJson operation.raw), ("requestCtor", toJson "apply"),
      ("delegate", delegate), ("receipts", toJson (directory / s!"{condition}-{index}.jsonl").toString)]
    let fault ← if condition == "unavailable" then
        pure [("mode", toJson "disconnect")]
      else if condition == "malformed" then
        pure [("mode", toJson "replace"), ("value", Json.mkObj [
          ("ctor", "valueData"), ("args", Json.arr #[Json.mkObj [("unexpected", toJson true)]])])]
      else if condition == "wrong" then
        -- Deliberately wrong backing data live only in the proxy's opaque callable.
        -- They never provide a host-side proof, endpoint inventory or acceptance oracle.
        let keys := (List.range 5).toArray.map toJson
        let graph := keys.map fun key => Json.arr #[key, toJson (0 : Nat)]
        pure [("mode", toJson "owned-replacement"), ("backing", Json.arr graph)]
      else throw <| IO.userError "unknown fixed-question execution condition"
    IO.FS.writeFile configuration ((Json.mkObj (common ++ fault)).pretty ++ "\n")
    backends := backends.push { backend with
      command := "python3", args := #[proxy.toString, configuration.toString] }
  return { base with backends }

private def materialize (harness : Harness) (fixed : FixedQuestion) : TermElabM Wire := do
  let trace ← IO.mkRef fixed.question.trace
  let descriptor ← realize harness trace "the fixed complete reindexed map" fixed.callable
  let actual ← realizeArrowObservation harness trace descriptor
  unless actual.value == fixed.callable && actual.owner?.isSome do
    throwError "the required selected reindexed callable was not actual returned owned data"
  return actual

private def observeOwnedSessions (harness : Harness) (fixed : FixedQuestion)
    (actual : Wire) (manifest : Manifest) (root : System.FilePath) : TermElabM Json := do
  let some owner := actual.owner? | throwError "the session control has no actual returned owner"
  let trace ← IO.mkRef fixed.question.trace
  let carrier ← CategoryContext.carrier fixed.context
  let dictionary ← CategoryContext.dictionary fixed.context
  let arrow ← mkAppOptM ``CategoryTheory.Arrow.mk
    #[some carrier, some dictionary, some fixed.domain, some fixed.target, some fixed.callable]
  Trace.record (some trace) arrow
    (.contextualArrow fixed.context fixed.callable fixed.domain fixed.target)
  let structured ← realize harness trace "the actual reindexed map in its complete Arrow" arrow
  let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some dictionary]
  let composed ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
    #[some carrier, some categoryStructure, some fixed.domain, some fixed.target,
      some fixed.target, some fixed.callable, some fixed.callable]
  Trace.record (some trace) composed
    (.contextualComposition fixed.context fixed.callable fixed.callable
      fixed.domain fixed.target fixed.target)
  let composite ← realize harness trace "the actual reindexed map in a later composition" composed
  for wrapper in #[structured, composite] do
    unless wrapper.owner? == actual.owner? && containsData wrapper.json actual.json do
      throwError "a complete reindexed-map wrapper detached its actual returned data or owner"
  let foreignCalls ← IO.mkRef #[]
  let foreign ← Harness.ofManifest root manifest
  let foreign := { foreign with computationOnly := true, dispatches := some foreignCalls }
  try
    let .ok other ← foreign.connection owner.1
      | throwError "the independent foreign session did not start"
    unless other.identity != owner.2 do throwError "independent sessions share one host identity"
    foreign.results.modify (·.insert fixed.callable actual)
    let foreignResult ← tryCatchRuntimeEx (evaluate foreign fixed.question) executionFailure
    unless foreignResult.toOutcome.kind == "unavailable" do
      throwError "the actual reindexed callable was not rejected by the foreign session boundary: {reprStr foreignResult}"
    unless !(← foreignCalls.get).any (fun sent =>
        (sent.getObjVal? "request").toOption.any (containsData · actual.json)) do
      throwError "the foreign session received the old callable before ownership rejection"
    harness.stop
    let .ok reconnected ← harness.connection owner.1
      | throwError "the replacement owning session did not start"
    unless reconnected.identity != owner.2 do throwError "reconnection revived the old host identity"
    let previousCalls ← match harness.dispatches with
      | some calls => pure (← calls.get).size
      | none => throwError "the session control lost its actual dispatch observations"
    harness.results.modify (·.insert fixed.callable actual)
    let expiredResult ← tryCatchRuntimeEx (evaluate harness fixed.question) executionFailure
    unless expiredResult.toOutcome.kind == "unavailable" do
      throwError "the actual old reindexed callable survived reconnection: {reprStr expiredResult}"
    let afterExpiration ← match harness.dispatches with
      | some calls => pure (← calls.get)
      | none => throwError "the session control lost its actual dispatch observations"
    unless !(afterExpiration.extract previousCalls afterExpiration.size).any (fun sent =>
        (sent.getObjVal? "request").toOption.any (containsData · actual.json)) do
      throwError "the replacement session received an expired callable before rejection"
    harness.results.set {}
    let fresh ← materialize harness fixed
    unless fresh.owner? == some (owner.1, reconnected.identity) && fresh.value == actual.value do
      throwError "fresh computation changed the full arrow or reused the expired ownership"
    let freshResult ← tryCatchRuntimeEx (evaluate harness fixed.question) executionFailure
    unless freshResult.toOutcome.kind == "holds" do
      throwError "fresh new-session computation did not answer the original question: {reprStr freshResult}"
    return Json.mkObj [
      ("kind", "holds"), ("originalOwner", toJson (some owner)),
      ("foreignOwner", toJson (owner.1, other.identity)), ("freshOwner", toJson fresh.owner?),
      ("structuredWrapper", structured.json), ("compositionWrapper", composite.json),
      ("foreignKind", toJson foreignResult.toOutcome.kind),
      ("expiredKind", toJson expiredResult.toOutcome.kind),
      ("freshKind", toJson freshResult.toOutcome.kind),
      ("foreignDispatches", Json.arr (← foreignCalls.get)),
      ("question", toJson fixed.question.identity.1)]
  finally
    foreign.stop

private def observeCondition (fixed : FixedQuestion) (manifest : Manifest)
    (root : System.FilePath) (condition : String) : TermElabM Json := do
  let dispatches ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with computationOnly := true, dispatches := some dispatches }
  let returned ← IO.mkRef (none : Option Wire)
  let afterMaterialization ← IO.mkRef 0
  try
    let execution : TermElabM ExecutionOutcome := do
      returned.set (some (← materialize harness fixed))
      afterMaterialization.set (← dispatches.get).size
      evaluate harness fixed.question
    let execution := if condition == "internal" then
        withCurrHeartbeats <| withTheReader Core.Context (fun context =>
          { context with maxHeartbeats := 1 }) execution
      else execution
    let outcome ← tryCatchRuntimeEx execution executionFailure
    let actual := outcome.toOutcome
    unless ← QuestionIdentity.equivalentTypedQuestion fixed.question fixed.independentlyRead do
      throwError "an execution environment changed the original complete question"
    let originalCalls ← dispatches.get
    let subsequent := originalCalls.extract (← afterMaterialization.get) originalCalls.size
    let reused := (← returned.get).any fun wire => subsequent.any fun sent =>
      (sent.getObjVal? "request").toOption.any (containsData · wire.json)
    let sessionControls ← if condition == "holds" && actual.kind == "holds" then do
        let some wire ← returned.get | throwError "the correct execution lost its actual callable"
        try
          observeOwnedSessions harness fixed wire manifest root
        catch error => return Json.mkObj [("kind", "internal"),
          ("detail", toJson (← error.toMessageData.toString))]
      else pure Json.null
    let callable ← match ← returned.get with
      | none => pure Json.null
      | some wire =>
        pure (Json.mkObj [("data", wire.json), ("owner", toJson wire.owner?),
          ("originalFormalTerm", toJson (wire.value == fixed.callable))])
    return Json.mkObj [
      ("condition", toJson condition), ("expectedKind", toJson condition),
      ("id", toJson fixed.id), ("source", toJson fixed.source), ("sourceLine", toJson fixed.line),
      ("question", toJson fixed.question.identity.1), ("proposition", toJson fixed.question.identity.2),
      ("kind", toJson actual.kind), ("detail", toJson actual.detail), ("fails", toJson actual.fails),
      ("sameIndependentTypedQuestion", toJson true),
      ("callable", callable), ("callableReused", toJson reused),
      ("dispatches", Json.arr originalCalls), ("sessionControls", sessionControls),
      ("rejectedRegistrations", toJson harness.rejected)]
  finally
    harness.stop

-- Each environment is an independent production-sized execution attempt. The
-- explicit one-heartbeat `internal` fault remains inside observeCondition.
run_cmd do
  let fixed ← readFixedQuestion
  let some manifestPath ← IO.getEnv "CAS_FROZEN_LEAF_MANIFEST"
    | throwError "CAS_FROZEN_LEAF_MANIFEST must select the independent public leaf manifest"
  let manifestPath : System.FilePath ← IO.FS.realPath manifestPath
  let .ok base ← Manifest.read manifestPath
    | throwError "the independently supplied leaf manifest did not read"
  let root := manifestPath.parent.getD "."
  let protocolDirectory : System.FilePath := (← IO.getEnv "CAS_CONDITION_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let proxy ← IO.FS.realPath (protocolDirectory / "probe_reply_conditions.py")
  let directory : System.FilePath := s!"/tmp/cas-fixed-question-conditions-{← IO.monoMsNow}"
  IO.FS.createDirAll directory
  let mut records := #[]
  let mut failures : Array String := #[]
  for condition in #["holds", "gap", "unavailable", "malformed", "wrong", "internal"] do
    let selected ← conditionManifest base root directory proxy condition fixed.operation
    let observed ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
      observeCondition fixed selected root condition
    records := records.push observed
    let actual := (observed.getObjValAs? String "kind").toOption.getD "missing"
    logInfo m!"RX10 fixed question: {condition} environment observed {actual}"
    unless actual == condition do failures := failures.push s!"{condition} observed {actual}"
    if condition == "holds" || condition == "wrong" then
      unless (observed.getObjValAs? Bool "callableReused").toOption == some true do
        failures := failures.push s!"{condition} did not consume its actual returned callable"
    if condition == "holds" then
      unless ((observed.getObjVal? "sessionControls").bind
          (·.getObjValAs? String "kind")).toOption == some "holds" do
        failures := failures.push "the exact selected reindexed callable failed a session control"
  if let some report ← IO.getEnv "CAS_FIXED_QUESTION_REPORT" then
    IO.FS.writeFile report ((Json.mkObj [
      ("independentOperands", fixed.independentOperands), ("observations", Json.arr records),
      ("conditionDirectory", toJson directory.toString),
      ("manifest", toJson manifestPath.toString)]).pretty ++ "\n")
  unless failures.isEmpty do throwError "fixed-question execution controls failed: {failures}"

end
