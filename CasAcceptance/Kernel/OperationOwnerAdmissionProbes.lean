/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for admission before an owner action has supplied its
target packet. Existing accepted actions and addition fix every formal request.
The unchanged protocol fixtures supply arbitrary owned or portable data; no
arithmetic value or mathematical correctness claim is part of these controls. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasCatalogue.OperationOwnerAdmissionProbes
meta section

private def parse (text : String) : TermElabM Syntax := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the owner-admission control did not parse"
  return parsed

private structure Question where
  trace : Trace
  source : Expr
  ownerValue : Value
  owner : Expr
  operation : OperationEntry
  actions : Array FunctorEntry

private def question : TermElabM Question := do
  let trace ← Trace.new
  let sourceValue ← (eval {} (← parse
    "view (ℤ in CommutativeRings) along «fun.commutative_rings.ring»()")).run
      { trace := some trace }
  let source ← (semanticObject sourceValue).run {}
  let ownerValue ← (eval {} (← parse
    "view (view S along «fun.rings.additive_group»()) along «fun.additive_groups.additive_monoid»()")).run
      { trace := some trace, bound := [(`S, sourceValue)] }
  let owner ← (semanticObject ownerValue).run {}
  let state ← registryState
  let some operation := state.operations.find? (·.id.raw == "op.additive_monoids.add")
    | throwError "the owner-admission control lost the existing operation"
  let actions ← #["fun.commutative_rings.ring", "fun.rings.additive_group",
      "fun.additive_groups.additive_monoid"].mapM fun id => do
    let some action := state.functors.find? (·.id.raw == id)
      | throwError "the owner-admission control lost an existing selected action"
    unless action.structural do
      throwError "the owner-admission control no longer retains structural source actions"
    pure action
  return { trace, source, ownerValue, owner, operation, actions }

private def operationTerm (selected : Question) (argument : Option Value := none) :
    TermElabM (Value × Expr × Array Expr) := do
  let previous := (← selected.trace.get).toArray.map Prod.fst
  let bound := [(`A, selected.ownerValue)] ++
    (argument.map fun value => [(`f, value)]).getD []
  let text := if argument.isSome then "(x ↦ f(x) + f(x)) in A → A"
    else "(x ↦ x + x) in A → A"
  let value ← (eval {} (← parse text)).run { trace := some selected.trace, bound }
  let operations := (← selected.trace.get).toArray.filterMap fun (formal, node) =>
    if previous.contains formal then none else match node with
      | .operationApply id parameters .. =>
          if id == selected.operation.id then some (formal, parameters) else none
      | _ => none
  let #[(formal, parameters)] := operations
    | throwError "the owner-admission control lost its one newly selected operation"
  return (value, formal, parameters)

private def manifest (selected : Question) (configuration : System.FilePath) : Manifest := {
  backends := #[
    { name := "owner-source", command := "python3"
      args := #["probe_reply_conditions.py", configuration.toString] },
    { name := "owner-target", command := "python3"
      args := #["probe_owned_callable.py", "--require-argument-owner", selected.operation.id.raw] },
    { name := "owner-peer", command := "python3"
      args := #["probe_owned_callable.py", "--require-argument-owner", selected.operation.id.raw] },
    { name := "owner-foreign", command := "python3"
      args := #["probe_owned_callable.py", "--require-argument-owner"] ++
        selected.actions.map (·.id.raw) ++ #[selected.operation.id.raw] }]
  registrations :=
    (#["owner-source", "owner-foreign"].flatMap fun backend =>
      selected.actions.map fun action => {
        operation := action.id.raw, input := action.inputAddress, backend }) ++
    (#["owner-target", "owner-peer", "owner-foreign"].map fun backend => {
      operation := selected.operation.id.raw, input := selected.operation.category.raw, backend }) }

private def withScope (base : Harness) (backend : String)
    (calls : IO.Ref (Array Json)) (peer : Bool := false) : IO Harness := do
  let scope ← Harness.empty
  return { scope with
    root := base.root, backends := base.backends, connections := base.connections
    serviceOperands := base.serviceOperands, demandObjectActions := true
    dispatches := some calls
    admitted := base.admitted.filter fun row =>
      row.registration.backend == backend ||
        (backend == "owner-target" && row.registration.backend == "owner-source") ||
        (peer && row.registration.backend == "owner-peer") }

private def expectedFailure (stratum : Stratum) (action : TermElabM Wire) :
    TermElabM Bool := do
  try
    discard action
    pure false
  catch error =>
    if Exception.stratum? error == some stratum then pure true else throw error

run_elab do
  for condition in #["portable", "ambiguous", "foreign", "owned-output"] do
    let selected ← question
    let directory : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
      ("CasAcceptance" / "Strata" : System.FilePath).toString
    let directory ← IO.FS.realPath directory
    let suppliedRuntime ← IO.getEnv "CAS_OWNER_ADMISSION_RUNTIME_DIR"
    let runtime ← match suppliedRuntime with
      | some path => IO.FS.realPath path
      | none => IO.FS.createTempDir
    let runtime ← IO.FS.realPath runtime
    let repository ← IO.FS.realPath "."
    if runtime == repository || runtime.toString.startsWith (repository.toString ++ "/") then
      throwError "the owner-admission runtime directory must be outside the source checkout"
    let configuration := runtime / s!"operation-owner-admission-{condition}.json"
    let inspect ← Harness.empty
    let (portable, _) ← realizedParameterData inspect selected.trace #[selected.owner]
    let #[portable] := portable
      | throwError "the portable target witness lost its one complete owner descriptor"
    unless portable.ownership.isEmpty &&
        (portable.json.getObjValAs? String "ctor").toOption == some "functorAction" do
      throwError "the portable witness must exercise actual data shaped like an action recipe"
    let config := Json.mkObj [
      ("mode", toJson (if condition == "owned-output" then "passthrough" else "replace")),
      ("operation", toJson selected.actions[2]!.id.raw),
      ("value", Backend.ComputationalValue.encode (.inline portable.json)),
      ("delegate", Json.mkObj [("command", toJson "python3"),
        ("args", toJson (#["probe_owned_callable.py", "--require-argument-owner"] ++
          selected.actions.map (·.id.raw))), ("root", toJson directory.toString)])]
    IO.FS.writeFile configuration (config.pretty ++ "\n")
    let base ← Harness.ofManifest directory (manifest selected configuration)
    try
      unless base.rejected.isEmpty && base.admitted.size == 9 do
        throwError "the existing owner-admission ports were not all admitted"
      let calls ← IO.mkRef #[]
      let harness ← withScope base "owner-target" calls (condition == "ambiguous")
      let foreign ← if condition == "foreign" then do
        -- Separate result caches model independently formed questions. Their
        -- process/session records and positioned service operands are shared;
        -- the only transferred result is an actually returned typed callable.
        let priorCalls ← IO.mkRef #[]
        let prior ← withScope base "owner-foreign" priorCalls
        let (value, _, _) ← operationTerm selected
        let .morphism formal _ _ _ _ := value
          | throwError "the foreign argument lost its complete generalized map"
        let actual ← realizeArrowObservation prior selected.trace
          (← realize prior selected.trace "the independently computed foreign argument" formal)
        unless actual.owner?.map Prod.fst == some "owner-foreign" do
          throwError "the independent argument was not supplied by its real foreign process"
        harness.results.modify (·.insert formal actual)
        pure (some value)
      else pure none
      let source ← realize harness selected.trace "the actually owned original ring" selected.source
      unless source.owner?.map Prod.fst == some "owner-source" &&
          (← calls.get).size == 1 && (← harness.actions.get).size == 1 do
        throwError "the prospective owner did not start with one actual source-owned packet"
      let (_, formal, parameters) ← operationTerm selected foreign
      let recipe ← realizeUnobserved harness selected.trace "the target operation recipe" formal
      let request ← prepareOperationObservation harness selected.trace recipe selected.operation.id parameters
      let candidates ← operationObservationRegistrations harness request
      unless (← calls.get).size == 1 && (← harness.actions.get).size == 1 do
        throwError "prospective target admission executed an owner action"
      if condition == "ambiguous" then
        unless candidates.size == 2 &&
            (← expectedFailure .ambiguousRealization (executeOperationObservation harness request)) &&
            (← calls.get).size == 1 do
          throwError "prospective target peers were hidden until after owner execution"
      else if condition == "foreign" then
        unless candidates.isEmpty &&
            (← expectedFailure .noImplementation (executeOperationObservation harness request)) &&
            (← calls.get).size == 1 do
          throwError "prospective owner substitution erased an unrelated actual argument supplier"
      else
        let #[candidate] := candidates
          | throwError "the owned source pre-eliminated its prospective target backend"
        unless candidate.registration.backend == "owner-target" do
          throwError "prospective admission selected a source process for the target operation"
        if condition == "owned-output" then
          unless (← expectedFailure .noImplementation (executeOperationObservation harness request)) &&
              (← calls.get).size == 3 do
            throwError "an incompatible actual owner escaped the pinned target registration"
        else
          let actual ← executeOperationObservation harness request
          let events ← calls.get
          unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
              (selected.actions.map fun action => some action.id.raw) ++ #[some selected.operation.id.raw] do
            throwError "the portable target did not consume the ordered actual owner actions"
          let #[first, second, third] ← harness.actions.get
            | throwError "the portable target lost its original action receipts"
          unless first.result.fragment == second.input.fragment &&
              second.result.fragment == third.input.fragment && third.result.fragment == portable &&
              third.input.owner?.map Prod.fst == some "owner-source" &&
              actual.owner?.map Prod.fst == some "owner-target" do
            throwError "portable owner execution changed an actual intermediate packet or supplier"
          let .ok sent := events[3]!.getObjVal? "request"
            | throwError "the target operation lost its complete invocation"
          let .ok invocation := Backend.PointInvocation.decode sent
            | throwError "the target operation lost its released generalized-point framing"
          unless invocation.parameters == #[portable.json] &&
              (events[3]!.getObjValAs? String "backend").toOption == some "owner-target" &&
              (events[3]!.getObjVal? "inputOwnership").toOption == some (toJson (#[] : DataOwnership.Table)) do
            throwError "the target operation retained a source supplier after portable export"
          -- Actual receive provenance survives even if a caller did not copy
          -- the convenience observed flag; returned action-shaped bytes stay data.
          let reused ← realizeObjectObservation harness selected.trace
            { third.result with objectObserved := false }
          unless reused.fragment == portable && (← calls.get).size == 4 do
            throwError "actual portable data were reinterpreted as an unexecuted action recipe"
    finally
      base.stop
      if suppliedRuntime.isNone then IO.FS.removeDirAll runtime

end
end CasCatalogue.OperationOwnerAdmissionProbes
