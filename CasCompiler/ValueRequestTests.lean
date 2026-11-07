module

import CasCompiler.Program
public meta import Lean.Elab.Command
meta import CasCompiler.Program

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalarRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let callableRole ← SourceLayout.ofTerm (← empty.close (mkConst ``Fin.last))
  let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Fin.last]
  let recordRole ← SourceLayout.ofTerm (← empty.close pair)
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (scalars, scalar) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "retained scalar".toUTF8)
  let (functions, callable) ← liftM (m := IO) <| scalars.stage owners.identities
    { program, occurrence, role := callableRole, parameters := #[] } (.closure program #[])
  let (graph, record) ← liftM (m := IO) <| functions.stage owners.identities
    { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar, callable])
  withLocalDeclD `extra (mkConst ``Nat) fun extra => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"value-request", 0⟩, role := .parameter, expression := extra }]
    let projectionOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let projection ← PreparedRequest.forProjection owners.identities program projectionOccurrence context graph record 1 #[]
    let .project operand field := projection.action
      | throwError "projection preparation changed its action"
    unless operand.value == record.value && field.sourceIndex == 1 && field.wireIndex == some 1 do
      throwError "projection preparation changed the retained operand or source field"
    unless projection.source.address == #[``Prod.snd] &&
        projection.source.source.context.entries.size == 1 do
      throwError "projection preparation lost its address or complete current context"
    let .ok projected := graph.project record 1
      | throwError "the stored field could not be projected"
    let .ok response := CandidateResponse.ofValue projection.source graph projected
      | throwError "the stored callable field could not fill the prepared response"
    unless response.root.value == callable.value do
      throwError "response preparation replaced the actual projected field"
    let argument ← context.close (mkNatLit 7)
    let .ok parameter := RuntimeParameter.ofValue graph ⟨"value-request", 0⟩ scalar
      | throwError "the actual source parameter is outside its graph"
    let applicationOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let .ok actualArgument := RuntimeArgument.ofValue graph 0 scalar
      | throwError "the actual callable argument is outside its graph"
    let application ← PreparedRequest.forApplication owners.identities program applicationOccurrence context
      response.root #[argument] #[actualArgument] #[parameter]
    let .ok (some supplied) := application.environment.lookup ⟨"value-request", 0⟩
      | throwError "the prepared application lost a supplied source binding"
    unless supplied.value == scalar.value && application.environment.values.size == 1 do
      throwError "the prepared runtime environment changed its source/value correspondence"
    unless application.origin.program == program &&
        application.origin.occurrence == applicationOccurrence &&
        application.origin.parameters.size == 1 &&
        (application.origin.parameters[0]?.bind id).map (·.value) == some scalar.value do
      throwError "the prepared result origin lost its actual producing context"
    let (produced, result) ← liftM (m := IO) <| graph.stage owners.identities application.origin
      (.portable "candidate field data".toUTF8)
    let some node := produced.find result.value
      | throwError "the prepared application origin could not stage its result"
    unless node.origin.role.source.context.entries.size == 1 &&
        node.references.map (·.value) == #[scalar.value, scalar.value, callable.value, scalar.value] do
      throwError "staging a prepared result discarded its complete producing context"
    let some preparedRecord := application.record
      | throwError "the dependent application did not prepare its complete result record"
    unless preparedRecord.fields.size == 2 &&
        preparedRecord.fields[0]?.map (·.field.wireIndex) == some (some 0) &&
        preparedRecord.fields[1]?.map (·.field.kind) == some .proof do
      throwError "request preparation lost computational or formal proof positions"
    let .apply retained arguments values := application.action
      | throwError "application preparation changed its action"
    unless retained.value == callable.value && arguments.size == 1 && values.size == 1 &&
        (values[0]?.bind id).map (·.value) == some scalar.value &&
        application.scope.size == 2 do
      throwError "application preparation lost its callable or argument scope"
    application.source.source.withOpen fun _ expression => do
      unless ← isDefEq (← inferType expression)
          (mkApp (mkConst ``Fin) (mkNatLit 8)) do
        throwError "application preparation lost its dependent result type"
    let rejected ← try
      discard <| PreparedRequest.forApplication owners.identities program occurrence context record
        #[argument] #[actualArgument] #[]
      pure false
    catch _ => pure true
    unless rejected do throwError "application accepted a value without a retained callable interface"
    let rejectedField ← try
      discard <| PreparedRequest.forProjection owners.identities program occurrence context graph record 2 #[]
      pure false
    catch _ => pure true
    unless rejectedField do throwError "projection accepted a field outside the source layout"
    match CandidateResponse.ofValue projection.source graph scalar with
    | .error _ => pure ()
    | .ok _ => throwError "a portable scalar filled a prepared callable response"
  let (malformed, incomplete) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar])
  match CandidateResponse.ofValue recordRole malformed incomplete with
  | .error _ => pure ()
  | .ok _ => throwError "a candidate record lost a required source field"
  let finiteRole ← SourceLayout.ofTerm (← empty.close (mkApp (mkConst ``Fin.last) (mkNatLit 7)))
  let (finiteGraph, finite) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := finiteRole, parameters := #[] } (.product #[scalar])
  let rejectedProof ← try
    discard <| PreparedRequest.forProjection owners.identities program occurrence empty finiteGraph finite 1 #[]
    pure false
  catch _ => pure true
  unless rejectedProof do throwError "a source proof field acquired a computational projection"
  let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  try
    let token ← liftM (m := IO) do
      child.child.stdin.putStr "retained native record\n"
      child.child.stdin.flush
      return (← child.child.stdout.getLine).trimAscii.toString
    let (nativeGraph, nativeRecord) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role := recordRole, parameters := #[] } (.ownedExport child token #[])
    let .ok response := CandidateResponse.ofValue recordRole nativeGraph nativeRecord
      | throwError "the native record candidate lost its retained root"
    unless response.root.value == nativeRecord.value do
      throwError "the native record candidate was rebuilt from fields"
    let some node := nativeGraph.find response.root.value
      | throwError "the native record root is missing"
    unless node.references.isEmpty && node.owners == #[child.generation] do
      throwError "candidate shape checking changed lazy captures or actual owners"
  finally liftM (m := IO) <| owners.close child.generation

example (request : PreparedRequest) : OperationalProgram (PreparedResponse request) :=
  PFunctor.FreeM.lift (P := OperationalSignature) request
