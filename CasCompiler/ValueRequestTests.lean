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
      { program, occurrence, role := scalarRole } (.portable "retained scalar".toUTF8)
  let (functions, callable) ← liftM (m := IO) <| scalars.stage owners.identities
    { program, occurrence, role := callableRole } (.closure program #[])
  let (graph, record) ← liftM (m := IO) <| functions.stage owners.identities
    { program, occurrence, role := recordRole } (.product #[scalar, callable])
  withLocalDeclD `extra (mkConst ``Nat) fun extra => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"value-request", 0⟩, role := .parameter, expression := extra }]
    let projection ← PreparedRequest.forProjection program occurrence context record 1
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
    let application ← PreparedRequest.forApplication program occurrence context
      response.root #[argument] #[scalar]
    let .apply retained arguments := application.action
      | throwError "application preparation changed its action"
    unless retained.value == callable.value && arguments.size == 1 &&
        application.scope.size == 2 do
      throwError "application preparation lost its callable or argument scope"
    application.source.source.withOpen fun _ expression => do
      unless ← isDefEq (← inferType expression)
          (mkApp (mkConst ``Fin) (mkNatLit 8)) do
        throwError "application preparation lost its dependent result type"
    let rejected ← try
      discard <| PreparedRequest.forApplication program occurrence context record #[argument] #[scalar]
      pure false
    catch _ => pure true
    unless rejected do throwError "application accepted a value without a retained callable interface"
    let rejectedField ← try
      discard <| PreparedRequest.forProjection program occurrence context record 2
      pure false
    catch _ => pure true
    unless rejectedField do throwError "projection accepted a field outside the source layout"
    match CandidateResponse.ofValue projection.source graph scalar with
    | .error _ => pure ()
    | .ok _ => throwError "a portable scalar filled a prepared callable response"

example (request : PreparedRequest) : OperationalProgram (CandidateResponse request.source) :=
  PFunctor.FreeM.lift (P := OperationalSignature) request
