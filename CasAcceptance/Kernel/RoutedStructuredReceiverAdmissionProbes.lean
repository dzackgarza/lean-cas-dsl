/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasAcceptance.Standard
import CasCatalogue.TestSuite
meta import CasAcceptance.Standard
meta import CasCatalogue.TestSuite

/-! Engineering guards for the original RegistrationProbes product question.
The unchanged question and existing protocol fixture supply every input. These
controls inspect admission, canonical ownership and exact packet retention;
they add no mathematical assertion or expected computational answer. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasCatalogue.RoutedStructuredReceiverAdmissionProbes
meta section

private structure Control where
  question : PreparedQuestion
  trace : Trace
  pending : Wire
  invocation : CapturedInvocation
  selected : SelectedRoutedInvocation
  original : InvocationExecution
  construction : SelectedStructuredInvocation

private def capture (h : Harness) : TermElabM Control := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert |Fin(2) × ℤ/3| = 6"
    | throwError "the unchanged product question did not parse"
  let question ← prepare {} parsed
  let methods := question.trace.toArray.filterMap fun (formal, node) => match node with
    | .method id route _ _ application => some (formal, id, route, application)
    | _ => none
  let #[(formal, id, route, application)] := methods
    | throwError "the original product question lost its one selected method"
  let trace ← IO.mkRef question.trace
  let pending ← realizeUnobserved h trace "the original product method" formal
  let some invocation ← retainedCapturedInvocation? pending
    | throwError "the original method lost its canonical preparation"
  let .routed selected := invocation.interface
    | throwError "the original method changed its captured interface"
  let expectedActions := route.zip application.routeApplications
  unless selected.method.id == id &&
      selected.canonical.prefixActions.size == expectedActions.size &&
      (selected.canonical.prefixActions.zip expectedActions).all (fun (actual, expected) =>
        actual.1 == expected.1 && Expr.equal actual.2 expected.2) &&
      sameCompleteWireContext selected.original selected.canonical.receiver do
    throwError "the method changed its original complete route or source occurrence"
  let some source ← retainedCapturedInvocation? selected.original
    | throwError "the original product lost its typed producer reference"
  let frame ← capturedInvocationFrame h selected.original source
  let .structured construction := frame.record.captured.interface
    | throwError "the original receiver is no longer its selected construction"
  unless construction.address == "lim.sets.product" && construction.creation.isNone &&
      frame.record.result.isNone do
    throwError "the product control changed its original pending construction"
  return {
    question := question
    trace := trace
    pending := pending
    invocation := invocation
    selected := selected
    original := frame.record
    construction := construction }

private def originalOwners (h : Harness) (control : Control) :
    TermElabM (InvocationExecution × InvocationExecution) := do
  let records ← h.invocations.get
  let #[source] := records.filter (fun record => match record.captured.interface with
    | .structured _ => true | _ => false)
    | throwError "the original product acquired a replacement producer"
  let #[method] := records.filter (fun record => match record.captured.interface with
    | .routed _ => true | _ => false)
    | throwError "the original method lost its unique canonical owner"
  let methodFrame ← capturedInvocationFrame h control.pending control.invocation
  unless source.prepared.same control.original.prepared &&
      method.prepared.same methodFrame.record.prepared &&
      Expr.equal source.input.value control.original.input.value &&
      sameCompleteWireContext source.input control.original.input && method.result.isNone do
    throwError "admission changed an original producer input or completed an unselected method"
  for (formal, before) in control.question.trace.toArray do
    let some after := (← control.trace.get)[formal]?
      | throwError "execution discarded an original semantic record"
    let first := before.producerDescription
    let second := after.producerDescription
    unless first.1 == second.1 && first.2.size == second.2.size &&
        (first.2.zip second.2).all (fun (a, b) => Expr.equal a b) do
      throwError "admission changed the original mathematical question"
  return (source, method)

private def failsAs (expected : Stratum) (action : TermElabM Wire) : TermElabM Unit := do
  let rejected ← try
    discard action
    pure false
  catch error =>
    if !Exception.hasConflictingStrata error && Exception.stratum? error == some expected then
      pure true
    else throw error
  unless rejected do throwError "the original method did not reject at the required boundary"

private def withFixture (action : Harness → IO.Ref (Array Json) → TermElabM Unit) :
    TermElabM Unit := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let base ← Harness.load (some (root / "registration_limits.json"))
  unless base.rejected.isEmpty && base.admitted.size == 3 do
    throwError "the unchanged product manifest lost its original admitted interfaces"
  let calls ← IO.mkRef (#[] : Array Json)
  let h := { base with dispatches := some calls }
  try action h calls finally base.stop

-- Removing only the selected method's registrations must not compute its
-- original product just to discover that no method implementation is installed.
run_elab withFixture fun base calls => do
  let control ← capture base
  let admitted := base.admitted.filter
    (·.registration.operation != control.selected.method.id.raw)
  let h := { base with admitted }
  unless h.admitted.size == 2 do
    throwError "the missing-method guard changed an original construction registration"
  let (_, registration) ← routedInvocationRegistrations h control.trace
    control.pending control.selected
  unless registration.isNone do throwError "an absent method acquired a registration"
  failsAs .noImplementation <| observeCapturedInvocation h control.trace
    control.pending control.invocation
  let (source, _) ← originalOwners h control
  unless source.result.isNone && (← calls.get).isEmpty &&
      (← h.connections.get).isEmpty && (← h.actions.get).isEmpty &&
      (← h.replies.get).isEmpty do
    throwError "a method with no installed registration dispatched its original producer"

-- The original named-form row is initially inapplicable to an unknown apex.
-- Once that same product completes, a category-wide peer must be reconsidered
-- together with it, before either method implementation is dispatched.
run_elab withFixture fun base calls => do
  let control ← capture base
  let #[named] := base.admitted.filter
    (·.registration.operation == control.selected.method.id.raw)
    | throwError "the original product manifest lost its one named method row"
  let categoryInput := control.selected.original.form.category.raw
  let peer : Registration := {
    operation := named.registration.operation, input := categoryInput,
    backend := named.registration.backend }
  let admission := (← registryState).admit {
    backends := base.backends, registrations := #[peer] }
  unless admission.rejected.isEmpty && admission.admitted.size == 1 &&
      named.registration.input != peer.input do
    throwError "the existing method has no distinct admitted category-wide peer"
  let h := { base with admitted := base.admitted ++ admission.admitted }
  let (_, initial) ← routedInvocationRegistrations h control.trace control.pending control.selected
  unless initial.any (sameRegistration peer) && (← calls.get).isEmpty &&
      (← h.replies.get).isEmpty do
    throwError "initial admission did not retain its sole known peer without dispatch"
  failsAs .ambiguousRealization <| observeCapturedInvocation h control.trace
    control.pending control.invocation
  let (source, _) ← originalOwners h control
  let some completed := source.result
    | throwError "actual-form admission omitted the original product's canonical completion"
  checkCapturedResultInterface completed source.captured.interface.result
  checkDataOwners h completed.fragment
  let #[event] ← calls.get
    | throwError "actual-form ambiguity did not dispatch exactly the original product"
  let #[reply] ← h.replies.get
    | throwError "actual-form ambiguity lost the original product's one reply receipt"
  let some (.ok connection) := (← h.connections.get)[reply.backend]?
    | throwError "the original product reply lost its live supplying session"
  let originalInputs ← control.construction.sourceInputs.mapM fun position => do
    let some operand := control.construction.operands[position.operand]?
      | throwError "the original product lost a declared input position"
    unless position.endpoints.isNone && operand.role == .object do
      throwError "the fixed product changed its original object-input roles"
    return operand.wire.fragment
  let originalDiagram ← scopedNode (Codec.label control.construction.standard) originalInputs
  unless reply.operation == control.construction.address &&
      (event.getObjValAs? String "operation").toOption == some reply.operation &&
      (event.getObjVal? "request").toOption == some reply.input.json &&
      (event.getObjVal? "response").toOption == some reply.original &&
      (event.getObjValAs? String "backend").toOption == some reply.backend &&
      (event.getObjValAs? Nat "session").toOption == some reply.session &&
      connection.identity == reply.session &&
      reply.input.fragment == originalDiagram &&
      Expr.equal reply.input.value control.construction.targetDiagram &&
      (← h.actions.get).isEmpty do
    throwError "the product completion changed its selected request, reply, or supplier"
  let some (packet, backend) := reply.completed
    | throwError "the original product reply has no completed packet receipt"
  let some answer := ComputationalData.recordPayload?
      { json := packet, ownership := reply.completedOwnership }
    | throwError "the original product reply lost its complete public data envelope"
  let .ok ("constructionApex", #[identifier, _, _]) := ComputationalData.envelope completed.json
    | throwError "the product completion lost its whole construction packet"
  let diagram ← checkedFragment (completed.fragment.project #[.field "args", .index 1])
  let retainedAnswer ← checkedFragment (completed.fragment.project #[.field "args", .index 2])
  unless identifier == toJson control.construction.resultForm.id &&
      backend == reply.backend && diagram == reply.input.fragment && retainedAnswer == answer do
    throwError "actual-form selection replaced the original diagram or complete returned cone"
  let observed ← realizeObjectObservation h control.trace control.selected.original
  unless Expr.equal observed.value control.selected.original.value &&
      observed.fragment == completed.fragment do
    throwError "the original product reference did not reuse its canonical complete packet"
  failsAs .ambiguousRealization <| observeCapturedInvocation h control.trace
    control.pending control.invocation
  let (reused, _) ← originalOwners h control
  let some reusedResult := reused.result
    | throwError "the original canonical construction completion disappeared"
  unless sameCompleteWireContext reusedResult completed &&
      Expr.equal reusedResult.value completed.value &&
      (← calls.get).size == 1 && (← h.replies.get).size == 1 do
    throwError "rechecking actual-form ambiguity retried or replaced the original producer"

end
end CasCatalogue.RoutedStructuredReceiverAdmissionProbes
