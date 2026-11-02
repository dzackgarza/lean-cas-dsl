/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Realize
meta import CasCatalogue.Realize

@[expose] public section

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

namespace CasAcceptance.SelectedOwnerFixture
meta section

/-! Engineering setup for the existing inherited-operation controls. The original
selected candidate owns its exact source action. That action is completed through
its real typed producer before the operation-only control starts. The process
returns arbitrary opaque data; these checks assert no mathematical answer. -/

structure Setup where
  operationHarness : Harness
  ownerHarness : Harness
  ownerCalls : IO.Ref (Array Json)
  operationCalls : IO.Ref (Array Json)
  entry : OperationEntry
  selected : OperationCandidate
  source : OperationSource
  action : FunctorEntry
  application : Expr

/-- Admit the original owner's existing action in a separate setup view. Both
views share the actual process, producer receipts, and operand tables. Neither
view resets an event counter or inserts a computed value into the result cache. -/
def harness (root : System.FilePath) (program : BackendProgram)
    (registration : Registration) (calls : IO.Ref (Array Json))
    (entry : OperationEntry) (selected : OperationCandidate) : TermElabM Setup := do
  unless registration.operation == selected.operation.raw && entry.id == selected.operation &&
      registration.input == entry.category.raw && registration.backend == program.name do
    throwError "the owner setup changed the original selected operation registration"
  let #[source] := selected.sources
    | throwError "the owner setup requires the original one complete source occurrence"
  let #[.functor id] := source.route
    | throwError "the owner setup requires the original one selected owner action"
  let #[application] := source.applications
    | throwError "the owner setup lost the original action application"
  let some action := (← registryState).functors.find? (·.id == id)
    | throwError "the owner setup lost its existing action declaration"
  unless program.command == "python3" && program.args[0]? == some "probe_owned_callable.py" do
    throwError "the owner setup requires the existing arbitrary ownership process"
  -- This existing mode returns an opaque result even after the owner parameter
  -- has become owned. Its later point requests also require the prior argument.
  let arguments := if program.args.contains "--require-argument-owner" then program.args
    else program.args.push "--require-argument-owner"
  let program := { program with args := arguments.push action.id.raw }
  let ownerRegistration : Registration := {
    operation := action.id.raw, input := action.inputAddress, backend := program.name }
  let base ← Harness.ofManifest root {
    backends := #[program], registrations := #[ownerRegistration, registration] }
  unless base.rejected.isEmpty && base.admitted.size == 2 do
    throwError "the original owner action and operation setup ports were not admitted"
  let ownerCalls ← IO.mkRef #[]
  let operationHarness := { base with
    admitted := base.admitted.filter (·.registration.operation == selected.operation.raw)
    dispatches := some calls }
  let ownerHarness := { base with
    admitted := base.admitted.filter (·.registration.operation == action.id.raw)
    dispatches := some ownerCalls, demandObjectActions := true }
  unless operationHarness.admitted.size == 1 && ownerHarness.admitted.size == 1 do
    throwError "the owner setup mixed its two independently checked execution phases"
  return {
    operationHarness, ownerHarness, ownerCalls, operationCalls := calls,
    entry, selected, source, action,
    application := ← instantiateMVars (← Semantic.asFunctor application) }

/-- Complete precisely the selected candidate's owner using its existing
retained producer. The action receipt authenticates the original input,
application, ordered parameters, returned packet, and live supplier. -/
def completeOwner (setup : Setup) (trace : Trace) : TermElabM Wire := do
  unless (← setup.ownerCalls.get).isEmpty && (← setup.operationCalls.get).isEmpty &&
      (← setup.ownerHarness.actions.get).isEmpty do
    throwError "the owner setup started with an already executed control"
  let pending ← realizedOperationOwner
    { setup.ownerHarness with demandObjectActions := false }
    trace setup.entry setup.selected.application
  let some recipe := pending.actionRecipe
    | throwError "the original selected owner lost its retained action producer"
  unless !pending.completedData && !recipe.morphism &&
      recipe.owner == .edge (.functor setup.action.id) &&
      Expr.equal recipe.application setup.application &&
      Expr.equal recipe.original.value setup.source.receiver &&
      recipe.source.expression.syntacticEq setup.source.context.expression do
    throwError "the owner setup changed an original complete action or source occurrence"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq recipe.source.bundle setup.source.context.bundle) do
    throwError "the owner setup changed the original complete source category"
  let (descriptor, dependencies) ← renderCapturedActionData recipe.descriptor
  let (operation, parameters) ← edgeActionDataInvocation (← registryState)
    (.functor setup.action.id) descriptor false
  unless (← setup.ownerCalls.get).isEmpty && (← setup.operationCalls.get).isEmpty do
    throwError "capturing the original owner executed a port"
  let actual ← realizeObjectObservation setup.ownerHarness trace pending
  let #[event] ← setup.ownerCalls.get
    | throwError "the original owner action did not execute exactly once during setup"
  let #[receipt] ← setup.ownerHarness.actions.get
    | throwError "the original owner action lost its one real execution receipt"
  let .ok request := event.getObjVal? "request"
    | throwError "the original owner action lost its complete request"
  unless (event.getObjValAs? String "operation").toOption == some operation &&
      (request.getObjVal? "receiver").toOption == some recipe.original.json &&
      receipt.operation == operation && Expr.equal receipt.action setup.application &&
      Expr.equal receipt.input.value recipe.original.value &&
      receipt.input.fragment == recipe.original.fragment &&
      receipt.parameters == parameters.map (·.json) &&
      receipt.parameterOwnership == (DataOwnership.Data.array parameters).ownership &&
      sameActionOperands receipt.parameterInputs dependencies &&
      Expr.equal actual.value pending.value && actual.objectObserved && actual.actualData &&
      actual.fragment == receipt.result.fragment && actual.owner?.isSome &&
      actual.owner? == receipt.result.owner? && (← setup.operationCalls.get).isEmpty do
    throwError "the completed owner changed its original producer, packet, or supplier"
  checkDataOwners setup.ownerHarness actual.fragment
  let reused ← realizeObjectObservation setup.ownerHarness trace pending
  unless Expr.equal reused.value actual.value && reused.fragment == actual.fragment &&
      reused.owner? == actual.owner? && (← setup.ownerCalls.get).size == 1 &&
      (← setup.ownerHarness.actions.get).size == 1 do
    throwError "the original owner producer was recomputed during setup reuse"
  return actual

/-- Every operation phase consumes the one completed owner at its original
parameter position. The original operation-count checks remain at each caller. -/
def checkOwnerReuse (setup : Setup) (owner : Wire) : TermElabM Unit := do
  unless (← setup.ownerCalls.get).size == 1 &&
      (← setup.ownerHarness.actions.get).size == 1 do
    throwError "the operation phase recomputed the separately completed owner"
  for event in ← setup.operationCalls.get do
    let .ok request := event.getObjVal? "request"
      | throwError "the operation lost its original complete request"
    let .ok invocation := Backend.PointInvocation.decode request
      | throwError "the operation lost its original public point interface"
    unless invocation.operation == setup.selected.operation.raw &&
        invocation.parameters == #[owner.json] do
      throwError "the operation replaced its completed selected owner parameter"

/-- Preserve the full original node equality without recursively printing its
shared expression graph. Unlike Expr's ordinary BEq, Expr.equal retains binder
names and annotations as well as every original ordered expression field. -/
def sameOriginalNode (left right : Node) : Bool :=
  let first := left.producerDescription
  let second := right.producerDescription
  first.1 == second.1 && first.2.size == second.2.size &&
    (first.2.zip second.2).all (fun (a, b) => Expr.equal a b)

end
end CasAcceptance.SelectedOwnerFixture
