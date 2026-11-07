module

import CasCompiler.Program
public meta import Lean.Elab.Command
meta import CasCompiler.Program

open Lean Meta CasCompiler CasRuntime

private def reject (expected : String) (action : MetaM α) : MetaM Unit := do
  let failure : Option Exception ← try
    discard action
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "callable preparation accepted invalid runtime arguments"
  unless (← failure.toMessageData.toString).startsWith expected do throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let leftRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 2))
  let rightRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 3))
  let callableRole ← SourceLayout.ofTerm (← empty.close (mkConst ``Nat.add))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, leftValue) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := leftRole, parameters := #[] } (.portable "2".toUTF8)
  let (graph, rightValue) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := rightRole, parameters := #[] } (.portable "3".toUTF8)
  let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := callableRole, parameters := #[] } (.closure program #[])
  withLocalDeclD `left (mkConst ``Nat) fun left =>
    withLocalDeclD `right (mkConst ``Nat) fun right => do
      let bindings : Array LocalBinding := #[
        { id := ⟨"application-context", 0⟩, role := .parameter, expression := left },
        { id := ⟨"application-context", 1⟩, role := .parameter, expression := right }]
      let context ← ContextTelescope.capture bindings
      let .ok leftParameter := RuntimeParameter.ofValue graph bindings[0]!.id leftValue
        | throwError "the actual left source parameter is absent"
      let .ok rightParameter := RuntimeParameter.ofValue graph bindings[1]!.id rightValue
        | throwError "the actual right source parameter is absent"
      let parameters := #[leftParameter, rightParameter]
      let argument (index : Nat) (value : ValueBinding) : MetaM RuntimeArgument := do
        let .ok argument := RuntimeArgument.ofValue graph index value
          | throwError "the actual application argument is absent"
        return argument
      let arguments := #[← context.close left, ← context.close right]
      let request ← PreparedRequest.forApplication program occurrence context callable arguments
        #[← argument 1 rightValue, ← argument 0 leftValue] parameters
      let .apply original formal actual := request.action
        | throwError "the application lost its original prepared action"
      unless original.value == callable.value && formal.size == 2 && actual.size == 2 &&
          (actual[0]?.bind id).map (·.value) == some leftValue.value &&
          (actual[1]?.bind id).map (·.value) == some rightValue.value &&
          request.scope.map (·.value) == #[callable.value, leftValue.value, rightValue.value] do
        throwError "callable preparation changed the complete source argument order or actual values"
      reject "the runtime argument does not retain its specified source value" do
        discard <| PreparedRequest.forApplication program occurrence context callable arguments
          #[← argument 0 rightValue, ← argument 1 leftValue] parameters
      reject "a callable source argument has duplicate runtime bindings" do
        discard <| PreparedRequest.forApplication program occurrence context callable arguments
          #[← argument 0 leftValue, ← argument 0 leftValue] parameters
      reject "a runtime argument is outside the complete callable argument list" do
        discard <| PreparedRequest.forApplication program occurrence context callable arguments
          #[← argument 2 leftValue] parameters
      reject "the runtime argument does not retain its specified source value" do
        discard <| PreparedRequest.forApplication program occurrence context callable
          #[← context.close (mkNatLit 2), ← context.close (mkNatLit 3)]
          #[← argument 0 rightValue, ← argument 1 leftValue] parameters
      let function ← Elab.Term.elabTermAndSynthesize (← `(fun (_h : True) (n : Nat) => n)) none
      let layout ← SourceLayout.ofTerm (← context.close function)
      let (graph, function) ← liftM (m := IO) <| graph.stage owners.identities
        { program, occurrence, role := layout, parameters := #[some leftValue, some rightValue] }
        (.closure program #[])
      let formal := #[← context.close (mkConst ``True.intro), ← context.close left]
      let request ← PreparedRequest.forApplication program occurrence context function formal
        #[← argument 1 leftValue] parameters
      let .apply _ _ actual := request.action
        | throwError "proof erasure changed the application action"
      unless actual.size == 2 && (actual[0]?.bind id).isNone &&
          (actual[1]?.bind id).map (·.value) == some leftValue.value do
        throwError "a formal proof displaced a later actual application argument"
      let .ok suppliedProof := RuntimeArgument.ofValue graph 0 leftValue
        | throwError "the proof-position rejection control is absent"
      reject "a formal proof argument has no runtime value binding" do
        discard <| PreparedRequest.forApplication program occurrence context function formal
          #[suppliedProof, ← argument 1 leftValue] parameters
