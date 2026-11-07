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
      for source in arguments, value in actual do
        let some value := value | throwError "a supplied source operand is absent"
        unless (← value.role.source.inContext context) == (← source.inContext context) do
          throwError "callable preparation changed the native consuming source argument"
      let .ok rightAlias := RuntimeParameter.ofValue graph bindings[1]!.id leftValue
        | throwError "the aliased source parameter is absent"
      let aliased ← PreparedRequest.forApplication program occurrence context callable arguments
        #[← argument 1 leftValue, ← argument 0 leftValue] #[leftParameter, rightAlias]
      let .apply _ formal actual := aliased.action
        | throwError "aliased argument preparation changed its action"
      unless actual.size == 2 && formal[0]?.map (·.expression) != formal[1]?.map (·.expression) &&
          (actual[0]?.bind id).map (·.value) == some leftValue.value &&
          (actual[1]?.bind id).map (·.value) == some leftValue.value &&
          aliased.scope.map (·.value) == #[callable.value, leftValue.value, leftValue.value] do
        throwError "callable preparation merged aliased values in distinct source arguments"
      reject "the source argument has no retained runtime binding" do
        discard <| PreparedRequest.forApplication program occurrence context callable arguments
          #[← argument 0 leftValue] #[rightParameter]
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
      let some layout := request.application
        | throwError "proof-bearing application lost its complete source argument layout"
      unless layout.arguments.map (·.wireIndex) == #[none, some 0] &&
          layout.arguments[0]?.map (·.source.kind) == some .proof do
        throwError "formal proof erasure changed the native application's wire positions"
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

-- A source callable and its let alias retain their own native application heads.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← empty.close (mkConst ``Nat.add))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, original) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role, parameters := #[] } (.closure program #[])
  withLocalDeclD `f (← inferType (mkConst ``Nat.add)) fun f => do
    withLetDecl `g (← inferType f) f fun g => do
      let bindings : Array LocalBinding := #[
        { id := ⟨"callable-source", 0⟩, role := .parameter, expression := f },
        { id := ⟨"callable-source", 1⟩, role := .definition, expression := g }]
      let context ← ContextTelescope.capture bindings
      let mut parameters := #[]
      for binding in bindings do
        let .ok parameter := RuntimeParameter.ofValue graph binding.id original
          | throwError "the source callable parameter is absent"
        parameters := parameters.push parameter
      let environment ← RuntimeEnvironment.capture owners.worker context parameters
      for binding in bindings do
        let .ok (some callable) := environment.lookup binding.id
          | throwError "the source callable binding is absent"
        unless callable.value == original.value &&
            (← callable.role.source.inContext context) == binding.expression do
          throwError "runtime capture changed the native source callable binding"
        let arguments := #[← context.close (mkNatLit 2), ← context.close (mkNatLit 3)]
        let request ← PreparedRequest.forApplication program occurrence context callable arguments
          #[] parameters
        let application ← request.source.source.inContext context
        unless application.getAppFn == binding.expression do
          throwError "callable preparation changed the native source application head"
      let some node := graph.find original.value
        | throwError "the original callable node is absent"
      unless (← node.origin.role.source.inContext context) == mkConst ``Nat.add do
        throwError "source association changed the original callable producer"

-- Formal argument dependency survives substitution of a closed source index.
run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `point (mkApp (mkConst ``Fin) (mkNatLit 7)) fun point => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"application-dependencies", 0⟩, role := .parameter, expression := point }]
    let function ← Elab.Term.elabTermAndSynthesize
      (← `(fun (n : Nat) (x : Fin n) => x)) none
    let role ← SourceLayout.ofTerm (← context.close function)
    let owners ← liftM (m := IO) OwnerRegistry.new
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let (_, callable) ← liftM (m := IO) <|
      (ValueGraph.empty owners.identities).stage owners.identities
        { program, occurrence, role, parameters := #[none] } (.closure program #[])
    let request ← PreparedRequest.forApplication program occurrence context callable
      #[← context.close (mkNatLit 7), ← context.close point] #[] #[]
    let some layout := request.application
      | throwError "application preparation lost its native argument telescope"
    unless request.source.contextDependencies.isEmpty && layout.arguments.size == 2 &&
        layout.arguments[0]?.map (·.precedingDependencies) == some #[] &&
        layout.arguments[1]?.map (·.precedingDependencies) == some #[0] &&
        layout.arguments.map (·.wireIndex) == #[some 0, some 1] &&
        layout.resultDependencies == #[0] do
      throwError "source index substitution erased an actual argument's dependent role"
    layout.resultTypeFamily.withOpen fun _ family =>
      lambdaTelescope family fun arguments result => do
        unless arguments.size == 2 && result.isAppOf ``Fin &&
            result.appArg! == arguments[0]! do
          throwError "application preparation changed its complete native result-type family"
    let partialRequest ← PreparedRequest.forApplication program occurrence context callable
      #[← context.close (mkNatLit 7)] #[] #[]
    let some partialLayout := partialRequest.application
      | throwError "partial application lost its native argument telescope"
    unless partialRequest.source.kind == .function && partialLayout.arguments.size == 1 &&
        partialLayout.resultDependencies == #[0] do
      throwError "partial application erased a retained argument from its remaining function type"
