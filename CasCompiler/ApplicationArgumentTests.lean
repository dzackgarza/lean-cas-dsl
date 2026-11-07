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
      let request ← PreparedRequest.forApplication owners.identities program occurrence context callable arguments
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
      let aliased ← PreparedRequest.forApplication owners.identities program occurrence context callable arguments
        #[← argument 1 leftValue, ← argument 0 leftValue] #[leftParameter, rightAlias]
      let .apply _ formal actual := aliased.action
        | throwError "aliased argument preparation changed its action"
      unless actual.size == 2 && formal[0]?.map (·.expression) != formal[1]?.map (·.expression) &&
          (actual[0]?.bind id).map (·.value) == some leftValue.value &&
          (actual[1]?.bind id).map (·.value) == some leftValue.value &&
          aliased.scope.map (·.value) == #[callable.value, leftValue.value, leftValue.value] do
        throwError "callable preparation merged aliased values in distinct source arguments"
      reject "the source argument has no retained runtime binding" do
        discard <| PreparedRequest.forApplication owners.identities program occurrence context callable arguments
          #[← argument 0 leftValue] #[rightParameter]
      reject "the runtime argument does not retain its specified source value" do
        discard <| PreparedRequest.forApplication owners.identities program occurrence context callable arguments
          #[← argument 0 rightValue, ← argument 1 leftValue] parameters
      reject "a callable source argument has duplicate runtime bindings" do
        discard <| PreparedRequest.forApplication owners.identities program occurrence context callable arguments
          #[← argument 0 leftValue, ← argument 0 leftValue] parameters
      reject "a runtime argument is outside the complete callable argument list" do
        discard <| PreparedRequest.forApplication owners.identities program occurrence context callable arguments
          #[← argument 2 leftValue] parameters
      reject "the runtime argument does not retain its specified source value" do
        discard <| PreparedRequest.forApplication owners.identities program occurrence context callable
          #[← context.close (mkNatLit 2), ← context.close (mkNatLit 3)]
          #[← argument 0 rightValue, ← argument 1 leftValue] parameters
      let function ← Elab.Term.elabTermAndSynthesize (← `(fun (_h : True) (n : Nat) => n)) none
      let layout ← SourceLayout.ofTerm (← context.close function)
      let (graph, function) ← liftM (m := IO) <| graph.stage owners.identities
        { program, occurrence, role := layout, parameters := #[some leftValue, some rightValue] }
        (.closure program #[])
      let formal := #[← context.close (mkConst ``True.intro), ← context.close left]
      let request ← PreparedRequest.forApplication owners.identities program occurrence context function formal
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
      let admitted ← request.admitInputs graph
      let .ok values := admitted.arguments graph
        | throwError "the proof-bearing input map is incomplete"
      let some proofRole := request.roles.arguments[0]?
        | throwError "the source proof role was erased from its telescope"
      let some valueRole := request.roles.arguments[1]?
        | throwError "the source data role is absent"
      let .ok bound := admitted.lookup graph valueRole.role.id
        | throwError "the source data role lost its actual binding"
      unless values.map (·.value) == #[leftValue.value] &&
          valueRole.role.id.address == .argument 1 && bound.source == .argument 1 do
        throwError "proof erasure changed the admitted source argument position"
      if (admitted.lookup graph proofRole.role.id).isOk then
        throwError "a formal proof acquired a computational input binding"
      let .ok suppliedProof := RuntimeArgument.ofValue graph 0 leftValue
        | throwError "the proof-position rejection control is absent"
      reject "a formal proof argument has no runtime value binding" do
        discard <| PreparedRequest.forApplication owners.identities program occurrence context function formal
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
        let request ← PreparedRequest.forApplication owners.identities program occurrence context callable arguments
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
    let request ← PreparedRequest.forApplication owners.identities program occurrence context callable
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
    let partialRequest ← PreparedRequest.forApplication owners.identities program occurrence context callable
      #[← context.close (mkNatLit 7)] #[] #[]
    let some partialLayout := partialRequest.application
      | throwError "partial application lost its native argument telescope"
    unless partialRequest.source.kind == .function && partialLayout.arguments.size == 1 &&
        partialLayout.resultDependencies == #[0] do
      throwError "partial application erased a retained argument from its remaining function type"

-- Equal source terms and packets retain distinct scoped input roles and actual occurrences.
run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let scalar ← context.close (mkNatLit 7)
  let role ← SourceLayout.ofTerm scalar
  let function ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.add))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let firstOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let secondOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, callable) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence := firstOccurrence, role := function, parameters := #[] } (.closure program #[])
  let (older, first) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence := firstOccurrence, role, parameters := #[] } (.portable "7".toUTF8)
  let (graph, second) ← liftM (m := IO) <| older.stage owners.identities
    { program, occurrence := secondOccurrence, role, parameters := #[] } (.portable "7".toUTF8)
  let .ok left := RuntimeArgument.ofValue graph 0 first
    | throwError "the first equal-term input is absent"
  let .ok right := RuntimeArgument.ofValue graph 1 second
    | throwError "the second equal-term input is absent"
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let request ← PreparedRequest.forApplication owners.identities program occurrence context callable
    #[scalar, scalar] #[right, left] #[]
  let admitted ← request.admitInputs graph
  let some firstRole := request.roles.arguments[0]?
    | throwError "the first scoped role is absent"
  let some secondRole := request.roles.arguments[1]?
    | throwError "the second scoped role is absent"
  let .ok firstBinding := admitted.lookup graph firstRole.role.id
    | throwError "the first role lost its input"
  let .ok secondBinding := admitted.lookup graph secondRole.role.id
    | throwError "the second role lost its input"
  unless firstRole.role.source.expression == secondRole.role.source.expression &&
      firstRole.role.id != secondRole.role.id && first.value != second.value &&
      firstBinding.value.value == first.value && secondBinding.value.value == second.value do
    throwError "the role map merged equal source terms or distinct actual occurrences"
  if (admitted.lookup older firstRole.role.id).isOk then
    throwError "a role map recovered an input outside its visible snapshot"
  let .ok aliasedArgument := RuntimeArgument.ofValue graph 1 first
    | throwError "the explicit input alias is absent"
  let next ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let aliases ← PreparedRequest.forApplication owners.identities program next context callable
    #[scalar, scalar] #[left, aliasedArgument] #[]
  let aliasMap ← aliases.admitInputs graph
  let .ok values := aliasMap.arguments graph
    | throwError "explicitly aliased inputs could not be admitted"
  unless values.map (·.value) == #[first.value, first.value] do
    throwError "the role map merged explicitly aliased input positions"
  let some foreignRole := aliases.roles.arguments[0]?
    | throwError "the other occurrence lost its declared role"
  match admitted.lookup graph foreignRole.role.id with
  | .error message =>
    unless message == "the computational role belongs to a different scope" do throwError message
  | .ok _ => throwError "equal source roles escaped their computational scope"
