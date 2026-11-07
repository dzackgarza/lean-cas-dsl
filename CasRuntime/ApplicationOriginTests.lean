module

import CasCompiler.Program
public meta import Lean.Elab.Command
meta import CasCompiler.Program

open Lean Meta CasCompiler CasRuntime

-- Native source families determine which actual arguments a produced field needs.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let indexRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let type ← Elab.Term.elabTermAndSynthesize
    (← `((n : Nat) → Nat × Fin (n + 1))) (some (mkSort (.succ .zero)))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let owner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  let codeOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  try
    let token ← liftM (m := IO) do
      owner.child.stdin.putStr "actual argument index\n"
      owner.child.stdin.flush
      return (← owner.child.stdout.getLine).trimAscii.toString
    let codeToken ← liftM (m := IO) do
      codeOwner.child.stdin.putStr "actual callable code\n"
      codeOwner.child.stdin.flush
      return (← codeOwner.child.stdout.getLine).trimAscii.toString
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    withLocalDeclD `f type fun f => do
      let context ← ContextTelescope.capture #[{
        id := ⟨"application-origin", 0⟩, role := .parameter, expression := f }]
      let role ← SourceLayout.ofTerm (← context.close f)
      let (older, callable) ← liftM (m := IO) <|
        (ValueGraph.empty owners.identities).stage owners.identities
        { program, occurrence, role, parameters := #[none] } (.ownedExport codeOwner codeToken #[])
      let (graph, index) ← liftM (m := IO) <| older.stage owners.identities
        { program, occurrence, role := indexRole, parameters := #[] } (.ownedExport owner token #[])
      let .ok argument := RuntimeArgument.ofValue graph 0 index
        | throwError "the actual source index is outside its graph"
      let request ← PreparedRequest.forApplication program occurrence context callable
        #[← context.close (mkNatLit 7)] #[argument] #[]
      let some record := request.record | throwError "the source result record is absent"
      let some first := record.fields[0]? | throwError "the independent source field is absent"
      let some second := record.fields[1]? | throwError "the dependent source field is absent"
      let finite ← RecordLayout.ofSource second.layout
      let some valueField := finite.fields[0]? | throwError "the nested source data field is absent"
      let independent ← request.originFor first.layout
      let dependent ← request.originFor second.layout
      let nested ← request.originFor valueField.layout
      let unrelated ← SourceLayout.ofTerm (← context.close (mkNatLit 1))
      let failure : Option Exception ← try
        discard <| request.originFor unrelated
        pure none
      catch error => pure (some error)
      let some failure := failure | throwError "result provenance accepted an unrelated source role"
      unless (← failure.toMessageData.toString).startsWith
          "the source role is not its prepared application result projection" do throw failure
      let some whole := request.origin.application
        | throwError "the prepared result lost its actual application provenance"
      let some left := independent.application
        | throwError "the independent result lost its application table"
      let some right := dependent.application
        | throwError "the dependent result lost its application table"
      let some inner := nested.application
        | throwError "the nested result lost its application table"
      unless whole.arguments.size == 1 &&
          (whole.arguments[0]?.bind id).map (·.value) == some index.value &&
          whole.callable.map (·.value) == some callable.value &&
          whole.dependencies == #[0] && right.dependencies == #[0] &&
          left.dependencies.isEmpty && inner.dependencies.isEmpty do
        throwError "result provenance changed an actual argument or a field's native dependencies"
      let hidden ← liftM (m := IO) do
        try
          discard <| older.stage owners.identities dependent (.portable "0".toUTF8)
          pure false
        catch error => pure (error.toString.endsWith "the value reference is outside the visible graph")
      unless hidden do throwError "application provenance recovered an index absent from its graph"
      let (graph, leftValue) ← liftM (m := IO) <|
        graph.stage owners.identities independent (.portable "0".toUTF8)
      let (graph, innerValue) ← liftM (m := IO) <|
        graph.stage owners.identities nested (.portable "0".toUTF8)
      let (graph, rightValue) ← liftM (m := IO) <|
        graph.stage owners.identities dependent (.product #[innerValue])
      let (graph, result) ← liftM (m := IO) <|
        graph.stage owners.identities request.origin (.product #[leftValue, rightValue])
      let some node := graph.find leftValue.value | throwError "the independent result is absent"
      unless node.references.map (·.value) == #[callable.value, index.value] && node.owners.isEmpty do
        throwError "an independent field lost argument visibility or acquired an unrelated owner"
      unless ← liftM (m := BaseIO) (graph.isAvailable owners result) do
        throwError "a result with a live argument index is unavailable"
      liftM (m := IO) <| owners.close codeOwner.generation
      unless ← liftM (m := BaseIO) (graph.isAvailable owners result) do
        throwError "completed portable data retained the supplying callable's unrelated owner"
      liftM (m := IO) <| owners.close owner.generation
      for value in #[rightValue, result] do
        if ← liftM (m := BaseIO) (graph.isAvailable owners value) then
          throwError "a dependent result survived loss of its actual argument index owner"
      for value in #[leftValue, innerValue] do
        unless ← liftM (m := BaseIO) (graph.isAvailable owners value) do
          throwError "a field independent of the argument index lost its usable value"
  finally
    liftM (m := IO) <| owners.close owner.generation
    liftM (m := IO) <| owners.close codeOwner.generation

-- Lazy access retains the original application's context across a later source telescope.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let zero ← SourceLayout.ofTerm (← empty.close (mkNatLit 0))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let contextOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  let indexOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  let accessOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  let extraOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  try
    let token (connection : Connection) (text : String) : IO String := do
      connection.child.stdin.putStr (text ++ "\n")
      connection.child.stdin.flush
      return (← connection.child.stdout.getLine).trimAscii.toString
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let (graph, contextValue) ← liftM (m := IO) <|
      (ValueGraph.empty owners.identities).stage owners.identities
        { program, occurrence, role := scalar, parameters := #[] }
        (.ownedExport contextOwner (← liftM (m := IO) <| token contextOwner "context index") #[])
    let (graph, index) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] }
      (.ownedExport indexOwner (← liftM (m := IO) <| token indexOwner "argument index") #[])
    let (graph, extra) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] }
      (.ownedExport extraOwner (← liftM (m := IO) <| token extraOwner "unused later binding") #[])
    let (graph, number) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role := zero, parameters := #[] } (.portable "0".toUTF8)
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let nBinding : LocalBinding := { id := ⟨"lazy-origin", 0⟩, role := .parameter, expression := n }
      let nContext ← ContextTelescope.capture #[nBinding]
      let functionType ← withLocalDeclD `k (mkConst ``Nat) fun k => do
        let bound := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) n k) (mkNatLit 1)
        mkForallFVars #[k] (← mkAppM ``Prod #[mkConst ``Nat, mkApp (mkConst ``Fin) bound])
      let closedFunctionType ← nContext.close functionType
      withLocalDeclD `f functionType fun f => do
        let fBinding : LocalBinding := { id := ⟨"lazy-origin", 1⟩, role := .parameter, expression := f }
        let context ← ContextTelescope.capture #[nBinding, fBinding]
        let role ← SourceLayout.ofTerm (← context.close f)
        let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities
          { program, occurrence, role, parameters := #[some contextValue, none] } (.closure program #[])
        let .ok parameter := RuntimeParameter.ofValue graph nBinding.id contextValue
          | throwError "the original context value is outside its graph"
        let .ok argument := RuntimeArgument.ofValue graph 0 index
          | throwError "the original argument value is outside its graph"
        let request ← PreparedRequest.forApplication program occurrence context callable
          #[← context.close (mkNatLit 7)] #[argument] #[parameter]
        let (graph, parent) ← liftM (m := IO) <| graph.stage owners.identities request.origin
          (.ownedExport accessOwner (← liftM (m := IO) <| token accessOwner "lazy record") #[])
        let parentType ← inferType (← request.source.source.inContext context)
        let closedParentType ← context.close parentType
        withLCtx {} #[] do
          withLocalDeclD `n (mkConst ``Nat) fun shadow => do
            let extraBinding : LocalBinding := {
              id := ⟨"lazy-current", 0⟩, role := .parameter, expression := shadow }
            withLocalDeclD `n (mkConst ``Nat) fun currentN => do
              let currentNBinding := { nBinding with expression := currentN }
              let prefixContext ← ContextTelescope.capture #[extraBinding, currentNBinding]
              let functionType ← closedFunctionType.inContext prefixContext
              withLocalDeclD `f functionType fun currentF => do
                let currentFBinding := { fBinding with expression := currentF }
                let prefixContext ← ContextTelescope.capture #[extraBinding, currentNBinding, currentFBinding]
                let parentType ← closedParentType.inContext prefixContext
                withLocalDeclD `r parentType fun r => do
                  let resultBinding : LocalBinding := {
                    id := ⟨"lazy-current", 1⟩, role := .result, expression := r }
                  let current ← ContextTelescope.capture
                    #[extraBinding, currentNBinding, currentFBinding, resultBinding]
                  let .ok extraParameter := RuntimeParameter.ofValue graph extraBinding.id extra
                    | throwError "the later unrelated context value is absent"
                  let .ok resultParameter := RuntimeParameter.ofValue graph resultBinding.id parent
                    | throwError "the lazy result is absent"
                  let parameters := #[extraParameter, parameter, resultParameter]
                  let environment ← RuntimeEnvironment.capture owners.worker current parameters
                  let .ok (some retained) := environment.lookup resultBinding.id
                    | throwError "the later source binding lost the actual lazy result"
                  let fieldOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
                  let projection ← PreparedRequest.forProjection program fieldOccurrence current graph retained 1 parameters
                  let (projected, point) ← liftM (m := IO) <|
                    graph.stage owners.identities projection.origin (.product #[number])
                  let .ok dependencies := projected.requiredOwners #[point]
                    | throwError "the projected result is outside its graph"
                  unless dependencies.contains contextOwner.generation &&
                      dependencies.contains indexOwner.generation &&
                      !dependencies.contains accessOwner.generation &&
                      !dependencies.contains extraOwner.generation do
                    throwError "lazy projection lost its original application context or argument dependencies"
  finally
    liftM (m := IO) <| owners.close contextOwner.generation
    liftM (m := IO) <| owners.close indexOwner.generation
    liftM (m := IO) <| owners.close accessOwner.generation
    liftM (m := IO) <| owners.close extraOwner.generation
