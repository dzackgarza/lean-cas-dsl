module

import CasCompiler.Program
public meta import Lean.Elab.Command
meta import CasCompiler.Program

open Lean Meta CasCompiler CasRuntime

-- Native source families determine which actual arguments a produced field needs.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let indexRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let type ← Elab.Term.elabType (← `((n : Nat) → Nat × Fin (n + 1)))
  let type ← instantiateMVars type
  let owners ← liftM (m := IO) OwnerRegistry.new
  let owner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  try
    let token ← liftM (m := IO) do
      owner.child.stdin.putStr "actual argument index\n"
      owner.child.stdin.flush
      return (← owner.child.stdout.getLine).trimAscii.toString
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let older := ValueGraph.empty owners.identities
    let (graph, index) ← liftM (m := IO) <| older.stage owners.identities
      { program, occurrence, role := indexRole, parameters := #[] } (.ownedExport owner token #[])
    withLocalDeclD `f type fun f => do
      let context ← ContextTelescope.capture #[{
        id := ⟨"application-origin", 0⟩, role := .parameter, expression := f }]
      let role ← SourceLayout.ofTerm (← context.close f)
      let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities
        { program, occurrence, role, parameters := #[none] } (.closure program #[])
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
      unless node.references.map (·.value) == #[index.value] && node.owners.isEmpty do
        throwError "an independent field lost argument visibility or acquired an unrelated owner"
      unless ← liftM (m := BaseIO) (graph.isAvailable owners result) do
        throwError "a result with a live argument index is unavailable"
      liftM (m := IO) <| owners.close owner.generation
      for value in #[rightValue, result] do
        if ← liftM (m := BaseIO) (graph.isAvailable owners value) then
          throwError "a dependent result survived loss of its actual argument index owner"
      for value in #[leftValue, innerValue] do
        unless ← liftM (m := BaseIO) (graph.isAvailable owners value) do
          throwError "a field independent of the argument index lost its usable value"
  finally liftM (m := IO) <| owners.close owner.generation
