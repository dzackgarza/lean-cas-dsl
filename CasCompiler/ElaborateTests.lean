module

import CasCompiler.Elaborate
public meta import Lean.Elab.Command
meta import CasCompiler.Elaborate

open Lean Meta Elab Term CasCompiler

private def sourceSyntax (text : String) : TermElabM Term := do
  let .ok syntax := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native source control did not parse"
  return ⟨syntax⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let initial ← SourceSession.empty "native-source"
  let types ← initial.assume `α (← sourceSyntax "Type 1")
  let instances ← types.assume `chosen (← sourceSyntax "Inhabited α") .instImplicit
  let parameters ← instances.assume `x (← sourceSyntax "α")
  let hypotheses ← parameters.assume `h (← sourceSyntax "x = x")
  let definitions ← hypotheses.define `y (← sourceSyntax "x")
  let selected ← definitions.define `z (← sourceSyntax "(default : α)")
  let readValue ← selected.term (← sourceSyntax "(y, z)")
  let readQuestion ← selected.proposition (← sourceSyntax "y = x")
  unless selected.context.entries.size == 6 && readValue.source.context.entries.size == 6 &&
      readQuestion.source.context.entries.size == 6 do
    throwError "native elaboration discarded unused source declarations"
  unless selected.context.entries[1]?.map (·.role) == some .instance &&
      selected.context.entries[3]?.map (·.role) == some .hypothesis &&
      selected.context.entries[4]?.map (·.role) == some .definition do
    throwError "native elaboration changed a selected instance, hypothesis or definition role"
  unless selected.context.entries[4]?.bind (·.value) == some (mkBVar 1) do
    throwError "native elaboration expanded a source definition instead of retaining its binder"
  readValue.source.withOpen fun bindings expression => do
    let first ← mkAppM ``Prod.fst #[expression]
    unless ← isDefEq first bindings[2]!.expression do
      throwError "a native source definition lost its dependent parameter"
    let second ← mkAppM ``Prod.snd #[expression]
    let dictionary ← synthInstance (mkApp (mkConst ``Inhabited [Level.succ Level.zero])
      bindings[0]!.expression)
    unless dictionary == bindings[1]!.expression do
      throwError "native elaboration selected a different local dictionary"
    let expected ← mkAppM ``Inhabited.default #[bindings[0]!.expression, dictionary]
    unless ← isDefEq second expected do
      throwError "native elaboration changed the source-selected default"
  let shadowed ← selected.define `x (← sourceSyntax "y")
  let later ← shadowed.term (← sourceSyntax "x")
  unless later.source.expression == mkBVar 0 &&
      selected.context.entries[2]?.map (·.id) != shadowed.context.entries[6]?.map (·.id) do
    throwError "native shadowing replaced an earlier stable binding identity"
  shadowed.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    discard <| readValue.source.inContext context
  for text in #["_", "Nat", "x"] do
    let rejected ← try
      discard <| selected.proposition (← sourceSyntax text)
      pure false
    catch _ => pure true
    unless rejected do throwError "a completed proposition accepted an unresolved or non-Prop term"
  unless initial.context.entries.isEmpty && hypotheses.context.entries.size == 4 do
    throwError "native source elaboration mutated an earlier persistent context"
