module

import CasCompiler.Elaborate
public meta import Lean.Elab.Command
meta import CasCompiler.Elaborate

open Lean Meta Elab Term CasCompiler

private def sourceSyntax (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native source control did not parse"
  return ⟨stx⟩

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
  unless selected.spans.size == 6 && readQuestion.span.fileName == (← getFileName) &&
      readQuestion.span.start.map (·.byteIdx) == some 0 &&
      readQuestion.span.stop.map (·.byteIdx) == some 5 do
    throwError "native elaboration lost declaration locations or the complete question source span"
  readValue.source.withOpen fun bindings expression => do
    let first ← mkAppM ``Prod.fst #[expression]
    unless ← isDefEq first bindings[2]!.expression do
      throwError "a native source definition lost its dependent parameter"
    let second ← mkAppM ``Prod.snd #[expression]
    let dictionary ← synthInstance (← mkAppM ``Inhabited #[bindings[0]!.expression])
    unless dictionary == bindings[1]!.expression do
      throwError "native elaboration selected a different local dictionary"
    let expected ← mkAppOptM ``Inhabited.default #[some bindings[0]!.expression, some dictionary]
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
  let laws ← selected.assume `small (← sourceSyntax "Subsingleton α") .instImplicit
  unless laws.context.entries[6]?.map (·.role) == some .instance do
    throwError "a proof-valued class lost its selected-instance source role"
  let dependent ← selected.term (← sourceSyntax "fun (n : Nat) (i : Fin n) => i")
  unless dependent.source.expression.isLambda && dependent.source.context.entries.size == 6 do
    throwError "native elaboration lost the complete scope of a dependent callable"
  for text in #["_", "Nat", "x"] do
    let rejected ← try
      discard <| selected.proposition (← sourceSyntax text)
      pure false
    catch _ => pure true
    unless rejected do throwError "a completed proposition accepted an unresolved or non-Prop term"
  unless initial.context.entries.isEmpty && hypotheses.context.entries.size == 4 do
    throwError "native source elaboration mutated an earlier persistent context"

run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← SourceSession.empty "native-source-safety"
  for (text, message) in #[
      ("sorryAx Nat true", "depends on sorryAx"),
      ("unsafeCast (α := Nat) (β := Nat) 7", "is unsafe")] do
    let rejected ← try
      discard <| session.term (← sourceSyntax text)
      pure false
    catch error => do
      let text ← error.toMessageData.toString
      pure ((text.splitOn message).length > 1)
    unless rejected do throwError "native source intake did not enforce its safety/axiom boundary"
  let rejected ← try
    discard <| session.assume `invalid (← sourceSyntax "Nat") .instImplicit
    pure false
  catch _ => pure true
  unless rejected do throwError "a selected-instance binder accepted a nonclass source type"

run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← SourceSession.empty "annotated-source-definition"
  let rejected ← try
    discard <| session.define `value (← sourceSyntax "Nat.zero")
      (some (← sourceSyntax "Bool"))
    pure false
  catch _ => pure true
  unless rejected do throwError "a source definition ignored its declared type"
