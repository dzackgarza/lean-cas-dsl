module

import CasCompiler.Elaborate
import CasCompiler.Parse
public meta import Lean.Elab.Command
meta import CasCompiler.Elaborate
meta import CasCompiler.Parse

open Lean Meta Elab Term CasCompiler

private def nativeSyntax (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native source formation control did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← SourceSession.empty "direct-source-formation"
  let types ← empty.assume `α (← nativeSyntax "Type")
  let instances ← types.assume `chosen (← nativeSyntax "Inhabited α") .instImplicit
  let parameters ← instances.assume `x (← nativeSyntax "α")
  let session ← parameters.assume `h (← nativeSyntax "x = x")
  let original ← session.term (← nativeSyntax "x")
  let file ← SourceFile.parse "source-formation.cas" "-- source\nlet y := x\n"
  let some reference := file.items[0]? | throwError "the source reference is absent"
  let formed ← file.withContext <| session.elaborate reference.raw fun context => do
    original.source.inContext context
  let defined ← session.defineTerm `y formed
  unless defined.context.entries.size == 5 &&
      defined.context.entries[4]?.bind (·.value) == some (mkBVar 1) &&
      defined.context.instances.size == 1 && formed.span.fileName == "source-formation.cas" do
    throwError "direct source formation lost its native definition, complete scope or source file"
  let shadowed ← defined.define `x (← nativeSyntax "(default : α)")
  let later ← shadowed.defineTerm `z formed
  unless later.context.entries[6]?.bind (·.value) == some (mkBVar 3) do
    throwError "direct definition intake rebound an earlier source variable by its spelling"
  let foreign ← SourceSession.empty "different-source-formation"
  let rejected ← try
    discard <| foreign.defineTerm `z formed
    pure false
  catch _ => pure true
  unless rejected do throwError "direct definition intake accepted an absent source scope"
  withLocalDeclD `escaped (mkConst ``Nat) fun escaped => do
    let rejected ← try
      discard <| session.elaborate reference.raw fun _ => pure escaped
      pure false
    catch _ => pure true
    unless rejected do throwError "source formation published an escaping native local"
  let rejected ← try
    discard <| session.elaborate reference.raw fun _ => mkFreshExprMVar (mkConst ``Nat)
    pure false
  catch _ => pure true
  unless rejected do throwError "source formation published an unresolved native term"
  let family ← session.constant reference.raw ``id [Level.param `sourceUniverse]
  unless family.source.universeParams.contains `sourceUniverse &&
      family.source.expression == Lean.mkConst ``id [Level.param `sourceUniverse] &&
      family.source.context.entries.size == 4 do
    throwError "source declaration intake specialized or discarded its complete family context"
  for (declaration, message) in #[(``unsafeCast, "is unsafe"), (``sorryAx, "depends on sorryAx")] do
    let rejected ← try
      discard <| session.constant reference.raw declaration []
      pure false
    catch error => do
      let text ← error.toMessageData.toString
      pure ((text.splitOn message).length > 1)
    unless rejected do
      throwError "whole declaration safety was not checked before universe specialization"

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← SourceSession.empty "dependent-source-application"
  let parameters ← empty.assume `n (← nativeSyntax "Nat")
  let session ← parameters.assume `point (← nativeSyntax "Fin n")
  let function ← session.term (← nativeSyntax "fun (k : Nat) (i : Fin k) => i")
  let width ← session.term (← nativeSyntax "n")
  let point ← session.term (← nativeSyntax "point")
  let reference ← nativeSyntax "point"
  let applied ← session.apply reference.raw function #[width, point]
  applied.source.withOpen fun bindings expression => do
    let expected := mkApp (Lean.mkConst ``Fin) bindings[0]!.expression
    unless ← isDefEq (← inferType expression) expected do
      throwError "direct source application changed the dependent result type"
    unless ← isDefEq expression bindings[1]!.expression do
      throwError "direct source application changed its actual source argument"
  let defined ← session.defineTerm `result applied
  unless defined.context.entries.size == 3 do
    throwError "a dependent source application discarded its complete parameter scope"
  let rejected ← try
    discard <| session.apply reference.raw function #[width, width]
    pure false
  catch _ => pure true
  unless rejected do throwError "direct source application accepted a mistyped dependent argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let initial ← SourceSession.empty "source-branches"
  let left ← initial.assume `left (← nativeSyntax "Nat")
  let right ← initial.assume `right (← nativeSyntax "Nat")
  let captured ← left.term (← nativeSyntax "left")
  let rejected ← try
    discard <| right.defineTerm `imported captured
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a restored source prefix reused an independent declaration identity"
