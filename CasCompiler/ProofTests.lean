module

import CasCompiler.Parse
import CasCompiler.Elaborate
import CasCompiler.Layout
public meta import Lean.Elab.Command
meta import CasCompiler.Parse
meta import CasCompiler.Elaborate
meta import CasCompiler.Layout

open Lean Meta Elab Term CasCompiler CasCatalogue.Language

private def nativeSyntax (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the source obligation control did not parse"
  return ⟨stx⟩

private def suppliedProof (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the explicit source proof control did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeSyntax "Nat")
  let propositions ← parameters.assume `P (← nativeSyntax "Prop")
  let session ← propositions.assume `h (← nativeSyntax "P")
  let obligation ← session.proposition (← nativeSyntax "P")
  let input := "-- source evidence\n\nlet evidence := proof(h)\n"
  let file ← SourceFile.parse "formal-evidence.cas" input
  let some item := file.items[0]? | throwError "the original evidence declaration is absent"
  let `(cas_item| let $_:ident := $evidence:cas_term) := item.raw
    | throwError "the original evidence declaration changed syntax"
  let checked ← file.withContext <| session.proof evidence obligation.source
  unless checked.source.expression == mkBVar 0 && checked.source.type == mkBVar 1 &&
      checked.source.context.entries.size == 3 &&
      checked.span.fileName == "formal-evidence.cas" do
    throwError "formal proof checking changed the obligation, source scope or original file"
  let some position := checked.span.start | throwError "the formal proof lost its source position"
  unless (file.context.fileMap.toPosition position).line == 3 do
    throwError "formal proof checking changed the original source line"
  let layout ← SourceLayout.ofTerm checked.source
  unless layout.kind == .proof && layout.kind.actions.isEmpty do
    throwError "source evidence acquired a computational interface"
  for text in #["proof(True.intro)", "h"] do
    let rejected ← try
      discard <| session.proof (← suppliedProof text) obligation.source
      pure false
    catch _ => pure true
    unless rejected do throwError "source evidence bypassed its wrapper or actual obligation: {text}"
  let dataType ← session.term (← nativeSyntax "Nat")
  let rejected ← try
    discard <| session.proof (← suppliedProof "proof(7)") dataType.source
    pure false
  catch _ => pure true
  unless rejected do throwError "a non-proposition was accepted as a formal proof obligation"
