module

import CasCompiler.Parse
import CasCompiler.SourceProof
import CasCompiler.Layout
public meta import Lean.Elab.Command
meta import CasCompiler.Parse
meta import CasCompiler.SourceProof
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

private def checkOriginalProof (session : SourceSession) (obligation proof : SourceTerm) :
    MetaM Unit := withCurrHeartbeats do
  unless proof.source.context.exactlyMatches session.context do
    throwError "native proof completion changed an original source declaration"
  proof.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let expected ← obligation.source.inContext context
    check expression
    checkWithKernel expression
    unless ← isDefEq (← inferType expression) expected do
      throwError "native proof completion changed the independently prepared proposition"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeSyntax "Nat")
  let obligation ← session.proposition (← nativeSyntax "True")
  let original ← getEnv
  let proof ← withCurrHeartbeats <| session.proof (← suppliedProof
    "proof(by\n  let rec witness (k : Nat) : True :=\n    match k with\n    | 0 => True.intro\n    | Nat.succ k => witness k\n  exact witness n)") obligation.source
  let declarations := proof.source.nativeDeclarations.constants
  unless !declarations.isEmpty && declarations.any (fun declaration =>
      proof.source.expression.containsConst (· == declaration.name)) do
    throwError "the standalone let-rec proof lost its actual checked helper"
  checkOriginalProof session obligation proof
  setEnv original
  checkOriginalProof session obligation proof
  for declaration in declarations do
    unless nativeConstantExactlyMatches declaration (← getConstInfo declaration.name) do
      throwError "reopening changed the completed native recursive helper"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let type ← empty.elaborate Syntax.missing fun _ =>
    pure (mkSort (.succ (.param `nativeProofScope)))
  let session ← empty.assumeTerm `α type
  let session ← session.assume `x (← nativeSyntax "α")
  let session ← session.assume `n (← nativeSyntax "Nat")
  let session ← session.define `xAlias (← nativeSyntax "x")
  let obligation ← session.proposition (← nativeSyntax "xAlias = x")
  let evidence ← nativeSyntax
    "by\n  let rec witness (k : Nat) : xAlias = x :=\n    match k with\n    | 0 => rfl\n    | Nat.succ k => witness k\n  exact witness n"
  let proof ← withCurrHeartbeats <| session.elaborate evidence fun context => do
    sourceFormalProof evidence (← obligation.source.inContext context)
  unless proof.source.universeParams.contains `nativeProofScope &&
      proof.source.nativeDeclarations.constants.any (fun declaration =>
        declaration.levelParams.contains `nativeProofScope) do
    throwError "native let-rec completion lost the source's rigid universe parameter"
  checkOriginalProof session obligation proof


  let supplied ← session.proof (← `(cas_term| proof($evidence:term))) obligation.source
  unless supplied.source.universeParams.contains `nativeProofScope &&
      supplied.source.nativeDeclarations.constants.any (fun declaration =>
        declaration.levelParams.contains `nativeProofScope) do
    throwError "source proof closure lost the original rigid universe or native helper"
  checkOriginalProof session obligation supplied




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeSyntax "Nat")
  let session ← session.assume `P (← nativeSyntax "Prop")
  let session ← session.assume `h (← nativeSyntax "P")
  let obligation ← session.proposition (← nativeSyntax "P")
  let nested ← withCurrHeartbeats <| session.proof (← suppliedProof
    "proof(by\n  let rec witness (k : Nat) : P :=\n    let rec inner (j : Nat) : P :=\n      match j with\n      | 0 => h\n      | Nat.succ j => inner j\n    match k with\n    | 0 => inner n\n    | Nat.succ k => witness k\n  exact witness n)") obligation.source
  let mutualProof ← withCurrHeartbeats <| session.proof (← suppliedProof
    "proof(let rec witness (k : Nat) : P := match k with | 0 => h | Nat.succ k => partner k, partner (k : Nat) : P := match k with | 0 => h | Nat.succ k => witness k; witness n)") obligation.source
  checkOriginalProof session obligation nested
  checkOriginalProof session obligation mutualProof
  let nestedDeclarations := nested.source.nativeDeclarations.constants.filter fun declaration =>
    nested.source.expression.containsConst (· == declaration.name)
  let mutualDeclarations := mutualProof.source.nativeDeclarations.constants.filter fun declaration =>
    mutualProof.source.expression.containsConst (· == declaration.name)
  unless !nestedDeclarations.isEmpty && !mutualDeclarations.isEmpty &&
      nestedDeclarations.all (fun first =>
        mutualDeclarations.all (fun second => first.name != second.name)) do
    throwError "separate source proofs reused a checked native helper occurrence"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeSyntax "Nat")
  let obligation ← session.proposition (← nativeSyntax "True")
  for text in #[
      "proof(by\n  let rec invalid (k : Nat) : True := invalid k\n  exact invalid n)",
      "proof(by\n  let rec invalid (k : Nat) : True := invalid k\n  exact True.intro)",
      "proof(by\n  let rec invalid (k : Nat) : True := False.elim (by exact True.intro)\n  exact invalid n)"] do
    let saved : Term.SavedState ← saveState
    let failure : Option Exception ← try
      discard <| withCurrHeartbeats <| session.proof (← suppliedProof text) obligation.source
      pure none
    catch error => pure (some error)
    saved.restore
    unless failure.isSome do
      throwError "native formal evidence accepted an invalid recursive declaration: {text}"
  let proof ← withCurrHeartbeats <| session.proof (← suppliedProof "proof(True.intro)")
    obligation.source
  checkOriginalProof session obligation proof
  unless (← getLetRecsToLift).isEmpty do
    throwError "failed native proof completion left pending local recursive declarations"
