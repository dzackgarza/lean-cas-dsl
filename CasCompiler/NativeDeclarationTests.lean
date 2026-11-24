module

import CasCompiler.SourceProof
import CasTools.QuestionObservation
public meta import Lean.Elab.Command
meta import CasCompiler.SourceProof
meta import CasTools.QuestionObservation

open Lean Meta Elab Term CasCompiler

private def nativeInput (text : String) : TermElabM Term := do
  let .ok source := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native declaration retention control did not parse"
  return ⟨source⟩

private def proofInput (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the retained source proof control did not parse"
  return ⟨source⟩

private def checkProof (proof : SourceTerm) : MetaM Unit :=
  withCurrHeartbeats <| proof.source.withOpen fun bindings expression => do
    check expression
    checkWithKernel expression
    unless bindings.size == 1 && bindings[0]!.role == .parameter &&
        (← inferType expression).isConstOf ``True do
      throwError "the retained proof changed its original native scope or proposition"

/- Native match compilation creates checked local helper declarations. Retention must survive
environment rollback while preserving the caller's later additions and callback additions. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeInput "Nat")
  let proposition ← session.proposition (← nativeInput "True")
  let original ← getEnv
  let proof ← withCurrHeartbeats <| session.proof (← proofInput
    "proof(match n, n with | 0, _ => True.intro | _, 0 => True.intro | Nat.succ _, Nat.succ _ => True.intro)")
    proposition.source
  let conclusion ← session.conclusion #[proposition] (some proof)
  let withProof ← session.defineTerm `p proof
  let declarations := proof.source.nativeDeclarations.constants
  unless !declarations.isEmpty && declarations.any (fun info =>
      proof.source.expression.containsConst (· == info.name) && !original.contains info.name) do
    throwError "the proof control did not retain its actual native matcher declaration"
  checkProof proof
  setEnv original
  withProof.context.withOpen fun bindings => do
    unless bindings.size == 2 do throwError "the retained native context changed its bindings"
    let some value := (← getFVarLocalDecl bindings[1]!.expression).value?
      | throwError "the retained native proof binding lost its definition"
    check value
    checkWithKernel value
    unless (← inferType value).isConstOf ``True do
      throwError "the retained native proof binding changed its proposition"
  setEnv original
  let beforeName ← mkAuxDeclName `retentionBefore
  addDecl (.defnDecl { name := beforeName, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 17, hints := .abbrev, safety := .safe })
  let callbackName ← mkAuxDeclName `retentionCallback
  proof.source.withOpen fun _ expression => do
    check expression
    checkWithKernel expression
    unless (← getEnv).contains beforeName do
      throwError "native source restoration replaced the caller's current environment"
    addDecl (.defnDecl { name := callbackName, levelParams := [], type := mkConst ``Nat,
      value := mkNatLit 29, hints := .abbrev, safety := .safe })
  unless (← getEnv).contains beforeName && (← getEnv).contains callbackName do
    throwError "native source inspection discarded a caller or callback environment change"
  for declaration in declarations do
    let actual ← getConstInfo declaration.name
    unless nativeConstantExactlyMatches declaration actual && !actual.isAxiom do
      throwError "native source restoration changed a checked helper or introduced an axiom"
  -- Serialization is inert, including after removal of the helpers from the active environment.
  setEnv original
  let document := CasTools.QuestionExport.observeConclusion conclusion
  let exported ← IO.ofExcept <| (document.getObjVal? "proof").mapError IO.userError
  let native ← IO.ofExcept <| (exported.getObjVal? "native").mapError IO.userError
  let stored ← IO.ofExcept <|
    (native.getObjValAs? (Array Json) "declarations").mapError IO.userError
  let graph ← IO.ofExcept <| (exported.getObjVal? "nativeExpressions").mapError IO.userError
  let nodes ← IO.ofExcept <| (CasTools.NativeExpression.decodeNodes graph).mapError IO.userError
  let mut names : Array Name := #[]
  for entry in stored do
    let name ← IO.ofExcept <| ((entry.getObjVal? "name").bind
      CasTools.NativeExpression.nameFromJson).mapError IO.userError
    names := names.push name
    let some declaration := declarations.find? (·.name == name)
      | throwError "the retained proof report invented a native declaration"
    let type ← IO.ofExcept <| (entry.getObjValAs? Nat "type").mapError IO.userError
    let some type := nodes[type]? | throwError "a retained declaration type is outside its graph"
    unless type.equal declaration.type do
      throwError "the retained proof report changed a native declaration's complete type"
    if let some value := declaration.value? (allowOpaque := true) then
      let root ← IO.ofExcept <| (entry.getObjValAs? Nat "value").mapError IO.userError
      let some stored := nodes[root]?
        | throwError "a retained declaration value is outside its graph"
      unless stored.equal value do
        throwError "the retained proof report changed a native declaration's original body"
  unless names.size == declarations.size && declarations.all (fun info => names.contains info.name) do
    throwError "the retained proof report omitted a local native dependency"
  unless declarations.all (fun info => !original.contains info.name) do
    throwError "the proof control unexpectedly depends on an ambient local declaration"
  let afterSerialization ← getEnv
  unless declarations.all (fun info => !afterSerialization.contains info.name) do
    throwError "inert native proof serialization modified the active environment"
  -- Replay the exported native payload through the kernel, without substituting a proof.
  for entry in stored do
    let declaration ← IO.ofExcept <|
      (CasTools.NativeExpression.valueDeclarationFromJson entry nodes).mapError IO.userError
    addDecl declaration
  for declaration in declarations do
    unless nativeConstantExactlyMatches declaration (← getConstInfo declaration.name) do
      throwError "kernel reconstruction changed an exported native declaration payload"
  let root ← IO.ofExcept <| (native.getObjValAs? Nat "expression").mapError IO.userError
  let some expression := nodes[root]?
    | throwError "the exported native proof is outside its expression graph"
  proof.source.context.withOpen fun bindings => do
    let expression := expression.instantiateRev (bindings.map (·.expression))
    check expression
    checkWithKernel expression
    unless (← inferType expression).isConstOf ``True do
      throwError "the reconstructed native proof changed its original proposition"

/- Imported primitives remain anchored in the fixed native source environment. They do not
expand the declaration closure or change the existing empty-closure graph format. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let proposition ← session.proposition (← nativeInput "Nat.zero = Nat.zero")
  let proof ← session.proof (← proofInput "proof(rfl)") proposition.source
  for term in #[proposition, proof] do
    unless term.source.nativeDeclarations.constants.isEmpty &&
        term.source.context.nativeDeclarations.constants.isEmpty do
      throwError "imported native primitives inflated a retained declaration closure"
  let expressions := #[proposition.source.expression, proof.source.expression]
  unless CasTools.NativeExpression.encodeWithDeclarations expressions #[] ==
      CasTools.NativeExpression.encode expressions do
    throwError "empty native declaration retention changed the original graph document"
  let document := CasTools.QuestionExport.observeConclusion
    (← session.conclusion #[proposition] (some proof))
  let exported ← IO.ofExcept <| (document.getObjVal? "proof").mapError IO.userError
  let native ← IO.ofExcept <| (exported.getObjVal? "native").mapError IO.userError
  if (native.getObjVal? "declarations").isOk then
    throwError "an empty native declaration closure added a field to the original snapshot"

/- A definitionally equal replacement is still a different checked declaration occurrence.
Retained source restoration rejects it without replacing the current declaration. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  let name ← mkAuxDeclName `retainedIdentity
  let value ← withLocalDeclD `n (mkConst ``Nat) fun n => mkLambdaFVars #[n] n
  let first : DefinitionVal := { name, levelParams := [], type := ← inferType value,
    value, hints := .abbrev, safety := .safe }
  addDecl (.defnDecl first)
  let term ← withLCtx {} #[] do
    let context ← ContextTelescope.capture #[]
    context.close (mkConst name)
  setEnv original
  let identity ← withLocalDeclD `originalValue first.type fun value => mkLambdaFVars #[value] value
  let replacement := { first with value := mkApp identity first.value }
  addDecl (.defnDecl replacement)
  let failure : Option Exception ← try
    term.ensureDeclarations
    pure none
  catch error => pure (some error)
  unless failure.isSome do
    throwError "retained source accepted another body at the same native declaration name"
  unless nativeConstantExactlyMatches (.defnInfo replacement) (← getConstInfo first.name) do
    throwError "retained source overwrote the caller's conflicting native declaration"
