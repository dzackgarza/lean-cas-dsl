module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source did not parse"
  return ⟨source⟩

/- A matrix of Mat₂(ℚ) acting on a vector of ℚ² (tests/acceptance/linear_algebra.cas,
`matrices.application` and `matrices.product`): the registered application `(M, v) ↦ M v` of
Mat is reached with no argument object, its parameters fixed by the matrix, and `M(v)` and
`M*v` read. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let matrices ← empty.read (← sourceTerm "Mat₂(ℚ)")
  let session ← empty.defineTerm `M (← empty.read (← sourceTerm "[1, 2; 3, 4]") (some matrices.source))
  let vectors ← session.read (← sourceTerm "ℚ²")
  let session ← session.defineTerm `v (← session.read (← sourceTerm "(1, 2)") (some vectors.source))
  for text in #["M(v)", "M*v"] do
    let product ← session.read (← sourceTerm text)
    product.source.withOpen fun _ value => do
      let value ← instantiateMVars value
      if value.hasMVar then throwError "`{text}` left a parameter undetermined: {value}"
      unless (value.find? (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.apply)).isSome do
        throwError "`{text}` is not the registered application of Mat: {value}"

/- The original formed-module source supplies Vec as a ModuleCat parameter of BilinearMaps.
Read that unchanged written domain through the public reader: the module constructor must read
its coefficient at its own RingCat parameter, rather than receive the base Vec's Type argument. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/b0-formed-positives.cas.proposed"
  let contents ← liftM (m := IO) <| IO.FS.readFile path
  let file ← SourceFile.parse path contents
  let mut writtenDomain : Option (TSyntax `cas_term) := none
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    let `(cas_stmt| let $name:ident := $body:cas_term) := statement | continue
    unless name.getId == `b do continue
    let `(cas_term| $_:cas_term in $domain:cas_term) := body
      | throwError "the original formed-module input lost its written bilinear domain"
    writtenDomain := some domain
    break
  let some selectedDomain := writtenDomain
    | throwError "the original formed-module input lost its first bilinear declaration"
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let domain ← file.withContext (session.read selectedDomain)
  unless domain.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
    throwError "the original bilinear domain changed its complete source context"
  domain.source.withOpen fun _ expression => do
    let native ← sourceDomain expression
    unless native.isAppOfArity
        ``CasCatalogue.Modules.Bilinear.Valued.Constructions.bilinearMaps 4 do
      throwError "the original bilinear domain lost its accepted constructor"
    for moduleValue in #[native.getAppArgs[1]!, native.getAppArgs[2]!] do
      let some (id, _) ← sourceObjectReference? moduleValue
        | throwError "the original Vec parameter lost its selected object row"
      unless id.raw == "obj.modules.vectors" do
        throwError "the original Vec parameter changed its selected module construction"
      let moduleValue ← sourceDomain moduleValue
      unless moduleValue.isAppOfArity ``CasCatalogue.Algebra.LinearAlgebra.vectorModule 2 do
        throwError "the original Vec parameter lost its own complete constructor arguments"
    checkWithKernel expression

/- T030: the original matrix-inverse input supplies its actual admitted unit. Check the
inverse subterm from that unchanged file through the public reader, without supplying a
native group, a chosen inverse or an expected numerical answer in the test setup. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/inverses.cas"
  let contents ← liftM (m := IO) <| IO.FS.readFile path
  let file ← SourceFile.parse path contents
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let mut written : Option Syntax := none
  for item in file.items do
    match item with
    | `(cas_item| test $id:ident $_:str : $statement:cas_stmt) =>
      if id.getId.toString (escape := false) != "inverses.value" then continue
      written := statement.raw.find? (·.isOfKind ``CasCatalogue.Language.casInverse)
      break
    | `(cas_item| $statement:cas_stmt) =>
      let formed ← try file.withContext (session.readStatement statement)
        catch error =>
          IO.eprintln s!"[inverse-prefix-failure] statement={reprStr statement.raw}"
          throwError "the original inverse prefix failed before inversion: {error.toMessageData}"
      let .definition next _ := formed
        | throwError "the original inverse prefix changed its declaration kind"
      session := next
    | _ => throwError "the original inverse input changed its item kind"
  let some inverseSyntax := written
    | throwError "the original inverses.value question lost its inverse expression"
  let operand ← file.withContext (session.read ⟨inverseSyntax[0]⟩)
  let inverse ← file.withContext (session.read ⟨inverseSyntax⟩)
  inverse.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let operand ← operand.source.inContext context
    let .fvar original := operand
      | throwError "the original inverse operand is no longer its source binding"
    unless expression.containsConst (· == ``CasCatalogue.Algebra.Units.groupInverse) &&
        expression.containsFVar original do
      throwError "source inversion lost its registered operation or original admitted operand"
    unless ← isDefEq (← inferType expression) (← inferType operand) do
      throwError "the inverse left the registered group of its original operand"
