module

import CasCompiler.Read
import CasCompiler.Parse
import Lean.Meta.Transform
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import Lean.Meta.Transform
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Term CasCompiler CasCatalogue

-- Native instance synthesis retains the complete authored argument table, including the
-- original selected object envelopes. These are the unchanged public source statements.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/rx08-ordinary-kernel.cas"
  let file ← SourceFile.parse path (← IO.FS.readFile path)
  let mut reached := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    let .definition next value ← file.withContext (session.readStatement statement)
      | throwError "the original source-module prefix changed its statement kind"
    session := next
    let isTarget := match statement with
      | `(cas_stmt| let $name:ident := $_:cas_term) => name.getId == `sourceModule
      | _ => false
    if isTarget then
      value.source.withOpen fun _ expression => do
        let declaration :=
          ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetDeclaration
        let some applied := expression.find? (·.isAppOfArity declaration 5)
          | throwError "the original source-module view lost its complete native functor"
        check applied
        if applied.hasMVar || applied.hasLevelMVar then
          throwError "the original source-module view retained an unresolved native instance"
        for index in #[0, 2] do
          let parameter := applied.getAppArgs[index]!
          let .mdata marker _ := parameter
            | throwError "a source-module parameter lost its original object envelope"
          unless marker.contains `CasCompiler.source.objectOrigin do
            throwError "a source-module parameter lost its explicit object origin"
          let some (category, _) ← sourceObjectOrigin? parameter
            | throwError "a source-module parameter lost its checked native owner"
          unless category.role == .object &&
              category.expression.syntacticEq (.atom CategoryId.sets) do
            throwError "a source-module parameter changed its selected complete category"
      reached := true
      break
  unless reached do throwError "the original sourceModule statement was not read"
  let define := fun (current : SourceSession) (text : String) => do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "the native-instance source control did not parse"
    let .definition next value ← current.readStatement ⟨parsed⟩
      | throwError "the native-instance source control is not a definition"
    return (next, value)
  let (next, _) ← define session "let Rfirst := ℚ"
  let (next, _) ← define next "let Rsecond := ℚ"
  session := next
  for (leftName, rightName, text) in #[
      (`Rfirst, `Rsecond,
        "let firstView := view formedSource along «fun.bilin_module.forget»(Rfirst, Rsecond)"),
      (`Rsecond, `Rfirst,
        "let secondView := view formedSource along «fun.bilin_module.forget»(Rsecond, Rfirst)")] do
    let (next, value) ← define session text
    session := next
    value.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let declaration :=
        ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetDeclaration
      let some applied := expression.find? (·.isAppOfArity declaration 5)
        | throwError "native synthesis lost the original complete functor application"
      let arguments := applied.getAppArgs
      let info ← getFunInfoNArgs applied.getAppFn arguments.size
      unless info.paramInfo.map (·.isInstance) == #[false, true, false, true, true] do
        throwError "native synthesis moved an original implicit dictionary position"
      let mut originals : Array Expr := #[]
      for (index, name) in #[(0, leftName), (2, rightName)] do
        let some original ← bindings.findM? fun binding =>
            return (← binding.expression.fvarId!.getUserName) == name
          | throwError "the original source parameter binding is absent"
        let .mdata marker _ := arguments[index]!
          | throwError "native inference removed an authored object envelope"
        unless marker.contains `CasCompiler.source.objectOrigin do
          throwError "native inference removed an authored object origin"
        let some (category, parameter) ← sourceObjectOrigin? arguments[index]!
          | throwError "native inference lost an original object parameter"
        let some selected := session.categoryFor original.id
          | throwError "the original source parameter lost its complete category"
        unless parameter == original.expression && category.role == .object &&
            category.expression.syntacticEq selected.expression &&
            category.bundle == (← selected.bundle.inContext context) do
          throwError "native inference substituted another original source parameter"
        originals := originals.push parameter
      unless originals[0]! != originals[1]! && (← isDefEq originals[0]! originals[1]!) do
        throwError "the native-instance control needs distinct equal native source objects"
      check applied
      if applied.hasMVar || applied.hasLevelMVar then
        throwError "native synthesis left an original dictionary position unresolved"
  -- The existing finite-subset source requires a native DecidableEq through a nested
  -- polynomial parameter, while both original owner envelopes remain in its source.
  let (_, finite) ← define session "let F := {x - 1} in 𝒫_fin(ℤ[x])"
  finite.source.withOpen fun _ expression => do
    check expression
    let observed ← IO.mkRef false
    discard <| Meta.transform expression (pre := fun literal => do
      if ← observed.get then return .done literal
      unless literal.isAppOfArity ``List.toFinset 3 do return .continue
      let arguments := literal.getAppArgs
      let .mdata outer _ := arguments[0]!
        | throwError "the finite-subset dictionary erased its original base envelope"
      unless outer.contains `CasCompiler.source.objectOrigin do
        throwError "the finite-subset dictionary erased its original base origin"
      let some (_, polynomial) ← sourceObjectOrigin? arguments[0]!
        | throwError "the finite subset lost its original polynomial object"
      let some nested := polynomial.find? (fun term => match term with
        | .mdata marker _ => marker.contains `CasCompiler.source.objectOrigin
        | _ => false)
        | throwError "native inference erased the polynomial's original scalar envelope"
      let some _ ← sourceObjectOrigin? nested
        | throwError "the polynomial's retained scalar origin is malformed"
      check literal
      if literal.hasMVar || literal.hasLevelMVar then
        throwError "the finite-subset dictionary is unresolved"
      observed.set true
      return .done literal)
    unless ← observed.get do
      throwError "the original finite subset lost its native quotient application"
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| define session
        "let unsupportedView := view formedSource along «fun.bilin_module.forget»(ℕ, ℕ)"
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "native inference fabricated an unavailable CommRing dictionary"
  let message ← failure.toMessageData.toString
  unless message.startsWith "failed to synthesize" &&
      (message.splitOn "CommRing").length > 1 do throw failure
