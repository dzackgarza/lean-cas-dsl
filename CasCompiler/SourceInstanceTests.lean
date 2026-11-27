module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceTestSupport
import Lean.Meta.Transform
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceTestSupport
meta import Lean.Meta.Transform
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest



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
      checkSelected value fun expression => do
        let scope ← get
        let declaration :=
          ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetDeclaration
        let #[applied] ← declaredApplications scope.context scope.selections declaration expression
          | liftM (m := TermElabM) <| throwError "the original source-module view lost its complete native functor"
        unless applied.isAppOfArity declaration 5 do
          liftM (m := TermElabM) <| throwError "the original source-module view changed its complete native functor"
        check applied
        if applied.hasMVar || applied.hasLevelMVar then
          liftM (m := TermElabM) <| throwError "the original source-module view retained an unresolved native instance"
        for index in #[0, 2] do
          let parameter := applied.getAppArgs[index]!
          let some retained ← SourceReadM.selection? parameter
            | liftM (m := TermElabM) <| throwError "a source-module parameter lost its original typed object binding"
          unless retained.category.isSome do
            liftM (m := TermElabM) <| throwError "a source-module parameter lost its explicit object origin"
          let some (category, _) ← sourceObjectOrigin? parameter
            | liftM (m := TermElabM) <| throwError "a source-module parameter lost its checked native owner"
          unless category.role == .object &&
              category.expression.syntacticEq (.atom CategoryId.sets) do
            liftM (m := TermElabM) <| throwError "a source-module parameter changed its selected complete category"
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
    checkSelected value fun expression => do
      let scope ← get
      let context := scope.context
      let bindings := context.bindings
      let declaration :=
        ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetDeclaration
      let #[applied] ← declaredApplications context scope.selections declaration expression
        | liftM (m := TermElabM) <| throwError "native synthesis lost the original complete functor application"
      unless applied.isAppOfArity declaration 5 do
        liftM (m := TermElabM) <| throwError "native synthesis changed the complete original functor application"
      let arguments := applied.getAppArgs
      let info ← getFunInfoNArgs applied.getAppFn arguments.size
      unless info.paramInfo.map (·.isInstance) == #[false, true, false, true, true] do
        liftM (m := TermElabM) <| throwError "native synthesis moved an original implicit dictionary position"
      let mut originals : Array Expr := #[]
      for (index, name) in #[(0, leftName), (2, rightName)] do
        let some original ← bindings.findM? fun binding =>
            return (← binding.expression.fvarId!.getUserName) == name
          | liftM (m := TermElabM) <| throwError "the original source parameter binding is absent"
        let some retained ← SourceReadM.selection? arguments[index]!
          | liftM (m := TermElabM) <| throwError "native inference removed an authored typed object binding"
        unless retained.category.isSome do
          liftM (m := TermElabM) <| throwError "native inference removed an authored object origin"
        let some (category, parameter) ← sourceObjectOrigin? arguments[index]!
          | liftM (m := TermElabM) <| throwError "native inference lost an original object parameter"
        let some selected := session.categoryFor original.id
          | liftM (m := TermElabM) <| throwError "the original source parameter lost its complete category"
        unless (← originatesAt context scope.selections parameter original.expression false) &&
            category.role == .object &&
            category.expression.syntacticEq selected.expression &&
            category.bundle == (← selected.bundle.inContext context) do
          liftM (m := TermElabM) <| throwError "native inference substituted another original source parameter"
        originals := originals.push original.expression
      unless originals[0]! != originals[1]! do
        liftM (m := TermElabM) <| throwError "the native-instance control needs distinct equal native source objects"
      checkOriginal originals fun values => do
        unless ← isDefEq values[0]! values[1]! do
          throwError "the native-instance control needs distinct equal native source objects"
      check applied
      if applied.hasMVar || applied.hasLevelMVar then
        liftM (m := TermElabM) <| throwError "native synthesis left an original dictionary position unresolved"


  let (_, finite) ← define session "let F := {x - 1} in 𝒫_fin(ℤ[x])"
  checkSelected finite fun expression => do
    check expression


    let admissions ← visitNativeData (fun candidate => do
      let some selected ← SourceReadM.selection? candidate | return false
      let some admission := selected.admission | return false
      let arity ← liftM (m := MetaM) <| forallTelescope (← inferType admission.family)
        fun parameters _ => pure parameters.size
      unless admission.entry.id.raw == "obj.sets.finite_subsets" &&
          admission.entry.admission == some ``CasCatalogue.Foundation.FiniteSubsets.admit &&
          admission.element == 1 && arity == 3 && admission.arguments.size == arity do
        liftM (m := TermElabM) <| throwError "the finite-subset admission changed its complete native argument positions"
      let some datum := admission.arguments[admission.element]?
        | liftM (m := TermElabM) <| throwError "the finite-subset admission lost its original datum slot"
      let count ← visitNativeData (fun literal => do
        unless literal.isAppOfArity ``List.toFinset 3 do return false
        let arguments := literal.getAppArgs
        let some outer ← SourceReadM.selection? arguments[0]!
          | liftM (m := TermElabM) <| throwError "the finite-subset dictionary erased its original base binding"
        unless outer.category.isSome do
          liftM (m := TermElabM) <| throwError "the finite-subset dictionary erased its original base origin"
        let some (_, polynomial) ← sourceObjectOrigin? arguments[0]!
          | liftM (m := TermElabM) <| throwError "the finite subset lost its original polynomial object"
        let scope ← get
        let some (row, _) ← sourceObjectSelection? scope.context scope.selections polynomial
          | liftM (m := TermElabM) <| throwError "the finite subset lost its original selected polynomial row"
        let applications ← declaredApplications scope.context scope.selections row.declaration polynomial
        unless !applications.isEmpty do
          liftM (m := TermElabM) <| throwError "native inference erased the polynomial's original declaration inputs"
        let mut nested := false
        for application in applications do
          for parameter in application.getAppArgs do
            if (← sourceObjectOrigin? parameter).isSome then nested := true
        unless nested do
          liftM (m := TermElabM) <| throwError "native inference erased the polynomial's original scalar binding"
        check literal
        if literal.hasMVar || literal.hasLevelMVar then
          liftM (m := TermElabM) <| throwError "the finite-subset dictionary is unresolved"
        return true) datum
      unless count > 0 do
        liftM (m := TermElabM) <| throwError "the original finite subset lost its native quotient application"
      return true) expression
    unless admissions == 1 do
      liftM (m := TermElabM) <| throwError "the finite subset lost its unique original admission"
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




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let type ← mkAppM ``Inhabited #[mkConst ``Nat]
  withLocalDeclD `first type fun first =>
    withLocalDeclD `second type fun second => do
      let selectedInstances : LocalInstances := #[
        { className := ``Inhabited, fvar := second },
        { className := ``Inhabited, fvar := first }]
      withLCtx (← getLCtx) selectedInstances do
        let context ← ContextTelescope.capture #[
          { id := ⟨"selected-instance-order", 0⟩, role := .instance, expression := first },
          { id := ⟨"selected-instance-order", 1⟩, role := .instance, expression := second }]
        let chosen ← synthInstance type
        for value in #[mkNatLit 7, first] do
          SourceSelectionScope.withBinding identities {} context { value }
              fun extended selections retained => do
            let actual ← getLocalInstances
            unless actual.size == selectedInstances.size do
              throwError "a selected value changed the original local-instance count"
            for current in actual, original in selectedInstances do
              unless current.className == original.className &&
                  current.fvar.equal original.fvar do
                throwError "a selected value changed the original local-instance priority"
            unless extended.telescope.instances.size == context.telescope.instances.size do
              throwError "the retained context included an unselected class-valued alias"
            for current in extended.telescope.instances, original in context.telescope.instances do
              unless current.className == original.className && current.binding == original.binding do
                throwError "the retained context changed an original selected instance identity"
            let some selected := selections.findAt? extended retained
              | throwError "the selected value lost its complete typed binding"
            unless selected.value.equal value do
              throwError "the selected value changed its original native expression"
            let source ← extended.close chosen
            source.withOpen fun _ original => do
              let current ← synthInstance (← inferType original)
              unless current.equal original do
                throwError "reopening a selected context changed native instance synthesis"
