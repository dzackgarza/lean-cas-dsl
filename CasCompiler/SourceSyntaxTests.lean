module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Parse
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | liftM (m := MetaM) <| throwError "the native source parameter did not parse"
  return ⟨stx⟩

private def definition (file : SourceFile) (index : Nat) :
    TermElabM (Ident × TSyntax `cas_term) := do
  let some item := file.items[index]? | liftM (m := MetaM) <| throwError "the source definition is absent"
  let `(cas_item| let $name:ident := $value:cas_term) := item
    | liftM (m := MetaM) <| throwError "the source item is not a definition"
  return (name, value)

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let session ← parameters.assume `h (← nativeTerm "n = n")
  let state ← semanticState
  let some rings := state.categories.find? (·.name == "Rings")
    | liftM (m := MetaM) <| throwError "the scalar source category is absent"
  let ringType ← session.elaborate Syntax.missing fun _ => do
    let info ← checkedDeclaration rings.declaration
    mkAppM ``CategoryTheory.Bundled.α
      #[Lean.mkConst rings.declaration (info.levelParams.map Level.param)]
  let mut session ← session.assumeTerm `R ringType
  let file ← SourceFile.parse "public-source.cas"
    "let X := Fin(n)\nlet X := Fin(3)\nlet Y := X\n\
     let Z := (Fin(n) in FiniteSets)\nlet M := RegularModule(R)\n"
  for index in [:file.items.size] do
    let (name, stx) ← definition file index
    let term ← file.withContext <| session.read stx
    unless term.span.fileName == "public-source.cas" && term.span.start == stx.raw.getPos? do
      liftM (m := MetaM) <| throwError "public source reading lost its complete scope or actual source span"
    SourceTest.checkSelected term fun expression => do
      let scope ← get
      let original ← ContextTelescope.capture
        (scope.context.bindings.take session.context.entries.size)
      let bindings ← SourceTest.authoredBindings
      unless original.telescope.exactlyMatches session.context && bindings.size == 3 + index do
        liftM (m := MetaM) <| throwError "public source reading lost its complete scope or actual source span"
      if index == 0 then
        unless (← SourceTest.visitNativeData
            (fun value => pure (value.equal bindings[0]!.expression)) expression false) > 0 do
          liftM (m := MetaM) <| throwError "public source reading discarded an actual native parameter"
      if index == 2 then
        unless ← SourceTest.originatesAt scope.context scope.selections
            expression bindings[4]!.expression false do
          liftM (m := MetaM) <| throwError "public source reading replayed or rebound a shadowed source definition"
      if index == 3 then
        let some refined := state.objects.find? fun entry =>
            entry.name == "Fin" && entry.refines.isSome
          | liftM (m := MetaM) <| throwError "the source refinement is absent"
        let some owner := state.categories.find? (·.id == refined.category)
          | liftM (m := MetaM) <| throwError "the original refined declaration lost its registered category"
        let selected ← SourceTest.visitNativeData (fun value => do
          let some selected ← SourceReadM.selection? value | return false
          return selected.reference.any
            (·.exactlyMatches (.named (.registered (.inl refined) owner)))) expression
        let applications ← SourceTest.declaredApplications scope.context scope.selections
          refined.declaration expression
        unless selected > 0 && !applications.isEmpty do
          liftM (m := MetaM) <| throwError "public source qualification lost its exact refined declaration"
      if index == 4 then
        unless (← SourceTest.visitNativeData
            (fun value => pure (value.equal bindings[2]!.expression)) expression false) > 0 do
          liftM (m := MetaM) <| throwError "public source reading discarded its selected scalar object"
    session ← session.defineTerm name.getId term
  for source in #["Fin(h)", "Fin(unregistered_parameter)", "Fin(n) in Rings", "3"] do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term source
      | liftM (m := MetaM) <| throwError "the source rejection control did not parse"
    let rejected ← try
      discard <| session.read ⟨stx⟩
      pure false
    catch _ => pure true
    unless rejected do liftM (m := MetaM) <| throwError "public source reading accepted an untyped source argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let dimensions ← empty.assume `n (← nativeTerm "Nat")
  let elements ← dimensions.assume `i (← nativeTerm "Fin n")
  let functions ← elements.define `f (← nativeTerm "fun (m : Nat) (j : Fin m) => j")
  let session ← functions.define `e (← nativeTerm "Equiv.refl (Fin n)")
  for source in #["f(n, i)", "(f)(n, i)", "e(i)", "(e)(i)"] do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term source
      | liftM (m := MetaM) <| throwError "the callable source control did not parse"
    let term ← session.read ⟨stx⟩
    SourceTest.checkSelected term fun expression => do
      let scope ← get
      let original ← ContextTelescope.capture
        (scope.context.bindings.take session.context.entries.size)
      let bindings ← SourceTest.authoredBindings
      unless original.telescope.exactlyMatches session.context && bindings.size == 4 do
        liftM (m := MetaM) <| throwError "public callable application lost its complete source context"
      let function := if source.startsWith "e" || source.startsWith "(e" then
        bindings[3]!.expression else bindings[2]!.expression
      unless (← SourceTest.visitNativeData
          (fun value => pure (value.equal function)) expression false) > 0 &&
          (← SourceTest.visitNativeData
            (fun value => pure (value.equal bindings[1]!.expression)) expression false) > 0 do
        liftM (m := MetaM) <| throwError "public application replaced its actual callable or argument"
  let shadowed ← session.define `Fin (← nativeTerm "fun (m : Nat) => m")
  let .ok qualified := Parser.runParserCategory (← getEnv) `cas_term "Fin(n) in FiniteSets"
    | liftM (m := MetaM) <| throwError "the qualified source shadowing control did not parse"
  let rejected ← try
    discard <| shadowed.read ⟨qualified⟩
    pure false
  catch _ => pure true
  unless rejected do liftM (m := MetaM) <| throwError "source qualification bypassed a retained lexical binding"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let parameters ← parameters.assume `m (← nativeTerm "Nat")
  let initial ← parameters.assume `h (← nativeTerm "n = n")
  let file ← SourceFile.parse "source-statements.cas"
    "let X := Fin(n)\nlet X := Fin(3)\nlet i : X := rev(3,2)\n\
     assert n = m and m = n\nassert i = i\n"
  let mut session := initial
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | liftM (m := MetaM) <| throwError "the source statement control changed its parsed category"
    match ← file.withContext (session.readStatement statement) with
    | .definition next value =>
      let before ← SourceTest.authoredEntries session.context session.selections
      let after ← SourceTest.authoredEntries next.context next.selections
      unless next.context.entries.size == value.source.context.entries.size + 1 &&
          after.size == before.size + 1 && value.span.fileName == "source-statements.cas" do
        liftM (m := MetaM) <| throwError "source statement formation lost its declaration or original location"
      next.context.withOpen fun bindings => do
        let original ← ContextTelescope.capture
          (bindings.take value.source.context.entries.size)
        unless original.telescope.exactlyMatches value.source.context do
          liftM (m := MetaM) <| throwError "source statement formation changed its complete retained source scope"
      session := next
    | .assumption _ | .proved .. | .inspection _ | .contextBlock _ =>
      liftM (m := MetaM) <| throwError "these original source statements contain no scoped declaration or explicit proof"
    | .implemented _ => liftM (m := MetaM) <| throwError "these source statements contain no implementation request"
    | .settled _ => liftM (m := MetaM) <| throwError "these source statements contain no typing question"
    | .question proposition =>
      let authored ← SourceTest.authoredEntries session.context session.selections
      unless authored.size == 6 do
        liftM (m := MetaM) <| throwError "a source question changed or shortened its complete preceding scope"
      SourceTest.checkSelected proposition fun expression => do
        let scope ← get
        let original ← ContextTelescope.capture
          (scope.context.bindings.take session.context.entries.size)
        let bindings ← SourceTest.authoredBindings
        unless original.telescope.exactlyMatches session.context && bindings.size == 6 do
          liftM (m := MetaM) <| throwError "a source question changed or shortened its complete preceding scope"
        unless ← isProp expression do liftM (m := MetaM) <| throwError "a source question is not a proposition"
        let native ← SourceTest.selectedValue expression
        if native.isAppOfArity ``And 2 then
          for equality in native.getAppArgs, positions in #[(0, 1), (1, 0)] do
            let equality ← SourceTest.selectedValue equality
            unless equality.isAppOfArity ``Eq 3 &&
                (← SourceTest.originatesAt scope.context scope.selections
                  equality.getAppArgs[1]! bindings[positions.1]!.expression false) &&
                (← SourceTest.originatesAt scope.context scope.selections
                  equality.getAppArgs[2]! bindings[positions.2]!.expression false) do
              liftM (m := MetaM) <| throwError "question formation changed the actual formal parameters or conjunction"
          let expected ← mkAppM ``And
            #[← mkEq bindings[0]!.expression bindings[1]!.expression,
              ← mkEq bindings[1]!.expression bindings[0]!.expression]
          SourceTest.checkOriginal #[expression, expected] fun values => do
            unless values[0]!.equal values[1]! do
              liftM (m := MetaM) <| throwError "question formation changed the actual formal parameters or conjunction"
        else
          unless native.isAppOfArity ``Eq 3 &&
              (← SourceTest.originatesAt scope.context scope.selections
                native.getAppArgs[1]! bindings[5]!.expression false) &&
              (← SourceTest.originatesAt scope.context scope.selections
                native.getAppArgs[2]! bindings[5]!.expression false) do
            liftM (m := MetaM) <| throwError "question formation replaced the retained source definition"
          let expected ← mkEq bindings[5]!.expression bindings[5]!.expression
          SourceTest.checkOriginal #[expression, expected] fun values => do
            unless values[0]!.equal values[1]! do
              liftM (m := MetaM) <| throwError "question formation replaced the retained source definition"
  for text in #["assert n", "assert n = X", "let bad : X := rev(4,2)"] do
    let source ← SourceFile.parse "rejected-statement.cas" text
    let `(cas_item| $statement:cas_stmt) := source.items[0]!
      | liftM (m := MetaM) <| throwError "the rejected statement did not parse"
    let rejected ← try
      discard <| source.withContext (session.readStatement statement)
      pure false
    catch _ => pure true
    unless rejected do liftM (m := MetaM) <| throwError "source statements accepted an ill-typed definition or question"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let points ← empty.assume `i (← nativeTerm "CasCatalogue.Foundation.Objects.fin 3")
  let session ← points.assume `j (← nativeTerm "CasCatalogue.Foundation.Objects.integersMod 3")
  let source ← SourceFile.parse "point-domain-equality.cas" "assert i = j"
  let `(cas_item| $statement:cas_stmt) := source.items[0]!
    | liftM (m := MetaM) <| throwError "the point domain comparison did not parse"
  let rejected ← try
    discard <| source.withContext (session.readStatement statement)
    pure false
  catch _ => pure true
  unless rejected do
    liftM (m := MetaM) <| throwError "source equality identified distinct point domains by their native representations"
