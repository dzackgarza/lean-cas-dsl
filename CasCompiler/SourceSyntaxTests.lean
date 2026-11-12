module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native source parameter did not parse"
  return ⟨stx⟩

private def definition (file : SourceFile) (index : Nat) :
    TermElabM (Ident × TSyntax `cas_term) := do
  let some item := file.items[index]? | throwError "the source definition is absent"
  let `(cas_item| let $name:ident := $value:cas_term) := item
    | throwError "the source item is not a definition"
  return (name, value)

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let session ← parameters.assume `h (← nativeTerm "n = n")
  let state ← semanticState
  let some rings := state.categories.find? (·.name == "Rings")
    | throwError "the scalar source category is absent"
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
    unless term.source.context.entries.size == 3 + index &&
        term.span.fileName == "public-source.cas" && term.span.start == stx.raw.getPos? do
      throwError "public source reading lost its complete scope or actual source span"
    if index == 0 then
      term.source.withOpen fun bindings expression => do
        unless expression.containsFVar bindings[0]!.expression.fvarId! do
          throwError "public source reading discarded an actual native parameter"
    if index == 2 then
      unless term.source.expression == mkBVar 0 do
        throwError "public source reading replayed or rebound a shadowed source definition"
    if index == 3 then
      let some refined := state.objects.find? fun entry =>
          entry.name == "Fin" && entry.refines.isSome
        | throwError "the source refinement is absent"
      unless term.source.expression.consumeMData.getAppFn.constName? == some refined.declaration do
        throwError "public source qualification lost its exact refined declaration"
    if index == 4 then
      term.source.withOpen fun bindings expression => do
        unless expression.containsFVar bindings[2]!.expression.fvarId! do
          throwError "public source reading discarded its selected scalar object"
    session ← session.defineTerm name.getId term
  for source in #["Fin(h)", "Fin(unregistered_parameter)", "Fin(n) in Rings", "3"] do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term source
      | throwError "the source rejection control did not parse"
    let rejected ← try
      discard <| session.read ⟨stx⟩
      pure false
    catch _ => pure true
    unless rejected do throwError "public source reading accepted an untyped source argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let dimensions ← empty.assume `n (← nativeTerm "Nat")
  let elements ← dimensions.assume `i (← nativeTerm "Fin n")
  let functions ← elements.define `f (← nativeTerm "fun (m : Nat) (j : Fin m) => j")
  let session ← functions.define `e (← nativeTerm "Equiv.refl (Fin n)")
  for source in #["f(n, i)", "(f)(n, i)", "e(i)", "(e)(i)"] do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term source
      | throwError "the callable source control did not parse"
    let term ← session.read ⟨stx⟩
    unless term.source.context.entries.size == 4 do
      throwError "public callable application lost its complete source context"
    term.source.withOpen fun bindings expression => do
      let function := if source.startsWith "e" || source.startsWith "(e" then
        bindings[3]!.expression else bindings[2]!.expression
      unless expression.containsFVar function.fvarId! &&
          expression.containsFVar bindings[1]!.expression.fvarId! do
        throwError "public application replaced its actual callable or argument"
  let shadowed ← session.define `Fin (← nativeTerm "fun (m : Nat) => m")
  let .ok qualified := Parser.runParserCategory (← getEnv) `cas_term "Fin(n) in FiniteSets"
    | throwError "the qualified source shadowing control did not parse"
  let rejected ← try
    discard <| shadowed.read ⟨qualified⟩
    pure false
  catch _ => pure true
  unless rejected do throwError "source qualification bypassed a retained lexical binding"

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
      | throwError "the source statement control changed its parsed category"
    match ← file.withContext (session.readStatement statement) with
    | .definition next value =>
      unless next.context.entries.size == session.context.entries.size + 1 &&
          value.span.fileName == "source-statements.cas" do
        throwError "source statement formation lost its declaration or original location"
      session := next
    | .implemented _ => throwError "these source statements contain no implementation request"
    | .settled _ => throwError "these source statements contain no typing question"
    | .question proposition =>
      unless proposition.source.context.entries.size == 6 &&
          session.context.entries.size == 6 do
        throwError "a source question changed or shortened its complete preceding scope"
      proposition.source.withOpen fun bindings expression => do
        unless ← isProp expression do throwError "a source question is not a proposition"
        if expression.isAppOfArity ``And 2 then
          let expected ← mkAppM ``And
            #[← mkEq bindings[0]!.expression bindings[1]!.expression,
              ← mkEq bindings[1]!.expression bindings[0]!.expression]
          unless expression == expected do
            throwError "question formation changed the actual formal parameters or conjunction"
        else
          let expected ← mkEq bindings[5]!.expression bindings[5]!.expression
          unless expression == expected do
            throwError "question formation replaced the retained source definition"
  for text in #["assert n", "assert n = X", "let bad : X := rev(4,2)"] do
    let source ← SourceFile.parse "rejected-statement.cas" text
    let `(cas_item| $statement:cas_stmt) := source.items[0]!
      | throwError "the rejected statement did not parse"
    let rejected ← try
      discard <| source.withContext (session.readStatement statement)
      pure false
    catch _ => pure true
    unless rejected do throwError "source statements accepted an ill-typed definition or question"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let points ← empty.assume `i (← nativeTerm "CasCatalogue.Foundation.Objects.fin 3")
  let session ← points.assume `j (← nativeTerm "CasCatalogue.Foundation.Objects.integersMod 3")
  let source ← SourceFile.parse "point-domain-equality.cas" "assert i = j"
  let `(cas_item| $statement:cas_stmt) := source.items[0]!
    | throwError "the point domain comparison did not parse"
  let rejected ← try
    discard <| source.withContext (session.readStatement statement)
    pure false
  catch _ => pure true
  unless rejected do
    throwError "source equality identified distinct point domains by their native representations"
