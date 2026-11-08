module

import CasTools.QuestionExport
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
meta import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source carrier control did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let input ← liftM (m := IO) (IO.FS.readFile path)
  let file ← SourceFile.parse path input
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | break
    if let `(cas_stmt| let $_:ident($_:cas_term) := $_:cas_term) := statement then break
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the original carrier prefix stopped before its function definition"
    session := next
  let source ← session.read (← sourceTerm "sourceModule")
  let some category := source.category
    | throwError "the original source module lost its complete selected category"
  let routes ← SourceRoutes.forOwner category.expression (.atom CategoryId.sets)
  let some candidates ← routes.finiteRoutes
    | throwError "the original module carrier control requires its complete finite route family"
  let domain ← session.read (← sourceTerm "sourceModule → targetModule")
  unless domain.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
    throwError "a carrier-domain expression shortened its complete original context"
  let some category := domain.category
    | throwError "a carrier-domain expression lost its selected set category"
  unless category.role == .object &&
      category.expression.syntacticEq (.atom CategoryId.sets) do
    throwError "a carrier-domain expression changed its source category or object role"
  let some sourceEntry := session.context.entries.find? (·.userName == `sourceModule)
    | throwError "the original source-module declaration is absent"
  let some targetEntry := session.context.entries.find? (·.userName == `targetModule)
    | throwError "the original target-module declaration is absent"
  domain.source.withOpen fun bindings expression => do
    unless expression.isAppOfArity ``TypeCat.Hom 2 do
      throwError "the original function domain did not retain its native set-map type"
    let source := expression.getAppArgs[0]!
    let target := expression.getAppArgs[1]!
    for carrier in #[source, target] do
      let .mdata data body := carrier
        | throwError "a carrier discarded its actual route references"
      unless data.getString `CasCompiler.source.carrierRoutes == reprStr (candidates.map (·.refs)) do
        throwError "a carrier discarded an original structural route"
      if candidates.size > 1 then
        let .letE _ proposition proof _ _ := body
          | throwError "implicit carrier alternatives lost their equality evidence"
        unless proposition.isAppOfArity ``Eq 3 &&
            (← whnf proposition.getAppArgs[0]!).isAppOf ``CategoryTheory.Functor &&
            proof.getUsedConstants.contains ``congrFun do
          throwError "carrier evidence compared particular objects instead of complete functors"
    let some sourceBinding := bindings.find? (·.id == sourceEntry.id)
      | throwError "the original source-module binding is absent"
    let some targetBinding := bindings.find? (·.id == targetEntry.id)
      | throwError "the original target-module binding is absent"
    unless source.containsFVar sourceBinding.expression.fvarId! &&
        !source.containsFVar targetBinding.expression.fvarId! &&
        target.containsFVar targetBinding.expression.fvarId! &&
        !target.containsFVar sourceBinding.expression.fvarId! do
      throwError "carrier formation replaced or exchanged its original selected module objects"
    discard <| getLevel source
    discard <| getLevel target
  let coordinate ← session.read (← sourceTerm
    "((a, b) ↦ a) in sourceModule → (ℚ in Sets)")
  coordinate.source.withOpen fun bindings expression => do
    let some sourceBinding := bindings.find? (·.id == sourceEntry.id)
      | throwError "the original coordinate function lost its source-module binding"
    unless (← inferType expression).containsFVar sourceBinding.expression.fvarId! do
      throwError "a coordinate function replaced its actual source-module domain"


run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let order ← empty.read (← sourceTerm "ReverseFinOrder(3) in LinearOrders")
  let some selection := order.category.bind (·.carrier)
    | throwError "a selected object lost its independently declared carrier prefix"
  let session ← empty.defineTerm `X order
  let domain ← session.read (← sourceTerm "X → X")
  domain.source.withOpen fun bindings expression => do
    for carrier in expression.getAppArgs do
      unless carrier.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a selected carrier was replaced by its named comparison target"
      let .mdata data _ := carrier
        | throwError "a selected carrier discarded its actual route"
      unless data.getString `CasCompiler.source.carrierRoutes == reprStr #[selection.refs] do
        throwError "a selected carrier was replaced by another structural route"
  let some edge := selection.refs[0]?
    | throwError "the selected carrier prefix control has no actual edge"
  let .functor id := edge
    | throwError "the selected carrier prefix control requires its registered functor"
  let image ← session.read (← sourceTerm s!"view X along «{id.raw}»()")
  let some remainder := image.category.bind (·.carrier)
    | throwError "an explicit view discarded its selected carrier continuation"
  unless remainder.refs.isEmpty && remainder.target.syntacticEq selection.target &&
      remainder.identifications == selection.identifications do
    throwError "an explicit view changed its supplied carrier continuation or comparison"
  let session ← session.defineTerm `Y image
  let retainedTerm ← session.read (← sourceTerm "Y")
  let some retained := retainedTerm.category.bind (·.carrier)
    | throwError "a native alias lost its selected carrier continuation"
  unless retained.refs == remainder.refs &&
      retained.identifications == remainder.identifications do
    throwError "a native alias changed its actual selected carrier data"
