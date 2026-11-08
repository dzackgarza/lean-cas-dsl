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
  let reordered ← session.read (← sourceTerm
    "((a, b) ↦ (b, a)) in sourceModule → targetModule")
  reordered.source.withOpen fun bindings expression => do
    let some sourceBinding := bindings.find? (·.id == sourceEntry.id)
      | throwError "the tuple function lost its source-module binding"
    let some targetBinding := bindings.find? (·.id == targetEntry.id)
      | throwError "the tuple function lost its target-module binding"
    let type ← inferType expression
    unless type.containsFVar sourceBinding.expression.fvarId! &&
        type.containsFVar targetBinding.expression.fvarId! &&
        expression.getUsedConstants.contains ``Fin.cases do
      throwError "a tuple function replaced its original domains or native components"
  let pointFunction ← session.read (← sourceTerm
    "((a, b) ↦ (a, 0)) in sourceModule → targetModule")
  pointFunction.source.withOpen fun bindings expression => do
    let some targetBinding := bindings.find? (·.id == targetEntry.id)
      | throwError "the point-valued tuple lost its target-module binding"
    unless (← inferType expression).containsFVar targetBinding.expression.fvarId! &&
        expression.getUsedConstants.contains ``CasCatalogue.Algebra.NamedRings.ringNumeral do
      throwError "a tuple point changed its original target domain or declared scalar numeral"
  let mut originalFunction := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) := statement then
      let .definition next _ ← file.withContext (session.readStatement statement)
        | throwError "the original function declaration did not extend its complete context"
      unless name.getId == `expectedF &&
          next.context.entries.size == session.context.entries.size + 1 do
        throwError "the original function changed its name or complete context"
      session := next
      originalFunction := true
      break
  unless originalFunction do throwError "the original function declaration was not inspected"
  let vectors ← session.read (← sourceTerm "Vec(Q, 2) in Sets")
  unless vectors.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
    throwError "the vector parameter shortened its original preceding context"
  let some scalarEntry := session.context.entries.find? (·.userName == `Q)
    | throwError "the original selected scalar object is absent"
  vectors.source.withOpen fun bindings expression => do
    let some scalar := bindings.find? (·.id == scalarEntry.id)
      | throwError "the vector parameter lost the original selected scalar binding"
    unless expression.containsFVar scalar.expression.fvarId! &&
        expression.containsConst (· == ``CasCatalogue.Algebra.LinearAlgebra.vectors) do
      throwError "the vector parameter replaced its selected source carrier"
    let carrier ← mkAppM ``CommRingCat.carrier #[scalar.expression]
    let expected ← mkAppM ``CasCatalogue.Algebra.LinearAlgebra.vectors #[carrier, mkNatLit 2]
    unless ← isDefEq expression expected do
      throwError "the vector declaration differs from the selected scalar's native carrier"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
  session := ← session.defineTerm `vectorSet vectors
  let product ← session.read (← sourceTerm "vectorSet × vectorSet")
  unless product.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
    throwError "the original product shortened its complete preceding context"
  let some vectorEntry := session.context.entries.find? (·.userName == `vectorSet)
    | throwError "the original vector-set declaration is absent"
  product.source.withOpen fun bindings value => do
    let some vectorSet := bindings.find? (·.id == vectorEntry.id)
      | throwError "the original product lost its selected vector-set binding"
    let presentation ← mkAppM ``CasCatalogue.Limits.Registration.setsProduct
      #[vectorSet.expression, vectorSet.expression]
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let expected ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    unless value.containsFVar vectorSet.expression.fvarId! &&
        value.containsConst (· == ``CasCatalogue.Limits.Registration.setsProduct) &&
        (← isDefEq value expected) do
      throwError "the original product replaced its actual vector set or universal presentation"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  session := ← session.defineTerm `pairOfVectors product
  let .ok native := Parser.runParserCategory (← getEnv) `term
      "TypeCat.ofHom (fun (p : pairOfVectors) => X.pairing p.1 p.2)"
    | throwError "the independently declared native pairing control did not parse"
  let expectedPairing ← session.term ⟨native⟩
  let mut originalPairing := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) := statement then
      unless name.getId == `sourcePairing do continue
      let .definition _ value ← file.withContext (session.readStatement statement)
        | throwError "the original pairing declaration did not form its source function"
      unless value.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
        throwError "the original pairing shortened its complete preceding context"
      value.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let expected ← expectedPairing.source.inContext context
        unless expression.containsConst
            (· == ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.pairing) &&
            (← isDefEq expression expected) do
          throwError "the original pairing changed its complete declared native map"
        checkWithKernel
          (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
      originalPairing := true
      break
  unless originalPairing do throwError "the original pairing declaration was not inspected"


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
