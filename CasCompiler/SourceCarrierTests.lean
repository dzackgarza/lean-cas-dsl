module

import CasTools.QuestionExport
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
meta import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | liftM (m := MetaM) <| throwError "the source carrier control did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let input ← liftM (m := IO) (IO.FS.readFile path)
  let file ← SourceFile.parse path input
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let checkContext := fun (session : SourceSession) (term : SourceTerm) (reason : String) => do
    let expected ← SourceTest.authoredEntries session.context session.selections
    let actual ← SourceTest.authoredEntries term.source.context term.selections
    term.source.withOpen fun bindings _ => do
      let original ← ContextTelescope.capture (bindings.take session.context.entries.size)
      unless original.telescope.exactlyMatches session.context do
        liftM (m := MetaM) <| throwError reason
    unless actual.map (·.id) == expected.map (·.id) do
      liftM (m := MetaM) <| throwError reason
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | break
    if let `(cas_stmt| let $_:ident($_:cas_term) := $_:cas_term) := statement then break
    let .definition next _ ← file.withContext (session.readStatement statement)
      | liftM (m := MetaM) <| throwError "the original carrier prefix stopped before its function definition"
    session := next
  let source ← session.read (← sourceTerm "sourceModule")
  let some category := source.category
    | liftM (m := MetaM) <| throwError "the original source module lost its complete selected category"
  let routes ← SourceRoutes.forOwner category.expression (.atom CategoryId.sets)
  let some candidates ← routes.finiteRoutes
    | liftM (m := MetaM) <| throwError "the original module carrier control requires its complete finite route family"
  let domain ← session.read (← sourceTerm "sourceModule → targetModule")
  checkContext session domain "a carrier-domain expression shortened its complete original context"
  let some category := domain.category
    | liftM (m := MetaM) <| throwError "a carrier-domain expression lost its selected set category"
  unless category.role == .object &&
      category.expression.syntacticEq (.atom CategoryId.sets) do
    liftM (m := MetaM) <| throwError "a carrier-domain expression changed its source category or object role"
  let some sourceEntry := session.context.entries.find? (·.userName == `sourceModule)
    | liftM (m := MetaM) <| throwError "the original source-module declaration is absent"
  let some targetEntry := session.context.entries.find? (·.userName == `targetModule)
    | liftM (m := MetaM) <| throwError "the original target-module declaration is absent"
  SourceTest.checkSelected domain fun expression => do
    let bindings := (← get).context.bindings
    let expression ← SourceTest.selectedValue expression
    unless expression.isAppOfArity ``TypeCat.Hom 2 do
      liftM (m := MetaM) <| throwError "the original function domain did not retain its native set-map type"
    let source := expression.getAppArgs[0]!
    let target := expression.getAppArgs[1]!
    for carrier in #[source, target] do
      let some selected ← SourceReadM.selection? carrier
        | liftM (m := MetaM) <| throwError "a carrier discarded its actual route references"
      let some origin := selected.typeOrigin
        | liftM (m := MetaM) <| throwError "a source carrier discarded its exact selected owner"
      unless selected.carrierRoutes == candidates.map (·.refs) do
        liftM (m := MetaM) <| throwError "a carrier discarded an original structural route"
      if candidates.size > 1 then
        let .letE _ proposition proof _ _ := origin.type
          | liftM (m := MetaM) <| throwError "implicit carrier alternatives lost their equality evidence"
        SourceTest.checkOriginal #[proposition, proof] fun values => do
          unless values[0]!.isAppOfArity ``Eq 3 &&
              (← whnf values[0]!.getAppArgs[0]!).isAppOf ``CategoryTheory.Functor &&
              values[1]!.getUsedConstants.contains ``congrFun do
            liftM (m := MetaM) <| throwError "carrier evidence compared particular objects instead of complete functors"
    let some sourceBinding := bindings.find? (·.id == sourceEntry.id)
      | liftM (m := MetaM) <| throwError "the original source-module binding is absent"
    let some targetBinding := bindings.find? (·.id == targetEntry.id)
      | liftM (m := MetaM) <| throwError "the original target-module binding is absent"
    for (carrier, binding) in #[(source, sourceBinding), (target, targetBinding)] do
      let some origin := (← SourceReadM.selection? carrier).bind (·.typeOrigin)
        | liftM (m := MetaM) <| throwError "the original carrier lost its typed source owner"
      let scope ← get
      unless (← SourceTest.originatesAt scope.context scope.selections
          origin.object binding.expression false) && origin.category.role == .object do
        liftM (m := MetaM) <| throwError "native context transport changed a carrier's original selected object"
    let occurs := fun expression original =>
      SourceTest.visitNativeData (fun value => pure (value.equal original)) expression false
    unless (← occurs source sourceBinding.expression) > 0 &&
        (← occurs source targetBinding.expression) == 0 &&
        (← occurs target targetBinding.expression) > 0 &&
        (← occurs target sourceBinding.expression) == 0 do
      liftM (m := MetaM) <| throwError "carrier formation replaced or exchanged its original selected module objects"
    discard <| getLevel source
    discard <| getLevel target
  let coordinate ← session.read (← sourceTerm
    "((a, b) ↦ a) in sourceModule → (ℚ in Sets)")
  SourceTest.checkSelected coordinate fun expression => do
    let bindings := (← get).context.bindings
    let some sourceBinding := bindings.find? (·.id == sourceEntry.id)
      | liftM (m := MetaM) <| throwError "the original coordinate function lost its source-module binding"
    unless (← SourceTest.visitNativeData (fun value =>
        pure (value.equal sourceBinding.expression)) (← inferType expression) false) > 0 do
      liftM (m := MetaM) <| throwError "a coordinate function replaced its actual source-module domain"
  let reordered ← session.read (← sourceTerm
    "((a, b) ↦ (b, a)) in sourceModule → targetModule")
  SourceTest.checkSelected reordered fun expression => do
    let bindings := (← get).context.bindings
    let some sourceBinding := bindings.find? (·.id == sourceEntry.id)
      | liftM (m := MetaM) <| throwError "the tuple function lost its source-module binding"
    let some targetBinding := bindings.find? (·.id == targetEntry.id)
      | liftM (m := MetaM) <| throwError "the tuple function lost its target-module binding"
    let type ← inferType expression
    let occurs := fun original =>
      SourceTest.visitNativeData (fun value => pure (value.equal original)) type false
    unless (← occurs sourceBinding.expression) > 0 && (← occurs targetBinding.expression) > 0 &&
        (← SourceTest.visitNativeData (fun value => pure (value.isConstOf ``Fin.cases)) expression) > 0 do
      liftM (m := MetaM) <| throwError "a tuple function replaced its original domains or native components"
  let pointFunction ← session.read (← sourceTerm
    "((a, b) ↦ (a, 0)) in sourceModule → targetModule")
  SourceTest.checkSelected pointFunction fun expression => do
    let bindings := (← get).context.bindings
    let some targetBinding := bindings.find? (·.id == targetEntry.id)
      | liftM (m := MetaM) <| throwError "the point-valued tuple lost its target-module binding"
    unless (← SourceTest.visitNativeData (fun value =>
        pure (value.equal targetBinding.expression)) (← inferType expression) false) > 0 &&
        (← SourceTest.visitNativeData (fun value =>
          pure (value.isConstOf ``CasCatalogue.Algebra.NamedRings.ringNumeral)) expression) > 0 do
      liftM (m := MetaM) <| throwError "a tuple point changed its original target domain or declared scalar numeral"
  let mut originalFunction := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) := statement then
      let .definition next value ← file.withContext (session.readStatement statement)
        | liftM (m := MetaM) <| throwError "the original function declaration did not extend its complete context"
      checkContext session value "the original function changed its name or complete context"
      unless name.getId == `expectedF &&
          next.context.entries.size == value.source.context.entries.size + 1 &&
          (next.context.entries.take value.source.context.entries.size).map (·.id) ==
            value.source.context.entries.map (·.id) do
        liftM (m := MetaM) <| throwError "the original function changed its name or complete context"
      session := next
      originalFunction := true
      break
  unless originalFunction do liftM (m := MetaM) <| throwError "the original function declaration was not inspected"
  let vectors ← session.read (← sourceTerm "Vec(Q, 2) in Sets")
  checkContext session vectors "the vector parameter shortened its original preceding context"
  let some scalarEntry := session.context.entries.find? (·.userName == `Q)
    | liftM (m := MetaM) <| throwError "the original selected scalar object is absent"
  SourceTest.checkSelected vectors fun expression => do
    let bindings := (← get).context.bindings
    let some scalar := bindings.find? (·.id == scalarEntry.id)
      | liftM (m := MetaM) <| throwError "the vector parameter lost the original selected scalar binding"
    unless (← SourceTest.visitNativeData (fun value =>
        pure (value.equal scalar.expression)) expression false) > 0 &&
        (← SourceTest.visitNativeData (fun value =>
          pure (value.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.vectors)) expression) > 0 do
      liftM (m := MetaM) <| throwError "the vector parameter replaced its selected source carrier"
    let carrier ← mkAppM ``CommRingCat.carrier #[scalar.expression]
    let expected ← mkAppM ``CasCatalogue.Algebra.LinearAlgebra.vectors #[carrier, mkNatLit 2]
    SourceTest.checkOriginal #[expression, expected] fun values => do
      unless ← isDefEq values[0]! values[1]! do
        liftM (m := MetaM) <| throwError "the vector declaration differs from the selected scalar's native carrier"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! values[1]!))
  session := ← session.defineTerm `vectorSet vectors
  let product ← session.read (← sourceTerm "vectorSet × vectorSet")
  checkContext session product "the original product shortened its complete preceding context"
  let some vectorEntry := session.context.entries.find? (·.userName == `vectorSet)
    | liftM (m := MetaM) <| throwError "the original vector-set declaration is absent"
  SourceTest.checkSelected product fun value => do
    let bindings := (← get).context.bindings
    let some vectorSet := bindings.find? (·.id == vectorEntry.id)
      | liftM (m := MetaM) <| throwError "the original product lost its selected vector-set binding"
    let presentation ← mkAppM ``CasCatalogue.Limits.Registration.setsProduct
      #[vectorSet.expression, vectorSet.expression]
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let expected ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    unless (← SourceTest.visitNativeData (fun expression =>
        pure (expression.equal vectorSet.expression)) value false) > 0 &&
        (← SourceTest.visitNativeData (fun expression =>
          pure (expression.isConstOf ``CasCatalogue.Limits.Registration.setsProduct)) value) > 0 do
      liftM (m := MetaM) <| throwError "the original product replaced its actual vector set or universal presentation"
    SourceTest.checkOriginal #[value, expected] fun values => do
      unless ← isDefEq values[0]! values[1]! do
        liftM (m := MetaM) <| throwError "the original product replaced its actual vector set or universal presentation"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! values[1]!))
  session := ← session.defineTerm `pairOfVectors product
  let .ok native := Parser.runParserCategory (← getEnv) `term
      "TypeCat.ofHom (fun (p : pairOfVectors) => X.pairing p.1 p.2)"
    | liftM (m := MetaM) <| throwError "the independently declared native pairing control did not parse"
  let expectedPairing ← session.term ⟨native⟩
  let mut originalPairing := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) := statement then
      unless name.getId == `sourcePairing do continue
      let .definition next value ← file.withContext (session.readStatement statement)
        | liftM (m := MetaM) <| throwError "the original pairing declaration did not form its source function"
      checkContext session value "the original pairing shortened its complete preceding context"
      SourceTest.checkSelected value fun expression => do
        let context := (← get).context
        let expected ← expectedPairing.source.inContext context
        unless (← SourceTest.visitNativeData (fun expression =>
            pure (expression.isConstOf ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.pairing))
            expression) > 0 do
          liftM (m := MetaM) <| throwError "the original pairing changed its complete declared native map"
        SourceTest.checkOriginal #[expression, expected] fun values => do
          unless ← isDefEq values[0]! values[1]! do
            liftM (m := MetaM) <| throwError "the original pairing changed its complete declared native map"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! values[1]!))
      originalPairing := true
      session := next
      break
  unless originalPairing do liftM (m := MetaM) <| throwError "the original pairing declaration was not inspected"
  let .ok native := Parser.runParserCategory (← getEnv) `term
      "TypeCat.ofHom (fun (p : pairOfVectors) => Y.pairing (LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.underlyingMap f p.1) (LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.underlyingMap f p.2))"
    | liftM (m := MetaM) <| throwError "the native image-pairing control did not parse"
  let expectedImage ← session.term ⟨native⟩
  let mut originalImage := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) := statement then
      unless name.getId == `imagePairing do continue
      let .definition next value ← file.withContext (session.readStatement statement)
        | liftM (m := MetaM) <| throwError "the original image pairing did not form its source function"
      checkContext session value "the original image pairing shortened its complete preceding context"
      SourceTest.checkSelected value fun expression => do
        let context := (← get).context
        let expected ← expectedImage.source.inContext context
        SourceTest.checkOriginal #[expression, expected] fun values => do
          unless ← isDefEq values[0]! values[1]! do
            liftM (m := MetaM) <| throwError "the original image pairing changed its selected native map action"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! values[1]!))
      originalImage := true
      session := next
      break
  unless originalImage do liftM (m := MetaM) <| throwError "the original image-pairing declaration was not inspected"
  let .ok native := Parser.runParserCategory (← getEnv) `term
      "TypeCat.ofHom (fun (t : scalarModule) => CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion.hom t)"
    | liftM (m := MetaM) <| throwError "the native inclusion control did not parse"
  let expectedInclusion ← session.term ⟨native⟩
  let mut originalInclusion := false
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) := statement then
      unless name.getId == `i0 do continue
      let .definition _ value ← file.withContext (session.readStatement statement)
        | liftM (m := MetaM) <| throwError "the original inclusion did not form its source function"
      checkContext session value "the original inclusion shortened its complete preceding context"
      SourceTest.checkSelected value fun expression => do
        let context := (← get).context
        let expected ← expectedInclusion.source.inContext context
        SourceTest.checkOriginal #[expression, expected] fun values => do
          unless ← isDefEq values[0]! values[1]! do
            liftM (m := MetaM) <| throwError "the original inclusion differs from its actual declared native map"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! values[1]!))
      originalInclusion := true
      break
  unless originalInclusion do liftM (m := MetaM) <| throwError "the original inclusion declaration was not inspected"


run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let order ← empty.read (← sourceTerm "ReverseFinOrder(3) in LinearOrders")
  let some selection := order.category.bind (·.carrier)
    | liftM (m := MetaM) <| throwError "a selected object lost its independently declared carrier prefix"
  let session ← empty.defineTerm `X order
  let domain ← session.read (← sourceTerm "X → X")
  SourceTest.checkSelected domain fun expression => do
    let bindings ← SourceTest.authoredBindings
    let expression ← SourceTest.selectedValue expression
    for carrier in expression.getAppArgs do
      unless (← SourceTest.visitNativeData (fun value =>
          pure (value.equal bindings[0]!.expression)) carrier false) > 0 do
        liftM (m := MetaM) <| throwError "a selected carrier was replaced by its named comparison target"
      let some selected ← SourceReadM.selection? carrier
        | liftM (m := MetaM) <| throwError "a selected carrier discarded its actual route"
      let some origin := selected.typeOrigin
        | liftM (m := MetaM) <| throwError "a selected carrier discarded its exact native owner"
      let scope ← get
      unless ← SourceTest.originatesAt scope.context scope.selections origin.object
          bindings[0]!.expression false do
        liftM (m := MetaM) <| throwError "a selected carrier discarded its exact native owner"
      unless selected.carrierRoutes == #[selection.refs] do
        liftM (m := MetaM) <| throwError "a selected carrier was replaced by another structural route"
  let some edge := selection.refs[0]?
    | liftM (m := MetaM) <| throwError "the selected carrier prefix control has no actual edge"
  let .functor id := edge
    | liftM (m := MetaM) <| throwError "the selected carrier prefix control requires its registered functor"
  let image ← session.read (← sourceTerm s!"view X along «{id.raw}»()")
  let some remainder := image.category.bind (·.carrier)
    | liftM (m := MetaM) <| throwError "an explicit view discarded its selected carrier continuation"
  unless remainder.refs.isEmpty && remainder.target.syntacticEq selection.target &&
      remainder.identifications == selection.identifications do
    liftM (m := MetaM) <| throwError "an explicit view changed its supplied carrier continuation or comparison"
  let session ← session.defineTerm `Y image
  let retainedTerm ← session.read (← sourceTerm "Y")
  let some retained := retainedTerm.category.bind (·.carrier)
    | liftM (m := MetaM) <| throwError "a native alias lost its selected carrier continuation"
  unless retained.refs == remainder.refs &&
      retained.identifications == remainder.identifications do
    liftM (m := MetaM) <| throwError "a native alias changed its actual selected carrier data"



  let other ← session.read (← sourceTerm "ReverseFinOrder(4) in LinearOrders")
  let some category := order.category
    | liftM (m := MetaM) <| throwError "the comparison control lost its original category"
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| session.elaborateScoped Syntax.missing do
        let actual ← session.readTerm order
        let alternative ← session.readTerm other
        let some original ← SourceReadM.selection? actual
          | liftM (m := TermElabM) <| throwError "the comparison control lost its actual object"
        let some supplied ← SourceReadM.selection? alternative
          | liftM (m := TermElabM) <| throwError "the comparison control lost its alternate application"
        let some originalReference := original.reference
          | liftM (m := TermElabM) <| throwError "the actual object lost its full original row"
        let some suppliedReference := supplied.reference
          | liftM (m := TermElabM) <| throwError "the alternate object lost its full original row"
        unless originalReference.exactlyMatches suppliedReference do
          liftM (m := TermElabM) <| throwError "the comparison control changed its selected row"
        let .named (.registered (.inl entry) _) := originalReference
          | liftM (m := TermElabM) <| throwError "the comparison control requires its registered object"
        let some application ← sourceApplication? entry.declaration supplied
          | liftM (m := TermElabM) <| throwError "the comparison control lost its declared application"
        let mismatched ← SourceReadM.select { original with originalApplication := some application }
        let bundle ← category.bundle.inContext (← get).context
        discard <| objectCarrierSelection entry bundle mismatched
        return mismatched
      pure none
    catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "the carrier comparison accepted different original parameters"
  unless (← failure.toMessageData.toString) ==
      "the selected carrier action has different complete comparison parameters" do
    throw failure



  let ordinary ← session.read (← sourceTerm "FinOrder(3) in LinearOrders")
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| session.elaborateScoped Syntax.missing do
        let actual ← session.readTerm order
        let alternative ← session.readTerm ordinary
        let some original ← SourceReadM.selection? actual
          | liftM (m := TermElabM) <| throwError "the same-carrier control lost its reverse order"
        let some supplied ← SourceReadM.selection? alternative
          | liftM (m := TermElabM) <| throwError "the same-carrier control lost its ordinary order"
        let some (.named (.registered (.inl entry) _)) := original.reference
          | liftM (m := TermElabM) <| throwError "the same-carrier control lost its complete original row"
        let scope ← get
        liftM (m := MetaM) <|
          scope.context.withOriginalSources #[original.value, supplied.value] fun sources => do
            let left ← mkAppM ``CasCatalogue.Foundation.PowerSets.orderCarrier #[sources[0]!]
            let right ← mkAppM ``CasCatalogue.Foundation.PowerSets.orderCarrier #[sources[1]!]
            unless ← isDefEq left right do
              throwError "the distinct-order control does not have the same native carrier"
            if ← withoutModifyingState <| isDefEq sources[0]! sources[1]! then
              throwError "the same-carrier control does not have distinct complete orders"
        let mismatched ← SourceReadM.select { original with value := supplied.value }
        let bundle ← category.bundle.inContext (← get).context
        discard <| objectCarrierSelection entry bundle mismatched
        return mismatched
      pure none
    catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "the carrier comparison accepted another selected structure on the same carrier"
  unless (← failure.toMessageData.toString) ==
      "the selected carrier action has different complete comparison parameters" do
    throw failure
