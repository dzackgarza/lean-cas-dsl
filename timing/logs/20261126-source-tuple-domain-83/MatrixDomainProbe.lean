module

import CasRuntime.Session
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction

namespace CasRuntime.ConstrainedPointTests

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeSyntax (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native constrained-point control did not parse"
  return ⟨stx⟩

private def readSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the constrained-point source control did not parse"
  session.read ⟨stx⟩

private def rejected (session : SourceSession) (text : String) (tag : Name) : TermElabM Unit := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the constrained-point source control did not parse"
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| session.read ⟨stx⟩
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "the constrained-point source was incorrectly admitted: {text}"
  unless failure.toMessageData.hasTag (· == tag) do throw failure

-- The same native Hom endpoint inspection as SourceReader.mapEnds, in the MetaM context
-- of ClosedTerm.withOpen. This fixture adds no source interpretation or chosen endpoint.
private def mapEndpoints (arrow : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR (← instantiateMVars (← inferType arrow))
  if type.isAppOfArity ``Quiver.Hom 4 then
    return some (← declaredEndpoint type.getAppArgs[2]!,
      ← declaredEndpoint type.getAppArgs[3]!)
  if type.isAppOfArity ``TypeCat.Hom 2 then
    return some (type.getAppArgs[0]!, type.getAppArgs[1]!)
  return none

-- Native Subtype is the independently declared constructor. Its one computational field
-- is the actual opaque input, even though no numeric value is supplied or observed.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let owner ← owners.spawn { cmd := "/bin/cat" }
    try
      let empty ← SourceSession.empty owners.identities
      let dataSource ← empty.assume `datum (← nativeSyntax "Nat")
      let some datumEntry := dataSource.context.entries.back?
        | throwError "the constrained input lost its original source declaration"
      let source ← dataSource.define `target (← nativeSyntax "{ n : Nat // n = datum }")
      let admitted ← readSource source "datum in target using (proof(rfl))"
      for (text, tag) in #[
          ("datum in target using (proof(True.intro))", `CasCompiler.sourceFormalProof.typeMismatch),
          ("datum in target using (proof(rfl), proof(rfl))", `CasCompiler.sourceConstrainedPoint.proofCount),
          ("datum in target using (rfl)", `CasCompiler.SourceReader.explicitProof),
          ("datum in target", `CasCompiler.SourceReader.declaredParameterType)] do
        rejected source text tag
      let twoFields ← source.define `target (← nativeSyntax "Nat × Nat")
      rejected twoFields "datum in target using (proof(True.intro))"
        `CasCompiler.sourceConstrainedPoint.dataFieldCount
      let recursiveSource ← source.define `target (← nativeSyntax "List Nat")
      rejected recursiveSource "datum in target using (proof(True.intro))"
        `CasCompiler.sourceConstrainedPoint.structureShape
      SourceTest.checkSelected admitted fun expression => do
        let scope ← get
        let some datum := scope.context.bindings.find? (·.id == datumEntry.id)
          | liftM (m := TermElabM) <| throwError "the constrained input lost its original source binding"
        let originalData ← SourceTest.visitNativeData
          (fun term => pure (term.equal datum.expression)) expression (throughAuthoredLets := false)
        let constructors ← SourceTest.visitNativeData
          (fun term => pure (term.isConstOf ``Subtype.mk)) expression (throughAuthoredLets := false)
        unless originalData > 0 && constructors > 0 do
          liftM (m := TermElabM) <| throwError "constrained formation replaced its original data or native constructor"
      admitted.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let selections ← admitted.selections.inContext context
        let some datum := bindings.find? (·.id == datumEntry.id)
          | throwError "the constrained input lost its original source binding"
        let layout ← SourceLayout.ofTerm admitted.source (selections := admitted.selections)
        unless layout.kind == .record &&
            (layout.fields.filter (·.wireIndex.isSome)).size == 1 &&
            (layout.fields.filter (·.kind == .proof)).size == 1 do
          throwError "constrained formation erased data or invented a computational proof field"
        let producer ← CellTransaction.begin kernel.ledger
        let program ← owners.identities.fresh .program
        let input ← producer.stage
          { program, occurrence := ← kernel.ledger.allocate,
            role := ← SourceLayout.ofTerm (← context.close datum.expression)
              (selections := admitted.selections),
            parameters := Array.replicate bindings.size none }
          (.ownedExport owner "original constrained input" #[])
        let .ok _ ← producer.commit
          | throwError "the original constrained input could not publish"
        let consumer ← CellTransaction.begin kernel.ledger
        try
          let supplied : Std.HashMap BindingId ValueBinding := {}
          let value ← kernel.run consumer context (supplied.insert datum.id input) expression
            (selections := selections)
          let graph ← consumer.view
          let some node := graph.find value.value
            | throwError "the constrained value is outside its actual graph"
          let some fields := node.payload.data.storedFields?
            | throwError "the native constrained value lost its stored data field"
          unless fields.size == 1 do
            throwError "the native constrained value invented an additional field"
          let .ok actual := graph.project value 0
            | throwError "the constrained value lost its declared computational field"
          unless actual.value == input.value &&
              input.associationIds.toList.isPrefixOf actual.associationIds.toList do
            throwError "the constrained value replaced the actual original data"
          let some originalNode := graph.find actual.value
            | throwError "the original constrained data are outside the visible graph"
          let .ownedToken generation token _ := originalNode.payload.data
            | throwError "the constrained value decoded or replaced opaque data"
          unless generation == owner.generation && token == "original constrained input" &&
              (← kernel.dispatches.get).isEmpty do
            throwError "constrained formation changed ownership or dispatched a provider"
        finally discard <| consumer.abort
    finally
      owners.close owner.generation
      kernel.close
  finally setEnv original

-- The prerequisite declarations and membership proof are unchanged RX08 source. This is
-- formal reading only: no kernel coordinate, inclusion, or pairing answer is supplied.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let identities ← liftM (m := IO) IdentitySupply.new
    let mut session ← SourceSession.empty identities
    for text in #[
        "let Q := ℚ in CommutativeRings",
        "let Qring := view Q along «fun.commutative_rings.ring»()",
        "let scalarModule := RegularModule(Qring)",
        "let formedSource := RationalDiagonal23()",
        "let sourceModule := view formedSource along «fun.bilin_module.forget»(ℚ, ℚ)",
        "let row := [1, 0] in RectangularMatrices(1, 2, Q)",
        "let projection := row_linear_map(2, Q, row)",
        "let restricted := RestrictToModuleKernel(Q, scalarModule, formedSource, scalarModule, projection)",
        "let formedInclusion := ordinary_kernel_inclusion(Q, scalarModule, formedSource, scalarModule, projection)",
        "let restrictionCarrier := view restricted along «fun.bilin_module.forget»(ℚ, ℚ)",
        "let coordinateData(t) := (0, t) in (ℚ in Sets) → (Vec(Q, 2) in Sets)"] do
      let .ok stx := Parser.runParserCategory (← getEnv) `cas_stmt text
        | throwError "an original RX08 declaration did not parse"
      if text == "let row := [1, 0] in RectangularMatrices(1, 2, Q)" then
        withoutModifyingState do
          let declared ← readSource session "RectangularMatrices(1, 2, Q)"
          discard <| session.elaborateScoped Syntax.missing do
            let expected ← session.readTerm declared
            let head := fun (value : Expr) => match value.getAppFn with
              | .const name _ => s!"const:{name}"
              | .fvar id => s!"fvar:{id.name}"
              | .mvar id => s!"mvar:{id.name}"
              | .bvar index => s!"bvar:{index}"
              | .lit value => s!"literal:{reprStr value}"
              | .forallE .. => "forall"
              | .lam .. => "lambda"
              | .letE .. => "let"
              | .mdata .. => "metadata"
              | .proj .. => "projection"
              | _ => "other"
            let mut current := expected
            for step in [:16] do
              let normalized ← liftM (m := MetaM) <| whnf current
              let selected ← SourceReadM.selection? normalized
              liftM (m := IO) <| IO.println s!"MATRIX_TYPE step={step} input={head current} whnf={head normalized} selected={selected.isSome}"
              if let .forallE _ domain codomain _ := normalized then
                let index ← liftM (m := MetaM) <| whnf domain
                liftM (m := IO) <| IO.println s!"MATRIX_INDEX head={head index} arity={index.getAppNumArgs}"
                for argument in index.getAppArgs do
                  liftM (m := IO) <| IO.println s!"MATRIX_DIMENSION head={head argument}"
                if !codomain.hasLooseBVars then
                  let row ← liftM (m := MetaM) <| whnf codomain
                  liftM (m := IO) <| IO.println s!"MATRIX_ROW head={head row}"
                  if let .forallE _ column coefficient _ := row then
                    let column ← liftM (m := MetaM) <| whnf column
                    liftM (m := IO) <| IO.println s!"MATRIX_COLUMN head={head column} coefficient={head coefficient}"
                    for argument in column.getAppArgs do
                      liftM (m := IO) <| IO.println s!"MATRIX_COLUMN_DIMENSION head={head argument}"
                break
              let some selected := selected | break
              liftM (m := IO) <| IO.println s!"MATRIX_SELECTION value={head selected.value} arity={selected.value.getAppNumArgs} reference={reprStr (selected.reference.bind (·.declaration))} category={selected.category.isSome} typeOrigin={selected.typeOrigin.isSome}"
              for argument in selected.value.getAppArgs do
                liftM (m := IO) <| IO.println s!"MATRIX_RETAINED_ARG head={head argument}"
              if let some origin := selected.typeOrigin then
                liftM (m := IO) <| IO.println s!"MATRIX_ORIGIN object={head origin.object} type={head origin.type}"
              if selected.value.equal normalized then break
              current := selected.value
            return expected
      let checked ← try session.readStatement ⟨stx⟩
        catch failure => throwError
          "the original RX08 declaration did not read: {text}; {failure.toMessageData}"
      let .definition next _ := checked
        | throwError "an original RX08 declaration changed statement kind"
      session := next
    let text := "coordinateData in restrictionCarrier using (proof(by intro t; exact (CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction.RationalProjection.mem_kernel ![0, t]).2 rfl))"
    let admitted ← readSource session text
    let nativeType ← session.term (← nativeSyntax "Type")
    let .ok carrierSyntax := Parser.runParserCategory (← getEnv) `cas_term "restrictionCarrier"
      | throwError "the original constrained target did not parse"
    let expectedTarget ← session.read ⟨carrierSyntax⟩ (some nativeType.source)
      (expectedSelections := nativeType.selections)
    let some category := admitted.category
      | throwError "the generalized constrained point lost its source-map category"
    unless category.role == .morphism &&
        category.expression.syntacticEq (.atom CategoryId.sets) do
      throwError "the generalized constrained point acquired another categorical role"
    let some coordinateEntry := session.context.entries.find? (·.userName == `coordinateData)
      | throwError "RX08 lost its original coordinate declaration"
    SourceTest.checkSelected admitted fun expression => do
      let scope ← get
      let some coordinateData := scope.context.bindings.find? (·.id == coordinateEntry.id)
        | liftM (m := TermElabM) <| throwError "RX08 lost its original coordinate map"
      let originalData ← SourceTest.visitNativeData
        (fun term => pure (term.equal coordinateData.expression)) expression
        (throughAuthoredLets := false)
      let constructors ← SourceTest.visitNativeData
        (fun term => pure (term.isConstOf ``Subtype.mk)) expression (throughAuthoredLets := false)
      let proofs ← SourceTest.visitNativeData (fun term => pure (term.isConstOf
        ``CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction.RationalProjection.mem_kernel))
        expression (throughAuthoredLets := false)
      unless originalData > 0 && constructors > 0 && proofs > 0 do
        liftM (m := TermElabM) <| throwError "RX08 changed its original map, full domain, selected target or supplied proof"
      let target ← session.readTerm expectedTarget
      SourceTest.checkOriginal #[coordinateData.expression, expression, target] fun terms => do
        let some (originalDomain, _) ← mapEndpoints terms[0]!
          | throwError "the original coordinate data lost its complete map domain"
        let some (actualDomain, actualTarget) ← mapEndpoints terms[1]!
          | throwError "the constrained coordinate data are not a complete generalized point"
        unless (← isDefEq actualDomain originalDomain) && (← isDefEq actualTarget terms[2]!) do
          throwError "RX08 changed its original map, full domain, selected target or supplied proof"
    -- A proof at one sample cannot replace the original universally quantified evidence.
    rejected session "coordinateData in restrictionCarrier using (proof((CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction.RationalProjection.mem_kernel ![0, (0 : ℚ)]).2 rfl))"
      `CasCompiler.sourceFormalProof.typeMismatch
    let withPoint ← session.defineTerm `kappa admitted
    let composite ← try readSource withPoint "formedInclusion(kappa)"
      catch failure => throwError
        "the original whole coordinate application did not read: {failure.toMessageData}"
    let some category := composite.category
      | throwError "the original whole coordinate inclusion lost its morphism role"
    unless category.role == .morphism &&
        category.expression.syntacticEq (.atom CategoryId.sets) do
      throwError "the original whole coordinate inclusion changed its carrier category"
    let some inclusionEntry := withPoint.context.entries.find? (·.userName == `formedInclusion)
      | throwError "the original formed inclusion binding is absent"
    let some pointEntry := withPoint.context.entries.find? (·.userName == `kappa)
      | throwError "the original admitted coordinate binding is absent"
    SourceTest.checkSelected composite fun expression => do
      let scope ← get
      let some inclusion := scope.context.bindings.find? (·.id == inclusionEntry.id)
        | liftM (m := TermElabM) <| throwError "the original formed inclusion is outside the source context"
      let some point := scope.context.bindings.find? (·.id == pointEntry.id)
        | liftM (m := TermElabM) <| throwError "the original coordinate map is outside the source context"
      let originalInclusion ← SourceTest.visitNativeData
        (fun term => pure (term.equal inclusion.expression)) expression (throughAuthoredLets := false)
      let originalPoint ← SourceTest.visitNativeData
        (fun term => pure (term.equal point.expression)) expression (throughAuthoredLets := false)
      unless originalInclusion > 0 && originalPoint > 0 do
        liftM (m := TermElabM) <| throwError "the whole coordinate inclusion replaced its actual source maps"
      SourceTest.checkOriginal #[expression, inclusion.expression, point.expression] fun terms => do
        -- Fixed.forget uses this independently declared underlyingMap. Its full implicit
        -- parameters, including the chosen Module instance, come from the actual arrow
        -- before any projection is applied; no instance is synthesized at ↑Q ↑scalarModule.
        let expected ← try
            let declaration ← mkConstWithFreshMVarLevels
              ``LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.underlyingMap
            let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
            let some arrow := parameters.back?
              | throwError "the native underlying map has no morphism parameter"
            unless ← isDefEq arrow terms[1]! do
              throwError "the native underlying map changed the actual inclusion type"
            let linear ← instantiateMVars (mkAppN declaration parameters)
            if linear.hasMVar || linear.hasLevelMVar then
              throwError "the native inclusion did not determine its complete parameters"
            let additive ← mkProjection linear `toAddHom
            let function ← mkProjection additive `toFun
            let carrierMap ← mkAppM ``TypeCat.ofHom #[function]
            mkAppM ``CategoryTheory.CategoryStruct.comp #[terms[2]!, carrierMap]
          catch failure => throwError
            "the native coordinate inclusion composite did not elaborate: {failure.toMessageData}"
        unless ← isDefEq terms[0]! expected do
          throwError "the whole coordinate inclusion replaced its actual source maps"
    let .ok question := Parser.runParserCategory (← getEnv) `cas_term
      "formedInclusion(kappa) = coordinateData"
      | throwError "the original whole coordinate assertion did not parse"
    discard <| withPoint.readQuestion ⟨question⟩
  finally setEnv original

-- Literal data use the same independently fixed native record constructor. The numeral
-- reader must leave a non-categorical proof annotation to constrained-point formation.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let identities ← liftM (m := IO) IdentitySupply.new
    let empty ← SourceSession.empty identities
    let source ← empty.define `numericTarget (← nativeSyntax "{ n : Nat // n = 3 }")
    let admitted ← readSource source "3 in numericTarget using (proof(rfl))"
    SourceTest.checkSelected admitted fun expression => do
      let constructors ← SourceTest.visitNativeData
        (fun term => pure (term.isConstOf ``Subtype.mk)) expression (throughAuthoredLets := false)
      unless constructors > 0 do
        liftM (m := TermElabM) <| throwError "the constrained literal lost its native record constructor"
    rejected source "3 in numericTarget using (proof(True.intro))"
      `CasCompiler.sourceFormalProof.typeMismatch
    rejected source "3 in numericTarget using (proof(rfl), proof(rfl))"
      `CasCompiler.sourceConstrainedPoint.proofCount
  finally setEnv original

end CasRuntime.ConstrainedPointTests
