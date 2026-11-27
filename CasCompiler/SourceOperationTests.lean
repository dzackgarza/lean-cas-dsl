module

import CasCompiler.Read
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | liftM (m := MetaM) <| throwError "the native operation parameter did not parse"
  return ⟨stx⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | liftM (m := MetaM) <| throwError "the source operation did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `a (← nativeTerm "Rat")
  let session ← session.assume `b (← nativeTerm "Rat")
  let type ← session.term (← nativeTerm "Rat")
  for (source, declaration) in #[
      ("a + b", ``CasCatalogue.Algebra.NamedRings.add),
      ("a · b", ``CasCatalogue.Algebra.NamedRings.mul),
      ("a * b", ``CasCatalogue.Algebra.NamedRings.mul),
      ("-a", ``CasCatalogue.Algebra.NamedRings.neg),
      ("a ^ 2", ``CasCatalogue.Algebra.NamedRings.pow)] do
    let term ← session.read (← sourceTerm source) (some type.source) type.selections
    SourceTest.checkSelected term fun expression => do
      let bindings ← SourceTest.authoredBindings
      let scope ← get
      let applications ← SourceTest.declaredApplications scope.context scope.selections
        declaration expression
      let occurs := fun original =>
        SourceTest.visitNativeData (fun value => pure (value.equal original)) expression false
      unless !applications.isEmpty && (← occurs bindings[0]!.expression) > 0 do
        liftM (m := MetaM) <| throwError "a source scalar operation changed its declared operation or first operand"
      if source == "a + b" || source == "a · b" || source == "a * b" then
        unless (← occurs bindings[1]!.expression) > 0 do
          liftM (m := MetaM) <| throwError "a binary source operation lost its second original operand"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let rings ← parameters.namedCategory Syntax.missing "Rings" [.zero] #[]
  let ring ← parameters.term (← nativeTerm "R")
  let selected ← ring.inCategory rings.expression rings.value
  let session ← parameters.defineTerm `S selected
  let session ← session.assume `x (← nativeTerm "S")
  let session ← session.assume `y (← nativeTerm "S")
  let session ← session.assume `customAddition (← nativeTerm "Add S") .instImplicit
  let session ← session.assume `customMapCall (← nativeTerm
    "CoeFun (TypeCat.Hom (S × S) S) (fun _ => (S × S) → S)") .instImplicit
  let term ← session.read (← sourceTerm "x + y")
  SourceTest.checkSelected term fun expression => do
    let bindings ← SourceTest.authoredBindings
    let pair ← mkAppM ``Prod.mk #[bindings[2]!.expression, bindings[3]!.expression]
    let addition ← mkAppM ``CasCatalogue.Algebra.NamedRings.add #[bindings[1]!.expression]
    let function ← mkAppM ``TypeCat.Hom.hom #[addition]
    let function ← mkAppM ``TypeCat.Fun.toFun #[function]
    let expected := mkApp function pair
    SourceTest.checkOriginal #[expression, expected] fun values => do
      unless ← isDefEq values[0]! values[1]! do
        liftM (m := MetaM) <| throwError "source addition differs from its complete selected native map"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!)
        (← mkEq values[0]! values[1]!))
    let scope ← get
    let applications ← SourceTest.declaredApplications scope.context scope.selections
      ``CasCatalogue.Algebra.NamedRings.add expression
    let occurs := fun original =>
      SourceTest.visitNativeData (fun value => pure (value.equal original)) expression false
    unless !applications.isEmpty && (← occurs bindings[1]!.expression) > 0 &&
        (← occurs bindings[2]!.expression) > 0 && (← occurs bindings[3]!.expression) > 0 &&
        (← occurs bindings[4]!.expression) == 0 && (← occurs bindings[5]!.expression) == 0 do
      liftM (m := MetaM) <| throwError "a source operation changed its selected ring, operands or dictionary"
  let session ← session.defineTerm `sum term
  let session ← session.assume `S (← nativeTerm "RingCat.{0}")
  let retained ← session.read (← sourceTerm "sum")
  SourceTest.checkSelected retained fun expression => do
    let bindings ← SourceTest.authoredBindings
    unless expression == bindings[6]!.expression do
      liftM (m := MetaM) <| throwError "a source operation was reconstructed after its structure name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `A (← nativeTerm "Type")
  let parameters ← parameters.assume `first (← nativeTerm "Ring A")
  let parameters ← parameters.assume `second (← nativeTerm "Ring A")
  let rings ← parameters.namedCategory Syntax.missing "Rings" [.zero] #[]
  let first ← parameters.term (← nativeTerm "@RingCat.of A first")
  let first ← first.inCategory rings.expression rings.value
  let parameters ← parameters.defineTerm `R first
  let second ← parameters.term (← nativeTerm "@RingCat.of A second")
  let second ← second.inCategory rings.expression rings.value
  let session ← parameters.defineTerm `S second
  let session ← session.assume `x (← nativeTerm "R")
  let session ← session.assume `y (← nativeTerm "S")
  let type ← session.term (← nativeTerm "(R : Type)")
  for expected in #[none, some type.source] do
    for source in #["x + y", "x * y"] do
      let rejected ← withoutModifyingState do
        try
          discard <| session.read (← sourceTerm source) expected type.selections
          pure false
        catch error => return CasCatalogue.Exception.isSemanticAmbiguity error
      unless rejected do
        liftM (m := MetaM) <| throwError "equal carriers selected one of two independently supplied ring structures"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let session ← session.define `RFirst (← nativeTerm "R")
  let session ← session.define `RSecond (← nativeTerm "R")
  let firstRing ← session.term (← nativeTerm "RFirst")
  let secondRing ← session.term (← nativeTerm "RSecond")
  let first ← session.namedCategory Syntax.missing "Modules" [.zero, .zero] #[firstRing]
  let second ← session.namedCategory Syntax.missing "Modules" [.zero, .zero] #[secondRing]
  let session ← session.assume `raw (← nativeTerm "ModuleCat.{0} RFirst")
  let raw ← session.term (← nativeTerm "raw")
  let firstModule ← raw.inCategory first.expression first.value
  let secondModule ← raw.inCategory second.expression second.value
  let session ← session.defineTerm `MFirst firstModule
  let session ← session.defineTerm `MSecond secondModule
  let session ← session.assume `unrelatedZero
    (← nativeTerm "OfNat (raw : Type) 0") .instImplicit
  for (name, scalar, otherName, otherScalar) in #[
      ("MFirst", `RFirst, `MSecond, `RSecond),
      ("MSecond", `RSecond, `MFirst, `RFirst)] do
    let point ← session.read (← sourceTerm s!"0 in {name}")
    SourceTest.checkSelected point fun expression => do
      let bindings ← SourceTest.authoredBindings
      let some chosen ← bindings.findM? fun binding => do
          return (← binding.expression.fvarId!.getUserName) == Name.mkSimple name
        | liftM (m := MetaM) <| throwError "the nullary control lost its chosen module"
      let findNamed := fun name => bindings.findM? fun binding => do
        return (← binding.expression.fvarId!.getUserName) == name
      let some scalar ← findNamed scalar
        | liftM (m := MetaM) <| throwError "the nullary control lost its chosen scalar"
      let some other ← findNamed otherName
        | liftM (m := MetaM) <| throwError "the nullary control lost the distinct equal module"
      let some otherScalar ← findNamed otherScalar
        | liftM (m := MetaM) <| throwError "the nullary control lost the distinct equal scalar"
      let some unrelated ← findNamed `unrelatedZero
        | liftM (m := MetaM) <| throwError "the nullary control lost its unrelated host instance"
      let some original := (← SourceReadM.selection? expression).bind (·.pointOrigin)
        | liftM (m := MetaM) <| throwError "the nullary numeral discarded its actual native point"
      let application := original.point.headBeta.consumeMData
      unless application.getAppFn.isConstOf ``CasCatalogue.Modules.Operations.zero &&
          application.getAppArgs.size == 2 do
        liftM (m := MetaM) <| throwError "the nullary numeral replaced its published operation family"
      let actualObject ← liftM (m := MetaM) <| withConfig (fun config => { config with zetaDelta := false }) <|
        withTransparency .all <| whnf application.getAppArgs[1]!
      let scope ← get
      let occurs := fun source original =>
        SourceTest.visitNativeData (fun value => pure (value.equal original)) source false
      unless (← SourceTest.originatesAt scope.context scope.selections
          application.getAppArgs[0]! scalar.expression false) &&
          (← SourceTest.originatesAt scope.context scope.selections actualObject chosen.expression false) &&
          (← occurs original.point other.expression) == 0 &&
          (← occurs original.point otherScalar.expression) == 0 &&
          (← occurs expression unrelated.expression) == 0 do
        liftM (m := MetaM) <| throwError "the nullary numeral replaced an exact selected input or dictionary"
      let expectedPoint ← mkAppM ``CasCatalogue.Modules.Operations.zero
        #[scalar.expression, chosen.expression]
      SourceTest.checkOriginal #[expression, expectedPoint, original.domain, original.target] fun values => do
        let type ← whnfR (← inferType values[1]!)
        unless type.isAppOfArity ``Quiver.Hom 4 &&
            (← isDefEq values[2]! type.getAppArgs[2]!) &&
            (← isDefEq values[3]! type.getAppArgs[3]!) do
          liftM (m := MetaM) <| throwError "the nullary numeral changed its complete native point domain"
        let defaultPoint ← mkAppOptM ``default #[some type.getAppArgs[2]!, none]
        let expected := mkApp (← sourceSetFunction values[1]!) defaultPoint
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! expected))
  let rawType ← session.term (← nativeTerm "(raw : Type)")
  for (text, expected) in #[
      ("0", some rawType.source), ("2 in MFirst", none), ("2 in MSecond", none)] do
    let failure : Option Exception ← withoutModifyingState do
      try
        discard <| session.read (← sourceTerm text) expected rawType.selections
        pure none
      catch error => pure (some error)
    let some failure := failure
      | liftM (m := MetaM) <| throwError "a nullary numeral borrowed a missing owner or an undeclared nonzero meaning"
    unless failure.toMessageData.hasTag (· == `CasCompiler.sourceNumeral.noAdmittedPoint) do throw failure



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "CommRingCat.{0}")
  let category ← session.namedCategory Syntax.missing "CommutativeRings" [.zero] #[]
  let original ← session.term (← nativeTerm "R")
  let session ← session.defineTerm `S
    (← original.inCategory category.expression category.value)
  let point ← session.read (← sourceTerm "1 in S")
  let native ← session.term (← nativeTerm
    "TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Algebra.NamedRings.ringNumeral (CasCatalogue.Algebra.Algebras.commutativeRingsRings.toFunctor.obj S) 1)) default")
  SourceTest.checkSelected point fun expression => do
    let scope ← get
    let selected ← SourceTest.visitNativeData (fun value => do
      let some retained ← SourceReadM.selection? value | return false
      return retained.reference.any fun
        | .numeral entry => entry.id == "num.rings"
        | _ => false) expression
    let replaced ← SourceTest.visitNativeData (fun value => do
      let some retained ← SourceReadM.selection? value | return false
      return retained.reference.any fun
        | .operation entry => entry.id == "op.monoids.one"
        | _ => false) expression
    unless selected > 0 && replaced == 0 do
      liftM (m := MetaM) <| throwError "the numeric token replaced its selected numeral with an inherited unit"
    let expected ← native.source.inContext scope.context
    SourceTest.checkOriginal #[expression, expected] fun values => do
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!)
        (← mkEq values[0]! values[1]!))



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `M (← nativeTerm "MonCat.{0}")
  let #[category] := (← semanticState).categories.filter (·.id == CategoryId.monoids)
    | liftM (m := MetaM) <| throwError "the independently registered monoid category is not unique"
  let bundle ← session.constant Syntax.missing category.declaration [.zero]
  let original ← session.term (← nativeTerm "M")
  let session ← session.defineTerm `S
    (← original.inCategory category.expression bundle)
  let point ← session.read (← sourceTerm "1 in S")
  SourceTest.checkSelected point fun expression => do
    let bindings ← SourceTest.authoredBindings
    let some origin := (← SourceReadM.selection? expression).bind (·.pointOrigin)
      | liftM (m := MetaM) <| throwError "the monoid unit lost its original native point"
    let application := origin.point.headBeta.consumeMData
    unless application.getAppFn.isConstOf ``CasCatalogue.Algebra.MonoidOperations.one &&
        application.getAppArgs.size == 1 do
      liftM (m := MetaM) <| throwError "the monoid unit changed its published nullary family"
    let selected ← liftM (m := MetaM) <| withConfig (fun config => { config with zetaDelta := false }) <|
      withTransparency .all <| whnf application.getAppArgs[0]!
    let scope ← get
    unless ← SourceTest.originatesAt scope.context scope.selections selected bindings[1]!.expression false do
      liftM (m := MetaM) <| throwError "the monoid unit changed its original selected object"
    let expectedPoint ← mkAppM ``CasCatalogue.Algebra.MonoidOperations.one
      #[bindings[1]!.expression]
    SourceTest.checkOriginal #[expression, expectedPoint, origin.domain, origin.target] fun values => do
      let type ← whnfR (← inferType values[1]!)
      unless type.isAppOfArity ``Quiver.Hom 4 &&
          (← isDefEq values[2]! type.getAppArgs[2]!) &&
          (← isDefEq values[3]! type.getAppArgs[3]!) do
        liftM (m := MetaM) <| throwError "the monoid unit changed its complete terminal source"
      let argument ← mkAppOptM ``default #[some type.getAppArgs[2]!, none]
      let expected := mkApp (← sourceSetFunction values[1]!) argument
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl values[0]!) (← mkEq values[0]! expected))
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| session.read (← sourceTerm "2 in S")
      pure none
    catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "the monoid unit invented a general numeral family"
  unless failure.toMessageData.hasTag (· == `CasCompiler.sourceNumeral.noAdmittedPoint) do throw failure




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let point ← empty.read (← sourceTerm "7 in ℕ")
  let originalPoint ← empty.elaborateScoped Syntax.missing do
    let expression ← empty.readTerm point
    let some original := (← SourceReadM.selection? expression).bind (·.pointOrigin)
      | liftM (m := MetaM) <| throwError "the projected-point control lost its original numeral map"
    return original.point
  let session ← empty.defineTerm `firstPoint originalPoint
  let firstId := session.context.entries.back!.id
  let session ← session.defineTerm `secondPoint originalPoint
  let secondId := session.context.entries.back!.id
  discard <| session.elaborateJudgementsScoped Syntax.missing do
    let expression ← session.readTerm point
    let some selected ← SourceReadM.selection? expression
      | liftM (m := MetaM) <| throwError "the projected-point control lost its selected numeral"
    let some original := selected.pointOrigin
      | liftM (m := MetaM) <| throwError "the projected-point control lost its original numeral map"
    let scope ← get
    let some firstBinding := scope.context.bindings.find? (·.id == firstId)
      | liftM (m := MetaM) <| throwError "the projected-point control lost its first original point"
    let some secondBinding := scope.context.bindings.find? (·.id == secondId)
      | liftM (m := MetaM) <| throwError "the projected-point control lost its second original point"
    let firstPoint := firstBinding.expression
    let secondPoint := secondBinding.expression
    unless firstPoint != secondPoint && (← isDefEq firstPoint secondPoint) do
      liftM (m := MetaM) <| throwError "the projected-point control needs distinct equal native arrows"
    let first ← SourceReadM.select (← retainSourcePoint firstPoint { selected with value := expression })
    let second ← SourceReadM.select (← retainSourcePoint secondPoint { selected with value := expression })
    let pair ← retainSourceConstructor (← mkAppM ``Prod.mk #[first, second])
    let firstKernel := mkProj ``Prod 0 pair
    let secondKernel := mkProj ``Prod 1 pair
    let firstFunction ← mkAppM ``Prod.fst #[pair]
    let secondFunction ← mkAppM ``Prod.snd #[pair]
    for (projection, expectedPoint, otherPoint) in #[
        (firstKernel, firstPoint, secondPoint),
        (secondKernel, secondPoint, firstPoint),
        (firstFunction, firstPoint, secondPoint),
        (secondFunction, secondPoint, firstPoint)] do
      let some projected ← retainSourceProjection? projection
        | liftM (m := MetaM) <| throwError "the selected native constructor field lost its point origin"
      let some retained := (← SourceReadM.selection? projected.value).bind (·.pointOrigin)
        | liftM (m := MetaM) <| throwError "the selected native constructor field lost its point origin"
      unless retained.point == expectedPoint && retained.point != otherPoint do
        liftM (m := MetaM) <| throwError "the native projection selected another point or changed its endpoints"
      SourceTest.checkOriginal #[retained.domain, original.domain, retained.target, original.target]
        fun values => do
          unless (← isDefEq values[0]! values[1]!) && (← isDefEq values[2]! values[3]!) do
            liftM (m := MetaM) <| throwError "the native projection selected another point or changed its endpoints"
      check projected.value

    let mixed ← retainSourceConstructor (← mkAppM ``Prod.mk #[first, mkNatLit 7])
    let unrelated := mkProj ``Prod 1 mixed
    if (← retainSourceProjection? unrelated).isSome then
      liftM (m := MetaM) <| throwError "a native projection borrowed its sibling's point origin"
    SourceReadM.withBinder `opaquePair (← inferType pair) none .default
      (fun _ result => pure result) fun opaquePair => do
        if (← retainSourceProjection? (mkProj ``Prod 0 opaquePair)).isSome then
          liftM (m := MetaM) <| throwError "point provenance was inferred without an actual source constructor"
    return #[]





run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let state ← semanticState
  let source := CasCatalogue.Algebra.Algebras.AlgebrasExpr
  let target := CategoryExpr.atom CategoryId.rings
  let refs : Array EdgeRef := #[.functor FunctorId.algebrasForget,
    .functor FunctorId.commutativeRingsRings]
  let some steps := state.routeEdges? source target refs
    | liftM (m := MetaM) <| throwError "the original polynomial operation lost its declared route"
  let route : Route := { source, target, steps }
  let registered ← selectCategory state "Algebras"
  let info ← getConstInfo registered.declaration
  let category ← empty.categoryFamily Syntax.missing "Algebras"
    (info.levelParams.map fun _ => Level.zero)
  unless category.expression.syntacticEq source do
    liftM (m := MetaM) <| throwError "the polynomial operation changed its complete selected category"
  let #[operation] := (state.operationBindings target "+").filter (·.id == "op.rings.add")
    | liftM (m := MetaM) <| throwError "the polynomial operation lost its exact source declaration"
  SourceTest.checkSelected category.family fun family => do
    let scope ← get
    let selectedCategories := scope.selections.toArray.filterMap fun (_, selected) =>
      match selected.reference with
      | some (.category _) => some selected
      | _ => none
    let #[selectedCategory] := selectedCategories
      | liftM (m := MetaM) <| throwError "the polynomial operation has a bare inferred algebra category"
    unless selectedCategory.value.equal family &&
        SourceSelection.exactlyMatches Expr.equal selectedCategory
          { selectedCategory with reference := some (.category registered) } &&
        registered.id.raw == "cat.algebras" &&
        registered.declaration == ``CasCatalogue.Algebra.Algebras.algebrasCategory do
      liftM (m := MetaM) <| throwError "the polynomial operation has a bare inferred algebra category"
    let native ← nativeOwnedFamily state source family route
      ``CasCatalogue.Algebra.NamedRings.add (fun infos => some (infos.size - 1))
      (some (.operation operation))
    unless SourceSelection.exactlyMatches Expr.equal
        { value := native.value, reference := native.reference }
        { value := native.value, reference := some (.operation operation) } do
      liftM (m := MetaM) <| throwError "the polynomial operation lost its exact source declaration"
    liftM (m := MetaM) <| lambdaTelescope native.value fun parameters application => do
      unless application.getAppFn.isConstOf ``CasCatalogue.Algebra.NamedRings.add do
        liftM (m := MetaM) <| throwError "the polynomial operation changed its selected addition"
      let some image := application.getAppArgs.back?
        | liftM (m := MetaM) <| throwError "the polynomial operation lost its original routed object"
      unless image.isAppOfArity ``CategoryTheory.Functor.obj 6 do
        liftM (m := MetaM) <| throwError "the polynomial operation does not retain its actual native object projection"
      let arguments := image.getAppArgs
      unless arguments.back! == parameters[native.objectIndex]! do
        liftM (m := MetaM) <| throwError "the polynomial operation replaced its rigid original object"
      let category := mkApp family parameters[0]!
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
      unless arguments[0]! == carrier do
        liftM (m := MetaM) <| throwError "the polynomial operation lost its selected algebra category parameter"
      let composite := arguments[4]!
      unless composite.isAppOfArity ``CategoryTheory.Functor.comp 8 &&
          composite.getAppArgs[0]! == carrier do
        liftM (m := MetaM) <| throwError "the polynomial operation changed the selected composition source"
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[composite]
      let original ← mkAppM ``Prefunctor.obj #[prefunctor, parameters[native.objectIndex]!]
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl image) (← mkEq image original))
