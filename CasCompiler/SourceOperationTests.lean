module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native operation parameter did not parse"
  return ⟨stx⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source operation did not parse"
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
    let term ← session.read (← sourceTerm source) (some type.source)
    term.source.withOpen fun bindings expression => do
      unless expression.containsConst (· == declaration) &&
          expression.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a source scalar operation changed its declared operation or first operand"
      if source == "a + b" || source == "a · b" || source == "a * b" then
        unless expression.containsFVar bindings[1]!.expression.fvarId! do
          throwError "a binary source operation lost its second original operand"

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
  term.source.withOpen fun bindings expression => do
    let pair ← mkAppM ``Prod.mk #[bindings[2]!.expression, bindings[3]!.expression]
    let addition ← mkAppM ``CasCatalogue.Algebra.NamedRings.add #[bindings[1]!.expression]
    let function ← mkAppM ``TypeCat.Hom.hom #[addition]
    let function ← mkAppM ``TypeCat.Fun.toFun #[function]
    let expected := mkApp function pair
    unless ← isDefEq expression expected do
      throwError "source addition differs from its complete selected native map"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
    unless expression.containsConst (· == ``CasCatalogue.Algebra.NamedRings.add) &&
        expression.containsFVar bindings[1]!.expression.fvarId! &&
        expression.containsFVar bindings[2]!.expression.fvarId! &&
        expression.containsFVar bindings[3]!.expression.fvarId! &&
        !expression.containsFVar bindings[4]!.expression.fvarId! &&
        !expression.containsFVar bindings[5]!.expression.fvarId! do
      throwError "a source operation changed its selected ring, operands or dictionary"
  let session ← session.defineTerm `sum term
  let session ← session.assume `S (← nativeTerm "RingCat.{0}")
  let retained ← session.read (← sourceTerm "sum")
  retained.source.withOpen fun bindings expression => do
    unless expression == bindings[6]!.expression do
      throwError "a source operation was reconstructed after its structure name was shadowed"

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
          discard <| session.read (← sourceTerm source) expected
          pure false
        catch error =>
          let message ← error.toMessageData.toString
          return (message.splitOn "selected common refinement").length > 1
      unless rejected do
        throwError "equal carriers selected one of two independently supplied ring structures"

-- A nullary numeral keeps the exact category parameter and original object even
-- when independently bound inputs have equal definitions. No host OfNat supplies it.
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
    point.source.withOpen fun bindings expression => do
      let some chosen ← bindings.findM? fun binding => do
          return (← binding.expression.fvarId!.getUserName) == Name.mkSimple name
        | throwError "the nullary control lost its chosen module"
      let findNamed := fun name => bindings.findM? fun binding => do
        return (← binding.expression.fvarId!.getUserName) == name
      let some scalar ← findNamed scalar
        | throwError "the nullary control lost its chosen scalar"
      let some other ← findNamed otherName
        | throwError "the nullary control lost the distinct equal module"
      let some otherScalar ← findNamed otherScalar
        | throwError "the nullary control lost the distinct equal scalar"
      let some unrelated ← findNamed `unrelatedZero
        | throwError "the nullary control lost its unrelated host instance"
      let some original ← sourcePointOrigin? expression
        | throwError "the nullary numeral discarded its actual native point"
      let application := original.point.headBeta.consumeMData
      unless application.getAppFn.isConstOf ``CasCatalogue.Modules.Operations.zero &&
          application.getAppArgs.size == 2 do
        throwError "the nullary numeral replaced its published operation family"
      let actualObject ← withConfig (fun config => { config with zetaDelta := false }) <|
        withTransparency .all <| whnf application.getAppArgs[1]!
      unless application.getAppArgs[0]! == scalar.expression &&
          actualObject == chosen.expression &&
          !original.point.containsFVar other.expression.fvarId! &&
          !original.point.containsFVar otherScalar.expression.fvarId! &&
          !expression.containsFVar unrelated.expression.fvarId! do
        throwError "the nullary numeral replaced an exact selected input or dictionary"
      let expectedPoint ← mkAppM ``CasCatalogue.Modules.Operations.zero
        #[scalar.expression, chosen.expression]
      let type ← whnfR (← inferType expectedPoint)
      unless type.isAppOfArity ``Quiver.Hom 4 &&
          (← isDefEq original.domain type.getAppArgs[2]!) &&
          (← isDefEq original.target type.getAppArgs[3]!) do
        throwError "the nullary numeral changed its complete native point domain"
      let defaultPoint ← mkAppOptM ``default #[some type.getAppArgs[2]!, none]
      let expected := mkApp (← sourceSetFunction expectedPoint) defaultPoint
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
  let rawType ← session.term (← nativeTerm "(raw : Type)")
  for (text, expected) in #[
      ("0", some rawType.source), ("2 in MFirst", none), ("2 in MSecond", none)] do
    let failure : Option Exception ← withoutModifyingState do
      try
        discard <| session.read (← sourceTerm text) expected
        pure none
      catch error => pure (some error)
    let some failure := failure
      | throwError "a nullary numeral borrowed a missing owner or an undeclared nonzero meaning"
    unless (← failure.toMessageData.toString).startsWith
        "no declared source point numeral was admitted in the supplied domain" do throw failure

-- Established numeric syntax keeps the selected registered numeral before the
-- same token's inherited monoid unit. No point-value comparison creates priority.
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
  point.source.withOpen fun bindings expression => do
    let selected := expression.find? fun term =>
      match term with
      | .mdata data _ => data.getName `CasCompiler.source.kind == ``NumeralEntry &&
          data.getString `CasCompiler.source.id == "num.rings"
      | _ => false
    let replaced := expression.find? fun term =>
      match term with
      | .mdata data _ => data.getName `CasCompiler.source.kind == ``OperationEntry &&
          data.getString `CasCompiler.source.id == "op.monoids.one"
      | _ => false
    unless selected.isSome && replaced.isNone do
      throwError "the numeric token replaced its selected numeral with an inherited unit"
    let expected ← native.source.inContext (← ContextTelescope.capture bindings)
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))

-- The other existing terminal presentation is Fin(1), with its own native Unique
-- dictionary. A monoid has its published unit, without a general numeral family.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `M (← nativeTerm "MonCat.{0}")
  let #[category] := (← semanticState).categories.filter (·.id == CategoryId.monoids)
    | throwError "the independently registered monoid category is not unique"
  let bundle ← session.constant Syntax.missing category.declaration [.zero]
  let original ← session.term (← nativeTerm "M")
  let session ← session.defineTerm `S
    (← original.inCategory category.expression bundle)
  let point ← session.read (← sourceTerm "1 in S")
  point.source.withOpen fun bindings expression => do
    let some origin ← sourcePointOrigin? expression
      | throwError "the monoid unit lost its original native point"
    let application := origin.point.headBeta.consumeMData
    unless application.getAppFn.isConstOf ``CasCatalogue.Algebra.MonoidOperations.one &&
        application.getAppArgs.size == 1 do
      throwError "the monoid unit changed its published nullary family"
    let selected ← withConfig (fun config => { config with zetaDelta := false }) <|
      withTransparency .all <| whnf application.getAppArgs[0]!
    unless selected == bindings[1]!.expression do
      throwError "the monoid unit changed its original selected object"
    let expectedPoint ← mkAppM ``CasCatalogue.Algebra.MonoidOperations.one
      #[bindings[1]!.expression]
    let type ← whnfR (← inferType expectedPoint)
    unless type.isAppOfArity ``Quiver.Hom 4 &&
        (← isDefEq origin.domain type.getAppArgs[2]!) &&
        (← isDefEq origin.target type.getAppArgs[3]!) do
      throwError "the monoid unit changed its complete terminal source"
    let argument ← mkAppOptM ``default #[some type.getAppArgs[2]!, none]
    let expected := mkApp (← sourceSetFunction expectedPoint) argument
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| session.read (← sourceTerm "2 in S")
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "the monoid unit invented a general numeral family"
  unless (← failure.toMessageData.toString).startsWith
      "no declared source point numeral was admitted in the supplied domain" do throw failure


-- A native projection retains only its own constructor component's original point.
-- The two equal native arrows remain distinct source occurrences.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let point ← empty.read (← sourceTerm "7 in ℕ")
  point.source.withOpen fun _ expression => do
    let some original ← sourcePointOrigin? expression
      | throwError "the projected-point control lost its original numeral map"
    let pointType ← inferType original.point
    withLetDecl `firstPoint pointType original.point fun firstPoint => do
      withLetDecl `secondPoint pointType original.point fun secondPoint => do
        unless firstPoint != secondPoint && (← isDefEq firstPoint secondPoint) do
          throwError "the projected-point control needs distinct equal native arrows"
        let first ← retainSourcePoint firstPoint expression
        let second ← retainSourcePoint secondPoint expression
        let pair ← mkAppM ``Prod.mk #[first, second]
        let firstKernel := mkProj ``Prod 0 pair
        let secondKernel := mkProj ``Prod 1 pair
        let firstFunction ← mkAppM ``Prod.fst #[pair]
        let secondFunction ← mkAppM ``Prod.snd #[pair]
        for (selected, expectedPoint, otherPoint) in #[
            (firstKernel, firstPoint, secondPoint),
            (secondKernel, secondPoint, firstPoint),
            (firstFunction, firstPoint, secondPoint),
            (secondFunction, secondPoint, firstPoint)] do
          let some retained ← sourcePointOrigin? selected
            | throwError "the selected native constructor field lost its point origin"
          unless retained.point == expectedPoint && retained.point != otherPoint &&
              (← isDefEq retained.domain original.domain) &&
              (← isDefEq retained.target original.target) do
            throwError "the native projection selected another point or changed its endpoints"
          check selected
        -- The unrelated component is the same native number, with no point authority.
        let mixed ← mkAppM ``Prod.mk #[first, mkNatLit 7]
        let unrelated := mkProj ``Prod 1 mixed
        if (← sourcePointOrigin? unrelated).isSome then
          throwError "a native projection borrowed its sibling's point origin"
        withLocalDeclD `opaquePair (← inferType pair) fun opaquePair => do
          if (← sourcePointOrigin? (mkProj ``Prod 0 opaquePair)).isSome then
            throwError "point provenance was inferred without an actual source constructor"

-- The polynomial question's algebra-to-ring operation is formed over a rigid selected
-- algebra category. Its actual routed object argument retains that category selection,
-- the two declared functors and the original object at their native positions. Inference
-- of convertible category projections must not replace that source selection.
run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  let source := CasCatalogue.Algebra.Algebras.AlgebrasExpr
  let target := CategoryExpr.atom CategoryId.rings
  let refs : Array EdgeRef := #[.functor FunctorId.algebrasForget,
    .functor FunctorId.commutativeRingsRings]
  let some steps := state.routeEdges? source target refs
    | throwError "the original polynomial operation lost its declared route"
  let route : Route := { source, target, steps }
  let family ← nativeCategoryFamily state source fun _ => pure .zero
  let native ← nativeOwnedFamily state source family route
    ``CasCatalogue.Algebra.NamedRings.add (fun infos => some (infos.size - 1))
    (some (``OperationEntry, "op.rings.add"))
  lambdaTelescope native.value fun parameters body => do
    let .mdata data application := body
      | throwError "the polynomial operation lost its exact source declaration"
    unless data.getString `CasCompiler.source.id == "op.rings.add" &&
        application.getAppFn.isConstOf ``CasCatalogue.Algebra.NamedRings.add do
      throwError "the polynomial operation changed its selected addition"
    let some image := application.getAppArgs.back?
      | throwError "the polynomial operation lost its original routed object"
    unless image.isAppOfArity ``CategoryTheory.Functor.obj 6 do
      throwError "the polynomial operation does not retain its actual native object projection"
    let arguments := image.getAppArgs
    unless arguments.back! == parameters[native.objectIndex]! do
      throwError "the polynomial operation replaced its rigid original object"
    let category := mkApp family parameters[0]!
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
    unless arguments[0]! == carrier do
      throwError "the polynomial operation lost its selected algebra category parameter"
    let composite := arguments[4]!
    unless composite.isAppOfArity ``CategoryTheory.Functor.comp 8 &&
        composite.getAppArgs[0]! == carrier do
      throwError "the polynomial operation changed the selected composition source"
    unless (carrier.find? (fun term => match term with
      | .mdata data _ => data.getName `CasCompiler.source.kind == ``NamedCategoryEntry &&
          data.getString `CasCompiler.source.id == "cat.algebras" &&
          data.getName `CasCompiler.source.declaration ==
            ``CasCatalogue.Algebra.Algebras.algebrasCategory
      | _ => false)).isSome do
      throwError "the polynomial operation has a bare inferred algebra category"
    let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[composite]
    let original ← mkAppM ``Prefunctor.obj #[prefunctor, parameters[native.objectIndex]!]
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl image) (← mkEq image original))
