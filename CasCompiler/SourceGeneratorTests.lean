module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Parse
import CasCompiler.SourceRing
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Parse
meta import CasCompiler.SourceRing
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let file ← SourceFile.parse "source-explicit-generators.cas"
      "let X := F9x\nlet Y := F9y\nlet Xalias := X\n\
       let GX := generator(X)\nlet GY := generator(Y)\nlet GA := generator(Xalias)\n"
    let mut session ← SourceSession.empty identities
    let expected := #[
      (`X, "obj.sets.f9_x", ``CasCatalogue.Algebra.PolynomialPresentations.firstGenerator),
      (`Y, "obj.sets.f9_y", ``CasCatalogue.Algebra.PolynomialPresentations.secondGenerator),
      (`Xalias, "obj.sets.f9_x", ``CasCatalogue.Algebra.PolynomialPresentations.firstGenerator)]
    for item in file.items, index in [:file.items.size] do
      let `(cas_item| $statement:cas_stmt) := item
        | throwError "the explicit generator control changed its parsed category"
      let .definition next value ← file.withContext (session.readStatement statement)
        | throwError "the explicit generator control is not a source definition"
      session := next
      if index < 3 then continue
      let some (name, objectId, declaration) := expected[index - 3]?
        | throwError "the generator control acquired an unexpected source statement"
      checkSelected value fun expression => do
        let scope ← get
        let some selected ← scope.context.bindings.findM? fun binding =>
            return (← binding.expression.fvarId!.getUserName) == name
          | liftM (m := TermElabM) <| throwError "the explicit generator lost its original source object"
        unless (← inferType expression) == selected.expression do
          liftM (m := TermElabM) <| throwError "the generator replaced its exact source object by another carrier"
        let some selection ← SourceReadM.selection? expression
          | liftM (m := TermElabM) <| throwError "the explicit generator lost its selected native binding"
        let some (.generator entry) := selection.reference
          | liftM (m := TermElabM) <| throwError "the explicit generator lost its selected catalogue reference"
        let #[originalEntry] := (← semanticState).objects.filter (·.id.raw == objectId)
          | liftM (m := TermElabM) <| throwError "the explicit generator lost its independently registered owner"
        unless entry.id.raw == objectId && entry.generator == some declaration &&
            (SelectedSourceReference.generator entry).exactlyMatches (.generator originalEntry) do
          liftM (m := TermElabM) <| throwError "the explicit generator changed its original registered declaration"
        checkOriginal #[expression] fun native => do
          unless native[0]!.containsConst (· == declaration) do
            throwError "the explicit generator changed its original registered declaration"
        let some ordinal := scope.context.bindings.findIdx? (·.id == selected.id)
          | liftM (m := TermElabM) <| throwError "the generator's source object is outside its complete telescope"
        unless (← contextDependencies scope.context.bindings (← inferType expression)).contains ordinal do
          liftM (m := TermElabM) <| throwError "the generator dropped its actual source-binding dependency"
  finally setEnv original




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let native : String → TermElabM Term := fun text => do
      let .ok parsed := Parser.runParserCategory (← getEnv) `term text
        | throwError "the coefficient control did not parse as native source"
      pure (⟨parsed⟩ : Term)
    let source : String → TermElabM (TSyntax `cas_term) := fun text => do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
        | throwError "the coefficient control did not parse as public source"
      pure (⟨parsed⟩ : TSyntax `cas_term)
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let empty ← SourceSession.empty identities
    let session ← empty.assume `R (← native "CommRingCat.{0}")
    let session ← session.define `RFirst (← native "R")
    let session ← session.define `RSecond (← native "R")
    for (text, chosenName, otherName) in #[
        ("x in RFirst[x]", `RFirst, `RSecond),
        ("x in RSecond[x]", `RSecond, `RFirst)] do
      let term ← session.read (← source text)
      checkSelected term fun expression => do
        let scope ← get
        let authored ← authoredBindings
        let some chosen ← authored.findM? fun binding =>
            return (← binding.expression.fvarId!.getUserName) == chosenName
          | liftM (m := TermElabM) <| throwError "the generator lost its chosen authored coefficient object"
        let some other ← authored.findM? fun binding =>
            return (← binding.expression.fvarId!.getUserName) == otherName
          | liftM (m := TermElabM) <| throwError "the generator control lost its independently equal coefficient object"
        unless chosen.id != other.id && !chosen.expression.equal other.expression do
          liftM (m := TermElabM) <| throwError "the generator control collapsed its two source identities"
        checkOriginal #[chosen.expression, other.expression] fun originals => do
          unless ← isDefEq originals[0]! originals[1]! do
            throwError "the generator control no longer has equal original coefficient objects"
        let #[expected] := (← semanticState).objects.filter
            (·.id.raw == "obj.sets.polynomials")
          | liftM (m := TermElabM) <| throwError "the independent polynomial object row is absent"
        let declaration := ``CasCatalogue.Algebra.Polynomials.generator
        unless expected.generator == some declaration do
          liftM (m := TermElabM) <| throwError "the independent polynomial generator changed"
        let count ← visitNativeData (fun value => do
          let some selected ← SourceReadM.selection? value | return false
          let some (.generator actual) := selected.reference | return false
          unless (SelectedSourceReference.generator actual).exactlyMatches (.generator expected) do
            liftM (m := TermElabM) <| throwError "the polynomial variable chose another registered generator"
          let some point ← sourceApplication? declaration selected
            | liftM (m := TermElabM) <| throwError "the polynomial variable lost its explicitly retained application"
          unless point.isAppOfArity declaration 1 do
            liftM (m := TermElabM) <| throwError "the polynomial generator changed its complete parameter table"
          let coefficient := point.getAppArgs[0]!
          unless ← originatesAt scope.context scope.selections
              coefficient chosen.expression false do
            liftM (m := TermElabM) <| throwError "the polynomial generator replaced its chosen coefficient binding"
          unless (← visitNativeData (fun input => pure (input.equal other.expression))
              coefficient false) == 0 do
            liftM (m := TermElabM) <| throwError "the polynomial generator acquired the independently equal coefficient binding"
          check point
          if point.hasMVar || point.hasLevelMVar then
            liftM (m := TermElabM) <| throwError "the polynomial generator retained an unresolved parameter"
          let expectedPoint ← mkAppM declaration #[chosen.expression]
          checkOriginal #[point, expectedPoint] fun originals => do
            checkWithKernel (← mkExpectedTypeHint (← mkEqRefl originals[0]!)
              (← mkEq originals[0]! originals[1]!))
          return true) expression
        unless count > 0 do
          liftM (m := TermElabM) <| throwError "the public polynomial variable lost its selected generator"
  finally setEnv original





run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let empty ← SourceSession.empty identities
    discard <| empty.elaborateScoped Syntax.missing do
      let state ← semanticState
      let #[named] := state.objects.filter (·.id.raw == "obj.sets.f9_x")
        | liftM (m := TermElabM) <| throwError "the independent named F9 row is absent"
      let #[generic] := state.objects.filter (·.id.raw == "obj.sets.polynomial_quotient")
        | liftM (m := TermElabM) <| throwError "the independent generic quotient row is absent"
      let some namedDeclaration := named.generator
        | liftM (m := TermElabM) <| throwError "the named F9 row lost its generator"
      let some genericDeclaration := generic.generator
        | liftM (m := TermElabM) <| throwError "the generic quotient row lost its generator"
      unless namedDeclaration == ``CasCatalogue.Algebra.PolynomialPresentations.firstGenerator &&
          genericDeclaration == ``CasCatalogue.Algebra.PolynomialPresentations.generator do
        liftM (m := TermElabM) <| throwError "the independent generator pair changed its declarations"
      let .defnInfo info ← getConstInfo namedDeclaration
        | liftM (m := TermElabM) <| throwError "the published named generator lost its checked definition"
      let namedPoint ← mkConstWithFreshMVarLevels namedDeclaration
      let genericPoint := info.value
      unless genericPoint.isAppOfArity genericDeclaration 2 do
        liftM (m := TermElabM) <| throwError "the published F9 generator no longer retains the generic quotient application"
      check namedPoint
      check genericPoint
      let namedType ← whnfR (← inferType namedPoint)
      let genericType ← whnfR (← inferType genericPoint)
      unless namedType.isAppOfArity ``Quiver.Hom 4 &&
          genericType.isAppOfArity ``Quiver.Hom 4 do
        liftM (m := TermElabM) <| throwError "the original generators lost their complete morphism boundaries"
      unless ← liftM (m := MetaM) <| withoutModifyingState <| isDefEq namedType genericType do
        liftM (m := TermElabM) <| throwError "the original generator pair no longer has the same native boundary"
      let target := genericType.getAppArgs[3]!
      unless target.isAppOfArity generic.declaration 2 &&
          target.getAppArgs.size == genericPoint.getAppArgs.size &&
          (target.getAppArgs.zip genericPoint.getAppArgs).all
            (fun (actual, original) => actual.equal original) do
        liftM (m := TermElabM) <| throwError "the quotient target lost its complete authored coefficient and polynomial arguments"
      for parameter in genericPoint.getAppArgs do checkWithKernel parameter
      checkWithKernel target
      let carrier ← liftM (m := MetaM) <|
        withLetDecl `originalQuotient (← inferType target) target fun value =>
          mkLetFVars #[value] value (usedLetOnly := false) (generalizeNondepLet := false)
      let .letE _ _ retainedTarget body _ := carrier
        | liftM (m := TermElabM) <| throwError "the native ambiguity control lost its unselected lexical let"
      unless retainedTarget.equal target && body.equal (mkBVar 0) do
        liftM (m := TermElabM) <| throwError "the native ambiguity control changed its complete original target"
      checkWithKernel carrier
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl carrier) (← mkEq carrier target))
      let (domain, selected) ← registeredSourceDomain carrier
      unless domain.equal carrier && selected.isEmpty &&
          (← SourceReadM.selection? carrier).isNone do
        liftM (m := TermElabM) <| throwError "the native ambiguity control unexpectedly retained a named object choice"
      let failure : Option Exception ← try
          discard <| sourceGeneratorAt? carrier none
          pure none
        catch error => pure (some error)
      let some failure := failure
        | liftM (m := TermElabM) <| throwError "the unselected quotient carrier silently selected a registered generator"
      unless CasCatalogue.Exception.isSemanticAmbiguity failure do
        throw failure
      return mkConst ``True.intro
  finally setEnv original
