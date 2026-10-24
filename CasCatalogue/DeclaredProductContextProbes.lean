module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- The source variable belongs to the selected regular module; the declared
tuple coordinate supplies its own complete scalar product. Both signs must
retain that product, rather than the source module's additive monoid operation.
The expected whole map is the already formalized selected kernel inclusion. -/
run_elab do
  let parse (source : String) : TermElabM Syntax := do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term source
      | throwError "the declared product fixture did not parse"
    return term
  let mut scope : Scope := {}
  for (name, source) in #[
      (`Q, "ℚ in CommutativeRings"),
      (`Qring, "view Q along «fun.commutative_rings.ring»()"),
      (`scalarModule, "RegularModule(Qring)"),
      (`X, "DegeneratePlane()"),
      (`sourceModule, "view X along «fun.bilin_module.forget»(ℚ, ℚ)")] do
    scope := scope.insert name (← parse source)
  let sourceSyntax ← parse "scalarModule"
  let targetSyntax ← parse "sourceModule"
  let components ← #["2*t", "-2*t"].mapM parse
  let trace ← Trace.new
  (show M Unit from do
    let source ← carrierObject (← eval scope sourceSyntax)
    let target ← carrierObject (← eval scope targetSyntax)
    let genericPoint ← identityAt source
    let (point, coordinate) ← withReader (fun context =>
        { context with stage := some source, bound := [(`t, .element genericPoint source)] }) do
      let some (count, coordinate) ← finiteFunctionContext target
        | throwError "the selected target lost its declared finite coordinates"
      unless count == components.size do throwError "the original tuple arity changed"
      let values ← components.mapM fun termSyntax => do
        unless termSyntax.getKind == ``casTimes do throwError "the original product syntax changed"
        let operand ← eval scope termSyntax[2] none (some coordinate)
        let value ← juxtaposeReading scope termSyntax[0] operand (some coordinate)
        let .element point actualTarget := value
          | throwError "the product lost its generalized point"
        let some (actualSource, actualEndpoint) := homEnds? (← inferType point)
          | throwError "the product lost its complete Hom"
        unless (← isDefEq actualSource (← semanticObject source)) &&
            (← isDefEq actualEndpoint (← semanticObject actualTarget)) do
          throwError "the product changed its original source or selected endpoint"
        return value
      let .element point _ ← declaredResult (← tupleOf values coordinate) target
        | throwError "the original tuple lost its whole map"
      return (point, coordinate)
    let expected ← liftM <| elabTermAndSynthesize
      (← `(fun t : ℚ =>
        CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion.hom t)) none
    let actual ← liftM <| functionOf point
    unless (← withTransparency .all <| isDefEq (← inferType actual) (← inferType expected)) &&
        (← withTransparency .all <| isDefEq actual expected) do
      throwError "the whole tuple map differs from the independently specified inclusion"
    let state ← registryState
    let mut productBindings := 0
    for (_, node) in (← trace.get).toArray do
      match node with
      | .operationApply id parameters _ _ _ =>
        if let some entry := state.operations.find? (fun row => row.id == id && row.name == "·") then
          let some owner := parameters[parameters.size - 1 - entry.numerals]?
            | throwError "the product lost its complete owner"
          let expectedOwner ← typedParameter (← inferType owner) coordinate
          unless (← withTransparency .all <| isDefEq (← inferType owner) (← inferType expectedOwner)) &&
              (← withTransparency .all <| isDefEq owner expectedOwner) do
            throwError "the product changed its independently selected complete owner"
          productBindings := productBindings + 1
      | .operationEquivalence representative chosen candidates comparisons =>
        liftM <| OperationAgreement.validate representative chosen candidates comparisons
        unless candidates.all (fun candidate => !candidate.sources.isEmpty &&
            candidate.sources.all (fun source => source.route.size == source.applications.size)) do
          throwError "the equivalent operations lost their complete ordered source actions"
      | _ => pure ()
    unless productBindings >= components.size do
      throwError "the complete product owner controls were not exercised").run { trace := some trace }
