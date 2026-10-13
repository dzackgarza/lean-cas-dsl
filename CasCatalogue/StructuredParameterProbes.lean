module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

set_option stderrAsMessages false

/- Complete registered constructor parameters are inferred from structured operand data.
The same path handles the identity scalar map and a declared nonidentity coefficient map. -/
run_cmd liftTermElabM do
  let state ← registryState
  let readObject := fun (text : String) => do
    let .ok term := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the selected object did not parse"
    (eval {} term).run {}
  let polynomial ← readObject "ℚ[x]"
  let .object _ _ (some (_, #[coefficient])) _ _ := polynomial
    | throwError "the polynomial lost its complete coefficient parameter"
  let evaluation ← mkConstWithFreshMVarLevels ``CasCatalogue.Algebra.Polynomials.evaluation
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType evaluation)
  let R ← (typedParameter (← inferType parameters[0]!) coefficient).run {}
  unless ← isDefEq parameters[0]! R do throwError "the coefficient parameter changed"
  let expected ← instantiateMVars (← inferType parameters[1]!)
  for (target, selfMap) in #[(coefficient, true), (← readObject "ℂ", false)] do
    withCurrHeartbeats do
      IO.eprintln s!"checking scalar parameter (identity: {selfMap})"
      let .element _ source ← (toElement (.nat 2) target).run {}
        | throwError "the argument lost its selected source"
      let trace ← Trace.new
      let some actual ← (registeredStructuredParameter expected source).run { trace := some trace }
        | throwError "the full registered scalar construction was not inferred"
      unless !actual.hasMVar && !actual.hasLevelMVar && (← isTypeCorrect actual) &&
          (← isDefEq (← inferType actual) expected) do
        throwError "the inferred scalar construction is not closed at its complete type"
      let some declared := state.objects.find? (·.id.raw == "obj.algebras.scalar_extension")
        | throwError "the scalar construction is not registered"
      let extension ← (typedParameter (← inferType R) target).run {}
      let expectedArrow ← if selfMap then mkAppM ``CategoryTheory.CategoryStruct.id #[R]
        else do
          let some row := state.morphisms.find?
              (·.id.raw == "mor.commutative_rings.rational_complex_coefficients")
            | throwError "the declared coefficient map is absent"
          instantiateFresh row.declaration
      unless ← isDefEq (← inferType expectedArrow) (← mkAppM ``Quiver.Hom #[R, extension]) do
        throwError "the coefficient map has different full endpoints"
      let expectedObject ← mkAppM declared.declaration #[R, extension, expectedArrow]
      unless ← withTransparency .all <| isDefEq actual expectedObject do
        throwError "the complete scalar construction or its coefficient map changed"
      if selfMap then
        let some (.object recorded recordedParameters) ← trace.node? actual
          | throwError "the constructor lost its declared trace"
        unless recorded == declared.id && recordedParameters == actual.getAppArgs do
          throwError "recording the constructor changed its exact ordered parameters"
      else
        let some (.parameterEquivalence targetType representative sources) ← trace.node? actual
          | throwError "the equivalent full scalar presentations lost their provenance"
        unless (← isDefEq targetType expected) && (← isDefEq representative actual) &&
            sources.any (·.source == declared.id) &&
            sources.any (·.source.raw == "obj.algebras.complex_rational") do
          throwError "the scalar equivalence dropped a declared source or changed its full type"
        for source in sources do
          unless !source.object.hasMVar && !source.object.hasLevelMVar &&
              (← isTypeCorrect source.object) && (← isTypeCorrect source.identity) &&
              (← withTransparency .all <| isDefEq (← inferType source.object) expected) &&
              (← withTransparency .all <| isDefEq (← inferType source.identity)
                (← mkEq source.object actual)) do
            throwError "the retained scalar equivalence is not checked at the complete type"
      let .object handle category _ _ _ := source | throwError "the source is not an object"
      if (← (registeredStructuredParameter expected
          (.object handle category none none none)).run {}).isSome then
        throwError "an anonymous carrier acquired an unprovided structure"
      IO.eprintln "PASS: complete scalar map and trace; anonymous carrier refused"

/- Equal endpoints do not make an arbitrary endomap an identity: the actual named reversal
competes with the categorical identity and must leave the parameter ambiguous. -/
run_cmd liftTermElabM do
  let state ← registryState
  let fin ← (object state "Fin" #[.nat 3] none).run {}
  let handle ← (semanticObject fin).run {}
  let expected ← mkAppM ``Quiver.Hom #[handle, handle]
  let ambiguous ← try
    discard <| (registeredArrowParameter expected).run {}
    pure false
  catch error =>
    if Exception.isSemanticAmbiguity error then pure true else throw error
  unless ambiguous do throwError "a named endomap was silently replaced by the identity"
  IO.eprintln "PASS: named endomap and identity remain ambiguous"

/- A target ring without a supplied or registered coefficient map does not provide a scalar
algebra merely because its carrier is known. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.commutativeRings)
    | throwError "the coefficient category is absent"
  let R ← (object state "ℂ" #[] (some rings)).run {}
  let S ← (object state "ℚ" #[] (some rings)).run {}
  let source ← (carrierObject S).run {}
  let expected ← mkAppM ``CasCatalogue.Algebra.Algebras.algebrasCategory
    #[← (semanticObject R).run {}]
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[expected]
  if (← (registeredStructuredParameter expected source).run {}).isSome then
    throwError "the scalar constructor invented a missing coefficient map"
  IO.eprintln "PASS: missing coefficient map refused"

/- A complete application does not turn a point of an unrelated finite set into a scalar.
The failure must be semantic invalidity, not a metavariable leak or interpreter exception. -/
run_cmd liftTermElabM do
  let state ← registryState
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "ℚ[x]"
    | throwError "the polynomial source did not parse"
  let polynomial ← (eval {} parsed).run {}
  let .object _ sets (some (_, #[coefficient])) _ _ := polynomial
    | throwError "the polynomial lost its selected coefficient"
  let generatorPoint ← (generatorOf polynomial).run {}
  let finite ← (object state "Fin" #[.nat 3] (some sets)).run {}
  let argument ← (toElement (.nat 2) finite).run {}
  let evaluation ← mkConstWithFreshMVarLevels ``CasCatalogue.Algebra.Polynomials.evaluation
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType evaluation)
  let R ← (typedParameter (← inferType parameters[0]!) coefficient).run {}
  let scalar ← mkAppM ``CasCatalogue.Algebra.Algebras.scalarAlgebra
    #[R, R, ← mkAppM ``CategoryTheory.CategoryStruct.id #[R]]
  let complete ← mkAppM ``CasCatalogue.Algebra.Polynomials.evaluation #[R, scalar]
  let rejected ← try
    discard <| (applyFamily ``CasCatalogue.Algebra.Polynomials.evaluation sets
      #[generatorPoint, argument] (application := some complete)).run {}
    pure false
  catch error =>
    if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "a complete family accepted an unrelated operand type"
  IO.eprintln "PASS: incompatible operand is invalid at the fixed dependent signature"
