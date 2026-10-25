/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Optional engineering checks of the original complete lift-input context.
The independently supplied declarations furnish the typed fixture; these checks
admit no mathematical assertion, numerical result or implementation. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the complete lift-input control did not parse"
    return parsed
  let trace ← Trace.new
  let cache ← IO.mkRef ({} : Std.HashMap String Value)
  let context : Ctx := { trace := some trace, closedTerms := some cache }
  let scalar ← (eval {} (← parse "ℚ in CommutativeRings")).run context
  let ring ← (eval {} (← parse "view scalar along «fun.commutative_rings.ring»()")).run
    { context with bound := [(`scalar, scalar)] }
  let domain ← (eval {} (← parse "RegularModule(ring)")).run
    { context with bound := [(`ring, ring)] }
  let receiver ← (eval {} (← parse "DegeneratePlane()")).run context
  let target ← (eval {} (← parse "view receiver along «fun.bilin_module.forget»(ℚ, ℚ)")).run
    { context with bound := [(`receiver, receiver)] }
  let inclusion ← instantiateMVars (← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion)) none)
  let some (source, codomain) := homEnds? (← inferType inclusion)
    | throwError "the complete input fixture lost its exact Hom endpoints"
  let .object actualSource category .. := domain
    | throwError "the complete input fixture lost its selected source module"
  let targetHandle ← (semanticObject target).run context
  unless ← withTransparency .all <|
      isDefEq source actualSource <&&> isDefEq codomain targetHandle do
    throwError "the original inclusion has different complete supplied endpoints"
  let original := Value.morphism inclusion source codomain category (some (domain, target))
  let selection ← (eval {} (← parse
    "lift(receiver) along «lift.bilin_module.restrict»(ℚ, ℚ) with original using \
      proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)")).run
    { context with bound := [(`receiver, receiver), (`original, original)] }
  unless (sourceParameterValues selection).any (·.sameSource original) do
    throwError "the selected lift discarded its original complete input map"
  let key ← (semanticObject selection).run context
  let some (.selectedLift _ _ retainedSource retainedMap _) ← trace.node? key
    | throwError "the selected lift lost its complete input trace"
  unless retainedMap == inclusion && retainedSource == (← (semanticObject receiver).run context) do
    throwError "retaining the input context replaced an actual supplied expression"
  let some backward ← (selectedLiftField selection "backward").run context
    | throwError "the selected lift lost its original backward field"
  let (_, _, _, _, coordinate, _) ← (morphismContext backward).run context
  let witnesses := sourceParameterValues coordinate
  unless witnesses.any (·.sameSource original) && witnesses.any (·.sameSource domain) &&
      witnesses.any (·.sameSource ring) do
    throwError "the lift field lost the original map's full domain or arithmetic owner"
  let carrier ← (carrierObject coordinate).run context
  let .element point actualTarget ← (toElement (.nat 3) carrier).run context
    | throwError "the original complete coordinate did not supply its registered numeral"
  unless (← isTypeCorrect point) &&
      (sourceParameterValues actualTarget).any (·.sameSource domain) &&
      (sourceParameterValues actualTarget).any (·.sameSource ring) do
    throwError "the coordinate numeral replaced its actual selected domain or owner"
  let baseMap ← (eval {} (← parse
    "row_linear_map(2, scalar, [3/2, -1] in RectangularMatrices(1, 2, scalar))")).run
      { context with bound := [(`scalar, scalar)] }
  let cone ← (eval {} (← parse "degenerate_plane_cone()")).run context
  let factor ← (eval {} (← parse
    "factor(baseInput) through selectedInput with coneInput using \
      proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization)")).run
    { context with bound :=
      [(`baseInput, baseMap), (`selectedInput, selection), (`coneInput, cone)] }
  let (_, _, _, _, factorSource, factorTarget) ← (morphismContext factor).run context
  for endpoint in #[factorSource, factorTarget] do
    let retained := sourceParameterValues endpoint
    unless retained.any (·.sameSource baseMap) && retained.any (·.sameSource cone) &&
        retained.any (·.sameSource selection) do
      throwError "the factor discarded an original complete checked input"
  let factorCarrier ← (carrierObject factorSource).run context
  let .element coordinates _ ←
      (tuple {} #[← parse "2", ← parse "1"] (some factorCarrier)).run context
    | throwError "the factor's original source lost its complete coordinate presentation"
  unless ← isTypeCorrect coordinates do
    throwError "retaining factor inputs changed the complete coordinate type"
