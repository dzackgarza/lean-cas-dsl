module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Stored fields expose the supplied polynomial type through its selected structures.
The published evidence still inhabits the original target; a nonunit remains refused. -/
run_cmd liftTermElabM <| withOptions
    (fun options => options.setBool `backward.isDefEq.respectTransparency true) do
  let state ← registryState
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "ℂ[x]"
    | throwError "the selected polynomial object did not parse"
  let polynomial ← (eval {} parsed).run {}
  let some multiplication := state.functors.find? (·.id == FunctorId.ringsMultiplicative)
    | throwError "the registered multiplication route is absent"
  let some monoids := state.categories.find? (·.expression.syntacticEq multiplication.target)
    | throwError "the monoid category is absent"
  let monoidType ← mkAppM ``CategoryTheory.Bundled.α #[← instantiateFresh monoids.declaration]
  let monoid ← (typedParameter monoidType polynomial).run {}
  let selectedView ← (structuredParameterView polynomial monoid monoids).run {}
  let target ← (carrierObject selectedView).run {}
  let some units := state.objects.find? (·.id.raw == "obj.sets.units")
    | throwError "the published units object is absent"
  let (some admission, some evidence) := (units.admission, units.evidence)
    | throwError "the units row lost its published admission or evidence"
  let callerConversion := (← getOptions).getBool `backward.isDefEq.respectTransparency true
  for numeral in #[2, 0] do
    withCurrHeartbeats do
      let .element point _ ← (toElement (.nat numeral) target).run {}
        | throwError "the selected numeral lost its point"
      let value ← elabTermAndSynthesize
        (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax point) 0)) none
      let value ← normalizedValue (← instantiateMVars value)
      let declaration ← mkConstWithFreshMVarLevels admission
      let application := mkAppN declaration #[monoid, value]
      let .forallE _ original _ _ ← whnf (← inferType application)
        | throwError "the published admission lost its obligation"
      let presented ← evidencePresentation state original
      unless presented.getAppFn == original.getAppFn && (← isTypeCorrect presented) &&
          (← withTransparency .all <| isDefEq presented original) do
        throwError "presenting the carrier changed the original predicate or chosen data"
      let carrier ← whnfR presented.getAppArgs[0]!
      unless carrier.isAppOf ``Polynomial do
        throwError "the supplied polynomial carrier is still hidden by categorical plumbing"
      if numeral == 2 then
        let term ← establish evidence original m!"registered constant-unit admission"
        unless (← getOptions).getBool `backward.isDefEq.respectTransparency true ==
            callerConversion do
          throwError "successful admission changed its caller's conversion options"
        unless !term.hasMVar && !term.hasLevelMVar && !term.hasSorry &&
            (← isTypeCorrect term) &&
            (← withTransparency .all <| isDefEq (← inferType term) original) do
          throwError "the evidence did not inhabit the original retained obligation"
      else
        let refused ← try
          discard <| establish evidence original m!"registered nonunit refusal"
          pure false
        catch error =>
          if (← Outcome.ofException error).kind == "invalid" then pure true else throw error
        unless refused do
          throwError "presenting a carrier admitted the zero constant polynomial as a unit"
        unless (← getOptions).getBool `backward.isDefEq.respectTransparency true ==
            callerConversion do
          throwError "rejected admission changed its caller's conversion options"
