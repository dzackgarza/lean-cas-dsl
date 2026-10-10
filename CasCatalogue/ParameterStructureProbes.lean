module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Incoming refinement prefixes retain the declared multiplication. Explicit additive
structures remain distinct even when their carriers are definitionally identical. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some multiplication := state.functors.find? (·.id == FunctorId.ringsMultiplicative)
    | throwError "no registered ring multiplication route"
  let some addition := state.functors.find? (·.id == FunctorId.ringsAdditive)
    | throwError "no registered ring addition route"
  let some rings := state.categories.find? (·.expression.syntacticEq multiplication.source)
    | throwError "no registered source category"
  let some monoids := state.categories.find? (·.expression.syntacticEq multiplication.target)
    | throwError "no registered monoid target"
  let some additiveGroups := state.categories.find? (·.expression.syntacticEq addition.target)
    | throwError "no registered additive target"
  let family ← instantiateFresh monoids.declaration
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
  let mut checked := false
  for entry in state.objects do
    if checked || entry.category != rings.id then continue
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    if (← inferType declaration).isForall then continue
    let ring ← (object state entry.name #[] (some rings)).run {}
    let carrier ← (carrierObject ring).run {}
    let .object handle sets origin _ _ := carrier | continue
    let rawCarrier := Value.object handle sets origin none none
    let trace ← Trace.new
    let multiplicative ← (typedParameter expected rawCarrier).run { trace := some trace }
    let evidence := (← trace.get).toArray.filterMap fun (_, node) => match node with
      | .parameterEquivalence expected representative sources => some (expected, representative, sources)
      | _ => none
    if evidence.isEmpty then continue
    let #[(expected, representative, sources)] := evidence
      | throwError "one incoming structure has several equivalence records"
    unless sources.size > 1 do throwError "incoming equivalent sources were dropped"
    for source in sources do
      unless !source.image.hasMVar && (← isTypeCorrect source.identity) &&
          (← isDefEq (← inferType source.image) expected) &&
          (← withTransparency .all <| isDefEq (← inferType source.identity)
            (← mkEq source.image representative)) do
        throwError "an incoming full-structure identity is not kernel checked"
      unless source.route.size ≤ source.carrierRoute.size &&
          decide (source.route = source.carrierRoute.extract 0 source.route.size) do
        throwError "a carrier acquisition used an undeclared route"
    let additive ← Semantic.objOf (← state.routeFunctor #[.functor addition.id])
      (← (semanticObject ring).run {})
    let additiveMonoid ← (typedParameter expected
      (.object additive additiveGroups none none none)).run {}
    if ← withTransparency .all <| isDefEq multiplicative additiveMonoid then
      throwError "additive and multiplicative full structures collapsed"
    let left ← (carrierObject (.object multiplicative monoids none none none)).run {}
    let right ← (carrierObject (.object additiveMonoid monoids none none none)).run {}
    unless ← withTransparency .all <| isDefEq (← (semanticObject left).run {})
        (← (semanticObject right).run {}) do
      throwError "the distinct-structure probe did not compare a shared carrier"
    checked := true
  unless checked do throwError "no accepted equivalent-source structure was checked"

/- Quotient notation retains its declared complete ring before an operation requests a
weaker structure. The bare residue set still has genuinely distinct monoid refinements. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some declared := state.objects.find? (·.id.raw == "obj.rings.integers_mod")
    | throwError "the quotient notation's declared row is absent"
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "ℤ/5"
    | throwError "the quotient notation did not parse"
  let trace ← Trace.new
  let quotient ← (eval {} parsed).run { trace := some trace }
  let .object carrier sets origin (some selected) _ := quotient
    | throwError "quotient notation lost its selected structure"
  let .object ring category (some (selectedRow, parameters)) _ _ := selected
    | throwError "quotient notation lost its named source"
  unless selectedRow.id == declared.id && category.id == declared.category do
    throwError "quotient notation selected a different declared object"
  let #[.nat 5] := parameters
    | throwError "quotient notation lost its exact declared parameter"
  let expectedRing ← Semantic.object declared #[Syntax.mkNumLit "5"]
  unless ← withTransparency .all <| isDefEq ring expectedRing do
    throwError "quotient notation changed the complete selected ring"
  let some multiplication := state.functors.find? (·.id == FunctorId.ringsMultiplicative)
    | throwError "no registered multiplication route"
  let some monoids := state.categories.find? (·.expression.syntacticEq multiplication.target)
    | throwError "no registered multiplication target"
  let family ← instantiateFresh monoids.declaration
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
  let retained ← (typedParameter expected quotient).run { trace := some trace }
  let actual ← Semantic.objOf (← state.routeFunctor #[.functor multiplication.id]) ring
  unless ← withTransparency .all <| isDefEq retained actual do
    throwError "quotient notation substituted a different full monoid"
  let ambiguous ← try
    discard <| (typedParameter expected
      (.object carrier sets origin none none)).run {}
    pure false
  catch error =>
    if CasCatalogue.Exception.stratum? error == some .semanticAmbiguity then pure true
    else throw error
  unless ambiguous do
    throwError "the bare residue set's distinct monoid structures were collapsed"
