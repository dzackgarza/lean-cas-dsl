module

import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Language
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

/- An explicit retained Sets action supplies its own source. A declaration-owned
coordinate that merely contains that view as context must still consider every
independently supplied full numeral owner. This exercises the public toElement path. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the independent owner control lost Rings"
  let some semirings := state.categories.find? (·.id == CategoryId.semirings)
    | throwError "the independent owner control lost Semirings"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the independent owner control lost Sets"
  let ringTerm ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let ring := Value.object ringTerm rings none none none
  let action ← Semantic.edgeFunctor state (.functor FunctorId.ringsSemiring)
  let semiringTerm ← Semantic.objOf action ringTerm
  let semiring := Value.object semiringTerm semirings none none none
  let (carrierValue, route, applications) ← (carrierObjectWithAction ring).run {}
  let carrier ← (semanticObject carrierValue).run {}
  unless !route.isEmpty do throwError "the actual ring carrier action was lost"
  let explicitView := Value.object carrier sets none none
    (some (#[ring], ring, route, #[], route.zip (applications.map (·.getAppArgs))))
  let trace ← Trace.new
  let .element point _ ← (toElement (.nat 3) explicitView).run { trace := some trace }
    | throwError "the explicit retained Sets view did not supply its numeral"
  unless ← isTypeCorrect point do throwError "the explicit source numeral is not typed"
  let coordinate := Value.object carrier sets none none none
  let mut escaped := false
  for sources in #[#[explicitView, semiring], #[semiring, explicitView]] do
    let supplied := retainObjectContext coordinate sources
    let refused ← try
      discard <| (toElement (.nat 3) supplied).run {}
      pure false
    catch error =>
      if Exception.interpretationKind error == .ambiguous then pure true else throw error
    logInfo m!"independent owners preserved through public toElement: {refused}"
    escaped := escaped || !refused
  if escaped then
    throwError "a context-only Sets view bypassed an independently supplied full numeral owner"
  logInfo "PASS: an actual Sets view forwards; zero-route context preserves independent owners in both orders"
