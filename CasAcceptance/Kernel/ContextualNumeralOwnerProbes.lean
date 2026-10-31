/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Language
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- Each complete source keeps its own literal family. A separately supplied
semiring remains an independent owner even when its carrier agrees with a ring. -/
run_elab do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the numeral control lost the declared ring category"
  let some semirings := state.categories.find? (·.id == CategoryId.semirings)
    | throwError "the numeral control lost the declared semiring category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the numeral control lost the declared set category"
  let ringTerm ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let ring := Value.object ringTerm rings none none none
  let action ← Semantic.edgeFunctor state (.functor FunctorId.ringsSemiring)
  let semiringTerm ← Semantic.objOf action ringTerm
  let semiring := Value.object semiringTerm semirings none none none
  let carrier ← (semanticObject (← (carrierObject ring).run {})).run {}
  let coordinate := Value.object carrier sets none none none
  for source in #[ring, semiring] do
    let selected := retainObjectContext coordinate #[source]
    let some (.element point retained) ← (contextualNumeral 3 selected).run {}
      | throwError "a complete numeral source acquired ambiguity from its own inherited view"
    unless (← isTypeCorrect point) &&
        (sourceParameterValues retained).any (·.sameSource source) do
      throwError "the numeral discarded its independently supplied complete source"
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "ℚ in CommutativeRings"
    | throwError "the named source control did not parse"
  let trace ← Trace.new
  let named ← (eval {} parsed).run { trace := some trace }
  let namedCarrier ← (semanticObject (← (carrierObject named).run { trace := some trace })).run {}
  let namedCoordinate := retainObjectContext
    (Value.object namedCarrier sets none none none) #[named]
  let some (.element point retained) ← (contextualNumeral 3 namedCoordinate).run
      { trace := some trace }
    | throwError "the named source lost its declared numeral refinement"
  let some (.elementNumeral _ _ actualOwner) ← trace.node? point
    | throwError "the named numeral lost its full actual owner"
  let namedRing ← Semantic.objOf
    (← Semantic.edgeFunctor state (.functor FunctorId.commutativeRingsRings))
    (← (semanticObject named).run {})
  unless (← withTransparency .all <|
      isDefEq (← inferType actualOwner) (← inferType namedRing) <&&>
        isDefEq actualOwner namedRing) &&
      (sourceParameterValues retained).any (·.sameSource named) do
    throwError "the declared numeral refinement replaced the original complete named source"
  for sources in #[#[ring, semiring], #[semiring, ring]] do
    let selected := retainObjectContext coordinate sources
    let refused ← try
        discard <| (contextualNumeral 3 selected).run {}
        pure false
      catch error =>
        if Exception.interpretationKind error == .ambiguous then pure true else throw error
    unless refused do
      throwError "independent full ring and semiring owners were merged by a common carrier"
  logInfo "PASS: each complete numeral source keeps its direct family; independent Ring/Semiring witnesses remain ambiguous in both orders"
