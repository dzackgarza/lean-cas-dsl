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


open Lean.Elab.Command

/- Engineering boundary for the explicit derived numeral path. These
are the existing accepted Ring/Semiring structures and numeral owner conditions.
A context-only coordinate never selects either independently supplied owner. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  unless maxHeartbeats.get (← getOptions) == 200000 do
    throwError "the derived-owner control changed its original budget"
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the derived-owner control lost Rings"
  let some semirings := state.categories.find? (·.id == CategoryId.semirings)
    | throwError "the derived-owner control lost Semirings"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the derived-owner control lost Sets"
  let ringTerm ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let ring := Value.object ringTerm rings none none none
  let action ← Semantic.edgeFunctor state (.functor FunctorId.ringsSemiring)
  let semiringTerm ← Semantic.objOf action ringTerm
  let semiring := Value.object semiringTerm semirings none none none
  let ringContext ← (objectContext ring).run {}
  let semiringContext ← (objectContext semiring).run {}
  let derivedRing := Value.derivedObject ringTerm ringContext #[]
  let derivedSemiring := Value.derivedObject semiringTerm semiringContext #[]
  -- Each directly supplied full derived owner still forms its own typed point
  -- and keeps that exact original Value. No named origin is supplied here.
  for selected in #[derivedRing, derivedSemiring] do
    let trace ← Trace.new
    let .element point retained ← (toElement (.nat 3) selected).run { trace := some trace }
      | throwError "a directly selected complete derived owner lost its numeral"
    unless !point.hasMVar && !point.hasLevelMVar && (← isTypeCorrect point) &&
        (sourceParameterValues retained).any (·.sameSource selected) do
      throwError "the derived numeral lost its original complete owner"
  let carrierValue ← (carrierObject derivedRing).run {}
  let carrier ← (semanticObject carrierValue).run {}
  let coordinate := Value.object carrier sets none none none
  for witnesses in #[#[derivedRing, derivedSemiring], #[derivedSemiring, derivedRing]] do
    let supplied := retainObjectContext coordinate witnesses
    -- A public carrier read must preserve this as context only. An empty route
    -- cannot turn either original witness into the coordinate's selection.
    let actualCoordinate ← (carrierObject supplied).run {}
    let .object _ _ _ selected data := actualCoordinate
      | throwError "the context-only derived-owner coordinate changed its kind"
    unless selected.isNone && data.all (fun (_, _, route, _, _) => route.isEmpty) &&
        witnesses.all (fun witness =>
          (sourceParameterValues actualCoordinate).any (·.sameSource witness)) do
      throwError "the context-only coordinate selected or discarded a derived owner"
    let refused ← try
      discard <| (toElement (.nat 3) supplied).run {}
      pure false
    catch error =>
      if Exception.interpretationKind error == .ambiguous then pure true else throw error
    unless refused do
      throwError "a context-only coordinate merged independent complete derived owners"
  logInfo "PASS: explicit derived owners retain their typed numerals; context-only derived Ring/Semiring owners remain ambiguous in both orders"
