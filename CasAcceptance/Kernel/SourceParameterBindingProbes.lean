module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- A declared carrier parameter is the supplied operand's exact type, even when
its retained context contains other types. Dependent occurrences still agree. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the registered category of sets is absent"
  withLocalDeclD `A (mkSort .one) fun A =>
    withLocalDeclD `B (mkSort .one) fun B => do
      let first := Value.object A sets none none none
      let second := Value.object B sets none none none
      let actual := retainObjectContext first #[second]
      let parameter ← mkFreshExprMVar (mkSort .one)
      unless ← (bindSourceParameter parameter actual).run {} do
        throwError "the direct carrier binder lost its supplied type"
      unless (← instantiateMVars parameter) == A do
        throwError "a contextual witness replaced the actual carrier argument"
      if ← withoutModifyingState ((bindSourceParameter parameter second).run {}) then
        throwError "one shared declaration parameter accepted distinct rigid types"
      let nested ← mkFreshExprMVar (mkSort .one)
      let expected ← mkAppM ``Prod #[A, nested]
      let product ← mkAppM ``Prod #[A, B]
      let whole := retainObjectContext
        (Value.object product sets none none none) #[first, second]
      unless ← (bindSourceParameter expected whole).run {} do
        throwError "a nested source parameter lost its supplied constructor context"
      unless (← instantiateMVars nested) == B do
        throwError "the dependent source equation selected a different type"

/- A carrier projection does not determine its hidden bundled owner. The two
existing selected monoid ports retain different full operations on the same type. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let read (text : String) : TermElabM Value := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the selected monoid port did not parse"
    (eval {} parsed).run {}
  let multiplicative ← read
    "view (ℤ in Rings) along «fun.rings.multiplicative_monoid»()"
  let additive ← read
    "view (view (view (ℤ in Rings) along «fun.rings.additive_group»()) along «fun.additive_groups.to_groups»()) along «fun.groups.monoid»()"
  let carrier ← (carrierObject multiplicative).run {}
  let actual := retainObjectContext carrier #[additive]
  let owner ← mkFreshExprMVar (← inferType (← (semanticObject multiplicative).run {}))
  let source ← mkAppM ``MonCat.carrier #[owner]
  let ambiguous ← try
    discard <| (bindSourceParameter source actual).run {}
    pure false
  catch error =>
    if Exception.interpretationKind error == .ambiguous then pure true else throw error
  unless ambiguous do
    throwError "a projected carrier silently selected one of two complete owners"

/- A retained named family can be reused only at its original parameter occurrences.
The supplied parameter B is definitionally equal to A but is a different producer;
ordinary reconstruction must retain B instead of reusing the family built from A. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let rings ← categoryNamed state "Rings"
  let some commutative := state.categories.find? (·.id == CategoryId.commutativeRings)
    | throwError "the parameter-occurrence control has no registered coefficient category"
  let some sum := state.morphisms.find? (·.name == "∑")
    | throwError "the parameter-occurrence control has no registered typed route"
  let trace ← Trace.new
  let first ← (object state "ℚ" #[] (some commutative)).run { trace := some trace }
  let second ← (object state "ℚ" #[] (some commutative)).run { trace := some trace }
  let .object firstHandle _ (some (firstEntry, _)) _ _ := first
    | throwError "the first supplied coefficient has no original named binding"
  let .object secondHandle _ (some (secondEntry, _)) _ _ := second
    | throwError "the second supplied coefficient has no original named binding"
  let some firstNode@(.object firstId _) ← trace.node? firstHandle
    | throwError "the first supplied coefficient has no real producer record"
  let some secondNode@(.object secondId _) ← trace.node? secondHandle
    | throwError "the second supplied coefficient has no real producer record"
  Trace.checkProducerRecord firstHandle firstNode
  Trace.checkProducerRecord secondHandle secondNode
  unless (Trace.producerAnchor? firstHandle).isSome &&
      (Trace.producerAnchor? secondHandle).isSome &&
      firstId == firstEntry.id && secondId == secondEntry.id && firstId == secondId &&
      !(firstHandle.equal secondHandle) &&
      (← withTransparency .all <| isDefEq (← inferType firstHandle) (← inferType secondHandle)) &&
      (← withTransparency .all <| isDefEq firstHandle secondHandle) do
    throwError "the source control does not distinguish equal-formal parameter producers"
  let original ← (object state "Poly" #[first] (some rings)).run { trace := some trace }
  let .object originalHandle category (some (entry, _)) selected viewData := original
    | throwError "the source control has no retained named polynomial family"
  let some originalNode@(.object originalId #[originalParameter]) ← trace.node? originalHandle
    | throwError "the original named family has no real parameterized producer record"
  Trace.checkProducerRecord originalHandle originalNode
  unless originalId == entry.id && originalParameter.equal firstHandle do
    throwError "the original named family does not retain parameter producer A"
  let supplied := Value.object originalHandle category (some (entry, #[second])) selected viewData
  let domain ← (object state "Fin" #[.nat 2] (some sets)).run {}
  let terms ← (typedParamTerms sum.declaration #[domain, supplied]).run { trace := some trace }
  unless terms.size == 2 do
    throwError "the original typed family route changed its explicit parameter positions"
  let actual ← elabTermAndSynthesize terms[1]! none
  let some routed@(.retainedRoute sourceCategory targetCategory route applications receiver) ←
      trace.node? actual
    | throwError "the supplied parameter has no actual retained structural route"
  Trace.checkProducerRecord actual routed
  unless sourceCategory == rings.id && targetCategory != rings.id &&
      !route.isEmpty && applications.size == route.size &&
      !(receiver.equal originalHandle) do
    throwError "a family built from A replaced construction from supplied producer B"
  let some rebuilt@(.object rebuiltId #[rebuiltParameter]) ← trace.node? receiver
    | throwError "the fallback construction has no actual named source record"
  Trace.checkProducerRecord receiver rebuilt
  let rebuiltParameters ← Semantic.namedDeclarationParameters entry.declaration receiver
  unless rebuiltId == entry.id && rebuiltParameter.equal secondHandle &&
      rebuiltParameters.size == 1 && rebuiltParameters[0]!.equal secondHandle do
    throwError "the reconstructed source erased supplied parameter producer B"
  let some preserved@(.object preservedId #[preservedParameter]) ← trace.node? originalHandle
    | throwError "the fallback construction replaced the original source record"
  Trace.checkProducerRecord originalHandle preserved
  unless preservedId == originalId && preservedParameter.equal firstHandle do
    throwError "the fallback construction changed original parameter producer A"
  let entries ← (← trace.get).toArray.mapM fun (value, node) => do
    return (← instantiateMVars value, ← node.mapTermsM instantiateMVars)
  Trace.checkProducedEntries entries #[firstHandle, secondHandle, originalHandle, actual]
