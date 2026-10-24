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
