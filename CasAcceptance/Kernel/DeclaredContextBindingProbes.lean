/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.TransferInstance

/-! Engineering controls for fixed data endpoints and complete family source parameters. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the fixed-endpoint control did not parse"
    return parsed
  let namedData ← (eval {} (← parse "ℕ in Sets")).run {}
  let .object dataType sets .. := namedData
    | throwError "the supplied named data has no selected set"
  let targetType ← elabTermAndSynthesize (← `({ n : Nat // n = n })) none
  let target : Value := .object targetType sets none none none
  let original ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun n : Nat => n))) none
  let input ← parse "supplied"
  let targetSyntax ← parse "target"
  let proofSyntax ← parse "proof(by intro n; rfl)"
  let trace ← Trace.new
  let context : Ctx := {
    trace := some trace
    bound := [(`supplied, .element original namedData), (`target, target)] }
  let value ← (evalInUsing {} input targetSyntax #[proofSyntax]).run context
  let .element admitted actualTarget := value
    | throwError "the constrained point did not remain an element"
  let some schema ← ConstrainedPoint.schema? targetType
    | throwError "the fixed constrained schema disappeared"
  unless (← isDefEq (← (semanticObject actualTarget).run {}) targetType) &&
      (← isDefEq (← ConstrainedPoint.project schema (← functionOf admitted))
        (← functionOf original)) do
    throwError "fixed data-field interpretation changed the original whole point or target"
  let some (.constrainedPoint constructor category domain retainedData retainedTarget point) ←
      trace.node? admitted
    | throwError "the constrained point lost its original input trace"
  unless constructor == schema.constructor && category == sets.id && point == original &&
      (← isDefEq domain dataType) && (← isDefEq retainedData dataType) &&
      (← isDefEq retainedTarget targetType) do
    throwError "the fixed-field reader changed the original domain, data or endpoint"
  -- The same fixed endpoint without a proof retains the unresolved whole condition.
  let unresolved ← try
      discard <| (evalIn {} input targetSyntax none none).run context
      pure false
    catch error =>
      if (Exception.stratum? error).isNone &&
          (← error.toMessageData.toString).startsWith
            "the constructor condition remains unresolved:" then pure true
      else throw error
  unless unresolved do
    throwError "the fixed data endpoint supplied a missing generalized proof"
  let wrongType ← elabTermAndSynthesize (← `({ b : Bool // b = b })) none
  let wrong : Value := .object wrongType sets none none none
  let rejected ← try
      discard <| (evalInUsing {} input targetSyntax #[proofSyntax]).run
        { context with bound := [(`supplied, .element original namedData), (`target, wrong)] }
      pure false
    catch error =>
      if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do
    throwError "a different fixed data endpoint accepted the supplied point"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some entry := state.functor? FunctorId.modulesFibreInclusion
    | throwError "the existing complete family action is absent"
  let receiver ← elabTermAndSynthesize (← `(ModuleCat.of ℚ (Fin 2 → ℚ))) none
  let action ← instantiateFresh entry.declaration
  let result ← Semantic.objOf action receiver
  let action ← instantiateMVars action
  let (source, _) ← Semantic.realizedFunctorEndpoints
    (← instantiateFresh entry.realization) action
  let some (_, parameter) ← Semantic.selectedFamilyParameter? source
    | throwError "the complete family action lost its supplied source witness"
  let expected ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  unless !action.hasMVar && !action.hasLevelMVar && !result.hasMVar &&
      !result.hasLevelMVar && (← isTypeCorrect result) &&
      (← withTransparency .all <| isDefEq (← inferType parameter) (← inferType expected) <&&>
        isDefEq parameter expected) do
    throwError "the actual receiver did not determine its complete source parameter"
  -- The existing transfer construction changes the full ring on the same carrier.
  let other ← elabTermAndSynthesize (← `(@RingCat.of ℚ (Equiv.neg ℚ).ring)) none
  unless (← withTransparency .all <| isDefEq
      (← mkAppM ``RingCat.carrier #[expected]) (← mkAppM ``RingCat.carrier #[other])) &&
      !(← withTransparency .all <| isDefEq expected other) do
    throwError "the source control does not distinguish complete same-carrier structures"
  let selected ← DirectConstruction.instantiate entry.declaration #[← exprToSyntax other]
  let rejected ← try
      discard <| Semantic.objOf selected.value receiver
      pure false
    catch error =>
      if (← error.toMessageData.toString) ==
          "the supplied receiver has a different complete declared family source type" then
        pure true
      else throw error
  unless rejected do
    throwError "the actual receiver replaced a different already selected full source"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some entry := state.constructions.find? (·.id.raw == "con.automorphisms")
    | throwError "the existing category-parameter construction is absent"
  let actual ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Automorphisms.automorphisms GrpCat.{0})) none
  let application ← DirectConstruction.instantiate entry.declaration #[]
  CategoryContext.exposeStructureParameters application.value
  let #[parameter] := application.explicit
    | throwError "the construction changed its complete category parameter signature"
  unless (← instantiateMVars parameter).hasMVar do
    throwError "structure exposure supplied missing category fields"
  let candidate ← Semantic.asFunctor application.value
  unless ← withTransparency .all <| isDefEq (← inferType candidate) (← inferType actual) <&&>
      isDefEq candidate actual do
    throwError "the actual whole action did not constrain its complete category"
  let application ← DirectConstruction.close application
  let #[parameter] := application.explicit
    | throwError "the complete source category parameter disappeared"
  let expected ← elabTermAndSynthesize (← `(CategoryTheory.Cat.of GrpCat.{0})) none
  unless (← isTypeCorrect application.value) &&
      (← withTransparency .all <| isDefEq (← inferType parameter) (← inferType expected) <&&>
        isDefEq parameter expected) do
    throwError "the full action replaced the category's actual dictionary"

/- A family endpoint names its complete supplied value module, even on the scalar carrier. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.bilinModule)
    | throwError "the complete family control has no formed category"
  let #[entry] := state.morphisms.filter (·.name == "pairing")
    | throwError "the complete family control has no unique declared pairing"
  let valueModule ← elabTermAndSynthesize (← `(ModuleCat.of ℚ ℚ)) none
  let expected ← elabTermAndSynthesize
    (← `(LeanCategories.Modules.Bilinear.Valued.BilinModuleCat
      (CommRingCat.of ℚ) (ModuleCat.of ℚ ℚ))) none
  withLocalDeclD `actualForm expected fun owner => do
    let trace ← Trace.new
    let selected := Value.object owner category none none none
    let .morphism hom _ _ _ (some (_, target)) ←
        (invariantOf entry selected).run { trace := some trace }
      | throwError "the complete family lost its declared morphism endpoints"
    let .object _ _ _ (some (.object actual moduleCategory ..)) _ := target
      | throwError "the family endpoint lost its complete supplied module"
    unless moduleCategory.id == CategoryId.modulesR &&
        (← withTransparency .all <| isDefEq (← inferType actual) (← inferType valueModule) <&&>
          isDefEq actual valueModule) && (← isTypeCorrect hom) do
      throwError "the family endpoint replaced its supplied module with a scalar carrier"
    unless (sourceParameterValues target).any (·.sameSource selected) do
      throwError "the full family endpoint discarded its original receiver"

/- Defining legs reuse complete factors; a shared bare handle does not choose their structures. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the complete construction endpoint control did not parse"
    return parsed
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the complete construction endpoint control has no ring category"
  let standard ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let changed ← elabTermAndSynthesize (← `(@RingCat.of ℚ (Equiv.neg ℚ).ring)) none
  unless !(← withTransparency .all <| isDefEq standard changed) do
    throwError "the construction control does not distinguish complete ring structures"
  let trace ← Trace.new
  let first ← (carrierObject (.object standard rings none none none)).run { trace := some trace }
  let second ← (carrierObject (.object changed rings none none none)).run { trace := some trace }
  let first := retainObjectContext first #[.nat 7]
  let productSyntax ← parse "firstEndpoint × secondEndpoint"
  let receiverSyntax ← parse "receiver"
  let formProduct (left right : Value) : TermElabM Value :=
    (eval {} productSyntax).run {
      trace := some trace, bound := [(`firstEndpoint, left), (`secondEndpoint, right)] }
  let product ← formProduct first second
  let apex ← (semanticObject product).run {}
  for (ordinal, expected) in #[(0, first), (1, second)] do
    let .morphism hom _ _ _ (some (actualSource, actualTarget)) ←
        (constructionLeg {} receiverSyntax (← parse (toString ordinal))).run {
          trace := some trace, bound := [(`receiver, product)] }
      | throwError "the exact construction leg lost its complete endpoints"
    unless actualSource.sameSource product && actualTarget.sameSelection expected &&
        (sourceParameterValues actualTarget).any (·.sameSource product) &&
        (← isTypeCorrect hom) do
      throwError "the defining leg replaced its original complete factor or cone"
    let some (.limitProjection original _) ← trace.node? hom
      | throwError "the defining leg lost its original construction trace"
    unless original == apex do throwError "the defining leg changed its actual cone"
    if ordinal == 0 && !(sourceParameterValues actualTarget).any (·.sameSource (.nat 7)) then
      throwError "coalescing an exact factor discarded its additional retained context"
  let (.object carrier sets _ (some firstStructure) _,
       .object _ _ _ (some secondStructure) _) := (first, second)
    | throwError "the construction control lost its actual selected ring structures"
  let bareCarrier ← withTransparency .all <| whnf carrier
  let ambiguous ← formProduct
    (.object bareCarrier sets none (some firstStructure) none)
    (.object bareCarrier sets none (some secondStructure) none)
  let rejected ← try
      discard <| (constructionLeg {} receiverSyntax (← parse "0")).run {
        trace := some trace, bound := [(`receiver, ambiguous)] }
      pure false
    catch error =>
      if Exception.interpretationKind error == .ambiguous then pure true else throw error
  unless rejected do
    throwError "a shared carrier handle selected one of two different complete structures"
