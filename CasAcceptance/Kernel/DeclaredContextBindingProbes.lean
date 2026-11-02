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

/- An exact numeral retains its complete owner and actual action at global and staged points. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let parse (text : String) : TermElabM Syntax := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the numeral-owner control did not parse"
    return parsed
  let mut scope : Language.Scope := {}
  for text in #["let Q := ℚ in CommutativeRings",
      "let Qring := view Q along «fun.commutative_rings.ring»()",
      "let scalarModule := RegularModule(Qring)"] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
      | throwError "the original scalar binding did not parse"
    let some (name, body) ← letBinding? parsed | throwError "the original scalar binding was lost"
    scope := scope.insert name body
  let trace ← Trace.new
  let context : Ctx := { trace := some trace }
  let ring ← (eval scope (← parse "Qring")).run context
  let .object ringTerm ringCategory .. := ring
    | throwError "the scalar control lost its complete ring"
  let selected ← (eval scope (← parse "scalarModule")).run context
  let carrier ← (carrierObject selected).run context
  let numerator ← (toElement (.nat 3) carrier).run context
  let .element point retained ← (coerceTo numerator carrier).run context
    | throwError "the exact numerator did not retain its declared coordinate"
  let some owner ← (retainedPointOwner? point retained).run context
    | throwError "an identity view dropped the exact point's complete source"
  unless (← withTransparency .all <| isDefEq
      (← (semanticObject owner).run context) (← (semanticObject ring).run context)) do
    throwError "the retained numeral source changed its complete ring"
  let expected ← (typedParameter (mkConst ``MonCat [.zero]) ring).run context
  let state ← registryState
  let #[row] := state.morphisms.filter (·.name == "/")
    | throwError "the division control has no unique declared family"
  for stage in #[none, some carrier] do
    let trace ← Trace.new
    let result ← (eval scope (← parse "3/2") none (some carrier)).run
      { context with trace := some trace, stage }
    let .element point target ← (declaredResult result carrier).run context
      | throwError "the fraction lost its original declared coordinate"
    unless target.sameSelection carrier && (← isTypeCorrect point) do
      throwError "the numeral owner replaced the declared target structure"
    let some (source, actualTarget) := homEnds? (← inferType point)
      | throwError "the fraction lost its original point type"
    let expectedSource ← match stage with
      | none => globalPointSource.run context
      | some value => (semanticObject value).run context
    unless (← isDefEq source expectedSource) &&
        (← isDefEq actualTarget (← (semanticObject carrier).run context)) do
      throwError "the numeric family changed the generalized point endpoints"
    let declarations := (← trace.get).toArray.filterMap fun (_, node) => match node with
      | .namedMorphism id parameters => if id == row.id then some parameters else none
      | _ => none
    unless !declarations.isEmpty && (← declarations.allM fun parameters => do
        let #[actual] := parameters | return false
        withTransparency .all <| isDefEq actual expected) do
      throwError "division did not retain the numeral's complete multiplicative owner"
    for parameters in declarations do
      let some (.retainedRoute source _ route applications receiver) ←
          trace.node? parameters[0]!
        | throwError "the chosen complete parameter lost its actual structural action"
      unless source == ringCategory.id && !route.isEmpty &&
          route.size == applications.size &&
          applications.all (fun action => !action.hasMVar && !action.hasLevelMVar) &&
          (← applications.allM fun action => isTypeCorrect action) &&
          (← withTransparency .all <| isDefEq receiver ringTerm) do
        throwError "the parameter trace replaced the original complete ring or its checked action"
  let identity ← (identityAt carrier).run context
  let ambiguous ← try
      discard <| (applyNamed state "/" #[.element identity carrier, .nat 2]
        (some carrier)).run context
      pure false
    catch error =>
      if Exception.interpretationKind error == .ambiguous then pure true else throw error
  unless ambiguous do
    throwError "a nonnumeral point borrowed an unrelated contextual monoid"
  let invalid ← try
      discard <| (eval {} (← parse "1/2 in ℤ")).run context
      pure false
    catch error =>
      if Exception.interpretationKind error == .invalid then pure true else throw error
  unless invalid do throwError "a retained numeral owner bypassed unit admission"

/- The original declared function endpoint must retain both complete modules and
   their actual carrier actions after unsuccessful whole-endpoint recognition. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let expected ← elabTermAndSynthesize (← `((ℚ × ℚ) →ₗ[ℚ] ℚ)) none
  let some plan ← DeclaredAdmission.resolve? CategoryId.sets expected true
    | throwError "the original typed function has no declared admission"
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the declared endpoint control has no set category"
  let trace ← Trace.new
  let context : Ctx := { trace := some trace }
  let domain ← (recognize state plan.application.value sets #[] plan.application.explicit).run context
  let some (_, endpoint) ← (inclusionOut? domain).run context
    | throwError "the original function admission has no declared inclusion"
  let .homSet source target ← (inclusionTargetValue domain endpoint sets).run context
    | throwError "the declared inclusion lost its complete function coordinate"
  let expectedSource ← elabTermAndSynthesize (← `(ModuleCat.of ℚ (ℚ × ℚ))) none
  let expectedTarget ← elabTermAndSynthesize (← `(ModuleCat.of ℚ ℚ)) none
  for (value, expectedModule) in #[(source, expectedSource), (target, expectedTarget)] do
    let .object carrier _ _ (some selected) _ := value
      | throwError "a function endpoint lost its selected complete module"
    unless (← withTransparency .all <| isDefEq
        (← (semanticObject selected).run context) expectedModule) &&
        (sourceParameterValues value).any (·.sameSource domain) do
      throwError "function endpoint reuse discarded its complete module or admission context"
    let some (.retainedRoute owner destination route applications receiver) ← trace.node? carrier
      | throwError "a reused endpoint lost its actual complete carrier action"
    unless owner == CategoryId.modulesR && destination == CategoryId.sets &&
        !route.isEmpty && route.size == applications.size &&
        applications.all closedReadingTerm && (← applications.allM fun action => isTypeCorrect action) &&
        (← withTransparency .all <| isDefEq receiver expectedModule) do
      throwError "the function endpoint changed its original source or complete registered action"

/- Retrying an exact carrier after a failed endpoint trial restores its own action;
   a different complete ring on the same carrier remains a different selection. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the carrier replay control has no ring category"
  let standard ← elabTermAndSynthesize (← `(RingCat.of ℚ)) none
  let changed ← elabTermAndSynthesize (← `(@RingCat.of ℚ (Equiv.neg ℚ).ring)) none
  unless !(← withTransparency .all <| isDefEq standard changed) do
    throwError "the replay control does not distinguish complete same-carrier rings"
  let first := Value.object standard rings none none none
  let second := Value.object changed rings none none none
  let trace ← Trace.new
  let readings ← IO.mkRef #[]
  let context : Ctx := { trace := some trace, carrierReadings := some readings }
  let failed : Option Value ← (optionalReading do
    discard <| carrierObject first
    throwStratum .invalid "the enclosing endpoint trial is inapplicable").run context
  unless failed.isNone && (← trace.get).isEmpty do
    throwError "a failed endpoint trial published a speculative carrier action"
  let mut carriers := #[]
  for selected in #[first, second] do
    let carrier ← (carrierObject selected).run context
    let .object handle _ _ (some actual) _ := carrier
      | throwError "carrier replay dropped the complete selected source"
    unless actual.sameSource selected do
      throwError "carrier replay identified different complete same-carrier structures"
    let some (.retainedRoute owner destination route applications receiver) ← trace.node? handle
      | throwError "carrier replay lost its checked action after the failed trial"
    unless owner == rings.id && destination == CategoryId.sets && !route.isEmpty &&
        route.size == applications.size && applications.all closedReadingTerm &&
        (← withTransparency .all <| isDefEq receiver (← (semanticObject selected).run context)) do
      throwError "carrier replay used another complete source's retained action"
    carriers := carriers.push carrier
  if (← (coercionMap carriers[0]! carriers[1]!).run context).isSome ||
      (← (coercionMap carriers[1]! carriers[0]!).run context).isSome then
    throwError "carrier reuse granted a carrier-only identification of different selected rings"
