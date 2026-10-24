module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Engineering probes only: complete request types, retained source contexts, ambiguity,
and literal shape. These do not compute answers or modify the permanent assertions. -/

/- A category selection reads the constructor's registered name before its dependent
arguments. An object parameter cannot be parsed as a numeral by that metadata lookup. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["Vec(ℤ, 2) in Sets",
      "PowerSeries(ℤ in CommutativeRings) in HausdorffTopologicalMonoids"] do
    withCurrHeartbeats do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
        | throwError "a selected dependent object failed to parse: {text}"
      let value ← (eval {} parsed).run {}
      let .object handle _ (some (_, parameters)) _ _ := value
        | throwError "a selected dependent object lost its registered parameters: {text}"
      unless !parameters.isEmpty && !handle.hasMVar && !handle.hasLevelMVar &&
          (← isTypeCorrect handle) do
        throwError "a selected dependent object has an incomplete type: {text}"

run_cmd liftTermElabM <| withoutErrToSorry do
  for text in #["i()", "id(ℤ)(2)", "2 • ((1, -1) in Vec(ℤ, 2))",
      "(x ↦ x + 1 in ℚ[x])(2)"] do
    withCurrHeartbeats do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
        | throwError "a generic registered application failed to parse: {text}"
      let trace ← Trace.new
      let value ← try (eval {} parsed).run { trace := some trace }
        catch error => throwError "{text}: {error.toMessageData}"
      let .element point _ := value
        | throwError "the generic application did not form an element request: {text}"
      unless !point.hasMVar && !point.hasLevelMVar && (← isTypeCorrect point) do
        throwError "the generic application has an incomplete declared type: {text}"
  for text in #["f.map(0)", "(id(ℤ)).map()", "id(ℤ)(2)"] do
    let .ok _ := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "a formed callable or raw identifier field failed to parse: {text}"

/- The published zero maps erase their scalar ring in their returned constant function.
Selection must still distinguish the complete ordered declaration arguments. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let left ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Operations.zero (RingCat.of ℤ) (ModuleCat.of ℤ PUnit.{1}))) none
  let right ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Operations.zero (RingCat.of ℚ) (ModuleCat.of ℚ PUnit.{1}))) none
  unless ← withTransparency .all <| isDefEq left right do
    throwError "the constant-operation control does not erase its different scalar parameters"
  if ← (sameOperationApplication left right).run {} then
    throwError "equal constant results erased distinct complete operation applications"
  let state ← registryState
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the operation probe has no registered module owner"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the operation probe has no category of sets"
  let first ← elabTermAndSynthesize (← `(ModuleCat.of ℤ PUnit.{1})) none
  let second ← elabTermAndSynthesize (← `(ModuleCat.of ℚ PUnit.{1})) none
  let carrier ← elabTermAndSynthesize (← `(PUnit.{1})) none
  let target := retainObjectContext (.object carrier sets none none none)
    #[.object first modules none none none, .object second modules none none none]
  let ambiguous ← try
    discard <| (selectedOperationApplication ``CasCatalogue.Modules.Operations.zero
      CategoryId.modulesR target #[]).run {}
    pure false
  catch error =>
    if CasCatalogue.Exception.isSemanticAmbiguity error then pure true else throw error
  unless ambiguous do
    throwError "selected operation dispatch collapsed distinct complete module owners"

/- An anonymous coordinate uses a complete supplied ring, retaining every alias of it.
The same bare carrier, without that independently supplied owner, provides no ring. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the coordinate probe has no registered numeral owner"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the coordinate probe has no category of sets"
  let named ← (object state "ℤ" #[] (some rings)).run {}
  let .object owner .. := named | unreachable!
  let otherName := Value.object owner rings none none none
  let carrier ← elabTermAndSynthesize (← `(ℤ)) none
  let bare := Value.object carrier sets none none none
  let coordinate := retainObjectContext bare #[named, otherName]
  let trace ← Trace.new
  let .element point retained ← (toElement (.nat 2) coordinate).run { trace := some trace }
    | throwError "the supplied complete owner did not supply its coordinate numeral"
  let .object _ _ none none _ := retained
    | throwError "the coordinate acquired a named or selected structure from its carrier"
  unless !point.hasMVar && !point.hasLevelMVar && (← isTypeCorrect point) do
    throwError "the contextual numeral has an incomplete type"
  let witnesses := sourceParameterValues retained
  unless witnesses.any (·.sameSource named) && witnesses.any (·.sameSource otherName) do
    throwError "the contextual numeral discarded an alias of its complete supplied owner"
  let rejected ← try
    discard <| (toElement (.nat 2) bare).run {}
    pure false
  catch error =>
    if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "an anonymous bare carrier supplied an unchosen numeral owner"
  let mut repeated := coordinate
  for _ in [:12] do repeated := retainObjectContext repeated #[named, otherName, coordinate]
  unless (sourceParameterValues repeated).size ≤ 5 do
    throwError "repeated context retention re-expanded identical source witnesses"

/- Actual finite-function domains fix both tuple length and rectangular matrix dimensions.
The coordinate stays anonymous and carries the independently supplied scalar context. -/
run_cmd liftTermElabM <| withoutErrToSorry do
  let state ← registryState
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the finite-function probe has no ring category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the finite-function probe has no sets category"
  let scalar ← (object state "ℤ" #[] (some rings)).run {}
  let vector ← elabTermAndSynthesize (← `(Fin 2 → ℤ)) none
  let matrix ← elabTermAndSynthesize (← `(Fin 2 → Fin 3 → ℤ)) none
  for (type, positive, negative) in #[
      (vector, "(1, -2)", "(1, -2, 3)"),
      (matrix, "[1, 2, 3; 4, 5, 6]", "[1, 2; 3, 4]")] do
    let target := retainObjectContext (.object type sets none none none) #[scalar]
    withCurrHeartbeats do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term positive
        | throwError "the contextual finite-function literal did not parse"
      let trace ← Trace.new
      let .element point retained ← (eval {} parsed none (some target)).run
          { trace := some trace }
        | throwError "the finite-function literal did not form an element request"
      let .object handle _ none none _ := retained
        | throwError "a declared anonymous finite-function object acquired an alias"
      unless (← isDefEq handle type) && !point.hasMVar && !point.hasLevelMVar &&
          (← isTypeCorrect point) do
        throwError "the finite-function request lost its exact declared target"
      unless (sourceParameterValues retained).any (·.sameSource scalar) do
        throwError "the finite-function request discarded its scalar context"
    withCurrHeartbeats do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term negative
        | throwError "the finite-function shape negative did not parse"
      let rejected ← try
        discard <| (eval {} parsed none (some target)).run {}
        pure false
      catch error =>
        if Exception.stratum? error == some .invalid then pure true else throw error
      unless rejected do throwError "a literal escaped its declared finite-function dimensions"

/- A fixed declaration can reframe the original generalized point at its exact endpoint.
It retains that arrow and source stage, rather than replacing it with a global point. -/
run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let named ← (object state "ℤ" #[] none).run {}
  let .object carrier category .. := named | unreachable!
  let anonymous := Value.object carrier category none none none
  let original ← (identityAt anonymous).run {}
  let .element reframed _ ← (declaredResult (.element original anonymous) named).run {}
    | throwError "the fixed declared codomain refused its original generalized point"
  unless original == reframed do
    throwError "declared endpoint reframing changed the original generalized point"
  let some (source, target) := homEnds? (← inferType reframed) | unreachable!
  unless ← isDefEq source carrier <&&> isDefEq target carrier do
    throwError "declared endpoint reframing changed the original point's stage"
