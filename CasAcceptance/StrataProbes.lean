/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasAcceptance.Surface.Semantic
public import CasAcceptance.Surface.Realized
public import CasCatalogue.ResolveSyntax
public meta import CasAcceptance.Standard
public meta import CasAcceptance.Surface.Semantic
public meta import CasAcceptance.Surface.Realized
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-failure-strata` (`specs/architecture.md`, "Failure is stratified")

* **Neutrality.** One registry elaborated without leaves and with every leaf has the same operation
  surface on sets, finite sets, groups and bilinear modules, and different implementation gaps.
  Installing realizations changes only computability.
* **Invalid.** An unknown method, an unregistered category, and a method whose owner no structural
  route reaches (`annihilator` on sets) fail as invalid calls.
* **NoImplementation.** `cardinality` applies to finite sets, but no registered action realizes
  the forgetful functor on finite sets presented by `n`, and the call fails as `NoImplementation`,
  not as an invalid call.
* **Ambiguous realization.** A receiver accepted by two registered realizers is refused as an
  ambiguous realization.
* **Unavailable.** A backend whose program does not exist, and one that fails while computing,
  are unavailable.
* **Malformed.** An answer outside the operation's result type is malformed. It is rejected by the
  operation's decoder and never returned as a value.
-/

open Lean Meta Elab Term Command
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.FiniteSets
open CasCatalogue.Foundation.Cardinality CasCatalogue.Modules.SageCardinality

namespace CasCatalogue.StrataProbes

#guard Surface.semanticSurfaces == Surface.realizedSurfaces
#guard Surface.semanticGaps != Surface.realizedGaps

def someSet : SetHandles := SetHandle.prod (.finite 2) (.zmod 3)
def threePoints : FiniteHandles := (3 : ℕ)

/-- The stratum of the failure of elaborating `term`, or `none` if it elaborates. -/
meta def stratumOf (term : Term) : TermElabM (Option Stratum) := do
  try
    discard <| Term.withoutErrToSorry (elabTerm term none)
    return none
  catch e => return Exception.stratum? e

meta def expectStratum (expected : Stratum) (term : Term) : TermElabM Unit := do
  let got ← stratumOf term
  unless got == some expected do
    throwError "{term} fails as {repr got}, not as {repr expected}"

run_cmd liftTermElabM do
  expectStratum .invalid (← `(method% frobnicate (someSet) in "cat.sets"))
  expectStratum .invalid (← `(method% cardinality (someSet) in "cat.no_such_category"))
  expectStratum .invalid (← `(method% annihilator (someSet) in "cat.sets"))
  expectStratum .noImplementation (← `(method% cardinality (threePoints) in "cat.finite_sets"))
  -- `set_eq` applies to sets through their whole subset; no action of it is registered.
  expectStratum .noImplementation (← `(method% set_eq (someSet) in "cat.sets"))
  let state ← registryState
  let setRealizers := state.realizers.filter (·.category == ⟨"cat.sets"⟩)
  let doubled := { state with realizers := state.realizers ++ setRealizers }
  let failed ← try
      discard <| receiverRealization doubled ⟨"cat.sets"⟩ (← `(someSet))
      pure none
    catch e => pure (Exception.stratum? e)
  unless failed == some .ambiguousRealization do
    throwError "a receiver of two realizers fails as {repr failed}"

/-- A registry in which the probe backend declares `meth.cardinality`. -/
meta def probeState : TermElabM RegistryState := do
  let state ← registryState
  let row : BackendOperationEntry :=
    { id := ⟨"bop.probe.cardinality"⟩, backend := "probe", operation := "meth.cardinality"
      decoder := `CasCatalogue.Modules.SageCardinality.decodeCardinality }
  return { state with backendOperations := state.backendOperations.push row }

run_cmd liftTermElabM do
  let state ← probeState
  match ← Backend.connect state "probe" "/nonexistent/program" with
  | .error e => unless e.stratum == .unavailable do throwError "{e.render} is not unavailable"
  | .ok c => Backend.stop c; throwError "a missing program connected"
  match ← Backend.connect state "probe" "/usr/bin/python3"
      #["CasAcceptance/Strata/hostile_cardinality.py"] with
  | .error (.unavailable _ reason) => logInfo m!"python3 is not usable here ({reason})"
  | .error e => throwError e.render
  | .ok c =>
      match ← Backend.callDecoded c "meth.cardinality"
          (Json.mkObj [("n", toJson 1), ("k", toJson 1)]) decodeCardinality with
      | .error e => unless e.stratum == .malformed do throwError "{e.render} is not malformed"
      | .ok card => throwError "a malformed answer was returned as {repr card}"
      match ← Backend.callDecoded c "meth.cardinality"
          (Json.mkObj [("n", toJson 2), ("k", toJson 1)]) decodeCardinality with
      | .error e => unless e.stratum == .unavailable do throwError "{e.render} is not unavailable"
      | .ok card => throwError "a failed computation was returned as {repr card}"
      Backend.stop c

end CasCatalogue.StrataProbes
