/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanCategories.Catalogue.Semantics
import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize


/-!
# Structured-result metadata through registered representation transport

An engineering regression for data loss: decode the apex and both defining maps of a finite-set
pullback cone, then send its named apex along the registered finite-set forgetful refinement.
The original cone, response and diagram must survive that change of presentation. This does not
assert that the retained cone is a cone in the target category, or establish computational lifting.
-/

open Lean Meta Elab Term Command

namespace CasCatalogue.StructuredResultProbes

run_cmd liftTermElabM do
  let state ← registryState
  let some category := state.categories.find? (·.id.raw == "cat.finite_sets")
    | throwError "the finite-set category fixture is not registered"
  let some entry := state.objects.find? (·.id.raw == "obj.finite_sets.fin")
    | throwError "the named finite-set fixture is not registered"
  let some refinement := entry.refines
    | throwError "the finite-set fixture has no registered refinement"
  let some row := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "the registered pullback shape fixture is unavailable"
  unless state.lifts.any (fun lift =>
      lift.kind == .createsLimits "pullback" &&
        refinement.route.contains lift.edge) do
    throwError "the finite-set pullback creation fixture is unavailable"
  let trace ← (Trace.new : IO _)
  let singleton ← Semantic.object entry #[Syntax.mkNumLit "1"] (some trace)
  let identity ← Semantic.hom (← `(CategoryTheory.CategoryStruct.id _)) singleton singleton
  let diagram ← instantiateMVars (← elabTermAndSynthesize
    (← `(CategoryTheory.Limits.cospan $(← exprToSyntax identity)
      $(← exprToSyntax identity))) none)
  let apexJson := Json.mkObj [("ctor", entry.id.raw), ("args", toJson (#[1] : Array Nat))]
  let legJson := toJson (#[#[0, 0]] : Array (Array Nat))
  let answer := Json.mkObj [("ctor", "cone"),
    ("args", Json.arr #[apexJson, legJson, legJson])]
  let (result, fields) ← match ← StructuredResult.decode row diagram answer
      (fun constructor expected args =>
        Realize.decodeFamily constructor expected args (Realize.decodeValue trace category)) with
    | .ok decoded => pure decoded
    | .error message => throwError "the complete finite-set cone fixture did not decode: {message}"

  unless fields.size == 3 do
    throwError "decoding lost an apex or a defining map"
  let some (apex, some form) := fields[0]?
    | throwError "the decoded apex has no registered form"
  let wire : Realize.Wire := {
    form := form
    value := apex
    json := apexJson
    universal := some result.cone
    universalJson := some result.answer
    universalDiagram := some result.diagram }

  let transported ← Realize.transport trace wire refinement.route
  unless transported.formId == refinement.base.raw do
    throwError "the probe did not execute the representation-changing refinement"
  unless (transported.json.getObjValAs? String "ctor").toOption == some refinement.base.raw do
    throwError "the transported apex has the wrong wire presentation"
  unless transported.universal == wire.universal do
    throwError "structural transport dropped or changed the source cone and defining maps"
  unless transported.universalJson == wire.universalJson do
    throwError "structural transport dropped or changed the complete source response"
  unless transported.universalDiagram == wire.universalDiagram do
    throwError "structural transport dropped or changed the source diagram"

end CasCatalogue.StructuredResultProbes
