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
  let decode := fun constructor expected args =>
    Realize.decodeFamily constructor expected args (Realize.decodeValue trace category)
  let (result, fields) ← match ← StructuredResult.decode row diagram answer decode with
    | .ok decoded => pure decoded
    | .error message => throwError "the complete finite-set cone fixture did not decode: {message}"

  unless fields.size == 3 do
    throwError "decoding lost an apex or a defining map"
  let some (_, some form) := fields[0]?
    | throwError "the decoded apex has no registered form"
  let diagramJson := Json.mkObj [("ctor", "cospan"),
    ("args", Json.arr #[legJson, legJson])]
  let sourceData := Json.mkObj [("ctor", "constructionApex"),
    ("args", Json.arr #[toJson form.id, diagramJson, result.answer])]
  let wire : Realize.Wire := {
    form := form
    payload := .computed result.apex (.inline sourceData) }

  let transported ← Realize.transport trace wire refinement.route
  unless transported.form.category == CategoryId.sets && transported.formId != wire.formId do
    throwError "the refinement did not change to the registered underlying set category"
  unless (transported.json.getObjValAs? String "ctor").toOption == some "functorAction" do
    throwError "the transported apex lost its registered structural functor action"
  let .ok #[_, retained] := (transported.json.getObjVal? "args").bind (·.getArr?)
    | throwError "structural transport lost the original source payload"
  unless (retained.getObjValAs? String "ctor").toOption == some "constructionApex" do
    throwError "structural transport lost the structured source construction"
  let .ok #[_, retainedDiagram, retainedResult] :=
      (retained.getObjVal? "args").bind (·.getArr?)
    | throwError "structural transport lost the construction fields"
  unless retainedDiagram == diagramJson && retainedResult == result.answer do
    throwError "structural transport lost the complete diagram, cone and returned maps"

end CasCatalogue.StructuredResultProbes
