/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import Mathlib.CategoryTheory.InducedCategory
meta import Mathlib.CategoryTheory.InducedCategory

/-! Engineering controls for recovery of a complete literal construction. The
packet fixtures test framing and ownership, without asserting a mathematical answer. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.groups.cyclic_quotient")
    | throwError "the accepted construction source fixture is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let receiver ← mkAppM ``CategoryTheory.Core.mk #[source]
  let functor ← instantiateMVars (← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Automorphisms.automorphisms GrpCat.{0})) none)
  let selected ← mkAppM ``CategoryTheory.Functor.obj #[functor, receiver]
  unless (← trace.node? receiver).isNone && (← trace.node? selected).isNone do
    throwError "the complete literal construction fixture already retained an occurrence"
  let some action ← completeLiteralConstruction? selected
    | throwError "the full literal construction was not recovered"
  let #[category] := action.parameters
    | throwError "the construction lost its complete dependent category argument"
  let groups ← instantiateMVars (← elabTermAndSynthesize
    (← `(LeanCategories.Algebra.Groups.{0})) none)
  unless action.entry.id.raw == "con.automorphisms" &&
      (← withTransparency .all <| isDefEq (← inferType category) (← inferType groups) <&&>
        isDefEq category groups) do
    throwError "the full literal construction changed its selected category dictionary"
  let categoryData := node "category" #[toJson "cat.groups", Json.arr #[]]
  unless (← parameterData trace category) == categoryData do
    throwError "the complete inferred category lost its accepted public descriptor"
  unless ← recordCompleteConstruction trace selected do
    throwError "the full literal construction was not recorded for ordinary execution"
  let some (.construction id parameters actualReceiver) ← trace.node? selected
    | throwError "the recovered construction has no complete execution trace"
  unless id == action.entry.id && parameters == action.parameters && actualReceiver == receiver do
    throwError "the recovered construction changed its actual receiver or ordered parameters"
  let some (.coreObject context original) ← trace.node? receiver
    | throwError "the exact literal core receiver was not framed"
  unless original == source &&
      (← withTransparency .all <| isDefEq context.bundle groups) do
    throwError "the core receiver changed its original object or complete category"
  let returned : Wire := {
    form := .object row
    payload := .computed source (.owned "literal-construction-source" 430
      (node "opaqueData" #[toJson "actual complete selected group"])) }
  let harness ← Harness.empty
  harness.results.modify (·.insert source returned)
  let actual ← realize harness trace "the literal construction's exact core source" receiver
  unless actual.value == receiver && actual.json == node "coreObject" #[returned.json] &&
      actual.owner? == returned.owner? do
    throwError "the recovered core receiver replaced actual data or its owner"
  let (parameters, dependencies) ← realizedParameters harness trace #[category, receiver]
  unless parameters == #[categoryData, actual.json] &&
      dependencies.any (fun wire => wire.json == actual.json && wire.owner? == returned.owner?) do
    throwError "construction parameters discarded their complete source dependency"
  -- Coincidence at this receiver cannot select the construction's whole action.
  let constant ← instantiateMVars (← elabTermAndSynthesize
    (← `((CategoryTheory.Functor.const (CategoryTheory.Core GrpCat.{0})).obj
      $(← exprToSyntax selected))) none)
  let coincident ← Semantic.objOf constant receiver
  unless ← withTransparency .all <| isDefEq coincident selected do
    throwError "the negative action fixture lost its coincident object value"
  unless (← completeLiteralConstruction? coincident).isNone do
    throwError "construction recovery chose a full action from its value at one receiver"

-- The same category carrier with another genuine Mathlib category dictionary
-- must not acquire the named Groups descriptor.
run_elab do
  let groups ← instantiateMVars (← elabTermAndSynthesize
    (← `(LeanCategories.Algebra.Groups.{0})) none)
  let alternative ← instantiateMVars (← elabTermAndSynthesize
    (← `(CategoryTheory.Cat.of
      (CategoryTheory.InducedCategory (Type 0) (fun _ : GrpCat.{0} => Fin 1)))) none)
  let originalCarrier ← mkAppM ``CategoryTheory.Bundled.α #[groups]
  let otherCarrier ← mkAppM ``CategoryTheory.Bundled.α #[alternative]
  unless ← withTransparency .all <| isDefEq originalCarrier otherCarrier do
    throwError "the negative fixture lost its equal category carriers"
  if ← withTransparency .all <| isDefEq groups alternative then
    throwError "the negative fixture lost its distinct complete category dictionary"
  unless (← completeDeclarationApplication? `LeanCategories.Algebra.Groups alternative).isNone &&
      (← completeNamedCategoryPresentations alternative).isEmpty do
    throwError "category recovery substituted a named dictionary on the same carrier"

end
