/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients

/-! Engineering checks for complete retained route prefixes and construction
occurrences. Actual packets and owners are fixtures, not mathematical answers. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

-- The monoid is the complete first image of an already selected longer route.
-- Its data must come from that route's actual group, not an equal cached result.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.groups.cyclic")
    | throwError "the accepted selected-group fixture is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let firstEdge := EdgeRef.functor FunctorId.groupsMonoid
  let secondEdge := EdgeRef.functor FunctorId.monoidsSemigroup
  let first ← Semantic.asFunctor (← Semantic.edgeFunctor state firstEdge)
  let middle ← Semantic.objOf first source
  let second ← Semantic.asFunctor (← Semantic.edgeFunctor state secondEdge)
  let finalImage ← Semantic.objOf second middle
  let first ← instantiateMVars first
  let second ← instantiateMVars second
  Trace.record (some trace) finalImage
    (.retainedRoute row.category ⟨"cat.semigroups"⟩ #[firstEdge, secondEdge]
      #[first, second] source)
  let selected ← instantiateMVars (← elabTermAndSynthesize
    (← `(MonCat.of (↑$(← exprToSyntax source)))) none)
  unless (← trace.node? selected).isNone &&
      (← withTransparency .all <| isDefEq selected middle) do
    throwError "the selected complete prefix fixture lost its distinct presentation"
  let some recovered ← FunctorActionData.retainedParameterAction? trace selected
    | throwError "the complete selected route prefix was not recovered"
  unless recovered.receiver == source && recovered.route == #[firstEdge] &&
      recovered.applications == #[first] do
    throwError "prefix recovery changed the original source or complete action"
  let original : Wire := {
    form := .object row
    payload := .computed source (.owned "retained-prefix-source" 420
      (node "opaqueData" #[toJson "original complete group"])) }
  let foreign := { original with
    payload := .computed middle
      (.owned "unrelated-prefix-image" 421 (node "opaqueData" #[toJson "foreign monoid"])) }
  let harness ← Harness.empty
  harness.results.modify (fun cache => (cache.insert source original).insert middle foreign)
  let expected := node FunctorId.groupsMonoid.raw #[]
  let data := node "functorAction" #[expected, original.json]
  let actual ← realize harness trace "the retained complete route prefix" selected
  unless actual.value == selected && actual.json == data && actual.owner? == original.owner? do
    throwError "prefix recovery substituted an equal result or lost the original owner"
  let (parameters, dependencies) ← realizedParameters harness trace #[selected]
  unless parameters == #[data] && dependencies.any (·.owner? == original.owner?) &&
      !dependencies.any (·.owner? == foreign.owner?) do
    throwError "prefix parameter encoding lost its actual complete source dependency"

-- Public Functor/Prefunctor projection spellings may refer to one full retained
-- construction and the exact same receiver. Reuse that occurrence's actual data.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.groups.cyclic_quotient")
    | throwError "the accepted construction source fixture is absent"
  let some entry := state.constructions.find? (·.id.raw == "con.automorphisms")
    | throwError "the accepted complete construction fixture is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let receiver ← mkAppM ``CategoryTheory.Core.mk #[source]
  let parameter ← instantiateMVars (← elabTermAndSynthesize
    (← `(LeanCategories.Algebra.Groups.{0})) none)
  let action ← DirectConstruction.select entry #[← exprToSyntax parameter] receiver
  let original ← instantiateMVars (← DirectConstruction.obj action receiver)
  Trace.record (some trace) original (.construction entry.id #[parameter] receiver)
  let publicAction ← instantiateMVars (← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Automorphisms.automorphisms GrpCat.{0})) none)
  let selected ← mkAppM ``CategoryTheory.Functor.obj #[publicAction, receiver]
  unless selected != original && (← trace.node? selected).isNone do
    throwError "the construction fixture lost its distinct public projection"
  unless (← retainedConstructionResult? trace selected) == some original do
    throwError "the exact retained construction occurrence was not recovered"
  let some form := state.constructionForm? entry.id.raw
    | throwError "the construction result form is absent"
  let returned : Wire := {
    form
    payload := .computed original (.owned "original-construction-owner" 422
      (node "opaqueData" #[toJson "actual constructed group"]))
    categoryContext := some action.target }
  let harness ← Harness.empty
  harness.results.modify (·.insert original returned)
  let actual ← realize harness trace "the original complete construction" selected
  unless actual.value == selected && actual.json == returned.json &&
      actual.owner? == returned.owner? do
    throwError "construction recovery replaced original returned data or its owner"
  let (parameters, dependencies) ← realizedParameters harness trace #[selected]
  unless parameters == #[returned.json] &&
      dependencies.any (fun wire => wire.json == returned.json && wire.owner? == returned.owner?) do
    throwError "construction parameter recovery omitted its actual returned dependency"
  -- A different complete action on the same exact receiver is not this result.
  let other ← elabTermAndSynthesize
    (← `(CasCatalogue.Algebra.Automorphisms.endomorphisms GrpCat.{0})) none
  let other ← mkAppM ``CategoryTheory.Functor.obj #[other, receiver]
  unless (← retainedConstructionResult? trace other).isNone do
    throwError "construction recovery substituted a different complete action"
  -- Distinct retained occurrences are not chosen by trace order or cache contents.
  let duplicate ← mkAppM ``id #[original]
  Trace.record (some trace) duplicate (.construction entry.id #[parameter] receiver)
  let ambiguous ← try
    discard <| retainedConstructionResult? trace selected
    pure false
  catch error => pure (Exception.stratum? error == some .ambiguousRealization)
  unless ambiguous do
    throwError "construction recovery silently chose one of two original data occurrences"

end
