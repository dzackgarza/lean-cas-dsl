/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

/-! Engineering checks of complete presentations and actual computational data.
These fixtures use already accepted catalogue rows and start no backend. The
opaque answers are data-flow controls, not evidence of a mathematical answer. -/

namespace CasAcceptance.Kernel.ObjectPresentationProbes

def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

-- The actual functor output and every parameter owner survive a named presentation,
-- its defining inclusion, and a membership map at the resulting ambient object.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Realize.Harness.empty
  let some entry := state.objects.find? (·.id.raw == "obj.sets.units")
    | throwError "the accepted object presentation is unavailable"
  let some published := entry.functorPresentation | throwError "the accepted presentation is absent"
  let some action := state.functor? published.functor | throwError "the accepted action is absent"
  let parameter ← elabTermAndSynthesize (← `(MonCat.of (ZMod 4))) none
  let sourceCategory ← Semantic.namedCategoryFor state action.source
  let parameterData := node "opaqueData" #[toJson "actual selected monoid"]
  let parameterWire : Realize.Wire := {
    form := .diagrams sourceCategory
    payload := .computed parameter (.owned "presentation-fixture" 73 parameterData) }
  harness.results.modify (·.insert parameter parameterWire)
  let named ← Realize.objectAt trace entry #[parameter]
  let some plan ← ObjectPresentation.plan entry #[parameter] (some trace)
    | throwError "the registered object has no complete formal presentation plan"
  let (image, imageCategory) ← Semantic.applyRegisteredFunctor action plan.argument #[] (some trace)
  let actualData := node "opaqueData" #[toJson "actual computed units"]
  let actualImage : Realize.Wire := {
    form := .functorImage action imageCategory.id
    payload := .computed image (.owned "presentation-fixture" 73 actualData) }
  harness.results.modify (·.insert image actualImage)
  let actual ← Realize.realize harness trace "the named computed presentation" named
  unless actual.owner? == parameterWire.owner? && actual.form.id == entry.id.raw do
    throwError "the named presentation dropped its complete input or result ownership"
  unless ← withTransparency .all <| isDefEq actual.value named do
    throwError "computational presentation data changed the fixed named object"
  let some retained := actual.endpointPresentation
    | throwError "the computational object discarded its accepted comparison"
  let fieldData := fun (selector : String) => node "objectField"
    #[toJson entry.id.raw, toJson selector, Json.arr #[parameterData]]
  unless retained.forward == fieldData "inversePresentation" &&
      retained.backward == fieldData "presentation" do
    throwError "the object comparison lost its direction or complete parameter data"
  let mapped ← Realize.transportImage trace actualImage published.route (some plan.applications)
  unless actual.json == mapped.json do
    throwError "the named presentation replaced actual returned data or a selected action"
  for selector in #["presentation", "inversePresentation"] do
    let arrow ← ObjectPresentation.field entry selector #[parameter] (some trace)
    let wire ← Realize.realize harness trace "a declared presentation direction" arrow
    unless wire.json == fieldData selector && wire.owner? == parameterWire.owner? do
      throwError "a public presentation direction changed its full parameters or owner"
    if let .error message ← ComputationalData.validatePublicData wire.json then
      throwError "public comparison framing rejected an accepted direction: {message}"
    if let .error message ← ComputationalData.validatePort arrow (← inferType arrow) wire.json then
      throwError "fixed comparison framing rejected an accepted direction: {message}"
    if let .error message ← ComputationalData.validateCallableAt #[(parameterData, parameter)]
        (← inferType arrow) wire.json then
      throwError "complete comparison endpoints rejected an accepted direction: {message}"
    if (← ComputationalData.validatePublicData
        (node "objectField" #[toJson entry.id.raw, toJson selector, Json.arr #[]])).isOk then
      throwError "a public comparison omitted a required selected parameter"
  let inclusion ← ObjectPresentation.field entry "inclusion" #[parameter] (some trace)
  let inclusionWire ← Realize.realize harness trace "the computed object's inclusion" inclusion
  let some (domain, ambient) := Language.homEnds? (← inferType inclusion)
    | throwError "the accepted inclusion has no complete endpoints"
  harness.results.modify (·.insert domain
    { actual with payload := Realize.forwardPayload actual domain actual.json })
  let (included, endpoints) ← Realize.frameMorphismData harness trace domain ambient inclusionWire
  unless included == node "compose" #[fieldData "presentation", inclusionWire.json] do
    throwError "the inclusion omitted its inverse domain comparison or replaced its original arrow"
  let some ambientWire := endpoints[1]? | throwError "the inclusion omitted its actual ambient endpoint"
  unless ambientWire.json == Backend.MorphismEndpoint.encode
      { callable := inclusionWire.json, source := false } do
    throwError "an unnamed ambient object lost the endpoint of its complete inclusion"
  if let .error message ← ComputationalData.validatePublicData ambientWire.json then
    throwError "the complete unnamed inclusion endpoint was rejected: {message}"
  if let .error message ← ComputationalData.validatePort ambient (← inferType ambient) ambientWire.json then
    throwError "the unnamed endpoint lost its independently fixed categorical type: {message}"
  harness.results.modify (·.insert ambient ambientWire)
  let some power := state.powerObjects.find? (·.object.raw == "obj.sets.power_set")
    | throwError "the accepted membership family is unavailable"
  let member ← mkAppM power.member #[ambient]
  Trace.record (some trace) member (.powerObjectMap power.id "member" #[ambient])
  let memberWire ← Realize.realize harness trace "membership at a computed ambient object" member
  unless memberWire.json == node "powerObjectMap"
      #[toJson power.id.raw, toJson "member", Json.arr #[ambientWire.json]] &&
      memberWire.owner? == parameterWire.owner? do
    throwError "membership dropped the complete computed ambient or its owner"

-- An infinite/opaque actual arrow is transported whole through a nonidentity
-- accepted comparison, in both directions. Equalities of carriers never select it.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some row := state.presentations.find? (·.id.raw == "cmp.f9.translation")
    | throwError "the existing nonidentity comparison is unavailable"
  let iso ← ObjectPresentation.applyParameters row.declaration #[]
  let some object := state.objects.find? (·.id == row.source)
    | throwError "the accepted comparison source is unavailable"
  let some category := state.categories.find? (·.id == object.category)
    | throwError "the accepted comparison category is unavailable"
  let descriptor := fun (inverse : Bool) => node "presentation"
    #[toJson row.id.raw, Json.arr #[], toJson inverse]
  for inverse in #[false, true] do
    let comparison ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[iso] else pure iso
    let reverse ← mkAppM ``CategoryTheory.Iso.symm #[comparison]
    let hom ← Semantic.presentationArrow row iso inverse (some trace)
    let some (source, target) := Language.homEnds? (← inferType hom)
      | throwError "the accepted comparison lost its categorical endpoints"
    let sourceWire : Realize.Wire := {
      form := .diagrams category
      payload := .computed source (.owned "presentation-fixture" 91
        (node "opaqueData" #[toJson "actual source representation"]))
      endpointPresentation := some {
        comparison := comparison
        forward := descriptor inverse, backward := descriptor (!inverse) } }
    let targetWire : Realize.Wire := {
      form := .diagrams category
      payload := .computed target (.inline
        (node (if inverse then row.target.raw else row.source.raw) #[]))
      endpointPresentation := some {
        comparison := reverse
        forward := descriptor (!inverse), backward := descriptor inverse } }
    let input : Realize.Wire := {
      form := .canonicalMorphism category
      payload := .computed hom (.owned "presentation-fixture" 91
        (node "opaqueData" #[toJson "unchanged actual callable"])) }
    let transported ← Realize.presentMorphism input sourceWire targetWire
    let expected := node "compose"
      #[node "compose" #[descriptor (!inverse), input.json], descriptor (!inverse)]
    unless transported.json == expected && transported.owner? == input.owner? &&
        transported.value == input.value do
      throwError "whole-arrow transport changed its original callable, directions, request or owner"
    unless (← Realize.presentMorphism transported sourceWire targetWire).json == expected do
      throwError "nested composition applied an endpoint presentation twice"
    let wrongSource := { sourceWire with
      endpointPresentation := some {
        comparison := reverse
        forward := descriptor (!inverse), backward := descriptor inverse } }
    let wrongEnds ← try
      discard <| Realize.presentMorphism input wrongSource targetWire
      pure false
    catch _ => pure true
    unless wrongEnds do
      throwError "whole-arrow transport accepted a comparison at different complete endpoints"
    let relabeledPortable := { targetWire with
      payload := .computed target (.owned "foreign-presentation" 92 targetWire.json) }
    unless relabeledPortable.ownership.isEmpty do
      throwError "a portable endpoint acquired a supplier from its wrapper label"
    let replayed ← Realize.presentMorphism input sourceWire relabeledPortable
    unless replayed.fragment == transported.fragment && replayed.value == transported.value do
      throwError "a portable endpoint label changed whole-arrow transport"
    let callable ← Realize.checkedFragment (replayed.fragment.project
      #[.field "args", .index 0, .field "args", .index 1])
    unless callable == input.fragment do
      throwError "whole-arrow transport changed the exact retained callable occurrence"

-- A selected action can carry the only live dependency. Its complete parameter
-- is encoded from the cached computation, not regenerated from the formal ring.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Realize.Harness.empty
  let some entry := state.functor? FunctorId.modulesFibreInclusion
    | throwError "the accepted parameterized action is unavailable"
  let ring ← elabTermAndSynthesize (← `(RingCat.of (ZMod 4))) none
  let action ← ObjectPresentation.applyParameters entry.declaration #[ring]
  let parameterData := node "opaqueData" #[toJson "actual action parameter"]
  let some category := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the accepted parameter category is unavailable"
  let parameter : Realize.Wire := {
    form := .diagrams category
    payload := .computed ring (.owned "parameter-fixture" 108 parameterData) }
  harness.results.modify (·.insert ring parameter)
  let (descriptor, dependencies) ← Realize.realizedEdgeDescriptor harness trace (.functor entry.id) action
  unless descriptor == node entry.id.raw #[parameterData] && dependencies.size == 1 do
    throwError "the complete action lost its actual parameter data or dependency"
  let input ← elabTermAndSynthesize
    (← `(ModuleCat.of (RingCat.of (ZMod 4)) (ZMod 4))) none
  let hom ← mkAppM ``CategoryTheory.CategoryStruct.id #[input]
  let output ← Semantic.mapOf action hom
  let sourceCategory ← Semantic.namedCategoryFor state entry.source
  let targetCategory ← Semantic.namedCategoryFor state entry.target
  let sourceData := node "obj.modules.regular" #[node "obj.rings.integers_mod" #[toJson (4 : Nat)]]
  let callable := node "identity" #[sourceData, sourceData]
  let original : Realize.Wire := {
    form := .canonicalMorphism sourceCategory, payload := .ordinary hom callable }
  harness.results.modify (·.insert hom original)
  Trace.record (some trace) output
    (.morphismTransport sourceCategory.id targetCategory.id #[.functor entry.id] hom)
  let transported ← Realize.realize harness trace "the action with an owned parameter" output
  unless transported.json == node "map" #[descriptor, callable] &&
      transported.owner? == parameter.owner? do
    throwError "morphism transport discarded the action parameter's sole owning session"

end CasAcceptance.Kernel.ObjectPresentationProbes
