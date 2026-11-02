module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

/- These checks exercise the published differential and infinite-subset response
interfaces. Arbitrary opaque data assert no mathematical answer or law. -/
run_elab do
  let state ← registryState
  let sets ← Language.categoryNamed state "Sets"
  let node := fun (tag : String) (args : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let named := fun id => do
    let some row := state.objects.find? (·.id.raw == id)
      | throwError "the public object fixture {id} is absent"
    instantiateFresh row.declaration
  let callable := fun id parameters => do
    let some row := state.morphisms.find? (·.id.raw == id)
      | throwError "the public callable fixture {id} is absent"
    mkAppM row.declaration parameters
  let trace ← Trace.new
  let h ← Harness.empty
  let domain ← Language.globalPointSource.run {}
  discard <| Semantic.recordNamedObject domain (some trace)
  let domainData := (← realizeEndpoint h trace "the declared point source" domain).json
  let ring ← named "obj.commutative_rings.rationals"
  let ringData := node "obj.commutative_rings.rationals" #[]
  let coordinate ← callable "mor.sets.kaehler_from_coordinate" #[ring]
  let some (polynomials, differentials) := Language.homEnds? (← inferType coordinate)
    | throwError "the differential coordinate lost its complete public map type"
  let polynomialData := node "obj.sets.polynomials" #[ringData]
  let differentialData := node "obj.sets.kaehler_polynomials" #[ringData]
  let fixed ← callable "mor.sets.kaehler_dx" #[ring]
  let coordinateData := node "mor.sets.kaehler_from_coordinate" #[ringData]
  let pointData := node "typedMap" #[domainData, polynomialData,
    node "opaqueData" #[toJson "actual polynomial coordinate"]]
  let reply := fun arrow => node "valueData" #[node "element" #[differentialData,
    node "point" #[arrow]]]
  let complete := reply (node "compose" #[pointData, coordinateData])
  if let .error message ← ComputationalData.validateElementAt differentials
      differentialData fixed complete then
    throwError "the complete public differential response was rejected: {message}"
  let .ok decoded ← decodeArrowData trace sets coordinateData
    | throwError "the complete coordinate declaration did not decode"
  unless ← withTransparency .all <| isDefEq decoded coordinate do
    throwError "coordinate decoding changed its selected ring or complete map"
  for bad in #[node "mor.sets.kaehler_from_coordinate" #[],
      node "mor.sets.kaehler_from_coordinate"
        #[node "obj.commutative_rings.integers" #[]],
      node "mor.sets.kaehler_coordinate" #[ringData]] do
    let .error _ ← ComputationalData.validateElementAt differentials differentialData fixed
        (reply (node "compose" #[pointData, bad]))
      | throwError "a differential response changed a parameter or reversed its coordinate map"
  let .error _ ← ComputationalData.validateElementAt differentials differentialData fixed
      (reply coordinateData)
    | throwError "a nonconstant coordinate map was accepted as a global differential"
  unless ← withTransparency .all <| isDefEq (← inferType polynomials) (← inferType differentials) do
    throwError "the public coordinate fixture changed category"

run_elab do
  let state ← registryState
  let sets ← Language.categoryNamed state "Sets"
  let node := fun (tag : String) (args : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let some integers := state.objects.find? (·.id.raw == "obj.sets.integers")
    | throwError "the infinite-domain fixture is absent"
  let some power := state.powerObjects.find? (·.id.raw == "pow.sets")
    | throwError "the published power-object interface is absent"
  let some powers := state.objects.find? (·.id == power.object)
    | throwError "the power-object family is absent"
  let some truth := state.objects.find? (·.id == power.omega)
    | throwError "the power object's truth-value object is absent"
  let ambient ← instantiateFresh integers.declaration
  let selected ← mkAppM powers.declaration #[ambient]
  let truthObject ← instantiateFresh truth.declaration
  let ambientData := node integers.id.raw #[]
  let selectedData := node powers.id.raw #[ambientData]
  let truthData := node truth.id.raw #[]
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[ambient]
  let identityData := node "identity" #[ambientData, ambientData]
  let fixedImage ← mkAppM power.image #[ambient, ambient, identity]
  let imageData := fun mapData => node "powerObjectMap" #[toJson power.id.raw, toJson "image",
    Json.arr #[ambientData, ambientData, mapData]]
  let owned := fun token => node "opaqueData" #[toJson (token : String)]
  let nativeMap := node "typedMap" #[ambientData, ambientData, owned "infinite map"]
  let reply := fun point => node "valueData" #[node "element" #[selectedData,
    node "point" #[point]]]
  for mapData in #[identityData, nativeMap] do
    if let .error message ← ComputationalData.validateElementAt selected selectedData fixedImage
        (reply (imageData mapData)) then
      throwError "the complete infinite image response was rejected: {message}"
  let trace ← Trace.new
  let .ok decoded ← decodeArrowData trace sets (imageData identityData)
    | throwError "the complete infinite-image declaration did not decode"
  unless ← withTransparency .all <| isDefEq decoded fixedImage do
    throwError "infinite-image decoding changed its full parameter map"
  let predicateType ← mkAppM ``Quiver.Hom #[ambient, truthObject]
  let predicate ← elabTermAndSynthesize (← `(TypeCat.ofHom (fun _ : Int => True)))
    (some predicateType)
  let fixedTranspose ← mkAppM power.transpose #[ambient, predicate]
  let predicateData := node "typedMap" #[ambientData, truthData, owned "infinite predicate"]
  let transposeData := node "powerObjectMap" #[toJson power.id.raw, toJson "transpose",
    Json.arr #[ambientData, predicateData]]
  if let .error message ← ComputationalData.validateElementAt selected selectedData fixedTranspose
      (reply transposeData) then
    throwError "the complete infinite predicate response was rejected: {message}"
  for bad in #[node "powerObjectMap" #[toJson power.id.raw, toJson "image",
        Json.arr #[ambientData, ambientData]],
      imageData predicateData,
      node "powerObjectMap" #[toJson power.id.raw, toJson "transpose",
        Json.arr #[ambientData, nativeMap]],
      node "powerObjectMap" #[toJson power.id.raw, toJson "transpose",
        Json.arr #[ambientData]],
      node "powerObjectMap" #[toJson power.id.raw, toJson "undeclaredField",
        Json.arr #[ambientData, nativeMap]]] do
    let .error _ ← ComputationalData.validateElementAt selected selectedData fixedImage (reply bad)
      | throwError "an infinite-subset response changed a declared map type, field or arity"
