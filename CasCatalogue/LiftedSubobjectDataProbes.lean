module

public meta import CasCatalogue.Realize
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Catalogue.Semantics.Limits.Lifts
public import Mathlib.Algebra.Algebra.Bilinear

/-! Engineering checks of opaque packet framing and independently fixed callable plans.
Computational claims are never decoded into categorical laws or accepted proofs. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue

run_elab do
  let state ← registryState
  let some sourceCategory := state.categories.find?
      (·.id.raw == "cat.subobjects_bilin_module")
    | throwError "missing accepted formed-module subobject category"
  let X ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ))) none
  let selectedSource ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleCategory ℤ ℤ)) none
  let selectedCarrier ← mkAppM ``CategoryTheory.Bundled.α #[selectedSource]
  let selectedX ← mkExpectedTypeHint X selectedCarrier
  let L ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift ℤ ℤ)) none
  let liftType ← whnfR (← inferType L)
  let #[_, selectedCategory, _, _, _] := liftType.getAppArgs
    | throwError "the closed accepted lift fixture has no full source category dictionary"
  let sourceArrow ← mkAppOptM ``CategoryTheory.Arrow
    #[some selectedCarrier, some selectedCategory]
  let sourceStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some selectedCarrier, some selectedCategory]
  let identity ← mkAppOptM ``CategoryTheory.CategoryStruct.id
    #[some selectedCarrier, some sourceStruct, some selectedX]
  let receiver ← mkExpectedTypeHint
    (← mkAppOptM ``CategoryTheory.Arrow.mk
      #[some selectedCarrier, some selectedCategory, some selectedX,
        some selectedX, some identity]) sourceArrow
  let base ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let some row := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "missing accepted formed-module lift"
  let expectedLifted ← Semantic.liftSubobject state row receiver base
  let expectedType ← inferType expectedLifted
  let .ok prepared ← LiftedSubobjectData.plan expectedType sourceCategory receiver #[row.id] base
    | throwError "the existing selected formal lift has no complete public port plan"
  let #[component] := prepared.components
    | throwError "the exact selected route lost its required component"
  unless component.ports.size == 4 do throwError "the public computation lost a field"
  for port in component.ports do
    discard <| StructuredResult.checkReconstruction port
    unless ← isTypeCorrect port do throwError "a full selected computation port is ill-typed"
  let some form := state.form? row.inputAddress
    | throwError "the published lift input form was not admitted"
  for field in LiftField.all do
    let some operation := state.operation? (row.fieldAddress field)
      | throwError "a public computation field has no concrete operation address"
    unless (state.rejects operation form).isNone do
      throwError "a public lift field was rejected on its own complete input"
    unless (state.rejects operation (.subobject sourceCategory)).isSome do
      throwError "a public lift field accepted an unrelated subobject input"
  let wrongSource ← LiftedSubobjectData.plan expectedType sourceCategory X #[row.id] base
  if wrongSource.isOk then throwError "a lift accepted a source without its complete Arrow type"
  let wrongRoute ← LiftedSubobjectData.plan expectedType sourceCategory receiver
    #[⟨"unregistered.lift"⟩] base
  if wrongRoute.isOk then throwError "a lift accepted a route outside the fixed catalogue"
  let trace ← CasCatalogue.Trace.new
  let .constructMap _ inner := row.edge
    | throwError "the registered lift lost its selected inner action"
  let action ← Realize.edgeDescriptor trace inner component.action
  let data (token : String) := Json.mkObj [("ctor", "opaqueData"),
    ("args", Json.arr #[toJson token])]
  let ambient := data "source object"
  let sourceData := Json.mkObj [("ctor", "arrow"),
    ("args", Json.arr #[ambient, ambient, data "source map"])]
  let image value := Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[action, value])]
  let baseData := Json.mkObj [("ctor", "subobject"),
    ("args", Json.arr #[data "base apex", data "base ambient", data "base inclusion"])]
  let objectData := data "actual returned object"
  let typedMap source target callable := Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[source, target, callable])]
  let outputs := #[objectData, typedMap objectData ambient (data "actual inclusion"),
    typedMap (image objectData) (data "base apex") (data "actual forward callable"),
    typedMap (data "base apex") (image objectData) (data "actual backward callable")]
  let step fields := Json.mkObj [("ctor", "liftStep"), ("args", Json.arr #[
    toJson row.id.raw, action, sourceData, baseData, Json.arr fields])]
  let envelope fields := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
    baseData, sourceData, toJson #[row.id.raw], Json.arr #[step fields]])]
  let validateSource (_ : CategoryExpr) (fixed : Expr) (data : Json) := do
    ComputationalData.validatePort fixed (← inferType fixed) data
  let validateBase (_ : NamedCategoryEntry) (fixed : Expr) (data : Json) := do
    ComputationalData.validatePort fixed (← inferType fixed) data
  let decode json := LiftedSubobjectData.decode expectedType sourceCategory receiver
    #[row.id] base json validateSource validateBase
  let checked ← decode (envelope outputs)
  let packet ← match checked with
    | some (.ok packet) => pure packet
    | some (.error message) => throwError "complete opaque computational claims rejected: {message}"
    | none => throwError "complete lifted data was not recognized"
  unless packet.outputs == #[outputs] && packet.data == envelope outputs do
    throwError "a complete lift discarded or replaced an actual returned field"
  unless ← withTransparency .all <| isDefEq packet.formalResult expectedLifted do
    throwError "computational claims changed the independently fixed formal result"
  let .ok next := LiftedSubobjectData.nextBase sourceData outputs
    | throwError "the actual completed fields could not advance the reverse route"
  let .ok fields := LiftedSubobjectData.fields "subobject" 3 next
    | throwError "the next actual base lost its complete subobject context"
  unless fields[0]! == objectData && fields[2]! == data "actual inclusion" && next != baseData do
    throwError "the next step repeated the initial base instead of the actual preceding outputs"
  let incomplete := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
    baseData, sourceData, toJson #[row.id.raw]])]
  let wrongEndpoints := outputs.set! 2
    (typedMap (data "unrelated object") (data "base apex") (data "wrong-domain callable"))
  for invalid in #[incomplete, envelope #[], envelope (outputs.extract 0 3),
      envelope wrongEndpoints] do
    let some result ← decode invalid | throwError "malformed completed framing was not recognized"
    if result.isOk then throwError "an incomplete or wrong-domain component was accepted"
  -- Neither returned object nor callable claims are forced to agree with a canonical answer.
  let wrongObject := data "well-framed mathematically wrong object"
  let wrongOutputs := #[wrongObject, typedMap wrongObject ambient (data "wrong inclusion"),
    typedMap (image wrongObject) (data "base apex") (data "wrong forward"),
    typedMap (data "base apex") (image wrongObject) (data "wrong backward")]
  let some (.ok wrong) ← decode (envelope wrongOutputs)
    | throwError "well-framed wrong data was rejected or certified at the computational boundary"
  unless wrong.outputs == #[wrongOutputs] do
    throwError "wrong computational data was replaced with a canonical result"
  unless ← withTransparency .all <| isDefEq wrong.formalResult packet.formalResult do
    throwError "actual computational claims changed the fixed mathematical question"
  -- The production executor must demand registered execution for the public fields.
  let harness ← Realize.Harness.empty
  let sourceWire : Realize.Wire := {
    form := .arrow (← Semantic.namedCategoryFor state prepared.sourceCategory),
    payload := .ordinary receiver sourceData }
  let baseWire : Realize.Wire := {
    form := .subobject prepared.baseCategory, payload := .ordinary base baseData }
  let missing ← try
      discard <| Realize.executePrescribedLift harness trace prepared sourceWire baseWire
      pure false
    catch error =>
      if CasCatalogue.Exception.stratum? error == some .noImplementation then pure true
      else throw error
  unless missing do throwError "the executor claimed a completed lift without registered execution"
