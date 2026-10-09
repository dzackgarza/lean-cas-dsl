module

public meta import CasCatalogue.LiftedSubobjectData
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
  let sourceData := Json.mkObj [("ctor", toJson "typedSourceFixture"),
    ("args", Json.arr #[toJson "complete selected zero form on integer pairs"])]
  let baseData := Json.mkObj [("ctor", toJson "typedBaseFixture"),
    ("args", Json.arr #[toJson "arbitrary computational claim"])]
  let envelope (ids : Array Json) (data : Json := baseData) :=
    Json.mkObj [("ctor", toJson "liftedSubobject"),
      ("args", Json.arr #[data, sourceData, Json.arr ids])]
  let sourceValidator (source : CategoryExpr) (fixed : Expr) (data : Json) :
      TermElabM (Except String Unit) := do
    let some edge := (state.edgesFrom source).find? (·.ref == row.edge)
      | return .error "no accepted structural edge"
    unless source.syntacticEq edge.source && data == sourceData do
      return .error "source descriptor changed"
    unless ← withTransparency .all <| isDefEq fixed receiver do
      return .error "independently fixed source changed"
    return .ok ()
  let baseValidator (category : NamedCategoryEntry) (fixed : Expr) (data : Json) :
      TermElabM (Except String Unit) := do
    unless category.id.raw == "cat.subobjects_modules_r" &&
        (data.getObjValAs? String "ctor").toOption == some "typedBaseFixture" do
      return .error "base framing or category changed"
    let .ok #[_] := (data.getObjVal? "args").bind (·.getArr?)
      | return .error "base data field omitted"
    unless ← withTransparency .all <| isDefEq fixed base do
      return .error "independently fixed base changed"
    return .ok ()
  let decode data := LiftedSubobjectData.decode expectedType sourceCategory receiver
    #[row.id] base data sourceValidator baseValidator
  let good := envelope #[toJson row.id.raw]
  let some (.ok packet) ← decode good
    | throwError "complete computational packet rejected"
  unless packet.data == good && packet.sourceData == sourceData && packet.baseData == baseData do
    throwError "opaque computational fields were replaced"
  unless ← withTransparency .all <| isDefEq packet.formalResult expectedLifted do
    throwError "opaque data changed the independent formal construction"
  let #[component] := packet.components
    | throwError "the prescribed route lost a required callable plan"
  unless component.lift == row.id && component.routeIndex == 0 &&
      some component.declaration == row.computation do
    throwError "callable plan changed the prescribed public computation"
  unless ← withTransparency .all <| isDefEq component.receiver receiver do
    throwError "callable plan changed the selected source"
  unless ← withTransparency .all <| isDefEq component.base base do
    throwError "callable plan changed the selected base"
  for port in #[component.obj, component.hom, component.forward, component.backward] do
    discard <| StructuredResult.checkReconstruction port
  -- Wrong answers are permitted computational claims, not formal terms or proofs.
  let wrongData := Json.mkObj [("ctor", toJson "typedBaseFixture"),
    ("args", Json.arr #[toJson "well-formed mathematically wrong answer"])]
  let wrong := envelope #[toJson row.id.raw] wrongData
  let some (.ok wrongPacket) ← decode wrong
    | throwError "a well-formed wrong computational claim was certified or rejected"
  unless wrongPacket.baseData == wrongData do
    throwError "a wrong computational claim was replaced by a canonical result"
  unless ← withTransparency .all <| isDefEq wrongPacket.formalResult packet.formalResult do
    throwError "computational truth changed formal meaning"
  let #[wrongComponent] := wrongPacket.components
    | throwError "wrong data changed callable availability"
  for (before, after) in #[(component.obj, wrongComponent.obj),
      (component.hom, wrongComponent.hom), (component.forward, wrongComponent.forward),
      (component.backward, wrongComponent.backward), (component.action, wrongComponent.action)] do
    unless ← withTransparency .all <| isDefEq before after do
      throwError "computational data changed a complete formal port or selected map action"
  let malformed := Json.mkObj [("ctor", toJson "liftedSubobject"),
    ("args", Json.arr #[baseData, sourceData])]
  let missingBase := Json.mkObj [("ctor", toJson "typedBaseFixture"),
    ("args", Json.arr #[])]
  for invalid in #[malformed, envelope #[], envelope #[toJson "unregistered.lift"],
      envelope #[toJson row.id.raw, toJson row.id.raw],
      envelope #[toJson row.id.raw] missingBase] do
    let some result ← decode invalid
      | throwError "malformed lifted envelope not recognized"
    if result.isOk then throwError "malformed framing or prescribed route accepted"
  let some other := state.lifts.find? (·.id != row.id)
    | throwError "missing alternate metadata fixture"
  let some changedOrder ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id, other.id] base (envelope #[toJson other.id.raw, toJson row.id.raw])
      sourceValidator baseValidator
    | throwError "reordered route not recognized"
  if changedOrder.isOk then throwError "independent prescribed order changed"
  let wrongBase ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ ℤ)), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ ℤ)); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let some wrongContext ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id] wrongBase good sourceValidator baseValidator
    | throwError "wrong fixed base context not recognized"
  if wrongContext.isOk then throwError "a different complete fixed base ambient accepted"
  let some wrongSource ← LiftedSubobjectData.decode expectedType sourceCategory X
      #[row.id] base good sourceValidator baseValidator
    | throwError "wrong fixed source context not recognized"
  if wrongSource.isOk then throwError "a source without its complete arrow accepted"
  logInfo "PASS: opaque lift packet, fixed contexts, exact public callable plans and malformed framing; well-formed wrong data preserves formal meaning"
