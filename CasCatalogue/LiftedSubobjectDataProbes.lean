module

public meta import CasCatalogue.LiftedSubobjectData
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Catalogue.Semantics.Limits.Lifts
public import Mathlib.Algebra.Algebra.Bilinear

/-! Engineering checks of envelope replay with independently supplied typed decoder fixtures.
The fixtures contain existing selected objects and categorical data, not backend evidence. -/

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
  let e ← elabTermAndSynthesize (← `((LinearEquiv.prodComm ℤ ℤ ℤ).toModuleIso)) none
  let returned ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk $(← exprToSyntax (← mkAppM ``CategoryTheory.Iso.inv #[e])), (by
      change Mono $(← exprToSyntax (← mkAppM ``CategoryTheory.Iso.inv #[e]))
      letI := CategoryTheory.Iso.isIso_inv $(← exprToSyntax e)
      infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let .ok baseIso ← StructuredResult.subobjectComparison base returned e
      (← mkAppM ``CategoryTheory.Iso.hom_inv_id #[e])
    | throwError "the accepted full base comparison did not assemble"
  let some row := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "missing accepted formed-module lift"
  let expectedLifted ← Semantic.liftSubobject state row receiver base
  let actualLifted ← Semantic.liftSubobject state row receiver returned
  let expectedType ← inferType expectedLifted
  let sourceData := Json.mkObj [("ctor", toJson "typedSourceFixture"),
    ("args", Json.arr #[toJson "identity", toJson "complete selected zero form on integer pairs"])]
  let baseData := Json.mkObj [("ctor", toJson "typedBaseFixture"),
    ("args", Json.arr #[toJson "integer pairs", toJson "integer pairs", toJson "swap inclusion"])]
  let envelope (ids : Array Json) := Json.mkObj [("ctor", toJson "liftedSubobject"),
    ("args", Json.arr #[baseData, sourceData, Json.arr ids])]
  let good := envelope #[toJson row.id.raw]
  let sourceDecoder (source : CategoryExpr) (type : Expr) (json : Json) := do
    let some edge := (state.edgesFrom source).find? (·.ref == row.edge)
      | return .error "the fixture has no accepted structural edge"
    unless source.syntacticEq edge.source && json == sourceData do
      return .error "the fixture source context or complete reply changed"
    unless ← withTransparency .all <| isDefEq (← inferType receiver) type do
      return .error "the fixture source has different complete type parameters"
    return .ok (receiver, none)
  let baseDecoder (category : NamedCategoryEntry) (type : Expr) (json : Json) := do
    unless category.id.raw == "cat.subobjects_modules_r" && json == baseData do
      return .error "the fixture base context or complete reply changed"
    unless ← withTransparency .all <| isDefEq (← inferType returned) type do
      return .error "the fixture base has different complete type parameters"
    return .ok (returned, some baseIso)
  let some result ← LiftedSubobjectData.decode expectedType sourceCategory receiver #[row.id] good
      sourceDecoder baseDecoder
    | throwError "the complete lifted envelope was not recognized"
  let (value, retained) ← match result with
    | .error message => throwError "full selected envelope replay failed: {message}"
    | .ok result => pure result
  unless ← withTransparency .all <| isDefEq value actualLifted do
    throwError "the replay replaced the actual selected form or defining inclusion"
  let some retained := retained | throwError "the replay dropped its complete base comparison"
  let wanted ← mkAppM ``CategoryTheory.Iso #[expectedLifted, actualLifted]
  unless ← withTransparency .all <| isDefEq (← inferType retained) wanted do
    throwError "the replay comparison has different complete chosen endpoints"
  for data in #[value, retained, ← mkAppM ``CategoryTheory.Iso.hom_inv_id #[retained],
      ← mkAppM ``CategoryTheory.Iso.inv_hom_id #[retained]] do
    discard <| StructuredResult.checkReconstruction data
  let ambientSwap ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.isoMk
      (L := $(← exprToSyntax X)) (M := $(← exprToSyntax X))
      (LinearEquiv.prodComm ℤ ℤ ℤ) (fun _ _ => rfl))) none
  let ambientHom ← mkAppM ``CategoryTheory.Iso.hom #[ambientSwap]
  let sourceSquare ← mkEqTrans
    (← mkAppM ``CategoryTheory.Category.comp_id #[ambientHom])
    (← mkEqSymm (← mkAppM ``CategoryTheory.Category.id_comp #[ambientHom]))
  let sourceSwap ← withTransparency .all <| mkAppOptM ``CategoryTheory.Arrow.isoMk
    #[some selectedCarrier, some selectedCategory, some receiver, some receiver,
      some ambientSwap, some ambientSwap, some sourceSquare]
  let U ← elabTermAndSynthesize (← `(LeanCategories.Modules.Bilinear.Valued.forget ℤ ℤ)) none
  let mappedSwap ← LiftedSubobjectData.mapComparison U ambientSwap
  let baseArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[base]
  let baseArrowSwap ← elabTermAndSynthesize (← `(
    CategoryTheory.Arrow.isoMk (f := $(← exprToSyntax baseArrow))
      (g := $(← exprToSyntax baseArrow)) $(← exprToSyntax mappedSwap)
      $(← exprToSyntax mappedSwap) (by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        simp only [Category.comp_id, Category.id_comp]))) none
  let fullBaseSwap ← elabTermAndSynthesize (← `(
    CategoryTheory.ObjectProperty.isoMk
      (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)
      (X := $(← exprToSyntax base)) (Y := $(← exprToSyntax base))
      $(← exprToSyntax baseArrowSwap))) none
  let ambientSourceDecoder (source : CategoryExpr) (type : Expr) (json : Json) := do
    let .ok _ ← sourceDecoder source type json | return .error "source context changed"
    return .ok (receiver, some sourceSwap)
  let ambientBaseDecoder (category : NamedCategoryEntry) (type : Expr) (json : Json) := do
    let .ok _ ← baseDecoder category type json | return .error "base context changed"
    return .ok (base, some fullBaseSwap)
  let some ambientResult ← LiftedSubobjectData.decode expectedType sourceCategory receiver #[row.id] good
      ambientSourceDecoder ambientBaseDecoder
    | throwError "the nonidentity complete source comparison envelope was not recognized"
  match ambientResult with
  | .error message => throwError "nonidentity full source envelope replay failed: {message}"
  | .ok (value, comparison) =>
      unless ← withTransparency .all <| isDefEq value expectedLifted do
        throwError "the ambient replay replaced the actual prescribed defining map"
      let some comparison := comparison | throwError "ambient replay dropped its full comparison"
      let wanted ← mkAppM ``CategoryTheory.Iso #[expectedLifted, expectedLifted]
      unless ← withTransparency .all <| isDefEq (← inferType comparison) wanted do
        throwError "the source replay comparison changed its full chosen endpoints"
      for proof in #[comparison, ← mkAppM ``CategoryTheory.Iso.hom_inv_id #[comparison],
          ← mkAppM ``CategoryTheory.Iso.inv_hom_id #[comparison]] do
        discard <| StructuredResult.checkReconstruction proof
  for invalid in #[envelope #[], envelope #[toJson "unregistered.lift"],
      envelope #[toJson row.id.raw, toJson row.id.raw]] do
    let some result ← LiftedSubobjectData.decode expectedType sourceCategory receiver #[row.id] invalid
        sourceDecoder baseDecoder
      | throwError "a malformed lifted envelope was not recognized"
    if result.isOk then throwError "an absent, unregistered or noncomposable lift sequence was accepted"
  let differentForm ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      ((LinearMap.mul ℤ ℤ).compl₁₂
        (LinearMap.fst ℤ ℤ ℤ) (LinearMap.fst ℤ ℤ ℤ)))) none
  let selectedDifferent ← mkExpectedTypeHint differentForm selectedCarrier
  let wrongIdentity ← mkAppOptM ``CategoryTheory.CategoryStruct.id
    #[some selectedCarrier, some sourceStruct, some selectedDifferent]
  let wrongReceiver ← mkExpectedTypeHint
    (← mkAppOptM ``CategoryTheory.Arrow.mk
      #[some selectedCarrier, some selectedCategory, some selectedDifferent,
        some selectedDifferent, some wrongIdentity]) sourceArrow
  unless ← withTransparency .all <| isDefEq
      (← Semantic.objOf U X) (← Semantic.objOf U differentForm) do
    throwError "the negative fixture does not retain the same module carrier"
  if ← withoutModifyingState <| withTransparency .all <| isDefEq X differentForm then
    throwError "the negative fixture does not retain different chosen pairings"
  let changedSourceDecoder (_ : CategoryExpr) (_ : Expr) (_ : Json) := do
    return .ok (wrongReceiver, none)
  let some changedSource ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id] good changedSourceDecoder baseDecoder
    | throwError "the changed original source envelope was not recognized"
  if changedSource.isOk then
    throwError "a different original selected source in the identical full category was accepted"
  let missingMapDecoder (_ : CategoryExpr) (_ : Expr) (_ : Json) := do
    return .ok (X, none)
  let some missingMap ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id] good missingMapDecoder baseDecoder
    | throwError "the missing complete source arrow was not recognized"
  if missingMap.isOk then throwError "a source without its original defining map was accepted"
  let wrongBase ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ ℤ)), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ ℤ)); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let wrongAmbientDecoder (_ : NamedCategoryEntry) (_ : Expr) (_ : Json) := do
    return .ok (wrongBase, none)
  let some wrongAmbient ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id] good sourceDecoder wrongAmbientDecoder
    | throwError "the changed full base ambient was not recognized"
  if wrongAmbient.isOk then throwError "a base inclusion into a different full module ambient was accepted"
  let bareBase ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[base]
  let missingBaseMapDecoder (_ : NamedCategoryEntry) (_ : Expr) (_ : Json) := do
    return .ok (bareBase, none)
  let some missingBase ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id] good sourceDecoder missingBaseMapDecoder
    | throwError "the incomplete subobject reply was not recognized"
  if missingBase.isOk then throwError "a reply without full subobject defining-map data was accepted"
  let some other := state.lifts.find? (·.id != row.id)
    | throwError "the registered alternate lift metadata negative has no distinct id"
  let some changedId ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id] (envelope #[toJson other.id.raw]) sourceDecoder baseDecoder
    | throwError "the changed prescribed registered lift was not recognized"
  if changedId.isOk then throwError "an alternate registered lift replaced the prescribed datum"
  let some changedOrder ← LiftedSubobjectData.decode expectedType sourceCategory receiver
      #[row.id, other.id] (envelope #[toJson other.id.raw, toJson row.id.raw])
      sourceDecoder baseDecoder
    | throwError "the changed prescribed lift order was not recognized"
  if changedOrder.isOk then throwError "the supplied envelope reordered independent prescribed lift ids"
  let sourceIsoType ← whnfR (← inferType sourceSwap)
  let #[sourceIsoCategory, sourceIsoDictionary, _, _] := sourceIsoType.getAppArgs
    | throwError "the full source comparison lacks its exact retained category dictionary"
  let wrongSourceDecoder (_ : CategoryExpr) (_ : Expr) (_ : Json) := do
    let reflexive ← withTransparency .all <| mkAppOptM ``CategoryTheory.Iso.refl
      #[some sourceIsoCategory, some sourceIsoDictionary, some receiver]
    return .ok (wrongReceiver, some reflexive)
  let rejected ← try
    let some result ← LiftedSubobjectData.decode expectedType sourceCategory receiver #[row.id] good
        wrongSourceDecoder baseDecoder
      | throwError "the wrong selected source fixture was not recognized"
    pure (!result.isOk)
  catch ex =>
    let message ← ex.toMessageData.toString
    unless message == "a retained lifted descriptor comparison ends at another actual object" do
      throw ex
    pure true
  unless rejected do throwError "a same-carrier wrong chosen source escaped its full comparison"
  logInfo "PASS: full selected lifted-envelope replay and inverse data; invalid lift metadata and same-carrier full source comparison mismatch rejected"
