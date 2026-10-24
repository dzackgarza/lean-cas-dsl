/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.TransferInstance
meta import CasCatalogue.ComputationalData

/-! A complete registered object action supplies its carrier interface without
requiring a separate named row for its result. Equal carriers cannot substitute
different selected structure dictionaries. These are interface controls only. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue

meta section

private def dataNode (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let state ← registryState
  let some sourceRow := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the independently registered source is absent"
  let source ← Semantic.object sourceRow #[]
  let edge := EdgeRef.functor ⟨"fun.rings.multiplicative_monoid"⟩
  let action ← Semantic.asFunctor (← Semantic.edgeFunctor state edge)
  let selected ← Semantic.objOf action source
  let descriptor := dataNode "functorAction" #[
    dataNode "fun.rings.multiplicative_monoid" #[], dataNode sourceRow.id.raw #[]]
  let .ok carrier ← ComputationalData.interfaceCarrier selected descriptor
    | throwError "the registered action result lost its complete carrier interface"
  let expected ← withTransparency .all <| mkAppM ``MonCat.carrier #[selected]
  unless ← withTransparency .all <| isDefEq carrier expected do
    throwError "the action changed its independently selected carrier"
  let sourceCarrier ← withTransparency .all <| mkAppM ``RingCat.carrier #[source]
  let different ← withTransparency .all <| elabTermAndSynthesize
    (← `(MonCat.of (Multiplicative $(← exprToSyntax sourceCarrier)))) none
  let differentCarrier ← withTransparency .all <| mkAppM ``MonCat.carrier #[different]
  unless (← withTransparency .all <| isDefEq expected differentCarrier) &&
      !(← withTransparency .all <| isDefEq selected different) do
    throwError "the interface fixture does not distinguish complete selected dictionaries"
  if (← ComputationalData.interfaceCarrier different descriptor).isOk then
    throwError "the action descriptor accepted a different structure on the same carrier"

  let opaqueSource := dataNode "opaqueData" #[toJson "retained structured source"]
  let retainedDescriptor := dataNode "functorAction" #[
    dataNode "fun.rings.multiplicative_monoid" #[], opaqueSource]
  let inputs : ComputationalData.InterfaceObjects := #[(opaqueSource, source)]
  let .ok retainedCarrier ← ComputationalData.interfaceCarrier selected retainedDescriptor inputs
    | throwError "the exact retained action source lost its carrier interface"
  unless ← withTransparency .all <| isDefEq retainedCarrier expected do
    throwError "the retained action source changed its declared carrier"
  let pointType ← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, expected]
  let pointData := dataNode "element" #[retainedDescriptor,
    dataNode "point" #[dataNode "opaqueData" #[toJson "retained closed point"]]]
  unless (← ComputationalData.validateCallableAt inputs pointType pointData).isOk do
    throwError "the nested point validator discarded the retained source interface"
  let .ok retainedValue ← ComputationalData.interfaceSelectedValue inputs selected retainedDescriptor
    | throwError "the retained action lost its complete source selection"
  let .object _ _ _ _ (some (_, retainedSource, route, _, _)) := retainedValue
    | throwError "the structural action discarded its retained source provenance"
  let retainedContext ← (Language.objectContext retainedSource).run {}
  let (sourceBundle, _) ← functorCategoryBundles action
  unless route == #[edge] && (← withTransparency .all <|
      isDefEq (← (Language.semanticObject retainedSource).run {}) source <&&>
        isDefEq retainedContext.bundle sourceBundle) do
    throwError "the retained action replaced its complete source or selected category"
  if (← ComputationalData.interfaceCarrier selected retainedDescriptor).isOk then
    throwError "an unretained source packet selected a mathematical object"
  if (← ComputationalData.interfaceCarrier different retainedDescriptor inputs).isOk then
    throwError "the retained action accepted a different complete result on the same carrier"
  let unknownTarget ← mkFreshExprMVar (← inferType selected)
  if (← ComputationalData.interfaceCarrier unknownTarget retainedDescriptor inputs).isOk then
    throwError "the action descriptor supplied the independently expected result"
  unless (← instantiateMVars unknownTarget).isMVar do
    throwError "the action image filled an unknown expected result"
  if (← ComputationalData.interfaceCarrier selected retainedDescriptor
      #[(opaqueSource, sourceCarrier)]).isOk then
    throwError "the retained action accepted a source from the wrong complete category"

  -- MulOpposite changes the carrier to PreOpposite. Transfer the existing ring
  -- along negation on this exact carrier instead; its unit becomes the old -1.
  let sourceRing ← mkAppM ``RingCat.ring #[source]
  let otherSource ← elabTermAndSynthesize
    (← `(letI : Ring $(← exprToSyntax sourceCarrier) := $(← exprToSyntax sourceRing)
         @RingCat.of $(← exprToSyntax sourceCarrier)
           (Equiv.neg $(← exprToSyntax sourceCarrier)).ring)) none
  let otherCarrier ← withTransparency .all <| mkAppM ``RingCat.carrier #[otherSource]
  unless ← withTransparency .all <| isDefEq sourceCarrier otherCarrier do
    throwError "the retained-source fixture changed the exact source carrier"
  if ← withTransparency .all <| isDefEq source otherSource then
    throwError "the retained-source fixture does not distinguish full dictionaries"
  if (← ComputationalData.interfaceCarrier selected retainedDescriptor
      #[(opaqueSource, otherSource)]).isOk then
    throwError "the action substituted a different full source on the same carrier"
  for conflicting in #[#[(opaqueSource, source), (opaqueSource, otherSource)],
      #[(opaqueSource, otherSource), (opaqueSource, source)]] do
    if (← ComputationalData.interfaceCarrier selected retainedDescriptor conflicting).isOk then
      throwError "input-table order selected one of two complete retained sources"
  let unknown ← mkFreshExprMVar (← inferType source)
  if (← ComputationalData.interfaceCarrier selected retainedDescriptor
      #[(opaqueSource, unknown)]).isOk then
    throwError "the action selected an unresolved retained structure"
  unless (← instantiateMVars unknown).isMVar do
    throwError "the action filled an unknown source from its requested result"
  let contradictory := dataNode "functorAction" #[
    dataNode "fun.rings.multiplicative_monoid" #[], dataNode sourceRow.id.raw #[]]
  if (← ComputationalData.interfaceCarrier selected contradictory
      #[(dataNode sourceRow.id.raw #[], otherSource)]).isOk then
    throwError "a retained packet bypassed its explicit named-source selection"

  let some parameterized := state.functor? FunctorId.modulesFibreInclusion
    | throwError "the accepted action-parameter fixture is absent"
  let moduleSource ← elabTermAndSynthesize
    (← `(letI : Ring $(← exprToSyntax sourceCarrier) := $(← exprToSyntax sourceRing)
         ModuleCat.of $(← exprToSyntax sourceCarrier) $(← exprToSyntax sourceCarrier))) none
  let parameterizedAction ← ObjectPresentation.applyParameters parameterized.declaration #[source]
  let parameterizedResult ← Semantic.objOf parameterizedAction moduleSource
  let parameterPacket := dataNode "opaqueData" #[toJson "retained action parameter"]
  let modulePacket := dataNode "opaqueData" #[toJson "retained action source module"]
  let parameterizedDescriptor := dataNode "functorAction" #[
    dataNode parameterized.id.raw #[parameterPacket], modulePacket]
  let parameters : ComputationalData.InterfaceObjects :=
    #[(parameterPacket, source), (modulePacket, moduleSource)]
  unless (← ComputationalData.interfaceSelectedValue parameters parameterizedResult
      parameterizedDescriptor).isOk do
    throwError "the action discarded its exact retained source and parameter"
  if (← ComputationalData.interfaceSelectedValue
      #[(parameterPacket, otherSource), (modulePacket, moduleSource)]
      parameterizedResult parameterizedDescriptor).isOk then
    throwError "the action replaced its complete selected parameter on the same carrier"
  if (← ComputationalData.interfaceSelectedValue #[(modulePacket, moduleSource)]
      parameterizedResult parameterizedDescriptor).isOk then
    throwError "the requested result supplied an unretained action parameter"

run_elab do
  let state ← registryState
  let some construction := state.constructions.find? (·.id.raw == "con.automorphisms")
    | throwError "the accepted dependent construction is absent"
  let category ← elabTermAndSynthesize (← `(LeanCategories.Foundation.Mathlib.Sets.{0})) none
  let original ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let other ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 3)) none
  let source ← mkAppM ``CategoryTheory.Core.mk #[original]
  let otherSource ← mkAppM ``CategoryTheory.Core.mk #[other]
  let action ← DirectConstruction.select construction #[← exprToSyntax category] source
  let selected ← DirectConstruction.obj action source
  let different ← DirectConstruction.obj action otherSource
  let categoryPacket := dataNode "opaqueData" #[toJson "retained construction category"]
  let sourcePacket := dataNode "opaqueData" #[toJson "retained construction source"]
  let descriptor := dataNode "functorAction" #[
    dataNode construction.id.raw #[categoryPacket], sourcePacket]
  let inputs : ComputationalData.InterfaceObjects :=
    #[(categoryPacket, category), (sourcePacket, source)]
  let .ok value ← ComputationalData.interfaceSelectedValue inputs selected descriptor
    | throwError "the construction lost its source from the complete dependent signature"
  let context ← (Language.objectContext value).run {}
  let (_, targetBundle) ← functorCategoryBundles action.functor
  unless ← withTransparency .all <|
      isDefEq (← (Language.semanticObject value).run {}) selected <&&>
        isDefEq context.bundle targetBundle do
    throwError "the construction changed its complete selected result or category"
  unless (← ComputationalData.interfaceCarrier selected descriptor inputs).isOk do
    throwError "the construction result lost its declared carrier interface"
  if (← ComputationalData.interfaceSelectedValue
      #[(categoryPacket, category), (sourcePacket, original)] selected descriptor).isOk then
    throwError "the construction accepted a retained source outside its full signature"
  if (← ComputationalData.interfaceSelectedValue
      #[(categoryPacket, category), (sourcePacket, otherSource)] selected descriptor).isOk then
    throwError "the construction replaced its retained source with a different full object"
  if (← ComputationalData.interfaceSelectedValue inputs different descriptor).isOk then
    throwError "the construction descriptor changed the independently fixed result"

end
