module

public meta import CasCatalogue.TestSuite
public meta import CasCatalogue.FunctorActionData

/-! Engineering checks of the registered restriction-of-scalars action. These inspect full
typed actions and trace parameters; they supply no mathematical acceptance oracle. -/

open Lean Meta Elab Term CasCatalogue
open CategoryTheory

run_elab do
  let state ← registryState
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "missing registered module fibre"
  let source ← elabTermAndSynthesize
    (← `(ModuleCat.of (RingCat.of (ZMod 4)) (ZMod 4))) none
  let baseMap ← elabTermAndSynthesize
    (← `(RingCat.ofHom (Int.castRingHom (ZMod 4)))) none
  let trace ← Trace.new
  let (restricted, _) ← Semantic.reindex source modules baseMap (some trace)
  let expected ← elabTermAndSynthesize
    (← `((LeanCategories.Modules.ModulesOverRings.reindex
      (RingCat.ofHom (Int.castRingHom (ZMod 4)))).obj
        (ModuleCat.of (RingCat.of (ZMod 4)) (ZMod 4)))) none
  unless ← withTransparency .all <| isDefEq restricted expected do
    throwError "reindex did not apply the accepted restriction functor"
  let some (.functor id params receiver) ← trace.node? restricted
    | throwError "reindex lost its registered functor trace"
  unless id == FunctorId.modulesReindex && params.size == 1 do
    throwError "reindex changed its declaration's ordered explicit parameters"
  unless ← isDefEq params[0]! baseMap do throwError "reindex lost its actual base map"
  unless ← isDefEq receiver source do throwError "reindex changed its selected receiver"
  let some entry := state.functors.find? (·.id == id)
    | throwError "missing recorded reindex declaration"
  let F ← elabTermAndSynthesize
    (← `((CasCatalogue.Modules.CatalogueRegistration.modulesReindexDeclaration
      (RingCat.ofHom (Int.castRingHom (ZMod 4))) :
        ModuleCat.{0} (RingCat.of (ZMod 4)) ⥤ ModuleCat.{0} (RingCat.of Int)))) none
  let wire := Json.mkObj [("ctor", toJson "functorAction"),
    ("args", Json.arr #[toJson "exact-selected-reindex", toJson "exact-selected-module"])]
  let decodeFunctor := fun (json : Json) => do
    unless json == toJson "exact-selected-reindex" do
      return .error "different selected reindex descriptor"
    return .ok (F, entry.source, entry.target)
  let decodeSource := fun (category : CategoryExpr) (expected : Expr) (json : Json) => do
    unless category.syntacticEq entry.source && json == toJson "exact-selected-module" do
      return .error "different selected source descriptor"
    unless ← isDefEq (← inferType source) expected do
      return .error "different complete source category"
    return .ok source
  let some (.ok reconstructed) ← FunctorActionData.decode (← inferType restricted)
      wire decodeFunctor decodeSource
    | throwError "full selected reindex action failed generic structured reconstruction"
  unless ← isDefEq reconstructed restricted do
    throwError "reconstructed reindex action changed its full selected object"
  let some inclusion := state.functors.find? (·.id == FunctorId.modulesFibreInclusion)
    | throwError "missing registered fibre inclusion"
  let some underlying := state.functors.find? (·.id == FunctorId.modulesUnderlying)
    | throwError "missing single total underlying functor"
  let (leftTotal, _) ← Semantic.applyRegisteredFunctor inclusion restricted
    #[← `(RingCat.of Int)] (some trace)
  let (rightTotal, _) ← Semantic.applyRegisteredFunctor inclusion source
    #[← `(RingCat.of (ZMod 4))] (some trace)
  for total in #[leftTotal, rightTotal] do
    let some (.functor id params _) ← trace.node? total
      | throwError "fibre inclusion lost its action trace"
    unless id == inclusion.id && params.size == 1 do
      throwError "fibre inclusion lost its full selected ring parameter"
  let (leftSet, _) ← Semantic.applyRegisteredFunctor underlying leftTotal #[] (some trace)
  let (rightSet, _) ← Semantic.applyRegisteredFunctor underlying rightTotal #[] (some trace)
  for set in #[leftSet, rightSet] do
    let some (.functor id params _) ← trace.node? set
      | throwError "total underlying functor lost its trace"
    unless id == underlying.id && params.isEmpty do
      throwError "underlying-set action invented a fibre-specific parameter"
  unless ← withTransparency .all <| isDefEq leftSet rightSet do
    throwError "the two accepted actions do not reach the same complete underlying set"
  let incompatible ← elabTermAndSynthesize
    (← `(RingCat.ofHom (Int.castRingHom (ZMod 5)))) none
  let rejected ← try
    discard <| Semantic.reindex source modules incompatible (some trace)
    pure false
  catch _ => pure true
  unless rejected do throwError "reindex accepted a base map with a different source fibre"
