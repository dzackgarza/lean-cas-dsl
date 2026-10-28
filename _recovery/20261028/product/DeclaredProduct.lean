/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.CategoryContext
public import CasCatalogue.DirectConstruction
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.DeclaredProduct

/-!
The ordered coordinates in a declaration are fixed before a universal-construction
registration is selected. The registry's full component fan supplies their universal
data. A cone with the same apex but different legs cannot supply this interface.

The binary adapter below only changes the finite indexing presentation. All universal
data and all coordinate maps come from the accepted object row. It does not select a
global product limit, choose another apex, or manufacture a mathematical witness.
-/

/-- One complete registered coordinate family at its original typed arguments.
`parameterInputs` records direct declaration-slot dependence on the ordered factors
before substituting possibly equal actual objects. It is occurrence plumbing, not
a lookup by a formal value or a computational packet. -/
structure Selection where
  private mk ::
  entry : ObjectEntry
  arguments : Array Expr
  parameters : Array Expr
  parameterInputs : Array (Option Nat)
  endpoint : Expr
  object : Expr
  factors : Array Expr
  arity : Expr
  projectionFamily : Expr
  indices : Array Expr
  coordinates : Array Expr
  cone : Expr
  isLimit : Expr

private def complete (value : Expr) : TermElabM Expr := do
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars ||
      type.hasMVar || type.hasLevelMVar || type.hasLooseBVars then
    throwStratum .invalid "the declared coordinate interface requires complete typed parameters"
  unless ← isTypeCorrect value do
    throwError "the declared coordinate interface is outside its complete type"
  return value

/-- Build an index in the already fixed finite coordinate type. Only the ordinary
kernel-checked decision for the literal bound is used. -/
def binaryIndex (ordinal : Nat) : TermElabM Expr := do
  let bound := mkNatLit 2
  let value := mkNatLit ordinal
  let proposition ← mkAppM ``LT.lt #[value, bound]
  let some proof ← Decide.decisionProof proposition
    | throwStratum .invalid "the binary coordinate index is outside its declared bound"
  complete (mkApp3 (mkConst ``Fin.mk) bound value proof)

/-- Literal record coordinates are fixed by the declaration's `Prod` fields.
This reflection names no catalogue object and chooses no categorical product. -/
private def recordCoordinate (context : CategoryContext) (first second : Expr)
    (ordinal : Nat) : TermElabM Expr := do
  unless ordinal < 2 do
    throwError "the literal product coordinate is outside its two declared fields"
  let endpoint ← mkAppM ``Prod #[first, second]
  let function ← withLocalDeclD `record endpoint fun value => do
    mkLambdaFVars #[value] (.proj ``Prod ordinal value)
  let coordinate ← mkAppM ``TypeCat.ofHom #[function]
  CategoryContext.checkMorphism context coordinate endpoint
    (if ordinal == 0 then first else second)
  complete coordinate

/-- Check one independently registered family against two rigid declared fields.
The complete projection maps, not just their types or apex, determine applicability. -/
private def candidate? (state : RegistryState) (context : CategoryContext)
    (entry : ObjectEntry) (first second : Expr) : TermElabM (Option Selection) :=
    withoutModifyingState do
  let some components := entry.components | return none
  let some declaration := components.isLimit | return none
  let some category := state.categories.find? (·.id == entry.category)
    | throwError "the registered coordinate family lost its category"
  let endpoint ← mkAppM ``Prod #[first, second]
  let application ← DirectConstruction.instantiate entry.declaration #[]
  unless ← withTransparency .all <|
      isDefEq (← inferType application.value) (← inferType endpoint) <&&>
        isDefEq application.value endpoint do return none
  let application ← DirectConstruction.close application
  let registeredContext ← CategoryContext.ofNamed category application.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq registeredContext.bundle context.bundle) do return none
  let supplied := application.arguments.map some
  let arity ← complete (← mkAppOptM components.arity supplied)
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq arity (mkNatLit 2)) do return none
  let projectionFamily ← complete (← mkAppOptM components.projection supplied)
  let signature ← whnfR (← inferType projectionFamily)
  unless signature.isForall &&
      (← withoutModifyingState (withTransparency .all <|
        isDefEq signature.bindingDomain! (← mkAppM ``Fin #[mkNatLit 2]))) do
    throwError "the accepted binary coordinate family lost its declared finite index"
  let mut indices := #[]
  let mut coordinates := #[]
  for ordinal in [:2] do
    let index ← binaryIndex ordinal
    let coordinate ← complete (mkApp projectionFamily index)
    let expected ← recordCoordinate context first second ordinal
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType coordinate) (← inferType expected) <&&>
          isDefEq coordinate expected) do return none
    indices := indices.push index
    coordinates := coordinates.push coordinate
  let cone ← complete (← mkAppM ``CategoryTheory.Limits.Fan.mk
    #[application.value, projectionFamily])
  let isLimit ← complete (← mkAppOptM declaration supplied)
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType isLimit) (← mkAppM ``CategoryTheory.Limits.IsLimit #[cone])) do
    throwError "the accepted universal witness changed its exact declared coordinate fan"
  let parameterInputs := application.explicit.map fun parameter =>
    if parameter == first then some 0 else if parameter == second then some 1 else none
  return some {
    entry, arguments := application.arguments, parameters := application.explicit,
    parameterInputs, endpoint, object := application.value, factors := #[first, second],
    arity, projectionFamily, indices, coordinates, cone, isLimit }

private def Selection.replaceInputs (selection : Selection) (rigid actual : Array Expr) :
    Selection :=
  let replace := fun (value : Expr) => value.replaceFVars rigid actual
  { selection with
    arguments := selection.arguments.map replace
    parameters := selection.parameters.map replace
    endpoint := replace selection.endpoint
    object := replace selection.object
    factors := selection.factors.map replace
    arity := replace selection.arity
    projectionFamily := replace selection.projectionFamily
    indices := selection.indices.map replace
    coordinates := selection.coordinates.map replace
    cone := replace selection.cone
    isLimit := replace selection.isLimit }

/-- Select the full ordered interface of an already declared literal product.
Distinct rigid factors preserve declaration-slot origin even when the two actual
factors coincide. No candidate is preferred by row order or backend availability.
This is a matcher for that literal constructor interface; a specialized family
such as `X × X` remains a valid coordinate family without matching this two-input
constructor. Open local parameters are supported; unresolved metavariables are not data. -/
def selectBinary (context : CategoryContext) (first second : Expr) :
    TermElabM Selection := do
  let first ← complete first
  let second ← complete second
  discard <| complete context.bundle
  CategoryContext.checkObject context first
  CategoryContext.checkObject context second
  let state ← registryState
  withLocalDeclD `firstFactor (← inferType first) fun rigidFirst =>
    withLocalDeclD `secondFactor (← inferType second) fun rigidSecond => do
      let mut candidates := #[]
      for entry in state.objects do
        if (entry.components.bind (·.isLimit)).isNone then continue
        let selected ← try candidate? state context entry rigidFirst rigidSecond
          catch error =>
            if Exception.interpretationKind error == .invalid then pure none else throw error
        if let some selected := selected then candidates := candidates.push selected
      let selected ← match candidates with
        | #[selected] => pure selected
        | #[] => throwStratum .invalid
            "the declared product has no registered complete ordered coordinate interface"
        | _ => throwSemanticAmbiguity
            "the declared product has several complete registered coordinate interfaces"
      let selected := selected.replaceInputs #[rigidFirst, rigidSecond] #[first, second]
      for value in #[selected.endpoint, selected.object, selected.projectionFamily,
          selected.cone, selected.isLimit] ++ selected.arguments ++ selected.coordinates do
        discard <| complete value
      return selected

/-- Reindex the supplied finite coordinate fan to the public binary diagram.
The existing index equivalences send left to zero and right to one. The diagram
comparison retains the actual objects and maps; no global product row is read. -/
def binaryPresentation (context : CategoryContext) (selection : Selection) :
    TermElabM (Expr × Expr) := do
  let #[first, second] := selection.factors
    | throwError "the binary adapter requires its two original ordered factors"
  let #[firstCoordinate, secondCoordinate] := selection.coordinates
    | throwError "the binary adapter lost its two original ordered maps"
  let swapped ← mkAppM ``Equiv.trans
    #[mkConst ``CategoryTheory.Limits.WalkingPair.swap,
      mkConst ``CategoryTheory.Limits.WalkingPair.equivBool]
  let indexEquivalence ← mkAppM ``Equiv.trans
    #[swapped, ← mkAppM ``Equiv.symm #[mkConst ``finTwoEquiv]]
  let reindexing ← mkAppM ``CategoryTheory.Limits.Fan.isLimitEquivOfEquiv
    #[indexEquivalence, selection.cone]
  let reindexedWitness ← mkAppM ``Equiv.toFun #[reindexing, selection.isLimit]
  let witnessType ← whnfR (← inferType reindexedWitness)
  unless witnessType.isAppOf ``CategoryTheory.Limits.IsLimit do
    throwError "the coordinate reindexing lost its complete universal witness"
  let reindexedCone := witnessType.appArg!
  let coneType ← whnfR (← inferType reindexedCone)
  unless coneType.isAppOf ``CategoryTheory.Limits.Cone do
    throwError "the coordinate reindexing lost its complete cone"
  let reindexedDiagram := coneType.appArg!
  let diagramComparison ← mkAppM ``CategoryTheory.Limits.diagramIsoPair #[reindexedDiagram]
  let postcomposition ← mkAppM ``CategoryTheory.Limits.Cone.postcompose
    #[← mkAppM ``CategoryTheory.Iso.hom #[diagramComparison]]
  let cone ← mkAppM ``CategoryTheory.Functor.obj #[postcomposition, reindexedCone]
  let universalEquivalence ← mkAppM ``CategoryTheory.Limits.IsLimit.postcomposeHomEquiv
    #[diagramComparison, reindexedCone]
  let witness ← mkAppM ``Equiv.toFun
    #[← mkAppM ``Equiv.symm #[universalEquivalence], reindexedWitness]
  let presentation ← complete (← mkAppM ``CategoryTheory.Limits.LimitCone.mk #[cone, witness])
  let diagram ← complete (← mkAppOptM ``CategoryTheory.Limits.pair #[
    some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
    some first, some second])
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType presentation)
        (← mkAppM ``CategoryTheory.Limits.LimitCone #[diagram])) do
    throwError "the coordinate adapter changed its complete ordered binary diagram"
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq apex selection.endpoint) do
    throwError "the coordinate adapter changed its originally declared product object"
  let maps ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  for (name, expected) in #[
      (``CategoryTheory.Limits.WalkingPair.left, firstCoordinate),
      (``CategoryTheory.Limits.WalkingPair.right, secondCoordinate)] do
    let index ← mkAppM ``CategoryTheory.Discrete.mk #[mkConst name]
    let actual ← mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType actual) (← inferType expected) <&&>
          isDefEq actual expected) do
      throwError "the coordinate adapter changed an original ordered projection"
  return (diagram, presentation)

/-- Pair arbitrary maps through the same supplied full coordinate fan. -/
def mediator (context : CategoryContext) (selection : Selection)
    (first second : Expr) : TermElabM Expr := do
  let (_, presentation) ← binaryPresentation context selection
  let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[first, second]
  let universal ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[presentation]
  complete (← mkAppM ``CategoryTheory.Limits.IsLimit.lift #[universal, fan])

end CasCatalogue.DeclaredProduct
