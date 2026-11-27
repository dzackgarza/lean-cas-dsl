module

public import CasCompiler.LimitFamily
import all CasCompiler.SelectionData

public section

namespace CasCompiler

open Lean Meta CasCatalogue



structure NativeConstructionLeg where
  private mk ::
  owner : Expr
  selection : NativeLimitSelection
  cone : Expr
  index : Expr
  value : Expr



opaque NativeConstructionLeg.prepare (owner : Expr) (selection : NativeLimitSelection)
    (cone index : Expr) : MetaM NativeConstructionLeg := do
  let value ← selection.legAt cone index
  return ⟨owner, selection, cone, index, value⟩




opaque NativeConstructionLeg.selected (leg : NativeConstructionLeg) :
    MetaM (SourceSelection Expr) := do
  let construction ← NativeLimitSelection.ofSource leg.selection.source leg.owner
  check leg.value
  return {
    value := leg.value
    leg := some ⟨construction, leg.index, leg.value⟩
    category := some {
      role := .morphism
      expression := leg.selection.source.category
      bundle := leg.selection.source.bundle } }




opaque withConstructionParameters (ownerFamily : SelectedLimitOwner Expr) (construction : Name)
    (count : Nat) (action : Array Expr → NativeLimitSelection → MetaM α) : MetaM α := do
  check ownerFamily.selection.receiver
  if ownerFamily.selection.receiver.hasMVar || ownerFamily.selection.receiver.hasLevelMVar then
    throwError "a construction endpoint has an unresolved original owner telescope"
  forallTelescope (← inferType ownerFamily.selection.receiver) fun parameters _ => do
    unless parameters.size == count do
      throwError "a construction endpoint changed its complete original parameter positions"
    let selected ← ownerFamily.specialize parameters
    unless selected.source.construction == construction && !construction.isAnonymous do
      throwError "a construction endpoint changed its original construction selection"
    action parameters selected






opaque checkConstructionLegEndpointAt (ownerFamily : SelectedLimitOwner Expr)
    (selected : NativeLimitSelection) (parameters : Array Expr)
    (indexFamily index : Expr) (target : Bool) (position : Nat)
    (path : Array Name := #[])
    (alternatives : Array (Nat × Array Name) := #[]) : MetaM Unit := do
  let rebound ← ownerFamily.specialize parameters
  unless rebound.source.construction == selected.source.construction &&
      rebound.source.row == selected.source.row &&
      rebound.source.declaration == selected.source.declaration &&
      rebound.source.colimit == selected.source.colimit &&
      rebound.source.diagram.equal selected.source.diagram &&
      rebound.source.cone.equal selected.source.cone do
    throwError "a construction endpoint changed its original complete source interface"
  unless target != selected.source.colimit do
    throwError "the original construction parameter check requires its diagram-side endpoint"
  check indexFamily
  if indexFamily.hasMVar || indexFamily.hasLevelMVar ||
      index.hasMVar || index.hasLevelMVar then
    throwError "a construction endpoint has an unresolved original typed index"
  let originalIndex := indexFamily.betaRev parameters.reverse (preserveMData := true)
  check originalIndex
  unless originalIndex.equal index do
    throwError "a construction endpoint changed its original typed index position"
  withConstructionParameters ownerFamily selected.source.construction parameters.size
    fun formals formal => do



      let mut candidates := #[]
      for (originalPosition, originalPath) in #[(position, path)] ++ alternatives do
        let some parameter := formals[originalPosition]?
          | throwError "a construction endpoint has no such original declaration position"
        if ← isProof parameter then
          throwError "a formal hypothesis is not a computational endpoint supplier"
        let mut candidate := parameter
        for projection in originalPath do
          unless ((← getEnv).getProjectionFnInfo? projection).isSome do
            throwError "a construction endpoint path is not an original native projection"
          candidate ← mkAppM projection #[candidate]
          if ← isProof candidate then
            throwError "a formal native field is not a computational endpoint supplier"
        candidates := candidates.push candidate
      let formalIndex := indexFamily.betaRev formals.reverse (preserveMData := true)
      check formalIndex
      let arrow ← formal.legAt formal.source.cone formalIndex
      let type ← instantiateMVars (← inferType arrow)
      unless type.isAppOfArity ``Quiver.Hom 4 do
        throwError "the construction component lost its complete native Hom interface"
      let slot := if target then 3 else 2
      let some endpoint := type.getAppArgs[slot]?
        | throwError "the construction component lost its native endpoint position"
      let mut matched : Option Expr := none
      for candidate in candidates do
        if matched.isNone && (← withoutModifyingState (isDefEq endpoint candidate)) then
          matched := some candidate
      let some candidate := matched
        | throwError "the construction endpoint differs from every supplied original declaration position"
      let expected := mkAppN type.getAppFn (type.getAppArgs.set! slot candidate)


      let checked ← mkAppOptM ``id #[some expected, some arrow]
      let locals := (← getLCtx).foldl (fun values declaration =>
        values.push (mkFVar declaration.fvarId)) (#[] : Array Expr)
      let closed ← mkLambdaFVars locals (← instantiateMVars checked)
        (usedOnly := false) (usedLetOnly := false)
      if closed.hasFVar || closed.hasMVar || closed.hasLevelMVar || closed.hasSorry then
        throwError "the construction endpoint did not close over its full rigid native scope"
      checkWithKernel closed

end CasCompiler
