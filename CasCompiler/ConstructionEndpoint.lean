module

public import CasCompiler.LimitFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- One compiler-prepared construction component keeps the exact retained owner,
complete actual cone and original typed index beside its unchanged native arrow. -/
structure NativeConstructionLeg where
  private mk ::
  owner : Expr
  selection : NativeLimitSelection
  cone : Expr
  index : Expr
  value : Expr

/-- Form only the source-native component; ownership remains with the original
runtime callback. No returned endpoint or diagram object is evaluated here. -/
opaque NativeConstructionLeg.prepare (owner : Expr) (selection : NativeLimitSelection)
    (cone index : Expr) : MetaM NativeConstructionLeg := do
  let value ← selection.legAt cone index
  return ⟨owner, selection, cone, index, value⟩

/-- Open the original full owner telescope. This supports both a raw presentation
and a created source cone; each caller supplies its already retained owner family.
All implicit, computational and proof positions stay in their original order. -/
opaque withConstructionParameters (ownerFamily : Expr) (construction : Name)
    (count : Nat) (action : Array Expr → NativeLimitSelection → MetaM α) : MetaM α := do
  check ownerFamily
  if ownerFamily.hasMVar || ownerFamily.hasLevelMVar then
    throwError "a construction endpoint has an unresolved original owner telescope"
  lambdaTelescope ownerFamily fun parameters owner => do
    unless parameters.size == count do
      throwError "a construction endpoint changed its complete original parameter positions"
    let some selected ← NativeLimitSelection.ofExpr? owner
      | throwError "a construction endpoint lost its original formal owner"
    unless selected.source.construction == construction && !construction.isAnonymous do
      throwError "a construction endpoint changed its original construction selection"
    action parameters selected

/-- Validate a supplied original parameter position against the diagram-side endpoint
of this exact native leg. The check takes place under the full rigid original owner
telescope. The original typed index is retained by exact positional back-substitution.
Native conversion checks a Hom interface; it never produces an endpoint value,
chooses a runtime operand, or evaluates a diagram object for later storage. -/
opaque checkConstructionLegEndpointAt (ownerFamily : Expr)
    (selected : NativeLimitSelection) (parameters : Array Expr)
    (indexFamily index : Expr) (target : Bool) (position : Nat)
    (path : Array Name := #[])
    (alternatives : Array (Nat × Array Name) := #[]) : MetaM Unit := do
  let original := ownerFamily.betaRev parameters.reverse (preserveMData := true)
  check original
  let some rebound ← NativeLimitSelection.ofExpr? original
    | throwError "a construction endpoint lost its retained owner application"
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
      -- Every listed route belongs to the same independently supplied actual
      -- binding. Validate all routes before trying native conversion, so an
      -- invalid original position cannot be hidden by another matching route.
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
      -- A checked identity at the required Hom type checks native conversion in
      -- the kernel. The term is transient interface validation, not a computation.
      let checked ← mkAppOptM ``id #[some expected, some arrow]
      let locals := (← getLCtx).foldl (fun values declaration =>
        values.push (mkFVar declaration.fvarId)) (#[] : Array Expr)
      let closed ← mkLambdaFVars locals (← instantiateMVars checked)
        (usedOnly := false) (usedLetOnly := false)
      if closed.hasFVar || closed.hasMVar || closed.hasLevelMVar || closed.hasSorry then
        throwError "the construction endpoint did not close over its full rigid native scope"
      checkWithKernel closed

end CasCompiler
