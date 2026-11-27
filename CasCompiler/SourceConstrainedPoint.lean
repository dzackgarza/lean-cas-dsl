module

public import CasCompiler.Elaborate
public import CasCompiler.SourceCarrier
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceProof

public section

namespace CasCompiler

open Lean Meta Elab Term

private structure ConstrainedPointSchema where
  constructor : Expr
  dataIndex : Nat
  proofCount : Nat




private def constrainedPointSchema (target : Expr) : MetaM ConstrainedPointSchema := do
  let target ← instantiateMVars target
  if target.hasMVar || target.hasLevelMVar || (← isProp target) then
    throwError "a constrained point requires a fixed native data type"
  let type ← whnf target
  let .const name levels := type.getAppFn
    | throwError "a constrained point requires its actual native structure"
  let .inductInfo info ← checkedDeclaration name
    | throwError "a constrained point requires its actual native structure"
  unless isStructure (← getEnv) name && !info.isRec && info.numIndices == 0 do
    throwError (MessageData.tagged `CasCompiler.sourceConstrainedPoint.structureShape
      "a constrained point requires a nonrecursive structure with no indices")
  let [constructor] := info.ctors
    | throwError "a constrained point requires exactly one native constructor"
  let .ctorInfo declaration ← checkedDeclaration constructor
    | throwError "the constrained structure lost its actual constructor"
  unless type.getAppNumArgs == declaration.numParams do
    throwError "the constrained structure has incomplete native parameters"
  let constructor := mkAppN (mkConst constructor levels) type.getAppArgs
  forallTelescope (← inferType constructor) fun fields result => do
    unless fields.size == declaration.numFields && (← isDefEq result target) do
      throwError "the constrained constructor has a different complete target"
    let mut dataFields : Array Nat := #[]
    for field in fields, index in [:fields.size] do
      unless ← isProp (← inferType field) do dataFields := dataFields.push index
    let #[dataIndex] := dataFields
      | throwError (MessageData.tagged `CasCompiler.sourceConstrainedPoint.dataFieldCount
          "a constrained point requires exactly one data field and only proof fields otherwise")
    return ⟨constructor, dataIndex, fields.size - 1⟩

private def constructConstrainedPoint (schema : ConstrainedPointSchema) (target : Expr)
    (proofs : Array Term) (readData : Expr → SourceReadM Expr)
    (readProof : Term → Expr → SourceReadM Expr) : SourceReadM Expr := do
  let previous ← liftM (m := MetaM) getMCtx
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType schema.constructor)
  let some original := arguments[schema.dataIndex]?
    | liftM (m := TermElabM) <| throwError "the constrained constructor lost its original data field"
  let current ← liftM (m := MetaM) getMCtx
  let owned := current.decls.foldl (fun result identity _ =>
    if previous.decls.contains identity then result else result.push identity) #[]
  let result ← withSynthesizeApplicableScoped do
    return .ok (← readData (← liftM (m := MetaM) <| instantiateMVars (← inferType original)))
  let actual ← match result with
    | .ok actual => pure actual
    | .error message => liftM (m := TermElabM) <| throwError message
  extendSourceApplicationScope owned
  unless ← isDefEq original actual do
    liftM (m := TermElabM) <| throwError "the original data do not have the constrained constructor's declared field type"
  let mut proofIndex := 0
  for argument in arguments, index in [:arguments.size] do
    if index == schema.dataIndex then continue
    let obligation ← liftM (m := MetaM) <| instantiateMVars (← inferType argument)
    unless ← isProp obligation do
      liftM (m := TermElabM) <| throwError "the constrained constructor acquired an additional data field"
    let some evidence := proofs[proofIndex]?
      | liftM (m := TermElabM) <| throwError "the constrained point is missing an explicit source proof"
    let proof ← readProof evidence obligation
    extendSourceApplicationScope owned
    unless ← isDefEq argument proof do
      liftM (m := TermElabM) <| throwError "the supplied source proof has a different constructor obligation"
    proofIndex := proofIndex + 1
  let value ← liftM (m := MetaM) <| instantiateMVars (mkAppN schema.constructor arguments)
  if value.hasMVar || value.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the constrained point has undetermined native parameters or proofs"
  SourceReadM.select { value } (some target)




def sourceConstrainedPointApplicable (target : Expr) (proofs : Array Term)
    (readData : Expr → SourceReadM (Except MessageData Expr))
    (readMap : SourceReadM NativeSourceJudgement) :
    SourceReadM NativeSourceJudgement := do
  let nativeTarget ← match (← SourceReadM.selection? target).bind (·.typeOrigin) with
    | some original => pure original.type
    | none => pure (← registeredSourceDomain target).1
  let schema ← constrainedPointSchema nativeTarget
  unless proofs.size == schema.proofCount do
    liftM (m := TermElabM) <| throwError (MessageData.tagged `CasCompiler.sourceConstrainedPoint.proofCount
      m!"the constrained point requires exactly {schema.proofCount} explicit source proofs")

  let direct ← SourceReadM.inspect do
    let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType schema.constructor)
    let some original := arguments[schema.dataIndex]?
      | liftM (m := TermElabM) <| throwError "the constrained constructor lost its original data field"
    let actual ← withSynthesizeApplicableScoped <| readData (← inferType original)
    match actual with
    | .error _ => return false
    | .ok actual => isDefEq (← inferType actual) (← inferType original)
  if direct then
    let requiredData : Expr → SourceReadM Expr := fun expected => do
      match ← readData expected with
      | .ok value => pure value
      | .error message => liftM (m := TermElabM) <| throwError message
    let value ← constructConstrainedPoint schema target proofs requiredData fun evidence obligation =>
      SourceReadM.prove obligation (fun expected _ => sourceFormalProof evidence expected)
    return ⟨value, none⟩
  let result ← withSynthesizeApplicableScoped do return .ok (← readMap)
  let original ← match result with
    | .ok original => pure original
    | .error message => liftM (m := TermElabM) <| throwError message
  let function ← sourceFunction original
  let .forallE _ domain _ binderInfo ← whnfR (← inferType function)
    | liftM (m := TermElabM) <| throwError "constrained data require a value or a map into the actual data-field type"
  let mapped ← SourceReadM.withLambda (← mkFreshUserName `point) domain binderInfo fun point => do
    let readData := fun expected => do
      let value := mkApp function point
      unless ← isDefEq (← inferType value) expected do
        liftM (m := TermElabM) <| throwError "the original map has a different constrained data-field target"
      pure value
    let readProof := fun evidence obligation => do
      let proposition ← mkForallFVars #[point] obligation
      let scope ← get
      let some pointIndex := scope.context.bindings.findIdx? (·.expression == point)
        | liftM (m := TermElabM) <| throwError "the constrained proof lost its original point binder"


      let proof ← SourceReadM.prove proposition fun expected _ => do
        let context ← getLCtx
        let locals := context.foldl (fun result declaration => result.push declaration) #[]
        let some selected := locals[pointIndex]?
          | liftM (m := TermElabM) <| throwError "the constrained proof changed its original native telescope"
        withLCtx (context.erase selected.fvarId)
            ((← getLocalInstances).filter (·.fvar != mkFVar selected.fvarId)) <|
          sourceFormalProof evidence expected
      pure (mkApp proof point)
    constructConstrainedPoint schema target proofs readData readProof
  let mappedArrow ← elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom)
    #[] #[Arg.expr mapped] none false false
  sourceSetJudgement .morphism mappedArrow



def sourceConstrainedPoint (target : Expr) (proofs : Array Term)
    (readData : Expr → SourceReadM Expr) (readMap : SourceReadM NativeSourceJudgement) :
    SourceReadM NativeSourceJudgement :=
  sourceConstrainedPointApplicable target proofs
    (fun expected => do return .ok (← readData expected)) readMap

end CasCompiler
