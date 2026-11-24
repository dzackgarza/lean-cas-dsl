module

public import CasCompiler.Elaborate
public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

private structure ConstrainedPointSchema where
  constructor : Expr
  dataIndex : Nat
  proofCount : Nat

/-- Inspect the actual selected native constructor, without inventing an admission row.
Source: casInProof and the constrained-point schema in CasContract.Port. Parameters stay
fixed by the complete target; only the declared fields are available for construction. -/
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
    (proofs : Array Term) (readData : Expr → TermElabM Expr)
    (readProof : Term → Expr → TermElabM Expr) : TermElabM Expr := do
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType schema.constructor)
  let some original := arguments[schema.dataIndex]?
    | throwError "the constrained constructor lost its original data field"
  let actual ← withSynthesize <| readData (← instantiateMVars (← inferType original))
  unless ← isDefEq original actual do
    throwError "the original data do not have the constrained constructor's declared field type"
  let mut proofIndex := 0
  for argument in arguments, index in [:arguments.size] do
    if index == schema.dataIndex then continue
    let obligation ← instantiateMVars (← inferType argument)
    unless ← isProp obligation do
      throwError "the constrained constructor acquired an additional data field"
    let some evidence := proofs[proofIndex]?
      | throwError "the constrained point is missing an explicit source proof"
    let proof ← readProof evidence obligation
    unless ← isDefEq argument proof do
      throwError "the supplied source proof has a different constructor obligation"
    proofIndex := proofIndex + 1
  let value ← instantiateMVars (mkAppN schema.constructor arguments)
  if value.hasMVar || value.hasLevelMVar then
    throwError "the constrained point has undetermined native parameters or proofs"
  unless ← isDefEq (← inferType value) target do
    throwError "the constrained point has a different complete selected target"
  mkExpectedTypeHint value target

/-- Build the existing native constrained constructor at the supplied original data.
For a generalized point, each proof is checked over the whole original domain before it
is applied pointwise. No membership procedure, representative, or backend reply is used. -/
def sourceConstrainedPoint (target : Expr) (proofs : Array Term)
    (readData : Expr → TermElabM Expr) (readMap : TermElabM NativeSourceJudgement) :
    TermElabM NativeSourceJudgement := do
  let schema ← constrainedPointSchema target
  unless proofs.size == schema.proofCount do
    throwError (MessageData.tagged `CasCompiler.sourceConstrainedPoint.proofCount
      m!"the constrained point requires exactly {schema.proofCount} explicit source proofs")
  -- Test only the data's declared type here. A wrong proof must never choose another reading.
  let direct ← withoutModifyingState do
    try
      let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType schema.constructor)
      let some original := arguments[schema.dataIndex]?
        | throwError "the constrained constructor lost its original data field"
      let actual ← withSynthesize <| readData (← inferType original)
      isDefEq (← inferType actual) (← inferType original)
    catch error => do
      CasCatalogue.keepTrialAmbiguity error
      pure false
  if direct then
    return ⟨← constructConstrainedPoint schema target proofs readData sourceFormalProof, none⟩
  let original ← withSynthesize readMap
  let function ← sourceFunction original
  let .forallE _ domain _ binderInfo ← whnfR (← inferType function)
    | throwError "constrained data require a value or a map into the actual data-field type"
  let outerContext ← getLCtx
  let outerInstances ← getLocalInstances
  let mapped ← withLocalDecl (← mkFreshUserName `point) binderInfo domain fun point => do
    let readData := fun expected => do
      let value := mkApp function point
      unless ← isDefEq (← inferType value) expected do
        throwError "the original map has a different constrained data-field target"
      pure value
    let readProof := fun evidence obligation => do
      let proposition ← mkForallFVars #[point] obligation
      -- The supplied proof is elaborated in the original scope, outside the fresh point.
      let proof ← withLCtx outerContext outerInstances <|
        sourceFormalProof evidence proposition
      pure (mkApp proof point)
    let value ← constructConstrainedPoint schema target proofs readData readProof
    mkLambdaFVars #[point] value (usedOnly := false) (usedLetOnly := false)
  let mappedArrow ← elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom)
    #[] #[Arg.expr mapped] none false false
  sourceSetJudgement .morphism mappedArrow

end CasCompiler
