module

public import CasCatalogue.Codec
public import CasContract.Failure

@[expose] public section

open Lean Meta

namespace CasCatalogue.ConstrainedPoint

/-- The actual one-data-field constructor of an independently fixed record type.
No predicate, mathematical object name, or chosen structure is inferred here. -/
structure Schema where
  target : Expr
  constructor : Name
  constructorValue : Expr
  structureName : Name
  dataField : Nat
  dataType : Expr
  fieldCount : Nat

def closed (value : Expr) : Bool :=
  !value.hasMVar && !value.hasLevelMVar && !value.hasFVar &&
    !value.hasLooseBVars && !value.hasSorry

/-- Inspect only the constructor of the complete supplied target. The single data
field must have a fixed type, independently of all proposition-valued fields. -/
def schema? (target : Expr) : MetaM (Option Schema) := do
  let target ← instantiateMVars target
  unless closed target && (← isTypeCorrect target) do return none
  let reduced ← withTransparency .all <| whnf target
  let .const name levels := reduced.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  unless isStructure (← getEnv) name do return none
  if info.isRec || info.numIndices != 0 then return none
  let [constructor] := info.ctors | return none
  unless reduced.getAppArgs.size == info.numParams do return none
  let constructorValue := mkAppN (mkConst constructor levels) reduced.getAppArgs
  forallTelescope (← inferType constructorValue) fun fields result => do
    unless ← withTransparency .all <| isDefEq result target do return none
    let mut dataFields : Array (Nat × Expr) := #[]
    for i in [:fields.size] do
      let type ← instantiateMVars (← inferType fields[i]!)
      unless ← isProp type do dataFields := dataFields.push (i, type)
    let #[(dataField, dataType)] := dataFields | return none
    unless closed dataType do return none
    if (← whnf dataType).isSort then return none
    return some {
      target := target
      constructor := constructor
      constructorValue := constructorValue
      structureName := name
      dataField := dataField
      dataType := dataType
      fieldCount := fields.size }

/-- The original generalized point and the actual checked constructor application.
The point's domain is never replaced by the distinguished global-point source. -/
structure Result where
  schema : Schema
  domain : Expr
  original : Expr
  value : Expr

/-- Build the actual constructor pointwise. Proofs are independent closed Lean terms,
either generalized over the original domain or constant when the field is constant.
Unresolved proof requirements remain interpreter obstructions; a proved negation is
an invalid point. No leaf result participates in this construction. -/
def construct (target original : Expr) (proofs : Array Expr := #[]) : MetaM Result := do
  let some schema ← schema? target
    | throwStratum .invalid "the target has no fixed single-data-field constrained record interface"
  let original ← instantiateMVars original
  unless closed original && (← isTypeCorrect original) do
    throwStratum .invalid "a constrained point requires its complete original function"
  let .forallE _ domain codomain _ ← withTransparency .all <| whnf (← inferType original)
    | throwStratum .invalid "a constrained point requires its original generalized domain"
  if codomain.hasLooseBVars then
    throwStratum .invalid "a constrained point requires a fixed original data-field type"
  unless ← withTransparency .all <| isDefEq codomain schema.dataType do
    throwStratum .invalid "the original point has a different data-field type"
  withLocalDeclD `point domain fun point => do
    let mut value := schema.constructorValue
    let mut proofIndex := 0
    for i in [:schema.fieldCount] do
      let .forallE _ fieldType _ _ ← whnf (← inferType value)
        | throwError "the constrained record constructor lost a declared field"
      if i == schema.dataField then
        let datum := mkApp original point
        unless ← withTransparency .all <| isDefEq (← inferType datum) fieldType do
          throwStratum .invalid "the original point does not inhabit the constructor's data field"
        value := mkApp value datum
      else
        unless ← isProp fieldType do
          throwError "the constrained record schema changed its data fields"
        let condition ← mkForallFVars #[point] fieldType
        let proof ← if let some supplied := proofs[proofIndex]? then do
            let supplied ← instantiateMVars supplied
            unless closed supplied && (← isTypeCorrect supplied) do
              throwStratum .invalid "a constructor proof must be a closed checked term without sorry"
            let proof ← if ← withTransparency .all <|
                isDefEq (← inferType supplied) condition then pure supplied
              else if ← withTransparency .all <| isDefEq (← inferType supplied) fieldType then
                mkLambdaFVars #[point] supplied
              else throwStratum .invalid "the supplied proof is not the actual constructor condition"
            unless closed proof && (← Decide.kernelAccepts condition proof) do
              throwStratum .invalid "the supplied constructor proof is not accepted by Lean"
            pure proof
          else if let some proof ← Codec.conditionProof condition then pure proof
          else if (← Codec.conditionProof (mkNot condition)).isSome then
            throwStratum .invalid "the original point violates the constructor condition"
          else
            throwError "the constructor condition remains unresolved: {condition}"
        value := mkApp value (mkApp proof point)
        proofIndex := proofIndex + 1
    if proofs.size > proofIndex then
      throwStratum .invalid "too many independent constructor proofs were supplied"
    let completed ← instantiateMVars (← mkLambdaFVars #[point] value)
    let expected ← withLocalDeclD `point domain fun point =>
      mkForallFVars #[point] target
    unless closed completed && (← isTypeCorrect completed) &&
        (← withTransparency .all <| isDefEq (← inferType completed) expected) do
      throwError "the constructed point changed its complete target or original domain"
    return { schema, domain, original, value := completed }

/-- The actual data projection of the fixed constructor, at the same original domain. -/
def project (schema : Schema) (value : Expr) : MetaM Expr := do
  let .forallE _ domain target _ ← withTransparency .all <| whnf (← inferType value)
    | throwStratum .invalid "a constrained point projection requires a complete function"
  unless !target.hasLooseBVars &&
      (← withTransparency .all <| isDefEq target schema.target) do
    throwStratum .invalid "a constrained point projection has a different selected target"
  withLocalDeclD `point domain fun point =>
    mkLambdaFVars #[point] (mkProj schema.structureName schema.dataField (mkApp value point))

end CasCatalogue.ConstrainedPoint
