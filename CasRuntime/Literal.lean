module

public import CasRuntime.Value
public import CasCompiler.Declaration

public section

namespace CasRuntime.ScalarLiteral

open Lean Meta CasCompiler CasCatalogue.Backend

inductive Status
  | notScalar | checked
  deriving BEq, Repr

private def constraintProof (condition : Expr) : MetaM (Option Expr) := do
  let some _ ← synthInstance? (← mkAppM ``Decidable #[condition]) | return none
  let decision ← withTransparency .all <| whnf (← mkDecide condition)
  if decision.isConstOf ``Bool.false then
    throwError "a scalar literal violates its declared representation constraint"
  unless decision.isConstOf ``Bool.true do return none
  let proof ← mkDecideProof condition
  checkWithKernel (← mkExpectedTypeHint proof condition)
  return some proof

/-- Read only closed, data-only scalar representations, discarding the value at the public gate.
Grammar reference: CasContract.Port wire encoding and CasCatalogue.Codec.decodeAt. Reuse Lean's
constructor telescopes, native literal expressions, mkDecideProof and synchronous kernel checks.
Function/type fields have no scalar decoding path; no finite-function or law reconstruction runs. -/
private partial def decode (asked : Expr) (packet : Json) : MetaM (Option Expr) := do
  let type ← whnf asked
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.isSort || type.isForall then
    return none
  if ← isProp type then return none
  if (packet.getObjValAs? String "ctor").toOption == some "valueData" then
    let .ok () := checkServiceFields #["ctor", "args"] packet
      | throwError "a scalar literal has unexpected computational envelope fields"
    let .ok (.inline data) := ComputationalValue.decode packet
      | throwError "a scalar literal has an invalid computational envelope"
    return ← decode asked data
  if type.isConstOf ``Nat then
    let .ok value := packet.getNat?
      | throwError "a scalar literal requires a natural JSON number"
    return some (mkNatLit value)
  if type.isConstOf ``Int then
    let .ok value := packet.getInt?
      | throwError "a scalar literal requires an integer JSON number"
    return some (toExpr value)
  if type.isAppOfArity ``List 1 then
    let .ok values := packet.getArr?
      | throwError "a scalar list literal requires a JSON array"
    let element := type.appArg!
    let mut decoded : Array Expr := #[]
    for value in values do
      let some value ← decode element value | return none
      decoded := decoded.push value
    let mut result ← mkAppOptM ``List.nil #[some element]
    for value in decoded.reverse do result ← mkAppM ``List.cons #[value, result]
    return some result
  if type.isAppOfArity ``Quot 2 then
    let #[carrier, relation] := type.getAppArgs | return none
    let some value ← decode carrier packet | return none
    let .const _ levels := type.getAppFn | return none
    return some (mkAppN (mkConst ``Quot.mk levels) #[carrier, relation, value])
  let .const name levels := type.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  let parameters := type.getAppArgs.extract 0 info.numParams
  let constructorName ← if info.ctors.length == 1 && info.numIndices == 0 then
      pure info.ctors[0]!
    else do
      let .ok () := checkServiceFields #["ctor", "args"] packet
        | throwError "a scalar literal has unexpected constructor fields"
      let .ok label := packet.getObjValAs? String "ctor"
        | throwError "a scalar literal requires its declared constructor tag"
      let some constructor := info.ctors.find? (·.getString! == label)
        | throwError "a scalar literal names a constructor outside its declared type"
      pure constructor
  discard <| checkedDeclaration constructorName
  let mut result := mkAppN (mkConst constructorName levels) parameters
  let count ← forallTelescope (← inferType result) fun fields _ => do
    let mut count := 0
    for field in fields do
      unless ← isProp (← inferType field) do count := count + 1
    return count
  let values ← if info.ctors.length == 1 && info.numIndices == 0 && count == 1 then
      pure #[packet]
    else do
      let .ok values := if info.ctors.length == 1 && info.numIndices == 0 then packet.getArr?
          else (packet.getObjVal? "args").bind (·.getArr?)
        | throwError "a scalar literal requires its complete ordered constructor data"
      pure values
  unless values.size == count do
    throwError "a scalar literal has a different declared data-field arity"
  let mut index := 0
  while true do
    let remaining ← whnf (← inferType result)
    let .forallE _ fieldType _ _ := remaining | break
    if ← isProp fieldType then
      let some proof ← constraintProof fieldType | return none
      result := mkApp result proof
    else
      let some packet := values[index]?
        | throwError "a scalar literal has an incomplete constructor prefix"
      let some value ← decode fieldType packet | return none
      result := mkApp result value
      index := index + 1
  unless ← isDefEq (← inferType result) asked do
    throwError "a scalar literal has a different declared native type"
  checkWithKernel (← mkExpectedTypeHint result asked)
  return some result

/-- Validate a wholly inline closed scalar at its source type, then discard the checked value.
This establishes representation constraints, not correctness of the requested computation.
Structured/owned/open-dependent values retain their prepared operational admission path. -/
opaque check (source : SourceLayout) (packet : Json) : MetaM Status := do
  let .ok () := CasRuntime.checkLiteral packet | return .notScalar
  source.source.withOpen fun _ expression => do
    let some _ ← decode (← inferType expression) packet | return .notScalar
    return .checked

end CasRuntime.ScalarLiteral
