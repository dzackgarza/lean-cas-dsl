module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.Declaration
public import LeanCategories.Catalogue.Lift
public import LeanCategories.Catalogue.Registry.Entry
public import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue


def LiftPort.name : LiftPort → String
  | .computation => "computation"
  | .factor => "factor"

def LiftPort.ofName? : String → Option LiftPort
  | "computation" => some .computation
  | "factor" => some .factor
  | _ => none




opaque LiftFamily.forLift (row : LiftEntry) (port : LiftPort) : MetaM LiftFamily := do
  match port with
  | .computation =>
    let some name := row.computation
      | throwError "the lift {row.id.raw} publishes no callable computation"
    let info ← checkedDeclaration name
    return ⟨row.id, port, mkConst name (info.levelParams.map Level.param), info.type,
      info.levelParams, row⟩
  | .factor =>
    let info ← checkedDeclaration row.evidence
    let evidence := mkConst row.evidence (info.levelParams.map Level.param)
    let family ← forallTelescope info.type fun locals _ => do
      mkLambdaFVars locals (← mkAppM ``MonoLift.factorComputation #[mkAppN evidence locals])
    return ⟨row.id, port, family, ← inferType family, info.levelParams, row⟩


def LiftFamily.instantiate (family : LiftFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)



opaque LiftFamily.projections (family : LiftFamily) : MetaM (Array Name) := do
  forallTelescope family.familyType fun parameters resultType => do
    let type ← whnf resultType
    let .const owner _ := type.getAppFn
      | throwError "the published computation has no native record result"
    let some information := getStructureInfo? (← getEnv) owner
      | throwError "the published computation has no native record interface"
    let result := mkAppN family.family parameters
    let mut projections := #[]
    for name in information.fieldNames, index in [:information.fieldNames.size] do
      let some projection := information.getProjFn? index
        | throwError "the published record lost a native field projection"
      let value ← mkProjection result name
      unless ← isProof value do projections := projections.push projection
    return projections



opaque LiftFamily.forAddress? (state : SemanticState) (address : String) :
    MetaM (Option (LiftEntry × LiftFamily × Array Name)) := do
  let [id, field] := address.splitOn "#" | return none
  let rows := state.lifts.filter (·.id.raw == id)
  if rows.isEmpty then return none
  let #[row] := rows | throwError "a published lift address has more than one source row"
  if row.computation.isNone then return none
  let ports := if row.kind == .subobjects then #[LiftPort.computation, .factor]
    else #[LiftPort.computation]
  let mut selectedPorts := #[]
  for port in ports do
    let family ← LiftFamily.forLift row port
    for projection in ← family.projections do
      if projection.getString! == field then
        selectedPorts := selectedPorts.push (row, family, #[projection])
  match selectedPorts with
  | #[] => return none
  | #[selected] => return some selected
  | _ => throwError "a published lift address names more than one native data field"


def LiftFamily.selected (family : LiftFamily) (levels : List Level)
    (parameters : Array Expr) : MetaM (SourceSelection Expr) := do
  unless levels.length == family.universeParams.length do
    throwError "the selected lift changed its complete universe telescope"
  let head := family.family.instantiateLevelParams family.universeParams levels
  let arity ← forallTelescope (← inferType head) fun parameters _ => pure parameters.size
  unless parameters.size == arity do
    throwError "the selected lift requires its complete native declaration parameters"
  let value := mkAppN head parameters
  check value
  return {
    value, reference := some (.lift family.entry), originalApplication := some value
    application := some {
      family := .lift family, universes := levels, parameters } }




def LiftFamily.atEvidence (row : LiftEntry) (port : LiftPort) (evidence : Expr) :
    MetaM (SourceSelection Expr) := do
  let evidence ← instantiateMVars evidence
  unless evidence.consumeMData.getAppFn.constName? == some row.evidence do
    throwError "the selected lift application lost its evidence declaration {row.evidence}"
  let family ← LiftFamily.forLift row port
  let (head, levels) ← family.instantiate
  let applied := mkAppN head evidence.consumeMData.getAppArgs
  let published ← match port with
    | .computation => mkAppM ``MonoLift.computation #[evidence]
    | .factor => mkAppM ``MonoLift.factorComputation #[evidence]
  unless ← withTransparency .all <| isDefEq applied published do
    throwError "the lift {row.id.raw} publishes a different computation at its evidence"
  family.selected (← levels.mapM instantiateLevelMVars)
    (← evidence.consumeMData.getAppArgs.mapM instantiateMVars)

end CasCompiler
