module

public import CasCompiler.Declaration
public import LeanCategories.Catalogue.Lift
public import LeanCategories.Catalogue.Registry.Entry
public import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The published computations of a selected subobject lift. -/
inductive LiftPort
  /-- `LiftEntry.computation`, a `MonoLiftComputation`: the fields `obj`, `hom`, `forward` and
  `backward`. -/
  | computation
  /-- `MonoLift.factorComputation` at the lift's evidence: the field `factor`. -/
  | factor
  deriving BEq, Repr

def LiftPort.name : LiftPort → String
  | .computation => "computation"
  | .factor => "factor"

def LiftPort.ofName? : String → Option LiftPort
  | "computation" => some .computation
  | "factor" => some .factor
  | _ => none

/-- A published computation of a selected lift, as a closed family of the parameters of the lift's
evidence declaration. Its fields are the leaf contract's ports `<lift id>#<field>`
(api/wire-examples.md, "Prescribed subobject lifts" and "Separate universal factor"). -/
structure LiftFamily where
  private mk ::
  lift : LiftId
  port : LiftPort
  family : Expr
  familyType : Expr
  universeParams : List Name

/-- The family of `port` for the registered lift `row`, read under the release axiom policy.
Reuse: checkedDeclaration, MonoLift.factorComputation and Lean's telescope operations. -/
opaque LiftFamily.forLift (row : LiftEntry) (port : LiftPort) : MetaM LiftFamily := do
  match port with
  | .computation =>
    let some name := row.computation
      | throwError "the lift {row.id.raw} publishes no callable computation"
    let info ← checkedDeclaration name
    return ⟨row.id, port, mkConst name (info.levelParams.map Level.param), info.type,
      info.levelParams⟩
  | .factor =>
    let info ← checkedDeclaration row.evidence
    let evidence := mkConst row.evidence (info.levelParams.map Level.param)
    let family ← forallTelescope info.type fun locals _ => do
      mkLambdaFVars locals (← mkAppM ``MonoLift.factorComputation #[mkAppN evidence locals])
    return ⟨row.id, port, family, ← inferType family, info.levelParams⟩

/-- The family at fresh universe metavariables. -/
def LiftFamily.instantiate (family : LiftFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

/-- Exact native data-field projections of the published result record. Proof fields
are absent; names and order come from Lean's source structure metadata. -/
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

/-- Resolve an exact lift port from the independently checked native result record.
The factor remains its separate accepted family. Conflicting native ports are rejected. -/
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

/-- The family applied to the evidence parameters `arguments`, marked so that the lowerer sends
it to its ports and does not unfold it (constitution C22). -/
def LiftFamily.mark (family : LiftFamily) (applied : Expr) : Expr :=
  .mdata (KVMap.empty |>.setName `CasCompiler.source.kind ``LiftFamily
    |>.setString `CasCompiler.source.id family.lift.raw
    |>.setString `CasCompiler.source.port family.port.name) applied

/-- The family of the computation `applied` at the evidence of the selected lift application:
`applied` must be the evidence's own published computation of `port`. Reuse: the same
definitional comparison as Registry.validateLift. -/
def LiftFamily.atEvidence (row : LiftEntry) (port : LiftPort) (evidence : Expr) : MetaM Expr := do
  let evidence ← instantiateMVars evidence
  unless evidence.consumeMData.getAppFn.constName? == some row.evidence do
    throwError "the selected lift application lost its evidence declaration {row.evidence}"
  let family ← LiftFamily.forLift row port
  let (head, _) ← family.instantiate
  let applied := mkAppN head evidence.consumeMData.getAppArgs
  let published ← match port with
    | .computation => mkAppM ``MonoLift.computation #[evidence]
    | .factor => mkAppM ``MonoLift.factorComputation #[evidence]
  unless ← withTransparency .all <| isDefEq applied published do
    throwError "the lift {row.id.raw} publishes a different computation at its evidence"
  return family.mark (← instantiateMVars applied)

end CasCompiler
