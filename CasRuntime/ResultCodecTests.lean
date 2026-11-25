module

import CasRuntime.ResultCodec
import CasRuntime.Transaction
import CasRuntime.Association
import Mathlib.CategoryTheory.Types.Basic
public meta import Lean.Elab.Command
meta import CasRuntime.ResultCodec
meta import CasRuntime.Transaction
meta import CasRuntime.Association
meta import Mathlib.CategoryTheory.Types.Basic

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- Equal endpoint data do not identify original nodes or distinct consuming views.
run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let ledger ← OccurrenceLedger.new owners
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin ledger
  let program ← owners.identities.fresh .program
  let context ← ContextTelescope.capture #[]
  let produced ← ledger.allocate
  let type := mkApp (mkConst ``Fin) (mkNatLit 2)
  let endpointRole ← SourceLayout.ofTerm (← context.close type)
  let inventory := Json.arr #[toJson (0 : Nat), toJson (1 : Nat)]
  let packet := Json.mkObj [("ctor", toJson "finiteData"),
    ("args", Json.arr #[toJson "original endpoint data", inventory])]
  let origin := { program, occurrence := produced, role := endpointRole,
    parameters := #[] : ValueOrigin }
  let source ← transaction.stage origin (.portable packet.compress.toUTF8)
  let target ← transaction.stage origin (.portable packet.compress.toUTF8)
  let other ← transaction.stage origin (.portable packet.compress.toUTF8)
  let marks ← IO.mkRef (#[] : Array ValueBinding)
  let mark (value : ValueBinding) := markValue marks value type
  let alias (value : ValueBinding) : MetaM ValueBinding := do
    let argument ← context.close (← mark value)
    let function ← SourceLayout.ofTerm (← context.close
      (mkLambda `endpoint .default (mkSort (.succ .zero)) (.bvar 0)))
    let occurrence ← ledger.allocate
    let sourceMarks := (← marks.get).mapIdx fun index value => (index, value)
    let callable ← transaction.stage
      { program, occurrence, role := function, parameters := #[], sourceMarks }
      (.closure program #[value])
    let graph ← transaction.view
    let .ok actual := RuntimeArgument.ofValue graph 0 value (← marks.get)
      | throwError "an original endpoint disappeared"
    let request ← PreparedRequest.forApplication owners.identities program occurrence context
      callable #[argument] #[actual] #[] (some graph) sourceMarks
    let (draft, result) ← request.associateResult owners.identities request.source
      (← transaction.draft) value
    discard <| request.admitResult draft.view result
    let .ok () ← transaction.installDraft draft
      | throwError "the original endpoint view could not be retained"
    return result
  let first ← alias source
  let second ← alias source
  unless first.value == second.value && first.associationIds != second.associationIds do
    throwError "the endpoint fixture lost its distinct consuming associations"
  let makeRequest (source target : ValueBinding) : MetaM PreparedRequest := do
    let sourceType ← mark source
    let targetType ← mark target
    let function := mkLambda `point .default sourceType (.bvar 0)
    let arrow ← mkAppOptM ``TypeCat.ofHom #[some sourceType, some targetType, some function]
    check arrow
    let callableRole ← SourceLayout.ofTerm (← context.close
      (mkLambda `ignored .default (mkConst ``Nat) arrow))
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
    let occurrence ← ledger.allocate
    let sourceMarks := (← marks.get).mapIdx fun index value => (index, value)
    let dummy ← transaction.stage
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "0".toUTF8)
    let callable ← transaction.stage
      { program, occurrence, role := callableRole, parameters := #[], sourceMarks }
      (.closure program #[source, target])
    let graph ← transaction.view
    let .ok actual := RuntimeArgument.ofValue graph 0 dummy (← marks.get)
      | throwError "the codec fixture lost its original argument"
    PreparedRequest.forApplication owners.identities program occurrence context callable
      #[scalarRole.source] #[actual] #[] (some graph) sourceMarks
  let request ← makeRequest first target
  let graph ← transaction.view
  let codec ← PreparedResultCodec.forMap request graph first target (← marks.get)
  let .map prepared := codec.kind | throwError "the map codec changed its original result kind"
  unless prepared.source.value == first.value &&
      prepared.source.associationIds == first.associationIds &&
      prepared.target.value == target.value do
    throwError "the map codec replaced its supplied original endpoint references"
  for (left, right) in #[(second, target), (other, target), (target, first), (first, other)] do
    let rejected ← try
        discard <| PreparedResultCodec.forMap request graph left right (← marks.get)
        pure false
      catch _ => pure true
    unless rejected do
      throwError "map framing accepted another original endpoint occurrence or association"
  let rejected ← try
      discard <| PreparedResultCodec.forMap request graph first target (← marks.get)
        (some fun _ _ _ => pure (.closure program #[]))
      pure false
    catch _ => pure true
  unless rejected do
    throwError "a callable transport acquired an unproved native carrier path"
  discard <| transaction.abort
