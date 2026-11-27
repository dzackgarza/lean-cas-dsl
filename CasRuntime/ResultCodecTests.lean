module

import CasRuntime.ResultCodec
import CasRuntime.Transaction
import CasRuntime.Association
import CasRuntime.ExecutionContext
import Mathlib.CategoryTheory.Types.Basic
public meta import Lean.Elab.Command
meta import CasRuntime.ResultCodec
meta import CasRuntime.Transaction
meta import CasRuntime.Association
meta import CasRuntime.ExecutionContext
meta import Mathlib.CategoryTheory.Types.Basic

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend


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
  let alias (value : ValueBinding) : MetaM ValueBinding := do
    let argument ← context.close type
    let function ← SourceLayout.ofTerm (← context.close
      (mkLambda `endpoint .default (mkSort (.succ .zero)) (.bvar 0)))
    let occurrence ← ledger.allocate
    let callable ← transaction.stage
      { program, occurrence, role := function, parameters := #[] }
      (.closure program #[value])
    let graph ← transaction.view
    let .ok actual := RuntimeArgument.ofValue graph 0 value
      | throwError "an original endpoint disappeared"
    let request ← PreparedRequest.forApplication owners.identities program occurrence context
      callable #[argument] #[actual] #[] (some graph)
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
    let function := mkLambda `point .default type (.bvar 0)
    let original ← mkAppOptM ``TypeCat.ofHom #[some type, some type, some function]
    check original
    let occurrence ← ledger.allocate
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
    let dummy ← transaction.stage
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "0".toUTF8)
    let functionRole ← SourceLayout.ofTerm (← context.close function)
    let functionValue ← transaction.stage
      { program, occurrence, role := functionRole, parameters := #[] } (.closure program #[])
    let graph ← transaction.view
    withBindingContext graph context {} source fun context bound =>
      withBindingContext graph context bound target fun context bound =>
        withApplicationInputs owners.identities context bound original.getAppFn original.getAppArgs
            #[some source, some target, some functionValue] fun context bound arguments => do
          let arrow := mkAppN original.getAppFn arguments
          check arrow
          let callableRole ← SourceLayout.ofTerm (← context.close
            (mkLambda `ignored .default (mkConst ``Nat) arrow))
          let environment ← RuntimeEnvironment.captureBound owners.worker context bound graph
          let callable ← transaction.stage (← environment.origin program occurrence callableRole)
            (.closure program #[source, target, functionValue])
          let graph ← transaction.view
          let .ok actual := RuntimeArgument.ofValue graph 0 dummy
            | throwError "the codec fixture lost its original argument"
          PreparedRequest.forApplication owners.identities program occurrence context callable
            #[scalarRole.source] #[actual] #[] (some graph)
  let request ← makeRequest first target
  let graph ← transaction.view
  let codec ← PreparedResultCodec.forMap request graph first target
  let .map prepared := codec.kind | throwError "the map codec changed its original result kind"
  unless prepared.source.value == first.value &&
      prepared.source.associationIds == first.associationIds &&
      prepared.target.value == target.value do
    throwError "the map codec replaced its supplied original endpoint references"
  for (left, right) in #[(second, target), (other, target), (target, first), (first, other)] do
    let rejected ← try
        discard <| PreparedResultCodec.forMap request graph left right
        pure false
      catch _ => pure true
    unless rejected do
      throwError "map framing accepted another original endpoint occurrence or association"
  let rejected ← try
      discard <| PreparedResultCodec.forMap request graph first target
        (some fun _ _ _ => pure (.closure program #[]))
      pure false
    catch _ => pure true
  unless rejected do
    throwError "a callable transport acquired an unproved native carrier path"
  discard <| transaction.abort
