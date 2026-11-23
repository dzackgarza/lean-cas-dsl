module

import CasRuntime.Materialize
import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups
public meta import Lean.Elab.Command
meta import CasRuntime.Materialize
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups

open Lean Meta CasCompiler CasRuntime CasCatalogue CasCatalogue.Backend

-- The registered group kernel returns an inclusion into the input arrow's source.
-- Equal endpoint terms have distinct retained nodes. The reply supplies only the new
-- apex and defining map, as in RoutedResultSchemaProbes on work/kernel-v1-20261023.
-- Opaque payloads exercise field assembly; they assert no computed group-theoretic answer.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let sign ← Elab.Term.elabTermAndSynthesize
      (← `(CasCatalogue.Algebra.FiniteGroups.sign 3)) none
    let signArrow ← mkAppM ``CategoryTheory.Arrow.mk #[sign]
    let object ← mkAppM ``CategoryTheory.Arrow.left #[signArrow]
    let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
    let receiver ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
    let receiverRole ← SourceLayout.ofTerm (← context.close receiver)
    let record ← RecordLayout.ofSource receiverRole
    let #[leftField, rightField, homField] :=
        record.fields.filter (·.field.wireIndex.isSome)
      | throwError "the existing group arrow changed its native computational fields"
    unless ← isDefEq (← leftField.layout.source.inContext context)
        (← rightField.layout.source.inContext context) do
      throwError "the fixed-input control requires equal source and target terms"
    let family ← SourceFamily.forReference (.functor ⟨"fun.arrows_groups.kernel"⟩)
    let declaration := family.source.family.instantiateLevelParams family.universeParams
      (family.universeParams.map fun _ => Level.zero)
    let callableSource ← mkProjection declaration `obj
    let callableRole ← SourceLayout.ofTerm (← context.close callableSource)
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let connection ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let transaction ← CellTransaction.begin ledger
      try
        let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
        let produced ← liftM (m := BaseIO) ledger.allocate
        let left ← liftM (m := IO) <| transaction.stage
          { program, occurrence := produced, role := leftField.layout, parameters := #[] }
          (.closure program #[])
        let right ← liftM (m := IO) <| transaction.stage
          { program, occurrence := produced, role := rightField.layout, parameters := #[] }
          (.closure program #[])
        let hom ← liftM (m := IO) <| transaction.stage
          { program, occurrence := produced, role := homField.layout, parameters := #[] }
          (.closure program #[])
        let input ← liftM (m := IO) <| transaction.stage
          { program, occurrence := produced, role := receiverRole, parameters := #[] }
          (.product #[left, right, hom])
        let callable ← liftM (m := IO) <| transaction.stage
          { program, occurrence := produced, role := callableRole, parameters := #[] }
          (.closure program #[])
        let graph ← liftM (m := IO) transaction.view
        let .ok argument := RuntimeArgument.ofValue graph 0 input
          | throwError "the group-kernel receiver is outside its actual graph"
        let occurrence ← liftM (m := BaseIO) ledger.allocate
        let request ← PreparedRequest.forApplication owners.identities program occurrence context
          callable #[← context.close receiver] #[argument] #[]
        let selected : DispatchIdentity := {
          manifestDigest := "fixed-input-result", profileDigest := "fixed-input-result"
          registration := {
            operation := "fun.arrows_groups.kernel"
            input := "fun.arrows_groups.kernel#input"
            backend := "field-assembly" } }
        let .ok reservation ← liftM (m := BaseIO) <|
          transaction.reserve occurrence selected connection #[input]
          | throwError "the fixed-result field assembly could not reserve its reply"
        let scope ← liftM (m := IO) <|
          RequestScope.issue ledger reservation graph #[input] #[] #[]
        let tokens := #["returned kernel group", "returned kernel inclusion"]
        let values := tokens.map (fun token => ComputationalValue.encode (.opaque token))
        let exports := tokens.map (fun token => Json.mkObj [
          ("token", .str token), ("captures", .arr #[])])
        let frame := Json.mkObj [
          ("request_id", toJson (1 : Nat)), ("status", .str "ok"),
          ("value", .arr values), ("exports", .arr exports)]
        let reply ← liftM (m := IO) <|
          ImmediateReply.parseControl scope reservation graph scope.wireId 1 frame
        let (draft, response) ← reply.materialize request transaction scope connection
        let .ok arrow := draft.view.project response.root 0
          | throwError "the fixed kernel result lost its underlying inclusion arrow"
        let .ok ambient := draft.view.project arrow 1
          | throwError "the fixed kernel result lost its ambient group"
        unless ambient.value == left.value && ambient.value != right.value do
          throwError "fixed result assembly replaced the actual source endpoint with an equal input"
        let .ok apex := draft.view.project arrow 0
          | throwError "the fixed kernel result lost its returned apex"
        let .ok inclusion := draft.view.project arrow 2
          | throwError "the fixed kernel result lost its returned defining map"
        for (value, token) in #[(apex, tokens[0]!), (inclusion, tokens[1]!)] do
          let some node := draft.view.find value.value
            | throwError "a new kernel field is outside the assembled graph"
          let .ownedToken owner actual _ := node.payload.data
            | throwError "a new kernel field lost its returned native data"
          unless owner == connection.generation && actual == token do
            throwError "fixed field assembly changed a provider-supplied kernel field"
      finally discard <| liftM (m := BaseIO) transaction.abort
    finally liftM (m := IO) <| owners.close connection.generation
  finally setEnv original
