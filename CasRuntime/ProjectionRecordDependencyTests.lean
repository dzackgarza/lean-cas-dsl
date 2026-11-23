module

import CasRuntime.Kernel
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel

namespace CasRuntime.ProjectionRecordDependencyTests

open Lean Meta CasCompiler

-- The original lazy input contains an ordinary native dependent record. Projecting that
-- record must succeed through its actual retained parent before any later field demand.
-- No provider or mathematical result is supplied, and no payload value is asserted.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let term ← Elab.Term.elabTermAndSynthesize
      (← `(((⟨7, ⟨0, Nat.zero_lt_succ 7⟩⟩ : Sigma (fun n : Nat => Fin (n + 1))), ()))) none
    let source ← empty.close term
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let code ← owners.identities.fresh .program
      kernel.codes.modify (·.insert code (.term source))
      let input ← producer.stage
        { program := code, occurrence := ← kernel.ledger.allocate,
          role := ← SourceLayout.ofTerm source, parameters := #[] }
        (.closure code #[])
      let .error _ := (← producer.view).project input 0
        | throwError "the native dependent-record control already has a stored first field"
      let .ok _ ← producer.commit
        | throwError "the original lazy dependent record could not publish"
      withLocalDeclD `x (← inferType term) fun x => do
        let binding : LocalBinding := {
          id := { session := "native-record-projection", serial := 0 },
          role := .parameter, expression := x }
        let context ← ContextTelescope.capture #[binding]
        let bound : Std.HashMap BindingId ValueBinding := {}
        let consumer ← CellTransaction.begin kernel.ledger
        try
          let result ← kernel.run consumer context (bound.insert binding.id input)
            (mkProj ``Prod 0 x)
          unless result.projectionAccesses.any (fun (parent, path) =>
              parent.value == input.value && parent.associationIds == input.associationIds &&
                path == #[``Prod.fst]) do
            throwError "the native record projection lost its exact original lazy parent"
          unless (← kernel.dispatches.get).isEmpty do
            throwError "the native record projection dispatched a provider"
        finally discard <| consumer.abort
      -- Session retains a definition's exact let role on the same original value node.
      -- Native conversion can still read its definition; reference selection keeps x.
      withLetDecl `x (← inferType term) term fun x => do
        let binding : LocalBinding := {
          id := { session := "native-record-projection-alias", serial := 0 },
          role := .definition, expression := x }
        let context ← ContextTelescope.capture #[binding]
        let .ok selected := input.withRole (← SourceLayout.ofTerm (← context.close x))
          | throwError "the native dependent record could not retain its source alias"
        let bound : Std.HashMap BindingId ValueBinding := {}
        let consumer ← CellTransaction.begin kernel.ledger
        try
          let result ← kernel.run consumer context (bound.insert binding.id selected)
            (mkProj ``Prod 0 x)
          unless result.projectionAccesses.any (fun (parent, path) =>
              parent.value == selected.value &&
                parent.associationIds == selected.associationIds && path == #[``Prod.fst]) do
            throwError "the aliased native record projection lost its exact original parent"
          unless (← kernel.dispatches.get).isEmpty do
            throwError "the aliased native record projection dispatched a provider"
        finally discard <| consumer.abort
    finally kernel.close
  finally setEnv original

end CasRuntime.ProjectionRecordDependencyTests
