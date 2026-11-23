module

import CasRuntime.Kernel
import LeanCategories.Foundation.Mathlib
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import LeanCategories.Foundation.Mathlib

namespace CasRuntime.NativeRecordConversionTests

open Lean Meta CasCompiler

-- Forgetting a functor's laws retains its one actual object action and the map that depends
-- on that action. The two projections of the original formal argument must share that input.
-- This uses only the existing native identity functor and requires no provider or value answer.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let declaration ← getConstInfo ``LeanCategories.Foundation.Mathlib.Sets
    let sets := mkConst declaration.name (declaration.levelParams.map fun _ => Level.zero)
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[sets]
    let category ← mkAppM ``CategoryTheory.Bundled.str #[sets]
    let functor ← mkAppOptM ``CategoryTheory.Functor.id #[some carrier, some category]
    let term ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let bound : Std.HashMap BindingId ValueBinding := {}
        let value ← kernel.run transaction context bound term
        let retained ← markValue kernel.marks value term
        let objectAction ← kernel.run transaction context bound (mkProj ``Prefunctor 0 retained)
        let mapAction ← kernel.run transaction context bound (mkProj ``Prefunctor 1 retained)
        let some consumed := mapAction.instantiations.find?
            (·.field.projection == ``CategoryTheory.Functor.map)
          | throwError "the native conversion lost the original functor's dependent map role"
        let some (some originalObject) := consumed.preceding[0]?
          | throwError "the native conversion lost the map's original object action"
        unless originalObject.value == objectAction.value &&
            originalObject.associationIds.toList.isPrefixOf objectAction.associationIds.toList do
          throwError "the native conversion rebuilt the original formal object-action occurrence"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "a native record conversion dispatched a provider"
      finally discard <| transaction.abort
      -- The same genuine functor source may name a descriptor with no native field data.
      -- Its source definition cannot replace those missing actual input projections.
      let missing ← CellTransaction.begin kernel.ledger
      try
        let program ← owners.identities.fresh .program
        let .ok payload := ValuePayload.descriptor .null #[]
          | throwError "the native conversion descriptor control is malformed"
        let descriptor ← missing.stage
          { program, occurrence := ← kernel.ledger.allocate,
            role := ← SourceLayout.ofTerm (← context.close functor), parameters := #[] }
          payload
        let marked ← markValue kernel.marks descriptor functor
        let unavailable ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[marked]
        let bound : Std.HashMap BindingId ValueBinding := {}
        let failure : Option Exception ← try
          discard <| kernel.run missing context bound unavailable
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "a native conversion fabricated a descriptor's unavailable fields"
        match CasCatalogue.Exception.stratum? failure with
        | some .noImplementation => pure ()
        | _ => throw failure
        unless (← kernel.dispatches.get).isEmpty do
          throwError "a missing native conversion field dispatched a provider"
      finally discard <| missing.abort
    finally kernel.close
  finally setEnv original

end CasRuntime.NativeRecordConversionTests
