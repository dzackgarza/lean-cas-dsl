module

import CasRuntime.Environment
public meta import Lean.Elab.Command
meta import CasRuntime.Environment

namespace CasRuntime.ResultPrefixDependencyTests

open Lean Meta CasCompiler

def selectedPrefix (width : Nat) : Sigma (fun n : Nat => Fin (n + 1)) :=
  ⟨width, ⟨0, Nat.zero_lt_succ width⟩⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let owners ← OwnerRegistry.new
  let program ← owners.identities.fresh .program
  let occurrence ← owners.identities.fresh .occurrence
  let seven := mkNatLit 7
  let point ← Elab.Term.elabTermAndSynthesize
    (← `((⟨0, Nat.zero_lt_succ 7⟩ : Fin (7 + 1)))) none
  let plain ← Elab.Term.elabTermAndSynthesize
    (← `((⟨7, ⟨0, Nat.zero_lt_succ 7⟩⟩ : Sigma (fun n : Nat => Fin (n + 1))))) none
  let scalarRole ← SourceLayout.ofTerm (← context.close seven)
  let pointRole ← SourceLayout.ofTerm (← context.close point)
  let plainLayout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close plain))
  let origin := fun role =>
    ({ program, occurrence, role, parameters := #[] } : ValueOrigin)
  let (graph, first) ← (ValueGraph.empty owners.identities).stage owners.identities
    (origin scalarRole) (.portable "7".toUTF8)
  let (graph, other) ← graph.stage owners.identities
    (origin scalarRole) (.portable "7".toUTF8)
  let (graph, point) ← graph.stage owners.identities
    (origin pointRole) (.closure program #[])
  let record ← RecordPrefix.begin owners.identities program occurrence plainLayout
  let (graph, record, originalWidth) ← record.bind graph first
  let (graph, _, originalPoint) ← record.bind graph point
  let sibling ← RecordPrefix.begin owners.identities program occurrence plainLayout
  let (graph, _, siblingWidth) ← sibling.bind graph first
  unless originalWidth.value == siblingWidth.value &&
      originalWidth.associationIds != siblingWidth.associationIds &&
      other.value != originalWidth.value do
    throwError "the result-prefix control lost its distinct original suppliers"
  let allocated ← owners.identities.fresh .sourceBinding
  context.withLocalBinding ⟨allocated.worker, allocated.serial⟩ .result `width
      (mkConst ``Nat) (fun context binding => do
        let native := mkConst ``CasRuntime.ResultPrefixDependencyTests.selectedPrefix
        let selectedId ← owners.identities.fresh .sourceBinding
        context.withLocalBinding ⟨selectedId.worker, selectedId.serial⟩ .definition `selectedPrefix
            (← inferType native) (fun context selected => do
            let source ← SourceLayout.ofTerm (← context.close (mkApp selected.expression binding.expression))
            let layout ← RecordLayout.ofSource source
            let parameter ← IO.ofExcept <|
              (RuntimeParameter.ofValue graph binding.id originalWidth).mapError IO.userError
            let environment ← RuntimeEnvironment.capture owners.worker context #[parameter] (some graph)
            let build (width field : ValueBinding) (associate : Bool) :
                MetaM (ValueGraph × ValueBinding) := do
              if !associate then
                return ← graph.stage owners.identities (← environment.origin program occurrence source)
                  (.product #[width, field])
              let record ← RecordPrefix.prepare owners.identities program occurrence layout graph environment.bound
              let (graph, record, _) ← record.bind graph width
              let (graph, record, _) ← record.bind graph field
              let payload ← IO.ofExcept <| record.finish.mapError IO.userError
              graph.stage owners.identities (← environment.origin program occurrence source) payload
            for associate in #[false, true] do
              let (goodGraph, good) ← build originalWidth originalPoint associate
              let accepted ← environment.checkResult goodGraph source good
              let acceptedPoint ← IO.ofExcept <| (goodGraph.project accepted.root 1).mapError IO.userError
              unless acceptedPoint.value == originalPoint.value &&
                  originalPoint.associationIds.toList.isPrefixOf acceptedPoint.associationIds.toList do
                throwError "dependent result admission replaced its original selected field"
              for wrong in #[other, siblingWidth] do
                let (badGraph, bad) ← build wrong originalPoint associate
                let rejected ← try
                  discard <| environment.checkResult badGraph source bad
                  pure false
                catch _ => pure true
                unless rejected do
                  throwError "dependent result admission accepted a different actual prefix supplier"

              let (badGraph, bad) ← build originalWidth point associate
              let rejected ← try
                discard <| environment.checkResult badGraph source bad
                pure false
              catch _ => pure true
              unless rejected do
                throwError "a consuming output association authorized its own missing original dependency"

        ) (originalSource := some native)

    ) (originalSource := some seven)

end CasRuntime.ResultPrefixDependencyTests
