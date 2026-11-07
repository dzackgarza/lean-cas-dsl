module

import CasRuntime.Value
public meta import Lean.Elab.Command
meta import CasRuntime.Value

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let family ← withLocalDeclD `n (mkConst ``Nat) fun n =>
    mkLambdaFVars #[n] (mkApp (mkConst ``Fin) (mkApp2 (mkConst ``Nat.add) n (mkNatLit 1)))
  let point := mkApp (mkConst ``Fin.last) (mkNatLit 5)
  let source ← mkAppOptM ``Sigma.mk #[some (mkConst ``Nat), some family,
    some (mkNatLit 5), some point]
  let layout ← SourceLayout.ofTerm (← context.close source)
  let recordLayout ← RecordLayout.ofSource layout
  let pointLayout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close point))
  let scalarLayout ← SourceLayout.ofTerm (← context.close (mkNatLit 8))
  let pair ← mkAppM ``Prod.mk #[mkNatLit 8, mkNatLit 8]
  let pairLayout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close pair))
  let proofFamily ← withLocalDeclD `h (mkConst ``True) fun h =>
    mkLambdaFVars #[h] (mkConst ``Nat) (usedOnly := false)
  let proofFirst ← mkAppOptM ``PSigma.mk #[some (mkConst ``True), some proofFamily,
    some (mkConst ``True.intro), some (mkNatLit 8)]
  let proofLayout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close proofFirst))
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let supply := owners.identities
    let program ← supply.fresh .program
    let occurrence ← supply.fresh .occurrence
    let origin : ValueOrigin := { program, occurrence, role := layout }
    let child ← owners.spawn { cmd := "/bin/cat" }
    try
      child.child.stdin.putStr "actual width\n"
      child.child.stdin.flush
      let token := (← child.child.stdout.getLine).trimAscii.toString
      let empty := ValueGraph.empty supply
      let (graph, number) ← empty.stage supply { origin with role := scalarLayout }
        (.portable "8".toUTF8)
      let finite ← RecordPrefix.begin supply program occurrence pointLayout
      let (finite, numeral) ← finite.bind graph number
      let finitePayload ← IO.ofExcept <| finite.finish.mapError IO.userError
      let (withoutWidth, finiteRoot) ← graph.stage supply
        { origin with role := pointLayout.source } finitePayload
      let (graph, width) ← withoutWidth.stage supply { origin with role := scalarLayout }
        (.ownedExport child token #[])
      let record ← RecordPrefix.begin supply program occurrence recordLayout
      match record.finish with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "an incomplete dependent record became a complete payload"
      let (record, first) ← record.bind graph width
      let (record, second) ← record.bind graph finiteRoot
      let payload ← IO.ofExcept <| record.finish.mapError IO.userError
      let (graph, root) ← graph.stage supply origin payload
      let selected ← IO.ofExcept <| (graph.project root 1).mapError IO.userError
      unless selected.value == finiteRoot.value && first.value == width.value do
        throw <| IO.userError "record binding or projection replaced an actual node"
      let some association := second.instantiations.back?
        | throw <| IO.userError "the dependent field lost its runtime instantiation"
      unless association.field.sourceIndex == 1 &&
          association.field.precedingDependencies == #[0] &&
          association.preceding.size == 1 &&
          (association.preceding[0]?.bind id).map (·.value) == some width.value &&
          association.id.worker == supply.worker do
        throw <| IO.userError "the dependent field uses a reconstructed or incomplete prefix"
      let some erased := numeral.instantiations.back?
        | throw <| IO.userError "the finite record lost its field instantiation"
      unless erased.field.sourceIndex == 0 && erased.preceding.isEmpty do
        throw <| IO.userError "proof erasure changed computational field positions"
      let proofRecord ← RecordPrefix.begin supply program occurrence proofLayout
      let (proofRecord, dataField) ← proofRecord.bind graph number
      discard <| IO.ofExcept <| proofRecord.finish.mapError IO.userError
      let some proofContext := dataField.instantiations.back?
        | throw <| IO.userError "the data field after a proof lost its instantiation"
      unless proofContext.field.sourceIndex == 1 && proofContext.preceding.size == 1 &&
          proofContext.preceding[0]?.map (·.isNone) == some true do
        throw <| IO.userError
          "an erased proof displaced a later data field's formal source position"
      let again ← RecordPrefix.begin supply program occurrence recordLayout
      let (again, _) ← again.bind graph width
      let (again, reused) ← again.bind graph second
      let againPayload ← IO.ofExcept <| again.finish.mapError IO.userError
      let (graph, againRoot) ← graph.stage supply origin againPayload
      let projectedAgain ← IO.ofExcept <| (graph.project againRoot 1).mapError IO.userError
      let some reusedAssociation := reused.instantiations.back?
        | throw <| IO.userError "the reused field lost its new consuming association"
      unless reused.value == second.value && projectedAgain.value == second.value &&
          projectedAgain.instantiations.size == reused.instantiations.size &&
          reused.instantiations.size > second.instantiations.size &&
          againRoot.value != root.value &&
          reusedAssociation.id != association.id &&
          reusedAssociation.association.id != association.association.id do
        throw <| IO.userError "reuse merged two record associations or discarded earlier provenance"
      let some original := graph.find second.value
        | throw <| IO.userError "the original producing node is missing"
      unless original.origin.occurrence == occurrence && original.origin.program == program do
        throw <| IO.userError "consuming record roles rewrote producing provenance"
      match withoutWidth.requiredOwners #[second] with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "an older graph recovered a field's absent actual prefix"
      let .ok dependencies := graph.requiredOwners #[selected]
        | throw <| IO.userError "the actual dependent prefix is outside the graph"
      unless dependencies == #[child.generation] do
        throw <| IO.userError "a dependent portable field lost its actual prefix owner"
      let fork ← RecordPrefix.begin supply program occurrence recordLayout
      let (left, _) ← fork.bind graph width
      let (_, leftField) ← left.bind graph finiteRoot
      let (right, _) ← fork.bind graph number
      let (_, rightField) ← right.bind graph finiteRoot
      let .ok combined := graph.requiredOwners #[rightField, leftField]
        | throw <| IO.userError "a branched record lost a valid source scope"
      let .ok independent := graph.requiredOwners #[rightField]
        | throw <| IO.userError "the independent branch lost its source scope"
      unless combined == #[child.generation] && independent.isEmpty do
        throw <| IO.userError "role traversal merged aliased nodes in different record branches"
      let mut retained := number
      for _ in [:64] do
        let chain ← RecordPrefix.begin supply program occurrence pairLayout
        let (chain, _) ← chain.bind graph retained
        let (_, next) ← chain.bind graph retained
        retained := next
      let .ok captured := graph.requiredOwners #[retained]
        | throw <| IO.userError "shared prefix traversal lost a retained reference"
      unless captured.isEmpty && retained.value == number.value &&
          retained.instantiations.size == 64 do
        throw <| IO.userError "shared prefix traversal changed identity, roles or owner independence"
      owners.close child.generation
      if ← graph.isAvailable owners selected then
        throw <| IO.userError "a dependent field survived loss of a required prefix owner"
      unless ← graph.isAvailable owners numeral do
        throw <| IO.userError "an independent portable field acquired an unrelated owner"
      unless ← graph.isAvailable owners rightField do
        throw <| IO.userError "an independent consuming role acquired another branch's owner"
      let rejected ← try
        discard <| record.bind graph number
        pure false
      catch _ => pure true
      unless rejected do throw <| IO.userError "a completed record accepted an extra field"
    finally owners.close child.generation
