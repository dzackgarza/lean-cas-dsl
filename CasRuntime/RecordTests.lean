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
      let (graph, width) ← empty.stage supply { origin with role := scalarLayout }
        (.ownedExport child token #[])
      let (graph, number) ← graph.stage supply { origin with role := scalarLayout }
        (.portable "8".toUTF8)
      let finite ← RecordPrefix.begin supply { origin with role := pointLayout.source } pointLayout
      let (finite, numeral) ← IO.ofExcept <|
        (finite.bind graph number).mapError IO.userError
      let finitePayload ← IO.ofExcept <| finite.finish.mapError IO.userError
      let (graph, finiteRoot) ← graph.stage supply { origin with role := pointLayout.source } finitePayload
      let prefix ← RecordPrefix.begin supply origin recordLayout
      match prefix.finish with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "an incomplete dependent record became a complete payload"
      let (prefix, first) ← IO.ofExcept <| (prefix.bind graph width).mapError IO.userError
      let (prefix, second) ← IO.ofExcept <| (prefix.bind graph finiteRoot).mapError IO.userError
      let payload ← IO.ofExcept <| prefix.finish.mapError IO.userError
      let (graph, root) ← graph.stage supply origin payload
      let selected ← IO.ofExcept <| (graph.project root 1).mapError IO.userError
      unless selected.value == finiteRoot.value && first.value == width.value do
        throw <| IO.userError "record binding or projection replaced an actual node"
      let some association := second.instantiations.back?
        | throw <| IO.userError "the dependent field lost its runtime instantiation"
      unless association.field.sourceIndex == 1 && association.field.precedingDependencies == #[0] &&
          association.prefix.size == 1 && association.prefix[0]?.flatten.map (·.value) == some width.value do
        throw <| IO.userError "the dependent field uses a reconstructed or incomplete prefix"
      let some erased := numeral.instantiations.back?
        | throw <| IO.userError "the finite record lost its field instantiation"
      unless erased.field.sourceIndex == 0 && erased.prefix.isEmpty do
        throw <| IO.userError "proof erasure changed computational field positions"
      let again ← RecordPrefix.begin supply origin recordLayout
      let (again, _) ← IO.ofExcept <| (again.bind graph width).mapError IO.userError
      let (again, reused) ← IO.ofExcept <| (again.bind graph second).mapError IO.userError
      let some reusedAssociation := reused.instantiations.back?
        | throw <| IO.userError "the reused field lost its new consuming association"
      unless reused.value == second.value && reused.instantiations.size > second.instantiations.size &&
          reusedAssociation.association.id != association.association.id do
        throw <| IO.userError "reuse merged two record associations or discarded earlier provenance"
      let some original := graph.find second.value
        | throw <| IO.userError "the original producing node is missing"
      unless original.origin.occurrence == occurrence && original.origin.program == program do
        throw <| IO.userError "consuming record roles rewrote producing provenance"
      let .ok dependencies := graph.requiredOwners #[selected]
        | throw <| IO.userError "the actual dependent prefix is outside the graph"
      unless dependencies == #[child.generation] do
        throw <| IO.userError "a dependent portable field lost its actual prefix owner"
      owners.close child.generation
      if ← graph.isAvailable owners selected then
        throw <| IO.userError "a dependent field survived loss of a required prefix owner"
      unless ← graph.isAvailable owners numeral do
        throw <| IO.userError "an independent portable field acquired an unrelated owner"
      match prefix.bind graph number with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "a completed record accepted an extra field"
    finally owners.close child.generation
