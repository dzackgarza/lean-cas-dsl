module

import CasRuntime.Kernel
import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

open Lean Meta Elab Command Term CasCompiler CasRuntime

-- The same inline named module is formed twice. Each native field's delayed code must
-- retain the exact ring occurrence in its own descriptor slot, before any later consumer
-- opens that code. Equal source expressions do not identify the two parameter occurrences.
run_cmd liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let source ← SourceSession.empty owners.identities
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "RegularModule(ℤ)"
        | throwError "the inline named-record source did not parse"
      let checked ← source.read ⟨parsed⟩
      checked.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let mut originals : Array ValueBinding := #[]
          for _ in [:2] do
            let value ← kernel.run transaction context {} expression
            let graph ← transaction.view
            let some node := graph.find value.value
              | throwError "the named record lost its actual producing node"
            let .container packet := node.payload.data
              | throwError "the named record lost its complete descriptor"
            let #[argument] := packet.slots
              | throwError "the named record lost its original declaration argument"
            unless argument.path == #[.field "args", .index 0] &&
                argument.fieldIndex.isNone do
              throwError "the named record changed its declared argument position"
            let some fields := packet.fields
              | throwError "the named record lost its native stored fields"
            unless fields.size > 1 do
              throwError "the inline module control lost its dependent native record"
            for index in [:fields.size] do
              let field ← IO.ofExcept <| (graph.project value index).mapError IO.userError
              let some fieldNode := graph.find field.value
                | throwError "the original native field is outside its producing graph"
              let .closure program _ := fieldNode.payload.data
                | throwError "the named native field lost its delayed original source"
              let some (.term code) := (← kernel.codes.get)[program]?
                | throwError "the named native field lost its original source code"
              let marks ← IO.ofExcept <|
                (captureSourceMarks (← kernel.marks.get) code).mapError IO.userError
              unless marks.any (fun (_, selected) =>
                  selected.value == argument.binding.value &&
                    selected.associationIds == argument.binding.associationIds) do
                throwError "the named native field did not retain its exact original argument slot"
              for other in originals do
                if marks.any (fun (_, selected) => selected.value == other.value) then
                  throwError "an equal inline source substituted another record's argument"
            if originals.any (fun previous => previous.value == argument.binding.value) then
              throwError "independent inline named records merged their original arguments"
            originals := originals.push argument.binding
          unless (← kernel.dispatches.get).isEmpty do
            throwError "retaining named source code dispatched mathematical computation"
        finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original

