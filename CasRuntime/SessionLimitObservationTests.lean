module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
import LeanCategories.Catalogue.Semantics.Algebra.Series
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
meta import LeanCategories.Catalogue.Semantics.Algebra.Series

open Lean Elab Command Term CasRuntime

/- A defining leg of a registered limit is that limit's named leg at its maps (constitution C7),
not the apex and not the presentation's definition (C22): the base-change functor's map action on
`C.leg(1)` receives the descriptor `colim.bil_w_form.cokernel#leg` with the limit's map and the
ordinal 1. A real protocol-v2 process answers; its log records each request. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let log := root / ".tmp" / "kernel-leg-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operation := "fun.bil_wform.base_change#map"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson (root / "scripts/probes/kernel_lift_peer.py").toString,
          toJson log.toString, toJson operation])]]),
      ("registrations", .arr #[Json.mkObj [("operation", toJson operation),
        ("input", "fun.bil_wform.base_change#input"), ("backend", "peer")]])]
    let path := root / ".tmp" / "kernel-leg-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    let (published, occurrence, observation, logBeforeClose) ← try
      for text in #["let C := cokernel(to_dual(1))",
          "let r := map C.leg(1) along «fun.bil_wform.base_change»(ℤ, ℚ)"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      let requests := ((← liftM (m := IO) <| IO.FS.readFile log).splitOn "\n").filter (!·.isEmpty)
      let some line := requests.head? | throwError "the base change's map action was not dispatched"
      let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
      let .ok arguments := (request.getObjValD "context").getObjValAs? (Array Json) "arguments"
        | throwError "the map action has no arguments: {line}"
      let leg := arguments.back?.getD .null
      unless (leg.getObjValAs? String "ctor").toOption == some "colim.bil_w_form.cokernel#leg" &&
          ((leg.getObjValD "args").getArr?.toOption.bind (·.back?)) == some (toJson (1 : Nat)) do
        throwError "the map action did not receive C's leg 1: {line}"
      let some selected := session.source.context.entries[0]?
        | throwError "the public cokernel definition lost its source binding"
      let some result := session.source.context.entries.back?
        | throwError "the public map definition lost its source binding"
      let some binding := session.value? result.id
        | throwError "the public map definition lost its actual computed value"
      let published ← SessionSnapshot.current
      let some node := published.graph.find binding.value
        | throwError "the public map result is absent from the committed graph"
      let occurrence := binding.applications.back?.map (·.association.occurrence)
        |>.getD node.origin.occurrence
      let some receipt := published.receipt occurrence
        | throwError "the public map result lost its committed request"
      let some source := receipt.association.request.observation.sourceSnapshot
        | throwError "the public source handoff omitted its original source snapshot"
      let .ok context := source.getObjValAs? (Array Json) "context"
        | throwError "the public source snapshot lost its original context"
      let .ok categories := source.getObjValAs? (Array Json) "categories"
        | throwError "the public source snapshot lost its selected categories"
      unless selected.userName == `C && result.userName == `r &&
          context.map (·.getObjValD "id") == #[CasCompiler.ContextSnapshot.bindingJson selected.id] &&
          (source.getObjValD "resultBinding").getObjValD "id" ==
            CasCompiler.ContextSnapshot.bindingJson result.id do
        throwError "the source snapshot changed the original context or result binding"
      let some selection := (session.source.categoryFor selected.id).bind (·.limit)
        | throwError "the public cokernel binding lost its selected presentation"
      let some category := categories[0]?
        | throwError "the source snapshot omitted the cokernel's selected category"
      let limit := category.getObjValD "limit"
      let .ok nodes := CasTools.NativeExpression.decodeNodes
          (source.getObjValD "nativeExpressions")
        | throwError "the source snapshot lost its exact native expression graph"
      for (name, original) in #[("cone", selection.cone),
          ("presentation", selection.presentation), ("diagram", selection.diagram)] do
        let retained := limit.getObjValD name
        let .ok expression := retained.getObjValAs? Nat "expression"
          | throwError "the source snapshot lost the selected {name}"
        let .ok type := retained.getObjValAs? Nat "type"
          | throwError "the source snapshot lost the selected {name}'s type"
        unless nodes[expression]? == some original.expression &&
            nodes[type]? == some original.type do
          throwError "the source snapshot changed the actual selected {name}"
      unless (limit.getObjValD "interface").getObjVal? "dataConstructor" |>.isOk do
        throwError "the source snapshot omitted the selected native data interface"
      pure (published, occurrence, receipt.association.request.observation.toJson,
        ← liftM (m := IO) <| IO.FS.readFile log)
    finally liftM (m := IO) session.close
    let some retained := published.receipt occurrence
      | throwError "provider shutdown hid the public result's inert observation"
    unless retained.association.request.observation.toJson == observation &&
        (← liftM (m := IO) <| IO.FS.readFile log) == logBeforeClose do
      throwError "reading the committed observation changed it or dispatched another request"
  finally setEnv environment
