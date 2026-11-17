module

import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization
import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization
meta import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra

open Lean Elab Command Term CasRuntime

/- RX-LIFT's first selected lift (tests/acceptance/proposals/independent-extension-reconstruction-
20261024/completion/rx-lift-prescribed-stages.cas) through the public path with no leaf. The lift
is a record of delayed fields: defining it dispatches nothing, and its fields are then projected
from that same retained record. A computation that needs a leaf is a gap, and so is a
projection whose dependent type needs such a value; reading holds. Functional work may use the
heartbeats it needs (constitution C21). -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let mut session ← KernelSession.start none
    try
      for (text, kind) in #[
          ("let Q := ℚ in CommutativeRings", "holds"),
          ("let Qring := view Q along «fun.commutative_rings.ring»()", "gap"),
          ("let scalarModule := RegularModule(Qring)", "gap"),
          ("let X := DegeneratePlane()", "holds"),
          ("let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)", "gap"),
          ("let i0(t) := (2*t, -2*t) in scalarModule → sourceModule", "holds"),
          ("let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)", "holds"),
          -- The lift's fields depend on the module scalarModule, whose computation has no
          -- leaf here: projecting them is that gap.
          ("let X1 := first.obj()", "gap"),
          ("let i1 := first.hom()", "gap")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
    finally liftM (m := IO) session.close
  finally setEnv environment

/- The same lift with leaves. A field of a selected lift is the lift's published computation
(LiftEntry.computation), so `first.obj()` is resolved to the leaf registered at the contract's
`<lift>#obj` port (api/wire-examples.md, "Prescribed subobject lifts") and is not reduced in Lean
(constitution C22). The request carries the lift's evidence parameters (ℚ, ℚ). A real
protocol-v2 process answers; its log records each request. -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let prepared ← liftM (m := IO) <| IO.Process.output {
      cmd := "/home/dzack/.local/bin/uv", args := #["sync", "--frozen", "--project", contract.toString] }
    unless prepared.exitCode == 0 do
      throwError "the pinned native SDK dependencies could not be provisioned: {prepared.stderr}"
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let log := root / ".tmp" / "kernel-lift-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operations : Array String := #["fun.commutative_rings.ring", "fun.bilin_module.forget",
      "fun.bilin_module.forget#map",
      "lift.bilin_module.restrict#obj", "lift.bilin_module.restrict#hom",
      "lift.bilin_module.restrict#forward", "lift.bilin_module.restrict#backward",
      "lift.bilin_module.restrict#factor", "mor.sets.divide", "mor.modules.row_linear_map"]
    -- The divider's leaf declares the multiplicative monoid route for `/` on commutative rings
    -- (C6), so `3/2` in Q reads.
    let preferences := fun (operation : String) => if operation == "mor.sets.divide" then
        #[Json.mkObj [("name", "/"), ("receiver", "cat.commutative_rings"),
          ("route", .arr #["fun.commutative_rings.ring", "fun.rings.multiplicative_monoid"])]]
      else #[]
    let input := fun (operation : String) => s!"{(operation.splitOn "#").head!}#input"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr (#[toJson (root / "scripts/probes/kernel_lift_peer.py").toString,
          toJson log.toString] ++ operations.map toJson))]]),
      ("registrations", .arr (operations.map fun (operation : String) => Json.mkObj [
        ("operation", toJson operation), ("input", toJson (input operation)),
        ("backend", "peer"), ("preferredRoutes", .arr (preferences operation))]))]
    let path := root / ".tmp" / "kernel-lift-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      unless session.kernel.rejected.isEmpty do
        throwError "a lift port registration was rejected: {session.kernel.rejected}"
      for text in #[
          "let Q := ℚ in CommutativeRings",
          "let Qring := view Q along «fun.commutative_rings.ring»()",
          "let scalarModule := RegularModule(Qring)",
          "let X := DegeneratePlane()",
          "let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)",
          "let i0(t) := (2*t, -2*t) in scalarModule → sourceModule",
          "let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)",
          "let X1 := first.obj()",
          "let i1 := first.hom()",
          "let alpha1 := first.forward()",
          "let beta1 := first.backward()",
          -- Later uses of the returned object and map (T049): each consumer receives the
          -- retained provider value, not a rebuilt term.
          "let firstCarrier := view X1 along «fun.bilin_module.forget»(ℚ, ℚ)",
          "let firstUnderlyingInclusion := map i1 along «fun.bilin_module.forget»(ℚ, ℚ)",
          -- The universal factor through the lift (T044), sent to its port and used later.
          "let cone := degenerate_plane_cone()",
          "let mediatorRow := [3/2, -1] in RectangularMatrices(1, 2, Q)",
          "let g0 := row_linear_map(2, Q, mediatorRow)",
          "let h1 := factor(g0) through first with cone using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization)",
          "let underlyingH1 := map h1 along «fun.bilin_module.forget»(ℚ, ℚ)"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      for port in #["obj", "hom", "forward", "backward", "factor"] do
        unless dispatched.contains s!"lift.bilin_module.restrict#{port}" do
          throwError "the lift's {port} was not dispatched to its port: {dispatched}"
      -- The domain of i1 is the object X1 already returned: it is not staged again (T046, T049;
      -- execution contract: an existing binding retains its occurrence).
      unless (dispatched.filter (· == "lift.bilin_module.restrict#obj")).size == 1 do
        throwError "the lift's object was staged again for a later use: {dispatched}"
      let requests := ((← liftM (m := IO) <| IO.FS.readFile log).splitOn "\n").filter (!·.isEmpty)
      -- The functor's object action on X1 and its map action on i1 receive the values that the
      -- lift's leaf returned: provider data goes back to its owner as its export token
      -- (`opaqueData`). The map's source endpoint is that same X1; its target is the named X.
      let arguments := fun (operation : String) (first : Bool) => do
        let matching := requests.filter (·.startsWith s!"\{\"op\": \"{operation}\"")
        let some line := if first then matching.head? else matching.getLast?
          | throwError "the peer received no request for {operation}: {requests}"
        let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
        let .ok values := (request.getObjValD "context").getObjValAs? (Array Json) "arguments"
          | throwError "the request has no arguments: {line}"
        pure values
      let returned := fun (argument : Json) =>
        (argument.getObjValAs? String "ctor").toOption == some "opaqueData"
      let objectAction ← arguments "fun.bilin_module.forget" false
      let mapAction ← arguments "fun.bilin_module.forget#map" true
      let #[carrierOf] := objectAction
        | throwError "the object action has a different arity: {objectAction}"
      let #[source, _, inclusion] := mapAction
        | throwError "the map action has a different arity: {mapAction}"
      unless returned carrierOf && returned inclusion && source == carrierOf do
        throwError "the later uses did not receive the returned X1 and i1: {objectAction} {mapAction}"
      -- The map action on h1 receives the value that the factor's leaf returned.
      let factorAction ← arguments "fun.bilin_module.forget#map" false
      let #[_, _, factor] := factorAction
        | throwError "the factor's map action has a different arity: {factorAction}"
      unless returned factor && factor != inclusion do
        throwError "the map action on h1 did not receive the returned factor: {factorAction}"
      let some line := requests.find? (·.startsWith "{\"op\": \"lift.bilin_module.restrict#obj\"")
        | throwError "the peer received no lift request: {requests}"
      let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
      let .ok parameters := (request.getObjValD "context").getObjValAs? (Array Json) "parameters"
        | throwError "the lift request has no parameters: {line}"
      -- Every non-proof argument of the evidence `forgetMonoLift (R) [CommRing R] (W)
      -- [AddCommGroup W] [Module R W]`, in order, as for every published family: ℚ at R and W.
      let rationals := Json.mkObj [("args", .arr #[]), ("ctor", "obj.sets.rationals")]
      unless parameters.size == 5 && parameters[0]! == rationals && parameters[2]! == rationals do
        throwError "the lift request does not carry the evidence parameters (ℚ, ℚ): {line}"
      -- Each later lift port receives the earlier outputs, in the order of the contract's ports
      -- (api/wire-examples.md, "Prescribed subobject lifts"): `#hom` the returned X1, `#forward`
      -- X1 and i1, `#backward` X1, i1 and the forward comparison, as its context `bindings`.
      let bindings := fun (port : String) => do
        let some line := requests.find? (·.startsWith s!"\{\"op\": \"lift.bilin_module.restrict#{port}\"")
          | throwError "the peer received no request for #{port}: {requests}"
        let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
        let .ok values := (request.getObjValD "context").getObjValAs? (Array Json) "bindings"
          | throwError "the #{port} request has no bindings: {line}"
        pure values
      let hom ← bindings "hom"
      let forward ← bindings "forward"
      let backward ← bindings "backward"
      unless hom == #[carrierOf] && forward == #[carrierOf, inclusion] && backward.size == 3 &&
          backward.extract 0 2 == forward && returned backward[2]! do
        throwError "the lift ports did not receive their earlier outputs: {hom} {forward} {backward}"
    finally liftM (m := IO) session.close
  finally setEnv environment
