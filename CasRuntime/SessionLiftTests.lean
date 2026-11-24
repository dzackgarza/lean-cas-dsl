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
from that same retained record. The setup views select actual input fields before registration
selection (T026); the lift's object and map ports still require their missing leaves.
Functional work may use the heartbeats it needs (constitution C21). -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← liftM (m := IO) IO.currentDir
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "kernel-lift-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let mut session ← KernelSession.start (some path)
    try
      let statements := #[
          ("let Q := ℚ in CommutativeRings", "holds"),
          ("let Qring := view Q along «fun.commutative_rings.ring»()", "holds"),
          ("let scalarModule := RegularModule(Qring)", "holds"),
          ("let X := DegeneratePlane()", "holds"),
          ("let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)", "holds"),
          ("let i0(t) := (2*t, -2*t) in scalarModule → sourceModule", "holds"),
          ("let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)", "holds"),
          -- These two fields demand their published lift ports after the input-only setup.
          ("let X1 := first.obj()", "gap"),
          ("let i1 := first.hom()", "gap")]
      let mut originalQ : Option (CasCompiler.BindingId × ValueBinding) := none
      for (text, kind) in statements, index in [:statements.size] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
        if index == 0 then
          let some entry := session.source.context.entries.back?
            | throwError "the Q declaration did not publish its source binding"
          unless entry.userName == `Q do
            throwError "the first lift declaration did not publish Q"
          let some value := session.value? entry.id
            | throwError "the Q declaration discarded its actual runtime value"
          originalQ := some (entry.id, value)
        if index == 1 then
          -- The registered ring view has exactly these two native input routes. Keep
          -- their actual field identities; no ring operation or provider answer is used.
          let some (qId, q) := originalQ
            | throwError "the ring view lost its original Q input"
          let some currentQ := session.value? qId
            | throwError "the ring view discarded its original Q binding"
          unless currentQ.value == q.value && currentQ.associationIds == q.associationIds do
            throwError "the ring view changed the retained Q occurrence"
          let some entry := session.source.context.entries.back?
            | throwError "the ring view did not publish its source binding"
          unless entry.userName == `Qring do
            throwError "the ring view published a different source binding"
          let some ring := session.value? entry.id
            | throwError "the wholly input-projected ring view has no actual value"
          let graph := (← SessionSnapshot.current).graph
          let some node := graph.find ring.value
            | throwError "the ring view is outside the committed graph"
          let some fields := node.payload.data.storedFields?
            | throwError "the ring view did not retain its complete native fields"
          unless fields.size == 2 do
            throwError "the ring view changed its complete native field arity"
          let select (parent : ValueBinding) (projection : Name) : MetaM ValueBinding := do
            let some field := parent.role.fields.find? (·.projection == projection)
              | throwError "the ring view lost the native field {projection}"
            let some index := field.wireIndex
              | throwError "the ring view erased a computational field {projection}"
            let .ok value := graph.project parent index
              | throwError "the ring view has no stored field {projection}"
            return value
          let originalCarrier ← select q ``CommRingCat.carrier
          let carrier ← select ring ``RingCat.carrier
          let ringStructure ← select ring ``RingCat.ring
          unless carrier.value == originalCarrier.value &&
              originalCarrier.associationIds.toList.isPrefixOf carrier.associationIds.toList do
            throwError "the ring view replaced Q's actual carrier"
          for (field, path) in #[(carrier, #[``CommRingCat.carrier]),
              (ringStructure, #[``CommRingCat.commRing, ``CommRing.toRing])] do
            let .ok (some baseline) := graph.projectionBasis field q path
              | throwError "the ring view lost an exact original Q projection"
            unless field.value == baseline.value &&
                baseline.associationIds.toList.isPrefixOf field.associationIds.toList do
              throwError "the ring view changed its source-selected field occurrence"
          unless (← session.kernel.dispatches.get).isEmpty do
            throwError "a wholly input-projected ring view dispatched a registration"
        if index ≥ 7 then
          let port := if index == 7 then "obj" else "hom"
          unless (run.outcome.detail.splitOn "NoImplementation").length > 1 &&
              (run.outcome.detail.splitOn s!"lift.bilin_module.restrict#{port}").length > 1 do
            throwError "`{text}` did not reach its missing lift port: {run.outcome.detail}"
          unless (← session.kernel.dispatches.get).isEmpty do
            throwError "the missing lift port dispatched a registration"
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
      -- X1 and i1, `#backward` X1, i1 and the forward comparison, with their original
      -- computational source-field slots in the complete dependent `bindings` envelope.
      let bindings := fun (port : String) => do
        let some line := requests.find? (·.startsWith s!"\{\"op\": \"lift.bilin_module.restrict#{port}\"")
          | throwError "the peer received no request for #{port}: {requests}"
        let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
        let .ok values := (request.getObjValD "context").getObjValAs? (Array Json) "bindings"
          | throwError "the #{port} request has no bindings: {line}"
        let mut retained := #[]
        for value in values, index in [:values.size] do
          let .ok () := CasCatalogue.Backend.checkServiceFields #["slot", "value"] value
            | throwError "the #{port} binding lost its exact dependent envelope"
          unless (value.getObjValAs? Nat "slot").toOption == some index do
            throwError "the #{port} binding changed its original source-field slot"
          let .ok data := value.getObjVal? "value"
            | throwError "the #{port} binding lost its original retained value"
          retained := retained.push data
        pure retained
      let hom ← bindings "hom"
      let forward ← bindings "forward"
      let backward ← bindings "backward"
      unless hom == #[carrierOf] && forward == #[carrierOf, inclusion] && backward.size == 3 &&
          backward.extract 0 2 == forward && returned backward[2]! do
        throwError "the lift ports did not receive their earlier outputs: {hom} {forward} {backward}"
    finally liftM (m := IO) session.close
  finally setEnv environment
