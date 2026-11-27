module

import CasRuntime.Session
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Command Term CasRuntime CasCompiler CasCatalogue

run_cmd do
  let preparationStarted ← IO.monoMsNow
  let environment ← getEnv
  try
    let input : System.FilePath := "tests/acceptance/sets.cas"
    let contents ← IO.FS.readFile input
    let original ← liftCoreM <| SourceFile.parse input.toString contents
    let some item := (original.items[0]? : Option (TSyntax `cas_item))
      | throwError "the original sets file has no first statement"
    let `(cas_item| test $id:ident $_:str : $statement:cas_stmt) := item
      | throwError "the original first sets item is not a named assertion"
    unless id.getId == `sets.card.z4_cubed &&
        (statement.raw.reprint.getD "").trimAscii.toString == "assert |(ℤ/4)^3| = 64" do
      throwError "the cost control changed the original sets.card.z4_cubed assertion"
    let root ← IO.currentDir
    let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
    let path := root / ".tmp" / s!"session-cost-{nonce}.json"
    IO.FS.createDirAll (root / ".tmp")
    IO.FS.writeFile path
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let session ← liftTermElabM <| KernelSession.start (some path)
      (computationOnly := true) (preparationStarted? := some preparationStarted)
    try
      unless session.kernel.rejected.isEmpty do
        throwError "the empty cost-control manifest produced a rejected registration"
      let run ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
        original.withContext (session.run statement)
      unless run.attempted && run.outcome.stratum? == some "noImplementation" do
        throwError "the original cardinality computation ended in {run.outcome.kind}: {run.outcome.detail}"
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "the empty manifest dispatched a leaf implementation"
      unless (← IO.FS.readFile input) == contents do
        throwError "the original sets source changed during the cost control"
      let events ← CasTools.ApplicationLog.readEvents session.kernel.log.path
      let dataOf (event : Json) : Json := (event.getObjVal? "data").toOption.getD .null
      let isEvent (name : String) (event : Json) : Bool :=
        (event.getObjValAs? String "event").toOption == some name
      unless (events.filter (isEvent "statement.started")).size == 1 &&
          (events.filter (isEvent "statement.finished")).size == 1 do
        throwError "the cost control did not execute exactly one original statement"
      unless events.any (fun event => isEvent "realization.missing" event &&
          ((dataOf event).getObjValAs? String "operation").toOption == some "meth.cardinality") do
        throwError "the original cardinality gap lost its registered meth.cardinality address"
      let prepared := events.filter (isEvent "request.prepared")
      let executed := events.filter (isEvent "request.execute")
      unless !prepared.isEmpty && !executed.isEmpty do
        throwError "the original cardinality computation lost its prepared or executed request"
      for line in (← IO.FS.readFile session.kernel.log.path).splitOn "\n" do
        if line.trimAscii.toString.isEmpty then continue
        let .ok wire := Json.parse line
          | throwError "the actual application log is not JSON"
        unless isEvent "request.prepared" wire || isEvent "request.execute" wire do continue
        let .ok sequence := wire.getObjValAs? Nat "sequence"
          | throwError "the actual observation lost its event identity"
        let some event := events[sequence]?
          | throwError "the decoded observation is outside the actual event stream"
        let .ok encoded := wire.getObjVal? "data"
          | throwError "the actual observation lost its encoded descriptor"
        unless (wire.getObjValAs? Nat "schema").toOption == some 2 &&
            (event.getObjValAs? Nat "sequence").toOption == some sequence &&
            CasTools.JsonGraph.encode (dataOf event) == encoded do
          throwError "the actual observation did not decode to its complete canonical descriptor"
        let descriptor := dataOf event
        let .ok native := descriptor.getObjVal? "native"
          | throwError "the complete observation lost its native descriptor"
        let .ok request := native.getObjVal? "request"
          | throwError "the complete observation lost its prepared request"
        let .ok readable := descriptor.getObjVal? "readable"
          | throwError "the complete observation lost its readable descriptor"
        let required : Array (String × Json × Array String) := #[
          ("descriptor", descriptor, #["native", "readable", "selection", "sourceSnapshot"]),
          ("native", native, #["request", "nativeExpressions"]),
          ("request", request, #["program", "occurrence", "action", "source", "scope",
            "outputs", "record", "environment", "origin", "application", "roles", "actualArguments"]),
          ("readable", readable, #["source", "context", "arguments", "results", "captures",
            "application", "bound", "sourceDependencies"])]
        for (name, document, expected) in required do
          let .ok fields := document.getObj?
            | throwError "the complete observation's {name} is not an object"
          let actual := fields.toList.toArray.map Prod.fst
          unless actual.size == expected.size && expected.all actual.contains do
            throwError "the complete observation changed its {name} field inventory"
      for event in executed do
        let .ok native := (dataOf event).getObjVal? "native"
          | throwError "the executed observation lost its native descriptor"
        let .ok request := native.getObjVal? "request"
          | throwError "the executed observation lost its prepared request"
        let .ok program := request.getObjVal? "program"
          | throwError "the executed observation lost its program identity"
        let .ok occurrence := request.getObjVal? "occurrence"
          | throwError "the executed observation lost its occurrence identity"
        let matching ← prepared.filterM fun candidate => do
          let .ok native := (dataOf candidate).getObjVal? "native"
            | throwError "the prepared observation lost its native descriptor"
          let .ok request := native.getObjVal? "request"
            | throwError "the prepared observation lost its request"
          pure ((request.getObjVal? "program").toOption == some program &&
            (request.getObjVal? "occurrence").toOption == some occurrence)
        let #[original] := matching
          | throwError "the executed observation lost its one original prepared descriptor"
        for field in #["native", "readable"] do
          let .ok before := (dataOf original).getObjVal? field
            | throwError "the prepared observation lost its {field} descriptor"
          let .ok after := (dataOf event).getObjVal? field
            | throwError "the executed observation lost its {field} descriptor"
          unless CasTools.JsonGraph.encode before == CasTools.JsonGraph.encode after do
            throwError "the execution changed its complete original {field} descriptor"
    finally
      session.close
  finally
    setEnv environment
