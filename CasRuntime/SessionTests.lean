module

import CasRuntime.Session
import CasCatalogue.TestSuite
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCatalogue.TestSuite
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients

open Lean Meta Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

run_cmd liftTermElabM do
  let preparationStarted ← IO.monoMsNow
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_session_peer.py"
    let registration := fun (operation : String) => Json.mkObj [("operation", operation),
      ("input", if operation == "meth.cardinality" then "obj.sets.fin" else s!"{operation}#input"),
      ("backend", "peer")]
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul", "meth.cardinality"].map
        registration ++ #[Json.mkObj [("operation", "op.unpublished"),
          ("input", "op.unpublished#input"), ("backend", "peer")]]))]
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "kernel-session-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
      (preparationStarted? := some preparationStarted)
    try
      unless session.kernel.rejected.size == 1 do
        throwError "an unpublished operation address was admitted as a registration"
      let expected : Array (String × String) := #[
        ("let a := 17 + 29 in ℤ", "holds"),
        ("assert a = 46 in ℤ", "holds"),
        ("assert a = 47 in ℤ", "wrong"),
        ("let b := a · a in ℤ", "holds"),
        ("assert b = 2116 in ℤ", "holds"),
        ("let d := a · 2 in ℤ", "holds"),
        ("assert d = 92 in ℤ", "holds"),
        ("let c := |Fin(3)|", "holds"),
        ("assert c = 3", "holds"),
        ("assert c = 4", "wrong"),
        ("assert implemented |Fin(2)|", "holds"),
        ("assert 2 + 2 = 4 in ℤ", "holds"),

        ("let x := 3 in ℤ/5", "holds")]
      for (text, kind) in expected do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session

      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["op.rings.add", "op.rings.mul", "op.rings.mul", "op.rings.add",
          "meth.cardinality", "meth.cardinality"] do
        throwError "the session dispatched {dispatched}"
    finally liftM (m := IO) session.close

    let emptyPreparationStarted ← IO.monoMsNow
    setEnv environment
    let emptyPath := root / ".tmp" / "kernel-session-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile emptyPath
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let bare ← KernelSession.start (some emptyPath)
      (preparationStarted? := some emptyPreparationStarted)
    try
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt "let a := 17 + 29 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let run ← withoutErrToSorry <| bare.run ⟨statement⟩
      unless run.outcome.kind == "gap" do
        throwError "a statement with no installed leaf is {run.outcome.kind}, not a gap"

      let question ← match Parser.runParserCategory (← getEnv) `cas_stmt "assert a = 46 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let asked ← withoutErrToSorry <| run.session.run ⟨question⟩
      unless asked.outcome.kind == "holds" do
        throwError "a definition with no installed leaf is lost: {asked.outcome.kind} ({asked.outcome.detail})"

      let mut written := asked.session
      for (text, kind) in #[("let h := t ↦ t² + 1 in ℤ → ℤ", "holds"),
          ("let hp(t) := t^2 + 1 in ℤ → ℤ", "holds"), ("assert h = hp", "holds")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let step ← withoutErrToSorry <| written.run ⟨statement⟩
        unless step.outcome.kind == kind do
          throwError "`{text}` is {step.outcome.kind} ({step.outcome.detail}), not {kind}"
        written := step.session
    finally liftM (m := IO) bare.close
  finally setEnv environment

run_cmd liftTermElabM do
  let mut preparationStarted ← IO.monoMsNow
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    for (mode, kind) in #[("unavailable", "unavailable"), ("unsupported", "gap")] do
      setEnv environment
      let log := root / ".tmp" / s!"kernel-session-{mode}.log"
      liftM (m := IO) <| IO.FS.writeFile log ""
      let manifest := Json.mkObj [
        ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
          ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString,
            "--fail-first-add", mode, log.toString])]]),
        ("registrations", .arr #[Json.mkObj [("operation", "op.rings.add"),
          ("input", "op.rings.add#input"), ("backend", "peer")]])]
      let path := root / ".tmp" / s!"kernel-session-{mode}.json"
      liftM (m := IO) <| IO.FS.writeFile path manifest.compress
      let mut session ← KernelSession.start (some path)
        (preparationStarted? := some preparationStarted)
      try
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt
            "let failedSum := 17 + 29 in ℤ" with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let failed ← withoutErrToSorry <| session.run ⟨statement⟩
        unless failed.outcome.kind == kind do
          throwError "the real {mode} reply became {failed.outcome.kind}: {failed.outcome.detail}"
        session := failed.session
        let some original := session.source.context.entries.back?
          | throwError "a failed computation discarded its checked source definition"
        unless original.userName == `failedSum && original.value.isSome &&
            (session.value? original.id).isNone do
          throwError "the failed definition lost its meaning or published a runtime result"
        let before ← SessionSnapshot.current
        let traffic ← liftM (m := IO) <| IO.FS.readFile log
        unless ((traffic.splitOn "\n").filter (!·.isEmpty)).length == 1 do
          throwError "the initial failure did not come from exactly one real provider request"
        for text in #["let failedAlias := failedSum", "let failedDependent := failedAlias",
            "let failedExpression := failedDependent + 1 in ℤ",
            "assert implemented failedDependent", "assert implemented failedExpression",
            "assert implemented failedSum",
            "context do\nassert implemented failedDependent\nend"] do
          let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
            | .ok statement => pure statement
            | .error error => throwError "the statement did not parse: {error}"
          let declarations := session.source.context.entries.size
          let run ← withoutErrToSorry <| session.run ⟨statement⟩
          unless run.outcome.kind == kind &&
              (run.outcome.detail.splitOn failed.outcome.detail).length > 1 do
            throwError "`{text}` lost the original {mode} outcome: \
              {run.outcome.kind} ({run.outcome.detail})"
          session := run.session
          if text.startsWith "let" then
            let some entry := session.source.context.entries.back?
              | throwError "a failed dependent definition was not retained"
            unless session.source.context.entries.size == declarations + 1 &&
                entry.value.isSome && (session.value? entry.id).isNone do
              throwError "a failed dependent definition published a value or lost its meaning"

        let question ← match Parser.runParserCategory (← getEnv) `cas_stmt
            "assert failedDependent = 46 in ℤ" with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let computedSession := { session with computationOnly := true }
        let computed ← withoutErrToSorry <| computedSession.run ⟨question⟩
        unless computed.outcome.kind == kind &&
            (computed.outcome.detail.splitOn failed.outcome.detail).length > 1 do
          throwError "a computed question lost the original {mode} outcome: \
            {computed.outcome.kind} ({computed.outcome.detail})"
        let unchanged ← SessionSnapshot.current
        unless unchanged.id == before.id && unchanged.graph.sameRevision before.graph &&
            unchanged.outputBatches.size == before.outputBatches.size &&
            (← session.kernel.dispatches.get).map (·.operation) == #["op.rings.add"] &&
            (← liftM (m := IO) <| IO.FS.readFile log) == traffic do
          throwError "a later failed-definition use retried or published a computation"

        for text in #["assert failedSum = 46 in ℤ", "let freshSum := 17 + 29 in ℤ",
            "assert freshSum = 46 in ℤ"] do
          let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
            | .ok statement => pure statement
            | .error error => throwError "the statement did not parse: {error}"
          let run ← withoutErrToSorry <| session.run ⟨statement⟩
          unless run.outcome.kind == "holds" do
            throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
          session := run.session
        let traffic ← liftM (m := IO) <| IO.FS.readFile log
        unless (← session.kernel.dispatches.get).map (·.operation) ==
            #["op.rings.add", "op.rings.add"] &&
            ((traffic.splitOn "\n").filter (!·.isEmpty)).length == 2 do
          throwError "a fresh addition did not make exactly its own independent invocation"
      finally liftM (m := IO) session.close
      preparationStarted ← IO.monoMsNow
  finally setEnv environment

run_cmd liftTermElabM do
  let preparationStarted ← IO.monoMsNow
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← IO.currentDir
    let python := (← IO.FS.realPath contract) / ".venv/bin/python"
    IO.FS.createDirAll (root / ".tmp")
    let traffic := root / ".tmp/kernel-source-child-parity.jsonl"
    IO.FS.writeFile traffic ""
    let registration := fun (operation : String) => Json.mkObj [
      ("operation", toJson operation), ("input", toJson s!"{operation}#input"),
      ("backend", "peer")]
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson (root / "scripts/probes/kernel_session_peer.py").toString,
          "--reference-add", toJson traffic.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul"].map registration))]
    let path := root / ".tmp/kernel-source-child-parity-leaves.json"
    IO.FS.writeFile path manifest.compress
    let initial ← KernelSession.start (some path) (computationOnly := true)
      (preparationStarted? := some preparationStarted)
    try
      let mut session := initial
      let mut originals : Array (BindingId × ValueBinding) := #[]
      for (name, text) in #[
          (`R, "let R := ℤ in Rings"),
          (`a, "let a := 17 in R"),
          (`two, "let two := 2 in R"),
          (`direct, "let direct := a + a in R"),
          (`mediated, "let mediated := a · two in R")] do
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "the public provider-parity statement did not parse: {text}"
        let run ← withoutErrToSorry <| session.run ⟨parsed⟩
        unless run.outcome.kind == "holds" && run.attempted && run.published do
          throwError "the public provider-parity statement did not commit: {text}: {run.outcome.detail}"
        session := run.session
        let some entry := (← SourceTest.authoredEntries
            session.source.context session.source.selections).back?
          | throwError "the public provider-parity statement lost its authored result"
        unless entry.userName == name do
          throwError "the public provider-parity statement changed its original result binding"
        let some actual := session.value? entry.id
          | throwError "the public provider-parity statement lost its actual runtime reference"
        originals := originals.push (entry.id, actual)
      let #[ring, operand, _, direct, mediated] := originals
        | throwError "the public provider-parity control changed its original statement count"
      let snapshot ← SessionSnapshot.current
      let codes ← session.kernel.codes.get
      let additionReceipt := fun (value : ValueBinding) => do
        let mut receipts : Array CommittedReceipt := #[]
        for application in value.applications do
          let some receipt := snapshot.receipt application.association.occurrence
            | continue
          let .invocation dispatch _ _ := receipt.association.producer | continue
          let .primitive identity := dispatch.selected | continue
          unless identity.registration.operation == "op.rings.add" do continue
          unless dispatch.occurrence == receipt.association.request.occurrence do
            throwError "the addition receipt changed its original dispatch occurrence"
          if receipts.any (fun prior => prior.association.request.occurrence ==
              receipt.association.request.occurrence) then continue
          receipts := receipts.push receipt
        let #[receipt] := receipts
          | throwError "the public result lost its one actual published addition invocation"
        return receipt
      let originalFamily := fun (receipt : CommittedReceipt) => do
        let .apply callable _ _ := receipt.association.request.action
          | throwError "the published addition lost its original native callable demand"
        let code ← IO.ofExcept <| (snapshot.graph.callable callable).mapError IO.userError
        let some node := snapshot.graph.find code.value
          | throwError "the published addition lost its actual callable node"
        let .closure program _ := node.payload.data
          | throwError "the published addition lost its retained family code"
        let some (.family family path) := codes[program]?
          | throwError "the published addition lost its original prepared family"
        receipt.association.request.requireFamily family path snapshot.graph codes
        return (family, path)
      let directReceipt ← additionReceipt direct.2
      let childReceipt ← additionReceipt mediated.2
      unless directReceipt.association.request.occurrence !=
          childReceipt.association.request.occurrence do
        throwError "the direct operation and provider child shared an invocation occurrence"
      let (directOriginal, directPath) ← originalFamily directReceipt
      let (childOriginal, childPath) ← originalFamily childReceipt
      let .primitive (.registered directFamily) directUniverses := directOriginal.action
        | throwError "the direct addition changed its retained published family"
      let .primitive (.registered childFamily) childUniverses := childOriginal.action
        | throwError "the child addition changed its retained published family"
      unless (SelectedApplicationFamily.registered directFamily).exactlyMatches
          (.registered childFamily) && directUniverses == childUniverses &&
          directPath.map (·.projection) == childPath.map (·.projection) do
        throwError "the provider child changed the original complete addition family"
      let .invocation directDispatch _ _ := directReceipt.association.producer
        | throwError "the direct addition lost its original provider dispatch"
      let .invocation childDispatch _ _ := childReceipt.association.producer
        | throwError "the requested addition lost its original provider dispatch"
      unless directDispatch.selected == childDispatch.selected do
        throwError "the provider child changed the original selected addition registration"
      for (receipt, family) in #[(directReceipt, directOriginal), (childReceipt, childOriginal)] do
        let some original := snapshot.receipt family.occurrence
          | throwError "the published addition lost its original family completion"
        family.requirePreparation original.association.request.roles.scope
        let #[actualRing] ← IO.ofExcept <|
            (original.association.inputs.arguments snapshot.graph).mapError IO.userError
          | throwError "the published addition changed its complete native parameter telescope"
        let #[pair] ← IO.ofExcept <|
            (receipt.association.inputs.arguments snapshot.graph).mapError IO.userError
          | throwError "the published addition changed its complete native operand telescope"
        unless retainsReference ring.2 actualRing do
          throwError "the direct or requested addition replaced its original selected ring"
        for index in #[0, 1] do
          let actual ← IO.ofExcept <| (snapshot.graph.project pair index).mapError IO.userError
          unless retainsReference operand.2 actual do
            throwError "the direct or requested addition replaced an original operand occurrence"
        unless receipt.association.request.observation.sourceSnapshot.isSome &&
            !receipt.association.request.selections.isEmpty &&
            !family.selections.isEmpty do
          throwError "the direct or requested addition discarded its original typed source meaning"
      for text in #["assert direct = 34 in R", "assert mediated = 34 in R"] do
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "the original public arithmetic check did not parse"
        let run ← withoutErrToSorry <| session.run ⟨parsed⟩
        unless run.outcome.kind == "holds" && run.published do
          throwError "the public arithmetic check did not observe the computed result: {run.outcome.detail}"
        session := run.session
      let expected := #["op.rings.add", "op.rings.mul", "op.rings.add"]
      unless (← session.kernel.dispatches.get).map (·.operation) == expected do
        throwError "the direct and provider-requested operations changed their actual dispatches"
      let mut observed : Array String := #[]
      for line in (← IO.FS.readFile traffic).splitOn "\n" do
        if line.isEmpty then continue
        let .ok frame := Json.parse line
          | throwError "the independent provider traffic log contains an invalid frame"
        let .ok operation := frame.getObjValAs? String "op"
          | throwError "the independent provider traffic log lost its operation"
        observed := observed.push operation
      unless observed == expected do
        throwError "the provider did not receive the original direct and requested operations"
    finally initial.close
  finally setEnv environment

run_cmd do
  let preparationStarted ← IO.monoMsNow
  let environment ← getEnv
  try
    let root ← IO.currentDir
    let contract ← CasCatalogue.Backend.packageDir CasCatalogue.Backend.contractPackage
    let python := (← IO.FS.realPath contract) / ".venv/bin/python"
    let logDirectory : System.FilePath :=
      (← IO.getEnv "CAS_APPLICATION_LOG_DIR").getD "timing/application"
    let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
    let evidence := logDirectory / "controls" / nonce
    IO.FS.createDirAll evidence
    let traffic := evidence / "peer.jsonl"
    IO.FS.writeFile traffic ""
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString,
          "--reference-add", traffic.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul"].map fun operation =>
        Json.mkObj [("operation", toJson operation), ("input", toJson s!"{operation}#input"),
          ("backend", "peer")]))]
    let manifestPath := evidence / "leaves.json"
    IO.FS.writeFile manifestPath manifest.compress
    let input := root / "tests/runtime/application_log.cas"
    let initial ← liftTermElabM <| KernelSession.start (some manifestPath) (computationOnly := true)
      (preparationStarted? := some preparationStarted)
    let readEvents (path : System.FilePath) : IO (Array Json) := do
      let mut events := #[]
      for line in (← IO.FS.readFile path).splitOn "\n" do
        if line.isEmpty then continue
        let event ← IO.ofExcept <| (Json.parse line).mapError IO.userError
        events := events.push event
      return events
    let dataOf (event : Json) : Json := (event.getObjVal? "data").toOption.getD .null
    let isEvent (name : String) (event : Json) : Bool :=
      (event.getObjValAs? String "event").toOption == some name
    try
      let (rows, _) ← CasCatalogue.Language.runFile initial input
      unless rows.map (·.id) == #["logging.direct", "logging.nested"] &&
          rows.all (fun row => row.kind == "holds" && row.attempted && row.published) do
        throwError "the complete public log fixture did not execute its original assertions: {toJson rows}"
      let events ← CasTools.ApplicationLog.readEvents initial.kernel.log.path
      for event in events, ordinal in [:events.size] do
        unless (event.getObjValAs? Nat "sequence").toOption == some ordinal &&
            (event.getObjValAs? String "session").toOption == some initial.kernel.log.session do
          throwError "the session log changed its sequence or original diagnostic session"
        let .ok parents := event.getObjValAs? (Array Nat) "parents"
          | throwError "the session log lost its causal event parents"
        unless parents.all (· < ordinal) do
          throwError "a diagnostic event references a missing or later parent"
      for (name, count) in #[("computation.started", 6), ("computation.timing", 6),
          ("statement.started", 6), ("statement.finished", 6),
          ("statement.child.reading", 2), ("statement.child.started", 2),
          ("statement.child.finished", 2), ("binding.retained", 5)] do
        unless (events.filter (isEvent name)).size == count do
          throwError "the public file log lost an original event: {name}"
      for event in events.filter (isEvent "statement.started") do
        let data := dataOf event
        let .ok source := data.getObjValAs? String "source"
          | throwError "a statement log lost its source text"
        let .ok position := data.getObjVal? "position"
          | throwError "a statement log lost its original source range"
        unless !source.isEmpty && (position.getObjValAs? String "file").toOption ==
            some input.toString && (position.getObjValAs? Nat "startByte").isOk &&
            (position.getObjValAs? Nat "stopByte").isOk do
          throwError "a statement log replaced its original source text or position"
      unless (events.filter (isEvent "statement.read")).size == 7 do
        throwError "the public file log omitted a selected source interpretation"
      for event in events.filter (isEvent "statement.read") do
        let .ok scope := (dataOf event).getObjVal? "scope"
          | throwError "a source reading log lost its complete scope"
        unless (scope.getObjVal? "context").isOk &&
            (scope.getObjVal? "selections").isOk &&
            (scope.getObjVal? "nativeExpressions").isOk do
          throwError "a source reading log discarded its native typed interpretation"
      let dispatched := events.filter (isEvent "dispatch")
      let peer ← readEvents traffic
      unless dispatched.size == 3 && peer.size == 3 do
        throwError "the public file did not retain its three actual provider invocations"
      for event in dispatched, received in peer do
        let data := dataOf event
        let .ok selected := data.getObjVal? "selected"
          | throwError "a dispatch log lost its actual selected registration"
        let .ok operation := selected.getObjValAs? String "operation"
          | throwError "a dispatch log lost its actual operation"
        unless (received.getObjValAs? String "op").toOption == some operation &&
            (selected.getObjValAs? String "input").toOption == some s!"{operation}#input" &&
            (selected.getObjValAs? String "backend").toOption == some "peer" &&
            (data.getObjVal? "operands").toOption == (received.getObjVal? "context").toOption do
          throwError "the dispatch log does not match the independent provider's exact operands"
        let .ok occurrence := data.getObjVal? "occurrence"
          | throwError "a dispatch log lost its exact occurrence"
        let .ok request := data.getObjVal? "request"
          | throwError "a dispatch log lost its prepared typed request"
        let .ok native := request.getObjVal? "native"
          | throwError "a dispatch log lost its complete native request"
        let .ok prepared := native.getObjVal? "request"
          | throwError "a dispatch log lost its original prepared request graph"
        let .ok source := prepared.getObjVal? "source"
          | throwError "a dispatch log lost its complete selected source"
        unless (request.getObjVal? "sourceSnapshot").toOption.any (· != .null) &&
            (source.getObjValAs? (Array Json) "selections").toOption.any (!·.isEmpty) do
          throwError "the actual dispatch discarded its source or selected request observation"
        unless events.any (fun candidate => isEvent "request.prepared" candidate &&
            ((dataOf candidate).getObjVal? "native").toOption == some native) do
          throwError "the dispatch did not retain its original prepared execution request"
        for phase in #["reply.admission.started", "reply.admitted"] do
          unless events.any (fun candidate => isEvent phase candidate &&
              ((dataOf candidate).getObjVal? "occurrence").toOption == some occurrence) do
            throwError "the actual reply lost its result-admission event: {phase}"
      let completed := (events.filter (isEvent "computation.timing")).map dataOf
      let #[fileStarted] := (events.filter (isEvent "file.started")).map dataOf
        | throwError "the public file lost its one actual file start"
      let .ok sharedSetup := fileStarted.getObjValAs? Nat "sharedFileSetupMilliseconds"
        | throwError "the public file lost its measured parsing and read setup"
      let mut setup := sharedSetup
      for definition in completed.take 4 do
        let .ok elapsed := definition.getObjValAs? Nat "executionMilliseconds"
          | throwError "a successful source definition lost its actual timing"
        setup := setup + elapsed
      for computation in completed.drop 4 do
        unless (computation.getObjValAs? Nat "cumulativeSetupMilliseconds").toOption == some setup do
          throwError "a later statement discarded its retained source setup after an assertion"
      unless (events.filter (isEvent "file.finished")).size == 1 &&
          (events.filter (isEvent "statement.interrupted")).isEmpty &&
          (events.filter (isEvent "reply.rejected")).isEmpty do
        throwError "the complete original file log recorded an incomplete or rejected run"
    finally initial.close
    let emptyPreparationStarted ← IO.monoMsNow
    setEnv environment
    let emptyPath := evidence / "empty-leaves.json"
    IO.FS.writeFile emptyPath
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let bare ← liftTermElabM <| KernelSession.start (some emptyPath) (computationOnly := true)
      (preparationStarted? := some emptyPreparationStarted)
    try
      let run ← CasCatalogue.Language.runStatement bare "let a := 17 + 29 in ℤ"
      unless run.outcome matches .noImplementation _ do
        throwError "the public missing-registration control changed its failure stratum: {run.outcome.detail}"
      let rejectedText := "let timingRejected :="
      let rejected ← try
          discard <| CasCatalogue.Language.runStatement run.session rejectedText
          pure false
        catch error =>
          unless (← error.toMessageData.toString).startsWith "not a statement of the language:" do
            throw error
          pure true
      unless rejected do
        throwError "an incomplete public definition was accepted by the parser"
      let events ← CasTools.ApplicationLog.readEvents bare.kernel.log.path
      let #[failure] := (events.filter (isEvent "statement.parseFailed")).map dataOf
        | throwError "the public parse rejection lost its one completed diagnostic event"
      unless (failure.getObjValAs? String "source").toOption == some rejectedText &&
          (failure.getObjValAs? Nat "cumulativeSetupMilliseconds").toOption ==
            some run.session.setupMilliseconds do
        throwError "the public parse rejection changed its original source or retained setup"
      unless events.any (fun event => isEvent "realization.missing" event &&
          ((dataOf event).getObjValAs? String "operation").toOption == some "op.rings.add" &&
          ((dataOf event).getObjValAs? (Array String) "forms").toOption ==
            some #["op.rings.add#input"]) do
        throwError "the noImplementation log omitted the exact unregistered operation and input"
      unless (events.filter (isEvent "dispatch")).isEmpty &&
          events.any (fun event => isEvent "statement.finished" event &&
            ((dataOf event).getObjValAs? String "stratum").toOption == some "noImplementation") do
        throwError "the missing-registration log invented a dispatch or lost its classified outcome"
    finally bare.close
  finally setEnv environment
