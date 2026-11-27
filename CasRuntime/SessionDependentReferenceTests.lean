module

import CasRuntime.Session
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue

open Lean Meta Elab Command Term CasCompiler CasRuntime






run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← liftM (m := IO) IO.currentDir
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let manifest := root / ".tmp" / "session-dependent-reference-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile manifest
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let mut session ← KernelSession.start (some manifest) (computationOnly := true)
    try
      let declarations := #[
        "let S3 := Sym(3) in Groups",
        "let C3 := ZMod(3) in Groups",
        "let sigma := sign(3)",
        "let zero_map := trivial(S3, ZMod(2) in Groups)",
        "let identity_map := id(S3)"]
      let mut failures : Array String := #[]
      let mut originalS3 : Option (BindingId × ValueBinding) := none
      for text in declarations, index in [:declarations.size] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the original declaration did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
        if index == 0 then
          let some entry := session.source.context.entries.back?
            | throwError "the S3 declaration did not publish its source binding"
          unless entry.userName == `S3 do
            throwError "the first original declaration did not publish S3"
          match session.value? entry.id with
          | none =>
            failures := failures.push
              "the successful S3 declaration discarded its actual runtime reference"
          | some binding => originalS3 := some (entry.id, binding)
        if let some (id, original) := originalS3 then
          match session.value? id with
          | none =>
            failures := failures.push s!"`{text}` discarded the retained S3 reference"
          | some current =>
            unless current.value == original.value &&
                current.associationIds == original.associationIds do
              failures := failures.push s!"`{text}` replaced S3's retained occurrence"
            unless ((← SessionSnapshot.current).graph.find current.value).isSome do
              failures := failures.push s!"`{text}` retained S3 outside the committed graph"


      for text in #["assert |sigma.ker()| = 3", "assert |zero_map.ker()| = 6",
          "assert |identity_map.ker()| = 1"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the original kernel question did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "gap" &&
            (run.outcome.detail.splitOn "NoImplementation").length > 1 &&
            (run.outcome.detail.splitOn "meth.group_arrow_kernel").length > 1 do
          failures := failures.push
            s!"`{text}` did not reach the published kernel operation: \
              {run.outcome.kind} ({run.outcome.detail})"
        session := run.session
        if let some (id, original) := originalS3 then
          match session.value? id with
          | none => failures := failures.push s!"`{text}` discarded the retained S3 reference"
          | some current =>
            unless current.value == original.value &&
                current.associationIds == original.associationIds do
              failures := failures.push s!"`{text}` replaced S3's retained occurrence"
      unless (← session.kernel.dispatches.get).isEmpty do
        failures := failures.push "the empty-provider control dispatched a provider operation"
      unless failures.isEmpty do
        let detail := "\n".intercalate failures.toList
        throwError "source-dependent session regressions:\n{detail}"
    finally liftM (m := IO) session.close
  finally setEnv environment





run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_session_peer.py"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString, toJson ("--corrupt-add" : String)])]]),
      ("registrations", .arr #[Json.mkObj [("operation", "op.rings.add"),
        ("input", "op.rings.add#input"), ("backend", "peer")]])]
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "session-dependent-reference-corrupt-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      let mut failures : Array String := #[]
      let mut original : Option (BindingId × ValueBinding) := none
      let expected : Array (String × String) := #[
        ("let a := 17 + 29 in ℤ", "holds"),
        ("assert a = 46 in ℤ", "wrong"),
        ("assert (a = 46 in ℤ) using (proof(rfl))", "wrong"),
        ("let copy := a", "holds"),
        ("let copy2 := copy", "holds"),
        ("assert copy2 = 46 in ℤ", "wrong"),
        ("assert (copy2 = 46 in ℤ) using (proof(rfl))", "wrong")]
      for (text, kind) in expected do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the scalar observation control did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          failures := failures.push
            s!"`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
        if (text.splitOn "using (proof").length > 1 then
          unless run.published && run.conclusions.any (·.proof.isSome) do
            failures := failures.push
              s!"`{text}` did not retain source evidence through actual candidate observation"
        if text.startsWith "let" then
          let some entry := session.source.context.entries.back?
            | throwError "the scalar observation control lost its declared source binding"
          match session.value? entry.id with
          | none =>
            failures := failures.push s!"`{text}` discarded the actual scalar reference"
          | some binding =>
            match original with
            | none =>
              unless entry.userName == `a do
                throwError "the scalar observation control lost its original provider result"
              original := some (entry.id, binding)
            | some (_, actual) =>
              unless binding.value == actual.value &&
                  actual.associationIds.toList.isPrefixOf binding.associationIds.toList do
                failures := failures.push s!"`{text}` replaced the actual provider result"
            unless ((← SessionSnapshot.current).graph.find binding.value).isSome do
              failures := failures.push s!"`{text}` retained a scalar outside the committed graph"
        if let some (id, actual) := original then
          match session.value? id with
          | none => failures := failures.push s!"`{text}` discarded the original scalar reference"
          | some binding =>
            unless binding.value == actual.value &&
                binding.associationIds == actual.associationIds do
              failures := failures.push s!"`{text}` changed the original scalar reference"
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["op.rings.add"] do
        failures := failures.push
          s!"the scalar observation control dispatched {dispatched}, not exactly one addition"
      unless failures.isEmpty do
        let detail := "\n".intercalate failures.toList
        throwError "source-alias observation regressions:\n{detail}"
    finally liftM (m := IO) session.close
  finally setEnv environment





run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← liftM (m := IO) IO.currentDir
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let manifest := root / ".tmp" / "session-distinct-endpoints-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile manifest
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let mut session ← KernelSession.start (some manifest) (computationOnly := true)
    try
      let declarations : Array (Name × String) := #[
        (`S3, "let S3 := Sym(3) in Groups"),
        (`S3again, "let S3again := Sym(3) in Groups"),
        (`equal_ends, "let equal_ends := trivial(S3, S3again)")]
      let mut endpoints : Array (BindingId × ValueBinding) := #[]
      for (name, text) in declarations do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the distinct-endpoint declaration did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
        let some entry := session.source.context.entries.back?
          | throwError "the distinct-endpoint declaration lost its source binding"
        unless entry.userName == name do
          throwError "the distinct-endpoint declaration published a different name"
        if name != `equal_ends then
          let some binding := session.value? entry.id
            | throwError "the declared endpoint has no actual runtime reference"
          endpoints := endpoints.push (entry.id, binding)
        for (id, original) in endpoints do
          let some current := session.value? id
            | throwError "a later declaration discarded an original endpoint"
          unless current.value == original.value &&
              current.associationIds == original.associationIds do
            throwError "a later declaration replaced an original endpoint occurrence"
      let #[(sourceId, sourceValue), (targetId, targetValue)] := endpoints
        | throwError "the distinct-endpoint control lost one of its two original endpoints"
      if sourceId == targetId || sourceValue.value == targetValue.value then
        throwError "equal source definitions merged their distinct binding or value identities"
      session.source.context.withOpen fun bindings => do
        let some source := bindings.find? (·.id == sourceId)
          | throwError "the source endpoint is outside its original context"
        let some target := bindings.find? (·.id == targetId)
          | throwError "the target endpoint is outside its original context"
        let context ← ContextTelescope.capture bindings
        unless ← context.withOriginalSources #[source.expression, target.expression]
            (fun original => isDefEq original[0]! original[1]!) do
          throwError "the distinct-endpoint control no longer has equal native source definitions"
      let text := "assert implemented |equal_ends.ker()|"
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
        | .ok statement => pure statement
        | .error error => throwError "the distinct-endpoint continuation did not parse: {error}"
      let run ← withoutErrToSorry <| session.run ⟨statement⟩
      session := run.session
      for (id, original) in endpoints do
        let some current := session.value? id
          | throwError "the kernel continuation discarded an original endpoint"
        unless current.value == original.value &&
            current.associationIds == original.associationIds &&
            ((← SessionSnapshot.current).graph.find current.value).isSome do
          throwError "the kernel continuation replaced or detached an original endpoint"
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "the distinct-endpoint empty-provider control dispatched an operation"
      unless run.outcome.kind == "gap" &&
          (run.outcome.detail.splitOn "NoImplementation").length > 1 &&
          (run.outcome.detail.splitOn "meth.group_arrow_kernel").length > 1 do
        throwError "`{text}` did not reach the published kernel operation: \
          {run.outcome.kind} ({run.outcome.detail})"
    finally liftM (m := IO) session.close
  finally setEnv environment




run_cmd liftTermElabM do
  let environment ← getEnv
  let root ← IO.currentDir
  let contract ← CasCatalogue.Backend.packageDir CasCatalogue.Backend.contractPackage
  let python := (← IO.FS.realPath contract) / ".venv/bin/python"
  let logDirectory : System.FilePath :=
    (← IO.getEnv "CAS_APPLICATION_LOG_DIR").getD "timing/application"
  for mode in #["left", "right"] do
    try
      let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
      let evidence := logDirectory / "controls" / nonce
      IO.FS.createDirAll evidence
      let traffic := evidence / "peer.jsonl"
      IO.FS.writeFile traffic ""
      let operation := "meth.group_arrow_kernel"
      let manifest := Json.mkObj [
        ("backends", .arr #[Json.mkObj [("name", "fixed-group-kernel-peer"),
          ("command", toJson python.toString),
          ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString,
            "--fixed-group-kernel", mode, traffic.toString])]]),
        ("registrations", .arr #[Json.mkObj [("operation", toJson operation),
          ("input", "cat.arrows_groups"), ("backend", "fixed-group-kernel-peer")]])]
      let path := evidence / "leaves.json"
      IO.FS.writeFile path manifest.compress
      let initial ← KernelSession.start (some path) (computationOnly := true)
      try
        unless initial.kernel.rejected.isEmpty do
          throwError "the public fixed-input registration was rejected: {initial.kernel.rejected}"
        let runStatement := fun (session : KernelSession) (text : String) => do
          let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
            | throwError "the public fixed-input statement did not parse: {text}"
          withoutErrToSorry <| session.run ⟨statement⟩
        let mut session := initial
        let mut endpoints : Array (BindingId × ValueBinding) := #[]
        for (name, text) in #[
            (`S3, "let S3 := Sym(3) in Groups"),
            (`S3again, "let S3again := Sym(3) in Groups"),
            (`equal_ends, "let equal_ends := trivial(S3, S3again)")] do
          let run ← runStatement session text
          unless run.outcome.kind == "holds" && run.attempted && run.published do
            throwError "the public fixed-input declaration did not commit: {text}: {run.outcome.detail}"
          session := run.session
          let #[entry] := session.source.context.entries.filter (·.userName == name)
            | throwError "the public fixed-input declaration lost its one original source binding"
          let some value := session.value? entry.id
            | throwError "the public fixed-input declaration lost its actual retained value"
          if name != `equal_ends then endpoints := endpoints.push (entry.id, value)
        let #[(sourceId, sourceValue), (targetId, targetValue)] := endpoints
          | throwError "the public fixed-input control lost an original endpoint"
        unless sourceId != targetId && sourceValue.value != targetValue.value do
          throwError "the public fixed-input control merged equal source occurrences"
        let before ← SessionSnapshot.current
        let .ok (some sourcePacket) := before.graph.packet? sourceValue
          | throwError "the public fixed-input source lost its actual descriptor"
        let .ok (some targetPacket) := before.graph.packet? targetValue
          | throwError "the public fixed-input target lost its actual descriptor"
        unless sourcePacket == targetPacket do
          throwError "the public fixed-input control no longer compares equal endpoint packets"
        let run ← runStatement session "let selected_kernel := equal_ends.ker()"
        let after ← SessionSnapshot.current
        if mode == "left" then
          unless run.outcome.kind == "holds" && run.attempted && run.published do
            throwError "the original fixed source input was rejected: {run.outcome.detail}"
          let #[entry] := run.session.source.context.entries.filter
              (·.userName == `selected_kernel)
            | throwError "the admitted public fixed result lost its original binding"
          let some result := run.session.value? entry.id
            | throwError "the admitted public fixed result lost its actual occurrence"
          let .ok arrow := after.graph.project result 0
            | throwError "the public fixed result lost its complete inclusion arrow"
          let .ok ambient := after.graph.project arrow 1
            | throwError "the public fixed result lost its original ambient field"
          unless retainsReference sourceValue ambient && ambient.value != targetValue.value do
            throwError "the public fixed result substituted the other equal-valued source input"
          let reused ← runStatement run.session "let kept_kernel := selected_kernel"
          unless reused.outcome.kind == "holds" && reused.published do
            throwError "the original admitted fixed result failed at its later public use"
          let #[keptEntry] := reused.session.source.context.entries.filter
              (·.userName == `kept_kernel)
            | throwError "the later public use lost its source binding"
          let some kept := reused.session.value? keptEntry.id
            | throwError "the later public use lost the original fixed result"
          unless retainsReference result kept do
            throwError "the later public use replaced the admitted fixed result"
        else
          let .malformed detail := run.outcome
            | throwError "the wrong equal-valued fixed input changed its failure stratum: {run.outcome.detail}"
          unless detail.endsWith "the reply changed a fixed source input" && run.attempted &&
              !run.published do
            throwError "the wrong equal-valued input did not fail at fixed-result admission: {detail}"
          unless before.id == after.id && before.graph.sameRevision after.graph &&
              before.outputBatches.size == after.outputBatches.size do
            throwError "the rejected equal-valued fixed input published a graph or output"
          unless (run.session.source.context.entries.filter
              (·.userName == `selected_kernel)).isEmpty do
            throwError "the rejected fixed result published its source binding"
        for (id, original) in endpoints do
          let some current := run.session.value? id
            | throwError "fixed-result admission discarded an original endpoint"
          unless current.value == original.value &&
              current.associationIds == original.associationIds do
            throwError "fixed-result admission replaced an original endpoint"
        unless (← initial.kernel.dispatches.get).map (·.operation) == #[operation] do
          throwError "the public fixed-input control changed its actual provider invocation"
        let lines := (← IO.FS.readFile traffic).splitOn "\n" |>.filter (!·.isEmpty)
        let [line] := lines
          | throwError "the public fixed-input control did not reach its one actual peer reply"
        let .ok frame := Json.parse line
          | throwError "the fixed-input peer lost its independent traffic record"
        let expected : Json := .arr #["receiver", "args",
          toJson (if mode == "left" then (0 : Nat) else 1)]
        unless (frame.getObjValAs? String "op").toOption == some operation &&
            (frame.getObjVal? "ambient").toOption == some expected do
          throwError "the peer did not return the selected original input address"
      finally initial.close
    finally setEnv environment
