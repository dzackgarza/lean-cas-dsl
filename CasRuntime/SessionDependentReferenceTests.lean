module

import CasRuntime.Session
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue

open Lean Meta Elab Command Term CasCompiler CasRuntime

/- The original group-kernel continuations in
tests/acceptance/b0-required-positives.cas.proposed require the actual group declared as S3.
All declarations and questions below are unchanged source inputs. With no provider installed,
each question must reach its published group-arrow-kernel operation. No cardinality answer is
computed or supplied by this engineering regression. -/
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
      -- Collect all three outcomes before reporting failures, so a broken trivial-map
      -- continuation cannot prevent the unchanged identity-map continuation from executing.
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

/- A provider's deliberately incorrect scalar reply must remain observable through source
aliases. This uses the existing integer-addition protocol peer with an explicit test-only fault;
it neither supplies an independent mathematical implementation nor changes the peer's default
answers. The ordinary proof-discharge path must not replace observed data by its source term. -/
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
        ("let copy := a", "holds"),
        ("let copy2 := copy", "holds"),
        ("assert copy2 = 46 in ℤ", "wrong")]
      for (text, kind) in expected do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the scalar observation control did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          failures := failures.push
            s!"`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
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

/- Equal native endpoint expressions still name distinct declared runtime occurrences.
The trivial map uses both original source positions. A consuming dependent reference must
select its own binding, rather than every context binding definitionally equal to that field.
The implementation query forces the existing kernel continuation without a cardinality answer. -/
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
        unless ← isDefEq source.expression target.expression do
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
