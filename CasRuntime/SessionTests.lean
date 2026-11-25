module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

/- Public statements run from source text through the reader, the lowerer and the kernel
executor to a real protocol-v2 process. The provider supplies integer-ring traffic only; the
catalogue fixes every question. Reuse: the pinned SDK project and KernelSession. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_session_peer.py"
    let registration := fun (operation : String) => Json.mkObj [("operation", operation),
      ("input", s!"{operation}#input"), ("backend", "peer")]
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
        -- A numeral of ℤ/5 is the image of 3 under ℤ → ℤ/5; computing it is a leaf's job
        -- (constitution C22), so defining it dispatches nothing and holds.
        ("let x := 3 in ℤ/5", "holds")]
      for (text, kind) in expected do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
      -- A source alias of an actual computed value retains that exact value, even when
      -- reading the alias dispatches nothing and the value has no live-owner requirement.
      let some original := session.source.context.entries.find? (·.userName == `a)
        | throwError "the public arithmetic control lost its original source binding"
      let some actual := session.value? original.id
        | throwError "the public arithmetic control lost its computed value"
      let aliasStatement ← match Parser.runParserCategory (← getEnv) `cas_stmt
          "let retainedAlias := a" with
        | .ok statement => pure statement
        | .error error => throwError "the alias statement did not parse: {error}"
      let aliased ← withoutErrToSorry <| session.run ⟨aliasStatement⟩
      unless aliased.outcome.kind == "holds" do
        throwError "the public alias is {aliased.outcome.kind} ({aliased.outcome.detail})"
      let some named := aliased.session.source.context.entries.back?
        | throwError "the public alias lost its original source declaration"
      let some retained := aliased.session.value? named.id
        | throwError "a public alias discarded its actual computed value"
      unless named.userName == `retainedAlias && retained.value == actual.value &&
          retained.associationIds == actual.associationIds do
        throwError "a public alias replaced its original computed reference"
      session := aliased.session
      let question ← match Parser.runParserCategory (← getEnv) `cas_stmt
          "assert retainedAlias = 46 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the alias question did not parse: {error}"
      let observed ← withoutErrToSorry <| session.run ⟨question⟩
      unless observed.outcome.kind == "holds" do
        throwError "the alias question is {observed.outcome.kind}: {observed.outcome.detail}"
      session := observed.session
      -- The retained sum is sent again as data. The deferred addition is a real dispatch.
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["op.rings.add", "op.rings.mul", "op.rings.mul", "op.rings.add",
          "meth.cardinality", "meth.cardinality"] do
        throwError "the session dispatched {dispatched}"
    finally liftM (m := IO) session.close
    -- An explicit empty manifest gives the same source its reading without a realization.
    setEnv environment
    let emptyPath := root / ".tmp" / "kernel-session-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile emptyPath
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let bare ← KernelSession.start (some emptyPath)
    try
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt "let a := 17 + 29 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let run ← withoutErrToSorry <| bare.run ⟨statement⟩
      unless run.outcome.kind == "gap" do
        throwError "a statement with no installed leaf is {run.outcome.kind}, not a gap"
      -- The definition keeps its meaning without a leaf (constitution C3): a later statement
      -- reads it, and this closed question is settled in Lean.
      let question ← match Parser.runParserCategory (← getEnv) `cas_stmt "assert a = 46 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let asked ← withoutErrToSorry <| run.session.run ⟨question⟩
      unless asked.outcome.kind == "holds" do
        throwError "a definition with no installed leaf is lost: {asked.outcome.kind} ({asked.outcome.detail})"
      -- Maps the user wrote are not computed values: a question about them is settled in Lean
      -- from their definitions, not sent to a leaf (tests/acceptance/functions.cas).
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

/- Scoped declarations use the original public statement reader and kernel session. The
hypothetical ring and module have no provider values; their uniform source operations and
hypotheses must remain usable with their original bindings after shadowing. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  let root ← liftM (m := IO) IO.currentDir
  let manifest := root / ".tmp" / "kernel-session-declarations.json"
  liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
  liftM (m := IO) <| IO.FS.writeFile manifest
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
  let runStatement : KernelSession → String → TermElabM StatementRun := fun session text => do
    let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
      | .ok statement => pure statement
      | .error error => throwError "the scoped statement did not parse: {error}"
    withoutErrToSorry <| session.run ⟨statement⟩
  let read : SourceSession → String → TermElabM SourceTerm := fun source text => do
    let expression ← match Parser.runParserCategory (← getEnv) `cas_term text with
      | .ok expression => pure expression
      | .error error => throwError "the scoped expression did not parse: {error}"
    withoutErrToSorry <| source.read ⟨expression⟩
  let mut session ← KernelSession.start (some manifest)
  try
    for text in #[
        "let R ∈ Rings",
        "let M ∈ Modules(R)",
        "let x ∈ R",
        "let y : R",
        "let h : x = y",
        "assert x = y",
        "let saved := h",
        "assert R ∈ Rings",
        "assert M ∈ Modules(R)",
        "assert x ∈ R",
        "let Q := ℚ ∈ Rings",
        "assert Q ∈ Rings"] do
      let step ← runStatement session text
      unless step.outcome.kind == "holds" do
        throwError "`{text}` is {step.outcome.kind}: {step.outcome.detail}"
      session := step.session
    let #[ring, module_, x, y, hypothesis, saved, concrete] := session.source.context.entries
      | throwError "the public declarations lost or added source bindings"
    for entry in #[ring, module_, x, y] do
      unless entry.role == .parameter && entry.value.isNone do
        throwError "a hypothetical source parameter became a definition or axiom"
    unless hypothesis.role == .hypothesis && hypothesis.value.isNone &&
        saved.role == .definition && saved.value.isSome &&
        concrete.role == .definition && concrete.value.isSome do
      throwError "hypotheses and concrete definitions lost their native declaration kinds"
    unless #[ring, module_, x, y, hypothesis].all (fun entry =>
        (session.value? entry.id).isNone) do
      throwError "a hypothetical input acquired an unsolicited computational value"
    session.source.context.withOpen fun bindings => do
      let expected ← Meta.mkEq bindings[2]!.expression bindings[3]!.expression
      unless ← Meta.isDefEq (← Meta.inferType bindings[4]!.expression) expected do
        throwError "the local hypothesis changed its original operands"
      let some value := (← bindings[5]!.expression.fvarId!.getDecl).value?
        | throwError "the source proof alias was not retained as a definition"
      unless value == bindings[4]!.expression do
        throwError "the source proof alias replaced the original local hypothesis"
    let some selected := session.source.categoryFor module_.id
      | throwError "the dependent hypothetical object lost its selected category"
    selected.bundle.withOpen fun bindings expression => do
      let some original := bindings.find? (·.id == ring.id)
        | throwError "the selected module category lost its original scalar binding"
      unless expression.containsFVar original.expression.fvarId! do
        throwError "the selected module category replaced its actual scalar parameter"
    let sum ← read session.source "x + y in R"
    sum.source.withOpen fun bindings expression => do
      for id in #[x.id, y.id] do
        let some original := bindings.find? (·.id == id)
          | throwError "a uniform source operation lost its original element"
        unless expression.containsFVar original.expression.fvarId! do
          throwError "a uniform source operation substituted a hypothetical operand"
    let beforeShadow := session.source
    let shadow ← runStatement session "let R ∈ Rings"
    unless shadow.outcome.kind == "holds" do
      throwError "a new scoped ring did not read: {shadow.outcome.detail}"
    session := shadow.session
    let some newRing := session.source.context.entries.back?
      | throwError "the shadowing declaration disappeared"
    unless newRing.userName == ring.userName && newRing.id != ring.id &&
        beforeShadow.context.entries.size == 7 do
      throwError "shadowing changed an earlier binding or its persistent scope"
    let identity ← read session.source "id(M)"
    unless identity.category.any (·.role == .morphism) do
      throwError "the hypothetical module lost its uniform identity operation"
    identity.source.withOpen fun bindings expression => do
      let some original := bindings.find? (·.id == module_.id)
        | throwError "the uniform identity lost its source module"
      let expected ← Meta.mkAppM ``Quiver.Hom #[original.expression, original.expression]
      unless ← Meta.isDefEq (← Meta.inferType expression) expected do
        throwError "the uniform identity no longer has the original module as both endpoints"
    for text in #["assert M ∈ Modules(R)", "let bad ∈ Modules(x)"] do
      let step ← runStatement session text
      unless step.outcome.fails &&
          step.session.source.context.entries.size == session.source.context.entries.size do
        throwError "a mismatched scoped category was accepted or changed the source scope"
    unless (← session.kernel.dispatches.get).isEmpty do
      throwError "a scoped declaration or typing judgement dispatched a computation"
    -- Keep the actual Environment unchanged while opening a new native source scope.
    -- A second runtime session would conflict with its existing initialized snapshot.
    let fresh ← SourceSession.empty session.kernel.ledger.owners.identities
    for (text, name) in #[("assert R ∈ Rings", "R"), ("let leaked := h", "h")] do
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
        | .ok statement => pure statement
        | .error error => throwError "the fresh-scope statement did not parse: {error}"
      let rejected ← try
          discard <| withoutErrToSorry <| fresh.readStatement ⟨statement⟩
          pure false
        catch error =>
          unless CasCatalogue.Exception.isUnknownSourceName error name do throw error
          pure true
      unless rejected && fresh.context.entries.isEmpty do
        throwError "a scoped assumption escaped into an independent source session"
  finally
    liftM (m := IO) session.close
    setEnv environment

/- A failed public definition retains the failure of its one actual invocation. The existing
SDK peer fails only its first addition; retrying an alias would therefore succeed and emit a
second request. Explicitly writing a new addition remains a new independent computation. -/
run_cmd liftTermElabM do
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
            "assert implemented failedDependent", "assert implemented failedSum"] do
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
        let unchanged ← SessionSnapshot.current
        unless unchanged.id == before.id && unchanged.graph.sameRevision before.graph &&
            unchanged.outputBatches.size == before.outputBatches.size &&
            (← session.kernel.dispatches.get).map (·.operation) == #["op.rings.add"] &&
            (← liftM (m := IO) <| IO.FS.readFile log) == traffic do
          throwError "a later failed-definition use retried or published a computation"
        -- The failure neither changes the mathematical definition nor poisons a fresh call.
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
  finally setEnv environment
