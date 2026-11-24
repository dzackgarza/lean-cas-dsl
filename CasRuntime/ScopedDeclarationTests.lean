module

import CasCatalogue.TestSuite
import CasTools.QuestionObservation
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCatalogue.TestSuite
meta import CasTools.QuestionObservation
meta import LeanCategories.Catalogue

open Lean Meta Elab Command Term CasCompiler CasRuntime CasCatalogue CasCatalogue.Backend

-- Reuse the existing SDK traffic peer and accepted integer operations. These controls
-- exercise public source scopes and the existing cell transaction, not a new provider law.
set_option maxHeartbeats 2000000 in
run_cmd do
  let root ← IO.currentDir
  let contract ← packageDir contractPackage
  let python := (← IO.FS.realPath contract) / ".venv/bin/python"
  let peer := root / "scripts/probes/kernel_session_peer.py"
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
      ("args", .arr #[toJson peer.toString])]]),
    ("registrations", .arr (#["op.rings.add", "op.rings.mul"].map fun operation =>
      Json.mkObj [("operation", operation), ("input", s!"{operation}#input"), ("backend", "peer")]))]
  IO.FS.createDirAll (root / ".tmp")
  let path := root / ".tmp/scoped-declaration-leaves.json"
  IO.FS.writeFile path manifest.compress
  CasCatalogue.Language.withSession (some path) false fun initial => do
    let parentRun ← CasCatalogue.Language.runStatement initial "let outer := 17 + 29 in ℤ"
    unless parentRun.outcome.kind == "holds" do
      throwError "the original parent input failed: {parentRun.outcome.detail}"
    let parent := parentRun.session
    let some parentEntry := parent.source.context.entries.back?
      | throwError "the parent definition disappeared"
    let some parentValue := parent.value? parentEntry.id
      | throwError "the parent definition lost its actual value"
    let before ← liftTermElabM SessionSnapshot.current
    let sent := (← parent.kernel.dispatches.get).size
    let scopedRun ← CasCatalogue.Language.runStatement parent
      "context do\n\
       let localSum := outer + 1 in ℤ\n\
       let localProduct := localSum · 2 in ℤ\n\
       inspect assumptions\n\
       test scope.product \"original integer operations\" : assert localProduct = 94 in ℤ\n\
       context do\n\
       let outer := localProduct + 1 in ℤ\n\
       test scope.shadow \"local definition\" : assert outer = 95 in ℤ\n\
       end\n\
       test scope.parent \"original outer definition\" : assert outer = 46 in ℤ\n\
       end"
    unless scopedRun.outcome.kind == "holds" && scopedRun.published do
      throwError "the public scope failed: {scopedRun.outcome.kind}: {scopedRun.outcome.detail}"
    let after ← liftTermElabM SessionSnapshot.current
    unless after.outputBatches.size == before.outputBatches.size + 1 &&
        scopedRun.session.source.context.exactlyMatches parent.source.context do
      throwError "a context block committed multiple cells or leaked its lexical source"
    let some retained := scopedRun.session.value? parentEntry.id
      | throwError "scope exit discarded the actual parent"
    unless retained.value == parentValue.value && retained.associationIds == parentValue.associationIds do
      throwError "scope exit changed an earlier retained occurrence"
    let calls ← parent.kernel.dispatches.get
    unless (calls.drop sent).map (·.operation) ==
        #["op.rings.add", "op.rings.mul", "op.rings.add", "op.rings.add"] do
      throwError "same-cell definitions were replayed or the original deferred child was omitted"
    let some batch := after.outputBatches.back?
      | throwError "the successful block has no output batch"
    unless batch.events.isEmpty && scopedRun.inspectionOutput == #["No local assumptions."] do
      throwError "explicit inspection was duplicated through the transaction and public display"
    let some shadow := scopedRun.observations.find? fun row =>
        match row.item with
        | `(cas_item| test $id:ident $_:str : $_:cas_stmt) => id.getId == `scope.shadow
        | _ => false
      | throwError "the original nested question identity was not retained"
    let some shadowConclusion := shadow.conclusions[0]?
      | throwError "the nested question lost its original scope"
    let sameNames := shadowConclusion.context.context.entries.filter (·.userName == `outer)
    unless sameNames.size == 2 && (sameNames[0]?.map (·.id)) != (sameNames[1]?.map (·.id)) do
      throwError "a shadowed name replaced its original stable source identity"
    unless scopedRun.observations.all (fun row => row.attempted && row.outcome.any (fun outcome =>
        outcome matches .holds)) do
      throwError "a published scope contains an unexecuted or failing child"
    let lost ← CasCatalogue.Language.runStatement scopedRun.session "assert localProduct = 94 in ℤ"
    unless lost.outcome.kind == "invalid" do
      throwError "a local name escaped its context block"

    -- All source is read before the first dispatch, even when an earlier child would compute.
    let beforeReadFailure ← liftTermElabM SessionSnapshot.current
    let beforeReadCalls := (← parent.kernel.dispatches.get).size
    let unread ← CasCatalogue.Language.runStatement parent
      "context do\nlet candidate := outer + 1 in ℤ\nassert neverDeclaredHere = 0 in ℤ\nend"
    unless unread.outcome.kind == "invalid" &&
        (← parent.kernel.dispatches.get).size == beforeReadCalls &&
        (← liftTermElabM SessionSnapshot.current).id == beforeReadFailure.id do
      throwError "a later source failure allowed an earlier child to dispatch or publish"

    -- This negative follows a real completed SDK call and explicit staged output.
    let beforeWrong ← liftTermElabM SessionSnapshot.current
    let beforeWrongCalls := (← parent.kernel.dispatches.get).size
    let wrong ← CasCatalogue.Language.runStatement parent
      "context do\n\
       let transient := outer + 2 in ℤ\n\
       inspect assumptions\n\
       test scope.wrong \"wrong comparison\" : assert transient = 0 in ℤ\n\
       test scope.unreached \"not executed after failure\" : assert outer = 46 in ℤ\n\
       end"
    unless wrong.outcome.kind == "wrong" && !wrong.published && wrong.inspectionOutput.isEmpty &&
        (← parent.kernel.dispatches.get).size == beforeWrongCalls + 1 do
      throwError "the failing block did not reach its actual staged computation and comparison"
    let afterWrong ← liftTermElabM SessionSnapshot.current
    unless afterWrong.id == beforeWrong.id &&
        afterWrong.graph.sameRevision beforeWrong.graph &&
        afterWrong.outputBatches.size == beforeWrong.outputBatches.size &&
        wrong.session.source.context.exactlyMatches parent.source.context do
      throwError "a failed block published a graph, receipt, output or local declaration"
    let labeled := wrong.observations.filter fun row =>
      match row.item with | `(cas_item| test $_:ident $_:str : $_:cas_stmt) => true | _ => false
    unless labeled.size == 2 &&
        (labeled[0]?.bind (·.outcome)).any (fun outcome => outcome matches .wrong _) &&
        (labeled[1]?.map (·.attempted)) == some false &&
        (labeled[1]?.bind (·.outcome)).isNone &&
        wrong.observations.all (fun row => !(row.outcome.any (fun outcome => outcome matches .holds))) do
      throwError "abort exposed an earlier staged success or changed the actual failing item"

    -- The public file adapter preserves original IDs and the established outcome taxonomy.
    -- An aborted or unexecuted child has no published answer; the actual failure stays wrong.
    let scopedFile := root / ".tmp/scoped-declaration-report.cas"
    IO.FS.writeFile scopedFile
      "context do\n\
       let staged := outer + 5 in ℤ\n\
       test scope.before \"staged comparison\" : assert staged = 51 in ℤ\n\
       test scope.failure \"actual wrong comparison\" : assert staged = 0 in ℤ\n\
       test scope.after \"unexecuted continuation\" : assert staged = 51 in ℤ\n\
       end"
    let beforeFile ← liftTermElabM SessionSnapshot.current
    let beforeFileCalls := (← parent.kernel.dispatches.get).size
    let (rows, fileSession) ← CasCatalogue.Language.runFile parent scopedFile
    unless rows.map (·.id) == #["scope.before", "scope.failure", "scope.after"] &&
        rows.map (·.kind) == #["unavailable", "wrong", "unavailable"] &&
        rows.map (·.fails) == #[false, true, false] &&
        rows.map (·.attempted) == #[true, true, false] &&
        rows.all (!·.published) &&
        rows.map (·.blockedBy) == #[some "scope.failure", none, some "scope.failure"] do
      throwError "the public report changed original identities or assigned unobserved truth values"
    let encodedRows := toJson rows
    let .ok decodedRows := fromJson? encodedRows (α := Array CasCatalogue.Language.TestResult)
      | throwError "the public scoped report no longer follows its JSON schema"
    unless decodedRows.map (·.kind) == rows.map (·.kind) &&
        decodedRows.map (·.attempted) == rows.map (·.attempted) &&
        decodedRows.map (·.blockedBy) == rows.map (·.blockedBy) &&
        (← parent.kernel.dispatches.get).size == beforeFileCalls + 1 &&
        (← liftTermElabM SessionSnapshot.current).id == beforeFile.id &&
        fileSession.source.context.exactlyMatches parent.source.context do
      throwError "file reporting replayed execution, lost block provenance or published an aborted cell"

    -- A genuine missing installed operation follows a successful staged child; it is a gap,
    -- and the containing context still has one all-or-nothing publication boundary.
    let beforeGap ← liftTermElabM SessionSnapshot.current
    let beforeGapCalls := (← parent.kernel.dispatches.get).size
    let gap ← CasCatalogue.Language.runStatement parent
      "context do\nlet temporary := outer + 3 in ℤ\ninspect assumptions\nassert implemented |Fin(2)|\nend"
    unless gap.outcome.kind == "gap" && !gap.published &&
        (← parent.kernel.dispatches.get).size == beforeGapCalls + 1 &&
        (← liftTermElabM SessionSnapshot.current).id == beforeGap.id &&
        gap.session.source.context.exactlyMatches parent.source.context do
      throwError "an unavailable block continuation published its preceding child"

    -- A direct returned wrong outcome retains the existing question commit policy.
    let beforeDirect ← liftTermElabM SessionSnapshot.current
    let direct ← CasCatalogue.Language.runStatement parent "assert outer = 0 in ℤ"
    unless direct.outcome.kind == "wrong" && direct.published &&
        (← liftTermElabM SessionSnapshot.current).outputBatches.size ==
          beforeDirect.outputBatches.size + 1 do
      throwError "the new block runner changed direct question publication"

    -- An unused abstract binder does not block a real concrete request in that same scope.
    let beforeConcrete := (← parent.kernel.dispatches.get).size
    let concrete ← CasCatalogue.Language.runStatement parent
      "context do\nlet unused ∈ CommutativeRings\nlet actual := outer + 4 in ℤ\nassert actual = 50 in ℤ\nend"
    unless concrete.outcome.kind == "holds" &&
        (← parent.kernel.dispatches.get).size == beforeConcrete + 1 do
      throwError "an unrelated hypothetical binder blocked the concrete selected request"

    -- Abstract parameters remain formal; uniform definitions and native proof(h) retain
    -- the complete actual context, and no concrete runtime parameter is fabricated.
    let beforeFormalCalls := (← parent.kernel.dispatches.get).size
    let beforeFormal ← liftTermElabM SessionSnapshot.current
    let formal ← CasCatalogue.Language.runStatement parent
      "context do\n\
       let R ∈ CommutativeRings\n\
       let x ∈ R\n\
       let y ∈ R\n\
       let one := 1 in R\n\
       assume h : x = y\n\
       inspect assumptions\n\
       test scope.hypothesis \"supplied local hypothesis\" : assert x = y using (proof(h))\n\
       end"
    unless formal.outcome.kind == "holds" && formal.published &&
        (← parent.kernel.dispatches.get).size == beforeFormalCalls &&
        (← liftTermElabM SessionSnapshot.current).graph.sameRevision beforeFormal.graph &&
        formal.session.source.context.exactlyMatches parent.source.context do
      throwError "an abstract source scope dispatched invented data or lost its supplied proof"
    let some retainedClaim := formal.conclusions.find? (·.proof.isSome)
      | throwError "the actual returned scoped conclusion lost its explicit native evidence"
    let assumptions := retainedClaim.context.context.entries.filter fun entry =>
      entry.role == .parameter || entry.role == .hypothesis
    unless assumptions.map (·.userName) == #[`R, `x, `y, `h] do
      throwError "the returned conclusion omitted original scoped parameters or hypotheses"
    for entry in retainedClaim.context.context.entries do
      if entry.id != parentEntry.id then
        unless (formal.session.value? entry.id).isNone &&
            !(formal.session.source.context.entries.any (·.id == entry.id)) do
          throwError "a scoped formal parameter acquired an escaping runtime binding"
    let some originalRing := retainedClaim.context.context.entries.find? (·.userName == `R)
      | throwError "the conclusion lost its abstract category parameter"
    let some originalCategory := retainedClaim.context.categoryFor originalRing.id
      | throwError "the conclusion lost the original selected category"
    let expectedCategory ← liftTermElabM do
      selectCategory (← semanticState) "CommutativeRings"
    unless originalCategory.expression.syntacticEq expectedCategory.expression do
      throwError "the abstract object was replaced by a concrete or unrelated category"
    let beforeInspection ← liftTermElabM SessionSnapshot.current
    let inspected := retainedClaim.inspectAssumptions
    let native := CasTools.QuestionExport.observeConclusion retainedClaim
    let .ok terms := native.getObjValAs? (Array Json) "terms"
      | throwError "public post-scope inspection lost the native terms"
    let some encoded := terms[0]?
      | throwError "public post-scope inspection omitted the actual conclusion"
    let .ok contexts := encoded.getObjValAs? (Array Json) "context"
      | throwError "public post-scope inspection lost the full telescope"
    let .ok categories := encoded.getObjValAs? (Array Json) "categories"
      | throwError "public post-scope inspection lost the selected categories"
    unless contexts.size == retainedClaim.context.context.entries.size &&
        categories.size == contexts.size && !inspected.isEmpty &&
        formal.inspectionOutput == #[inspected] &&
        (← parent.kernel.dispatches.get).size == beforeFormalCalls &&
        (← liftTermElabM SessionSnapshot.current).id == beforeInspection.id do
      throwError "inspection reopened computation or substituted the restored outer context"
    let some retainedTerm := retainedClaim.terms[0]?
      | throwError "the returned claim has no original proposition"
    let some originalHypothesis := assumptions.find? (·.userName == `h)
      | throwError "the returned claim has no original hypothesis"
    let hypothesisType ← liftTermElabM <| retainedTerm.source.withOpen fun bindings term => do
      let context ← ContextTelescope.capture bindings
      let some h := bindings.find? (·.id == originalHypothesis.id)
        | throwError "the original local hypothesis is missing"
      unless ← isDefEq (← inferType h.expression) term do
        throwError "the retained proof no longer establishes its original conditional statement"
      return ← context.close term
    unless hypothesisType.context.exactlyMatches retainedClaim.context.context do
      throwError "native post-scope reopening shortened the actual telescope"

    let beforePureProof ← liftTermElabM SessionSnapshot.current
    let pureProof ← CasCatalogue.Language.runStatement parent
      "assert (0 = 0 in ℤ) using (proof(rfl))"
    unless pureProof.outcome.kind == "holds" && !pureProof.published &&
        pureProof.conclusions.any (·.proof.isSome) &&
        (← liftTermElabM SessionSnapshot.current).id == beforePureProof.id do
      throwError "a pure supplied source proof allocated a computational publication"

    let abstractRun ← CasCatalogue.Language.runStatement parent "let R ∈ CommutativeRings"
    unless abstractRun.outcome.kind == "holds" && !abstractRun.published do
      throwError "a formal declaration performed a runtime publication"
    let some formalEntry := abstractRun.session.source.context.entries.back?
      | throwError "the formal declaration disappeared"
    unless (abstractRun.session.value? formalEntry.id).isNone do
      throwError "an abstract declaration invented a concrete value"
    let beforePureInspection ← liftTermElabM SessionSnapshot.current
    let pureInspection ← CasCatalogue.Language.runStatement abstractRun.session "inspect assumptions"
    unless pureInspection.outcome.kind == "holds" && !pureInspection.published &&
        pureInspection.inspectionOutput == #[abstractRun.session.source.observation.assumptionsText] &&
        (← liftTermElabM SessionSnapshot.current).id == beforePureInspection.id do
      throwError "direct inspection allocated a new publication or evaluated its frozen data"
    let beforeMissing := (← parent.kernel.dispatches.get).size
    let missing ← CasCatalogue.Language.runStatement abstractRun.session "assert implemented 1 in R"
    unless missing.outcome.kind == "gap" && !missing.published &&
        (← parent.kernel.dispatches.get).size == beforeMissing do
      throwError "an unsupplied abstract input was sent to a concrete provider"

    -- Missing data on the right is prepared before the otherwise computable left can dispatch.
    let element ← CasCatalogue.Language.runStatement parent "let x ∈ ℤ"
    unless element.outcome.kind == "holds" do
      throwError "the independent formal element did not read"
    let beforeComparison := (← parent.kernel.dispatches.get).size
    let missingRight ← CasCatalogue.Language.runStatement element.session
      "assert (17 + 29 in ℤ) = x"
    unless missingRight.outcome.kind == "gap" && !missingRight.published &&
        (← parent.kernel.dispatches.get).size == beforeComparison do
      throwError "comparison dispatched before admitting its complete abstract input"

  -- Computation-only mode retains supplied proof as source evidence, but still computes
  -- the actual proposition through the same ordinary public question path.
  CasCatalogue.Language.withSession (some path) true fun initial => do
    let result ← CasCatalogue.Language.runStatement initial
      "assert (17 + 29 = 46 in ℤ) using (proof(rfl))"
    unless result.outcome.kind == "holds" && result.published &&
        result.conclusions.any (·.proof.isSome) &&
        (← initial.kernel.dispatches.get).map (·.operation) == #["op.rings.add"] do
      throwError "supplied evidence bypassed the computation-only question policy"

  -- Preserve the existing direct definition-gap contract without introducing another peer.
  let emptyPath := root / ".tmp/scoped-declaration-empty-leaves.json"
  IO.FS.writeFile emptyPath
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
  CasCatalogue.Language.withSession (some emptyPath) false fun initial => do
    let defined ← CasCatalogue.Language.runStatement initial "let a := 17 + 29 in ℤ"
    unless defined.outcome.kind == "gap" && !defined.published &&
        defined.session.source.context.entries.size == 1 do
      throwError "a direct missing computation discarded its actual source definition"
    let later ← CasCatalogue.Language.runStatement defined.session "assert a = 46 in ℤ"
    unless later.outcome.kind == "holds" do
      throwError "a direct definition's unavailable computation changed its native meaning"
