module

import CasCatalogue.TestSuite
import CasTools.QuestionObservation
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCatalogue.TestSuite
meta import CasTools.QuestionObservation
meta import LeanCategories.Catalogue

open Lean Meta Elab Command Term CasCompiler CasRuntime CasCatalogue CasCatalogue.Backend

private def retainedStatementTerm (run : StatementRun) (scope : ContextTelescope)
    (input body : String) : TermElabM (SourceConclusion × SourceTerm) := do
  let #[conclusion] := run.conclusions
    | throwError "the failed statement lost its original conclusion"
  let #[term] := conclusion.terms
    | throwError "the failed statement changed its original source terms"
  unless conclusion.context.context.exactlyMatches scope &&
      term.source.context.exactlyMatches scope do
    throwError "the failed statement changed its complete original source scope"
  let some start := term.span.start
    | throwError "the failed statement lost its original source start"
  let some stop := term.span.stop
    | throwError "the failed statement lost its original source end"
  let original := ({ str := input, startPos := start, stopPos := stop } :
    Substring.Raw).toString
  unless original == body do
    throwError "the retained conclusion no longer identifies the original source question"
  return (conclusion, term)

/-- Close the actual definition-only source prefix in the public report, retaining its
native expressions and declared types. The control below checks both claims and evidence. -/
private def closePreflightTerm (term : Json) : TermElabM (Expr × Expr) := do
  let .ok context := term.getObjValAs? (Array Json) "context"
    | throwError "the preflight reading lost its original context"
  let .ok graph := term.getObjVal? "nativeExpressions"
    | throwError "the preflight reading lost its exact native graph"
  let .ok nodes := CasTools.NativeExpression.decodeNodes graph
    | throwError "the preflight native graph did not decode"
  let .ok #[expression, type] := CasTools.NativeExpression.decode graph
    | throwError "the preflight reading changed its expression and type roots"
  let .ok native := term.getObjVal? "native"
    | throwError "the preflight reading lost its native source record"
  unless native.getObjValAs? (Array Json) "context" == .ok context do
    throwError "the preflight native record changed its original telescope"
  for field in #["expression", "type"], root in #[expression, type] do
    let .ok index := native.getObjValAs? Nat field
      | throwError "the preflight native record lost its {field} reference"
    unless nodes[index]? == some root do
      throwError "the preflight native root changed its original {field}"
  let mut closed := expression
  let mut closedType := type
  for entry in context.reverse do
    let .ok nameJson := entry.getObjVal? "nativeName"
      | throwError "the preflight declaration lost its native name"
    let .ok name := CasTools.NativeExpression.nameFromJson nameJson
      | throwError "the preflight native name did not decode"
    let .ok typeIndex := entry.getObjValAs? Nat "type"
      | throwError "the preflight definition lost its type"
    let some type := nodes[typeIndex]?
      | throwError "the preflight definition type is outside its native graph"
    let .ok valueIndex := entry.getObjValAs? Nat "value"
      | throwError "the preflight definition lost its original value"
    let some value := nodes[valueIndex]?
      | throwError "the preflight definition value is outside its native graph"
    let .ok nondep := entry.getObjValAs? Bool "nondep"
      | throwError "the preflight definition lost its dependency information"
    closed := .letE name type value closed nondep
    closedType := .letE name type value closedType nondep
  unless !closed.hasFVar && !closed.hasLooseBVars &&
      !closedType.hasFVar && !closedType.hasLooseBVars do
    throwError "the preflight reading escaped its complete original scope"
  checkWithKernel (← mkExpectedTypeHint closed closedType)
  return (closed, closedType)

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
    unless !unread.attempted && !unread.published do
      throwError "source preflight was reported as attempted execution or publication"

    -- A later source error keeps the actual checked prefix, including the inner scope
    -- and supplied proofs. None of this block enters execution; the outer scope resumes.
    let preflightFile := root / ".tmp/scoped-declaration-preflight-report.cas"
    let preflightSource :=
      "context do\n\
       let staged := outer + 5 in ℤ\n\
       test preflight.before \"checked outer prefix\" : assert staged = staged using (proof(rfl))\n\
       context do\n\
       let inner := staged + 1 in ℤ\n\
       test preflight.inner \"checked inner prefix\" : assert inner = inner using (proof(rfl))\n\
       test preflight.failure \"actual source error\" : assert neverDeclaredHere = 0 in ℤ\n\
       test preflight.inner_after \"unread inner suffix\" : assert inner = inner\n\
       end\n\
       test preflight.after \"unread outer suffix\" : assert staged = staged\n\
       test preflight.unread_block \"unread labeled scope\" : context do\n\
       test preflight.unread_nested \"unread nested identity\" : assert staged = staged\n\
       end\n\
       end\n\
       test preflight.restored \"restored outer source\" : assert outer in ℤ\n"
    IO.FS.writeFile preflightFile preflightSource
    let beforePreflight ← liftTermElabM SessionSnapshot.current
    let beforePreflightCalls := (← parent.kernel.dispatches.get).size
    let (preflightRows, preflightSession) ← CasCatalogue.Language.runFile parent preflightFile
    unless preflightRows.map (·.id) == #["preflight.before", "preflight.inner",
          "preflight.failure", "preflight.inner_after", "preflight.after",
          "preflight.unread_block", "preflight.unread_nested", "preflight.restored"] &&
        preflightRows.map (·.kind) ==
          #["unavailable", "unavailable", "invalid", "unavailable", "unavailable",
            "unavailable", "unavailable", "holds"] &&
        preflightRows.map (·.fails) == #[false, false, true, false, false, false, false, false] &&
        preflightRows.map (·.attempted) == #[false, false, false, false, false, false, false, true] &&
        preflightRows.all (fun row => !row.published && row.dispatches.isEmpty) &&
        preflightRows.map (·.blockedBy) == #[some "preflight.failure", some "preflight.failure",
          none, some "preflight.failure", some "preflight.failure", some "preflight.failure",
          some "preflight.failure", none] do
      throwError "source preflight changed an original identity, failure or execution status"
    let afterPreflight ← liftTermElabM SessionSnapshot.current
    unless (← parent.kernel.dispatches.get).size == beforePreflightCalls &&
        afterPreflight.id == beforePreflight.id &&
        afterPreflight.graph.sameRevision beforePreflight.graph &&
        afterPreflight.outputBatches.size == beforePreflight.outputBatches.size &&
        preflightSession.source.context.exactlyMatches parent.source.context do
      throwError "a failed source preflight dispatched, published or leaked its lexical scope"
    let expectedOuter := Json.mkObj [("session", toJson parentEntry.id.session),
      ("serial", toJson parentEntry.id.serial)]
    let mut stagedId : Option Json := none
    for row in preflightRows.take 2, body in #["staged = staged", "inner = inner"],
        names in #[#["outer", "staged"], #["outer", "staged", "inner"]] do
      unless !row.question.isEmpty && row.question == row.proposition do
        throwError "the checked source prefix lost its original question display"
      let #[conclusion] := row.conclusions
        | throwError "a checked prefix question lost its original typed conclusion"
      let .ok #[term] := conclusion.getObjValAs? (Array Json) "terms"
        | throwError "a checked prefix conclusion changed its original terms"
      let .ok proof := conclusion.getObjVal? "proof"
        | throwError "a checked prefix conclusion lost its evidence field"
      unless !proof.isNull do throwError "a checked prefix discarded its supplied proof"
      let .ok context := term.getObjValAs? (Array Json) "context"
        | throwError "a checked prefix question lost its original lexical scope"
      unless context.map (·.getObjValAs? String "name") == names.map (Except.ok) &&
          context.all (fun entry => entry.getObjValAs? String "role" == .ok "definition") &&
          proof.getObjValAs? (Array Json) "context" == .ok context &&
          proof.getObjVal? "categories" == term.getObjVal? "categories" do
        throwError "a checked prefix substituted another scope, selection or supplied proof"
      let some outer := context[0]?
        | throwError "the checked prefix lost its original outer declaration"
      let some staged := context[1]?
        | throwError "the checked prefix lost its preceding local definition"
      let .ok actualStaged := staged.getObjVal? "id"
        | throwError "the checked prefix lost its stable local binding identity"
      unless outer.getObjVal? "id" == .ok expectedOuter && actualStaged != expectedOuter &&
          stagedId.all (· == actualStaged) do
        throwError "source preflight replaced an original retained binding occurrence"
      stagedId := some actualStaged
      let .ok start := term.getObjValAs? Nat "startByte"
        | throwError "the checked prefix lost its original start position"
      let .ok stop := term.getObjValAs? Nat "stopByte"
        | throwError "the checked prefix lost its original end position"
      let original := ({ str := preflightSource, startPos := ⟨start⟩, stopPos := ⟨stop⟩ } :
        Substring.Raw).toString
      unless original == body && term.getObjValAs? String "file" == .ok preflightFile.toString do
        throwError "source preflight changed the original checked question's file or span"
      liftTermElabM do
        let (proposition, _) ← closePreflightTerm term
        let (evidence, evidenceType) ← closePreflightTerm proof
        unless (← isProp proposition) && (← isDefEq evidenceType proposition) do
          throwError "the retained prefix evidence no longer proves its original proposition"
        checkWithKernel (← mkExpectedTypeHint evidence proposition)
    for row in preflightRows.extract 2 7 do
      unless row.conclusions.isEmpty && row.question.isEmpty && row.proposition.isEmpty do
        throwError "source preflight invented a judgement for failed or unread source"
    let some restored := preflightRows.back?
      | throwError "the source-preflight file lost its original outer continuation"
    let #[restoredConclusion] := restored.conclusions
      | throwError "the outer continuation lost its actual source reading"
    let .ok #[restoredTerm] := restoredConclusion.getObjValAs? (Array Json) "terms"
      | throwError "the outer continuation changed its original typing question"
    let .ok #[restoredOuter] := restoredTerm.getObjValAs? (Array Json) "context"
      | throwError "an inner source declaration escaped the failed context block"
    unless restoredOuter.getObjVal? "id" == .ok expectedOuter do
      throwError "the outer continuation no longer refers to its original source binding"

    -- Two separate failed source preflights must keep their checked native match helpers
    -- occupied before either retained proof is reopened. The second matcher has a different
    -- arity, so restoring a colliding name with another checked body cannot satisfy this test.
    let beforeHelperState ← liftTermElabM SessionSnapshot.current
    let beforeHelperCalls := (← parent.kernel.dispatches.get).size
    let beforeHelperEnvironment ← liftTermElabM do
      return (← getEnv).setExporting false
    let mut retainedHelpers : Array (SourceConclusion × SourceTerm × Array ConstantInfo) := #[]
    for proofText in #[
        "match n, n with | 0, _ => rfl | _, 0 => rfl | Nat.succ _, Nat.succ _ => rfl",
        "match n, n, n with | 0, _, _ => rfl | _, 0, _ => rfl | _, _, 0 => rfl | Nat.succ _, Nat.succ _, Nat.succ _ => rfl"] do
      let source := s!"context do\nlet n ∈ ℕ\nassert n = n using (proof({proofText}))\nassert neverDeclaredHere = 0 in ℤ\nend"
      let run ← CasCatalogue.Language.runStatement parent source
      unless run.outcome.kind == "invalid" && !run.attempted && !run.published &&
          run.session.source.context.exactlyMatches parent.source.context do
        throwError "the auxiliary-declaration control executed or escaped its failed scope"
      let #[conclusion] := run.conclusions
        | throwError "the failed source preflight lost its checked match-proof conclusion"
      let some proof := conclusion.proof
        | throwError "the failed source preflight discarded its original match proof"
      let helpers := proof.source.nativeDeclarations.constants.filter fun declaration =>
        !beforeHelperEnvironment.contains declaration.name
      unless !helpers.isEmpty do
        throwError "the failed source preflight did not exercise a new native declaration"
      retainedHelpers := retainedHelpers.push (conclusion, proof, helpers)
    let #[(firstConclusion, firstProof, firstHelpers),
          (secondConclusion, secondProof, secondHelpers)] := retainedHelpers
      | throwError "the auxiliary-declaration control lost one of its failed source scopes"
    unless firstHelpers.all (fun first => secondHelpers.all (fun second =>
        first.name != second.name)) do
      throwError "a later source preflight reused a retained checked declaration name"
    liftTermElabM do
      -- Check eager preservation before withOpen's own dependency restoration can run.
      let environment := (← getEnv).setExporting false
      for original in firstHelpers ++ secondHelpers do
        let some current := environment.find? original.name
          | throwError "runtime rollback forgot a checked native source declaration"
        unless nativeConstantExactlyMatches original current do
          throwError "runtime rollback replaced a retained declaration's original body"
      for (conclusion, proof) in #[(firstConclusion, firstProof),
          (secondConclusion, secondProof)] do
        let #[proposition] := conclusion.terms
          | throwError "the failed source scope changed its original proved proposition"
        unless proof.source.context.exactlyMatches conclusion.context.context &&
            proposition.source.context.exactlyMatches conclusion.context.context do
          throwError "the retained match proof changed its complete source telescope"
        proof.source.withOpen fun bindings evidence => do
          let context ← ContextTelescope.capture bindings
          let proposition ← proposition.source.inContext context
          unless ← isDefEq (← inferType evidence) proposition do
            throwError "the retained native helper no longer proves its original claim"
          checkWithKernel (← mkExpectedTypeHint evidence proposition)
    let afterHelperState ← liftTermElabM SessionSnapshot.current
    unless (← parent.kernel.dispatches.get).size == beforeHelperCalls &&
        afterHelperState.id == beforeHelperState.id &&
        afterHelperState.graph.sameRevision beforeHelperState.graph &&
        afterHelperState.outputBatches.size == beforeHelperState.outputBatches.size do
      throwError "retaining checked source helpers changed runtime traffic or publication"

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
    let scopedSource :=
      "context do\n\
       let staged := outer + 5 in ℤ\n\
       test scope.before \"staged comparison\" : assert staged = 51 in ℤ\n\
       test scope.failure \"actual wrong comparison\" : assert staged = 0 in ℤ\n\
       test scope.after \"unexecuted continuation\" : assert staged = 51 in ℤ\n\
       end"
    IO.FS.writeFile scopedFile scopedSource
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
        decodedRows.map (·.conclusions) == rows.map (·.conclusions) &&
        rows.all (fun row => !row.question.isEmpty && row.question == row.proposition) &&
        (← parent.kernel.dispatches.get).size == beforeFileCalls + 1 &&
        (← liftTermElabM SessionSnapshot.current).id == beforeFile.id &&
        fileSession.source.context.exactlyMatches parent.source.context do
      throwError "file reporting replayed execution, lost block provenance or published an aborted cell"
    -- Each original ID retains its own full typed reading, including the rolled-back
    -- success and the unexecuted continuation. Source spans distinguish the two equal
    -- propositions without substituting an earlier question or rereading the file.
    let mut previousStop := 0
    let mut stagedIdentity : Option Json := none
    for row in rows, body in #["staged = 51 in ℤ", "staged = 0 in ℤ", "staged = 51 in ℤ"] do
      let #[conclusion] := row.conclusions
        | throwError "the public report discarded an original typed source conclusion"
      let .ok #[term] := conclusion.getObjValAs? (Array Json) "terms"
        | throwError "a reported conclusion changed its original source terms"
      let .ok proof := conclusion.getObjVal? "proof"
        | throwError "a reported conclusion lost its evidence field"
      let .ok start := term.getObjValAs? Nat "startByte"
        | throwError "a reported question lost its original start position"
      let .ok stop := term.getObjValAs? Nat "stopByte"
        | throwError "a reported question lost its original end position"
      let original := ({ str := scopedSource, startPos := ⟨start⟩, stopPos := ⟨stop⟩ } :
        Substring.Raw).toString
      unless proof.isNull && term.getObjValAs? String "file" == .ok scopedFile.toString &&
          previousStop < start && start < stop && original == body do
        throwError "a reported source reading changed its identity, span or evidence"
      previousStop := stop
      let .ok context := term.getObjValAs? (Array Json) "context"
        | throwError "a reported source reading lost its complete context"
      let #[outerEntry, stagedEntry] := context
        | throwError "a reported question substituted the restored outer scope"
      unless context.map (·.getObjValAs? String "name") == #[.ok "outer", .ok "staged"] &&
          context.all (fun entry => entry.getObjValAs? String "role" == .ok "definition") do
        throwError "a reported question changed an original declaration or its role"
      let .ok outerId := outerEntry.getObjVal? "id"
        | throwError "a reported question lost its original outer binding identity"
      let expectedOuter := Json.mkObj [("session", toJson parentEntry.id.session),
        ("serial", toJson parentEntry.id.serial)]
      let .ok stagedId := stagedEntry.getObjVal? "id"
        | throwError "a reported question lost its original inner binding identity"
      unless outerId == expectedOuter && stagedId != outerId &&
          stagedIdentity.all (· == stagedId) do
        throwError "file reporting replaced a retained source occurrence"
      stagedIdentity := some stagedId
      let .ok categories := term.getObjValAs? (Array Json) "categories"
        | throwError "a reported question lost its complete selected-category table"
      let .ok native := term.getObjVal? "native"
        | throwError "a reported question lost its original native source term"
      unless categories.size == context.size &&
          native.getObjValAs? (Array Json) "context" == .ok context do
        throwError "a reported native term changed its complete source telescope"
      let .ok graph := term.getObjVal? "nativeExpressions"
        | throwError "a reported question lost its exact native graph"
      let .ok nodes := CasTools.NativeExpression.decodeNodes graph
        | throwError "a reported source graph did not decode"
      let .ok #[expression, type] := CasTools.NativeExpression.decode graph
        | throwError "a reported question changed its native expression and type roots"
      for field in #["expression", "type"], root in #[expression, type] do
        let .ok index := native.getObjValAs? Nat field
          | throwError "a reported source term lost its {field} reference"
        unless nodes[index]? == some root do
          throwError "a reported source root no longer refers to its original {field}"
      let mut closed := expression
      let mut closedType := type
      for entry in context.reverse do
        let .ok nameJson := entry.getObjVal? "nativeName"
          | throwError "a reported native declaration lost its name"
        let .ok name := CasTools.NativeExpression.nameFromJson nameJson
          | throwError "a reported native declaration's name did not decode"
        let .ok typeIndex := entry.getObjValAs? Nat "type"
          | throwError "a reported native definition lost its type"
        let some type := nodes[typeIndex]?
          | throwError "a reported definition type is outside its native graph"
        let .ok valueIndex := entry.getObjValAs? Nat "value"
          | throwError "a reported native definition lost its actual value"
        let some value := nodes[valueIndex]?
          | throwError "a reported definition value is outside its native graph"
        let .ok nondep := entry.getObjValAs? Bool "nondep"
          | throwError "a reported native definition lost its dependency information"
        closed := .letE name type value closed nondep
        closedType := .letE name type value closedType nondep
      unless !closed.hasFVar && !closed.hasLooseBVars &&
          !closedType.hasFVar && !closedType.hasLooseBVars do
        throwError "a reported question escaped its complete original native context"
      liftTermElabM do
        checkWithKernel (← mkExpectedTypeHint closed closedType)
    -- An older report may omit this additive source field. A present malformed value
    -- remains an error rather than being treated as an absent reading.
    let some firstRow := rows[0]?
      | throwError "the report compatibility control lost its original first item"
    let .obj fields := toJson firstRow
      | throwError "the public test result is no longer a JSON object"
    let .ok legacy := fromJson? (.obj (fields.erase "conclusions"))
        (α := CasCatalogue.Language.TestResult)
      | throwError "the additive native field made an older public report unreadable"
    unless legacy.conclusions.isEmpty &&
        toJson legacy == .obj (fields.insert "conclusions" (.arr #[])) do
      throwError "decoding an older report changed a legacy outcome or display field"
    let .error _ := fromJson? (.obj (fields.insert "conclusions" .null))
        (α := CasCatalogue.Language.TestResult)
      | throwError "a malformed native source payload was silently accepted"
    unless (← parent.kernel.dispatches.get).size == beforeFileCalls + 1 &&
        (← liftTermElabM SessionSnapshot.current).id == beforeFile.id do
      throwError "observing reported source data executed or published another request"

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
    let #[gapConclusion] := gap.conclusions
      | throwError "the failed block discarded its actual failing conclusion"
    let #[gapTerm] := gapConclusion.terms
      | throwError "the failed block changed its actual implementation request"
    let some failedChild := gap.observations.find? fun row =>
        row.outcome.any (fun outcome => outcome.kind == "gap" &&
          outcome.stratum? == some "noImplementation")
      | throwError "the failed block lost its actual failing item"
    let #[childConclusion] := failedChild.conclusions
      | throwError "the failed child discarded its original typed conclusion"
    let some temporary := gapConclusion.context.context.entries.back?
      | throwError "the failed child lost its original inner declaration"
    let afterGap ← liftTermElabM SessionSnapshot.current
    unless failedChild.attempted && gapConclusion.proof.isNone &&
        gapConclusion.context.context.exactlyMatches childConclusion.context.context &&
        gapTerm.source.context.exactlyMatches gapConclusion.context.context &&
        gapConclusion.context.context.entries.size == parent.source.context.entries.size + 1 &&
        temporary.userName == `temporary && temporary.role == .definition &&
        gap.inspectionOutput.isEmpty && afterGap.graph.sameRevision beforeGap.graph &&
        afterGap.outputBatches.size == beforeGap.outputBatches.size do
      throwError "retaining the failed inner request changed its source scope or block rollback"

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
    let beforeMissingState ← liftTermElabM SessionSnapshot.current
    let missingSource := "assert implemented 1 in R"
    let missing ← CasCatalogue.Language.runStatement abstractRun.session missingSource
    unless missing.outcome.kind == "gap" && !missing.published &&
        !missing.proposition.isEmpty &&
        (← parent.kernel.dispatches.get).size == beforeMissing do
      throwError "an unsupplied abstract input was sent to a concrete provider"
    let (missingConclusion, _) ← liftTermElabM <| retainedStatementTerm missing
      abstractRun.session.source.context missingSource "1 in R"
    let some retainedCategory := missingConclusion.context.categoryFor formalEntry.id
      | throwError "the failed implementation lost its original abstract category selection"
    let some originalCategory := abstractRun.session.source.categoryFor formalEntry.id
      | throwError "the implementation control lost its original source category"
    let afterMissing ← liftTermElabM SessionSnapshot.current
    unless missingConclusion.proof.isNone &&
        retainedCategory.expression.syntacticEq originalCategory.expression &&
        retainedCategory.bundle.expression == originalCategory.bundle.expression &&
        retainedCategory.bundle.type == originalCategory.bundle.type &&
        retainedCategory.bundle.universeParams == originalCategory.bundle.universeParams &&
        missing.session.source.context.exactlyMatches abstractRun.session.source.context &&
        afterMissing.id == beforeMissingState.id &&
        afterMissing.graph.sameRevision beforeMissingState.graph &&
        afterMissing.outputBatches.size == beforeMissingState.outputBatches.size do
      throwError "retaining the failed implementation changed its selected source or publication"

    -- Missing data on the right is prepared before the otherwise computable left can dispatch.
    let element ← CasCatalogue.Language.runStatement parent "let x ∈ ℤ"
    unless element.outcome.kind == "holds" do
      throwError "the independent formal element did not read"
    let beforeComparison := (← parent.kernel.dispatches.get).size
    let beforeComparisonState ← liftTermElabM SessionSnapshot.current
    let comparisonSource := "assert (17 + 29 in ℤ) = x"
    let missingRight ← CasCatalogue.Language.runStatement element.session
      comparisonSource
    unless missingRight.outcome.kind == "gap" && !missingRight.published &&
        !missingRight.proposition.isEmpty &&
        (← parent.kernel.dispatches.get).size == beforeComparison do
      throwError "comparison dispatched before admitting its complete abstract input"
    let (questionConclusion, questionTerm) ← liftTermElabM <| retainedStatementTerm missingRight
      element.session.source.context comparisonSource "(17 + 29 in ℤ) = x"
    let afterComparison ← liftTermElabM SessionSnapshot.current
    unless questionConclusion.proof.isNone &&
        missingRight.session.source.context.exactlyMatches element.session.source.context &&
        afterComparison.id == beforeComparisonState.id &&
        afterComparison.graph.sameRevision beforeComparisonState.graph &&
        afterComparison.outputBatches.size == beforeComparisonState.outputBatches.size do
      throwError "retaining the failed comparison changed its original scope or publication"
    liftTermElabM <| questionTerm.source.withOpen fun _ expression => do
      unless ← isProp expression do
        throwError "the failed question no longer retains its original proposition type"

  -- Computation-only mode retains supplied proof as source evidence, but still computes
  -- the actual proposition through the same ordinary public question path.
  CasCatalogue.Language.withSession (some path) true fun initial => do
    let result ← CasCatalogue.Language.runStatement initial
      "assert (17 + 29 = 46 in ℤ) using (proof(rfl))"
    unless result.outcome.kind == "holds" && result.published &&
        result.conclusions.any (·.proof.isSome) &&
        (← initial.kernel.dispatches.get).map (·.operation) == #["op.rings.add"] do
      throwError "supplied evidence bypassed the computation-only question policy"
    -- The supplied proof remains attached when the required computation throws on an
    -- unsupplied parameter. It does not discharge the computation-only request.
    let formal ← CasCatalogue.Language.runStatement initial "let x ∈ ℤ"
    unless formal.outcome.kind == "holds" && !formal.published do
      throwError "the proved-failure control did not retain its formal parameter"
    let beforeProofFailure ← liftTermElabM SessionSnapshot.current
    let beforeProofCalls := (← initial.kernel.dispatches.get).size
    let proofSource := "assert x = x using (proof(rfl))"
    let failedProof ← CasCatalogue.Language.runStatement formal.session proofSource
    let afterProofFailure ← liftTermElabM SessionSnapshot.current
    unless failedProof.outcome.kind == "gap" && !failedProof.published &&
        !failedProof.proposition.isEmpty &&
        (← initial.kernel.dispatches.get).size == beforeProofCalls &&
        failedProof.session.source.context.exactlyMatches formal.session.source.context &&
        afterProofFailure.id == beforeProofFailure.id &&
        afterProofFailure.graph.sameRevision beforeProofFailure.graph &&
        afterProofFailure.outputBatches.size == beforeProofFailure.outputBatches.size do
      throwError "retaining supplied evidence changed the actual computation failure or rollback"
    let (conclusion, proposition) ← liftTermElabM <| retainedStatementTerm failedProof
      formal.session.source.context proofSource "x = x"
    let some evidence := conclusion.proof
      | throwError "the failed proved question lost its explicitly supplied native evidence"
    liftTermElabM <| proposition.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      unless evidence.source.context.exactlyMatches conclusion.context.context &&
          (← isDefEq (← inferType (← evidence.source.inContext context)) expression) do
        throwError "the retained proof no longer proves the exact original failed question"

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
