module

import CasRuntime.Kernel
import all CasRuntime.Session
import all CasCompiler.Elaborate
import CasCompiler.SourceTestSupport
import CasRuntime.NativeMapEndpoints
import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
public meta import CasCompiler.Elaborate
meta import CasRuntime.Kernel
public meta import CasRuntime.Session
public meta import CasCompiler.SourceTestSupport
meta import CasRuntime.NativeMapEndpoints
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

namespace CasRuntime.BindingIdentityTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Language

private def statement (session : SourceSession) (text : String) :
    TermElabM SourceStatement := do
  let file ← SourceFile.parse "binding-identities.cas" text
  let #[item] := file.items
    | throwError "the binder control changed its original statement count"
  let `(cas_item| $source:cas_stmt) := item
    | throwError "the binder control changed its public statement syntax"
  file.withContext <| session.readStatement source

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the binder control's original source term did not parse"
  return ⟨parsed⟩

private meta def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the binder control's native function type did not parse"
  return ⟨parsed⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let producer ← CellTransaction.begin kernel.ledger
  let firstOwner ← owners.spawn { cmd := "/bin/cat" }
  let secondOwner ← owners.spawn { cmd := "/bin/cat" }
  try
    let empty ← SourceSession.empty owners.identities
    let .assumption firstSource ← statement empty "let x ∈ ℤ"
      | throwError "the original abstract element did not remain a native parameter"
    let some firstEntry := firstSource.context.entries.back?
      | throwError "the first source parameter lost its native identity"
    let firstTerm ← firstSource.read (← sourceTerm "x")
    let .definition aliasSource _ ← statement firstSource "let saved := x"
      | throwError "the original source alias did not retain a native definition"
    let some aliasEntry := aliasSource.context.entries.back?
      | throwError "the source alias lost its original native binding"
    let .assumption shadowSource ← statement aliasSource "let x ∈ ℤ"
      | throwError "the shadowing element did not remain a native parameter"
    let some secondEntry := shadowSource.context.entries.back?
      | throwError "the shadowing source parameter lost its native identity"
    let shadowTerm ← shadowSource.read (← sourceTerm "x")
    let aliasTerm ← shadowSource.read (← sourceTerm "saved")
    unless firstEntry.id != secondEntry.id && firstEntry.userName == `x &&
        secondEntry.userName == `x && aliasEntry.userName == `saved do
      throwError "source shadowing changed display names or reused an earlier binding identity"

    let lower : SourceTerm → Std.HashMap BindingId ValueBinding → MetaM ValueBinding :=
      fun term supplied => term.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        kernel.run producer context supplied expression
          (selections := ← term.selections.inContext context)
    let reopened : Std.HashMap BindingId ValueBinding → MetaM ValueBinding :=
      fun supplied => shadowTerm.source.withOpen fun bindings _ => do
        let context ← ContextTelescope.capture bindings
        let earlier ← firstTerm.source.inContext context
        let some retained := bindings.find? (·.id == firstEntry.id)
          | throwError "context reopening lost the original shadowed binder"
        unless earlier == retained.expression do
          throwError "context transport changed the earlier binder to its same-named successor"
        kernel.run producer context supplied earlier
          (selections := ← shadowTerm.selections.inContext context)
    let firstType ← firstSource.term (← nativeTerm "Int → Int")
    let firstFunction ← firstSource.read (← sourceTerm "t ↦ x") (some firstType.source)
      firstType.selections
    let type ← shadowSource.term (← nativeTerm "Int → Int")
    let function ← shadowSource.read (← sourceTerm "t ↦ saved") (some type.source)
      type.selections
    let identity ← shadowSource.read (← sourceTerm "t ↦ t") (some type.source)
      type.selections
    let nativeIdentity ← shadowSource.term (← nativeTerm "fun t : Int => t")


    let graphBefore ← producer.view
    let codeCount := (← kernel.codes.get).size
    let unsupplied : Array (BindingId × MetaM ValueBinding) := #[
      (firstEntry.id, lower firstTerm {}),
      (secondEntry.id, lower shadowTerm {}),
      (firstEntry.id, lower aliasTerm {}),
      (firstEntry.id, reopened {}),
      (firstEntry.id, lower firstFunction {}),
      (firstEntry.id, lower function {})]
    for (identity, action) in unsupplied do
      let failure : Option Exception ← try
        discard <| liftM (m := MetaM) action
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "an unsupplied source parameter acquired a runtime value"
      unless CasCatalogue.Exception.stratum? failure == some .noImplementation &&
          missingValueOf failure identity do throw failure
      unless graphBefore.sameRevision (← producer.view) &&
          (← kernel.codes.get).size == codeCount && (← kernel.dispatches.get).isEmpty do
        throwError "an unsupplied source parameter staged graph data, code or an external demand"



    for term in #[nativeIdentity, identity] do
      let value ← lower term {}
      let graph ← producer.view
      let .ok code := graph.callable value
        | throwError "the identity lambda lost its actual callable"
      let some node := graph.find code.value
        | throwError "the identity lambda lost its retained native code"
      let .closure program captures := node.payload.data
        | throwError "the identity lambda changed its callable representation"
      unless captures.isEmpty do
        throwError "the identity lambda captured an unused original source parameter"
      let some (.term retainedSource _) := (← kernel.codes.get)[program]?
        | throwError "the identity lambda lost its original closed term"
      unless retainedSource.context.exactlyMatches term.source.context &&
          retainedSource.expression.equal term.source.expression do
        throwError "the identity lambda changed its original source or complete context"



    let firstToken ← liftM (m := IO) do
      firstOwner.child.stdin.putStr "first captured parameter\n"
      firstOwner.child.stdin.flush
      return (← firstOwner.child.stdout.getLine).trimAscii.toString
    let secondToken ← liftM (m := IO) do
      secondOwner.child.stdin.putStr "second shadowed parameter\n"
      secondOwner.child.stdin.flush
      return (← secondOwner.child.stdout.getLine).trimAscii.toString
    let stage := fun (term : SourceTerm) (payload : ValuePayload) =>
      term.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let selections ← term.selections.inContext context
        let environment ← RuntimeEnvironment.capture owners.worker context #[]
          (selections := selections)
        let origin ← environment.origin (← owners.identities.fresh .program)
          (← kernel.ledger.allocate) (← SourceLayout.ofTerm (← context.close expression)
            (selections := ← selections.close context))
        producer.stage origin payload
    let firstValue ← stage firstTerm (.ownedExport firstOwner firstToken #[])
    let secondValue ← stage shadowTerm (.ownedExport secondOwner secondToken #[])
    let bound : Std.HashMap BindingId ValueBinding :=
      ({} : Std.HashMap BindingId ValueBinding).insert firstEntry.id firstValue
        |>.insert secondEntry.id secondValue
    unless (bound[aliasEntry.id]?).isNone do
      throwError "the native-alias control accidentally supplied its own runtime binding"



    let firstActual ← lower firstTerm (bound.erase secondEntry.id)
    let secondActual ← lower shadowTerm bound
    let aliasActual ← lower aliasTerm bound
    let reopenedActual ← reopened bound
    unless firstActual.exactlyMatches firstValue &&
        secondActual.exactlyMatches secondValue &&
        aliasActual.exactlyMatches firstValue &&
        reopenedActual.exactlyMatches firstValue && firstValue.value != secondValue.value do
      throwError "supplied source identity changed under shadowing, native aliasing or reopening"

    let callable ← function.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      kernel.run producer context bound expression
        (selections := ← function.selections.inContext context)
    let graph ← producer.view
    let .ok code := graph.callable callable
      | throwError "the source lambda lost its actual callable"
    let some node := graph.find code.value
      | throwError "the source lambda lost its retained native code"
    let .closure program captures := node.payload.data
      | throwError "the source lambda was replaced by another computational interface"
    let #[capture] := captures
      | throwError "a native alias lost or enlarged its exact earlier capture"
    unless capture.value == firstValue.value &&
        capture.associationIds == firstValue.associationIds &&
        capture.value != secondValue.value do
      throwError "the native alias captured the shadowing value instead of its original occurrence"
    let some (.term retainedSource _) := (← kernel.codes.get)[program]?
      | throwError "the source lambda lost its original closed term"
    unless retainedSource.context.exactlyMatches function.source.context &&
        retainedSource.expression.equal function.source.expression do
      throwError "closure capture changed the complete original source or native telescope"
    let .ok dependencies := graph.requiredOwners #[callable]
      | throwError "the original closure capture is outside its active graph"
    unless dependencies == #[firstOwner.generation] do
      throwError "the closure did not retain exactly the owner of its original alias capture"

    let functions ← shadowSource.defineTerm `f function
    let some functionEntry := functions.context.entries.back?
      | throwError "the source function lost its original definition binding"
    let applied ← functions.read (← sourceTerm "f(saved)")
    let consuming := bound.insert functionEntry.id callable
    let .ok _ ← producer.commit
      | throwError "the source closure and its actual input values did not publish"
    owners.close secondOwner.generation
    let consumer ← CellTransaction.begin kernel.ledger
    try
      let result ← applied.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        kernel.run consumer context consuming expression
          (selections := ← applied.selections.inContext context)
      unless result.value == firstValue.value &&
          firstValue.associationIds.toList.isPrefixOf result.associationIds.toList do
        throwError "the actual source application replaced its original captured value"
      unless ← (← consumer.view).isAvailable owners callable do
        throwError "an unused shadowing owner invalidated the original closure"
      let .ok _ ← consumer.commit
        | throwError "the source application could not publish its original captured result"
    finally discard <| consumer.abort
    owners.close firstOwner.generation
    let unavailable ← CellTransaction.begin kernel.ledger
    try
      unless !(← (← unavailable.view).isAvailable owners callable) do
        throwError "the closed original capture remained available after its owner retired"
      let failure : Option Exception ← try
        discard <| applied.source.withOpen fun bindings expression => do
          let context ← ContextTelescope.capture bindings
          kernel.run unavailable context consuming expression
            (selections := ← applied.selections.inContext context)
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "an actual application consumed its retired captured owner"
      unless CasCatalogue.Exception.stratum? failure == some .unavailable do throw failure
    finally discard <| unavailable.abort
    unless (← kernel.dispatches.get).isEmpty do
      throwError "native binder identity or capture preservation dispatched an external operation"
  finally
    discard <| producer.abort
    owners.close firstOwner.generation
    owners.close secondOwner.generation
    kernel.close
    setEnv original




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin kernel.ledger
  try
    let context ← ContextTelescope.capture #[]
    let source := mkNatLit 7
    let actual ← kernel.run transaction context {} source
    withBoundValue owners.identities context {} source actual fun context bound retainedSource => do
      let callable ← withLocalDeclD `unused (mkConst ``Unit) fun argument =>
        mkLambdaFVars #[argument] retainedSource
      checkWithKernel callable
      let retained ← kernel.run transaction context bound callable
      let graph ← transaction.view
      let some node := graph.find retained.value
        | throwError "the ordinary bound closure was not retained"
      let .closure _ captures := node.payload.data
        | throwError "the bound native function lost its callable code"
      unless captures.map (·.value) == #[actual.value] do
        throwError "the bound native function lost its exact actual capture"
      let codeCount := (← kernel.codes.get).size
      let emptyEnvironment ← RuntimeEnvironment.captureBound owners.worker context {} graph
      let missingReference : Option Exception ← try
        discard <| emptyEnvironment.hasRetainedSource context retainedSource
        pure none
      catch error => pure (some error)
      let some missingReference := missingReference
        | throwError "a missing actual occurrence was treated as a source-only parameter"
      unless (← missingReference.toMessageData.toString).endsWith
          "the source lost a retained runtime binding" do throw missingReference

      checkWithKernel callable
      let failed : Option Exception ← try
        discard <| kernel.run transaction context {} callable
        pure none
      catch error => pure (some error)
      let some failed := failed
        | throwError "a closure silently discarded its missing actual runtime capture"
      unless (← failed.toMessageData.toString).endsWith
          "the source lost a retained runtime binding" do throw failed
      unless graph.sameRevision (← transaction.view) &&
          (← kernel.codes.get).size == codeCount && (← kernel.dispatches.get).isEmpty do
        throwError "a lost capture published closure code, graph data or an external demand"
  finally
    discard <| transaction.abort
    kernel.close
    setEnv original



run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let producer ← CellTransaction.begin kernel.ledger
  try
    let context ← ContextTelescope.capture #[]
    let seven := mkNatLit 7
    let first ← kernel.run producer context {} seven
    let second ← kernel.run producer context {} seven
    unless first.value != second.value do
      throwError "equal-source control did not produce distinct runtime occurrences"
    withBoundValue owners.identities context {} seven first fun context bound firstSource => do
      withBoundValue owners.identities context bound seven second fun context bound secondSource => do
        unless firstSource.isFVar && secondSource.isFVar && firstSource != secondSource do
          throwError "equal defining expressions lost their distinct native runtime binders"
        let pairSource ← mkAppM ``Prod.mk #[firstSource, secondSource]
        let pair ← kernel.run producer context bound pairSource
        withBoundValue owners.identities context bound pairSource pair fun context bound pairSource => do
          let projected ← kernel.run producer context bound (mkProj ``Prod 0 pairSource)
          unless projected.value == first.value && projected.value != second.value do
            throwError "projection substituted the equal-valued sibling occurrence"
          let substituted ← withLetDecl `samePair (← inferType pairSource) pairSource fun aliasValue =>
            mkLetFVars #[aliasValue] (mkProj ``Prod 0 aliasValue) (usedLetOnly := false)
          let substituted ← kernel.run producer context bound substituted
          unless substituted.value == first.value && substituted.value != second.value do
            throwError "native substitution changed the selected original field occurrence"
          let callableSource ← withLocalDeclD `unused (mkConst ``Nat) fun unused =>
            mkLambdaFVars #[unused] (mkProj ``Prod 1 pairSource)
          let callable ← kernel.run producer context bound callableSource
          withBoundValue owners.identities context bound callableSource callable
              fun context bound callableSource => do
            let application ← context.close (mkApp callableSource firstSource)
            let .ok _ ← producer.commit
              | throwError "the equal-source producer did not publish its complete captured context"
            let consumer ← CellTransaction.begin kernel.ledger
            try
              let result ← application.withOpen fun bindings expression => do
                kernel.run consumer (← ContextTelescope.capture bindings) bound expression
              unless result.value == second.value && result.value != first.value do
                throwError "a later call replaced its captured field with an equal input"
              let .ok _ ← consumer.commit
                | throwError "the later call did not preserve its original captured result"
            finally discard <| consumer.abort
    unless (← kernel.dispatches.get).isEmpty do
      throwError "runtime occurrence preservation dispatched an external mathematical operation"
  finally
    discard <| producer.abort
    kernel.close
    setEnv original



run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 1000
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin kernel.ledger
  try
    let empty ← SourceSession.empty owners.identities
    let selected ← empty.read (← sourceTerm "ℤ")
    selected.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let selections ← selected.selections.inContext context
      let some sourceBinding := bindings.find? (·.expression == expression)
        | throwError "the public object lost its explicit typed source binder"
      unless sourceBinding.role == .selectedStructure && selections.contains sourceBinding.id do
        throwError "the public object lost its complete selected source role"
      discard <| kernel.run transaction context {} expression (selections := selections)
      let graph ← transaction.view
      let codeCount := (← kernel.codes.get).size
      let broken := selections.erase sourceBinding.id
      let expectMissing := fun (action : MetaM Unit) => do
        let failed : Option Exception ← try
          action
          pure none
        catch error => pure (some error)
        let some failed := failed
          | throwError "a missing typed selection became a source-only native value"
        unless (← failed.toMessageData.toString).endsWith
            "the source lost its retained typed selection" do throw failed
      expectMissing do
        discard <| boundSourceReferences (some graph) context {} expression broken
      expectMissing do
        let environment ← RuntimeEnvironment.captureBound owners.worker context {} graph
          (selections := broken)
        discard <| environment.hasRetainedSource context expression
      expectMissing do
        let environment ← RuntimeEnvironment.captureBound owners.worker context {} graph
          (selections := broken)
        discard <| environment.endpointValue? context graph expression
      expectMissing do
        discard <| kernel.run transaction context {} expression (selections := broken)
      unless graph.sameRevision (← transaction.view) &&
          (← kernel.codes.get).size == codeCount && (← kernel.dispatches.get).isEmpty do
        throwError "a lost typed selection published graph data, code or an external demand"
  finally
    discard <| transaction.abort
    kernel.close
    setEnv original






public meta opaque observePublicOccurrences (path : System.FilePath)
    (definition : String := "nativeSeven")
    (expectedDispatches : Array (String × String × String) := #[])
    (nativeType : String := "Nat") : TermElabM Unit := do
  let original ← getEnv
  try
    let initial ← KernelSession.start (some path) (computationOnly := true)
    try
      unless initial.kernel.rejected.isEmpty do
        throwError "the public occurrence control lost an admitted peer registration"
      let mut source := initial.source
      for (name, body) in #[
          (`nativeSeven, "(7 : Nat)"),
          (`nativePair, s!"fun (left right : {nativeType}) => (left, right)"),
          (`nativeFirst, s!"fun (pair : {nativeType} × {nativeType}) => pair.1"),
          (`nativeSubstituted, s!"fun (pair : {nativeType} × {nativeType}) => let samePair := pair; samePair.1"),
          (`nativePick, s!"fun (pair : {nativeType} × {nativeType}) (_ : {nativeType}) => pair.2")] do
        source ← source.define name (← nativeTerm body)
      let mut session := { initial with source }
      let runStatement := fun (session : KernelSession) (text : String) => do
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "the public occurrence statement did not parse: {text}"
        withoutErrToSorry <| session.run ⟨parsed⟩
      let mut retained : Array (BindingId × ValueBinding) := #[]
      for (name, text) in #[
          (`first, s!"let first := {definition}"),
          (`second, s!"let second := {definition}"),
          (`pair, "let pair := nativePair(first, second)"),
          (`projected, "let projected := nativeFirst(pair)"),
          (`alias, "let «alias» := pair"),
          (`substituted, "let substituted := nativeSubstituted(«alias»)"),
          (`pick, "let pick := nativePick(pair)"),
          (`later, "let later := pick(first)")] do
        let run ← runStatement session text
        unless run.outcome.kind == "holds" && run.attempted && run.published do
          throwError "the public occurrence statement did not commit: {text}: {run.outcome.detail}"
        session := run.session
        let some entry := (← SourceTest.authoredEntries
            session.source.context session.source.selections).back?
          | throwError "the public occurrence statement lost its authored declaration"
        unless entry.userName == name do
          throwError "the public occurrence statement changed its original result binding"
        let some value := session.value? entry.id
          | throwError "the public occurrence statement lost its actual computed reference"
        retained := retained.push (entry.id, value)
      let #[first, second, pair, projected, aliasValue, substituted, pick, later] := retained
        | throwError "the public occurrence control changed its original statement count"
      unless first.1 != second.1 && first.2.value != second.2.value do
        throwError "equal public definitions shared one source or runtime occurrence"
      unless retainsReference first.2 projected.2 && retainsReference first.2 substituted.2 &&
          projected.2.value != second.2.value && substituted.2.value != second.2.value &&
          retainsReference pair.2 aliasValue.2 &&
          retainsReference second.2 later.2 && later.2.value != first.2.value do
        throwError "a public projection, substitution or later call changed its chosen occurrence"
      let published ← SessionSnapshot.current
      for (_, value) in retained do
        unless (published.graph.find value.value).isSome do
          throwError "a public occurrence did not survive its publication boundary"
      let .ok (some firstPacket) := published.graph.packet? first.2
        | throwError "the first public literal lost its admitted descriptor"
      let .ok (some secondPacket) := published.graph.packet? second.2
        | throwError "the second public literal lost its admitted descriptor"
      unless firstPacket == secondPacket do
        throwError "the distinct-occurrence control no longer has equal actual literals"
      let .ok _ := published.graph.callable pick.2
        | throwError "the public delayed projection lost its retained callable"
      let implemented ← runStatement session "assert implemented later"
      unless implemented.outcome.kind == "holds" && implemented.published do
        throwError "the committed original field could not be demanded by a later public statement"
      session := implemented.session
      unless (← session.kernel.dispatches.get).map
          (fun registration => (registration.operation, registration.input, registration.backend)) ==
            expectedDispatches do
        throwError "public occurrence preservation changed its actual registered dispatches"



      let objectRun ← runStatement session "let R := ℤ"
      unless objectRun.outcome.kind == "holds" && objectRun.published do
        throwError "the ordinary public selected object did not commit: {objectRun.outcome.detail}"
      session := objectRun.session
      let selected := session.source.context.entries.filter (·.role == .selectedStructure)
      unless !selected.isEmpty do
        throwError "the ordinary public object did not retain a typed selection binder"
      let .ok reuse := Parser.runParserCategory (← getEnv) `cas_stmt "let reused := R"
        | throwError "the ordinary public object reuse did not parse"
      for entry in selected do
        unless session.source.selections.contains entry.id do
          throwError "the original public source was already missing a selected row"
        let brokenSource := { session.source with
          selections := session.source.selections.erase entry.id }
        let broken := { session with source := brokenSource }
        let before ← SessionSnapshot.current
        let codeCount := (← session.kernel.codes.get).size
        let dispatchCount := (← session.kernel.dispatches.get).size
        let failure : Option Exception ← try
          discard <| broken.source.readStatement ⟨reuse⟩
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "the reader accepted a public source with a missing selected row"
        unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReadM.missingSelection) do
          throw failure
        let failed ← withoutErrToSorry <| broken.run ⟨reuse⟩
        let .internal message := failed.outcome
          | throwError "the public boundary changed the missing-selection reader failure"
        unless message.endsWith "the source lost its retained typed selection" &&
            !failed.attempted && !failed.published &&
            failed.session.source.context.exactlyMatches session.source.context &&
            !failed.session.source.selections.contains entry.id &&
            failed.session.source.selections.size + 1 == session.source.selections.size do
          throwError "a missing public source selection entered execution or changed its original scope"
        unless before.graph.sameRevision (← SessionSnapshot.current).graph &&
            (← session.kernel.codes.get).size == codeCount &&
            (← session.kernel.dispatches.get).size == dispatchCount do
          throwError "a reader-rejected selected source changed graph, code or dispatch state"
    finally initial.close
  finally setEnv original

run_cmd Lean.Elab.Command.liftTermElabM do
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  let path := root / ".tmp/kernel-binding-identity-empty-leaves.json"
  IO.FS.writeFile path
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
  observePublicOccurrences path

end CasRuntime.BindingIdentityTests
