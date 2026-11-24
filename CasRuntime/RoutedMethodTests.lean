module

import CasRuntime.Session
import CasRuntime.RoutedMethod
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasRuntime.RoutedMethod
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra

namespace CasRuntime.RoutedMethodTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue CasCatalogue.Backend

private def failureAt (stratum : Stratum) (action : MetaM Unit) : MetaM Unit := do
  let failure : Option Exception ← try
    action
    pure none
  catch error => pure (some error)
  let some error := failure | throwError "the routed-method negative control was accepted"
  unless CasCatalogue.Exception.stratum? error == some stratum do throw error

private def readTerm (session : KernelSession) (text : String) : TermElabM SourceTerm := do
  let parsed ← match Parser.runParserCategory (← getEnv) `cas_term text with
    | .ok parsed => pure parsed
    | .error message => throwError "the original method term did not parse: {message}"
  session.source.read ⟨parsed⟩

private def define (session : KernelSession) (text : String) : TermElabM KernelSession := do
  let parsed ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
    | .ok parsed => pure parsed
    | .error message => throwError "the original source declaration did not parse: {message}"
  let result ← withoutErrToSorry <| session.run ⟨parsed⟩
  unless result.outcome.kind == "holds" do
    throwError "`{text}` is {result.outcome.kind}: {result.outcome.detail}"
  return result.session

private def value (session : KernelSession) (name : Name) : MetaM ValueBinding := do
  let some entry := session.source.context.entries.find? (·.userName == name)
    | throwError "the original source binding {name} is absent"
  let some binding := session.value? entry.id
    | throwError "the original source binding {name} has no actual value"
  return binding

/-- Intercept the final real method application before Execute.run owns it. Every setup demand
uses the production executor and resolver. Throwing only outside that interpreter leaves the
cell available for the structural selection/packet checks; no method response is fabricated. -/
private def captureMethod (kernel : Kernel) (transaction : CellTransaction)
    (action : SourceEvaluation → MetaM ValueBinding) :
    MetaM (PreparedRequest × PreparedMethodRoute) := do
  let captured ← IO.mkRef (none : Option
    (PreparedRequest × PreparedRequest × Array FieldLayout × Array ValueBinding))
  let evaluate : SourceEvaluation := fun cell program context bound expression => do
    let handler : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
      fun request current => do
        if let .apply callable _ _ := request.action then
          let graph ← current.view
          if let .ok callable := graph.callable callable then
            if let some node := graph.find callable.value then
              if let .closure code captures := node.payload.data then
                if let some (.family original path) := (← kernel.codes.get)[code]? then
                  if let .primitive (.routedMethod _) _ := original.action then
                    captured.set (some (request, original, path, captures))
                    throwError "captured the original prepared method application"
        let response ← Execute.run kernel.executor
          (PFunctor.FreeM.lift (P := OperationalSignature) request) current
          (some (kernel.resolveFixedInput
            (fun cell _ context bound expression => kernel.run cell context bound expression)
            current program))
        return (response, current)
    lowerTerm {
      ledger := kernel.ledger, transaction := cell, codes := kernel.codes, marks := kernel.marks
      run := fun computation => do
        let (value, _) ← handler.run computation cell
        return value }
      program context bound expression
  let failure : Option Exception ← try
    discard <| action evaluate
    pure none
  catch error => pure (some error)
  let some (request, original, path, captures) ← captured.get
    | if let some error := failure then throw error
      else throwError "the source never reached its original prepared method application"
  return (request, ← PreparedMethodRoute.prepare kernel (← transaction.view)
    request original path captures)

/-- Exercise the complete original reader output through production Lower, including exact
receiver-slot recovery. The capture is solely a stop before a mathematical method result. -/
private def prepare (session : KernelSession) (transaction : CellTransaction)
    (term : SourceTerm) : MetaM (PreparedRequest × PreparedMethodRoute) :=
  term.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let mut bound : Std.HashMap BindingId ValueBinding := {}
    for binding in bindings do
      if let some value := session.value? binding.id then bound := bound.insert binding.id value
    let program ← session.kernel.ledger.owners.identities.fresh .program
    captureMethod session.kernel transaction fun evaluate =>
      evaluate transaction program context bound expression

private def manifest (operation : String) (inputs : Array String) : MetaM Manifest := do
  let packet := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "unused-method-peer"),
      ("command", "/bin/false"), ("args", .arr #[])]]),
    ("registrations", .arr (inputs.map fun input => Json.mkObj [
      ("operation", toJson operation), ("input", toJson input),
      ("backend", toJson "unused-method-peer")]))]
  IO.ofExcept <| (Manifest.parse packet).mapError IO.userError

private def select (route : PreparedMethodRoute) (inputs : Array String) :
    MetaM SelectedMethodBoundary := do
  let installed ← manifest route.family.entry.id.raw inputs
  let profile ← RealizationProfile.prepare installed none
  route.select profile installed

private def evaluate (kernel : Kernel) : SourceEvaluation :=
  fun transaction _ context bound expression => kernel.run transaction context bound expression

private def sameExactInput (left right : ValueBinding) : Bool :=
  left.value == right.value && left.associationIds == right.associationIds

private def sameInput (original current : ValueBinding) : Bool :=
  original.value == current.value &&
    original.associationIds.toList.isPrefixOf current.associationIds.toList

-- Rank's accepted declaration has one universe, while its nominal owner has independent
-- scalar and module universes. The complete source family retains the declaration's diagonal
-- relation at an arbitrary universe; it neither defaults to zero nor widens to other fibres.
run_cmd liftTermElabM do
  let state ← semanticState
  let #[entry] := state.methods.filter (·.id.raw == "meth.rank")
    | throwError "the rank control lost its accepted method declaration"
  let #[family] ← RoutedMethodFamily.atSource entry.owner entry.name
    | throwError "the rank control changed its complete first-hit family"
  unless family.entry.shape == .isoInvariant && family.parameterCount == 1 &&
      family.universeParams.length == 1 do
    throwError "the rank source lost its original shape, parameter or universe family"
  for expression in #[family.categoryFamily, family.functorFamily, family.family] ++ family.actions do
    if expression.hasFVar || expression.hasMVar || expression.hasLevelMVar then
      throwError "the rank source family did not close all original parameters and universes"
  let #[repeated] ← RoutedMethodFamily.atSource entry.owner entry.name
    | throwError "the repeated rank source changed its original family"
  unless (← sourceFamilyConversion family.functorFamily repeated.functorFamily #[]).isSome do
    throwError "independent rank readings changed their complete rigid family"
  let arbitraryLevel := Level.param `rankDeclarationUniverse
  let categoryFamily := family.categoryFamily.instantiateLevelParams family.universeParams [arbitraryLevel]
  forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
    let #[ring] := parameters
      | throwError "the rank family lost its original ring parameter"
    let expected := mkApp
      (Lean.mkConst ``LeanCategories.Modules.Mathlib.ModulesOf [arbitraryLevel, arbitraryLevel]) ring
    unless ← isDefEq (mkAppN categoryFamily parameters) expected do
      throwError "the rank owner did not retain its declared universe relation"
    let #[action] ← family.specializeActions [arbitraryLevel] parameters
      | throwError "the rank owner acquired a synthetic route action"
    let #[(_, supplied)] ← routedActionParameters (.functor family.functor.id) action
      | throwError "the rank action lost its original explicit parameter position"
    unless supplied.consumeMData == ring do
      throwError "the rank action reconstructed its whole original ring parameter"
    let (declared, _) ← functorCategoryBundles action
    let core ← applyConstructorInterface ``CasCatalogue.Constructors.core #[expected] #[expected]
    unless ← isDefEq declared core do
      throwError "the rank method lost its complete native Core domain"
    if ← isDefEq declared expected then
      throwError "the rank method identified its Core domain with the ordinary owner"
    let callable := (mkAppN
      (family.family.instantiateLevelParams family.universeParams [arbitraryLevel]) parameters).headBeta
    let .forallE _ domain _ _ ← whnf (← inferType callable)
      | throwError "the rank family lost its original receiver boundary"
    unless ← isDefEq domain (← mkAppM ``CategoryTheory.Bundled.α #[expected]) do
      throwError "the rank callable replaced its original receiver by a synthetic Core input"
  let scalarUniverse := Level.param `rankScalarUniverse
  let moduleUniverse := Level.param `rankModuleUniverse
  withLocalDeclD `ring (Lean.mkConst ``RingCat [scalarUniverse]) fun ring => do
    let independent := mkApp
      (Lean.mkConst ``LeanCategories.Modules.Mathlib.ModulesOf [scalarUniverse, moduleUniverse]) ring
    let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
    let category := family.categoryFamily.instantiateLevelParams family.universeParams levels
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType category)
    if ← withoutModifyingState <| isDefEq (mkAppN category parameters) independent then
      throwError "the rank declaration was widened to independent module and scalar universes"

-- These are source/interface and dispatch controls only. The accepted native methods, routes,
-- object constructors and parameter telescopes supply every mathematical declaration. No leaf
-- computes a cardinality, rank, kernel or a replacement mathematical result in this module.
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← IO.currentDir
    IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "routed-method-empty-leaves.json"
    IO.FS.writeFile path (Json.mkObj [("backends", .arr #[]),
      ("registrations", .arr #[])]).compress
    let mut session ← KernelSession.start (some path) (computationOnly := true)
    try
      for text in #["let S3 := Sym(3) in Groups", "let S3again := Sym(3) in Groups",
          "let equal_ends := trivial(S3, S3again)"] do
        session ← define session text
      let s3 ← value session `S3
      let second ← value session `S3again
      unless s3.value != second.value do
        throwError "the distinct source group declarations share one fabricated value"
      let term ← readTerm session "|S3|"
      let transaction ← CellTransaction.begin session.kernel.ledger
      try
        let (request, route) ← prepare session transaction term
        unless route.family.entry.id.raw == "meth.cardinality" &&
            route.boundaries.size > 2 && sameInput s3 route.receiver do
          throwError "the cardinality source lost its original full inherited route"
        let before ← transaction.view
        failureAt .noImplementation do
          discard <| select route #[]
        -- The old generic dependentContext input is not a released method boundary.
        failureAt .noImplementation do
          discard <| select route #[s!"{route.family.entry.id.raw}#input"]
        let some sourceBoundary := route.boundaries[0]?
          | throwError "the source method boundary is absent"
        let some ownerBoundary := route.boundaries.back?
          | throwError "the owner method boundary is absent"
        let some sourceForm := sourceBoundary.forms[0]?
          | throwError "the source method has no complete registered category"
        let some ownerForm := ownerBoundary.forms[0]?
          | throwError "the owner method has no complete registered category"
        failureAt .ambiguousRealization do
          discard <| select route #[sourceForm, ownerForm]
        -- Occurrence counting also rejects one triple admitted at two boundary positions.
        failureAt .ambiguousRealization do
          let installed ← manifest route.family.entry.id.raw #[sourceForm]
          let profile ← RealizationProfile.prepare installed none
          discard <| profile.selectMethod installed route.family.entry.id
            #[#[sourceForm], #[sourceForm]]
        unless (← transaction.view).sameRevision before &&
            (← session.kernel.dispatches.get).isEmpty do
          throwError "method realization inspection executed a prefix or dispatched a leaf"

        let some intermediate := route.boundaries[1]?
          | throwError "the original inherited method has no intermediate boundary"
        let some intermediateForm := intermediate.forms[0]?
          | throwError "the intermediate method has no registered category"
        let selection ← select route #[intermediateForm]
        let offset := selection.boundary.offset
        unless offset == 1 do throwError "method selection changed its exact intermediate position"
        let .registration _ := selection.realization
          | throwError "the selected protocol control became a mathematical derivation"
        let calls ← IO.mkRef 0
        let ordinary : SourceEvaluation := fun cell program context bound expression => do
          calls.modify (· + 1)
          evaluate session.kernel cell program context bound expression
        let selected ← selection.materialize session.kernel ordinary request transaction
        unless (← calls.get) == offset do
          throwError "the method executed more than the uniquely selected prefix"
        let invocation ← selected.invocation session.kernel (evaluate session.kernel) request transaction
        let expected := (route.family.route.refs.extract offset route.family.route.refs.size).push
          (.functor route.family.functor.id)
        unless invocation.offset == offset && invocation.edges == expected &&
            invocation.parameters.size == expected.size &&
            sameExactInput invocation.receiver selected.receiver do
          throwError "the method packet changed its residual suffix or selected receiver"
        let registry : RegistryState := { toSemanticState := ← semanticState }
        let some imageForm := intermediate.forms.find? (fun input =>
            match registry.form? input with
            | some (.functorImage ..) | some (.edgeImage ..) => true
            | _ => false)
          | throwError "the selected intermediate route lost its published image form"
        withSourceScope request fun context _ => do
          let source ← selected.receiverSource.inContext context
          let childFamily ← RoutedMethodFamily.forSelection intermediate.category
            route.family.entry.id.raw
            (route.family.route.refs.extract offset route.family.route.refs.size)
          unless ← CasRuntime.RoutedMethodFamily.admitsSourceForm childFamily source imageForm do
            throwError "the original native object-action spine rejected its image form {imageForm}: {source}"
          let .mdata metadata unmarked := source
            | throwError "the selected method image lost its original source witness"
          unless metadata.getName `CasCompiler.source.kind == ``EdgeRef do
            throwError "the selected method image changed its source witness kind"
          let .ok (edge : EdgeRef) := (Json.parse (metadata.getString `CasCompiler.source.id)).bind fromJson?
            | throwError "the selected method image lost its complete original edge"
          unless route.family.route.refs[offset - 1]? == some edge do
            throwError "the selected method image changed its original edge identity"
          if ← CasRuntime.RoutedMethodFamily.admitsSourceForm childFamily unmarked imageForm then
            throwError "an unselected native image recovered a catalogue address from its declaration"
          let declaration := metadata.getName `CasCompiler.source.declaration
          let direct := match edge with
            | .functor id => some (sourceReference ``EdgeRef.functor id.raw declaration unmarked)
            | .classifierForget id => some (sourceReference ``EdgeRef.classifierForget id.raw declaration unmarked)
            | .constructMap .. => none
          if let some direct := direct then
            unless ← CasRuntime.RoutedMethodFamily.admitsSourceForm childFamily direct imageForm do
              throwError "the original source-reader image reference lost its selected form"
        let connection ← session.kernel.ledger.owners.spawn { cmd := "/bin/cat" }
        try
          let graph ← transaction.view
          let .ok (encoded, packet) := invocation.encode graph connection.generation
            | throwError "the intermediate method packet lost its exact image receiver"
          let .ok decoded := ConstructionInvocation.decodeMethod route.family.entry.id.raw
              route.family.functor.id.raw packet
            | throwError "the intermediate method did not retain its complete residual packet"
          let identity : DispatchIdentity := {
            manifestDigest := "method-image-child-control"
            profileDigest := "no-mathematical-provider"
            registration := {
              operation := route.family.entry.id.raw
              input := imageForm
              backend := "scope-control" } }
          let .ok reservation ← transaction.reserve request.occurrence identity connection
              invocation.dependencies
            | throwError "the intermediate method lost its original scoped receiver"
          let scope ← RequestScope.issue session.kernel.ledger reservation graph
            encoded.slots encoded.inputs #[]
          try
            let packet := { decoded with receiver := inputRef #[.field "receiver"] }
            let call := Json.mkObj [("op", toJson route.family.entry.id.raw),
              ("input", toJson imageForm), ("args", packet.encode)]
            let (_, childRoute) ← captureMethod session.kernel transaction fun evaluate =>
              session.kernel.child evaluate request transaction reservation scope call
            unless childRoute.family.route.refs ==
                route.family.route.refs.extract offset route.family.route.refs.size &&
                sameExactInput childRoute.receiver invocation.receiver do
              throwError "the image-form child lost its original selected edge result"
            let some childSource := childRoute.boundaries[0]?
              | throwError "the image-form child lost its prepared source boundary"
            unless childSource.forms.contains imageForm do
              throwError "the image-form child discarded its admitted intermediate source form"
            let childSelection ← select childRoute #[imageForm]
            unless childSelection.boundary.offset == 0 do
              throwError "the original image form moved after the deferred round trip"
          finally scope.retire
        finally session.kernel.ledger.owners.close connection.generation
        let original ← (← select route #[sourceForm]).materialize session.kernel ordinary request transaction
        unless sameExactInput original.receiver route.receiver && (← calls.get) == offset do
          throwError "a source-composite registration transported or replaced its receiver"
        let owner ← (← select route #[ownerForm]).materialize session.kernel
          (evaluate session.kernel) request transaction
        let ownerInvocation ← owner.invocation session.kernel (evaluate session.kernel) request transaction
        unless ownerInvocation.edges == #[.functor route.family.functor.id] &&
            sameExactInput ownerInvocation.receiver owner.receiver do
          throwError "the owner registration retained a residual action or another receiver"
        unless (← session.kernel.dispatches.get).isEmpty do
          throwError "the native input projections in method preparation dispatched a provider"
      finally discard <| transaction.abort

      -- The actual group-arrow method sends one Arrow view rooted at the original native
      -- parent. Its equal but separately declared endpoints remain distinct scoped values.
      let term ← readTerm session "equal_ends.ker()"
      let transaction ← CellTransaction.begin session.kernel.ledger
      let connection ← session.kernel.ledger.owners.spawn { cmd := "/bin/cat" }
      try
        let (request, route) ← prepare session transaction term
        unless route.family.entry.id.raw == "meth.group_arrow_kernel" &&
            route.family.route.refs.isEmpty do
          throwError "the original kernel method acquired a different source route"
        let selected ← (← select route #["cat.arrows_groups"]).materialize session.kernel
          (evaluate session.kernel) request transaction
        let invocation ← selected.invocation session.kernel (evaluate session.kernel) request transaction
        let graph ← transaction.view
        let .ok (encoded, packet) := invocation.encode graph connection.generation
          | throwError "the native group arrow could not use its released method packet"
        let .ok decoded := ConstructionInvocation.decodeMethod route.family.entry.id.raw
            route.family.functor.id.raw packet
          | throwError "the method did not use its complete ConstructionInvocation"
        unless decoded.parameters.size == 1 &&
            (decoded.receiver.getObjValAs? String "ctor").toOption == some "arrow" do
          throwError "the group method lost its final functor or complete Arrow descriptor"
        let roots : Array (Array InputPathStep × ValueBinding) := #[
          (#[.field "receiver", .field "args", .index 0], s3),
          (#[.field "receiver", .field "args", .index 1], second),
          (#[.field "receiver", .field "args", .index 2, .field "args", .index 0], s3),
          (#[.field "receiver", .field "args", .index 2, .field "args", .index 1], second)]
        for (path, original) in roots do
          let some actual := encoded.inputs.find? (·.path == path)
            | throwError "the method packet lost an exact native endpoint/parameter position"
          unless sameInput original actual.binding do
            throwError "method framing replaced an actual endpoint by equal source data"
        let some root := encoded.inputs.find? (·.path == #[.field "receiver"])
          | throwError "the complete Arrow packet lost its actual whole input authority"
        unless sameExactInput root.binding invocation.receiver do
          throwError "the public Arrow view fabricated a replacement input root"
        let identity : DispatchIdentity := {
          manifestDigest := "method-input-scope-control"
          profileDigest := "no-mathematical-provider"
          registration := {
            operation := route.family.entry.id.raw
            input := "cat.arrows_groups"
            backend := "scope-control" } }
        let .ok reservation ← transaction.reserve request.occurrence identity connection
            invocation.dependencies
          | throwError "the method scope lost its original inputs"
        let scope ← RequestScope.issue session.kernel.ledger reservation graph encoded.slots encoded.inputs #[]
        try
          for (path, original) in roots do
            let actual ← scope.resolveMany reservation graph scope.wireId #[.input path]
            let #[actual] := actual | throwError "the original method input path did not resolve"
            unless sameInput original actual do
              throwError "the method scope changed a positioned declaration parameter"
          let childPacket : ConstructionInvocation := { decoded with
            receiver := inputRef #[.field "receiver"] }
          let child := Json.mkObj [("op", toJson route.family.entry.id.raw),
            ("input", toJson "cat.arrows_groups"), ("args", childPacket.encode)]
          let (_, nested) ← captureMethod session.kernel transaction fun evaluate =>
            session.kernel.child evaluate request transaction reservation scope child
          unless nested.family.route.refs == route.family.route.refs &&
              nested.family.entry.id == route.family.entry.id &&
              sameExactInput nested.receiver invocation.receiver do
            throwError "the named method child changed its complete source family or actual receiver"
          failureAt .malformed do
            discard <| session.kernel.child (evaluate session.kernel) request transaction reservation
              scope (Json.mkObj [("op", toJson route.family.entry.id.raw),
                ("input", toJson "cat.arrows_groups"), ("args", Json.mkObj [
                  ("parameters", .arr #[]), ("prepared_role", toJson ""),
                  ("arguments", .arr #[inputRef #[.field "receiver"]])])])
          failureAt .malformed do
            discard <| session.kernel.child (evaluate session.kernel) request transaction reservation
              scope (Json.mkObj [("op", toJson route.family.entry.id.raw),
                ("input", toJson "cat.arrows_groups"),
                ("args", ({ childPacket with parameters := #[] } : ConstructionInvocation).encode)])
        finally scope.retire
      finally
        discard <| transaction.abort
        session.kernel.ledger.owners.close connection.generation

      -- The rank functor's explicit ring parameter is the actual selected RingCat value.
      -- These independent equal source definitions must retain distinct parameter nodes.
      for text in #["let Qfirst := ℚ in CommutativeRings", "let Qsecond := ℚ in CommutativeRings",
          "let Rfirst := view Qfirst along «fun.commutative_rings.ring»()",
          "let Rsecond := view Qsecond along «fun.commutative_rings.ring»()",
          "let Mfirst := RegularModule(Rfirst)", "let Msecond := RegularModule(Rsecond)"] do
        session ← define session text
      let firstRing ← value session `Rfirst
      let secondRing ← value session `Rsecond
      unless firstRing.value != secondRing.value do
        throwError "the independent ring declarations lost their distinct actual nodes"
      for (text, ring, moduleName) in #[
          ("Mfirst.rank()", firstRing, `Mfirst), ("Msecond.rank()", secondRing, `Msecond)] do
        let term ← readTerm session text
        let transaction ← CellTransaction.begin session.kernel.ledger
        try
          let (request, route) ← prepare session transaction term
          unless route.family.entry.id.raw == "meth.rank" && route.family.route.refs.isEmpty do
            throwError "the rank fixture changed its original owner method"
          let selected ← (← select route #["obj.modules.regular"]).materialize session.kernel
            (evaluate session.kernel) request transaction
          let invocation ← selected.invocation session.kernel (evaluate session.kernel) request transaction
          let #[#[parameter]] := invocation.parameters
            | throwError "the complete rank declaration lost its explicit ring parameter"
          unless sameInput ring parameter && sameInput (← value session moduleName) invocation.receiver do
            throwError "rank framing changed an actual parameter or introduced a synthetic Core input"
          if moduleName == `Mfirst then
            let connection ← session.kernel.ledger.owners.spawn { cmd := "/bin/cat" }
            try
              let graph ← transaction.view
              let .ok (encoded, _) := invocation.encode graph connection.generation
                | throwError "the rank invocation lost its complete encoded inputs"
              let identity : DispatchIdentity := {
                manifestDigest := "method-rank-child-control"
                profileDigest := "no-mathematical-provider"
                registration := {
                  operation := route.family.entry.id.raw
                  input := "obj.modules.regular"
                  backend := "scope-control" } }
              let .ok reservation ← transaction.reserve request.occurrence identity connection
                  (invocation.dependencies.push secondRing)
                | throwError "the rank child lost its original input authority"
              let scope ← RequestScope.issue session.kernel.ledger reservation graph
                (encoded.slots.push secondRing) encoded.inputs #[]
              try
                let parameterPath := #[InputPathStep.field "args", .index 0, .field "args", .index 0]
                let packet : ConstructionInvocation := {
                  construction := route.family.entry.id.raw,
                  parameters := #[routedActionDescriptor (.functor route.family.functor.id)
                    #[inputRef parameterPath]], receiver := inputRef #[.field "receiver"] }
                let child := fun packet => Json.mkObj [("op", toJson route.family.entry.id.raw),
                  ("input", toJson "obj.modules.regular"), ("args", packet)]
                let (childRequest, childRoute) ← captureMethod session.kernel transaction fun evaluate =>
                  session.kernel.child evaluate request transaction reservation scope (child packet.encode)
                let chosen ← (← select childRoute #["obj.modules.regular"]).materialize session.kernel
                  (evaluate session.kernel) childRequest transaction
                let nested ← chosen.invocation session.kernel (evaluate session.kernel)
                  childRequest transaction
                let #[#[nestedRing]] := nested.parameters
                  | throwError "the named rank child lost its original ring input"
                unless sameInput ring nestedRing &&
                    sameExactInput nested.receiver invocation.receiver do
                  throwError "the named rank child replaced an actual input by equal source data"
                let changed := { packet with parameters := #[
                  routedActionDescriptor (.functor route.family.functor.id)
                    #[(ScopedReference.scope encoded.slots.size).encode]] }
                failureAt .malformed do
                  discard <| session.kernel.child (evaluate session.kernel) request transaction
                    reservation scope (child changed.encode)
              finally scope.retire
            finally session.kernel.ledger.owners.close connection.generation
        finally discard <| transaction.abort

      -- A category input need not have its own source-session name. The original receiver's
      -- exact descriptor slot is its authority; evaluating the same closed ring again would
      -- create a different occurrence and is not parameter recovery.
      session ← define session
        "let Mclosed := RegularModule(view (ℚ in CommutativeRings) along «fun.commutative_rings.ring»())"
      let moduleValue ← value session `Mclosed
      let term ← readTerm session "Mclosed.rank()"
      let transaction ← CellTransaction.begin session.kernel.ledger
      try
        let graph ← transaction.view
        let some node := graph.find moduleValue.value
          | throwError "the closed-parameter module is outside its producing graph"
        let .container packet := node.payload.data
          | throwError "the native RegularModule source lost its original descriptor parameters"
        let #[ringSlot] := packet.slots.filter (·.path == #[.field "args", .index 0])
          | throwError "the native RegularModule descriptor lost its original ring slot"
        unless ringSlot.binding.value != firstRing.value do
          throwError "independent equal ring occurrences were merged before method preparation"
        let (request, route) ← prepare session transaction term
        let selected ← (← select route #["obj.modules.regular"]).materialize session.kernel
          (evaluate session.kernel) request transaction
        let invocation ← selected.invocation session.kernel (evaluate session.kernel) request transaction
        let #[#[parameter]] := invocation.parameters
          | throwError "the closed-parameter rank call lost its full declared functor"
        unless sameInput ringSlot.binding parameter && sameInput moduleValue invocation.receiver do
          throwError "the rank call reconstructed its unbound category parameter from a source term"
      finally discard <| transaction.abort
      -- A morphism method keeps its native Arrow wrapper and the hom producer's exact
      -- category inputs. Forgetting commutativity is a complete input-derived record view.
      for text in #[
          "let firstScalar := ℚ in CommutativeRings",
          "let secondScalar := ℚ in CommutativeRings",
          "let firstRow := [1, 0] in RectangularMatrices(1, 2, firstScalar)",
          "let secondRow := [1, 0] in RectangularMatrices(1, 2, secondScalar)",
          "let firstProjection := row_linear_map(2, firstScalar, firstRow)",
          "let secondProjection := row_linear_map(2, secondScalar, secondRow)"] do
        session ← define session text
      let firstScalar ← value session `firstScalar
      let secondScalar ← value session `secondScalar
      unless firstScalar.value != secondScalar.value do
        throwError "the distinct equal scalar declarations lost their actual occurrences"
      let transaction ← CellTransaction.begin session.kernel.ledger
      try
        let mut prepared := #[]
        for (text, original, projectionName) in #[
            ("firstProjection.ker()", firstScalar, `firstProjection),
            ("secondProjection.ker()", secondScalar, `secondProjection)] do
          let term ← readTerm session text
          let (request, route) ← prepare session transaction term
          unless route.family.entry.id.raw == "meth.arrow_ker" && route.family.route.refs.isEmpty do
            throwError "the original module-arrow method changed its selected source route"
          -- The existing hom is selected through its actual Arrow before its producer slots
          -- are read. Publication retains the stored node and its complete baseline chain.
          do
            let graph ← transaction.view
            let .ok (some (stored, remaining)) :=
                graph.projectionFrontier route.receiver #[``CategoryTheory.Comma.hom]
              | throwError "the method lost its original stored Arrow hom"
            let .ok (some published) :=
                graph.projected? route.receiver #[``CategoryTheory.Comma.hom]
              | throwError "the method hom lost its prepared original projection"
            unless remaining.isEmpty && sameInput (← value session projectionName) stored &&
                sameExactInput stored published do
              throwError "the method hom projection changed its original input or baseline"
          let parameter ← withSourceScope request fun context bound => do
            let some action := route.actions.back?
              | throwError "the module-arrow method lost its final native action"
            let #[(_, source)] ← routedActionParameters (.functor route.family.functor.id)
                (← action.inContext context)
              | throwError "the module-arrow method lost its original ring parameter"
            session.kernel.run transaction context bound source
          let graph ← transaction.view
          let some node := graph.find parameter.value
            | throwError "the native ring view is outside its producing graph"
          let some application := node.origin.application
            | throwError "the native ring view lost its certified original application"
          let #[some actual] := application.arguments
            | throwError "the native ring view changed its original scalar input position"
          unless sameInput original actual do
            throwError "the native ring view reconstructed an equal scalar occurrence"
          prepared := prepared.push (request, route, parameter)
        let #[(request, route, original), (_, _, other)] := prepared
          | throwError "the original scalar controls lost a complete method preparation"
        withSourceScope request fun context bound => do
          let some action := route.actions.back?
            | throwError "the original method lost its parameter source"
          let #[(_, source)] ← routedActionParameters (.functor route.family.functor.id)
              (← action.inContext context)
            | throwError "the original method lost its single native category parameter"
          -- The native Ring instance is a projection hidden by its original instance
          -- wrapper. Its retained parent remains the first scalar even when another
          -- independently supplied scalar has definitionally equal native fields.
          do
            let nativeSource ← sourceDomain source
            unless nativeSource.getAppFn.isConstOf ``RingCat.of do
              throwError "the native category view lost its original RingCat.of source"
            let #[_, structureSource] := nativeSource.getAppArgs
              | throwError "the native ring view lost its original structure argument"
            let graph ← transaction.view
            let path := #[``CommRingCat.commRing, ``CommRing.toRing]
            let .ok (some originalStructure) := graph.projectedAccess? firstScalar path
              | throwError "the first scalar lost its published native ring access"
            let .ok (some otherStructure) := graph.projectedAccess? secondScalar path
              | throwError "the second scalar lost its published native ring access"
            request.environment.checkDeclaredInput context graph (← session.kernel.marks.get)
              structureSource originalStructure
            let changedFailure : Option Exception ← try
              request.environment.checkDeclaredInput context graph (← session.kernel.marks.get)
                structureSource otherStructure
              pure none
            catch error => pure (some error)
            let some changedFailure := changedFailure
              | throwError "an equal scalar satisfied another scalar's wrapped native field"
            unless changedFailure.toMessageData.hasTag
                (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do
              throw changedFailure
          let evaluate := session.kernel.run transaction context bound
          let supplied ← markValue session.kernel.marks original source
          let #[retained] ← request.environment.methodParameters context transaction
              session.kernel.marks session.kernel.ledger.allocate route.family #[supplied]
              route.receiver evaluate
            | throwError "the retained category parameter changed its original arity"
          unless sameExactInput original (← evaluate retained) do
            throwError "rechecking a native category view replaced its original occurrence"
          let changed ← markValue session.kernel.marks other source
          let failure : Option Exception ← try
            discard <| request.environment.methodParameters context transaction
              session.kernel.marks session.kernel.ledger.allocate route.family #[changed]
              route.receiver evaluate
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "a separately produced equal scalar satisfied the original category input"
          let message ← failure.toMessageData.toString
          unless message.endsWith "the input result changed its original selected occurrence" ||
              failure.toMessageData.hasTag (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do
            throw failure
      finally discard <| transaction.abort
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "the source/packet controls dispatched a mathematical provider"
    finally session.close
  finally setEnv environment

end CasRuntime.RoutedMethodTests
