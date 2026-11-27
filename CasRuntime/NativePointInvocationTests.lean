module

import CasRuntime.Kernel
import CasRuntime.Point
import CasCompiler.SourceNumeral
import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Modules.Operations
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.Point
meta import CasCompiler.SourceNumeral
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Modules.Operations
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups

namespace CasRuntime.NativePointInvocationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def failAt (stratum : Stratum) (action : MetaM Unit) : MetaM Unit := do
  let failure : Option Exception ← try
    action
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "the negative named-point control was accepted"
  unless CasCatalogue.Exception.stratum? failure == some stratum do throw failure

private def prepare (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (callable point : ValueBinding) (pointSource : Expr)
    (bound : Std.HashMap BindingId ValueBinding := {})
    (selections : SourceSelectionScope Expr := {}) :
    MetaM (PreparedRequest × PreparedPointInvocation) := do
  withBoundValue kernel.ledger.owners.identities context bound pointSource point fun context bound pointSource => do
    let graph ← transaction.view
    let .ok code := graph.callable callable
      | throwError "the named point callable is outside its actual graph"
    let some node := graph.find code.value
      | throwError "the named point callable lost its original code"
    let .closure program _ := node.payload.data
      | throwError "the named point callable is not its retained native source"
    let some (.family family path) := (← kernel.codes.get)[program]?
      | throwError "the named point callable was replaced by a source computation"
    let .ok argument := RuntimeArgument.ofValue graph 0 point
      | throwError "the named point operand is outside its actual graph"
    let mut parameters := #[]
    for binding in context.bindings do
      if let some value := bound[binding.id]? then
        parameters := parameters.push (← IO.ofExcept <|
          (RuntimeParameter.ofValue graph binding.id value).mapError IO.userError)
    let request ← PreparedRequest.forApplication kernel.ledger.owners.identities program
      (← kernel.ledger.allocate) context callable #[← context.close pointSource] #[argument]
      parameters (some graph) (selections := selections)
    let evaluate : SourceEvaluation := fun cell _ current bound selections source =>
      kernel.run cell current bound source (selections := selections)
    let some invocation ← PreparedPointInvocation.prepare? kernel evaluate request family path transaction
      | throwError "the original named point action did not prepare its published packet"
    return (request, invocation)



run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let connection ← owners.spawn { cmd := "/bin/cat" }
    try
      for declaration in #[
          ``CasCatalogue.Algebra.PolynomialPresentations.firstConstants,
          ``CasCatalogue.Algebra.PolynomialPresentations.secondConstants] do
        let #[entry] := (← semanticState).morphisms.filter (·.declaration == declaration)
          | throwError "an original F9 constants map is not uniquely registered"
        let family ← PointFamily.forEntry entry
        let readInputs : SourceReadM (Expr × Expr × NativeSourcePointOrigin) := do
          let rawArrow := mkConst declaration
          let arrowSource ← SourceReadM.select (← family.selected rawArrow.constLevels! #[] rawArrow)
          let callableSource ← family.function arrowSource
          let (source, _) ← family.endpoints rawArrow
          let pointSource ← sourceNumeral (fun _ => pure none) 2 source
          let some selected ← SourceReadM.selection? pointSource
            | liftM (m := TermElabM) <| throwError "the source numeral lost its exact selected binder"
          let some pointOrigin := selected.pointOrigin
            | liftM (m := TermElabM) <| throwError "the source numeral lost its independently supplied point map"
          return (callableSource, pointSource, pointOrigin)
        readInputs.runK { identities := owners.identities, context, selections := {} }
            fun (callableSource, pointSource, pointOrigin) sourceScope => do
          let context := sourceScope.context
          let selections := sourceScope.selections
          let producer ← CellTransaction.begin kernel.ledger
          let callable ← kernel.run producer context {} callableSource (selections := selections)
          let point ← kernel.run producer context {} pointSource (selections := selections)
          let .ok _ ← producer.commit
            | throwError "the original named point inputs could not publish"
          let transaction ← CellTransaction.begin kernel.ledger
          try
            let (request, invocation) ← prepare kernel transaction context callable point pointSource (selections := selections)
            unless invocation.operation == entry.id.raw && invocation.parameters.isEmpty &&
                invocation.argument.value == point.value &&
                invocation.argument.associationIds == point.associationIds do
              throwError "the named point action changed its released identity or original argument"
            do
              unless invocation.preparation == request.roles.scope do
                throwError "the named point lost its original complete request preparation"
              let rejectPreparation (action : MetaM Unit) : MetaM Unit := do
                let failure : Option Exception ← try
                  action
                  pure none
                catch error => pure (some error)
                let some failure := failure
                  | throwError "a named point accepted a different request preparation"
                unless failure.toMessageData.hasTag (· == requestPreparationMismatchTag) do throw failure
              let otherPoint ← kernel.run transaction context {} pointSource (selections := selections)
              unless otherPoint.value != point.value do
                throwError "the named-point scope control merged separate equal operands"
              let graph ← transaction.view
              let rebuild := fun (occurrence : RuntimeId .occurrence) (value : ValueBinding) =>
                withBoundValue owners.identities context {} pointSource value fun context bound source => do
                  let .ok argument := RuntimeArgument.ofValue graph 0 value
                    | throwError "the named-point scope control lost its original operand"
                  let mut parameters := #[]
                  for binding in context.bindings do
                    if let some value := bound[binding.id]? then
                      parameters := parameters.push (← IO.ofExcept <|
                        (RuntimeParameter.ofValue graph binding.id value).mapError IO.userError)
                  PreparedRequest.forApplication owners.identities request.program occurrence context
                    callable #[← context.close source] #[argument] parameters (some graph)
                    (selections := selections)
              let otherRequest ← rebuild (← kernel.ledger.allocate) otherPoint
              let rebuilt ← rebuild request.occurrence point
              unless otherRequest.occurrence != request.occurrence &&
                  rebuilt.occurrence == request.occurrence && rebuilt.roles.scope != request.roles.scope do
                throwError "the named-point scope control lost its independent preparations"
              let .ok code := graph.callable callable
                | throwError "the named-point scope control lost its actual callable"
              let some node := graph.find code.value
                | throwError "the named-point scope control lost its retained code"
              let .closure program _ := node.payload.data
                | throwError "the named-point scope control has no family closure"
              let some (.family originalFamily fieldPath) := (← kernel.codes.get)[program]?
                | throwError "the named-point scope control lost its original family"
              let .primitive boundary levels := originalFamily.action
                | throwError "the named-point scope control changed its native family"
              unless originalFamily.application.isNone && originalFamily.scope.isEmpty do
                throwError "the named-point scope control unexpectedly has declaration parameters"
              let otherFamily ← PreparedRequest.forBoundary owners.identities originalFamily.program
                originalFamily.occurrence boundary levels context #[] #[] #[] #[] (selections := selections)
              unless otherFamily.occurrence == originalFamily.occurrence &&
                  otherFamily.roles.scope != originalFamily.roles.scope do
                throwError "the named-point scope control reused its original family preparation"
              let beforeRejection ← transaction.view
              let evaluate : SourceEvaluation := fun cell _ current bound selections expression =>
                kernel.run cell current bound expression (selections := selections)
              rejectPreparation do
                discard <| PreparedPointInvocation.prepare? kernel evaluate request otherFamily
                  fieldPath transaction
              let registration : Registration := {
                operation := entry.id.raw, input := entry.id.raw, backend := "scope-control" }
              for wrong in #[otherRequest, rebuilt] do
                rejectPreparation do
                  discard <| kernel.invokePoint evaluate wrong transaction registration invocation
                unless (← kernel.ledger.pendingFor wrong.occurrence transaction.id).isNone do
                  throwError "a rejected named-point preparation reserved a dispatch"
              unless (← transaction.view).sameRevision beforeRejection &&
                  (← kernel.dispatches.get).isEmpty do
                throwError "a rejected named-point preparation published or dispatched"
            let graph ← transaction.view
            withBindingContext graph context {} invocation.domain fun context _ => do
              context.withOriginalSources #[← invocation.domain.selectedSource context, pointOrigin.domain]
                  fun native => do
                unless ← isDefEq native[0]! native[1]! do
                  throwError "the point packet guessed a domain instead of retaining its native source"
            let .ok (encoded, packet) := invocation.encode graph connection.generation
              | throwError "the complete original named point could not encode"
            let .ok decoded := PointInvocation.decode packet
              | throwError "the named point did not use the public seven-field envelope"
            unless decoded.operation == entry.id.raw && decoded.parameters.isEmpty &&
                (decoded.arrow.getObjValAs? String "ctor").toOption == some entry.id.raw &&
                (decoded.source.getObjValAs? String "ctor").toOption == some "obj.sets.integers_mod" do
              throwError "the point packet changed its released arrow or authored source alias"
            for root in invocation.roots do
              let some retained := encoded.inputs.find? (·.path == root.path)
                | throwError "the point packet lost an original root authority"
              unless retained.binding.value == root.binding.value &&
                  retained.binding.associationIds == root.binding.associationIds do
                throwError "the point packet replaced an input by a descriptor value node"
            let identity : DispatchIdentity := {
              manifestDigest := "native-point-scope-control"
              profileDigest := "no-providers"
              registration := {
                operation := entry.id.raw
                input := entry.id.raw
                backend := "scope-control" } }
            let .ok reservation ← transaction.reserve request.occurrence identity connection
                invocation.dependencies
              | throwError "the original named point scope could not reserve its actual inputs"
            let scope ← RequestScope.issue kernel.ledger reservation graph encoded.slots encoded.inputs #[]
            try
              let arrowReference := ScopedReference.input #[.field "args", .index 2]
              let #[retainedArrow] ← scope.resolveMany reservation graph scope.wireId #[arrowReference]
                | throwError "the named descriptor lost its original arrow scope authority"
              unless retainedArrow.value == invocation.arrow.value &&
                  retainedArrow.associationIds == invocation.arrow.associationIds do
                throwError "an arrow-root reference resolved a new descriptor node"
              let reference := fun index =>
                (ScopedReference.input #[.field "args", .index index]).encode
              let child : PointInvocation := {
                operation := entry.id.raw, parameters := #[], arrow := reference 2,
                domain := reference 3, source := reference 4,
                target := reference 5, argument := reference 6 }
              let observed ← IO.mkRef false
              let evaluate : SourceEvaluation := fun cell _ current bound selections source => do
                let .app _ argument := source.consumeMData
                  | return ← kernel.run cell current bound source (selections := selections)
                let some selected := selections.findAt? current argument.getAppFn
                  | return ← kernel.run cell current bound source (selections := selections)
                let selected ← selected.specialize argument.getAppArgs
                let some (.named original actual) := selected.pointRequest
                  | return ← kernel.run cell current bound source (selections := selections)
                unless (SelectedApplicationFamily.application family).exactlyMatches
                    (.application original) do
                  throwError "the named child changed its original selected point family"
                for term in #[actual.domain, actual.source, actual.target, actual.point],
                    expected in #[invocation.domain, invocation.source, invocation.target, point] do
                  let .fvar localId := term.consumeMData
                    | throwError "the named child replaced a supplied original input"
                  let some binding := current.bindings.find? (·.expression.fvarId! == localId)
                    | throwError "the named child has no actual typed input binder"
                  let some value := bound[binding.id]?
                    | throwError "the named child input is outside its retained table"
                  unless value.value == expected.value &&
                      value.associationIds == expected.associationIds do
                    throwError "the named child substituted another equal source input"
                observed.set true
                kernel.run cell current bound source (selections := selections)
              failAt .noImplementation do
                discard <| kernel.child evaluate request transaction reservation scope
                  (Json.mkObj [("op", toJson entry.id.raw), ("args", child.encode)])
              unless ← observed.get do
                throwError "the named child bypassed common typed source lowering"
            finally scope.retire
          finally discard <| transaction.abort
      unless (← kernel.dispatches.get).isEmpty do
        throwError "the named point controls dispatched a mathematical provider"
    finally
      kernel.close
      owners.close connection.generation
  finally setEnv original



run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let #[groupEntry] := (← semanticState).objects.filter
      (·.declaration == ``CasCatalogue.Algebra.FiniteGroups.symmetric)
      | throwError "the original symmetric-group source has no unique declared row"
    let #[groupCategory] := (← semanticState).categories.filter (·.id == groupEntry.category)
      | throwError "the original symmetric group lost its complete registered category"
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let connection ← owners.spawn { cmd := "/bin/cat" }
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let readGroup : SourceReadM Expr := do
          return (← registeredExpressions (.inl groupEntry) groupCategory
            (fun function _ => pure (mkAppN function #[mkNatLit 3]))).2
        readGroup.runK { identities := owners.identities, context, selections := {} } fun groupSource sourceScope => do
          let context := sourceScope.context
          let selections := sourceScope.selections
          let group ← kernel.run transaction context {} groupSource (selections := selections)
          controlAt MetaM fun run =>
            withBoundValue owners.identities context {} groupSource group fun context bound selected => run do
              let readArrows : SourceReadM (Array Expr) := do
                let mut sources := #[]
                for (declaration, arguments) in #[
                    (``CasCatalogue.Algebra.FiniteGroups.identity, #[selected]),
                    (``CasCatalogue.Algebra.FiniteGroups.trivial, #[selected, selected])] do
                  let #[entry] := (← semanticState).morphisms.filter (·.declaration == declaration)
                    | liftM (m := TermElabM) <|
                        throwError "the original named-arrow source has no unique declared row"
                  let family ← PointFamily.forEntry entry
                  let arrow ← mkAppM declaration arguments
                  sources := sources.push (← SourceReadM.select
                    (← family.selected arrow.getAppFn.constLevels! arrow.getAppArgs arrow))
                return sources
              readArrows.runK { identities := owners.identities, context, selections } fun sources sourceScope => do
                let context := sourceScope.context
                let selections := sourceScope.selections
                let #[identitySource, trivialSource] := sources
                  | throwError "the original named-arrow controls lost their complete source table"
                unless ← isDefEq (← inferType identitySource) (← inferType trivialSource) do
                  throwError "the family-identity control did not retain equal declared endpoints"
                let identity ← kernel.run transaction context bound identitySource
                  (selections := selections)
                let trivial ← kernel.run transaction context bound trivialSource
                  (selections := selections)
                let graph ← transaction.view
                let codes ← kernel.codes.get
                let some first ← InputDescriptorView.namedMorphism? graph codes identity
                  | throwError "the original identity arrow has no checked named descriptor"
                let some second ← InputDescriptorView.namedMorphism? graph codes trivial
                  | throwError "the original trivial arrow has no checked named descriptor"
                let some firstFamily := first.family
                  | throwError "the identity arrow lost its original family"
                let some secondFamily := second.family
                  | throwError "the trivial arrow lost its original family"
                unless firstFamily.reference != secondFamily.reference &&
                    first.binding.value == identity.value && second.binding.value == trivial.value &&
                    second.parameters.size == 2 do
                  throwError "equal endpoints merged distinct named-arrow sources"
                let some (.morphism firstId) := firstFamily.reference
                  | throwError "the identity arrow lost its released morphism address"
                failAt .malformed do
                  discard <| InputDescriptorView.requireMorphism graph codes trivial firstId
                for value in second.parameters do
                  unless value.value == group.value && value.associationIds == group.associationIds do
                    throwError "the named arrow reconstructed an equal parameter instead of its original input"
                let views ← InputDescriptorView.collect graph codes #[trivial]
                let root : InputPosition := { path := #[.field "arrow"], binding := trivial }
                let .ok encoded := graph.encodeInputs connection.generation #[root] views
                  | throwError "the parameterized named arrow could not encode"
                for index in [:2] do
                  let path := #[.field "arrow", .field "args", .index index]
                  let some retained := encoded.inputs.find? (·.path == path)
                    | throwError "the named arrow lost a complete parameter root"
                  unless retained.binding.value == group.value &&
                      retained.binding.associationIds == group.associationIds do
                    throwError "a named arrow parameter root changed its original binding"
                unless (← kernel.dispatches.get).isEmpty do
                  throwError "the named arrow codec control invoked a mathematical provider"
      finally discard <| transaction.abort
    finally
      kernel.close
      owners.close connection.generation
  finally setEnv original




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let #[entry] := (← semanticState).morphisms.filter (·.declaration ==
        ``CasCatalogue.Algebra.FiniteGroups.identity)
      | throwError "the existing group identity family is not uniquely registered"
    let #[groupEntry] := (← semanticState).objects.filter
      (·.declaration == ``CasCatalogue.Algebra.FiniteGroups.cyclic)
      | throwError "the original cyclic-group source has no unique declared row"
    let #[groupCategory] := (← semanticState).categories.filter (·.id == groupEntry.category)
      | throwError "the original cyclic group lost its complete registered category"
    let family ← PointFamily.forEntry entry
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let parameter ← kernel.run transaction context {} (mkNatLit 2)
        controlAt MetaM fun run =>
          withBoundValue owners.identities context {} (mkNatLit 2) parameter fun context bound selectedParameter => run do
            let readGroups : SourceReadM (Expr × Expr) := do
              let (_, first) ← registeredExpressions (.inl groupEntry) groupCategory
                (fun function _ => pure (mkAppN function #[selectedParameter]))
              let (_, other) ← registeredExpressions (.inl groupEntry) groupCategory
                (fun function _ => pure (mkAppN function #[selectedParameter]))
              return (first, other)
            readGroups.runK { identities := owners.identities, context, selections := {} } fun (firstSource, otherSource) sourceScope => do
              let context := sourceScope.context
              let selections := sourceScope.selections
              let first ← kernel.run transaction context bound firstSource (selections := selections)
              let other ← kernel.run transaction context bound otherSource (selections := selections)
              unless first.value != other.value do
                throwError "the endpoint control did not retain two distinct supplied objects"
              controlAt MetaM fun run =>
                withBoundValue owners.identities context bound firstSource first fun context bound firstSource => run do
                  controlAt MetaM fun run =>
                    withBoundValue owners.identities context bound otherSource other fun context bound otherSource => run do
                      let nativeArrow ← mkAppM entry.declaration #[firstSource]
                      let selectedArrow ← family.selected nativeArrow.getAppFn.constLevels!
                        nativeArrow.getAppArgs nativeArrow
                      selections.withBinding owners.identities context selectedArrow fun context selections arrowSource => do
                        let arrow ← kernel.run transaction context bound arrowSource
                          (selections := selections)
                        controlAt MetaM fun run =>
                          withBoundValue owners.identities context bound arrowSource arrow fun context bound arrowSource => run do
                            let callable ← kernel.run transaction context bound
                              (← family.function arrowSource) (selections := selections)
                            let carrier ← mkAppM ``CasCatalogue.Foundation.Objects.integersMod #[selectedParameter]
                            let readPoint : SourceReadM (Expr × SourceSelection Expr) := do
                              let pointSource ← sourceNumeral (fun _ => pure none) 0 carrier
                              let some selection ← SourceReadM.selection? pointSource
                                | liftM (m := TermElabM) <| throwError "the endpoint control lost its original point binder"
                              return (pointSource, { selection with value := pointSource })
                            readPoint.runK { identities := owners.identities, context, selections }
                                fun (pointSource, pointSelection) sourceScope => do
                              let context := sourceScope.context
                              let selections := sourceScope.selections
                              let some origin := pointSelection.pointOrigin
                                | throwError "the endpoint control lost its original numeral point map"
                              let point ← kernel.run transaction context bound pointSource
                                (selections := selections)
                              let exact ← family.withRequest arrowSource origin.domain firstSource firstSource
                                pointSelection (context := some context)
                              selections.withBinding owners.identities context exact fun context selections exact => do
                                let (_, invocation) ← prepare kernel transaction context callable point exact bound
                                  (selections := selections)
                                unless invocation.source.value == first.value && invocation.target.value == first.value &&
                                    invocation.source.associationIds == first.associationIds &&
                                    invocation.target.associationIds == first.associationIds do
                                  throwError "the named point packet changed its original chosen endpoint"
                                let changed ← family.withRequest arrowSource origin.domain otherSource firstSource
                                  pointSelection (context := some context)
                                selections.withBinding owners.identities context changed fun context selections changed => do
                                  let failure : Option Exception ← try
                                    discard <| prepare kernel transaction context callable point changed bound
                                      (selections := selections)
                                    pure none
                                  catch error => pure (some error)
                                  let some failure := failure
                                    | throwError "the named point action accepted a different equal endpoint node"
                                  unless failure.toMessageData.hasTag
                                      (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do
                                    throw failure
                                  unless (← kernel.dispatches.get).isEmpty do
                                    throwError "the original endpoint control dispatched a mathematical provider"
      finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original


run_cmd Lean.Elab.Command.liftTermElabM do
  let packet : PointInvocation := {
    operation := "mor.groups.identity"
    parameters := #[]
    arrow := .null
    domain := .null
    source := .null
    target := .null
    argument := .null
  }
  let .ok fields := (packet.encode.getObjVal? "args").bind (·.getArr?)
    | throwError "the public point encoder lost its ordered input packet"
  for fields in #[fields.pop, fields.push .null, fields.set! 0 (.str "")] do
    if (PointInvocation.decode
        (Json.mkObj [("ctor", "apply"), ("args", .arr fields)])).isOk then
      throwError "the point decoder accepted an incomplete or unidentified request"



run_cmd Lean.Elab.Command.liftTermElabM do
  let nativeTerm : String → TermElabM Term := fun text => do
    let .ok source := Parser.runParserCategory (← getEnv) `term text
      | throwError "the native nullary input did not parse"
    return ⟨source⟩
  let sourceTerm : String → TermElabM (TSyntax `cas_term) := fun text => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the public nullary source did not parse"
    return ⟨source⟩
  let originalEnvironment ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let connection ← owners.spawn { cmd := "/bin/cat" }
    try
      let empty ← SourceSession.empty owners.identities
      let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
      let ring ← session.term (← nativeTerm "R")
      let category ← session.namedCategory Syntax.missing "Modules" [.zero, .zero] #[ring]
      let session ← session.assume `raw (← nativeTerm "ModuleCat.{0} R")
      let raw ← session.term (← nativeTerm "raw")
      let session ← session.defineTerm `M
        (← raw.inCategory category.expression category.value)
      let point ← session.read (← sourceTerm "0 in M")
      point.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let selections ← point.selections.inContext context
        let program ← owners.identities.fresh .program
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let some ringEntry := session.context.entries.find? (·.userName == `R)
            | throwError "the nullary input lost its original ring declaration"
          let some moduleEntry := session.context.entries.find? (·.userName == `M)
            | throwError "the nullary input lost its original module declaration"
          let some ringSource := bindings.find? (·.id == ringEntry.id)
            | throwError "the nullary input lost its original ring binding"
          let some moduleSource := bindings.find? (·.id == moduleEntry.id)
            | throwError "the nullary input lost its original module binding"
          let ringRole ← SourceLayout.ofTerm (← context.close ringSource.expression)
          let ringRole := { ringRole with
            selections := point.selections
            selectionBinding := if selections.contains ringSource.id then some ringSource.id else none }
          let moduleRole ← SourceLayout.ofTerm (← context.close moduleSource.expression)
          let moduleRole := { moduleRole with
            selections := point.selections
            selectionBinding := if selections.contains moduleSource.id then some moduleSource.id else none }
          let ring ← transaction.stage
            { program, occurrence := ← kernel.ledger.allocate,
              role := ringRole,
              parameters := Array.replicate bindings.size none }
            (.ownedExport connection "original nullary scalar" #[])
          let .ok parameter := RuntimeParameter.ofValue
              (← transaction.view) ringSource.id ring
            | throwError "the nullary runtime scalar is outside its original graph"
          let environment ← RuntimeEnvironment.capture owners.identities.worker
            context #[parameter] (selections := selections)
          let moduleValue ← transaction.stage
            (← environment.origin program (← kernel.ledger.allocate)
              moduleRole)
            (.ownedExport connection "original nullary module" #[ring])
          let observed ← IO.mkRef false
          let observe : PFunctor.Handler.Stateful MetaM CellTransaction
              OperationalSignature := fun request _ => do
            unless request.reference == some (.operation ⟨"op.modules.zero"⟩) do
              throwError "the public nullary value emitted another demand before its operation"
            let some application := request.origin.application
              | throwError "the nullary operation demand lost its native argument telescope"
            let #[some actualRing, some actualModule] := application.arguments
              | throwError "the nullary operation changed its complete original argument slots"
            unless actualRing.value == ring.value &&
                actualRing.associationIds == ring.associationIds do
              throwError "the nullary operation changed its original scalar reference"
            unless actualModule.value == moduleValue.value &&
                moduleValue.associationIds.toList.isPrefixOf actualModule.associationIds.toList do
              throwError "the nullary operation changed its original module reference"


            let some identityCall := actualModule.applications.back?
              | throwError "the nullary module lost its declared identity application"
            unless actualModule.associationIds ==
                moduleValue.associationIds.push identityCall.association.id &&
                identityCall.association.path.isEmpty && identityCall.access.isNone &&
                identityCall.callable.isSome do
              throwError "the nullary module acquired another consuming association"
            let #[some originalModule] := identityCall.arguments
              | throwError "the nullary identity application changed its original input slots"
            unless originalModule.value == moduleValue.value &&
                originalModule.associationIds == moduleValue.associationIds do
              throwError "the nullary identity application replaced its original module"
            let #[originalArgument] := identityCall.association.layout.arguments
              | throwError "the nullary identity family changed its declared argument telescope"
            let sourceArgument ← originalArgument.source.source.inContext context
            unless sourceArgument.consumeMData == moduleSource.expression do
              throwError "the nullary identity application changed its original source binding"
            let some scalarPosition :=
                identityCall.association.layout.result.source.context.entries.findIdx?
                  (·.id == ringSource.id)
              | throwError "the nullary identity application lost its original scalar context"
            let some originalRing := identityCall.applicationParameters[scalarPosition]?.bind id
              | throwError "the nullary identity application lost its actual scalar parameter"
            unless originalRing.value == ring.value &&
                originalRing.associationIds == ring.associationIds do
              throwError "the nullary identity application replaced its original scalar"
            let some selected ← identityCall.association.layout.inputProjectionAt #[]
              | throwError "the nullary identity family lost its original input selection"
            let .argument 0 := selected.target
              | throwError "the nullary identity family selected another source input"
            unless selected.path.isEmpty do
              throwError "the nullary identity family selected a module field"
            let bundle ← category.value.source.inContext context
            let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
            let structureValue ← mkAppM ``CategoryTheory.Bundled.str #[bundle]
            let identityFunctor ← mkAppOptM ``CategoryTheory.Functor.id
              #[some carrier, some structureValue]
            let identityAction ← mkProjection identityFunctor `obj
            let family ← identityCall.association.layout.resultTermFamily.inContext context
            unless (← isDefEq (← inferType family) (← inferType identityAction)) &&
                (← isDefEq family identityAction) do
              throwError "the nullary module association changed its whole native identity family"
            observed.set true
            throwError "observed the original nullary operation demand"
          let bound : Std.HashMap BindingId ValueBinding :=
            ({} : Std.HashMap BindingId ValueBinding)
              |>.insert ringSource.id ring |>.insert moduleSource.id moduleValue
          let failure : Option Exception ← try
              discard <| lowerTerm {
                ledger := kernel.ledger, transaction, codes := kernel.codes
                run := fun computation => Execute.run observe computation transaction }
                program context bound expression (selections := selections)
              pure none
            catch error => pure (some error)
          let some failure := failure
            | throwError "the reader computed a nullary operation without its published demand"
          unless (← observed.get) && (← failure.toMessageData.toString).startsWith
              "observed the original nullary operation demand" do throw failure
          unless (← kernel.dispatches.get).isEmpty do
            throwError "the nullary source control dispatched a mathematical provider"
        finally discard <| transaction.abort
    finally
      owners.close connection.generation
      kernel.close
  finally setEnv originalEnvironment

end CasRuntime.NativePointInvocationTests
