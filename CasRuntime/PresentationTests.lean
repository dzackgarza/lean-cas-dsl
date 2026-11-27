module

import CasRuntime.Kernel
import CasRuntime.Presentation
import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.Presentation
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients

namespace CasRuntime.PresentationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def prepare (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (callable point : ValueBinding) (pointSource : Expr)
    (selections : SourceSelectionScope Expr := {}) :
    MetaM (PreparedRequest × PreparedPresentationInvocation) := do
  withBoundValue kernel.ledger.owners.identities context {} pointSource point fun context bound pointSource => do
    let graph ← transaction.view
    let .ok code := graph.callable callable
      | throwError "the selected comparison has no retained native callable"
    let some node := graph.find code.value
      | throwError "the comparison callable is outside the actual graph"
    let .closure program _ := node.payload.data
      | throwError "the comparison source did not retain its original family"
    let some (.family family path) := (← kernel.codes.get)[program]?
      | throwError "the comparison callable was replaced by source evaluation"
    let .primitive (.presentation _) _ := family.action
      | throwError "the comparison lost its published native boundary"
    let .ok argument := RuntimeArgument.ofValue graph 0 point
      | throwError "the original comparison point is outside its graph"
    let mut parameters := #[]
    for binding in context.bindings do
      if let some value := bound[binding.id]? then
        parameters := parameters.push (← IO.ofExcept <|
          (RuntimeParameter.ofValue graph binding.id value).mapError IO.userError)
    let request ← PreparedRequest.forApplication kernel.ledger.owners.identities program
      (← kernel.ledger.allocate) context callable #[← context.close pointSource] #[argument] parameters
      (some graph) (selections := selections)
    return (request, ← PreparedPresentationInvocation.prepare request family path graph
      (← kernel.codes.get))

private def manifest (inputs : Array String) : MetaM Manifest := do
  let packet := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "unused-protocol-peer"),
      ("command", "/bin/false"), ("args", .arr #[])]]),
    ("registrations", .arr (inputs.map fun input => Json.mkObj [
      ("operation", "cmp.f9.translation"), ("input", toJson input),
      ("backend", "unused-protocol-peer")]))]
  IO.ofExcept <| (Manifest.parse packet).mapError IO.userError

private def failureAt (stratum : Stratum) (action : MetaM Unit) : MetaM Unit := do
  let failure : Option Exception ← try
    action
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "the negative presentation control was accepted"
  unless CasCatalogue.Exception.stratum? failure == some stratum do throw failure




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let some row := (← semanticState).presentations.find? (·.id.raw == "cmp.f9.translation")
      | throwError "the original F9 comparison is not registered"
    let family ← PresentationFamily.forEntry row
    let owners ← OwnerRegistry.new
    let empty ← SourceSession.empty owners.identities
    let .ok firstSyntax := Parser.runParserCategory (← getEnv) `cas_term "generator(F9x)"
      | throwError "the original first generator source did not parse"
    let .ok secondSyntax := Parser.runParserCategory (← getEnv) `cas_term "generator(F9y)"
      | throwError "the original second generator source did not parse"
    let firstTerm ← empty.read ⟨firstSyntax⟩
    let secondTerm ← empty.read ⟨secondSyntax⟩
    let inputs : SourceReadM (Expr × Expr × Expr × Expr) := do
      let iso ← SourceReadM.select (← family.selected (mkConst row.declaration))
      let forward ← family.function iso false
      let backward ← family.function iso true
      let firstPoint ← empty.readTerm firstTerm
      let secondPoint ← empty.readTerm secondTerm
      return (forward, backward, firstPoint, secondPoint)
    inputs.runK ⟨owners.identities, context, {}⟩ fun
        (forward, backward, firstPoint, secondPoint) scope => do
      let context := scope.context
      let selections := scope.selections
      let kernel ← Kernel.load owners none none 1000
      discard <| SessionSnapshot.initialize owners


      let connection ← owners.spawn { cmd := "/bin/cat" }
      try
        let producer ← CellTransaction.begin kernel.ledger
        let first ← kernel.run producer context {} forward (selections := selections)
        let second ← kernel.run producer context {} backward (selections := selections)
        let x ← kernel.run producer context {} firstPoint (selections := selections)
        let y ← kernel.run producer context {} secondPoint (selections := selections)
        unless (← kernel.dispatches.get).isEmpty do
          throwError "forming a presentation arrow or distinguished point dispatched computation"
        let .ok _ ← producer.commit
          | throwError "the original comparison sources could not be retained"
        for (inverse, callable, point, source) in #[
            (false, first, x, firstPoint), (true, second, y, secondPoint)] do
          let transaction ← CellTransaction.begin kernel.ledger
          try
            let (request, invocation) ← prepare kernel transaction context callable point source selections
            unless invocation.operation == row.id.raw && invocation.inverse == inverse &&
                invocation.parameters.isEmpty && invocation.argument.value == point.value &&
                invocation.argument.associationIds == point.associationIds do
              throwError "the comparison changed its original operation, direction or point binding"
            do
              unless invocation.preparation == request.roles.scope do
                throwError "the comparison lost its original complete request preparation"
              let rejectPreparation (action : MetaM Unit) : MetaM Unit := do
                let failure : Option Exception ← try
                  action
                  pure none
                catch error => pure (some error)
                let some failure := failure
                  | throwError "a presentation accepted a different request preparation"
                unless failure.toMessageData.hasTag (· == requestPreparationMismatchTag) do throw failure
              let otherPoint ← kernel.run transaction context {} source (selections := selections)
              unless otherPoint.value != point.value do
                throwError "the presentation scope control merged separate equal operands"
              let graph ← transaction.view
              let rebuild := fun (occurrence : RuntimeId .occurrence) (value : ValueBinding) =>
                withBoundValue owners.identities context {} source value fun context bound source => do
                  let .ok argument := RuntimeArgument.ofValue graph 0 value
                    | throwError "the presentation scope control lost its original operand"
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
                throwError "the presentation scope control lost its independent preparations"
              let .ok code := graph.callable callable
                | throwError "the comparison scope control lost its actual callable"
              let some node := graph.find code.value
                | throwError "the comparison scope control lost its retained code"
              let .closure program _ := node.payload.data
                | throwError "the comparison scope control has no family closure"
              let codes ← kernel.codes.get
              let some (.family originalFamily fieldPath) := codes[program]?
                | throwError "the comparison scope control lost its original family"
              let .primitive (.presentation original) levels := originalFamily.action
                | throwError "the comparison scope control changed its native family"
              unless (originalFamily.application.map (·.arguments.isEmpty)).getD true do
                throwError "the comparison scope control unexpectedly has declaration parameters"
              let (firstEnd, secondEnd) ← originalFamily.presentationEndpoints graph
              let .ok firstArgument := RuntimeArgument.ofValue graph 0 firstEnd
                | throwError "the comparison scope control lost its original first endpoint"
              let .ok secondArgument := RuntimeArgument.ofValue graph 1 secondEnd
                | throwError "the comparison scope control lost its original second endpoint"
              let otherFamily ← PreparedRequest.forPresentation owners.identities
                originalFamily.program originalFamily.occurrence original levels context #[] #[]
                #[firstEnd.role.source, secondEnd.role.source] #[firstArgument, secondArgument] #[]
                graph (selections := selections)
              unless otherFamily.roles.scope != originalFamily.roles.scope do
                throwError "the comparison scope control reused its original family preparation"
              let beforeRejection ← transaction.view
              rejectPreparation do
                discard <| PreparedPresentationInvocation.prepare request otherFamily fieldPath graph
                  codes
              let evaluate : SourceEvaluation := fun cell _ current bound selections expression =>
                kernel.run cell current bound expression (selections := selections)
              let registration : Registration := {
                operation := row.id.raw, input := row.id.raw, backend := "scope-control" }
              for wrong in #[otherRequest, rebuilt] do
                rejectPreparation do
                  discard <| kernel.invokePresentation evaluate wrong transaction registration invocation
                unless (← kernel.ledger.pendingFor wrong.occurrence transaction.id).isNone do
                  throwError "a rejected presentation preparation reserved a dispatch"
              unless (← transaction.view).sameRevision beforeRejection &&
                  (← kernel.dispatches.get).isEmpty do
                throwError "a rejected presentation preparation published or dispatched"
            let sourceId := if inverse then row.target.raw else row.source.raw
            let targetId := if inverse then row.source.raw else row.target.raw
            unless invocation.forms == #[row.id.raw, sourceId] do
              throwError "the comparison selected a target-endpoint form or lost its own request form"
            let graph ← transaction.view
            let .ok (encoded, packet) := invocation.encode graph connection.generation
              | throwError "the original comparison inputs could not encode"
            let .ok decoded := PresentationInvocation.decode packet
              | throwError "the comparison did not use its published five-field packet"
            unless decoded.inverse == inverse && decoded.parameters.isEmpty &&
                (decoded.source.getObjValAs? String "ctor").toOption == some sourceId &&
                (decoded.target.getObjValAs? String "ctor").toOption == some targetId do
              throwError "comparison encoding changed its complete oriented endpoints"
            let roots := invocation.roots
            unless roots.map (·.path) == #[
                #[.field "args", .index 2], #[.field "args", .index 3],
                #[.field "args", .index 4]] do
              throwError "comparison references were rooted in a dependentContext packet"
            for root in roots do
              let some actual := encoded.inputs.find? (·.path == root.path)
                | throwError "comparison encoding lost a complete original input position"
              unless actual.binding.value == root.binding.value &&
                  actual.binding.associationIds == root.binding.associationIds do
                throwError "comparison encoding replaced an endpoint or point by equal data"
            let (installed, rejected) ← admitManifest (← manifest #[sourceId, targetId])
            unless rejected.isEmpty && installed.registrations.size == 2 do
              throwError "the original two presentation endpoint registrations were rejected"
            let profileTarget := ProfileTarget.presentation row.id
            let defaultProfile ← RealizationProfile.prepare installed none
            unless (← selectLift defaultProfile installed profileTarget
                invocation.operation invocation.forms).input == sourceId do
              throwError "the opposite endpoint became an eligible comparison input"
            let (overlap, rejected) ← admitManifest (← manifest #[sourceId, row.id.raw])
            unless rejected.isEmpty do throwError "the complete presentation request form was rejected"
            failureAt .ambiguousRealization do
              discard <| selectLift defaultProfile overlap profileTarget invocation.operation invocation.forms
            let (empty, _) ← admitManifest (← manifest #[])
            failureAt .noImplementation do
              discard <| selectLift defaultProfile empty profileTarget invocation.operation invocation.forms

            let freeze := fun (installed : Manifest) (entries : Array Registration) =>
              RealizationProfile.prepare installed (some (Json.mkObj [
                ("format", "cas-realization-profile/1"), ("id", "presentation-control"),
                ("default", "all"), ("rules", .arr #[Json.mkObj [
                  ("target", Json.mkObj [("kind", "presentation"), ("id", toJson row.id.raw)]),
                  ("primitive_registrations", Json.mkObj [("mode", "only"),
                    ("entries", .arr (entries.map fun entry => Json.mkObj [
                      ("operation", toJson entry.operation), ("input", toJson entry.input),
                      ("backend", toJson entry.backend)]))]),
                  ("derivations", Json.mkObj [("mode", "only"), ("ids", .arr #[])])]])]))
            let excluded ← freeze overlap #[]
            failureAt .noImplementation do
              discard <| selectLift excluded overlap profileTarget invocation.operation invocation.forms
            let sourceOnly ← freeze overlap #[overlap.registrations[0]!]
            unless (← selectLift sourceOnly overlap profileTarget
                invocation.operation invocation.forms) == overlap.registrations[0]! do
              throwError "the presentation profile replaced its exact selected source registration"
            let completeOnly ← freeze overlap #[overlap.registrations[1]!]
            unless (← selectLift completeOnly overlap profileTarget
                invocation.operation invocation.forms) == overlap.registrations[1]! do
              throwError "the presentation profile lost its complete original request registration"
            let oppositeOnly ← freeze installed #[installed.registrations[1]!]
            failureAt .noImplementation do
              discard <| selectLift oppositeOnly installed profileTarget
                invocation.operation invocation.forms
            let multiple ← freeze overlap overlap.registrations
            failureAt .ambiguousRealization do
              discard <| selectLift multiple overlap profileTarget invocation.operation invocation.forms
            let permuted ← freeze overlap overlap.registrations.reverse
            unless multiple.normalized == permuted.normalized &&
                multiple.sha256 == permuted.sha256 && multiple.sha256.length == 64 do
              throwError "presentation profile normalization changed exact set identity"
            unless (← kernel.dispatches.get).isEmpty do
              throwError "presentation profile selection dispatched an implementation"

            let identity : DispatchIdentity := {
              manifestDigest := "presentation-scope-control", profileDigest := "no-providers",
              registration := {
                operation := row.id.raw
                input := row.id.raw
                backend := "scope-control" } }
            let .ok reservation ← transaction.reserve request.occurrence identity connection
                invocation.dependencies
              | throwError "the named child control could not reserve its original scope"
            let scope ← RequestScope.issue kernel.ledger reservation graph encoded.slots encoded.inputs #[]
            try
              let reference := fun index =>
                (ScopedReference.input #[.field "args", .index index]).encode
              let childPacket : PresentationInvocation := {
                parameters := #[], inverse, source := reference 2,
                target := reference 3, argument := reference 4 }
              let observed ← IO.mkRef false
              let evaluate : SourceEvaluation := fun cell _ current bound selections term => do
                let applied := (selections.findAt? current term).map (·.value) |>.getD term
                let some projection ← (← current.close applied.getAppFn).inputProjectionAt #[]
                  | return ← kernel.run cell current bound term (selections := selections)
                let .context isoId := projection.target
                  | throwError "the named child changed its actual comparison source position"
                let some selected := selections[isoId]?
                  | return ← kernel.run cell current bound term (selections := selections)
                let some application := selected.application
                  | throwError "the named child lost its complete typed comparison application"
                let .presentation selectedFamily := application.family
                  | return ← kernel.run cell current bound term (selections := selections)
                unless reprStr selectedFamily == reprStr family &&
                    family.direction? projection.path == some inverse do
                  throwError "the named child changed its original comparison family or direction"
                let some (actualFirst, actualSecond) := selected.presentationEndpoints
                  | throwError "the named child reconstructed its supplied endpoint values"
                let (actualSource, actualTarget) :=
                  if inverse then (actualSecond, actualFirst) else (actualFirst, actualSecond)
                let inputs := #[actualSource, actualTarget, applied.getAppArgs.back!]
                for actual in inputs, expected in #[invocation.source, invocation.target, point] do
                  let .fvar localId := actual.consumeMData
                    | throwError "the named child lost an actual input reference"
                  let some binding := current.bindings.find? (·.expression.fvarId! == localId)
                    | throwError "the named child replaced a scoped input by source reconstruction"
                  let some retained := bound[binding.id]?
                    | throwError "the named child reference is outside its retained table"
                  unless retained.value == expected.value &&
                      retained.associationIds == expected.associationIds do
                    throwError "the named child selected another equal endpoint or point"
                observed.set true
                kernel.run cell current bound term (selections := selections)
              failureAt .noImplementation do
                discard <| kernel.child evaluate request transaction reservation scope
                  (Json.mkObj [("op", toJson row.id.raw), ("args", childPacket.encode)])
              unless ← observed.get do throwError "the named child bypassed the common source lowerer"
            finally scope.retire
          finally discard <| transaction.abort
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the source and protocol controls dispatched a mathematical provider"
      finally
        kernel.close
        owners.close connection.generation
  finally setEnv original


run_cmd Lean.Elab.Command.liftTermElabM do
  let base : PresentationInvocation := {
    parameters := #[], inverse := false, source := .null, target := .null, argument := .null }
  let .ok fields := (base.encode.getObjVal? "args").bind (·.getArr?)
    | throwError "the public presentation encoder lost its ordered packet"
  for malformed in #[fields.pop, fields.push .null, fields.set! 1 (toJson (1 : Nat)),
      fields.set! 1 (.str "false")] do
    if (PresentationInvocation.decode
        (Json.mkObj [("ctor", "presentationApply"), ("args", .arr malformed)])).isOk then
      throwError "the named comparison parser admitted a malformed complete request"




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let some row := (← semanticState).presentations.find? (·.declaration ==
        ``CasCatalogue.Algebra.CyclicQuotients.residueComparison)
      | throwError "the original parameterized comparison is not registered"
    let family ← PresentationFamily.forEntry row
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let term := mkNatLit 3
        let first ← kernel.run transaction context {} term
        let other ← kernel.run transaction context {} term
        unless first.value != other.value do
          throwError "the parameter control did not retain distinct original inputs"
        controlAt MetaM fun run =>
          withBoundValue owners.identities context {} term first
            fun context bound firstSource => run do
              controlAt MetaM fun run =>
                withBoundValue owners.identities context bound term other
                  fun context bound otherSource => run do
                    let (head, levels) ← family.instantiate
                    let firstIso := mkApp head firstSource
                    let otherIso := mkApp head otherSource
                    let firstEnds ← family.endpoints firstIso
                    let otherEnds ← family.endpoints otherIso
                    let withEnds (ends : SourceSelection Expr × SourceSelection Expr)
                        (action : MetaM PreparedRequest → MetaM Unit) : MetaM Unit :=
                      SourceSelectionScope.withBinding owners.identities {} context ends.1
                        fun context selections sourceTerm =>
                          SourceSelectionScope.withBinding owners.identities selections context ends.2
                            fun context selections targetTerm => do
                              let source ← kernel.run transaction context bound sourceTerm
                                (selections := selections)
                              let target ← kernel.run transaction context bound targetTerm
                                (selections := selections)
                              withBoundValue owners.identities context bound sourceTerm source fun context bound sourceTerm =>
                                withBoundValue owners.identities context bound targetTerm target fun context bound targetTerm => do
                                  let graph ← transaction.view
                                  let .ok parameter := RuntimeArgument.ofValue graph 0 first
                                    | throwError "the original comparison parameter is outside its graph"
                                  let .ok sourceArgument := RuntimeArgument.ofValue graph 0 source
                                    | throwError "the original comparison source is outside its graph"
                                  let .ok targetArgument := RuntimeArgument.ofValue graph 1 target
                                    | throwError "the original comparison target is outside its graph"
                                  let mut parameters := #[]
                                  for binding in context.bindings do
                                    if let some value := bound[binding.id]? then
                                      parameters := parameters.push (← IO.ofExcept <|
                                        (RuntimeParameter.ofValue graph binding.id value).mapError IO.userError)
                                  let program ← owners.identities.fresh .program
                                  let occurrence ← kernel.ledger.allocate
                                  let universes ← levels.mapM instantiateLevelMVars
                                  let parameterSources := #[← context.close firstSource]
                                  let endpointSources := #[← context.close sourceTerm, ← context.close targetTerm]
                                  action (PreparedRequest.forPresentation owners.identities program
                                    occurrence family universes context parameterSources #[parameter]
                                    endpointSources #[sourceArgument, targetArgument] parameters graph
                                    (selections := selections))

                    withEnds firstEnds fun request => discard request
                    withEnds otherEnds fun request => do
                      let failure : Option Exception ← try
                        discard request
                        pure none
                      catch error => pure (some error)
                      let some failure := failure
                        | throwError "the presentation accepted endpoint descriptors with another equal parameter node"
                      unless failure.toMessageData.hasTag
                          (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do throw failure
                    unless (← kernel.dispatches.get).isEmpty do
                      throwError "the parameter identity control dispatched a comparison"
      finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original

end CasRuntime.PresentationTests
