module

import CasRuntime.Property
import CasCatalogue.TestSuite
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Property
meta import CasCatalogue.TestSuite
meta import LeanCategories.Catalogue

namespace CasRuntime.PropertyTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue CasCatalogue.Backend

-- Source, packet and lifecycle controls only. Existing published properties supply every
-- proposition. These tests neither prove abelianness/finiteness nor supply mathematical answers.
set_option maxHeartbeats 2000000 in
run_cmd do
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  let path := root / ".tmp" / "property-empty-leaves.json"
  IO.FS.writeFile path
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
  CasCatalogue.Language.withSession (some path) true fun initial => do
    let mut session := initial
    for text in #["let C3 := ZMod(3) in Groups", "let C3again := ZMod(3) in Groups",
        "let S3 := Sym(3) in Groups", "let Rfirst := ℤ in Rings", "let Rsecond := ℤ in Rings",
        "let Mfirst := RegularModule(Rfirst)", "let Msecond := RegularModule(Rsecond)"] do
      let result ← CasCatalogue.Language.runStatement session text
      unless result.outcome.kind == "holds" do
        throwError "the original property input failed: {text}: {result.outcome.detail}"
      session := result.session
    liftTermElabM do
      let originalValue (name : Name) : MetaM ValueBinding := do
        let some entry := session.source.context.entries.find? (·.userName == name)
          | throwError "the property control lost original binding {name}"
        let some selected := session.value? entry.id
          | throwError "the property control lost actual value {name}"
        return selected
      let exact := fun (left right : ValueBinding) =>
        left.value == right.value && left.associationIds == right.associationIds
      let failAt (stratum : Stratum) (action : MetaM Unit) : MetaM Unit := do
        let failure : Option Exception ← try
          action
          pure none
        catch error => pure (some error)
        let some failure := failure | throwError "the property negative was accepted"
        unless CasCatalogue.Exception.stratum? failure == some stratum do throw failure
      let failWith (message : String) (action : MetaM Unit) : MetaM Unit := do
        let failure : Option Exception ← try
          action
          pure none
        catch error => pure (some error)
        let some failure := failure | throwError "the property identity negative was accepted"
        unless (← failure.toMessageData.toString).startsWith message do throw failure
      -- The same production Lower/Execute capture pattern as RoutedMethodTests. Only the
      -- final property observation is stopped; every input uses the ordinary interpreter.
      let capture (transaction : CellTransaction) (action : SourceEvaluation → MetaM ValueBinding) :
          MetaM (PreparedRequest × PreparedPropertyRoute) := do
        let captured ← IO.mkRef (none : Option PreparedRequest)
        let evaluate : SourceEvaluation := fun cell program context bound expression => do
          let handler : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
            fun request current => do
              if let .primitive (.property _) _ := request.action then
                captured.set (some request)
                throwError "captured the original prepared property observation"
              let response ← Execute.run session.kernel.executor
                (PFunctor.FreeM.lift (P := OperationalSignature) request) current
                (some (session.kernel.resolveFixedInput
                  (fun cell _ context bound expression => session.kernel.run cell context bound expression)
                  current program))
              return (response, current)
          lowerTerm {
            ledger := session.kernel.ledger, transaction := cell,
            codes := session.kernel.codes, marks := session.kernel.marks
            run := fun computation => do
              let (result, _) ← handler.run computation cell
              return result }
            program context bound expression
        let failure : Option Exception ← try
          discard <| action evaluate
          pure none
        catch error => pure (some error)
        let some request ← captured.get
          | if let some failure := failure then throw failure
            else throwError "the source never reached its complete property observation"
        return (request, ← PreparedPropertyRoute.prepare session.kernel
          (← transaction.view) request)
      let installed (forms : Array String) : MetaM Manifest := do
        let packet := Json.mkObj [
          ("backends", .arr #[Json.mkObj [("name", "unused-property-peer"),
            ("command", "/bin/false"), ("args", .arr #[])]]),
          ("registrations", .arr (forms.map fun form => Json.mkObj [
            ("operation", "prop.is_abelian"), ("input", toJson form),
            ("backend", "unused-property-peer")]))]
        let parsed ← IO.ofExcept <| (Manifest.parse packet).mapError IO.userError
        let (admitted, rejected) ← admitManifest parsed
        unless rejected.isEmpty do
          throwError "the published property input forms were rejected: {rejected}"
        return admitted
      let firstGroup ← originalValue `C3
      let otherGroup ← originalValue `C3again
      let firstRing ← originalValue `Rfirst
      let otherRing ← originalValue `Rsecond
      unless firstGroup.value != otherGroup.value && firstRing.value != otherRing.value do
        throwError "the property control merged separately declared equal inputs"
      let connection ← session.kernel.ledger.owners.spawn { cmd := "/bin/cat" }
      try
        let cases : Array (String × String × Option Name × Option String) := #[
          ("C3", "is_abelian", none, some "C3again"),
          ("C3again", "is_abelian", none, some "C3"),
          ("S3", "is_abelian", none, none),
          ("Mfirst", "is_finite", some `Rfirst, some "Msecond"),
          ("Msecond", "is_finite", some `Rsecond, some "Mfirst")]
        for (name, propertyName, scalarName, peerName) in cases do
          let text := s!"{name}.{propertyName}()"
          let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
            | throwError "the original property expression did not parse"
          let term ← session.source.read ⟨parsed⟩
          let peer ← peerName.mapM fun peerName => do
            let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
                s!"{peerName}.{propertyName}()"
              | throwError "the equal-source property expression did not parse"
            session.source.read ⟨parsed⟩
          let original ← originalValue (Name.mkSimple name)
          let some originalEntry := session.source.context.entries.find?
              (·.userName == Name.mkSimple name)
            | throwError "the property lost its exact original receiver identity"
          let transaction ← CellTransaction.begin session.kernel.ledger
          try
            let (request, route) ← term.source.withOpen fun bindings expression => do
              let context ← ContextTelescope.capture bindings
              let some (data, _) ← propertySource? expression
                | throwError "the source property lost its selected marker"
              let family ← PropertyFamily.fromMark data
              let (_, parameters, receiver) ← family.application expression
              let some selected := bindings.find? (·.id == originalEntry.id)
                | throwError "the source property lost its original receiver binder"
              unless receiver == selected.expression &&
                  data.getString `CasCompiler.source.id == s!"prop.{propertyName}" &&
                  data.getName `CasCompiler.source.declaration == family.classifier.declaration do
                throwError "the property source changed its receiver or accepted classifier"
              if let some scalarName := scalarName then
                let some scalarEntry := session.source.context.entries.find? (·.userName == scalarName)
                  | throwError "the property lost its exact selected scalar identity"
                let some scalar := bindings.find? (·.id == scalarEntry.id)
                  | throwError "the property lost its chosen scalar binder"
                let #[parameter] := parameters
                  | throwError "the property changed its exact category parameter arity"
                let .mdata marker _ := parameter
                  | throwError "the property lost its selected category parameter wrapper"
                unless marker.contains `CasCompiler.source.objectOrigin do
                  throwError "the property lost its explicit category parameter origin"
                let some (parameterCategory, parameterSource) ← sourceObjectOrigin? parameter
                  | throwError "the property lost its original category parameter"
                let some selectedCategory := session.source.categoryFor scalarEntry.id
                  | throwError "the property lost its original scalar category"
                unless parameterSource == scalar.expression && parameterCategory.role == .object &&
                    parameterCategory.expression.syntacticEq (.atom CategoryId.rings) &&
                    parameterCategory.expression.syntacticEq selectedCategory.expression &&
                    parameterCategory.bundle == (← selectedCategory.bundle.inContext context) do
                  throwError "the property source replaced its exact category parameter"
              else unless parameters.isEmpty do
                throwError "the group property invented a category parameter"
              -- A well-typed but inconsistent payload must not substitute an equal
              -- receiver or complete category argument behind the literal Holds image.
              if let some peer := peer then
                let (_, peerParameters, peerReceiver) ← family.application
                  (← peer.source.inContext context)
                let (position, replacement) ← match scalarName with
                  | none => pure (family.parameterCount, peerReceiver)
                  | some _ => do
                    let #[parameter] := peerParameters
                      | throwError "the equal-source property changed its complete parameter arity"
                    pure (0, parameter)
                let some witness := expression.find? fun term => match term with
                    | .mdata marker _ => marker.getName
                        `CasCompiler.source.propertyApplication == ``PropertyFamily
                    | _ => false
                  | throwError "the original property lost its application witness"
                let .mdata witnessData retained := witness
                  | throwError "the original property witness lost its metadata"
                unless retained.isAppOfArity ``Function.const 4 do
                  throwError "the original property witness changed its typed field shape"
                let applied := retained.getAppArgs[3]!
                let some originalArgument := applied.getAppArgs[position]?
                  | throwError "the original property witness lost its complete argument position"
                unless originalArgument != replacement &&
                    (← isDefEq originalArgument replacement) do
                  throwError "the property witness control needs distinct equal source arguments"
                let changedApplication := mkAppN applied.getAppFn
                  (applied.getAppArgs.set! position replacement)
                let changedWitness := Expr.mdata witnessData (mkAppN retained.getAppFn
                  (retained.getAppArgs.set! 3 changedApplication))
                let forged := expression.replace fun term =>
                  if term == witness then some changedWitness else none
                check forged
                withoutModifyingState <|
                  failWith "the property source witness changed its original native proposition" do
                    discard <| family.application forged
              let mut bound : Std.HashMap BindingId ValueBinding := {}
              for binding in bindings do
                if let some actual := session.value? binding.id then
                  bound := bound.insert binding.id actual
              let program ← session.kernel.ledger.owners.identities.fresh .program
              capture transaction fun evaluate =>
                evaluate transaction program context bound expression
            let expectedId := s!"prop.{propertyName}"
            unless request.source.kind == .typeValue && request.reference.isNone &&
                route.family.entry.id.raw == expectedId &&
                route.family.entry.classifier == route.family.classifier.id &&
                exact original route.receiver && route.preparation == request.roles.scope do
              throwError "the complete property demand changed its source authority"
            let some application := request.origin.application
              | throwError "the property lost its complete actual input table"
            if let some scalarName := scalarName then
              let scalar ← originalValue scalarName
              let #[some actualScalar, some actualReceiver] := application.arguments
                | throwError "the parameterized property lost its original complete positions"
              unless exact scalar actualScalar && exact original actualReceiver do
                throwError "the property changed an original scalar or receiver occurrence"
            else
              let #[some actualReceiver] := application.arguments
                | throwError "the group property changed its original receiver arity"
              unless exact original actualReceiver do
                throwError "the group property changed its original receiver reference"
            -- Rebuild only for the negative controls, keeping the original expected sources.
            let rebuild (replacement : Option (Nat × ValueBinding)) : MetaM PreparedRequest :=
              withSourceScope request fun context bound => do
                let graph ← transaction.view
                let some layout := request.application
                  | throwError "the property lost its source application layout"
                let mut parameters := #[]
                for binding in context.bindings do
                  if let some actual := bound[binding.id]? then
                    parameters := parameters.push (← IO.ofExcept <|
                      (RuntimeParameter.ofValue graph binding.id actual).mapError IO.userError)
                let mut actual := #[]
                for selected in application.arguments, index in [:application.arguments.size] do
                  if let some selected := selected then
                    let selected := match replacement with
                      | some (position, changed) => if position == index then changed else selected
                      | none => selected
                    actual := actual.push (← IO.ofExcept <|
                      (RuntimeArgument.ofValue graph index selected (← session.kernel.marks.get)).mapError IO.userError)
                let .primitive boundary levels := request.action
                  | throwError "the property control lost its primitive request"
                PreparedRequest.forBoundary session.kernel.ledger.owners.identities request.program
                  request.occurrence boundary levels context
                  (layout.arguments.map (·.source.source)) actual #[] parameters
            if name != "S3" then
              let replacement ← match scalarName with
                | some scalar => originalValue (if scalar == `Rfirst then `Rsecond else `Rfirst)
                | none => originalValue (if name == "C3" then `C3again else `C3)
              let failure : Option Exception ← try
                discard <| rebuild (some (0, replacement))
                pure none
              catch error => pure (some error)
              let some failure := failure
                | throwError "the property identity negative was accepted"
              unless failure.toMessageData.hasTag
                  (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do throw failure
            if name == "C3" then
              let some originalBoundary := route.boundaries[0]?
                | throwError "the property has no original source boundary"
              unless originalBoundary.offset == 0 &&
                  originalBoundary.forms.contains "cat.groups" &&
                  originalBoundary.forms.contains "obj.groups.cyclic" &&
                  route.family.classifier.id == ClassifierId.magmasCommutative do
                throwError "the abelian property changed its complete source forms or classifier"
              failAt .noImplementation do
                discard <| route.select session.kernel.manifest
              failAt .ambiguousRealization do
                discard <| route.select (← installed #["cat.groups", "obj.groups.cyclic"])
              let selection ← route.select (← installed #["cat.groups"])
              let evaluate : SourceEvaluation := fun cell _ context bound expression =>
                session.kernel.run cell context bound expression
              let invocation ← selection.materialize session.kernel evaluate request transaction
              unless invocation.offset == 0 && invocation.property.raw == expectedId &&
                  invocation.preparation == request.roles.scope && exact original invocation.receiver do
                throwError "the selected property changed its boundary or original receiver"
              do
                let rebuilt ← rebuild none
                unless rebuilt.occurrence == request.occurrence &&
                    rebuilt.roles.scope != request.roles.scope do
                  throwError "the property control did not make a distinct preparation"
                let rejectPreparation (action : MetaM Unit) : MetaM Unit := do
                  let failure : Option Exception ← try
                    action
                    pure none
                  catch error => pure (some error)
                  let some failure := failure
                    | throwError "a property accepted a different request preparation"
                  unless failure.toMessageData.hasTag (· == requestPreparationMismatchTag) do
                    throw failure
                rejectPreparation do
                  discard <| selection.materialize session.kernel evaluate rebuilt transaction
                rejectPreparation do
                  discard <| session.kernel.invokeProperty evaluate rebuilt transaction invocation
              let graph ← transaction.view
              let .ok (encoded, packet) := invocation.encode graph connection.generation
                | throwError "the original property receiver did not encode"
              unless (packet.getObjValAs? String "ctor").toOption == some "obj.groups.cyclic" do
                throwError "the property replaced its original raw receiver packet"
              let #[rootInput] := invocation.roots
                | throwError "the property packet changed its root arity"
              let some encodedRoot := encoded.inputs.find? (·.path.isEmpty)
                | throwError "the raw property packet lost its original scope root"
              unless rootInput.path.isEmpty && exact original rootInput.binding &&
                  exact original encodedRoot.binding do
                throwError "property encoding reconstructed the original receiver"
              let identity : DispatchIdentity := {
                manifestDigest := "property-scope-control", profileDigest := "no-provider"
                registration := invocation.registration }
              let .ok reservation ← transaction.reserve request.occurrence identity connection
                  invocation.dependencies
                | throwError "the property could not reserve its original source scope"
              let scope ← RequestScope.issue session.kernel.ledger reservation graph
                encoded.slots encoded.inputs #[]
              try
                let call := Json.mkObj [("op", toJson expectedId), ("input", "cat.groups"),
                  ("args", (ScopedReference.input #[]).encode)]
                let (childRequest, childRoute) ← capture transaction fun evaluate =>
                  session.kernel.child evaluate request transaction reservation scope call
                unless childRequest.occurrence != request.occurrence &&
                    childRoute.family.entry.id == route.family.entry.id &&
                    childRoute.family.classifier.id == route.family.classifier.id &&
                    childRoute.family.route.refs == route.family.route.refs &&
                    exact original childRoute.receiver do
                  throwError "the property child changed its native source selection or actual receiver"
                unless (← sourceFamilyConversion route.family.family childRoute.family.family #[]).isSome do
                  throwError "the child property changed the complete unapplied native family"
                failAt .malformed do
                  discard <| session.kernel.child evaluate request transaction reservation scope
                    (Json.mkObj [("op", toJson expectedId), ("input", "cat.sets"),
                      ("args", (ScopedReference.input #[]).encode)])
                -- Real reply admission, with a protocol-only payload. Rejection must leave
                -- this exact occurrence pending and its isolated delta invisible.
                let malformed := #[Json.bool true,
                  Json.mkObj [("ctor", "some"), ("args", .arr #[.bool true])],
                  Json.mkObj [("ctor", "none"), ("args", .arr #[.null])],
                  Json.mkObj [("ctor", "some"), ("args", .arr #[Json.mkObj
                    [("ctor", "true"), ("args", .arr #[]), ("extra", .null)]])]]
                let some resultRole := request.roles.results[0]?
                  | throwError "the property observation lost its result role"
                for packet in malformed do
                  let before ← transaction.view
                  let reply ← ImmediateReply.parseControl scope reservation before scope.wireId 0
                    (Json.mkObj [("request_id", toJson (0 : Nat)), ("status", "ok"),
                      ("value", packet), ("exports", .arr #[])])
                  failAt .malformed do
                    discard <| reply.stageCompletion request transaction scope connection
                  unless before.sameRevision (← transaction.view) &&
                      ((← SessionSnapshot.current).receipt request.occurrence).isNone do
                    throwError "a malformed property answer published a result"
                  match ← transaction.reuse request.occurrence resultRole.role.id with
                  | .ok (.pending retained) =>
                    unless retained.occurrence == reservation.occurrence &&
                        retained.connection == reservation.connection do
                      throwError "a malformed property answer changed its pending occurrence"
                  | _ => throwError "a malformed property answer became a reusable completion"
              finally scope.retire
          finally discard <| transaction.abort
        unless (← session.kernel.dispatches.get).isEmpty do
          throwError "the property source controls dispatched a mathematical provider"
      finally session.kernel.ledger.owners.close connection.generation

-- Exercise the actual computing question path. The fixed protocol packets are deliberately
-- independent of the group: they test observation/lifecycle classification, never B0 mathematics.
-- The unchanged SessionPredicateTests separately retains ordinary predicate raw-Boolean behavior.
run_cmd do
  let contract ← packageDir contractPackage
  let root ← IO.currentDir
  let python := (← IO.FS.realPath contract) / ".venv/bin/python"
  let peer := root / "scripts/probes/protocol_v2_peer.py"
  let answer := fun (label : String) => Json.mkObj [("ctor", "some"), ("args", .arr #[Json.mkObj
    [("ctor", toJson label), ("args", .arr #[])]])]
  let cases : Array (Json × String) := #[
    (answer "true", "holds"), (answer "false", "wrong"),
    (Json.mkObj [("ctor", "none"), ("args", .arr #[])], "gap"), (.bool true, "malformed")]
  for (packet, expected) in cases, index in [:cases.size] do
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "property-observation-peer"),
        ("command", python.toString), ("args", .arr #[toJson peer.toString,
          "--property-observation", toJson packet.compress])]]),
      ("registrations", .arr #[Json.mkObj [("operation", "prop.is_abelian"),
        ("input", "cat.groups"), ("backend", "property-observation-peer")]])]
    IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / s!"property-observation-{index}.json"
    IO.FS.writeFile path manifest.compress
    CasCatalogue.Language.withSession (some path) true fun initial => do
      let input ← CasCatalogue.Language.runStatement initial "let C3 := ZMod(3) in Groups"
      unless input.outcome.kind == "holds" do
        throwError "the property observation input failed: {input.outcome.detail}"
      let result ← CasCatalogue.Language.runStatement input.session "assert C3.is_abelian()"
      unless result.outcome.kind == expected do
        throwError "the property packet {packet.compress} was {result.outcome.kind}: {result.outcome.detail}"
      let negatedExpected := if expected == "holds" then "wrong"
        else if expected == "wrong" then "holds" else expected
      let negated ← CasCatalogue.Language.runStatement result.session
        "assert C3.is_abelian() = false"
      unless negated.outcome.kind == negatedExpected do
        throwError "the negated property packet {packet.compress} was {negated.outcome.kind}: {negated.outcome.detail}"
      let dispatched := (← negated.session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["prop.is_abelian", "prop.is_abelian"] do
        throwError "the computing property questions bypassed their original observation boundaries"

end CasRuntime.PropertyTests
