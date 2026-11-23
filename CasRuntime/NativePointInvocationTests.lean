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
    (callable point : ValueBinding) (pointSource : Expr) :
    MetaM (PreparedRequest × PreparedPointInvocation) := do
  let graph ← transaction.view
  let .ok code := graph.callable callable
    | throwError "the named point callable is outside its actual graph"
  let some node := graph.find code.value
    | throwError "the named point callable lost its original code"
  let .closure program _ := node.payload.data
    | throwError "the named point callable is not its retained native source"
  let some (.family family path) := (← kernel.codes.get)[program]?
    | throwError "the named point callable was replaced by a source computation"
  let .ok argument := RuntimeArgument.ofValue graph 0 point (← kernel.marks.get)
    | throwError "the named point operand is outside its actual graph"
  let request ← PreparedRequest.forApplication kernel.ledger.owners.identities program
    (← kernel.ledger.allocate) context callable #[← context.close pointSource] #[argument] #[]
  let evaluate : SourceEvaluation := fun cell _ current bound source =>
    kernel.run cell current bound source
  let some invocation ← PreparedPointInvocation.prepare? kernel evaluate request family path transaction
    | throwError "the original named point action did not prepare its published packet"
  return (request, invocation)

-- The native source supplies the original numeral map and all endpoint families. The complete
-- packet and scoped child use the production kernel, without a provider or substitute answer.
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
        let some entry := (← semanticState).morphisms.find? (·.declaration == declaration)
          | throwError "an original F9 constants map is not registered"
        let family ← PointFamily.forEntry entry
        let arrowSource := sourceReference ``MorphismEntry entry.id.raw declaration (mkConst declaration)
        let callableSource ← family.function arrowSource
        let (source, _) ← family.endpoints (mkConst declaration)
        let pointSource ← sourceNumeral (fun _ => pure none) 2 source
        let some pointOrigin ← sourcePointOrigin? pointSource
          | throwError "the source numeral lost its independently supplied point map"
        let producer ← CellTransaction.begin kernel.ledger
        let callable ← kernel.run producer context {} callableSource
        let point ← kernel.run producer context {} pointSource
        let .ok _ ← producer.commit
          | throwError "the original named point inputs could not publish"
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let (request, invocation) ← prepare kernel transaction context callable point pointSource
          unless invocation.operation == entry.id.raw && invocation.parameters.isEmpty &&
              invocation.argument.value == point.value &&
              invocation.argument.associationIds == point.associationIds do
            throwError "the named point action changed its released identity or original argument"
          let graph ← transaction.view
          let actualDomain ← invocation.domain.role.source.inContext context
          unless ← isDefEq actualDomain pointOrigin.domain do
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
            let evaluate : SourceEvaluation := fun cell _ current bound source => do
              let some selected := source.find? fun expression =>
                  match expression with
                  | .mdata data _ =>
                    data.getString `CasCompiler.source.pointRequest == entry.id.raw
                  | _ => false
                | throwError "the named child discarded its explicitly supplied complete inputs"
              let some actual ← family.request? selected
                | throwError "the named child lost its typed input provenance"
              for term in #[actual.domain, actual.source, actual.target, actual.point],
                  expected in #[invocation.domain, invocation.source, invocation.target, point] do
                let .mdata mark _ := term
                  | throwError "the named child replaced a supplied original input"
                let some index := markedKey? mark
                  | throwError "the named child has no actual source input mark"
                let some value := (← kernel.marks.get)[index]?
                  | throwError "the named child input is outside its retained table"
                unless value.value == expected.value &&
                    value.associationIds == expected.associationIds do
                  throwError "the named child substituted another equal source input"
              observed.set true
              kernel.run cell current bound source
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

-- A complete named-arrow descriptor uses every original declared parameter slot, including
-- repeated aliases. Distinct released families with the same endpoints remain distinct.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let groupSource ← mkAppM ``CasCatalogue.Algebra.FiniteGroups.symmetric #[mkNatLit 3]
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let connection ← owners.spawn { cmd := "/bin/cat" }
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let group ← kernel.run transaction context {} groupSource
        let selected ← markValue kernel.marks group groupSource
        let identitySource ← mkAppM ``CasCatalogue.Algebra.FiniteGroups.identity #[selected]
        let trivialSource ← mkAppM ``CasCatalogue.Algebra.FiniteGroups.trivial #[selected, selected]
        unless ← isDefEq (← inferType identitySource) (← inferType trivialSource) do
          throwError "the family-identity control did not retain equal declared endpoints"
        let identity ← kernel.run transaction context {} identitySource
        let trivial ← kernel.run transaction context {} trivialSource
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

-- A named arrow's parameter is an actual chosen endpoint, even when another object has the
-- same declared family and scalar data. Reuse the original numeral map and original arrow;
-- changing only the supplied endpoint must fail before any provider can observe the request.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let some entry := (← semanticState).morphisms.find? (·.declaration ==
        ``CasCatalogue.Algebra.FiniteGroups.identity)
      | throwError "the existing group identity family is not registered"
    let family ← PointFamily.forEntry entry
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let parameter ← kernel.run transaction context {} (mkNatLit 2)
        let selectedParameter ← markValue kernel.marks parameter (mkNatLit 2)
        let groupSource ← mkAppM ``CasCatalogue.Algebra.FiniteGroups.cyclic #[selectedParameter]
        let first ← kernel.run transaction context {} groupSource
        let other ← kernel.run transaction context {} groupSource
        unless first.value != other.value do
          throwError "the endpoint control did not retain two distinct supplied objects"
        let firstSource ← markValue kernel.marks first groupSource
        let otherSource ← markValue kernel.marks other groupSource
        let arrowSource ← mkAppM entry.declaration #[firstSource]
        let callable ← kernel.run transaction context {} (← family.function arrowSource)
        let carrier ← mkAppM ``CasCatalogue.Foundation.Objects.integersMod #[selectedParameter]
        let pointSource ← sourceNumeral (fun _ => pure none) 0 carrier
        let some origin ← sourcePointOrigin? pointSource
          | throwError "the endpoint control lost its original numeral point map"
        let point ← kernel.run transaction context {} pointSource
        let exact ← family.withRequest arrowSource origin.domain firstSource firstSource pointSource
        let (_, invocation) ← prepare kernel transaction context callable point exact
        unless invocation.source.value == first.value && invocation.target.value == first.value &&
            invocation.source.associationIds == first.associationIds &&
            invocation.target.associationIds == first.associationIds do
          throwError "the named point packet changed its original chosen endpoint"
        let changed ← family.withRequest arrowSource origin.domain otherSource firstSource pointSource
        let failure : Option Exception ← try
          discard <| prepare kernel transaction context callable point changed
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "the named point action accepted a different equal endpoint node"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do
          throw failure
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the original endpoint control dispatched a mathematical provider"
      finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original

-- Framing remains the public parser's exact seven fields; it supplies no point interpretation.
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

-- The public zero source lowers to its exact published operation demand. The
-- opaque original inputs carry no fields or answer; the observer returns no result.
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
        let program ← owners.identities.fresh .program
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let ringSource := bindings[0]!
          let moduleSource := bindings[2]!
          let ring ← transaction.stage
            { program, occurrence := ← kernel.ledger.allocate,
              role := ← SourceLayout.ofTerm (← context.close ringSource.expression),
              parameters := Array.replicate bindings.size none }
            (.ownedExport connection "original nullary scalar" #[])
          let .ok parameter := RuntimeParameter.ofValue
              (← transaction.view) ringSource.id ring
            | throwError "the nullary runtime scalar is outside its original graph"
          let environment ← RuntimeEnvironment.capture owners.identities.worker
            context #[parameter]
          let moduleValue ← transaction.stage
            (← environment.origin program (← kernel.ledger.allocate)
              (← SourceLayout.ofTerm (← context.close moduleSource.expression)))
            (.ownedExport connection "original nullary module" #[ring])
          let observed ← IO.mkRef false
          let observe : PFunctor.Handler.Stateful MetaM CellTransaction
              OperationalSignature := fun request _ => do
            unless request.reference == some (.operation ⟨"op.modules.zero"⟩) do
              throwError "the public nullary value emitted another demand before its operation"
            let some application := request.origin.application
              | throwError "the nullary operation demand lost its native argument telescope"
            let arguments := application.arguments
            unless arguments.size == 2 &&
                arguments[0]?.flatten.any (fun value =>
                  value.value == ring.value && value.associationIds == ring.associationIds) &&
                arguments[1]?.flatten.any (fun value =>
                  value.value == moduleValue.value &&
                    value.associationIds == moduleValue.associationIds) do
              throwError "the nullary operation demand replaced its original scalar or module"
            observed.set true
            throwError "observed the original nullary operation demand"
          let bound : Std.HashMap BindingId ValueBinding :=
            ({} : Std.HashMap BindingId ValueBinding)
              |>.insert ringSource.id ring |>.insert moduleSource.id moduleValue
          let failure : Option Exception ← try
              discard <| lowerTerm {
                ledger := kernel.ledger, transaction, codes := kernel.codes, marks := kernel.marks
                run := fun computation => Execute.run observe computation transaction }
                program context bound expression
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
