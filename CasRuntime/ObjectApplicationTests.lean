module

import CasRuntime.Kernel
import CasRuntime.Point
import CasRuntime.ManifestAdmission
import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.Point
meta import CasRuntime.ManifestAdmission
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings

namespace CasRuntime.ObjectApplicationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original application term did not parse"
  return ⟨source⟩

private def assumeSource (session : SourceSession) (text : String) : TermElabM SourceSession := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_stmt text
    | throwError "the application input declaration did not parse"
  let .assumption session ← session.readStatement ⟨source⟩
    | throwError "the application input was not retained as its original assumption"
  return session

private def exactInput (left right : ValueBinding) : Bool :=
  left.value == right.value && left.associationIds == right.associationIds

private def failAt (stratum : Stratum) (action : MetaM Unit) : MetaM Unit := do
  let failure : Option Exception ← try
    action
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "an invalid object application was accepted"
  unless CasCatalogue.Exception.stratum? failure == some stratum do throw failure

private def rejected (action : MetaM Unit) : MetaM Unit := do
  let failed ← try
    action
    pure false
  catch _ => pure true
  unless failed do throwError "an incompatible selected application was accepted"


private def prepare (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (callable point : ValueBinding) (pointSource : Expr) (parameters : Array RuntimeParameter)
    (selections : SourceSelectionScope Expr := {}) :
    MetaM (PreparedRequest × PreparedPointInvocation × PreparedRequest) := do
  let bound := parameters.foldl (fun bound parameter => bound.insert parameter.source parameter.value)
    ({} : Std.HashMap BindingId ValueBinding)
  withBoundValue kernel.ledger.owners.identities context bound pointSource point fun context bound pointSource => do
    let graph ← transaction.view
    let .ok code := graph.callable callable | throwError "the original callable is not visible"
    let some node := graph.find code.value | throwError "the original callable lost its code"
    let .closure program _ := node.payload.data | throwError "the original callable is not native code"
    let some (.family family path) := (← kernel.codes.get)[program]?
      | throwError "the object application lost its retained family"
    let .ok argument := RuntimeArgument.ofValue graph 0 point
      | throwError "the original point is not visible"
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
      | throwError "the original object application did not prepare its published packet"
    return (request, invocation, family)




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let connection ← owners.spawn { cmd := "/bin/cat" }
    try
      for (first, second, text, owner, otherOwner) in #[
          ("let M ∈ Mat₂(ℚ)", "let v ∈ ℚ²", "M(v)", "obj.sets.matrices", "obj.sets.polynomials"),
          ("let p ∈ ℤ[x]", "let a ∈ ℤ", "p(a)", "obj.sets.polynomials", "obj.sets.matrices")] do
        let empty ← SourceSession.empty owners.identities
        let session ← assumeSource (← assumeSource empty first) second
        let term ← session.read (← sourceTerm text)
        term.source.withOpen fun bindings expression => do
          let originalInputs := session.context.entries.filter (·.role == .parameter)
          unless originalInputs.size == 2 && originalInputs[0]!.id != originalInputs[1]!.id do
            throwError "the original operands lost their distinct source bindings"
          let operands ← originalInputs.mapM fun entry => do
            let some binding := bindings.find? (·.id == entry.id)
              | throwError "the reader lost an original operand's actual binding"
            pure binding
          let context ← ContextTelescope.capture bindings
          let selections ← term.selections.inContext context


          let original := ((selections.findAt? context expression).map (·.value)
            |>.getD expression).consumeMData
          let original := if original.isAppOfArity ``id 2 then
              original.getAppArgs[1]!.consumeMData else original
          let .app callableSource pointSource := original
            | throwError "the original reading is not its final native point application"
          let some selectedPoint := selections.findAt? context pointSource
            | throwError "the exact original application argument lost its selected source binder"
          let some pointOrigin := selectedPoint.pointOrigin
            | throwError "the exact original application argument lost its point provenance"
          let program ← owners.identities.fresh .program
          let transaction ← CellTransaction.begin kernel.ledger
          try
            let mut values : Array ValueBinding := #[]
            let mut parameters : Array RuntimeParameter := #[]
            let mut bound : Std.HashMap BindingId ValueBinding := {}
            for binding in operands do
              let role ← SourceLayout.ofTerm (← context.close binding.expression)
              let role := { role with
                selections := term.selections
                selectionBinding := if selections.contains binding.id then some binding.id else none }
              let value ← transaction.stage
                { program, occurrence := ← kernel.ledger.allocate,
                  role,
                  parameters := Array.replicate bindings.size none }
                (.ownedExport connection s!"formal operand {binding.id.serial}" #[])
              let .ok parameter := RuntimeParameter.ofValue (← transaction.view) binding.id value
                | throwError "the original operand lost its source binding authority"
              values := values.push value
              parameters := parameters.push parameter
              bound := bound.insert binding.id value
            let callable ← kernel.run transaction context bound callableSource (selections := selections)
            let point ← kernel.run transaction context bound pointSource (selections := selections)
            let (request, invocation, family) ←
              prepare kernel transaction context callable point pointSource parameters selections
            let .primitive (.application selected) _ := family.action
              | throwError "the object application was replaced by another computation boundary"
            let .application entry := selected.owner
              | throwError "the selected application changed its owner kind"
            unless entry.id.raw == owner && invocation.operation == entry.applicationAddress &&
                invocation.preparation == request.roles.scope && exactInput invocation.argument point do
              throwError "the application packet changed its original owner, request or operand"
            family.environment.withContext context bound fun context bound => do
              let arrow ← family.source.source.inContext context
              let (expectedSource, expectedTarget) ← selected.endpoints arrow
              unless expectedSource.isAppOfArity ``Prod 2 do
                throwError "the application lost its whole native product source"
              for actual in #[invocation.domain, invocation.source, invocation.target],
                  expected in #[pointOrigin.domain, expectedSource, expectedTarget] do
                withBindingContext (← transaction.view) context bound actual fun context _ => do
                  context.withOriginalSources #[← actual.selectedSource context, expected]
                      fun native => do
                    unless ← isDefEq native[0]! native[1]! do
                      throwError "the application changed its complete native domain or endpoint"
            let some originalArguments := family.origin.application
              | throwError "the application lost its original declared parameter table"
            let some application := family.application
              | throwError "the application lost its complete native telescope"
            let declared := application.arguments.filter fun argument =>
              argument.wireIndex.isSome && argument.binderInfo.isExplicit
            unless declared.size == 2 && invocation.parameters.size == declared.size do
              throwError "the application omitted a declared ring, dimension or algebra parameter"
            for slot in declared, value in invocation.parameters do
              let some original := originalArguments.arguments[slot.sourceIndex]?.bind id
                | throwError "the application lost an original selected parameter"
              unless exactInput value original do
                throwError "the application replaced an original parameter by an equal value"
            let graph ← transaction.view
            for expectedValue in values, index in [:values.size] do
              let .ok actual := graph.project invocation.argument index
                | throwError "the application lost an ordered original operand slot"
              unless actual.value == expectedValue.value &&
                  expectedValue.associationIds.toList.isPrefixOf actual.associationIds.toList do
                throwError "the product operand changed a source binding or its association chain"
            let codes ← kernel.codes.get
            let some descriptor ← InputDescriptorView.namedApplication? graph codes invocation.arrow
              | throwError "the application arrow lost its original checked descriptor"
            unless exactInput descriptor.binding invocation.arrow &&
                (← InputDescriptorView.namedMorphism? graph codes invocation.arrow).isNone do
              throwError "the object application was reclassified as an unrelated named morphism"
            failAt .malformed do
              discard <| InputDescriptorView.requireApplication graph codes invocation.arrow ⟨otherOwner⟩
            let .ok (encoded, packet) := invocation.encode graph connection.generation
              | throwError "the complete object application could not encode"
            let .ok decoded := PointInvocation.decode packet
              | throwError "the application did not use the public point packet"
            unless decoded.operation == entry.applicationAddress && decoded.parameters.size == 2 &&
                (decoded.arrow.getObjValAs? String "ctor").toOption == some entry.applicationAddress &&
                (decoded.source.getObjValAs? String "ctor").toOption == some "objectProduct" do
              throwError "the application wire packet lost its selected owner or product source"
            for root in invocation.roots do
              let some actual := encoded.inputs.find? (·.path == root.path)
                | throwError "the application omitted an original scope root"
              unless exactInput actual.binding root.binding do
                throwError "the application encoded a replacement for an original scope root"
            let identity : DispatchIdentity := {
              manifestDigest := "object-application-scope-control", profileDigest := "no-providers",
              registration := {
                operation := entry.applicationAddress
                input := entry.applicationAddress
                backend := "scope-control" } }
            let .ok reservation ← transaction.reserve request.occurrence identity connection
                invocation.dependencies
              | throwError "the application could not retain its actual scope inputs"
            let scope ← RequestScope.issue kernel.ledger reservation graph encoded.slots encoded.inputs #[]
            try
              let evaluate : SourceEvaluation := fun cell _ current bound selections source =>
                kernel.run cell current bound source (selections := selections)
              let changed := { decoded with operation := otherOwner ++ "#application" }
              failAt .malformed do
                discard <| kernel.child evaluate request transaction reservation scope
                  (Json.mkObj [("op", toJson entry.applicationAddress), ("args", changed.encode)])
              let reference := fun index =>
                (ScopedReference.input #[.field "args", .index index]).encode
              let child : PointInvocation := {
                operation := entry.applicationAddress
                parameters := invocation.parameters.mapIdx fun index _ =>
                  (ScopedReference.input #[.field "args", .index 1, .index index]).encode
                arrow := reference 2
                domain := reference 3
                source := reference 4
                target := reference 5
                argument := reference 6 }
              let observed ← IO.mkRef false
              let evaluateChild : SourceEvaluation := fun cell _ current bound selections source => do
                let .app _ point := source.consumeMData
                  | return ← kernel.run cell current bound source (selections := selections)
                let some original := selections.findAt? current point.getAppFn
                  | return ← kernel.run cell current bound source (selections := selections)
                let original ← original.specialize point.getAppArgs
                let some (.named family actual) := original.pointRequest
                  | return ← kernel.run cell current bound source (selections := selections)
                unless (SelectedApplicationFamily.application family).exactlyMatches
                    (.application selected) do
                  throwError "the scoped application changed its original selected point family"
                for source in #[actual.domain, actual.source, actual.target, actual.point],
                    expected in #[invocation.domain, invocation.source, invocation.target, invocation.argument] do
                  let .fvar localId := source.consumeMData
                    | throwError "the scoped application replaced an original input"
                  let some binding := current.bindings.find? (·.expression.fvarId! == localId)
                    | throwError "the scoped application lost an original input's typed binder"
                  let some value := bound[binding.id]?
                    | throwError "the scoped application lost its retained input authority"
                  unless exactInput value expected do
                    throwError "the scoped application replaced an input by an equal value"
                observed.set true
                kernel.run cell current bound source (selections := selections)
              failAt .noImplementation do
                discard <| kernel.child evaluateChild request transaction reservation scope
                  (Json.mkObj [("op", toJson entry.applicationAddress), ("args", child.encode)])
              unless ← observed.get do
                throwError "the scoped application bypassed the shared typed source boundary"
            finally scope.retire
          finally discard <| transaction.abort
      unless (← kernel.dispatches.get).isEmpty do
        throwError "an application preparation control dispatched a mathematical provider"
    finally
      kernel.close
      owners.close connection.generation
  finally setEnv original



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← assumeSource empty "let input ∈ Fin(2)"
  let (entry, category) ← selectObject "Fin" (some "Sets")
  let some originalEntry := session.context.entries.find? (·.userName == `input)
    | throwError "the original point input was not retained"
  discard <| session.elaborateScoped Syntax.missing do
    let scope ← get
    let some binding := scope.context.bindings.find? (·.id == originalEntry.id)
      | liftM (m := TermElabM) <| throwError "the original point input was not retained"
    let input := binding.expression
    let selectedDomain ← mkAppM entry.declaration #[mkNatLit 2]
    let selectedDomain ← SourceReadM.select (← sourceReferenceAt
      (.named (.registered (.inl entry) category)) selectedDomain selectedDomain)
    let otherDomain ← mkAppM entry.declaration #[mkNatLit 3]
    let otherDomain ← SourceReadM.select (← sourceReferenceAt
      (.named (.registered (.inl entry) category)) otherDomain otherDomain)
    let domain ← inferType input
    let pointMap ← liftM (m := MetaM) <| withLocalDeclD `argument domain fun argument => do
      let function ← mkLambdaFVars #[argument] argument (usedOnly := false) (usedLetOnly := false)
      mkAppM ``TypeCat.ofHom #[function]
    let point ← retainSourcePoint pointMap { value := input }
    let some original := point.pointOrigin
      | liftM (m := TermElabM) <| throwError "the supplied point lost its original native domain"
    let scope ← get
    scope.context.withOriginalSources #[original.domain, selectedDomain] fun native => do
      checkRegisteredDomains native[0]! native[1]!
      unless ← isDefEq native[0]! native[1]! do
        throwError "the supplied point does not have its selected Fin(2) domain"
    let pair ← sourcePairPoint (fun source => SourceReadM.select source) point point
    let some retained := pair.pointOrigin
      | liftM (m := TermElabM) <| throwError "pairing erased the supplied generalized point"
    unless retained.domain == original.domain do
      liftM (m := TermElabM) <| throwError "pairing replaced the original nonterminal point domain"
    let applied := mkApp (← sourceSetFunction retained.point) input
    unless ← isDefEq applied (← mkAppM ``Prod.mk #[input, input]) do
      liftM (m := TermElabM) <| throwError "pairing changed the original point maps"
    let otherMap ← liftM (m := MetaM) <| withLocalDeclD `other otherDomain fun other => do
      let function ← mkLambdaFVars #[other] input (usedOnly := false) (usedLetOnly := false)
      mkAppM ``TypeCat.ofHom #[function]
    let otherPoint ← retainSourcePoint otherMap { value := input }
    let failed ← try
      discard <| sourcePairPoint (fun source => SourceReadM.select source) point otherPoint
      pure false
    catch _ => pure true
    unless failed do
      liftM (m := TermElabM) <| throwError "different supplied point domains were silently identified"
    SourceReadM.select pair




run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  let #[matrix] := state.objects.filter (·.id.raw == "obj.sets.matrices")
    | throwError "the existing matrix owner is not unique"
  let #[polynomial] := state.objects.filter (·.id.raw == "obj.sets.polynomials")
    | throwError "the existing polynomial owner is not unique"
  discard <| PointFamily.forApplication matrix
  rejected do discard <| PointFamily.forApplication { matrix with application := polynomial.application }
  let first : Registration := {
    operation := matrix.applicationAddress, input := matrix.applicationAddress, backend := "first" }
  let second := { first with backend := "second" }
  let wrongOwner := { first with input := polynomial.applicationAddress }
  let wrongPort := { first with operation := matrix.id.raw ++ "#application.extra" }
  let (manifest, refused) ← admitManifest {
    backends := #[{ name := "first", command := "/bin/cat" },
      { name := "second", command := "/bin/cat" }],
    registrations := #[first, second, wrongOwner, wrongPort] }
  unless manifest.registrations == #[first, second] && refused.size == 2 do
    throwError "application admission changed its exact owner, complete port or eligible alternatives"
  let all ← RealizationProfile.prepare manifest none
  failAt .ambiguousRealization do
    discard <| selectLift all manifest (.application matrix.id)
      matrix.applicationAddress #[matrix.applicationAddress]
  let registration := Json.mkObj [("operation", toJson first.operation),
    ("input", toJson first.input), ("backend", toJson first.backend)]
  let configuration := fun (owner : String) => Json.mkObj [
    ("format", toJson "cas-realization-profile/1"), ("id", toJson "application-control"),
    ("default", toJson "all"), ("rules", .arr #[Json.mkObj [
      ("target", Json.mkObj [("kind", toJson "application"), ("id", toJson owner)]),
      ("primitive_registrations", Json.mkObj [("mode", toJson "only"), ("entries", .arr #[registration])]),
      ("derivations", Json.mkObj [("mode", toJson "all")])]])]
  let frozen ← RealizationProfile.prepare manifest (some (configuration matrix.id.raw))
  unless (← selectLift frozen manifest (.application matrix.id)
      matrix.applicationAddress #[matrix.applicationAddress]) == first &&
      frozen.sha256.length == 64 && frozen.normalized == configuration matrix.id.raw do
    throwError "the frozen profile changed its exact application registration"
  rejected do
    discard <| RealizationProfile.prepare manifest (some (configuration polynomial.id.raw))

end CasRuntime.ObjectApplicationTests
