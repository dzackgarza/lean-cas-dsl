module

import CasRuntime.ConstructorPorts
import CasRuntime.Transaction
import CasRuntime.Association
import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasRuntime.ConstructorPorts
meta import CasRuntime.Transaction
meta import CasRuntime.Association
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

open Lean Meta Elab Term CasCompiler CasRuntime CasCatalogue

private def constructorPortNative (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the original native constructor parameter did not parse"
  return ⟨parsed⟩

private def constructorPortSource (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original public construction did not parse"
  return ⟨parsed⟩

-- Actual accepted product and pullback constructors preserve native/proof slot order.
-- Equal endpoint packets at distinct original bindings never identify those endpoints.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    discard <| SessionSnapshot.initialize owners
    let supplier ← owners.spawn { cmd := "/bin/cat" }
    try
      let source ← SourceSession.empty owners.identities
      let source ← source.assume `X (← constructorPortNative "Type")
      let source ← source.assume `Y (← constructorPortNative "Type")
      for (text, proofExpected) in #[
          ("X × Y", false), ("pullback(id(X), id(X))", true)] do
        let construction ← source.read (← constructorPortSource text)
        let some category := construction.category
          | throwError "the public construction lost its original category"
        let some selected := category.limit
          | throwError "the public construction lost its accepted native constructor"
        let fresh : MetaM BindingId := do
          let id ← liftM (m := BaseIO) <| owners.identities.fresh .sourceBinding
          return ⟨id.worker, id.serial⟩
        let plan ← ConstructorPorts.prepare selected.interface fresh
        unless plan.context.entries.size == plan.originalContext.entries.size + plan.ports.size do
          throwError "constructor preparation dropped part of its complete native telescope"
        let mut wire := 0
        let mut seen : Std.HashSet BindingId := {}
        for port in plan.ports, index in [:plan.ports.size] do
          unless port.argument.sourceIndex == index && !seen.contains port.binding do
            throwError "constructor ports merged original bindings or reordered native positions"
          seen := seen.insert port.binding
          if let some actual := port.argument.wireIndex then
            unless actual == wire do throwError "constructor wire order replaced native source order"
            wire := wire + 1
          port.argument.typeFamily.withOpen fun _ family => do
            lambdaTelescope family fun previous _ => do
              unless previous.size == index do
                throwError "a constructor port erased an earlier native or proof binder"
        unless plan.ports.any (·.argument.wireIndex.isNone) == proofExpected do
          throwError "the original proof-port control lost its native telescope"
        let some apex ← plan.projectionAt #[``CategoryTheory.Limits.Cone.pt]
          | throwError "the accepted constructor lost its source-authored apex route"
        let .argument apexIndex := apex.target
          | throwError "the accepted constructor replaced its apex data port"
        let some originalApexPort := plan.ports[apexIndex]?
          | throwError "the accepted constructor lost its original apex position"
        unless apex.path.isEmpty && originalApexPort.argument.wireIndex == some 0 do
          throwError "the accepted constructor changed its original apex supplier"
        if (← plan.projectionAt #[``CategoryTheory.Limits.Cone.π,
            ``CategoryTheory.NatTrans.app]).isSome then
          throwError "a matcher-defined cone leg was guessed from a data-port ordinal"

        construction.source.withOpen fun bindings _ => do
          let context ← ContextTelescope.capture bindings
          let program ← owners.identities.fresh .program
          let occurrence ← ledger.allocate
          let transaction ← CellTransaction.begin ledger
          try
            let packet := Lean.Json.mkObj [("ctor", toJson "finiteData"),
              ("args", .arr #[toJson "equal original endpoint data", .arr #[toJson (0 : Nat)]])]
            let mut parameters := #[]
            let mut endpoints : Array ValueBinding := #[]
            for binding in bindings do
              let role ← SourceLayout.ofTerm (← context.close binding.expression)
              let value ← transaction.stage
                { program, occurrence, role, parameters := Array.replicate bindings.size none }
                (.portable packet.compress.toUTF8)
              let parameter ← IO.ofExcept <|
                (RuntimeParameter.ofValue (← transaction.view) binding.id value).mapError IO.userError
              parameters := parameters.push parameter
              endpoints := endpoints.push value
            let #[firstEndpoint, secondEndpoint] := endpoints
              | throwError "the original endpoint fixture lost a declared binding"
            unless firstEndpoint.value != secondEndpoint.value &&
                bindings[0]!.id != bindings[1]!.id do
              throwError "equal-data endpoint controls lost their distinct original occurrences"
            let cone ← selected.cone.inContext context
            let function ← SourceLayout.ofTerm (← context.close
              (mkLambda `ignored .default (mkConst ``Nat) cone))
            let actualContext := endpoints.map some
            let callable ← transaction.stage
              { program, occurrence, role := function, parameters := actualContext }
              (.closure program endpoints)
            let dummyRole ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
            let dummy ← transaction.stage
              { program, occurrence, role := dummyRole, parameters := actualContext }
              (.portable "0".toUTF8)
            let graph ← transaction.view
            let actual ← IO.ofExcept <| (RuntimeArgument.ofValue graph 0 dummy).mapError IO.userError
            let request ← PreparedRequest.forApplication owners.identities program occurrence
              context callable #[dummyRole.source] #[actual] parameters (some graph)
            let initial ← ConstructorPortPrefix.prepare request graph plan
            let apexOrigin ← initial.origin request graph
            let apex ← transaction.stage apexOrigin (.portable packet.compress.toUTF8)
            let otherApex ← transaction.stage apexOrigin (.portable packet.compress.toUTF8)
            let graph ← transaction.view
            let mut nativePrefix ← initial.bind graph apex
            let otherPrefix ← initial.bind graph otherApex
            let mut first := true
            let mut last : Option ValueBinding := none
            while nativePrefix.current?.isSome do
              let some port := nativePrefix.current? | throwError "the original constructor cursor disappeared"
              let (domain, target) ← port.argument.source.source.withOpen fun locals value => do
                let (domain, target) ← categoricalPointEndpoints value
                let originalValue (endpoint : Expr) : MetaM ValueBinding := do
                  let .fvar id := endpoint.consumeMData
                    | throwError "the constructor endpoint control changed its original native binder"
                  let some originalBinding := locals.find? (·.expression.fvarId! == id)
                    | throwError "the constructor endpoint lost its original BindingId"
                  let some actual ← IO.ofExcept <|
                      (nativePrefix.environment.lookup originalBinding.id).mapError IO.userError
                    | throwError "the constructor endpoint has no earlier actual supplier"
                  return actual
                return (← originalValue domain, ← originalValue target)
              let codec ← nativePrefix.mapCodec (← transaction.view) domain target
              unless codec.source.value == apex.value && codec.target.value == target.value do
                throwError "the map port replaced its original constructor/request endpoint"
              let wrong := if target.value == firstEndpoint.value then secondEndpoint else firstEndpoint
              let rejected ← try
                  discard <| nativePrefix.mapCodec (← transaction.view) domain wrong
                  pure false
                catch _ => pure true
              unless rejected do
                throwError "equal endpoint bytes replaced a different original request binding"
              supplier.child.stdin.putStr s!"constructor-port-{port.argument.sourceIndex}\n"
              supplier.child.stdin.flush
              let token := (← supplier.child.stdout.getLine).trimAscii.toString
              let origin ← nativePrefix.origin request (← transaction.view)
              let nativeMap ← transaction.stage origin (.ownedExport supplier token #[domain, target])
              let graph ← transaction.view
              if first then
                let rejected ← try
                    discard <| otherPrefix.bind graph nativeMap
                    pure false
                  catch _ => pure true
                unless rejected do
                  throwError "a map captured another equal-data constructor predecessor"
                first := false
              nativePrefix ← nativePrefix.bind graph nativeMap
              last := some nativeMap
            let values ← IO.ofExcept <| nativePrefix.finish.mapError IO.userError
            unless values.size == plan.ports.size && (values.filterMap id).size == wire do
              throwError "the completed constructor lost its full native/proof port table"
            for port in plan.ports, value in values do
              if port.argument.wireIndex.isNone && value.isSome then
                throwError "a formal constructor proof acquired a computational payload"
            -- The complete original table rejects a different equal-data apex before
            -- any native result association is created.
            let wrongValues := values.set! apexIndex (some otherApex)
            let wrongTableRejected ← try
                discard <| ConstructorPortPrefix.ofValues request (← transaction.view)
                  plan wrongValues
                pure false
              catch _ => pure true
            unless wrongTableRejected do
              throwError "a completed constructor accepted another actual predecessor"
            let missingRejected ← try
                discard <| ConstructorPortPrefix.ofValues request (← transaction.view)
                  plan (values.extract 0 (values.size - 1))
                pure false
              catch _ => pure true
            unless missingRejected do
              throwError "constructor transport accepted an incomplete native telescope"

            -- Consume the port through the original outer Cone interface, rather than
            -- admitting the port only inside the extra formal constructor scope.
            let admitted ← ConstructorPortPrefix.ofValues request (← transaction.view) plan values
            let before ← transaction.view
            let some originalNode := before.find apex.value
              | throwError "the original apex disappeared before outer-cone assembly"
            let some declaredPoint := request.source.fields.find?
                (·.projection == ``CategoryTheory.Limits.Cone.pt)
              | throwError "the original cone lost its declared apex position"
            let bareRejected ← try
                discard <| request.environment.checkResult before
                  (← declaredPoint.toLayout) apex
                pure false
              catch _ => pure true
            unless bareRejected do
              throwError "an untransported port escaped its original full native telescope"
            let draft ← transaction.draft
            let (draft, nativeApex) ← admitted.transportProjection request
              #[``CategoryTheory.Limits.Cone.pt] draft
            unless nativeApex.value == apex.value &&
                apex.associationIds.toList.isPrefixOf nativeApex.associationIds.toList do
              throwError "native cone transport replaced its original apex node or baseline"
            let some unchanged := draft.view.find apex.value
              | throwError "native cone transport dropped its original apex node"
            unless unchanged.origin.role.source.context.exactlyMatches
                originalNode.origin.role.source.context &&
                unchanged.origin.role.source.expression.equal
                  originalNode.origin.role.source.expression &&
                unchanged.origin.parameters.size == plan.context.entries.size do
              throwError "native cone transport rewrote or truncated the immutable producing scope"

            let coneLayout ← RecordLayout.ofSource request.source
            let #[pointField, transformationField] :=
                coneLayout.fields.filter (·.field.wireIndex.isSome)
              | throwError "the actual native cone changed its complete data interface"
            unless pointField.field.projection == ``CategoryTheory.Limits.Cone.pt do
              throwError "the native cone changed its source-prescribed apex field"
            let transformation ← RecordLayout.ofSource transformationField.layout
            let #[componentField] := transformation.fields.filter (·.field.wireIndex.isSome)
              | throwError "the native cone changed its component interface"
            let (draft, component) ← draft.stage
              (← request.originFor componentField.layout (some draft.view))
              (.closure program (values.filterMap id))
            let transPrefix ← RecordPrefix.prepare owners.identities program request.occurrence
              transformation draft.view request.environment.sourceMarks
            let (draft, transPrefix, _) ← draft.bindField transPrefix component
            let payload ← IO.ofExcept <| transPrefix.finish.mapError IO.userError
            let (draft, transformationValue) ← draft.stage
              (← request.originFor transformationField.layout (some draft.view)) payload
            let conePrefix ← RecordPrefix.prepare owners.identities program request.occurrence
              coneLayout draft.view request.environment.sourceMarks
            let (draft, conePrefix, nativeApex) ← draft.bindField conePrefix nativeApex
            let (draft, conePrefix, _) ← draft.bindField conePrefix transformationValue
            let payload ← IO.ofExcept <| conePrefix.finish.mapError IO.userError
            let (draft, coneValue) ← draft.stage
              (← request.originFor request.source (some draft.view)) payload
            let whole ← request.admitResult draft.view coneValue
            unless whole.root.value == coneValue.value do
              throwError "whole-cone admission replaced the returned result occurrence"
            let apexOwners ← IO.ofExcept <|
              (draft.view.requiredOwners #[nativeApex]).mapError IO.userError
            let coneOwners ← IO.ofExcept <|
              (draft.view.requiredOwners #[whole.root]).mapError IO.userError
            unless !apexOwners.contains supplier.generation &&
                coneOwners.contains supplier.generation do
              throwError "portable apex ownership was widened to the cone's retained legs"

            let projection ← PreparedRequest.forStoredProjection owners.identities program
              (← ledger.allocate) context draft.view whole.root
              #[``CategoryTheory.Limits.Cone.pt] parameters
            let (draft, access) ← projection.associateResult owners.identities projection.source
              draft nativeApex #[] (complete := true)
            discard <| projection.admitResult draft.view access
            let marks ← IO.mkRef (#[] : Array ValueBinding)
            let selectedCone ← markValue marks whole.root
              (← request.source.source.inContext context)
            let actualSource ← context.close (← mkProjection selectedCone `pt)
            let actual ← IO.ofExcept <|
              (RuntimeArgument.ofValue draft.view 0 access (← marks.get)).mapError IO.userError
            let consumed ← request.environment.checkArgument actualSource actual
            unless consumed.value == apex.value &&
                access.associationIds.toList.isPrefixOf consumed.associationIds.toList do
              throwError "the later native consumer lost the exact projected apex occurrence"
            let wrongConsumerRejected ← try
                let wrong ← IO.ofExcept <|
                  (RuntimeArgument.ofValue draft.view 0 otherApex (← marks.get)).mapError IO.userError
                discard <| request.environment.checkArgument actualSource wrong
                pure false
              catch _ => pure true
            unless wrongConsumerRejected do
              throwError "a later cone consumer accepted another equal-data apex"
            if proofExpected then
              owners.close supplier.generation
              unless ← draft.view.isAvailable owners nativeApex do
                throwError "an unrelated leg owner invalidated the portable apex"
              if ← draft.view.isAvailable owners whole.root then
                throwError "owner death left the complete owned-leg cone available"
            let some lastValue := last | throwError "the original construction had no retained map port"
            let rejected ← try
                discard <| nativePrefix.bind (← transaction.view) lastValue
                pure false
              catch _ => pure true
            unless rejected do throwError "a completed constructor accepted an extra data port"
          finally discard <| transaction.abort
    finally owners.close supplier.generation
  finally setEnv original
