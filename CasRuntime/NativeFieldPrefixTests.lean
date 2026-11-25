module

import CasRuntime.ResultCodec
import CasRuntime.NativeMapEndpoints
public meta import Lean.Elab.Command
meta import CasRuntime.ResultCodec
meta import CasRuntime.NativeMapEndpoints

namespace CasRuntime.NativeFieldPrefixTests

open Lean Meta CasCompiler

structure NativeMapRecord where
  domain : Type
  law : True
  target : Type
  arrow : domain → target

-- The whole W has no runtime binding. Only its actual earlier source-order fields
-- authorize the endpoint roles, including the intervening native proof position.
run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let program ← owners.identities.fresh .program
  let occurrence ← owners.identities.fresh .occurrence
  withLocalDeclD `W (mkConst ``NativeMapRecord) fun w => do
    let identity ← owners.identities.fresh .sourceBinding
    let context ← ContextTelescope.capture #[
      { id := ⟨identity.worker, identity.serial⟩, role := .result, expression := w }]
    let source ← SourceLayout.ofTerm (← context.close w)
    let layout ← RecordLayout.ofSource source
    let graph := ValueGraph.empty owners.identities
    let environment ← RuntimeEnvironment.capture owners.worker context #[] #[] (some graph)
    let checkAt := fun (label : String) (action : MetaM Unit) => do
      try action
      catch failure => throwError "native field prefix {label}: {failure.toMessageData}"
    let packet := Json.mkObj [("ctor", toJson "finiteData"),
      ("args", .arr #[toJson "same endpoint bytes", .arr #[toJson (0 : Nat)]])]
    let record ← RecordPrefix.prepare owners.identities program occurrence layout graph #[]
    let firstPrefix ← record.currentField
    let firstOrigin ← firstPrefix.origin environment program occurrence graph
    let (graph, first) ← graph.stage owners.identities firstOrigin
      (.portable packet.compress.toUTF8)
    let (graph, other) ← graph.stage owners.identities firstOrigin
      (.portable packet.compress.toUTF8)
    checkAt "domain" do discard <| firstPrefix.checkResult environment graph first
    let originalFirst := first
    let (graph, record, first) ← record.bind graph first
    let sibling ← RecordPrefix.prepare owners.identities program occurrence layout graph #[]
    let (graph, _, siblingFirst) ← sibling.bind graph originalFirst
    unless first.value == siblingFirst.value &&
        first.associationIds != siblingFirst.associationIds &&
        other.value != first.value do
      throwError "native prefix controls lost their original endpoint occurrences"

    let targetPrefix ← record.currentField
    let #[frame] := targetPrefix.frames
      | throwError "the native target prefix lost its original declaration"
    unless frame.field.sourceIndex == 2 && frame.preceding.size == 2 &&
        (frame.preceding[1]?.bind id).isNone do
      throwError "native prefix preparation erased or filled an original proof slot"
    let targetOrigin ← targetPrefix.origin environment program occurrence graph
    let (graph, target) ← graph.stage owners.identities targetOrigin
      (.portable packet.compress.toUTF8)
    checkAt "target" do discard <| targetPrefix.checkResult environment graph target
    let (graph, record, target) ← record.bind graph target

    let arrowPrefix ← record.currentField
    let globalMarks := #[first, target, other]
    let prepared ← try
        PreparedMapResult.forSource environment arrowPrefix.native graph
          first target globalMarks (fieldPrefix := some arrowPrefix)
      catch failure => throwError "native field prefix codec: {failure.toMessageData}"
    unless prepared.source.value == first.value && prepared.target.value == target.value &&
        prepared.source.associationIds == first.associationIds &&
        prepared.target.associationIds == target.associationIds do
      throwError "native map framing replaced an original preceding field"
    for wrong in #[other, siblingFirst, target] do
      let rejected ← try
          discard <| PreparedMapResult.forSource environment arrowPrefix.native graph
            wrong target globalMarks (fieldPrefix := some arrowPrefix)
          pure false
        catch _ => pure true
      unless rejected do
        throwError "native map framing accepted another equal-data endpoint occurrence"

    let rawOrigin ← environment.origin program occurrence arrowPrefix.native
    let wrongOccurrence ← owners.identities.fresh .occurrence
    let wrongOriginRejected ← try
        discard <| arrowPrefix.attachOrigin { rawOrigin with occurrence := wrongOccurrence } graph
        pure false
      catch _ => pure true
    unless wrongOriginRejected do
      throwError "a native prefix stamped a different original result occurrence"
    let (rawGraph, raw) ← graph.stage owners.identities rawOrigin
      (.closure program #[first, target])
    let rawRejected ← try
        discard <| arrowPrefix.checkResult environment rawGraph raw
        pure false
      catch _ => pure true
    unless rawRejected do
      throwError "a consuming prefix supplied missing original producer evidence"

    let origin ← arrowPrefix.attachOrigin rawOrigin graph
    let (graph, arrow) ← graph.stage owners.identities origin (.closure program #[first, target])
    checkAt "callable" do discard <| arrowPrefix.checkResult environment graph arrow
    checkAt "standalone retained operand" do
      let admitted ← environment.checkOperand graph arrowPrefix.native arrow
      unless admitted.root.value == arrow.value &&
          admitted.root.associationIds == arrow.associationIds do
        throwError "native input admission replaced its original standalone field"
    let some producing := graph.find arrow.value
      | throwError "the original native field producer disappeared"
    unless producing.origin.parameters.size == context.bindings.size &&
        producing.origin.parameters.all (·.isNone) &&
        producing.origin.role.source.expression.equal rawOrigin.role.source.expression do
      throwError "native prefix staging fabricated a parent or rewrote its producing source"
    let (graph, record, _) ← record.bind graph arrow
    let payload ← IO.ofExcept <| record.finish.mapError IO.userError
    let (graph, whole) ← graph.stage owners.identities
      (← environment.origin program occurrence source) payload
    let admitted ← try environment.checkResult graph source whole
      catch failure => throwError "native field prefix whole record: {failure.toMessageData}"
    let retained ← IO.ofExcept <| (graph.project admitted.root 2).mapError IO.userError
    unless retained.value == arrow.value &&
        arrow.associationIds.toList.isPrefixOf retained.associationIds.toList do
      throwError "whole native record admission replaced its original callable field"
    let rootParameter ← IO.ofExcept <|
      (RuntimeParameter.ofValue graph context.bindings[0]!.id admitted.root).mapError IO.userError
    let consumer ← RuntimeEnvironment.capture owners.worker context #[rootParameter] #[] (some graph)
    let consumed ← try consumer.checkResult graph arrowPrefix.native retained
      catch failure => throwError "native field prefix bound consumer: {failure.toMessageData}"
    unless consumed.root.value == arrow.value &&
        arrow.associationIds.toList.isPrefixOf consumed.root.associationIds.toList do
      throwError "a native field consumer replaced its original producing occurrence"
    for wrong in #[other, siblingFirst] do
      let (badGraph, bad) ← graph.stage owners.identities
        (← environment.origin program occurrence source)
        (.product #[wrong, target, arrow])
      let rejected ← try
          discard <| environment.checkResult badGraph source bad
          pure false
        catch _ => pure true
      unless rejected do
        throwError "whole native record admission replaced an original producer endpoint"
      let changedParentRejected ← try
          let parameter ← IO.ofExcept <|
            (RuntimeParameter.ofValue badGraph context.bindings[0]!.id bad).mapError IO.userError
          let changed ← RuntimeEnvironment.capture owners.worker context #[parameter] #[]
            (some badGraph)
          discard <| changed.checkResult badGraph arrowPrefix.native retained
          pure false
        catch _ => pure true
      unless changedParentRejected do
        throwError "a native field consumer accepted a different actual parent dependency"

    let (unframedGraph, unframed) ← rawGraph.stage owners.identities
      (← environment.origin program occurrence source) (.product #[first, target, raw])
    let unframedRejected ← try
        discard <| environment.checkResult unframedGraph source unframed
        pure false
      catch _ => pure true
    unless unframedRejected do
      throwError "whole native record admission supplied missing original field provenance"

    let checkRawRecord := fun (label : String) (nativeContext : OpenContext)
        (term : Expr) (accepted : Bool) => do
      let source ← SourceLayout.ofTerm (← nativeContext.close term)
      let layout ← RecordLayout.ofSource source
      let environment ← RuntimeEnvironment.capture owners.worker nativeContext #[] #[] (some graph)
      let mut currentGraph := graph
      let mut fields := #[]
      for prepared in layout.fields do
        unless prepared.field.wireIndex.isSome do continue
        let origin ← environment.origin program occurrence prepared.layout
        let payload : ValuePayload := if prepared.layout.kind == .function then
          .closure program fields else .portable packet.compress.toUTF8
        let (next, field) ← currentGraph.stage owners.identities origin payload
        currentGraph := next
        fields := fields.push field
      let (checkedGraph, whole) ← currentGraph.stage owners.identities
        (← environment.origin program occurrence source) (.product fields)
      let failure : Option Exception ← try
          discard <| environment.checkResult checkedGraph source whole
          pure none
        catch error => pure (some error)
      if accepted then
        if let some failure := failure then
          throwError "native field prefix {label}: {failure.toMessageData}"
      else unless failure.isSome do
        throwError "native field prefix {label} admitted an unresolved computational parent"
    let closed ← Elab.Term.elabTermAndSynthesize
      (← `(NativeMapRecord.mk (Fin 2) True.intro (Fin 2) (fun point => point))) none
    checkRawRecord "closed constructor" context closed true
    withLetDecl `closedRecord (mkConst ``NativeMapRecord) closed fun named => do
      let identity ← owners.identities.fresh .sourceBinding
      let nativeContext ← ContextTelescope.capture (context.bindings.push
        { id := ⟨identity.worker, identity.serial⟩, role := .definition, expression := named })
      checkRawRecord "closed definition" nativeContext named true
    withLocalDeclD `h (mkForall `input .default (mkConst ``NativeMapRecord)
        (mkConst ``NativeMapRecord)) fun function => do
      let identity ← owners.identities.fresh .sourceBinding
      let nativeContext ← ContextTelescope.capture (context.bindings.push
        { id := ⟨identity.worker, identity.serial⟩, role := .parameter, expression := function })
      checkRawRecord "open application" nativeContext (mkApp function w) false


structure NativeCallableRecord (domain target : Type) where
  apply : domain → target

structure NativeNestedMapRecord where
  domain : Type
  target : Type
  universal : NativeCallableRecord domain target

-- A standalone dependent record keeps its actual earlier fields when a later request
-- projects its callable. Another equal-source record cannot supply that continuation.
run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let program ← owners.identities.fresh .program
  let occurrence ← owners.identities.fresh .occurrence
  withLocalDeclD `W (mkConst ``NativeNestedMapRecord) fun w => do
    let identity ← owners.identities.fresh .sourceBinding
    let context ← ContextTelescope.capture #[
      { id := ⟨identity.worker, identity.serial⟩, role := .result, expression := w }]
    let source ← SourceLayout.ofTerm (← context.close w)
    let layout ← RecordLayout.ofSource source
    let graph := ValueGraph.empty owners.identities
    let environment ← RuntimeEnvironment.capture owners.worker context #[] #[] (some graph)
    let packet := (toJson "same native field packet").compress.toUTF8
    let makeRecord := fun (graph : ValueGraph) => do
      let record ← RecordPrefix.prepare owners.identities program occurrence layout graph #[]
      let domainPrefix ← record.currentField
      let (graph, domain) ← graph.stage owners.identities
        (← domainPrefix.origin environment program occurrence graph) (.portable packet)
      let (graph, record, domain) ← record.bind graph domain
      let targetPrefix ← record.currentField
      let (graph, target) ← graph.stage owners.identities
        (← targetPrefix.origin environment program occurrence graph) (.portable packet)
      let (graph, record, target) ← record.bind graph target
      let universalPrefix ← record.currentField
      let (graph, universal) ← graph.stage owners.identities
        (← universalPrefix.origin environment program occurrence graph)
        (.closure program #[domain, target])
      let admitted ← universalPrefix.checkResult environment graph universal
      return (graph, admitted.root)
    let (graph, first) ← makeRecord graph
    let (graph, second) ← makeRecord graph
    let prepareCallable := fun (graph : ValueGraph) (parent : ValueBinding) => do
      let request ← PreparedRequest.forProjection owners.identities program
        (← owners.identities.fresh .occurrence) context graph parent 0 #[] (some environment)
      let (graph, callable) ← graph.stage owners.identities
        (← request.originFor request.source (some graph)) (.closure program #[parent])
      return (graph, request, callable)
    let (graph, request, callable) ← prepareCallable graph first
    let accepted ← try request.admitResult graph callable
      catch failure => throwError "standalone dependent record projection: {failure.toMessageData}"
    unless accepted.root.value == callable.value do
      throwError "the native projection replaced its original callable occurrence"
    let (graph, _, other) ← prepareCallable graph second
    let rejected ← try
        discard <| request.admitResult graph other
        pure false
      catch _ => pure true
    unless rejected do
      throwError "a native projection accepted another equal-source record's callable"

end CasRuntime.NativeFieldPrefixTests
