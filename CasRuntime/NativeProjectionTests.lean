module

import CasRuntime.Session
import CasCompiler.SourceLimit
import CasCompiler.SourceCarrier
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
import LeanCategories.Catalogue.Semantics.Algebra.Series
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.SourceLimit
meta import CasCompiler.SourceCarrier
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
meta import LeanCategories.Catalogue.Semantics.Algebra.Series

namespace CasRuntime.NativeProjectionTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue

private abbrev BindingKey := RuntimeId .value × Array (RuntimeId .association)

private def bindingKey (binding : ValueBinding) : BindingKey :=
  (binding.value, binding.associationIds)

private def sameContext (left right : ContextTelescope) : Bool :=
  left.entries.size == right.entries.size &&
    (left.entries.zip right.entries).all (fun (left, right) =>
      left.id == right.id && left.role == right.role && left.userName == right.userName &&
        left.binderInfo == right.binderInfo && left.kind == right.kind &&
        left.type == right.type && left.value == right.value &&
        left.originalSource == right.originalSource && left.nondep == right.nondep) &&
    left.instances.size == right.instances.size &&
    (left.instances.zip right.instances).all (fun (left, right) =>
      left.className == right.className && left.binding == right.binding)

private def sameSource (left right : ClosedTerm) : Bool :=
  left.expression == right.expression && left.type == right.type &&
    left.universeParams == right.universeParams && sameContext left.context right.context

private structure ProjectionFrame where
  field : Name
  source : ClosedTerm
  origin : ClosedTerm
  parameters : Array (Option BindingKey)
  captures : Array BindingKey
  operand : BindingKey
  occurrence : RuntimeId .occurrence



private def sameProjection (left right : ProjectionFrame) : Bool :=
  left.field == right.field && sameSource left.source right.source &&
    sameSource left.origin right.origin && left.parameters == right.parameters &&
    left.captures == right.captures

private def projectionFrame? (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (Option ProjectionFrame) := do
  let .project operand field := request.action | return none
  let some node := (← transaction.view).find operand.value | return none
  let .closure program captures := node.payload.data | return none
  let some (.term source _) := (← kernel.codes.get)[program]? | return none
  return some {
    field := field.projection
    source
    origin := node.origin.role.source
    parameters := node.origin.parameters.map (·.map bindingKey)
    captures := captures.map bindingKey
    operand := bindingKey operand
    occurrence := request.occurrence }




private partial def describeSpine (expression : Expr) : MetaM (Array String) := do
  if let .mdata _ body := expression then return ← describeSpine body
  if let some projection ← SourceProjection.ofExpr? expression then
    return #[s!"projection {projection.declaration}"] ++ (← describeSpine projection.parent)
  if expression.isApp then
    return #[s!"application ({expression.getAppNumArgs} arguments)"] ++
      (← describeSpine expression.getAppFn)
  return #[match expression with
    | .const name _ => s!"constant {name}"
    | .proj owner index _ => s!"native projection {owner}[{index}]"
    | .fvar id => s!"local {repr id}"
    | .bvar index => s!"bound variable {index}"
    | .mvar id => s!"metavariable {repr id}"
    | .lam name .. => s!"lambda {name}"
    | .forallE name .. => s!"forall {name}"
    | .letE name .. => s!"let {name}"
    | .sort level => s!"sort {repr level}"
    | .lit .. => "literal"
    | .app .. | .mdata .. => "unreachable outer expression"]

private def describeProjection (frame : ProjectionFrame) : MetaM MessageData := do
  let source ← frame.source.withOpen fun _ expression => ppExpr expression
  let sourceSpine ← describeSpine frame.source.expression
  let typeSpine ← describeSpine frame.source.type
  let origin ← if sameSource frame.source frame.origin then
      pure m!"same exact closed source, type and context"
    else do
      let shown ← frame.origin.withOpen fun _ expression => ppExpr expression
      let spine ← describeSpine frame.origin.expression
      let type ← describeSpine frame.origin.type
      pure m!"{shown}\norigin spine: {repr spine}\norigin type head: {repr type}\n\
        origin context: {repr (frame.origin.context.entries.map (·.id))}"
  return m!"field: {frame.field}\noperand: {repr frame.operand}\n\
    occurrence: {repr frame.occurrence}\nsource: {source}\n\
    source spine: {repr sourceSpine}\nsource type head: {repr typeSpine}\n\
    source context: {repr (frame.source.context.entries.map (·.id))}\n\
    origin: {origin}\nparameters: {repr frame.parameters}\ncaptures: {repr frame.captures}"

private structure ProjectionGuard where
  active : IO.Ref (Array ProjectionFrame)
  demands : IO.Ref Nat

mutual



private partial def evaluateBounded (kernel : Kernel) (guard : ProjectionGuard) : SourceEvaluation :=
  fun transaction program context bound selections expression =>
    lowerTerm {
      ledger := kernel.ledger, transaction, codes := kernel.codes
      run := fun computation => Execute.run (executeBounded kernel guard) computation transaction
        (some (kernel.resolveFixedInput (evaluateBounded kernel guard) transaction program)) }
      program context bound expression (selections := selections)

private partial def executeBounded (kernel : Kernel) (guard : ProjectionGuard) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    let count ← guard.demands.get
    guard.demands.set (count + 1)
    let active ← guard.active.get
    let frame ← projectionFrame? kernel request transaction
    if let some frame := frame then
      if let some prior := active.find? (sameProjection · frame) then
        throwError "a native projection re-entered its active source computation\n\
          earlier:\n{← describeProjection prior}\nrepeated:\n{← describeProjection frame}"
      guard.active.set (active.push frame)
    try


      if count ≥ 256 then
        let detail ← match frame with
          | some frame => describeProjection frame
          | none => pure m!"the current demand is not a native term projection"
        throwError "the native projection diagnostic exceeded 256 demands\n{detail}"
      return (← kernel.execute (evaluateBounded kernel guard) request transaction, transaction)
    finally guard.active.set active

end


private partial def underBindings : Expr → Expr
  | .letE _ _ value body _ => underBindings (body.instantiate1 value)
  | .mdata _ body => underBindings body
  | expression => expression

private def expectMissing (text operation : String) (action : MetaM ValueBinding) : MetaM Unit := do
  let failure : Option Exception ← try
    discard <| action
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "`{text}` unexpectedly computed without a leaf"
  unless failure.toMessageData.hasTag (· == Stratum.noImplementation.tag) do
    throwError "`{text}` failed before its original published boundary:\n{failure.toMessageData}"
  let detail ← failure.toMessageData.toString
  unless (detail.splitOn operation).length > 1 do
    throwError "`{text}` did not reach {operation}: {detail}"



private def checkQuestion (source : SourceSession) (kernel : Kernel) (text operation : String)
    (evaluate : CellTransaction → OpenContext → SourceSelectionScope Expr → Expr →
      MetaM ValueBinding) : TermElabM Unit :=
  withCurrHeartbeats <|
  withTheReader Core.Context (fun context =>
    { context with maxHeartbeats := statementHeartbeats * 1000 }) do
    let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
      | .ok statement => pure statement
      | .error error => throwError "the original projection question did not parse: {error}"
    let .question proposition ← source.readStatement ⟨statement⟩
      | throwError "the original projection question did not read as a question"
    let transaction ← CellTransaction.begin kernel.ledger
    try
      proposition.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let selections ← proposition.selections.inContext context
        let asked := underBindings expression
        let some (_, left, _) := asked.eq?
          | throwError "the original projection question did not read as an equality"
        expectMissing text operation (evaluate transaction context selections left)
    finally discard <| transaction.abort




private def checkSelectedLimitProducer (source : SourceSession) (kernel : Kernel) :
    TermElabM Unit := do
  let .ok parsedSource := Parser.runParserCategory (← getEnv) `cas_term "cokernel(to_dual(1))"
    | throwError "the original cokernel producer source did not parse"
  let selected ← source.read ⟨parsedSource⟩
  let transaction ← CellTransaction.begin kernel.ledger
  try
    selected.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let selections ← selected.selections.inContext context
      let value ← kernel.run transaction context {} expression (selections := selections)
      let identities := transaction.owners.identities
      let graph ← transaction.view
      withBindingContext graph context {} value fun context bound => do
        let selections ← SourceSelectionScope.merge selections
          (← value.role.selections.inContext context)
        let environment ← RuntimeEnvironment.captureBound identities.worker context bound graph
          (selections := selections)
        let some produced ← environment.declaredResultSource? context graph value
          | throwError "the selected limit lost its original declaration projection"
        let expectedPath := #[``CategoryTheory.Limits.ColimitCocone.cocone,
          ``CategoryTheory.Limits.Cocone.pt]
        unless produced.declaration == ``CasCatalogue.Limits.Registration.bilWFormCokernel &&
            produced.path == expectedPath && produced.position == 4 do
          throwError "the selected limit changed its complete native producer or actual input position"
        let some input ← environment.declaredInputAt? context graph
            produced.declaration produced.position value
          | throwError "the selected limit lost its original retained map slot"
        let some node := graph.find value.value
          | throwError "the selected limit descriptor is outside its actual graph"
        let .container packet := node.payload.data
          | throwError "the selected limit lost its original descriptor"
        let #[slot] := packet.slots
          | throwError "the selected limit changed its sole actual packet input"
        unless slot.path == #[.field "args", .index 0] && slot.fieldIndex.isNone &&
            slot.binding.value == input.value.value &&
            slot.binding.associationIds == input.value.associationIds do
          throwError "the selected limit reconstructed its original producer input"
        let some category := selected.category
          | throwError "the selected limit lost its original category"
        let families ← RoutedMethodFamily.atSource category.expression "cardinality"
        let some family := families[0]?
          | throwError "the selected limit lost its original cardinality method family"
        let direct ← family.receiverParameterRoutes ``CategoryTheory.Limits.Cocone.pt
        unless direct.all (fun route => match route with | .unavailable => true | _ => false) do
          throwError "a generic apex accessor fabricated a concrete category parameter route"
        let routes ← family.receiverProjectionInputRoutes produced.declaration produced.path
          produced.position ``LeanCategories.Lattices.Integral.rootAToDual
        let #[.fixed scalar, .fixed dictionary] := routes
          | throwError "the whole original producer families did not fix their declared scalar category"
        unless (← isDefEq scalar (Lean.mkConst ``Int)) &&
            (← isDefEq (← inferType dictionary) (← mkAppM ``CommRing #[Lean.mkConst ``Int])) do
          throwError "the whole original producer families changed their fixed scalar category"
        checkWithKernel dictionary

        let some originalSelection ← value.role.selected? context
          | throwError "the original cokernel source lost its selected reference"
        let some (.limit originalRow) := originalSelection.reference
          | throwError "the original cokernel source changed its selected reference kind"
        unless originalRow.declaration == produced.declaration do
          throwError "the selected source changed its original complete limit row"
        let bareRole ← SourceLayout.ofTerm (← context.close originalSelection.value)
        let bareOrigin ← environment.origin node.origin.program (← identities.fresh .occurrence)
          bareRole
        let bare ← transaction.stage bareOrigin node.payload
        if (← environment.declaredResultSource? context (← transaction.view) bare).isSome then
          throwError "an unselected equal apex recovered a declaration from the registry"



        let some inputNode := graph.find input.value.value
          | throwError "the original producer input is outside its actual graph"
        let otherOccurrence ← identities.fresh .occurrence
        let other ← transaction.stage
          { inputNode.origin with occurrence := otherOccurrence } inputNode.payload
        if other.value == input.value.value then
          throwError "the distinct producer-input control reused its original occurrence"
        let original ← produced.source.inContext context
        let inputSource ← input.source.inContext context
        let allocated ← identities.fresh .sourceBinding
        let retainedId : BindingId := ⟨allocated.worker, allocated.serial⟩
        context.withLocalBinding retainedId .result `originalMap (← inferType inputSource)
            (fun context binding => do
          let bound := bound.insert binding.id input.value
          let retainedProducer := mkAppN original.getAppFn
            (original.getAppArgs.set! produced.position binding.expression)
          let some construction := originalSelection.limit
            | throwError "the original selected producer lost its complete construction"
          let some ownerSource := construction.source.ownerFamily
            | throwError "the selected construction lost its original owner template"
          let owner ← SelectedLimitOwner.ofBinding context selections ownerSource
          let some family := originalSelection.limitFamily
            | throwError "the original selected producer lost its complete limit family"
          let some rebound ← LimitFamily.formalAt family context construction owner
              retainedProducer.getAppArgs
            | throwError "the original selected construction could not retain its exact input binder"
          unless rebound.source.presentation.equal retainedProducer do
            throwError "the selected producer changed its exact retained application"
          let retainedSelection := { originalSelection with
            value := rebound.receiver, limit := some rebound,
            originalApplication := some retainedProducer,
            category := originalSelection.category.map
              (fun category => { category with limit := some rebound.source }) }
          selections.withBinding identities context retainedSelection
              fun context selections retainedApex => do
            let some selectedBinding := context.bindings.find?
                (·.expression == retainedApex)
              | throwError "the selected producer lost its original typed source binder"
            let environment ← RuntimeEnvironment.captureBound identities.worker context bound
              (← transaction.view) (selections := selections)
            let retainedRole ← SourceLayout.ofTerm (← context.close retainedApex)
              (← selections.close context) (some selectedBinding.id)
            let correctOrigin ← environment.origin node.origin.program
              (← identities.fresh .occurrence) retainedRole
            let correct ← transaction.stage correctOrigin node.payload
            let some correctInput ← environment.declaredInputAt? context (← transaction.view)
                produced.declaration produced.position correct
              | throwError "the correctly retained producer lost its original input"
            unless correctInput.value.value == input.value.value &&
                correctInput.value.associationIds == input.value.associationIds do
              throwError "the correctly retained producer changed its actual original input"

            let payload ← IO.ofExcept <| (ValuePayload.descriptor packet.template
              #[{ slot with binding := other }]).mapError IO.userError
            let changedOrigin ← environment.origin node.origin.program
              (← identities.fresh .occurrence) retainedRole
            let changed ← transaction.stage changedOrigin payload
            let failure : Option Exception ← try
                discard <| environment.declaredInputAt? context (← transaction.view)
                  produced.declaration produced.position changed
                pure none
              catch error => pure (some error)
            let some failure := failure
              | throwError "the selected producer accepted a different equal original input"
            unless failure.toMessageData.hasTag
                (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do throw failure



            unless !original.equal retainedProducer &&
                (← context.withOriginalSources #[original, retainedProducer]
                  fun sources => isDefEq sources[0]! sources[1]!) do
              throwError "the mismatched producer control lost its equal distinct native sources"
            let forgedSelection := { retainedSelection with originalApplication := some original }
            selections.withBinding identities context forgedSelection
                fun context selections forgedSource => do
              let some forgedBinding := context.bindings.find?
                  (·.expression == forgedSource)
                | throwError "the mismatched producer lost its typed source binder"
              let environment ← RuntimeEnvironment.captureBound identities.worker context bound
                (← transaction.view) (selections := selections)
              let forgedRole ← SourceLayout.ofTerm (← context.close forgedSource)
                (← selections.close context) (some forgedBinding.id)
              let forgedOrigin ← environment.origin node.origin.program
                (← identities.fresh .occurrence) forgedRole
              let forgedValue ← transaction.stage forgedOrigin node.payload
              let failure : Option Exception ← try
                  discard <| environment.declaredResultSource? context
                    (← transaction.view) forgedValue
                  pure none
                catch error => pure (some error)
              let some failure := failure
                | throwError "a definitionally equal but different producer witness was accepted"
              unless ((← failure.toMessageData.toString).splitOn
                  "changed its original producer application").length > 1 do throw failure)
          (originalSource := some inputSource)
  finally discard <| transaction.abort



private def checkRepeatedLimitSource (source : SourceSession) (kernel : Kernel) :
    TermElabM Unit := do
  let function ← source.elaborateScoped Syntax.missing <|
    SourceReadM.withBinder `X (mkSort (Level.succ Level.zero)) none .default
      (fun binding body => mkLambdaFVars #[binding.expression] body) fun input => do
        let object ← sourceSetJudgement .object input
        let product ← sourceBinaryLimit object object false
        return product.value
  let readObject := fun text => do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the repeated construction's original object source did not parse"
    source.read ⟨parsed⟩
  let first ← readObject "Fin(2)"
  let second ← readObject "Fin(3)"
  let transaction ← CellTransaction.begin kernel.ledger
  try
    function.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let selections ← function.selections.inContext context
      let selection ← lambdaTelescope expression fun _ body => do
        let some selectedConstruction := selections.findAt? context body.getAppFn
          | throwError "the compiled construction lost its original source anchor"
        let some original := (← selectedConstruction.specialize body.getAppArgs).limit
          | throwError "the compiled construction lost its original source anchor"
        return original.source.construction
      let before := (← kernel.dispatches.get).size
      let callable ← kernel.run transaction context {} expression (selections := selections)
      withBindingContext (← transaction.view) context {} callable fun context bound => do
        let selections ← SourceSelectionScope.merge selections
          (← callable.role.selections.inContext context)
        let callableSource ← callable.selectedSource context
        withBoundValue kernel.ledger.owners.identities context bound callableSource callable
            fun context bound retainedCallable => do
          let mut receivers := #[]
          for input in #[first, first, second] do
            let receiver ← input.source.context.withInContext context fun context => do
              let selections ← SourceSelectionScope.merge selections
                (← input.selections.inContext context)
              let argument ← input.source.inContext context
              let receiver ← kernel.run transaction context bound
                (mkApp retainedCallable argument) (selections := selections)
              let some _ := (← transaction.view).find receiver.value
                | throwError "the repeated construction lost its actual receiver node"
              withBindingContext (← transaction.view) context bound receiver fun context _ => do
                let some retained ← receiver.role.selected? context
                  | throwError "the construction execution lost its original source selection"
                let some retained := retained.limit
                  | throwError "the construction execution lost its original source selection"
                unless retained.source.construction == selection do
                  throwError "the one compiled source lambda acquired another producer identity"
              return receiver
            receivers := receivers.push receiver
          let #[firstReceiver, equalReceiver, otherReceiver] := receivers
            | throwError "the repeated construction lost an actual source application"
          unless firstReceiver.value != equalReceiver.value &&
              firstReceiver.value != otherReceiver.value &&
              equalReceiver.value != otherReceiver.value do
            throwError "the compiled construction merged distinct actual applications"
          let field := `occurrenceProbe
          let .ok () ← transaction.bindSelectedAt selection field firstReceiver firstReceiver
            | throwError "the first actual source receiver could not retain its selection"
          for unrelated in #[equalReceiver, otherReceiver] do
            let .ok none ← transaction.selectedAt selection field unrelated
              | throwError "a compiled source selection crossed an actual receiver boundary"
            let .ok () ← transaction.bindSelectedAt selection field unrelated unrelated
              | throwError "another source application could not retain its own occurrence"
          let .ok (some selected) ← transaction.selectedAt selection field firstReceiver
            | throwError "the first actual source occurrence lost its original selection"
          unless bindingKey selected == bindingKey firstReceiver do
            throwError "a later application replaced the first exact receiver selection"
          unless (← kernel.dispatches.get).size == before do
            throwError "forming the original symbolic constructions demanded an implementation"
  finally discard <| transaction.abort

run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let source ← SourceSession.empty owners.identities
    let cases := #[
      ("assert |cokernel(to_dual(1))| = 2", "fun.bil_wform.carrier"),
      ("assert |Fin(2) ⊔ Fin(3)| = 5", "meth.cardinality")]
    try
      checkSelectedLimitProducer source kernel
      checkRepeatedLimitSource source kernel


      let context ← ContextTelescope.capture #[]
      let info ← getConstInfo ``LeanCategories.Algebra.associative
      let classifier := Lean.mkConst info.name (info.levelParams.map (fun _ => Level.zero))
      let total ← mkAppM ``LeanCategories.Classifier.total #[classifier]
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[total]
      for bounded in #[true, false] do
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let before := (← kernel.dispatches.get).size
          let value ← if bounded then do
              let guard : ProjectionGuard := ⟨← IO.mkRef #[], ← IO.mkRef 0⟩
              let program ← owners.identities.fresh .program
              evaluateBounded kernel guard transaction program context {} {} carrier
            else kernel.run transaction context {} carrier
          let some node := (← transaction.view).find value.value
            | throwError "the native classifier carrier is outside its actual graph"
          if let .closure .. := node.payload.data then
            throwError "the native classifier carrier retained unevaluated projection code"
          unless ← isDefEq (← node.origin.role.source.inContext context) carrier do
            throwError "the nested native projection changed its declared carrier"
          unless (← kernel.dispatches.get).size == before do
            throwError "a nested native definition projection dispatched a computation"
        finally discard <| transaction.abort
      for (text, operation) in cases do
        let guard : ProjectionGuard := ⟨← IO.mkRef #[], ← IO.mkRef 0⟩
        checkQuestion source kernel text operation fun transaction context selections expression => do
          let program ← owners.identities.fresh .program
          evaluateBounded kernel guard transaction program context {} selections expression

      for (text, operation) in cases do
        checkQuestion source kernel text operation fun transaction context selections expression =>
          kernel.run transaction context {} expression (selections := selections)
    finally kernel.close
  finally setEnv environment

end CasRuntime.NativeProjectionTests
