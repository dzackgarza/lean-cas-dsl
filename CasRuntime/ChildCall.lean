module

public import CasRuntime.ExecutionContext
public import CasCompiler.PublishedSource
public import CasRuntime.Literal
public import CasRuntime.Encode
public import CasRuntime.RoutedMethod
public import CasRuntime.Property
public import CasRuntime.ConstructionSource

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend


private structure ChildSourceState where
  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  selections : SourceSelectionScope Expr



private partial def childReferences (packet : Json) : Except String (Array ScopedReference) := do
  if let some reference ← ScopedReference.parse? packet then return #[reference]
  let children : Array Json := match packet with
    | .arr values => values
    | .obj fields => fields.toList.toArray.map (fun (entry : String × Json) => entry.2)
    | _ => #[]
  let mut references := #[]
  for child in children do
    for reference in ← childReferences child do
      unless references.contains reference do references := references.push reference
  return references



private def boundSourceValue (transaction : CellTransaction) (state : ChildSourceState)
    (source : Expr) : MetaM ValueBinding := do
  let .fvar localId := source.consumeMData
    | throwError "the prepared source operand lost its actual bound variable"
  let some binding := state.context.bindings.find? (·.expression.fvarId! == localId)
    | throwError "the prepared source operand is outside its complete typed context"
  let some value := state.bound[binding.id]?
    | throwError "the prepared source operand names an unavailable bound identity"
  discard <| IO.ofExcept <| ((← transaction.view).requiredOwners #[value]).mapError IO.userError
  return value




partial def Kernel.child (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (call : Json) : MetaM ValueBinding := do
  let malformed : {α : Type} → MessageData → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred call {call.compress}: {reason}"
  let retained : Json → MetaM (Option ValueBinding) := fun packet => do
    match ScopedReference.parse? packet with
    | .error reason => malformed reason
    | .ok none => return none
    | .ok (some reference) =>
      let #[binding] ← scope.resolveMany reservation (← transaction.view) scope.wireId #[reference]
        | throwError "internal: one scoped reference resolved to several values"
      return some binding
  let references ← match childReferences call with
    | .ok references => pure references
    | .error reason => malformed reason
  let finish := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
      (sources : Array (ScopedReference × Expr)) => do
    let readRetained := fun (_state : ChildSourceState) packet => do
      match ScopedReference.parse? packet with
      | .error reason => malformed reason
      | .ok none => pure none
      | .ok (some reference) =>
        let some (_, source) := sources.find? (·.1 == reference)
          | throwError "the child source lost an explicit original wire reference"
        pure (some source)
    let environment := fun (state : ChildSourceState) => do
      RuntimeEnvironment.captureBound request.environment.worker state.context state.bound
        (← transaction.view) (some request.environment) state.selections
    let stateIn := fun (state : ChildSourceState) context bound => do
      let current ← environment { state with context, bound }
      return ({ context, bound, selections := ← current.selections.inContext context } :
        ChildSourceState)
    let readAction : Json → StateCpsT ChildSourceState Elab.Term.TermElabM
        (Option (ValueBinding × Expr)) := fun packet _ state continuation =>
      controlAt MetaM fun run => do
        let some value ← retained packet
          | run (continuation none state)
        withNativeInterface kernel.ledger.owners.identities (← transaction.view)
            state.context state.bound state.selections value
            fun context bound selections nativeSource => do
          let next ← stateIn { state with selections } context bound
          run (continuation (some (value, nativeSource)) next)
    let source : PublishedSourceContext ChildSourceState := {
      scope := (·.context)
      selections := (·.selections)
      identities := fun _ => kernel.ledger.owners.identities
      select := fun selection declaredType _ state continuation =>
        controlAt MetaM fun run => do
          SourceSelectionScope.withBinding kernel.ledger.owners.identities
            state.selections state.context selection
            (fun context selections sourceVariable =>
              run (continuation sourceVariable { state with context, selections }))
            (declaredType := declaredType)
      retained := readRetained
      actionSource := fun packet => do return (← readAction packet).map (·.2)
      literal := ScalarLiteral.readAt
      bind := fun term _ state continuation =>
        controlAt MetaM fun run => do
          let value ← evaluateSource transaction request.program state.context state.bound state.selections term
          withBindingContext (← transaction.view) state.context state.bound value fun context bound =>
            withBoundValue kernel.ledger.owners.identities context bound term value
              fun context bound sourceVariable => do
                let next ← stateIn state context bound
                let selections ← next.selections.alias context
                  (← value.selectedSource context) sourceVariable
                run (continuation sourceVariable { next with selections })
      bindAt := fun term declaredType _ state continuation =>
        controlAt MetaM fun run => do
          let value ← evaluateSource transaction request.program state.context state.bound state.selections term
          withBindingContext (← transaction.view) state.context state.bound value fun context bound =>
            withBoundValue kernel.ledger.owners.identities context bound term value
              (fun context bound sourceVariable => do
                let next ← stateIn state context bound
                let selections ← next.selections.alias context
                  (← value.selectedSource context) sourceVariable
                run (continuation sourceVariable { next with selections }))
              (declaredType := some declaredType)
      withLocal := fun _ _ _ _ _ =>
        throwError "a child source request cannot invent a symbolic interface"
      rebind := fun original selected _ state continuation =>
        controlAt MetaM fun run => do
          let value ← boundSourceValue transaction state selected
          withBoundValue kernel.ledger.owners.identities state.context state.bound original value
            fun context bound sourceVariable => do
                let next ← stateIn state context bound
                let selections ← next.selections.alias context
                  (← value.selectedSource context) sourceVariable
                run (continuation sourceVariable { next with selections })
      methodParameters := fun family parameters receiver _ state continuation =>
        controlAt MetaM fun run => do
          let receiver ← boundSourceValue transaction state receiver
          let environment ← environment state
          let continuing ← IO.mkRef false
          try
            environment.methodParameters state.context state.bound transaction kernel.ledger.allocate
              family parameters receiver
              (fun context bound selections expression => do
                let selections ← SourceSelectionScope.merge state.selections selections
                let current ← stateIn { state with selections } context bound
                evaluateSource transaction request.program context bound current.selections expression)
              (fun context bound selections parameters => do
                continuing.set true
                let selections ← SourceSelectionScope.merge state.selections selections
                let next ← stateIn { state with selections } context bound
                run (continuation parameters next))
              request.observation.sourceSnapshot
          catch error =>
            if ← continuing.get then throw error
            malformed m!"the original receiver's category inputs disagree: {error.toMessageData}"
      checkInput := fun state expected selected => do
        let value ← boundSourceValue transaction state selected
        try
          (← environment state).checkDeclaredInput state.context (← transaction.view) expected value
        catch error => malformed m!"a complete action parameter disagrees: {error.toMessageData}"
      admitMethod := fun state family receiver input => do
        unless ← CasRuntime.RoutedMethodFamily.admitsSourceForm
            state.context state.selections family receiver input do
          malformed "the input form is not the original receiver's source boundary"
      admitProperty := fun state family receiver input => do
        let some boundary := (← routedSourceBoundaries
            state.context state.selections family.route receiver)[0]?
          | malformed "the property lost its original source boundary"
        unless boundary.forms.contains input do
          malformed "the input form is not the original receiver's source boundary"
      admitPoint := fun state family selected => do
        let value ← boundSourceValue transaction state selected
        match family.owner with
        | .morphism row =>
          discard <| InputDescriptorView.requireMorphism (← transaction.view)
            (← kernel.codes.get) value row.id
        | .application row =>
          discard <| InputDescriptorView.requireApplication (← transaction.view)
            (← kernel.codes.get) value row.id
      admitCategorical := fun state family parameters selected => do
        let value ← boundSourceValue transaction state selected
        let graph ← transaction.view
        let view ← InputDescriptorView.requireCategorical graph (← kernel.codes.get) value family
        let some original := view.family
          | malformed "the categorical arrow lost its original source preparation"
        let values := original.origin.application.map (·.arguments) |>.getD #[]
        unless parameters.size == values.size do
          malformed "the categorical arrow changed its complete original parameter telescope"
        let environment ← environment state
        for expected in parameters, supplied in values do
          match supplied with
          | some actual => environment.checkDeclaredInput state.context graph expected actual
          | none =>
            unless ← isProof expected do
              malformed "the categorical arrow lost an original computational parameter"
      constructionCone := fun packet _ state continuation =>
        controlAt MetaM fun run => do
          kernel.retainedConstructionCone transaction (← transaction.view) state.context state.bound retained packet
            fun context bound selected => do
              let next ← stateIn state context bound
              run (continuation selected next)
      creationOwner := fun packet _ state continuation =>
        controlAt MetaM fun run => do
          kernel.retainedCreationOwner (← transaction.view) state.context state.bound retained packet
            fun context bound selected => do
              let next ← stateIn state context bound
              run (continuation selected next)
      projection := fun packet position => do
        let some (value, source) ← readAction packet
          | liftM (m := MetaM) <| malformed "the acted value must be a scoped reference"
        let some field := value.nativeRole.fields.find? (·.wireIndex == some position)
          | liftM (m := MetaM) <| malformed "the field is outside the prepared record interface"
        return (source, field.projection) }
    let selections ← SourceSelectionScope.merge (← request.selections.inContext context)
      (← request.environment.selections.inContext context)
    let initial ← stateIn { context, bound, selections } context bound
    Elab.Term.TermElabM.run' do
      Elab.Term.withSynthesize do
        (PublishedSource.prepare source call).runK initial fun term state =>
          evaluateSource transaction request.program state.context state.bound state.selections term
  withSourceScope request fun context bound => do
    let rec prepare (remaining : List ScopedReference) (context : OpenContext)
        (bound : Std.HashMap BindingId ValueBinding) (sources : Array (ScopedReference × Expr)) :
        MetaM ValueBinding := do
      match remaining with
      | [] => finish context bound sources
      | reference :: remaining =>
        let #[value] ← scope.resolveMany reservation (← transaction.view) scope.wireId #[reference]
          | throwError "internal: one scoped reference resolved to several values"
        withBindingContext (← transaction.view) context bound value fun context bound => do
          withBoundValue kernel.ledger.owners.identities context bound
              (← value.selectedSource context) value fun context bound source =>
            prepare remaining context bound (sources.push (reference, source))
    prepare references.toList context bound #[]

end CasRuntime
