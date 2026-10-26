/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import LeanCategories.Catalogue.Registry.Computation
public import CasCatalogue.Language
public import CasCatalogue.Admission
public import CasCatalogue.FunctorActionData

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.ComputationDerivation

/-- A published computational address retains the kind of its mathematical family. -/
def reference? : Operation → Option ComputationRef
  | .operation entry => some (.operation entry.id)
  | .morphism entry => some (.morphism entry.id)
  | .functor entry | .functorMap entry => some (.functor entry.id)
  | .method entry => some (.method entry.id)
  | .construction entry _ => some (.construction entry.id)
  | _ => none

def address : ComputationRef → String
  | .operation id => id.raw
  | .morphism id => id.raw
  | .functor id => id.raw
  | .method id => id.raw
  | .construction id => id.raw

/-- A finite least fixed point of declared prerequisite support. A cyclic rule
alone adds nothing. This says only that some installed primitive families ground
a finite tree; the executor still checks every actual request form and supplier. -/
def grounded (entries : Array ComputationDerivationEntry)
    (direct : ComputationRef → Bool) (blocked : Array ComputationRef := #[]) :
    Array ComputationRef := Id.run do
  let references := entries.foldl (fun refs entry =>
    refs ++ #[entry.target] ++ entry.prerequisites) #[]
  let mut available := references.foldl (fun refs reference =>
    if direct reference && !refs.contains reference then refs.push reference else refs) #[]
  for _ in [:entries.size] do
    let previous := available
    for entry in entries do
      if !blocked.contains entry.target && !available.contains entry.target &&
          entry.prerequisites.all available.contains then
        available := available.push entry.target
    if available.size == previous.size then break
  return available

/-- Only administrative wrappers are removed. No mathematical definition is
unfolded to discover an implementation or manufacture a returned value. -/
def applicationBody (value : Expr) : Expr := Id.run do
  let mut value := value.consumeMData
  while value.isAppOfArity ``id 2 || value.isAppOfArity ``Trace.operationResult 3 do
    value := value.appArg!.consumeMData
  return value

/-- The original ordered argument spine of a complete categorical application. -/
partial def applicationSpine (value : Expr) : Array Expr × Expr :=
  let value := applicationBody value
  if value.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    let (arguments, operation) := applicationSpine value.getAppArgs[6]!
    (#[value.getAppArgs[5]!] ++ arguments, operation)
  else (#[], value)

def closed (value : Expr) : Bool :=
  !value.hasMVar && !value.hasLevelMVar && !value.hasFVar && !value.hasLooseBVars

def checkClosed (value : Expr) : TermElabM Unit := do
  unless closed value && (← isTypeCorrect value) do
    throwError "a computational derivation lost its complete checked expression"

def same (expected actual : Expr) : TermElabM Unit := do
  checkClosed expected
  checkClosed actual
  unless ← withoutModifyingState <| withTransparency .all <|
      isDefEq (← inferType expected) (← inferType actual) <&&> isDefEq expected actual do
    throwStratum .noImplementation
      "the formal derivation requires a composition outside the existing closed reader"

/-- A transparent marker carries an exact upstream prerequisite address. It has
no mathematical content and is never supplied by a computational reply. -/
structure Slot where
  reference : ComputationRef
  declaration : Name
  family : Expr
  marker : Expr
  arity : Nat

structure Instance where
  entry : ComputationDerivationEntry
  application : Expr
  original : Expr
  expanded : Expr
  identity : Expr
  slots : Array Slot

/-- Specialize only a previously checked whole-family equality, at the exact
complete application retained by request preparation. The enclosing expression
is an ordinary congruence context; no result data participate in specialization. -/
def instantiate (checked : CheckedComputationDerivation) (application original : Expr) :
    TermElabM Instance := do
  checkClosed application
  checkClosed original
  unless application.getAppFn.isConstOf checked.targetDeclaration do
    throwError "the derivation target changed its original published family"
  let levels := application.getAppFn.constLevels!
  unless levels.length == checked.universeParams.length do
    throwError "the derivation target lost its complete universe application"
  let specialize := fun value : Expr => value.instantiateLevelParams checked.universeParams levels
  let target := specialize checked.target
  let arity ← forallTelescopeReducing (← inferType target) fun arguments _ => pure arguments.size
  unless application.getAppNumArgs == arity do
    throwError "the derivation target lost its complete dependent telescope"
  unless application.getAppFn == target do
    throwError "the derivation target changed its exact declaration or universes"
  let mut slots : Array Slot := #[]
  for (prerequisite, index) in checked.prerequisites.zipIdx do
    let family := specialize prerequisite.family
    let marker ← mkAppM ``Trace.operationResult
      #[toExpr s!"derivation:{checked.entry.id.raw}:{index}:{address prerequisite.reference}", family]
    let arity ← forallTelescopeReducing (← inferType family) fun arguments _ => pure arguments.size
    slots := slots.push {
      reference := prerequisite.reference
      declaration := prerequisite.declaration
      family := family
      marker := marker
      arity := arity }
  let family := (mkAppN (specialize checked.template) (slots.map (·.marker))).headBeta
  let body := (mkAppN family application.getAppArgs).headBeta
  checkClosed body
  let mut identity := specialize checked.correctness
  for argument in application.getAppArgs do identity ← mkCongrFun identity argument
  unless ← Decide.kernelAccepts (← mkEq body application) identity do
    throwError "the derivation failed its complete specialized family identity"
  unless (original.find? (· == application)).isSome do
    throwError "the original request does not retain its selected family application"
  withLocalDeclD `_derivedFamily (← inferType application) fun replacement => do
    let context := original.replace fun expression =>
      if expression == application then some replacement else none
    let context ← mkLambdaFVars #[replacement] context
    let expanded := (mkApp context body).headBeta
    let identity ← mkCongrArg context identity
    unless ← Decide.kernelAccepts (← mkEq expanded original) identity do
      throwError "the derivation failed its original complete request identity"
    return { entry := checked.entry, application, original, expanded, identity, slots }

structure Call where
  reference : ComputationRef
  application : Expr
  result : Expr

structure Compiler where
  trace : Trace
  slots : Array Slot
  known : Array Expr
  knownObjects : Array Language.Value := #[]
  contexts : Array CategoryContext
  calls : IO.Ref (Array Call)

/-- Primitive markers are recognized by their complete expression, never by
parsing a spelling, comparing carrier types, or searching equal declarations. -/
def slotApplication? (compiler : Compiler) (value : Expr) : Option (Slot × Array Expr) := do
  let value := value.consumeMData.headBeta
  let arguments := value.getAppArgs
  let slot ← compiler.slots.find? fun slot =>
    value.getAppFn == slot.marker.getAppFn &&
      arguments.size == slot.marker.getAppNumArgs + slot.arity &&
      arguments.extract 0 slot.marker.getAppNumArgs == slot.marker.getAppArgs
  return (slot, arguments.extract slot.marker.getAppNumArgs arguments.size)

def containsSlot (compiler : Compiler) (value : Expr) : Bool :=
  (value.find? fun expression => compiler.slots.any (·.marker == expression)).isSome

def valueExpression : Language.Value → TermElabM Expr
  | .object value .. | .morphism value .. | .element value .. => pure value
  | _ => throwError "the formal derivation reader returned no complete value"

def contextFor (compiler : Compiler) (arrow source target : Expr) : TermElabM CategoryContext := do
  let mut candidates := compiler.contexts
  let state ← registryState
  for category in state.categories do
    let candidate ← withoutModifyingState do
      try
        let context ← CategoryContext.ofNamed category source
        CategoryContext.checkMorphism context arrow source target
        return some context
      catch error =>
        if Exception.interpretationKind error == .invalid then return none else throw error
    if let some candidate := candidate then
      unless candidates.any (· == candidate) do candidates := candidates.push candidate
  let mut compatible := #[]
  for context in candidates do
    let valid ← withoutModifyingState do
      try
        CategoryContext.checkMorphism context arrow source target
        return true
      catch error =>
        if Exception.interpretationKind error == .invalid then return false else throw error
    if valid && !compatible.any (· == context) then compatible := compatible.push context
  let some selected := compatible[0]?
    | throwStratum .noImplementation "the formal derivation has no complete accepted category context"
  for candidate in compatible do
    unless candidate.expression.syntacticEq selected.expression &&
        (← withoutModifyingState <| withTransparency .all <| isDefEq candidate.bundle selected.bundle) do
      throwStratum .ambiguousRealization "the formal derivation retains different complete category contexts"
  return selected

def knownValues (compiler : Compiler) : TermElabM (Array Language.Value) := do
  let state ← registryState
  let mut values := compiler.knownObjects
  for value in compiler.known do
    let some (.object id _) ← compiler.trace.node? value | continue
    let some entry := state.objects.find? (·.id == id) | continue
    let some category := state.categories.find? (·.id == entry.category) | continue
    discard <| CategoryContext.ofNamed category value
    values := values.push (Language.Value.object value category none none none)
  return values

mutual

/-- Compile only published calls and the existing structural expression forms.
The result is definitionally the supplied closed expression, annotated by the
same reader records used for an ordinary statement. -/
partial def compile (compiler : Compiler) (value : Expr) : TermElabM Expr := do
  checkClosed value
  if compiler.known.contains value then return value
  if !containsSlot compiler value && (← compiler.trace.node? value).isSome then return value
  let selected := value.consumeMData.headBeta
  if selected != value then
    let actual ← compile compiler selected
    same value actual
    return actual
  if selected.isAppOfArity ``id 2 then
    let actual ← compile compiler selected.appArg!
    same value actual
    return actual
  if let .letE _ _ argument body _ := selected then
    let actual ← compile compiler (body.instantiate1 argument)
    same value actual
    return actual
  if let some (action, receiver) := FunctorActionData.objectAction? selected then
    return ← compileAction compiler action receiver false
  if selected.isAppOfArity ``CategoryTheory.Functor.map 8 then
    return ← compileAction compiler selected.getAppArgs[4]! selected.appArg! true
  if selected.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    return ← compileAt compiler selected.getAppArgs[6]! selected.getAppArgs[5]!
  if selected.isAppOfArity ``CategoryTheory.CategoryStruct.id 3 then
    let object := selected.appArg!
    let object ← compileParameter compiler object
    let context ← contextFor compiler value object object
    Trace.record (some compiler.trace) value (.contextualIdentity context object)
    return value
  if let some (slot, arguments) := slotApplication? compiler selected then
    let arguments ← arguments.mapM (compileParameter compiler)
    let application := mkAppN slot.family arguments
    checkClosed application
    match slot.reference with
    | .operation _ | .morphism _ =>
      let some (source, _) := Language.homEnds? (← inferType application)
        | throwError "a published derivation callable lost its complete Hom type"
      let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
      let context ← contextFor compiler application source
        (Language.homEnds? (← inferType application)).get!.2
      Trace.record (some compiler.trace) identity (.contextualIdentity context source)
      let actual ← compileAt compiler selected identity
      same value actual
      return actual
    | .functor id =>
      let parameters ← (Language.explicitArguments slot.declaration application).run {}
      Trace.record (some compiler.trace) application (.functorParameter id parameters)
      return application
    | _ => return application
  let state ← registryState
  let objects := state.objects.filter (fun entry => selected.getAppFn.isConstOf entry.declaration)
  if objects.size == 1 && (← Semantic.recordNamedObject selected (some compiler.trace)) then
    return selected
  throwStratum .noImplementation
    m!"the formal derivation has no published closed expression reader for {selected.getAppFn}"

partial def compileParameter (compiler : Compiler) (value : Expr) : TermElabM Expr := do
  if containsSlot compiler value then return ← compile compiler value
  if compiler.known.contains value || (← compiler.trace.node? value).isSome then return value
  let state ← registryState
  let objects := state.objects.filter (fun entry => value.getAppFn.isConstOf entry.declaration)
  if objects.size == 1 then discard <| Semantic.recordNamedObject value (some compiler.trace)
  return value

partial def compileAt (compiler : Compiler) (arrow argument : Expr) : TermElabM Expr := do
  let arrow := arrow.consumeMData.headBeta
  if arrow.isAppOfArity ``id 2 then return ← compileAt compiler arrow.appArg! argument
  if let .letE _ _ value body _ := arrow then
    return ← compileAt compiler (body.instantiate1 value) argument
  if arrow.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    let first ← compileAt compiler arrow.getAppArgs[5]! argument
    let result ← compileAt compiler arrow.getAppArgs[6]! first
    same (← mkAppM ``CategoryTheory.CategoryStruct.comp #[argument, arrow]) result
    return result
  if let some (slot, arguments) := slotApplication? compiler arrow then
    if slot.reference matches .operation _ | .morphism _ then
      let arguments ← arguments.mapM (compileParameter compiler)
      let application := mkAppN slot.family arguments
      checkClosed application
      let argument ← compile compiler argument
      let some (source, _) := Language.homEnds? (← inferType application)
        | throwError "the primitive family lost its complete source"
      let state ← registryState
      let (category, arity, operation, callable) :
          NamedCategoryEntry × Nat × Option OperationId × Option String ← match slot.reference with
        | .operation id => do
          let some entry := state.operations.find? (·.id == id)
            | throwError "the derivation prerequisite is no longer published"
          let some category := state.categories.find? (·.id == CategoryId.sets)
            | throwError "the primitive operation has no declared data category"
          pure (category, entry.arity, some id, none)
        | .morphism id => do
          let some entry := state.morphisms.find? (·.id == id)
            | throwError "the derivation prerequisite is no longer published"
          let some category := state.categories.find? (·.id == entry.category)
            | throwError "the primitive morphism has no complete category"
          pure (category, 1, none, some id.raw)
        | _ => unreachable!
      -- The primitive's whole application fixes its structured parameters.
      -- An unrelated original request object must not acquire another route
      -- merely because the derived operation uses an equal carrier.
      let known := (← knownValues compiler).filter fun
        | .object value .. => arguments.contains value
        | _ => false
      let result ← (do
        let known ← match operation with
          | some id => do
            let some entry := state.operations.find? (fun (entry : OperationEntry) => entry.id == id)
              | unreachable!
            Language.operationParameterObjects entry application known
          | none => Language.completeParameterObjects arguments known
        let sourceValue ← Language.declaredEndpointObject source category known arguments
        let operand := Language.Value.element argument sourceValue
        let operands ← match arity with
          | 0 => pure #[]
          | 1 => pure #[operand]
          | count => do
            if count == 2 then
              if let some (.productMediator _ _ _ left right) ← compiler.trace.node? argument then
                #[left, right].mapM fun point => do
                  let some (_, endpoint) := Language.homEnds? (← inferType point)
                    | throwError "the original paired argument lost a complete endpoint"
                  let target ← Language.declaredEndpointObject endpoint category known arguments
                  return Language.Value.element point target
              else Language.componentElements operand count
            else Language.componentElements operand count
        let result ← Language.applyFamily slot.declaration category operands
          (application := some application) (callableAddress := callable) (operationId := operation)
        valueExpression result).run { trace := some compiler.trace }
      -- Keep the original whole argument, even when the reader decomposes its
      -- formal product to validate the operation's arity. Its actual runtime
      -- packet may differ from the value of that formal product.
      let original ← mkAppM ``CategoryTheory.CategoryStruct.comp #[argument, application]
      same original result
      Trace.alias (some compiler.trace) result original
      compiler.calls.modify (·.push { reference := slot.reference, application, result := original })
      return original
  let first ← compile compiler argument
  let second ← compile compiler arrow
  let some (source, middle) := Language.homEnds? (← inferType first)
    | throwError "the derived application lost its complete argument signature"
  let some (declaredSource, target) := Language.homEnds? (← inferType second)
    | throwError "the derived application lost its complete callable signature"
  same middle declaredSource
  let result ← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]
  let context ← contextFor compiler result source target
  Trace.record (some compiler.trace) result
    (.contextualComposition context first second source middle target)
  return result

partial def compileAction (compiler : Compiler) (action receiver : Expr) (morphism : Bool) :
    TermElabM Expr := do
  let mut action := action.consumeMData.headBeta
  while action.isAppOfArity ``id 2 || action.isAppOf ``CategoryTheory.Cat.Hom.toFunctor do
    action := action.appArg!.consumeMData.headBeta
  if action.isAppOfArity ``CategoryTheory.Functor.comp 8 ||
      action.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    let arguments := action.getAppArgs
    let first ← compileAction compiler arguments[arguments.size - 2]! receiver morphism
    return ← compileAction compiler arguments.back! first morphism
  let some (slot, arguments) := slotApplication? compiler action
    | throwStratum .noImplementation "the formal derivation action has no exact published prerequisite slot"
  let arguments ← arguments.mapM (compileParameter compiler)
  let application := mkAppN slot.family arguments
  checkClosed application
  let receiver ← compileParameter compiler receiver
  let parameters ← (Language.explicitArguments slot.declaration application).run {}
  let state ← registryState
  let result ← match slot.reference with
    | .functor id => do
      let some entry := state.functor? id
        | throwError "the derivation action is no longer published"
      let actualAction ← Semantic.asFunctor application
      if !morphism then
        let result ← Semantic.objOf actualAction receiver
        Trace.record (some compiler.trace) result (.functor id parameters receiver)
        pure result
      else do
        let (sourceBundle, targetBundle) ← functorCategoryBundles actualAction
        let source : CategoryContext := { expression := entry.source, bundle := sourceBundle }
        let target : CategoryContext := { expression := entry.target, bundle := targetBundle }
        let result ← Semantic.mapOf actualAction receiver
        Trace.record (some compiler.trace) result
          (.contextualRoute source target #[.functor id] #[application] receiver true)
        pure result
    | .construction id => do
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the derivation construction is no longer published"
      if !morphism then
        let result ← Semantic.objOf application receiver
        Trace.record (some compiler.trace) result (.construction id parameters receiver)
        pure result
      else do
        let some (source, target) := Language.homEnds? (← inferType receiver)
          | throwError "the derivation construction map lost its complete endpoints"
        let selected ← DirectConstruction.select entry (← parameters.mapM exprToSyntax) source
        same selected.functor (← Semantic.asFunctor application)
        let result ← DirectConstruction.map selected source target receiver
        Trace.record (some compiler.trace) result (.constructionMap id parameters source target receiver)
        pure result
    | .method id => do
      if morphism then
        throwStratum .noImplementation "the method prerequisite has no separate published map port"
      let some entry := state.methods.find? (·.id == id)
        | throwError "the derivation method is no longer published"
      let (result, _) ← Semantic.methodIn entry.name receiver entry.owner (some compiler.trace)
      let some (.method selected _ _ _) ← compiler.trace.node? result
        | throwStratum .noImplementation "the derivation method requires a separately retained prescribed lift"
      unless selected == id do
        throwError "the derivation method changed its exact published address"
      same (← Semantic.objOf application receiver) result
      pure result
    | _ => throwError "a derivation functor action names a callable prerequisite"
  compiler.calls.modify (·.push { reference := slot.reference, application, result })
  return result

end

end CasCatalogue.ComputationDerivation
