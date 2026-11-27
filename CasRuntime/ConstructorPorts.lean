module

public import CasCompiler.ConstructorPorts
public import CasRuntime.PreparedRequest
public import CasRuntime.ResultCodec

public section

namespace CasRuntime

open Lean Meta CasCompiler




structure ConstructorPortPrefix (scope : RoleScope) where
  private mk ::
  plan : ConstructorPorts
  environment : RuntimeEnvironment
  private parameters : Array RuntimeParameter
  values : Array (Option ValueBinding)
  nextIndex : Nat

private def ConstructorPortPrefix.skipProofs (nativePrefix : ConstructorPortPrefix scope) :
    ConstructorPortPrefix scope := Id.run do
  let mut nextIndex := nativePrefix.nextIndex
  while nextIndex < nativePrefix.plan.ports.size do
    let some port := nativePrefix.plan.ports[nextIndex]? | break
    if port.argument.wireIndex.isSome then break
    nextIndex := nextIndex + 1
  return { nativePrefix with nextIndex }



opaque ConstructorPortPrefix.prepare (request : PreparedRequest) (graph : ValueGraph)
    (plan : ConstructorPorts) :
    MetaM (ConstructorPortPrefix request.roles.scope) := do
  unless plan.originalContext.exactlyMatches request.environment.context do
    throwError "the constructor ports changed their original prepared request context"
  unless request.environment.values.size == plan.originalContext.entries.size do
    throwError "the constructor ports lost the complete original context value table"
  let mut parameters := #[]
  for entry in plan.originalContext.entries, value in request.environment.values do
    if let some value := value then
      parameters := parameters.push (← IO.ofExcept <|
        (RuntimeParameter.ofValue graph entry.id value).mapError IO.userError)
  let environment ← plan.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    RuntimeEnvironment.capture request.program.worker context parameters
      (some graph) (selections := ← request.environment.selections.inContext context)
  return (⟨plan, environment, parameters, Array.replicate plan.ports.size none, 0⟩ :
    ConstructorPortPrefix request.roles.scope).skipProofs

def ConstructorPortPrefix.current? (nativePrefix : ConstructorPortPrefix scope) :
    Option ConstructorPort :=
  nativePrefix.plan.ports[nativePrefix.nextIndex]?



opaque ConstructorPortPrefix.origin (nativePrefix : ConstructorPortPrefix scope)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM ValueOrigin := do
  request.requirePreparation scope
  let some port := nativePrefix.current?
    | throwError "the complete constructor has no remaining computational data port"
  let environment ← nativePrefix.environment.withGraph (some graph)
  environment.origin request.program request.occurrence port.argument.source



opaque ConstructorPortPrefix.bind (nativePrefix : ConstructorPortPrefix scope)
    (graph : ValueGraph) (value : ValueBinding) : MetaM (ConstructorPortPrefix scope) := do
  let some port := nativePrefix.current?
    | throwError "a constructor reply supplied an extra computational data port"
  unless port.argument.sourceIndex == nativePrefix.nextIndex && port.argument.wireIndex.isSome do
    throwError "the constructor reply changed its original native port order"
  let candidate ← nativePrefix.environment.checkResult graph port.argument.source value
  let parameter ← IO.ofExcept <|
    (RuntimeParameter.ofValue graph port.binding candidate.root).mapError IO.userError
  let parameters := nativePrefix.parameters.push parameter
  let environment ← nativePrefix.plan.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    RuntimeEnvironment.capture nativePrefix.environment.worker context parameters
      (some graph) (selections := ← nativePrefix.environment.selections.inContext context)
  return ({ nativePrefix with
    environment := environment
    parameters := parameters
    values := nativePrefix.values.set! nativePrefix.nextIndex (some candidate.root),
    nextIndex := nativePrefix.nextIndex + 1 }).skipProofs



opaque ConstructorPortPrefix.finish (nativePrefix : ConstructorPortPrefix scope) :
    Except String (Array (Option ValueBinding)) := do
  let nativePrefix := nativePrefix.skipProofs
  unless nativePrefix.nextIndex == nativePrefix.plan.ports.size do
    throw "the constructor reply omitted a required dependent data port"
  for port in nativePrefix.plan.ports, value in nativePrefix.values do
    unless port.argument.wireIndex.isSome == value.isSome do
      throw "the constructor reply changed its original computational/proof port table"
  return nativePrefix.values



opaque ConstructorPortPrefix.mapCodec (nativePrefix : ConstructorPortPrefix scope)
    (graph : ValueGraph) (source target : ValueBinding)
    (operands : Array (ValueBinding × ValueBinding × ValueBinding) := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none) : MetaM PreparedMapResult := do
  let some port := nativePrefix.current?
    | throwError "the complete constructor has no remaining native map port"
  PreparedMapResult.forSource nativePrefix.environment port.argument.source graph source target
    none none none operands checkSymbolic




opaque _root_.CasCompiler.ConstructorPorts.projectionSupplier? (plan : ConstructorPorts)
    (environment : RuntimeEnvironment) (values : Array (Option ValueBinding))
    (path : Array Name) : MetaM (Option (ValueBinding × Array Name)) := do
  unless values.size == plan.ports.size do
    throwError "constructor projection requires the complete original native port table"
  let some selected ← plan.projectionAt path | return none
  let value ← match selected.target with
    | .argument index =>
      let some original := values[index]?
        | throwError "a constructor projection selected an undeclared native port"
      pure original
    | .context id =>
      IO.ofExcept <| (environment.lookup id).mapError IO.userError
  let some value := value
    | throwError "a constructor projection has no actual original supplier"
  return some (value, selected.path)




opaque ConstructorPortPrefix.ofValues (request : PreparedRequest) (graph : ValueGraph)
    (plan : ConstructorPorts) (values : Array (Option ValueBinding)) :
    MetaM (ConstructorPortPrefix request.roles.scope) := do
  unless values.size == plan.ports.size do
    throwError "constructor transport requires its complete native/proof port table"
  let mut nativePrefix ← ConstructorPortPrefix.prepare request graph plan
  for port in plan.ports, value in values do
    match port.argument.wireIndex, value with
    | none, none => pure ()
    | some _, some value =>
      unless nativePrefix.nextIndex == port.argument.sourceIndex do
        throwError "constructor transport changed its original dependent port order"
      unless value.role.address == port.argument.source.address &&
          value.role.source.context.exactlyMatches port.argument.source.source.context &&
          value.role.source.expression.equal port.argument.source.source.expression &&
          value.role.source.type.equal port.argument.source.source.type do
        throwError "constructor transport changed an original admitted port view"
      nativePrefix ← nativePrefix.bind graph value
    | _, _ => throwError "constructor transport changed a native computational/proof slot"
  discard <| IO.ofExcept <| nativePrefix.finish.mapError IO.userError
  return nativePrefix




opaque ConstructorPortPrefix.transportProjection (nativePrefix : ConstructorPortPrefix scope)
    (request : PreparedRequest) (path : Array Name) (draft : CellDraft) :
    MetaM (CellDraft × ValueBinding) := do
  request.requirePreparation scope
  let values ← IO.ofExcept <| nativePrefix.finish.mapError IO.userError
  let transport ← nativePrefix.plan.projectionTransport request.source path
  let some (parent, remaining) ← nativePrefix.plan.projectionSupplier?
      nativePrefix.environment values path
    | throwError "the accepted constructor lost its original result-field supplier"
  let some (selected, #[]) ← IO.ofExcept <|
      (draft.view.projectionFrontier parent remaining).mapError IO.userError
    | throwError "constructor transport requires the original stored field selection"
  let original ← nativePrefix.environment.checkResult draft.view transport.source selected
  unless original.root.value == selected.value &&
      original.root.associationIds == selected.associationIds do
    throwError "constructor transport changed its original selected port baseline"
  let (draft, value) ← draft.bindTelescopeTransport transport nativePrefix.environment.values
    original.root
  let candidate ← request.environment.checkResult draft.view transport.target value
  return (draft, candidate.root)
end CasRuntime
