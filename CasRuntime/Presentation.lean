module

public import CasRuntime.PreparedRequest
public import CasRuntime.Encode
public import CasCatalogue.Admission

@[expose] public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend



structure PreparedPresentationInvocation where
  private mk ::
  preparation : RoleScope
  operation : String
  parameters : Array ValueBinding
  inverse : Bool
  source : ValueBinding
  target : ValueBinding
  argument : ValueBinding
  forms : Array String
  dependencies : Array ValueBinding




opaque PreparedPresentationInvocation.prepare (request family : PreparedRequest)
    (path : Array FieldLayout) (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) :
    MetaM PreparedPresentationInvocation := do
  request.requireFamily family path graph codes
  let .primitive (.presentation selected) _ := family.action
    | throwError "a presentation invocation lost its original named family"
  let some inverse := selected.direction? (path.map (·.projection))
    | throwStratum .noImplementation
        m!"{selected.entry.id.raw} has no published action at this native field path"
  let .apply _ arguments _ := request.action
    | throwError "a presentation point action requires an actual application"
  unless arguments.size == 1 do
    throwError "a presentation action requires its one complete original point argument"
  discard <| family.admitInputs graph
  let inputs ← request.admitInputs graph
  let #[argument] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "a presentation point action lost its original computational operand"
  let mut parameters := #[]
  if let some application := family.application then
    let some original := family.origin.application
      | throwError "a presentation family lost its complete native argument table"
    for parameter in application.arguments do
      if parameter.wireIndex.isSome && parameter.binderInfo.isExplicit then
        let some value := original.arguments[parameter.sourceIndex]?.bind id
          | throwError "a presentation family is missing an explicit computational parameter"
        parameters := parameters.push value
  let (first, second) ← family.presentationEndpoints graph
  let (source, target) := if inverse then (second, first) else (first, second)
  let endpointForm ← family.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let selections ← source.role.selections.inContext context
    let some (entry, _) ← sourceObjectSelection? context selections
        (← source.role.source.inContext context)
      | return none
    let state : RegistryState := { toSemanticState := ← semanticState }
    let some form := state.form? entry.id.raw
      | throwError "the presentation source lost its admitted endpoint form"
    if let some reason := state.rejects (.presentation selected.entry) form then
      throwError "the presentation source form is incompatible: {reason}"
    return some entry.id.raw
  let forms := #[selected.entry.id.raw] ++ endpointForm.toArray
  return ⟨request.roles.scope, selected.entry.id.raw, parameters, inverse, source, target,
    argument, forms, family.scope ++ request.scope⟩



def PreparedPresentationInvocation.roots (invocation : PreparedPresentationInvocation) :
    Array InputPosition :=
  invocation.parameters.mapIdx (fun index binding =>
    { path := #[.field "args", .index 0, .index index], binding }) ++ #[
    { path := #[.field "args", .index 2], binding := invocation.source },
    { path := #[.field "args", .index 3], binding := invocation.target },
    { path := #[.field "args", .index 4], binding := invocation.argument }]



def PreparedPresentationInvocation.encode (invocation : PreparedPresentationInvocation)
    (graph : ValueGraph) (receiver : ConnectionGeneration) :
    Except String (EncodedInputs × Json) := do
  let encoded ← graph.encodeInputs receiver invocation.roots
  let count := invocation.parameters.size
  let #[source, target, argument] := encoded.values.extract count encoded.values.size
    | throw "presentation encoding lost a complete endpoint or original point"
  let packet : PresentationInvocation := {
    parameters := encoded.values.extract 0 count, inverse := invocation.inverse,
    source, target, argument }
  return (encoded, packet.encode)

end CasRuntime
