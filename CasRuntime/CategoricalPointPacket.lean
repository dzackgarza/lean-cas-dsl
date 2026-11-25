module

public import CasRuntime.Value
public import CasCompiler.CategoricalPointFamily
public import CasCompiler.RoutedMethodFamily

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- The released parameter grouping and arrow descriptor of one actual native family.
The slots refer to original admitted inputs; packet arrays are never fabricated Lean values. -/
structure CategoricalPointPacket where
  parameters : ValueContainer
  arrow : ValuePayload

private def packetContainer (template : Json) (slots : Array ContainerSlot) :
    MetaM ValueContainer := do
  let payload ← IO.ofExcept <| (ValuePayload.descriptor template slots).mapError IO.userError
  let .container packet := payload.data
    | throwError "the point descriptor lost its checked packet layout"
  return packet

private def parameterSlot (path : Array InputPathStep) (binding : ValueBinding) : ContainerSlot :=
  { path, binding, fieldIndex := none }

private def actionParameterPath : EdgeRef → Array InputPathStep
  | .functor _ => #[.field "args"]
  | .classifierForget _ => #[.field "args", .index 1]
  | .constructMap _ inner => #[.field "args", .index 1] ++ actionParameterPath inner

/-- Read only the original native parameter table and use the released encoders for framing.
This is a descriptor view; it adds no source action, result field or alternate operation. -/
def CategoricalPointPacket.prepare (family : CategoricalPointFamily)
    (actual : Array (Option ValueBinding)) : MetaM CategoricalPointPacket := do
  unless actual.size == family.parameterCount do
    throwError "the point packet lost its original complete parameter table"
  let value := fun index => do
    let some original := actual[index]?.bind id
      | throwError "the point packet is missing an original computational parameter"
    return original
  let indices ← family.explicitParameters
  let parameters ← indices.mapM value
  let holes := Array.replicate parameters.size Json.null
  let parameterSlots := fun (pathStart : Array InputPathStep) => parameters.mapIdx fun index binding =>
    parameterSlot (pathStart.push (.index index)) binding
  let (parameterTemplate, parameterSlots, arrowTemplate, arrowSlots) ← match family.owner with
    | .named owner =>
      pure (.arr holes, parameterSlots #[],
        Json.mkObj [("ctor", toJson owner.operation), ("args", .arr holes)],
        parameterSlots #[.field "args"])
    | .component entry constructors inverse => do
      let receiver ← value family.declarationParameterCount
      let parametersTemplate := Json.arr #[.arr holes, .null, toJson inverse]
      let slots := parameterSlots #[.index 0] ++ #[parameterSlot #[.index 1] receiver]
      let descriptor : ConstructedCellComponent := {
        constructors := constructors.map (·.raw)
        component := { cell := entry.id.raw, parameters := holes, receiver := .null, inverse } }
      let pathStart := if constructors.isEmpty then #[] else #[.field "args", .index 1]
      let arrowSlots := parameterSlots (pathStart ++ #[.field "args", .index 1]) ++
        #[parameterSlot (pathStart ++ #[.field "args", .index 2]) receiver]
      pure (parametersTemplate, slots, descriptor.encode, arrowSlots)
    | .cartesian entry => do
      let receiver ← value family.declarationParameterCount
      let slots := parameterSlots #[.index 0] ++ #[parameterSlot #[.index 1] receiver]
      let arrow : CartesianMap := { reindex := entry.id.raw, parameters := holes, receiver := .null }
      pure (.arr #[.arr holes, .null], slots, arrow.encode,
        parameterSlots #[.field "args", .index 1] ++
          #[parameterSlot #[.field "args", .index 2] receiver])
    | .binder entry =>
      pure (.arr holes, parameterSlots #[],
        Json.mkObj [("ctor", toJson entry.id.raw), ("args", .arr holes)],
        parameterSlots #[.field "args"])
    | .action edge => do
      let source ← value family.declarationParameterCount
      let target ← value (family.declarationParameterCount + 1)
      let arrow ← value (family.declarationParameterCount + 2)
      let action := routedActionDescriptor edge holes
      let path := actionParameterPath edge
      let (template, invocationSlots) := match edge with
        | .functor _ => (Json.arr holes, parameterSlots #[])
        | _ => (Json.arr #[action], parameterSlots (#[InputPathStep.index 0] ++ path))
      let mapped := Json.mkObj [("ctor", "map"), ("args", .arr #[action,
        TypedMap.encode { source := .null, target := .null, callable := .null }])]
      let slots := parameterSlots (#[InputPathStep.field "args", .index 0] ++ path) ++ #[
        parameterSlot #[.field "args", .index 1, .field "args", .index 0] source,
        parameterSlot #[.field "args", .index 1, .field "args", .index 1] target,
        parameterSlot #[.field "args", .index 1, .field "args", .index 2] arrow]
      pure (template, invocationSlots, mapped, slots)
  return {
    parameters := ← packetContainer parameterTemplate parameterSlots
    arrow := ← IO.ofExcept <| (ValuePayload.descriptor arrowTemplate arrowSlots).mapError IO.userError }

/-- The same complete native action inputs in the released object-action envelope. -/
def CategoricalPointPacket.action (family : SourceActionFamily)
    (actual : Array (Option ValueBinding)) : MetaM ValueContainer := do
  unless actual.size == family.parameterCount + 1 do
    throwError "the object action lost its complete original native input table"
  let parameters ← (← family.explicitParameters).mapM fun index => do
    let some value := actual[index]?.bind id
      | throwError "the object action lost an original explicit declaration parameter"
    pure value
  let some receiver := actual[family.parameterCount]?.bind id
    | throwError "the object action lost its actual original receiver"
  let holes := Array.replicate parameters.size Json.null
  let action := routedActionDescriptor family.edge holes
  let (packets, pathStart) : Array Json × Array InputPathStep := match family.edge with
    | .functor _ => (holes, #[.field "args"])
    | _ => (#[action], #[InputPathStep.field "args", .index 0] ++ actionParameterPath family.edge)
  let slots := parameters.mapIdx (fun index binding =>
      parameterSlot (pathStart.push (.index index)) binding) ++
    #[parameterSlot #[.field "receiver"] receiver]
  let packet : ConstructionInvocation := {
    construction := family.operation, parameters := packets, receiver := .null }
  packetContainer packet.encode slots

end CasRuntime
