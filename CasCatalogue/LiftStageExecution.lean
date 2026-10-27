/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.LiftedSubobjectData
public import CasCatalogue.DataOwnership

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.LiftStageExecution

/-- One selected stage over retained operands. The source is the object `X`;
`original` is either that object or its complete original Arrow. A supplied
source image selects the actual-image contract. Absence retains legacy framing. -/
structure Input (α : Type) where
  selection : SelectedLift.Plan
  originalArrow : Bool
  action : DataOwnership.Data
  parameters : DataOwnership.Data
  original : α
  source : α
  base : α
  baseObject : α
  sourceImage? : Option α := none
  /-- Object endpoint `U(X)` of the complete image, retained by its producer. -/
  sourceImageObject? : Option α := none

/-- The fixed public field and its complete request. Endpoints and earlier
outputs refer to the same retained operand occurrences, never equal-byte lookup. -/
structure Field (α : Type) where
  field : LiftField
  index : Nat
  formal : Expr
  context : CategoryContext
  request : DataOwnership.Data
  preceding : Array α
  endpoints : Option (α × α)
  comparisonImage? : Option α

/-- All four fields and the selected image of the actual object output. This
record alone asserts no execution: private prospective readers use the same fold. -/
structure Result (α : Type) where
  outputs : Array α
  comparisonImage : α
  step : DataOwnership.Data

def checked (result : Except String α) : TermElabM α := do
  match result with
  | .ok value => return value
  | .error message =>
      throwStratum .unavailable m!"the selected lift lost a positioned data supplier: {message}"

/-- The existing five ordered fields keep their positions. Optional images are
separate public slots with independent ownership scopes. -/
def packet (tag id : String) (parameters action source base : DataOwnership.Data)
    (outputs : Array DataOwnership.Data)
    (sourceImage? : Option DataOwnership.Data := none)
    (comparisonImage? : Option DataOwnership.Data := none) :
    TermElabM DataOwnership.Data := do
  let metadata :=
    (sourceImage?.toList.map fun data => ("sourceImage", data)) ++
      (comparisonImage?.toList.map fun data => ("comparisonImage", data))
  checked <| DataOwnership.Data.object ([
    ("ctor", { json := toJson tag }), ("parameters", parameters),
    ("args", DataOwnership.Data.array #[{ json := toJson id }, action, source, base,
      DataOwnership.Data.array outputs])] ++ metadata)

/-- One typed field order serves execution and prospective inspection. Only the
caller supplies a field's data and observes the selected object action. The
comparison image is obtained once, immediately before the forward field. No
registration, formal lift or result interface is selected from returned data. -/
def fold (fragment : α → DataOwnership.Data) (input : Input α)
    (image : α → TermElabM α) (returned : Field α → TermElabM α)
    (readEndpoints : α → CategoryContext → TermElabM (α × α)) :
    TermElabM (Result α) := do
  unless input.selection.ports.size == LiftField.all.size do
    throwError "the selected lift lost its four fixed public ports"
  let mut outputs : Array α := #[]
  let mut comparisonImage? : Option α := none
  let mut comparisonEndpoints? : Option (α × α) := none
  for (field, index) in LiftField.all.zipIdx do
    if index == 2 then
      let some object := outputs[0]?
        | throwError "the selected comparison image precedes its object output"
      comparisonImage? := some (← image object)
    let endpoints ← if index == 0 then pure none
      else if index == 1 then do
        let some object := outputs[0]?
          | throwError "the selected inclusion precedes its object output"
        pure (some (object, input.source))
      else if index == 2 then do
        let some image := comparisonImage?
          | throwError "the selected comparison field lost its actual image endpoint"
        pure (some (image, input.baseObject))
      else do
        let some (image, baseObject) := comparisonEndpoints?
          | throwError "the backward comparison lost the forward map's actual endpoints"
        pure (some (baseObject, image))
    let sourceImage? := input.sourceImage?.map fragment
    let comparison := if sourceImage?.isSome then comparisonImage?.map fragment else none
    let request ← packet (if input.originalArrow then "liftInput" else "monoLiftInput")
      input.selection.entry.id.raw input.parameters input.action
      (fragment input.original) (fragment input.base) (outputs.map fragment)
      sourceImage? comparison
    let context ← SelectedLift.context input.selection (index >= 2)
    let output ← returned {
      field, index, formal := input.selection.ports[index]!, context, request,
      preceding := outputs, endpoints, comparisonImage? }
    if index == 2 then comparisonEndpoints? := some (← readEndpoints output context)
    outputs := outputs.push output
  let some comparisonImage := comparisonImage?
    | throwError "the completed lift lost its selected comparison image"
  let step ← packet "liftStep" input.selection.entry.id.raw input.parameters input.action
    (fragment input.original) (fragment input.base) (outputs.map fragment)
    (input.sourceImage?.map fragment)
    (if input.sourceImage?.isSome then some (fragment comparisonImage) else none)
  return { outputs, comparisonImage, step }

end CasCatalogue.LiftStageExecution
