/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

/-! # Question-export records shared by the command and its executable entry point -/

open Lean

namespace CasCatalogue.Tools.QuestionExport

structure Options where
  suite : String := "tests/acceptance"
  inventory : String := "CasAcceptance/Permanent/admitted.json"
  readings : String := ""
  failures : String := ""
  imports : Array Name := #[]

structure Reading where
  file : String
  id : String
  /-- Original one-based source line; zero denotes an inventory-only record. -/
  sourceLine : Nat := 0
  question : String := ""
  proposition : String := ""
  deriving ToJson, FromJson, Inhabited

structure Failure where
  file : String
  id : String
  /-- Preserve the attempted source even when no complete typed question exists. -/
  sourceLine : Nat := 0
  source : String := ""
  stage : String
  kind : String
  detail : String
  /-- Completed production stages, useful when the reader or serializer failed. -/
  completedStages : Array (String × Nat) := #[]
  deriving ToJson, FromJson, Inhabited

structure Export where
  readings : Array Reading := #[]
  failures : Array Failure := #[]

def inventoryIds (path : String) : IO (Array String) := do
  let .ok document := Json.parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse fixed assertion inventory {path}"
  let .ok (.obj assertions) := document.getObjVal? "assertions"
    | throw <| IO.userError s!"missing assertions in fixed inventory {path}"
  return assertions.toList.toArray.map (·.1) |>.qsort (· < ·)

/-- Every admitted ID survives in the export, including absent and unreadable input. -/
def checkInventory (suite : String) (required : Array String) (result : Export) : Export := Id.run do
  let mut result := result
  for id in required do
    let count := (result.readings.filter (·.id == id)).size
    if count == 0 then
      result := { result with
        readings := result.readings.push { file := suite, id },
        failures := result.failures.push {
          file := suite, id, stage := "inventory", kind := "internal",
          detail := "required assertion produced no reading record" } }
    else if count != 1 then
      result := { result with failures := result.failures.push {
          file := suite, id, stage := "inventory", kind := "internal",
          detail := s!"required assertion produced {count} reading records" } }
  for reading in result.readings do
    unless reading.id.startsWith "(statement)" || required.contains reading.id do
      result := { result with failures := result.failures.push {
          file := reading.file, id := reading.id, stage := "inventory", kind := "internal",
          detail := "assertion is absent from the supplied fixed inventory" } }
  return result

def writeExport (o : Options) (required : Array String) (result : Export)
    (provenance : Json) : IO Unit := do
  IO.FS.writeFile o.readings (toJson result.readings).pretty
  let unread := required.filter fun id =>
    !(result.readings.any fun r => r.id == id && !r.question.isEmpty && !r.proposition.isEmpty)
  IO.FS.writeFile o.failures (Json.mkObj [
    ("purpose", toJson "interpretation only; no acceptance or migration verdict"),
    ("inventory", toJson o.inventory), ("requiredCount", toJson required.size),
    ("readableCount", toJson (required.size - unread.size)), ("unreadableIds", toJson unread),
    ("provenance", provenance), ("failures", toJson result.failures)]).pretty

end CasCatalogue.Tools.QuestionExport
