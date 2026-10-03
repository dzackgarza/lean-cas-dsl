/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.ElementData

/-- Closed arithmetic data, interpreted by the existing language at an independently fixed
selected object. Wire tags are a fixed grammar, never Lean source or declaration names. -/
partial def read (selected : Language.Value) (json : Json) : Language.M Language.Value := do
  let .ok tag := json.getObjValAs? String "ctor"
    | throwStratum .malformed m!"element data requires a constructor tag"
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | throwStratum .malformed m!"element data requires an arguments array"
  let carrier ← Language.carrierObject selected
  match tag, args with
  | "numeral", #[number] =>
      let .ok n := number.getNat? | throwStratum .malformed m!"an element numeral is a natural number"
      Language.toElement (.nat n) carrier
  | "generator", #[] => Language.generatorOf carrier
  | "generator", #[number] =>
      let .ok n := number.getNat? | throwStratum .malformed m!"a generator index is a natural number"
      Language.generatorOf carrier (some n)
  | "add", #[left, right] =>
      Language.applyOperation "+" #[← read selected left, ← read selected right] carrier
  | "mul", #[left, right] =>
      Language.applyOperation "·" #[← read selected left, ← read selected right] carrier
  | "neg", #[value] =>
      Language.applyOperation "-" #[← read selected value] carrier
  | _, _ => throwStratum .malformed m!"unknown element data constructor or incorrect arity"

/-- Decode only an explicit `element` envelope. Its descriptor is compared with the exact
registered endpoint descriptor fixed by the question, including all parameters. The reply never
chooses an object by unifying carriers: interpretation uses `selected` exclusively. -/
def decode (selected : Language.Value) (descriptor : Json) (expected : Expr) (json : Json) :
    TermElabM (Option (Except String Expr)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "element" do return none
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | return some (.error "an element envelope requires an arguments array")
  let #[object, data] := args
    | return some (.error "an element envelope requires an exact object descriptor and data")
  unless object == descriptor do
    return some (.error "the element descriptor differs from the exact selected endpoint")
  try
    let .element hom _ ← (read selected data).run {}
      | return some (.error "element data did not produce an element")
    let point ← elabTermAndSynthesize (← `(CategoryTheory.ConcreteCategory.hom
      (C := Type) $(← exprToSyntax hom) 0)) (some expected)
    let point ← instantiateMVars point
    if point.hasMVar || point.hasLevelMVar || point.hasFVar then
      return some (.error "element data did not determine a closed typed point")
    unless ← isDefEq (← inferType point) expected do
      return some (.error "element data has the wrong point type")
    return some (.ok point)
  catch exception =>
    match Exception.stratum? exception with
    | some .invalid | some .malformed =>
        return some (.error (← exception.toMessageData.toString))
    | _ => throw exception

end CasCatalogue.ElementData
