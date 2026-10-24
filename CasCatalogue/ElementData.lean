/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.ElementData

/-- Recursive decoding belongs to the execution layer, which already owns the generic
registered-declaration and morphism decoders. Supplying those decoders here avoids a second
interpretation of dependent parameters and avoids an import cycle with `Realize`. -/
structure Decoders where
  application : Name → Expr → Array Json → TermElabM (Except String Expr) :=
    fun _ _ _ => pure (.error "a registered operation expression requires its declaration decoder")
  point : Expr → Expr → Json → TermElabM (Except String Expr) :=
    fun _ _ _ => pure (.error "a point expression requires its released morphism decoder")

/-- Closed arithmetic data, interpreted by the existing language at an independently fixed
selected object. Wire tags are a fixed grammar, never Lean source or declaration names. -/
partial def read (selected : Language.Value) (json : Json) (decoders : Decoders := {}) :
    Language.M Language.Value := do
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
      Language.applyOperation "+" #[← read selected left decoders, ← read selected right decoders] carrier
  | "mul", #[left, right] =>
      Language.applyOperation "·" #[← read selected left decoders, ← read selected right decoders] carrier
  | "neg", #[value] =>
      Language.applyOperation "-" #[← read selected value decoders] carrier
  | "operationExpression", #[id, parameters, operands] =>
      let .ok id := id.getStr?
        | throwStratum .malformed m!"an operation expression requires its registered operation id"
      let state ← registryState
      let some operation := state.operations.find? (·.id.raw == id)
        | throwStratum .malformed m!"the element expression names no registered operation"
      let .ok parameters := parameters.getArr?
        | throwStratum .malformed m!"operation parameters must be ordered data"
      let .ok operands := operands.getArr?
        | throwStratum .malformed m!"operation operands must be ordered element expressions"
      unless operands.size == operation.arity do
        throwStratum .malformed m!"the operation expression has the wrong declared arity"
      let constant ← mkConstWithFreshMVarLevels operation.declaration
      let (_, _, expected) ← forallMetaTelescopeReducing (← inferType constant)
      let .ok application ← decoders.application operation.declaration expected parameters
        | throwStratum .malformed m!"the operation parameters do not inhabit their released dependent signature"
      let application ← instantiateMVars application
      if application.hasMVar || application.hasLevelMVar || application.hasFVar ||
          application.getAppFn.constName? != some operation.declaration then
        throwStratum .malformed m!"the operation expression did not determine its complete registered application"
      unless ← isTypeCorrect application do
        throwStratum .malformed m!"the operation application is outside its released dependent signature"
      -- An endo-operation keeps the selected structure, even when another structure has
      -- definitionally the same carrier. Operations with a separately registered result
      -- object instead derive their operand selections from their complete parameters.
      if operation.result.isNone then
        let explicit ← Language.explicitArguments operation.declaration application
        let mut matched := false
        for slot in [:explicit.size] do
          if ← Language.parameterCompatible
              (Language.bindSelectedReceiver explicit slot selected (some operation.category)) then
            matched := true
        unless matched do
          throwStratum .malformed m!"the operation parameters differ from the selected structure"
      let some (source, target) := Language.homEnds? (← inferType application)
        | throwStratum .malformed m!"the registered element operation is not a morphism"
      unless ← withTransparency .all <| isDefEq target (← Language.semanticObject carrier) do
        throwStratum .malformed m!"the operation expression lands outside the selected endpoint"
      let sources ← if operands.isEmpty then pure #[] else if operands.size == 2 then do
        let source ← whnfR source
        match source.getAppFn.constName?, source.getAppArgs with
        | some ``Prod, #[left, right] => pure #[left, right]
        | _, _ => throwStratum .malformed m!"a binary operation requires its declared product source"
      else pure #[source]
      unless sources.size == operands.size do
        throwStratum .malformed m!"the operation's operand interface is not its declared source"
      let some sets := state.categories.find? (·.id == CategoryId.sets)
        | throwStratum .invalid m!"element data has no registered category of sets"
      let elements ← (sources.zip operands).mapM fun (source, data) => do
        let operand ← Language.recognize state source sets #[selected] application.getAppArgs
        read operand data decoders
      Language.applyFamily operation.declaration sets elements (some carrier)
        (application := some application)
  | "point", #[data] =>
      let source ← Language.semanticObject (← Language.oneObject)
      let target ← Language.semanticObject carrier
      let .ok hom ← decoders.point source target data
        | throwStratum .malformed m!"the point data do not inhabit the selected morphism interface"
      let hom ← instantiateMVars hom
      if hom.hasMVar || hom.hasLevelMVar || hom.hasFVar then
        throwStratum .malformed m!"the point data did not determine a closed morphism"
      let expected ← mkAppM ``Quiver.Hom #[source, target]
      unless ← isTypeCorrect hom <&&> isDefEq (← inferType hom) expected do
        throwStratum .malformed m!"the point data have different declared endpoints"
      return .element hom carrier
  | _, _ => throwStratum .malformed m!"unknown element data constructor or incorrect arity"

/-- Decode only an explicit `element` envelope. Its descriptor is compared with the exact
registered endpoint descriptor fixed by the question, including all parameters. The reply never
chooses an object by unifying carriers: interpretation uses `selected` exclusively. -/
def decode (selected : Language.Value) (descriptor : Json) (expected : Expr) (json : Json)
    (decoders : Decoders := {}) :
    TermElabM (Option (Except String Expr)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "element" do return none
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | return some (.error "an element envelope requires an arguments array")
  let #[object, data] := args
    | return some (.error "an element envelope requires an exact object descriptor and data")
  unless object == descriptor do
    return some (.error "the element descriptor differs from the exact selected endpoint")
  try
    let .element hom _ ← (read selected data decoders).run {}
      | return some (.error "element data did not produce an element")
    let unit ← Language.globalPoint.run {}
    let point ← elabTermAndSynthesize (← `(CategoryTheory.ConcreteCategory.hom
      (C := Type) $(← exprToSyntax hom) $(← exprToSyntax unit))) (some expected)
    let point ← instantiateMVars point
    if point.hasMVar || point.hasLevelMVar || point.hasFVar then
      return some (.error "element data did not determine a closed typed point")
    unless ← isDefEq (← inferType point) expected do
      return some (.error "element data has the wrong point type")
    return some (.ok point)
  catch exception =>
    if Exception.hasConflictingStrata exception then throw exception
    match Exception.stratum? exception with
    | some .invalid | some .malformed =>
        return some (.error (← exception.toMessageData.toString))
    | _ => throw exception

end CasCatalogue.ElementData
