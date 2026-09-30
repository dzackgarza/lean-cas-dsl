/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

/-!
# The generic structural codec (`specs/leaf-registration.md`, "Forms are formal")

The kernel owns each form's wire encoding, and it is one codec over every inductive type, derived
from the type's definition in the environment. It has no per-type code:

* a natural number or an integer is a JSON number;
* a list is a JSON array;
* any other constructor application is `{"ctor": <constructor name>, "args": [<fields>]}`, the
  constructor spelled by its short name within its type (`finite`, `aleph0`).

Decoding is total: JSON becomes a closed value of the expected type, driven by that type's
inductive definition, or it is rejected with the reason. A type the codec does not handle (a
quotient, a field that is a proof or a type) is rejected by name; nothing special-cases it.
-/

open Lean Meta

namespace CasCatalogue.Codec

/-- The wire spelling of a constructor: its name within its type. -/
def label (ctor : Name) : String :=
  match ctor with
  | .str _ s => s
  | n => n.toString

/-- The natural number a closed term is. -/
def nat? (e : Expr) : MetaM (Option Nat) := (evalNat e).run

/-- Encode the closed value `e`. -/
partial def encode (e : Expr) : MetaM (Except String Json) := do
  let e ← instantiateMVars e
  let type ← whnf (← inferType e)
  if type.isConstOf ``Nat then
    return match ← nat? e with
      | some n => .ok (toJson n)
      | none => .error s!"the natural number {e} is not a closed literal"
  if type.isConstOf ``Int then
    let e ← whnf e
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Int.ofNat, #[n] =>
        return match ← nat? n with
          | some n => .ok (toJson (Int.ofNat n))
          | none => .error s!"the integer {e} is not a closed literal"
    | some ``Int.negSucc, #[n] =>
        return match ← nat? n with
          | some n => .ok (toJson (Int.negSucc n))
          | none => .error s!"the integer {e} is not a closed literal"
    | _, _ => return .error s!"the integer {e} is not a closed literal"
  if type.isAppOf ``List then
    let mut items : Array Json := #[]
    let mut rest ← whnf e
    repeat
      match rest.getAppFn.constName?, rest.getAppArgs with
      | some ``List.nil, _ => break
      | some ``List.cons, #[_, x, xs] =>
          match ← encode x with
          | .ok j => items := items.push j
          | .error m => return .error m
          rest ← whnf xs
      | _, _ => return .error s!"the list {rest} is not a closed literal"
    return .ok (Json.arr items)
  let e ← whnf e
  let .const c _ := e.getAppFn
    | return .error s!"{e} is not a constructor application"
  let some (.ctorInfo ctor) := (← getEnv).find? c
    | return .error s!"{e} is not a constructor application ({c} is not a constructor)"
  let fields := e.getAppArgs.extract ctor.numParams (ctor.numParams + ctor.numFields)
  let mut args : Array Json := #[]
  for field in fields do
    if ← isProof field then
      return .error s!"the constructor {c} has a proof field: it is not a data type the codec \
        encodes"
    if ← isType field then
      return .error s!"the constructor {c} has a type field: it is not a data type the codec \
        encodes"
    match ← encode field with
    | .ok j => args := args.push j
    | .error m => return .error m
  return .ok (Json.mkObj [("ctor", label c), ("args", Json.arr args)])

/-- Decode `j` as a closed value of the type `type`. -/
partial def decode (type : Expr) (j : Json) : MetaM (Except String Expr) := do
  let type ← whnf (← instantiateMVars type)
  if type.isConstOf ``Nat then
    return match j.getNat? with
      | .ok n => .ok (mkNatLit n)
      | .error _ => .error s!"{j.compress} is not a natural number"
  if type.isConstOf ``Int then
    return match j.getInt? with
      | .ok n =>
          if n ≥ 0 then .ok (mkApp (mkConst ``Int.ofNat) (mkNatLit n.toNat))
          else .ok (mkApp (mkConst ``Int.negSucc) (mkNatLit (-n - 1).toNat))
      | .error _ => .error s!"{j.compress} is not an integer"
  if type.isAppOf ``List then
    let element := type.appArg!
    let .ok items := j.getArr? | return .error s!"{j.compress} is not a list"
    let mut decoded : Array Expr := #[]
    for item in items do
      match ← decode element item with
      | .ok v => decoded := decoded.push v
      | .error m => return .error m
    let mut list ← mkAppOptM ``List.nil #[some element]
    for v in decoded.reverse do list ← mkAppM ``List.cons #[v, list]
    return .ok list
  let .const typeName levels := type.getAppFn
    | return .error s!"{type} is not an inductive type the codec handles"
  let some (.inductInfo info) := (← getEnv).find? typeName
    | return .error s!"{typeName} is not an inductive type the codec handles"
  let .ok name := j.getObjValAs? String "ctor"
    | return .error s!"{j.compress} is not a constructor application of {typeName} \
        (no `ctor` field)"
  let .ok args := (j.getObjVal? "args").bind (·.getArr?)
    | return .error s!"{j.compress} is not a constructor application of {typeName} \
        (no `args` array)"
  let some ctor := info.ctors.find? fun c => label c == name || c.toString == name
    | return .error s!"{typeName} has no constructor {name} (its constructors are \
        {info.ctors.map label})"
  let ctorInfo ← getConstInfoCtor ctor
  unless args.size == ctorInfo.numFields do
    return .error s!"the constructor {name} of {typeName} takes {ctorInfo.numFields} fields, \
      not {args.size}"
  let mut value := mkAppN (mkConst ctor levels) (type.getAppArgs.extract 0 info.numParams)
  for arg in args do
    let .forallE _ fieldType _ _ ← whnf (← inferType value)
      | return .error s!"the constructor {name} of {typeName} has fewer fields than {args.size}"
    if ← isProp fieldType then
      return .error s!"a field of the constructor {name} of {typeName} is a proposition: it is \
        not a data type the codec decodes"
    if (← whnf fieldType).isSort then
      return .error s!"a field of the constructor {name} of {typeName} is a type: it is not a \
        data type the codec decodes"
    match ← decode fieldType arg with
    | .ok v => value := mkApp value v
    | .error m => return .error m
  return .ok value

end CasCatalogue.Codec
