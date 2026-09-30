/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Decide

@[expose] public section

/-!
# The generic structural codec (`specs/leaf-registration.md`, "Forms are formal")

The kernel owns each form's wire encoding, and it is one codec over every inductive type, derived
from the type's definition in the environment. It has no per-type code:

* a natural number or an integer is a JSON number;
* a list is a JSON array;
* a quotient `Quot r` is a representative: the encoding of a value of the carrier, and decodes
  as the class of the value read (a `Multiset` is a list; a `Finset` is a list, its `nodup`
  decided);
* a record (an inductive type with one constructor and no indices: a pair, `Fin n`, a subtype)
  is the JSON array of its data fields, and is the field itself when it has exactly one (a
  point of `Fin n` is its number, a pair is `[x, y]`);
* any other constructor application is `{"ctor": <constructor name>, "args": [<fields>]}`, the
  constructor spelled by its short name within its type (`finite`, `aleph0`), with its data
  fields.

A proof field is never on the wire (`k < n` of a point of `Fin n`). Decoding establishes it by
the kernel's decision (`CasCatalogue.Decide`), from the data fields before it, or rejects the
value: what a leaf sends is data, and whether it satisfies the form's conditions is decided here.

Decoding is total: JSON becomes a closed value of the expected type, driven by that type's
inductive definition, or it is rejected with the reason. A type the codec does not handle (a
quotient, a field that is a type) is rejected by name; nothing special-cases it.
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

/-- Whether `info` is a record: one constructor and no indices. -/
def isRecord (info : InductiveVal) : Bool := info.ctors.length == 1 && info.numIndices == 0

/-- The number of data (non-proof) fields of the constructor `ctor`. -/
def dataFieldCount (ctor : ConstructorVal) : MetaM Nat :=
  forallTelescopeReducing ctor.type fun xs _ => do
    let fields := xs.extract ctor.numParams (ctor.numParams + ctor.numFields)
    fields.foldlM (init := 0) fun n x => return if ← isProp (← inferType x) then n else n + 1

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
  if type.isAppOf ``Quot then
    let e ← whnf e
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Quot.mk, #[_, _, a] => return ← encode a
    | _, _ => return .error s!"the class {e} is not a closed literal"
  let e ← whnf e
  let .const c _ := e.getAppFn
    | return .error s!"{e} is not a constructor application"
  let some (.ctorInfo ctor) := (← getEnv).find? c
    | return .error s!"{e} is not a constructor application ({c} is not a constructor)"
  let some (.inductInfo info) := (← getEnv).find? ctor.induct
    | return .error s!"{ctor.induct} is not an inductive type the codec handles"
  let fields := e.getAppArgs.extract ctor.numParams (ctor.numParams + ctor.numFields)
  let mut args : Array Json := #[]
  for field in fields do
    -- A proof field is not on the wire: decoding decides it.
    if ← isProof field then continue
    if ← isType field then
      return .error s!"the constructor {c} has a type field: it is not a data type the codec \
        encodes"
    match ← encode field with
    | .ok j => args := args.push j
    | .error m => return .error m
  if isRecord info then
    return .ok (if args.size == 1 then args[0]! else Json.arr args)
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
  if type.isAppOf ``Quot then
    let #[carrier, relation] := type.getAppArgs
      | return .error s!"{type} is not a quotient the codec handles"
    let .const _ levels := type.getAppFn | unreachable!
    return (← decode carrier j).map fun a => mkAppN (mkConst ``Quot.mk levels) #[carrier, relation, a]
  let .const typeName levels := type.getAppFn
    | return .error s!"{type} is not an inductive type the codec handles"
  let some (.inductInfo info) := (← getEnv).find? typeName
    | return .error s!"{typeName} is not an inductive type the codec handles"
  -- The constructor and its data fields' encodings: a record's from the array (or the single
  -- field itself), any other type's from `{"ctor", "args"}`.
  let (ctor, args) ← if isRecord info then do
      let ctor ← getConstInfoCtor info.ctors[0]!
      let count ← dataFieldCount ctor
      if count == 1 then pure (ctor, #[j])
      else match j.getArr? with
        | .ok args => pure (ctor, args)
        | .error _ => return .error s!"{j.compress} is not a {typeName}: its {count} fields are \
            an array"
    else do
      let .ok name := j.getObjValAs? String "ctor"
        | return .error s!"{j.compress} is not a constructor application of {typeName} \
            (no `ctor` field)"
      let .ok args := (j.getObjVal? "args").bind (·.getArr?)
        | return .error s!"{j.compress} is not a constructor application of {typeName} \
            (no `args` array)"
      let some ctor := info.ctors.find? fun c => label c == name || c.toString == name
        | return .error s!"{typeName} has no constructor {name} (its constructors are \
            {info.ctors.map label})"
      pure (← getConstInfoCtor ctor, args)
  let count ← dataFieldCount ctor
  unless args.size == count do
    return .error s!"the constructor {label ctor.name} of {typeName} takes {count} values, not \
      {args.size}"
  let mut value := mkAppN (mkConst ctor.name levels) (type.getAppArgs.extract 0 info.numParams)
  let mut remaining := args.toList
  for _ in [0:ctor.numFields] do
    let .forallE _ fieldType _ _ ← whnf (← inferType value)
      | return .error s!"the constructor {label ctor.name} of {typeName} has fewer fields than \
          {args.size}"
    if ← isProp fieldType then
      -- The condition the data must satisfy, decided by the kernel.
      let some proof ← Decide.decisionProof fieldType
        | return .error s!"{j.compress} is not a {typeName}: the kernel does not decide \
            {fieldType}"
      value := mkApp value proof
      continue
    if (← whnf fieldType).isSort then
      return .error s!"a field of the constructor {label ctor.name} of {typeName} is a type: it \
        is not a data type the codec decodes"
    let arg :: rest := remaining | unreachable!
    remaining := rest
    match ← decode fieldType arg with
    | .ok v => value := mkApp value v
    | .error m => return .error m
  return .ok value

end CasCatalogue.Codec
