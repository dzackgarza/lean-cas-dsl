/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

/-!
# Ownership of exact computational data occurrences

An opaque token has meaning only in its actual live supplying session. Equal
JSON at two different positions does not identify those sessions. These pure
helpers retain a supplier at each opaque occurrence without changing the public
wire data or choosing an implementation. The caller checks session liveness and
the complete declared data interface separately.

Tables are relative to the JSON value they accompany. Assembly prefixes paths;
projection strips the exact selected prefix. No helper recovers provenance by
searching for equal JSON values. A complete table has exactly one binding for
each opaque occurrence and no bindings for absent or portable data.
-/

open Lean

namespace CasCatalogue.DataOwnership

inductive Step where
  | field (key : String)
  | index (index : Nat)
  deriving BEq, DecidableEq, Repr, ToJson

abbrev Path := Array Step
abbrev Owner := String × Nat

structure Binding where
  path : Path
  owner : Owner
  deriving BEq, DecidableEq, Repr, ToJson

abbrev Table := Array Binding

/-- Select exactly one JSON position. A wrong container kind or absent position
returns `none`; equal data at another position is never considered. -/
def get? (data : Json) (path : Path) : Option Json := do
  let mut selected := data
  for step in path do
    selected ← match step, selected with
      | .field key, .obj _ => (selected.getObjVal? key).toOption
      | .index index, .arr values => values[index]?
      | _, _ => none
  return selected

/-- Strip an exact initial path, including every field name and array index. -/
def stripPrefix? (initial path : Path) : Option Path :=
  if initial.size ≤ path.size && path.extract 0 initial.size == initial then
    some (path.extract initial.size path.size)
  else none

/-- Attach an already scoped packet at its exact new position. -/
def «prefix» (initial : Path) (table : Table) : Table :=
  table.map fun binding => { binding with path := initial ++ binding.path }

/-- Retain only suppliers inside the selected subtree and rebase their paths.
The input table must belong to the complete original packet. -/
def project (selected : Path) (table : Table) : Table :=
  table.filterMap fun binding =>
    (stripPrefix? selected binding.path).map fun path => { binding with path }

/-- Combine tables for disjoint positioned subtrees. Call `checkCoverage` at the
completed packet boundary; append does not conceal conflicting bindings. -/
def append (left right : Table) : Table := left ++ right

/-- Locate opaque occurrences structurally. An opaque envelope is one atomic
occurrence; validating its token and field grammar belongs to the data codec. -/
partial def opaquePaths (data : Json) : Array Path := Id.run do
  if (data.getObjValAs? String "ctor").toOption == some "opaqueData" then
    return #[#[]]
  let mut paths : Array Path := #[]
  match data with
  | .arr values =>
    for index in [:values.size] do
      paths := paths ++ (opaquePaths values[index]!).map (fun path => #[.index index] ++ path)
  | .obj fields =>
    for (key, value) in fields.toList do
      paths := paths ++ (opaquePaths value).map (fun path => #[.field key] ++ path)
  | _ => pure ()
  return paths

/-- Bind every opaque occurrence newly returned by this one supplier.
References to earlier results must preserve their own tables instead. -/
def capture (data : Json) (owner : Owner) : Table :=
  (opaquePaths data).map fun path => { path, owner }

/-- Read the owner of one exact occurrence. Duplicate bindings are an error even
when they repeat the same owner; a complete packet has one binding per position. -/
def lookup (table : Table) (path : Path) : Except String (Option Owner) :=
  match table.filter (fun binding => binding.path == path) with
  | #[] => .ok none
  | #[binding] => .ok (some binding.owner)
  | _ => .error s!"an opaque occurrence has duplicate ownership bindings at {reprStr path}"

/-- Require a supplier for every opaque occurrence, exactly once, and prohibit
ownership annotations on nonexistent or nonopaque positions. This validates
provenance coverage only, never liveness, the wire grammar, or mathematics. -/
def checkCoverage (data : Json) (table : Table) : Except String Unit := do
  let paths := opaquePaths data
  for binding in table do
    unless paths.contains binding.path do
      throw s!"an ownership binding does not select an opaque occurrence at {reprStr binding.path}"
  for path in paths do
    let owner ← lookup table path
    unless owner.isSome do
      throw s!"an opaque occurrence has no supplying session at {reprStr path}"

/-- Distinct actual suppliers, preserving first occurrence order. This is useful
for liveness and dispatch checks; it is not a replacement for the positioned table. -/
def owners (table : Table) : Array Owner := Id.run do
  let mut result := #[]
  for binding in table do
    unless result.contains binding.owner do result := result.push binding.owner
  return result

/-- One computational fragment with ownership relative to its own JSON root.
The structure carries no formal value or evidence. Public fields permit ordinary
runtime bookkeeping; `validate` remains required at completed payload boundaries. -/
structure Data where
  json : Json
  ownership : Table := #[]
  deriving BEq, ToJson, Inhabited

instance : Repr Data where
  reprPrec data prec := reprPrec (data.json.compress, data.ownership) prec

namespace Data

/-- Check exact ownership coverage, independently of wire typing and liveness. -/
def validate (data : Data) : Except String Unit :=
  checkCoverage data.json data.ownership

/-- Introduce known portable data, refusing an unowned opaque occurrence. -/
def portable (json : Json) : Except String Data := do
  let data : Data := { json }
  data.validate
  return data

/-- Scope a fresh response from one actual supplier. Earlier result references
must be assembled from their existing fragments rather than captured again. -/
def capture (json : Json) (owner : Owner) : Data :=
  { json, ownership := CasCatalogue.DataOwnership.capture json owner }

/-- Assemble ordered occurrences with their exact array positions. Valid child
fragments produce valid complete coverage; malformed child annotations are never
repaired or discarded and are rejected by the final `validate`. -/
def array (values : Array Data) : Data := Id.run do
  let mut ownership : Table := #[]
  for index in [:values.size] do
    ownership := append ownership
      (CasCatalogue.DataOwnership.prefix #[.index index] values[index]!.ownership)
  return { json := Json.arr (values.map (·.json)), ownership }

/-- Assemble named fields, rejecting duplicate keys before `Json.mkObj` can
collapse two independent occurrences. The complete result's coverage is checked. -/
def object (fields : List (String × Data)) : Except String Data := do
  let mut keys : Array String := #[]
  let mut ownership : Table := #[]
  for (key, data) in fields do
    if keys.contains key then
      throw s!"a computational object repeats the field {key}"
    keys := keys.push key
    ownership := append ownership
      (CasCatalogue.DataOwnership.prefix #[.field key] data.ownership)
  let data : Data := {
    json := Json.mkObj (fields.map fun (key, value) => (key, value.json))
    ownership }
  data.validate
  return data

/-- Build an ordinary public constructor envelope. `opaqueData` needs a captured
supplier and cannot be introduced through this portable tag/argument constructor. -/
def ctor (tag : String) (arguments : Array Data) : Except String Data :=
  object [("ctor", { json := toJson tag }), ("args", array arguments)]

/-- Project one exact occurrence and rebase its ownership. Check the original
coverage first so projection cannot hide an invalid or conflicting annotation. -/
def project (data : Data) (path : Path) : Except String Data := do
  data.validate
  let some json := get? data.json path
    | throw s!"the computational projection selects an absent position at {reprStr path}"
  let selected : Data := {
    json, ownership := CasCatalogue.DataOwnership.project path data.ownership }
  selected.validate
  return selected

end Data

end CasCatalogue.DataOwnership
