/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import Std.Data.HashMap

@[expose] public section

/-!
# The operation tree of a semantic reading (`specs/leaf-registration.md`, "The realized reading")

The realized reading evaluates the same term the semantic reading elaborates; there is no second
traversal of the statement. The semantic reading records, as it forms each value, the catalogue
operation that formed it, keyed by the value it produced: a named object at its parameters, a
method or property after its structural route, a registered limit at its diagram. The realized
reading walks these records bottom-up. Nothing is reverse-engineered from a printed term.
-/

open Lean

namespace CasCatalogue

/-- How the semantic reading formed a value. -/
inductive Node
  /-- The registered object `id` at its explicit parameters (numerals, or other values). -/
  | object (id : ObjectId) (params : Array Expr)
  /-- The denotation of the literal `literal` of the registered literal form `form` (a morphism
  of its graph, a finite subset of its elements). -/
  | literal (form : LiteralId) (literal : Expr)
  /-- The method `id`, applied to `receiver` after the structural route `route`. -/
  | method (id : MethodId) (route : Array EdgeRef) (receiver : Expr)
  /-- The property `id`, decided of `receiver` after the structural route `route`. -/
  | property (id : PropertyId) (route : Array EdgeRef) (receiver : Expr)
  /-- The registered limit `id` at the diagram `diagram`, returned along the registered creation
  lift `lift` when it is computed in another category. -/
  | limit (id : LimitId) (diagram : Expr) (lift : Option LiftId)

/-- The records of one statement's semantic reading. -/
abbrev Trace := IO.Ref (Std.HashMap Expr Node)

def Trace.new : IO Trace := IO.mkRef {}

/-- Record that `value` was formed by `node`, when a trace is being kept. -/
def Trace.record (trace? : Option Trace) (value : Expr) (node : Node) : IO Unit :=
  match trace? with
  | some trace => trace.modify (·.insert value node)
  | none => pure ()

/-- Record `derived` as formed the way `value` was (the apex of a recorded limit, say). -/
def Trace.alias (trace? : Option Trace) (value derived : Expr) : IO Unit := do
  let some trace := trace? | return
  if let some node := (← trace.get)[value]? then trace.modify (·.insert derived node)

/-- How `value` was formed, if it was recorded. -/
def Trace.node? (trace : Trace) (value : Expr) : IO (Option Node) :=
  return (← trace.get)[value]?

end CasCatalogue
