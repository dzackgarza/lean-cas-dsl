/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.HashMap

@[expose] public section

/-!
# Memoization of explicit applications (CC-MEMO)

A runtime may retain `(F, X) ↦ F(X)`, keyed by the explicit application: the name of the applied
action and the handle it is applied to. It is an optimization only — `memoApply none` computes
the same value — and it never records which structure was "grafted" where, because nothing is.
-/

namespace CasCatalogue

/-- A memo table of explicit applications. -/
abbrev MemoTable (α β : Type) [BEq α] [Hashable α] := IO.Ref (Std.HashMap (String × α) β)

/-- A fresh memo table. -/
def MemoTable.new (α β : Type) [BEq α] [Hashable α] : IO (MemoTable α β) := IO.mkRef {}

/-- Apply `f` (the action named `key`) to `x`, through the memo table when one is given. -/
def memoApply {α β : Type} [BEq α] [Hashable α] (table : Option (MemoTable α β)) (key : String)
    (f : α → β) (x : α) : IO β :=
  match table with
  | none => pure (f x)
  | some table => do
      match (← table.get)[(key, x)]? with
      | some y => pure y
      | none =>
          let y := f x
          table.modify (·.insert (key, x) y)
          pure y

end CasCatalogue
