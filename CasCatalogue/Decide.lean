/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

/-!
# Decision by the kernel (`specs/leaf-registration.md`, "What Lean discharges")

The one proof the kernel forms itself: `of_decide_eq_true (Eq.refl true) : p` (Lean's
`mkDecideProof`, on `Decidable` instances alone, running no tactic), checked by Lean's kernel
within a fixed heartbeat budget. It decides a statement's proposition before any leaf is consulted
(`CasCatalogue.Realize`), the obligations a decoded answer must satisfy (`CasCatalogue.Codec`: a
proof field, a literal's side conditions, a cone's commutation), and the comparison of a decoded
value with a literal. Which propositions are decidable is the catalogue's and Mathlib's: the kernel
supplies no `Decidable` instance and runs no proof search.
-/

open Lean Meta

namespace CasCatalogue.Decide

/-- The heartbeat budget of one decision by the kernel (in the units of `maxHeartbeats`). -/
def decideBudget : Nat := 20000

/-- Whether Lean's kernel accepts `proof` as a proof of the closed proposition `p`, within
`decideBudget`. The proof is type-checked synchronously by the kernel (`Environment.addDeclCore`,
bounded by `decideBudget`) into a copy of the environment that is discarded. `Lean.addDecl` is
not used: under `Elab.async` it checks theorems in a background task and returns before the
kernel has judged the proof, so its return says nothing. `false` when the kernel does not accept
the proof within the budget (a decision that reduces to `false`, a computation beyond the
budget). -/
def kernelAccepts (p proof : Expr) : MetaM Bool := do
  let attempt : MetaM Bool := do
    let decl := Declaration.thmDecl
      { name := `CasCatalogue.Decide.decided, levelParams := [], type := p, value := proof }
    match (← getEnv).addDeclCore (USize.ofNat (decideBudget * 1000))
        (USize.ofNat maxRecDepth.defValue) decl none with
    | .ok _ => return true
    | .error _ => return false
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|
      -- not a reading fallback: a proof the kernel does not accept decides nothing; the claim is
      -- then realized, unchanged
      tryCatchRuntimeEx attempt fun _ => pure false

/-- Whether Lean's kernel accepts the proof of `p` by decision, `of_decide_eq_true (Eq.refl
true) : p` (`mkDecideProof`), within `decideBudget` (`kernelAccepts`). `false` when `p` has no
`Decidable` instance, or the kernel does not accept the proof within the budget (a classical
instance, a decision that reduces to `false`, a computation beyond the budget). `Decidable`
instances are the catalogue's and Mathlib's; the kernel runs no proof search. -/
def kernelDecides (p : Expr) : MetaM Bool := do
  let attempt : MetaM Bool := do kernelAccepts p (← mkDecideProof p)
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|
      -- not a reading fallback: a proposition without a `Decidable` instance is not decided by
      -- Lean; the claim is then realized, unchanged
      tryCatchRuntimeEx attempt fun _ => pure false

/-- The proposition `p` decided in Lean: `some true` when the kernel accepts its proof by
decision, `some false` when it accepts the proof of `¬p`, `none` otherwise. -/
def decideProp (p : Expr) : MetaM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  if ← kernelDecides p then return some true
  if ← kernelDecides (mkNot p) then return some false
  return none

/-- The kernel's proof of the closed proposition `p` by decision, when it accepts one. -/
def decisionProof (p : Expr) : MetaM (Option Expr) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  if ← kernelDecides p then return some (← mkDecideProof p) else return none

end CasCatalogue.Decide
