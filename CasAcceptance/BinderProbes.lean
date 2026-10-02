/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.TestSuite
public meta import CasAcceptance.Standard
public meta import CasCatalogue.TestSuite

@[expose] public section

/-!
# Acceptance for `b0-binders` (`specs/binders.md`)

Binding notation is read by the catalogue's binder rows of its token, through the kernel's one
binder path (`CasCatalogue.Language.bind`), with no manifest installed:

* **Two rows of one token are told apart by their arguments.** `lim` has two rows,
  `bind.sets.limit` (the point `a ∈ ℝ`) and `bind.sets.limit_at_infinity` (the point `a ∈ ℝ̄ ∖ ℝ`).
  `lim_{t → 0} t` is read by the first: its value is formed by the limit at a real point.
  `lim_{t → ∞} 1/t` is read by the second: its value is formed by the limit at `±∞`. Each statement
  is read, and, since nothing computes it, is a gap.
* **A statement no row reads is invalid.** `∑_{t ∈ {1, 2}} t`: `{1, 2}` is a subset in `𝒫(ℤ)`, not
  established to be finite, and no row of `∑` takes it. `∑_{n ∈ ℕ} n`: the rows of `∑` over an
  index set take `ℕ`, and none of them lands in `ℕ`, the set of the body.
* **A statement two rows read is invalid.** Over a table in which `∑` writes both the sum and the
  product over a finite subset (`bind.sets.finite_sum`, and `bind.sets.finite_product` given the
  token `∑`; a table of this probe, registered nowhere), `∑_{a ∈ A} a` for the finite set `A` of
  the complex roots of `x³ - 2x + 1` is read by both rows, and is invalid. Over the registered
  rows of `∑` alone it is read.
-/

open Lean Elab Command Meta

namespace CasCatalogue.BinderProbes

open Language Realize

/-- Run `text` after the `let`s `lets`; its outcome. -/
meta def outcomeOf (harness : Harness) (lets : List String) (text : String) :
    CommandElabM (Outcome × Language.Scope) := do
  let mut scope : Language.Scope := {}
  for binding in lets do
    scope := (← runStatement harness scope binding).2
  let (outcome, _) ← runStatement harness scope text
  return (outcome, scope)

/-- Whether `detail` says `phrase`. -/
meta def mentions (detail phrase : String) : Bool := (detail.splitOn phrase).length > 1

/-- The term `text` of the language. -/
meta def termOf (text : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `cas_term text with
  | .ok stx => pure stx
  | .error e => throwError "not a term of the language: {e}\n{text}"

/-- The value of the term `text` read in `scope`, instantiated. -/
meta def valueOf (scope : Language.Scope) (text : String) : CommandElabM Expr := do
  let stx ← termOf text
  liftTermElabM <| Term.withoutErrToSorry do
    let .element hom _ ← (eval scope stx).run {}
      | throwError "`{text}` is not read as an element"
    instantiateMVars hom

/-- The kind of the reading of the binding notation `text` in `scope` by the rows `rows`, and
what it says. -/
meta def readingBy (scope : Language.Scope) (rows : Array BinderEntry) (text : String) :
    CommandElabM (String × String) := do
  let stx ← termOf text
  let some b := binding? stx | throwError "`{text}` is not a binding notation"
  liftTermElabM <| Term.withoutErrToSorry do
    try
      discard <| (bind scope rows b none).run {}
      return ("read", "")
    catch e =>
      let outcome ← Outcome.ofException e
      return (outcome.kind, outcome.detail)

/-- Whether `e` is formed by the declaration `n`. -/
meta def formedBy (e : Expr) (n : Name) : Bool := (e.find? (·.isConstOf n)).isSome

-- Two rows of `lim`, told apart by their arguments: the point `0 ∈ ℝ` is read by the limit at a
-- real point, the point `∞ ∈ ℝ̄ ∖ ℝ` by the limit at `±∞`; neither by the other.
run_cmd do
  let harness ← (Harness.empty : IO Harness)
  let atZero ← valueOf {} "lim_{t → 0} t"
  unless formedBy atZero ``CasCatalogue.Algebra.RealLimits.limit &&
      !formedBy atZero ``CasCatalogue.Algebra.RealLimits.limitAtInfinity do
    throwError "`lim_\{t → 0} t` is not read by bind.sets.limit: {atZero}"
  let atInfinity ← valueOf {} "lim_{t → ∞} 1/t"
  unless formedBy atInfinity ``CasCatalogue.Algebra.RealLimits.limitAtInfinity &&
      !formedBy atInfinity ``CasCatalogue.Algebra.RealLimits.limit do
    throwError "`lim_\{t → ∞} 1/t` is not read by bind.sets.limit_at_infinity: {atInfinity}"
  for text in ["assert lim_{t → 0} t = 0", "assert lim_{t → ∞} 1/t = 0"] do
    let (outcome, _) ← outcomeOf harness [] text
    unless outcome.kind == "gap" do
      throwError "`{text}` is {repr outcome}, not a gap"

-- A statement no row reads is invalid: no row of `∑` takes a subset not established to be finite,
-- and none of the rows that take `ℕ` lands in `ℕ`.
run_cmd do
  let harness ← (Harness.empty : IO Harness)
  for text in ["assert ∑_{t ∈ {1, 2}} t = 3", "assert ∑_{n ∈ ℕ} n = 0"] do
    let (outcome, _) ← outcomeOf harness [] text
    unless outcome.kind == "invalid" && mentions outcome.detail "no binder row reads" do
      throwError "`{text}` is {repr outcome}, not invalid for want of a reading row"

-- A statement two rows read is invalid: over a table in which `∑` writes the sum and the product
-- over a finite subset, `∑_{a ∈ A} a` is read by both. Over the registered rows of `∑` it is read.
run_cmd do
  let harness ← (Harness.empty : IO Harness)
  let (_, scope) ← outcomeOf harness ["let r(x) := x³ - 2x + 1 in ℚ[x]"] "assert 1 = 1"
  let text := "∑_{a ∈ ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots()} a"
  let state ← liftCoreM registryState
  let registered := state.binders.filter (·.token == "∑")
  let (kind, detail) ← readingBy scope registered text
  unless kind == "read" do
    throwError "`{text}` is not read by the registered rows of ∑: {kind}: {detail}"
  let some product := state.binders.find? (·.id.raw == "bind.sets.finite_product")
    | throwError "no row bind.sets.finite_product"
  let (kind, detail) ← readingBy scope (registered.push { product with token := "∑" }) text
  unless kind == "invalid" && mentions detail "several binder rows read" &&
      mentions detail "bind.sets.finite_sum" && mentions detail "bind.sets.finite_product" do
    throwError "`{text}` over the sum and the product is {kind}: {detail}, not invalid for two rows"

end CasCatalogue.BinderProbes
