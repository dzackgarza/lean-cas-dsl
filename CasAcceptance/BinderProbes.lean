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
* **A statement two rows read is a semantic ambiguity.** Over a table in which `∑` writes both the sum and the
  product over a finite subset (`bind.sets.finite_sum`, and `bind.sets.finite_product` given the
  token `∑`; a table of this probe, registered nowhere), `∑_{a ∈ A} a` for the finite set `A` of
  the complex roots of `x³ - 2x + 1` is read by both rows, and is ambiguous. Over the registered
  rows of `∑` alone it is read.
* **A row that refuses an argument does not read it; the others still may.** Over the rows of `lim`
  and a row of this probe whose point is a point of `Fin 2` (registered nowhere), the numeral `5`
  is no numeral of `Fin 2` (`5 < 2` does not hold): that row does not take it, and
  `lim_{t → 5} t` is read by `bind.sets.limit`.
* **Rows are told apart by declaration, not by carrier.** Two rows of this probe (registered
  nowhere) land in `ℝ²` (`Vec(ℝ, 2)`) and in `Maps(Fin 2, ℝ)`, objects with one carrier
  `Fin 2 → ℝ`. A body in `ℝ²` is read by the first alone: adding the second changes nothing.
* **The separator is the notation's.** `∑_{n → ℕ} n` and `lim_{t ∈ 0} t` are no terms of the
  language: a sum ranges over a set (`∈`), a limit is taken at a point (`→`).
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

-- A statement two rows read is a semantic ambiguity (its own stratum, not invalid): over a table in which `∑` writes the sum and the product
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
  unless kind == "ambiguous" && mentions detail "several binder rows read" &&
      mentions detail "bind.sets.finite_sum" && mentions detail "bind.sets.finite_product" do
    throwError "`{text}` over the sum and the product is {kind}: {detail}, not ambiguous for two rows"

/-- A family of this probe, registered nowhere: its point is a point of `Fin 2`, so it refuses
the numerals that are no numerals of `Fin 2`. -/
noncomputable def pointOfFinTwo {b : CasCatalogue.Foundation.Objects.fin 1 ⟶
    CasCatalogue.Algebra.NumberSystems.reals}
    (_ : CasCatalogue.Foundation.Objects.fin 1 ⟶ CasCatalogue.Foundation.Objects.fin 2) :
    CasCatalogue.Algebra.RealLimits.convergentMaps b ⟶ CasCatalogue.Algebra.NumberSystems.reals :=
  CasCatalogue.Algebra.RealLimits.limit b

-- A row that refuses an argument does not read it, and the other rows of its token still may:
-- `5` is no numeral of `Fin 2`, and `lim_{t → 5} t` is read by the limit at a real point.
run_cmd do
  let state ← liftCoreM registryState
  let registered := state.binders.filter (·.token == "lim")
  let some limit := registered.find? (·.id.raw == "bind.sets.limit")
    | throwError "no row bind.sets.limit"
  let refusing := { limit with id := ⟨"bind.probe.fin_two"⟩,
                               operation := ``CasCatalogue.BinderProbes.pointOfFinTwo }
  let text := "lim_{t → 5} t"
  for rows in [registered, registered.push refusing, #[refusing] ++ registered] do
    let (kind, detail) ← readingBy {} rows text
    unless kind == "read" do
      throwError "`{text}` over {rows.toList.map (·.id.raw)} is {kind}: {detail}, not read"
  let (kind, detail) ← readingBy {} #[refusing] text
  unless kind == "invalid" && mentions detail "no binder row reads" do
    throwError "`{text}` over the refusing row alone is {kind}: {detail}, not invalid"

/-- A family of this probe, registered nowhere: from the maps `ℝ ∖ {a} → ℝ²` to `ℝ²`. -/
noncomputable def intoVectors (a : CasCatalogue.Foundation.Objects.fin 1 ⟶
    CasCatalogue.Algebra.NumberSystems.reals) :
    CasCatalogue.Foundation.Maps.maps (CasCatalogue.Algebra.RealLimits.puncturedLine a)
        (CasCatalogue.Algebra.LinearAlgebra.vectors CasCatalogue.Algebra.NumberSystems.reals 2) ⟶
      CasCatalogue.Algebra.LinearAlgebra.vectors CasCatalogue.Algebra.NumberSystems.reals 2 :=
  TypeCat.ofHom fun _ _ => 0

/-- A family of this probe, registered nowhere: from the maps `ℝ ∖ {a} → Maps(Fin 2, ℝ)` to
`Maps(Fin 2, ℝ)`, whose carrier is the carrier of `ℝ²`. -/
noncomputable def intoMaps (a : CasCatalogue.Foundation.Objects.fin 1 ⟶
    CasCatalogue.Algebra.NumberSystems.reals) :
    CasCatalogue.Foundation.Maps.maps (CasCatalogue.Algebra.RealLimits.puncturedLine a)
        (CasCatalogue.Foundation.Maps.maps (CasCatalogue.Foundation.Objects.fin 2)
          CasCatalogue.Algebra.NumberSystems.reals) ⟶
      CasCatalogue.Foundation.Maps.maps (CasCatalogue.Foundation.Objects.fin 2)
        CasCatalogue.Algebra.NumberSystems.reals :=
  TypeCat.ofHom fun _ _ => 0

-- Rows are told apart by declaration: a body in `ℝ²` is read by the row landing in `ℝ²`, and a row
-- landing in `Maps(Fin 2, ℝ)`, which has the same carrier, neither reads it nor makes it ambiguous.
run_cmd do
  let state ← liftCoreM registryState
  let some limit := state.binders.find? (·.id.raw == "bind.sets.limit")
    | throwError "no row bind.sets.limit"
  let vectors := { limit with id := ⟨"bind.probe.into_vectors"⟩,
                              operation := ``CasCatalogue.BinderProbes.intoVectors }
  let maps := { limit with id := ⟨"bind.probe.into_maps"⟩,
                           operation := ``CasCatalogue.BinderProbes.intoMaps }
  let text := "lim_{t → 0} (sin(t), sin(t))"
  let (kind, detail) ← readingBy {} #[vectors] text
  unless kind == "read" do
    throwError "`{text}` over the row into ℝ² is {kind}: {detail}, not read"
  for rows in [#[vectors, maps], #[maps, vectors]] do
    let (kind', detail') ← readingBy {} rows text
    unless kind' == kind && detail' == detail && !mentions detail' "into_maps" do
      throwError "`{text}` over {rows.toList.map (·.id.raw)} is {kind'}: {detail'}, not as over \
        the row into ℝ² alone ({kind}: {detail})"

-- The separator is the notation's: a sum over a set is written with `∈`, a limit with `→`.
run_cmd do
  for text in ["∑_{n → ℕ} n", "∏_{n → ℕ} n", "lim_{t ∈ 0} t"] do
    if let .ok _ := Parser.runParserCategory (← getEnv) `cas_term text then
      throwError "`{text}` is read as a term of the language"

end CasCatalogue.BinderProbes
