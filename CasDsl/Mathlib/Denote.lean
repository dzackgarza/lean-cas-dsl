/-
The denotation bridge: the ONE by-fiat correspondence of the semantic layer
(SPEC-REGISTRY-TYPE-PREPASS, invariant I3).

`Domain.denote` sends a runtime domain tag to the Lean TYPE its elements
inhabit: `.int ↦ ℤ`, `.mod n ↦ ZMod n`, `.poly c ↦ Polynomial (denote c)`.
Every claim the registry makes about a domain — membership in a category,
an inclusion edge, method availability — is an elaborated Mathlib term AT
THIS TYPE. This function is therefore the single place where "this runtime
value denotes an element of that type" is taken on faith; nothing else in
the semantic layer is.

ℝ deserves its note: the runtime presents exact algebraic reals (`√2`), and
they enter Mathlib's `ℝ` through the algebraic operations; the domain
denotes `ℝ` itself, not a bespoke subfield.

Instance-carrying type formers (`Polynomial` needs `[Semiring R]`) go
through `mkAppM`, so a coefficient domain whose denotation is not a semiring
fails LOUDLY here — the bridge never invents an instance.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import CasDsl.Value

namespace CasDsl

open Lean Meta

/-- The Lean type a `Domain` denotes. Total on the constructors; instance
synthesis inside (`Polynomial`, via `mkAppM`) may fail, and that failure is
the honest report that the composite domain has no ring structure to offer. -/
partial def Domain.denote : Domain → MetaM Expr
  | .nat => return mkConst ``Nat
  | .int => return mkConst ``Int
  | .rat => return mkConst ``Rat
  | .real => return mkConst ``Real
  | .complex => return mkConst ``Complex
  | .mod n => return mkApp (mkConst ``ZMod) (mkNatLit n)
  | .poly c => do mkAppOptM ``Polynomial #[some (← denote c), none]
  | .matrix n e => do
      let fin := mkApp (mkConst ``Fin) (mkNatLit n)
      mkAppM ``Matrix #[fin, fin, ← denote e]
  | .vector n e => do
      mkArrow (mkApp (mkConst ``Fin) (mkNatLit n)) (← denote e)
  | .funcs s t => do mkArrow (← denote s) (← denote t)
  | .series c => do mkAppM ``PowerSeries #[← denote c]

end CasDsl
