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

/-- Fully apply a class to explicit arguments, synthesizing the class's OWN
instance parameters (`UniqueFactorizationMonoid` needs
`CancelCommMonoidWithZero`; `Module R M` needs `Semiring R` and
`AddCommGroup M`). The result is the class TYPE, ready for
`synthInstance`. -/
def classApp (cls : Name) (args : Array Expr) : MetaM Expr := do
  let mut e ← mkAppM cls args
  let mut ty ← whnf (← inferType e)
  while ty.isForall do
    let .forallE _ bt _ bi := ty | break
    unless bi == .instImplicit do
      throwError "{cls} has a non-instance parameter this check cannot fill"
    e := mkApp e (← synthInstance bt)
    ty ← whnf (← inferType e)
  return e

/-- Synthesize a class membership at a type. Failure is the honest report
that the claimed mathematics does not hold there. -/
def synthMembership (cls : Name) (T : Expr) : MetaM Unit := do
  discard <| synthInstance (← classApp cls #[T])

/-- Synthesize a class membership at explicit arguments — the
ring-parameterized form (`Module ℤ (ZMod n)`). -/
def synthMembershipAt (cls : Name) (args : Array Expr) : MetaM Unit := do
  discard <| synthInstance (← classApp cls args)

/-- Run `k` under instance binders for each class of `telescope` at `R` —
the hypotheses of a quantified derivation. -/
partial def withTelescopeInsts (R : Expr) (telescope : List Name)
    (k : MetaM α) : MetaM α :=
  match telescope with
  | [] => k
  | cls :: rest => do
      withLocalDecl `inst .instImplicit (← classApp cls #[R]) fun _ =>
        withTelescopeInsts R rest k

/-- The quantified inclusion edge, discharged by elaboration:
`∀ R [src-telescope R], tgt-class R` for every class of the target's
telescope. Returns the first class that does NOT follow, or `none` when the
edge is a theorem. -/
def synthEdgeImplication (srcTel tgtTel : Array Name) : MetaM (Option Name) := do
  let u ← mkFreshLevelMVar
  withLocalDecl `R .default (mkSort (mkLevelSucc u)) fun R =>
    withTelescopeInsts R srcTel.toList do
      for cls in tgtTel do
        try synthMembership cls R
        catch _ => return some cls
      return none

end CasDsl
