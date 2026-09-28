/-
The `sage-categories` leaf probes as notebook specimens (`cc-probe-corpus`). Each specimen runs
through the public DSL surface only: `let … in …` ascriptions, method calls and `assert`.

## The ring diamond (CC-RESOLVE, CC-COHERE; #53 §9)

A ring reaches sets along its multiplicative port `Ring → Mon → Semigrp → Magma → Set` and along
its additive port `Ring → AddGrp → Grp → Mon → …`. The two routes carry different operations, so
`is_commutative` stays ambiguous (asserted in `Abelian.lean`); at `Set` they are identified by the
registered comparison `cmp.rings.carrier`, so `cardinality` resolves and is computed by the
registered table actions along the route.
-/
import CasDsl

namespace CasDslTests.ProbeCorpus

open Lean Elab Command
open CasDsl

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- `assert l rel r`, evaluated as the notebook evaluates it. -/
private def runAssert (env : Environment) (rel : AssertRel) (l r : CasExpr) :
    IO (Except EvalError (Option Bool)) := do
  let ctx : EvalCtx := { env, notes := ← IO.mkRef #[], annotations := ← IO.mkRef #[] }
  (evalAssert ctx rel l r).run

let R := ZZ/4 in Rings
let F := ZZ/5 in Rings

assert R.cardinality() = 4
assert F.cardinality() = 5
assert R.cardinality() ≠ 5

run_cmd do
  let env ← getEnv
  -- the two ports are one route to `Set` only by the registered comparison, which the audit names
  match ← Semantic.explain env "cat.rings" none (.domainObj (.mod 4)) "cardinality" with
  | .ok text =>
      for needle in ["identified:  the other routes by [cmp.rings.carrier]",
          "composed Lean-native actions"] do
        unless contains text needle do
          throwError s!"the audit of R.cardinality() does not mention {needle}:\n{text}"
  | .error e => throwError s!"the audit of R.cardinality() failed: {e}"
  -- …and they stay distinct where they carry different operations
  match ← runEval env (.method (.ref `R) `is_commutative #[]) with
  | .error e =>
      unless contains e.render "ambiguous" && contains e.render "fun.rings.additive_group" &&
          contains e.render "fun.rings.multiplicative_monoid" do
        throwError s!"R.is_commutative() did not report both ports: {e.render}"
  | .ok v => throwError s!"R.is_commutative() was answered ({v.render}) without choosing a port"

/-! ## Carriers of presented rings (CC-CARRIER)

`ℤ/2` is presented on the residues `{0, 1}`: the underlying-set functor's image is that set, computed
by the registered actions. `𝔽₉` is presented twice, by `x² + 1` and by `x² + x + 2` over `ℤ/3`
(Mathlib's `QuadraticAlgebra (ZMod 3) a b`, enumerated): two objects of `Rings` with their own
carriers. Their equality is not decided; the registered isomorphism `x ↦ y + 2` relates the first to
the second, and the reverse row's absence is reported as absence. -/

let F2 := ZZ/2 in Rings
let f(x) := x^2 + 1 in (ZZ/3)[x]
let g(x) := x^2 + x + 2 in (ZZ/3)[x]
let K1 := (ZZ/3)[x]/(f) in Rings
let K2 := (ZZ/3)[x]/(g) in Rings

assert F2.cardinality() = 2
assert K1.cardinality() = 9
assert K2.cardinality() = 9
assert K1 = K1

run_cmd do
  let env ← getEnv
  -- U(ℤ/2) is {0, 1}, the image the registered actions compute: the ring table of ℤ/2 is on
  -- `Fin 2` by the identity enumeration `Fin 2 = ZMod 2`, so its elements are the residues
  match ← Semantic.call env "cat.rings" none (.domainObj (.mod 2)) "contains"
      (withArguments := true) with
  | .ok { image? := some image, .. } =>
      unless image == Semantic.decodeSet (.finite 2) do
        throwError s!"U(ℤ/2) is {image.presentation}, expected the residues 0, 1"
  | .ok _ => throwError "`contains` on ℤ/2 has no decoded image"
  | .error e => throwError s!"`contains` did not resolve on ℤ/2: {e}"
  -- the two presentations of 𝔽₉: equality undecided, related by the registered isomorphism
  match ← runAssert env .eq (.ref `K1) (.ref `K2) with
  | .error e =>
      unless contains e.render "is not decided" &&
          contains e.render "iso.f9.quadratic.x_to_y_plus_2" do
        throwError s!"K1 = K2 was refused for another reason: {e.render}"
  | .ok v => throwError s!"K1 = K2 was decided ({v})"
  match ← runAssert env .eq (.ref `K2) (.ref `K1) with
  | .error e =>
      unless contains e.render "is not decided" &&
          contains e.render "no registered isomorphism relates them" do
        throwError s!"K2 = K1 was refused for another reason: {e.render}"
  | .ok v => throwError s!"K2 = K1 was decided ({v})"

/-! Elements of a presented ring are residue classes of polynomials (`let a := u in K1` is the
image of `u` under `(ℤ/3)[x] → K1`); `map a to K2` moves an element along the registered
isomorphism, and only along one. `x ↦ y + 2` sends `x` to `x + 2` of `K2`, and `x² = 2` in `K1` to
`2`. -/

let u(x) := x in (ZZ/3)[x]
let sq(x) := x^2 in (ZZ/3)[x]
let two(x) := 2 in (ZZ/3)[x]
let w(x) := x + 2 in (ZZ/3)[x]
let a := u in K1
let a2 := sq in K1
let t := two in K1
let c := w in K2

assert a2 = t
assert a ≠ t
assert map a to K2 = c
assert map a2 to K2 = map t to K2

/-- error: no registered isomorphism from (ℤ/3)[x]/(x^2 + x + 2) to (ℤ/3)[x]/(x^2 + 1): the element is not transported -/
#guard_msgs in
let back := map c to K1

/-- error: x ∈ (ℤ/3)[x]/(x^2 + 1) and x + 2 ∈ (ℤ/3)[x]/(x^2 + x + 2) are elements of different presented rings: equality is not decided; `map … to` moves an element along a registered isomorphism -/
#guard_msgs in
assert a = c

/-! ## Formed modules and lattices over the module fibration (CC-TRANSPORT, CC-FIB)

A Gram matrix ascribed to `BilinModules(ℤ)` is a ℤ-valued bilinear form on `ℤⁿ`; ascribed to
`Lattices(ℤ)` it must be symmetric. Their sets are reached along the registered structural route
through the fibre `Mod_ℤ` of the module fibration and its total category, and computed by the
registered actions. -/

let A2 := [2, -1; -1, 2] in Lattices(ZZ)
let E8 := [2, -1, 0, 0, 0, 0, 0, 0; -1, 2, -1, 0, 0, 0, 0, 0; 0, -1, 2, -1, 0, 0, 0, -1; 0, 0, -1, 2, -1, 0, 0, 0; 0, 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0; 0, 0, 0, 0, 0, -1, 2, 0; 0, 0, -1, 0, 0, 0, 0, 2] in Lattices(ZZ)
let B := [1, 2; 3, 4] in BilinModules(ZZ)

assert A2.cardinality() = ℵ₀
assert E8.cardinality() = ℵ₀
assert B.cardinality() = ℵ₀
assert A2.rank() = 2
assert E8.rank() = 8
assert B.rank() = 2

run_cmd do
  let env ← getEnv
  let a2 : Obj := .elem (.matrix 2 .int) (.mat 2 .int #[#[.int 2, .int (-1)], #[.int (-1), .int 2]])
  -- the lattice's route: its form, the form's module in the fibre Mod_ℤ, the total category, sets
  match ← Semantic.explain env "cat.lattice" (some .int) a2 "cardinality" with
  | .ok text =>
      for needle in ["cat.lattice --fun.lattice.forget_form--> cat.bilin_module \
--fun.bilin_module.forget--> cat.modules_r --fun.modules.fibre_inclusion--> cat.modules_total \
--fun.modules.underlying--> cat.sets", "realized by rz.lattice.int_gram",
          "composed Lean-native actions"] do
        unless contains text needle do
          throwError s!"the audit of A2.cardinality() does not mention {needle}:\n{text}"
  | .error e => throwError s!"the audit of A2.cardinality() failed: {e}"

-- a non-symmetric Gram matrix is a bilinear form and not a lattice
/--
error: [1, 2; 3, 4] ∈ Mat₂(ℤ) is not in Lattices(ℤ): no registered realizer realizes it there, and it is not constructed in a category that reaches it
-/
#guard_msgs in
let N := [1, 2; 3, 4] in Lattices(ZZ)

/-! ## Undecided is not false (CC-DECIDE)

`sage-categories` decided `False` for two equal homomorphisms whose component comparisons were
undecided. Here: `n ↦ 2n` and `n ↦ 6n` on `ℤ/2 → ℤ/4` are equal maps written differently, and
`n ↦ 2n`, `n ↦ 4n` are different ones; the surface computes a body in the source ring, which does
not give the values of a map into `ℤ/4`, so neither equality is decided — in particular neither is
`false` for the equal pair. Where evaluation decides, it decides both ways: on `ℤ/2 → ℤ/2` by the
two points, on `ℤ → ℤ` because a nonzero integer polynomial has finitely many roots. -/

let f := n ↦ 2n in ZZ/2 → ZZ/4
let g := n ↦ 6n in ZZ/2 → ZZ/4
let f4 := n ↦ 4n in ZZ/2 → ZZ/4
let p := n ↦ n^2 in ZZ/2 → ZZ/2
let q := n ↦ n in ZZ/2 → ZZ/2
let r := n ↦ n + 1 in ZZ/2 → ZZ/2
let h := n ↦ 2n in ℤ → ℤ
let k := n ↦ 3n in ℤ → ℤ

assert p = q
assert p ≠ r
assert h ≠ k

/-- error: the assertion outcome is unknown: the two sides of f = g are not comparable -/
#guard_msgs in
assert f = g

/-- error: the assertion outcome is unknown: the two sides of f ≠ g are not comparable -/
#guard_msgs in
assert f ≠ g

/-- error: the assertion outcome is unknown: the two sides of f = f4 are not comparable -/
#guard_msgs in
assert f = f4

end CasDslTests.ProbeCorpus
