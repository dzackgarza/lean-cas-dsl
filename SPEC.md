# Elementary mathematics

Definitions use :=. Equality = is a proposition. The command assert asks the available computational backend to decide or establish that proposition.

## Exact number systems

```text
assert 2 + 3 = 5
assert 2 + 3 = 0 in ℤ/5
assert gcd(84, 30) = 6

(360).factor()
# 2³ · 3² · 5

assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ

assert -3 ∈ ℤ
assert 7/3 ∈ ℚ
assert √2 ∈ ℝ
assert 2 + 2i ∈ ℂ

```

```text
let z := 2 + 2i in ℂ
assert z.re() = 2
assert z.im() = 2
assert z.bar() = 2 - 2i
assert z · z.bar() = 8
assert |z| = 2√2

```

Numerical approximation is an operation on exact elements:

```text
map √2 to ℝ/O(1/10^{10})
# 1.4142135623 + O(1/10^{10})

```

## Finite sets
Sets generally work by denoting `{ x ∈ X| P(x)}.` or `{ f(x) | x ∈ X, P(x)}` etc.

Plain numbers are naturally elements of ZZ.

```text
let A := {1, 2, 3} in 𝒫(ℤ)
let B := {3, 4, 5} in 2^ℤ

assert A ∪ B = {1, 2, 3, 4, 5}
assert A ∩ B = {3}
assert A \ B = {1, 2}
assert A △ B = {1, 2, 4, 5}

assert |A| = 3
assert |A × B| = 9
assert |𝒫(A)| = 2^|A|

```

```text
assert 2 ∈ A
assert 4 ∉ A
assert A ⊆ A ∪ B
assert A ∩ B ⊆ A

```

## Set comprehensions

```text
let S := {n ∈ ℤ | n² ≤ 20} 
assert S in 𝒫(ℤ)

assert S = {-4, -3, -2, -1, 0, 1, 2, 3, 4}
assert |S| = 9

```

```text
let E := {2n | n ∈ ℕ} 
assert E in 𝒫(ℕ)

assert 8 ∈ E
assert 9 ∉ E
assert |E| = ℵ₀

let m2: ℕ → ℕ := n ↦ 2n
assert m2(ℕ) = E
assert m2.image() = E

{m2(n) | n ∈ ℕ, 0 ≤ n < 6}
# {0, 2, 4, 6, 8, 10}

```

## Functions

```text
let h := t ↦ t² + 1 in ℝ → ℝ
let hp(t) := t^2 + 1 in R->R
assert h = hp
assert h(0) = 1
assert h(3) = 10
assert h(-t) = h(t)

```

## Polynomials

```text
let p(x) := x³ - 2x + 1 in ℤ[x]

assert x ∈ ℤ[x]
assert p ∈ ℤ[x]
assert p.deg() = 3
assert p(1) = 0

p.factor()
# (x - 1)(x² + x - 1)
q := map p to ℂ[x]
q.factor()
# (x-1)(x - (-1+√5)/2)(x - (-1-√5)/2)

```

```text
let q := x ↦ x² - 2 in ℚ[x]
assert q(√2) = 0
assert q(-√2) = 0
assert q.roots() ⊆ ℂ - ℚ

```

## Differentials

```text
let f := x ↦ 3x² + x + 1 in ℚ[x]
let X := Spec ℚ[x] in Schemes/ℚ

d
# d_{X / Spec ℚ} : 𝒪_X → Ω¹_{X / Spec ℚ}
#
# On global sections:
#
# ℚ[x] → Ω¹_{ℚ[x] / ℚ} ≅ ℚ[x] dx

```

```text
assert f ∈ ℚ[x]
assert f.deg() = 2
assert f(2) = 15

assert d(f) = (6x + 1) dx
assert (d/dx)(f) = 6x + 1

```

The differential is the universal relative differential. Its displayed coordinate expression uses

[  
\Omega^1_{\mathbf Q[x]/\mathbf Q}\cong \mathbf Q[x],dx.  
]

## Indefinite integration

```text
kernel(d/dx : ℚ[x] → ℚ[x])
# ℚ

```

```text
∫ f dx
# x³ + (1/2)x² + x + ℚ
assert ∫ f dx = x³ + (1/2)x² + x + ℚ
```

The result is a coset of the kernel of differentiation, equivalently the complete set of primitives.

```text
let Fs := {h ∈ ∫ f dx | h(0) = 0} in 𝒫(ℚ[x])
assert Fs.cardinality() = 1
let F := Fs[0] in ℚ[x]

assert F(x) = x³ + (1/2)x² + x
assert d(F) = f dx
assert (d/dx)(F) = f

```

## Elementary calculus

```text
assert lim_{t → 0} sin(t)/t = 1
assert lim_{t → ∞} 1/t = 0

```

```text
assert ∫₀¹ t² dt = 1/3
assert ∫₀^π sin(t) dt = 2

```

```text
let f := t ↦ e^t in ℝ → ℝ
# Taylor expansion: 𝒪_X → 𝒥^∞_X
let Tf := f.taylor_expansion(0) in ℝ[[t]]
assert Tf ∈ ℝ[[t]]
map Tf to ℝ[[t]]/(t^6)
# 1 + t + t²/2 + t³/6 + t⁴/24 + t⁵/120 + O(t⁶)

```

```text
let g: ℝ → ℝ := t ↦ sin(t)
let Tg := g.taylor_expansion(0) in ℝ[[t]]
assert Tg ∈ ℝ[[t]]
map Tg to ℝ[[t]]/(t^8)
# t - t³/6 + t⁵/120 - t⁷/5040 + O(t⁸)

```

## Vectors and matrices

```text
let M := [1, 2;
          3, 4]
 in Mat₂(ℚ)
let v := (1, 2) in ℚ²
let b := (5, 11) in ℚ²

```

```text
assert M*v = b
assert M.det() = -2
assert M.rank() = 2
assert M.ker() = {0}

```

```text
M⁻¹
# [-2,   1;
#  3/2, -1/2]

```

```text
assert M⁻¹ b = v
assert M⁻¹(M v) = v
assert M(M⁻¹ b) = b

```

## Subspaces and spans

```text
let u₁ := (1, 0, 1) in ℚ³
let u₂ := (0, 1, 1) in ℚ³

let W := span_QQ{u₁, u₂} \leq ℚ³ in Mod(QQ)
# N.B.: \leq means subobject in a category

assert W.dim() = 2
assert (1, 1, 2) ∈ W
assert (1, 1, 0) ∉ W

```

```text
let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c

assert W = ker φ

```

## A composed computation

```text
let r(x) := x³ - 2x + 1 in ℚ[x]
let roots := {a ∈ ℂ | r(a) = 0} in 𝒫(ℂ)

assert |roots| = 3
assert 1 ∈ roots
assert ∑_{a ∈ roots} a = 0
assert ∏_{a ∈ roots} a = -1

```

```text
let C := r.companion_matrix()

assert C.charpoly() = r
assert C.det() = -1
assert C.trace() = 0

```


```text
let f(t) = t^2 in RR->RR
let g(t) = t^3 in RR->RR
assert (f ∘ g)(t) = t^6
```

# Ellipses

Much like Haskell, ellipses `...` can be used to denote an infinite sequence inferred from a finite pattern.

```text
let X := {0,1,2,...}
assert X = \NN
let Y := {0, 2, 4, ...}
assert Y = {2n | n in \NN}
assert Y = 2\NN
let f: NN -> NN := n ↦ n^2
let Z := {n in \NN | f(n) \in 2\NN}
let primes := {n in \NN | n.is_prime() }
```

It can also be used to infer a continuation of a finite pattern filling in the missing elements:

```text
let R := CC[x_0, x_1, ..., x_9]
assert R in Algebras/CC
assert R.dimension() is 10
```

Note that `is` just means `=`.


```text
let f(t) = ∑_{n ∈ \NN} n^2 t^n \in ZZ[[t]]
map f to ZZ[[t]] / O(t^5)
# t + 4t^2 + 9t^3 + 16 t^4 + O(t^5)
f
# t + 4t^2 + 9t^3 + 16 t^4 + ...
assert [t^2]f = 4
```
