# Elementary mathematics

Definitions use :=. Equality = is a proposition. The command assert states that proposition: the language reads it through `lean-categories`' mathematics, runs whatever computations are installed for the operations it names, and compares the computed values. A computation supplies values only; it never decides or establishes a proposition, and nothing it reports about itself is believed. A proposition may also be stated bare — the cell then displays its truth value, `true | false | unknown` — while assert is the collapsing form: it commits only on `true`, and `false` and `unknown` are both assertion failures.

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

## Registered actions, components, and selected lifts

The following forms consume declarations already registered by `lean-categories`.
Names in angle brackets below stand for actual registered names or identifiers;
they are not new declarations. Identifiers containing punctuation can be written
with Lean's identifier quotes, for example `«the.registered.identifier»`.
All parameters are supplied in declaration order and are checked against the
complete dependent signature.

A registered morphism family can also be selected from a complete object with
`X.<family>()`, then applied with `X.<family>(a, …)`. The reader tries the supplied
receiver at the declaration's applicable explicit parameter slots. Its complete
dependent type may determine preceding ring, module, category, or other structure
parameters. Every such parameter must be completely fixed by that type; equality
of underlying carriers does not select a structure. Several applicable slots or
distinct complete readings remain ambiguous. A positional call
`<family>(p₁, …, pₙ)` still supplies parameters in declaration order; it does not
skip leading parameters merely because a later argument might determine them.

An object construction uses its registered surface name. Its final argument is
the selected source object; preceding arguments are the construction's explicit
parameters:

```text
<construction>(p₁, …, pₙ, X)
map f along <construction>(p₁, …, pₙ)
```

The second form is the same construction's map action. Its source and target
are the construction applied to the exact source and target of `f`. If the
declaration consumes a category and that argument is omitted, the selected
object's own complete category context supplies it. For a construction on the
core category, an accepted invertible presentation or component supplies both
directions of its isomorphism. A general morphism cannot stand in for that
isomorphism. Applicable registered meanings are compared together; a construction
name does not take precedence over another applicable declaration.

Select a whole registered presentation map, with all its declaration parameters,
using these forms:

```text
let e := presentation(<presentation-name-or-id>(p₁, …, pₙ))
let e_inv := inverse_presentation(<presentation-name-or-id>(p₁, …, pₙ))
map e along <construction>(q₁, …, qₘ)
map e_inv along <construction>(q₁, …, qₘ)
```

Each selector returns the corresponding directed map while retaining the original
accepted isomorphism and both its directions. This is the complete input needed
by a construction whose source is a core category. It is distinct from applying
the comparison to an individual element with `map t along P` or
`map t back along P`. Empty parameter lists are written `P()`.

A registered functor can be selected explicitly, including when it is not a
structural inheritance edge. An exact registered classifier identifier selects
that classifier's accepted forgetful action. Both kinds of action have an object
selector and a whole-map selector:

```text
view X along <functor-id>
view X along <functor-id>(p₁, …, pₙ)
map f along <functor-id>(p₁, …, pₙ)
view X along <classifier-id>(p₁, …, pₙ)
map f along <classifier-id>(p₁, …, pₙ)
```

The selected declaration fixes the complete source and target categories and all
dependent parameters. A map action applies to the original whole morphism and
both of its exact endpoints. Classifier forgetful actions consume an object or
morphism of the already formed classifier total category; they supply no new
property evidence. Explicit parameter lists remain in declaration order, and a
map selector with no parameters is written with `()`. Applicable functor,
classifier-forget and construction map declarations participate in the same
ambiguity check; their registry kind does not assign precedence.

Registered category names and functor identifiers may also occur in an explicit
parameter slot whose declared type asks for that category or functor. Category
parameters retain their full structure and ordered parameters. A value in an
accepted constructed category retains that entire category expression and its
typed bundle even when the registry has no separate name for the expression.
Subsequent composition, selected action, and inherited method or property
resolution use this retained context.

Family reindexing has the public forms `reindex(X, baseMap)` and
`reindex(f, baseMap)`. The first uses the selected reindexing's object action; the
second uses its map action on the whole fibre morphism, retaining both complete
endpoints. The registered family determines variance and all dependent parameters.
For restriction of scalars, a base map `φ : R → S` takes the fibre over `S` to the
fibre over `R`. `cartesian(X, φ)` selects the canonical cartesian map from
`(R, reindex(X, φ))` to `(S, X)` in the total category of that same accepted family.
Its complete parameters, original base map and receiver remain attached to the
map and both endpoints. It can be composed or applied to a compatible generalized
map. Several applicable registered reindexings are an ambiguity. An independently
registered morphism continues to use its ordinary registered name and declared
argument order.

A natural cell component fixes the registered cell, all its data parameters,
the complete receiver, and an ordered constructor path:

```text
component(<cell-id>(p₁, …, pₙ), X, [])
component(<cell-id>(p₁, …, pₙ), X, [<outer-constructor-id>, <inner-constructor-id>])
inverse_component(<cell-id>(p₁, …, pₙ), X, [<constructor-id>])
```

An empty path selects the base cell. Constructor identifiers run from the outer
construction to the inner construction; the receiver is an object of that full
constructed source category. An arrow can be supplied directly when that receiver
is an object of the arrow category. Each constructor must publish the required
accepted comparison action. An inverse requires the registered cell to be
invertible. The result is a typed morphism with both exact endpoints, usable in
ordinary composition and generalized application. For `f : A → B` and
`u : D → A`, `f(u)` retains the full original domain `D` and yields `D → B`.
No restriction to terminal domains or graph presentations is imposed by these
forms.

An explicit subobject lift selects the registered evidence family as well as its
original source and base inclusion:

```text
let L := lift(X) along <lift-id>(p₁, …, pₙ) with m using proof(<monicity-term>)
L.obj()
L.hom()
L.forward()
L.backward()
factor(g) through L with f using proof(<compatibility-term>)
```

For the selected functor `U`, the inclusion has type `m : S → U(X)` and the
monicity term is checked at `Mono m`. The four projections are the lifted object,
its defining map to `X`, and the forward and backward maps between its image and
`S`. A factor call keeps the original generalized domain `D`, with
`f : D → X`, `g : U(D) → S`, and a checked term of
`U.map f = g ≫ m`; its result has type `D → L.obj()`.
The same projections and factor call apply to a method result with prescribed
lifts. For several prescribed stages, the forward and backward fields use every
declared functor map and comparison in order, and factorization runs through all
the selected stages. Taking `.obj()` retains the complete selected lift for later
field access and factorization.

For separately selected successive lifts, choose their composition explicitly:

```text
let inner := lift(U(X)) along <inner-lift>(…) with m using proof(<monicity-term>)
let outer := lift(X) along <outer-lift>(…) with inner.hom() using proof(<monicity-term>)
let L := composite_lift(outer)
L.forward()
L.backward()
factor(g) through L with f using proof(<composite-compatibility-term>)
```

Here `U(X)` denotes the actual selected outer functor image, obtained by its
registered `view … along …` form. `composite_lift` follows the retained defining-map
links and checks each pair of adjacent complete category contexts, selected
actions, source objects and inclusions. It keeps every stage's already returned
four-field packet and its owners. The ordinary `outer.forward()` and
`outer.backward()` still denote the outer stage's own comparisons. On `L`, these
fields compose all selected comparison maps with the intervening declared functor
maps. The composed factor keeps the original full cone domain and consumes the
accepted factor and source equations at every stage, starting at the deepest
stage. Taking `L.obj()` retains that complete selection. Unrelated lifts are never
joined by comparing the shapes or carriers of their results.

A registered universal construction retains its complete accepted presentation,
apex, returned data and defining legs. For an apex `K`, `K.obj()` is that apex and
`K.leg(i)` selects the defining leg at the actual diagram index `i`. `K.field(i)`
selects the `i`th non-proposition data port of the registered `dataConstructor`,
in its declared order. A data-port index is different from a diagram-leg index.
`K.hom()` selects the defining map when that schema has exactly one independent
morphism port. Several such ports require `field(i)` or `leg(i)` explicitly;
their order or equality at a particular input does not choose a map.

An ordinary complete subobject has `obj()` (also `source()`), `target()`,
`hom()`, and `inclusion()`. These project its actual underlying object, ambient
object, defining map, and whole Arrow object. A whole Arrow has the same endpoint
and map projections. They use the accepted constructor's actual typed fields,
including registered aliases, and retain all category parameters and original
computational owners. Thus an ordinary kernel or cokernel exposes its defining
map through its registered universal schema, while a subobject-valued method
exposes its complete inclusion without requiring a selected lift. A result with a
prescribed or explicit lift additionally has the four selected-lift fields above.
Every field remains tied to the whole original result; projecting it supplies no
universality, monicity, comparison law, or mathematical equality from returned data.

An already admitted whole coefficient family can be supplied directly to a
registered binder:

```text
let a := rawFamily in <declared-family-object> using (proof(<condition-term>))
binder(<binder-id>(p₁, …, pₙ), a)
```

The explicit parameters are the binder operation's ordered declaration
parameters. The last argument is one whole element of its exact admitted input
object, or a complete generalized map into that object. The selector uses the
given admission and preserves the original generalized domain. Binding notation
such as `∑_{i ∈ A} body` remains the separate form that constructs and admits a
body family before applying its registered operation.

`proof(<Lean term>)` is a formal input checked at the exact proposition required
by the declaration. It must be closed and contain no `sorry`. Computational
answers never supply these proofs or choose a different lift, cell, constructor,
category, or endpoint. All these forms fix their mathematical meaning before any
implementation is selected; missing computation is reported separately.

## Explicit proof parameters

A proposition-valued parameter of a registered declaration can be supplied as
`proof(p)`, where `p` is a closed Lean theorem or proof term. The reader checks it
against that declaration's complete proposition, including its selected parameters.
This syntax supplies formal input; a computational result does not supply a proof.

For a fixed record type with one data field and proposition-valued remaining fields,
`t in X using (proof(p), ...)` supplies the constructor's obligations in field order.
The target `X` and its data-field type must already be determined. A generalized point
keeps its original domain, and each proof must cover that entire domain rather than
one sample point. The actual data map remains available for subsequent computations.
No proof term is sent through the computational port.

## Polynomials

A named object can expose a distinguished generator through its mathematical declaration.
`generator(X)` reads that generator; `generator(X, i)` reads an indexed generator when the
declaration has an index. This keeps the selected object and its parameters.

A registered presentation comparison has a name and fixed source and target presentations.
`map t along P` applies its forward map; `map u back along P` applies its inverse. The chosen
comparison and the endpoint data remain part of the question. The language checks each argument
at the declared source or target; naming two objects with the same carrier does not identify them.
These forms apply to any registered generator or presentation comparison.

Use `X in Groups`, `X in FiniteSets`, or another category's registered surface name to select
the declared structure when the same display name denotes objects with different structures.

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
