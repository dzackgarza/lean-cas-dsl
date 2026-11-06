# Coverage and independent derivations

The fixed source questions are `../questions.md`; their original mathematical
sources are `../source-notes.md`. This supplement completes public syntax without
changing any selected input, proposition, expected answer, negative control, or
required execution. The files have not been admitted or run. A source expression
is not evidence that the current reader interprets it correctly.

## Source files and full obligations

| Scope | Concrete source | Full requirement retained beyond individual scalar samples |
| --- | --- | --- |
| RX-01 | `rx01-selected-orders.cas` | Selected ordinary and reverse relations on the original `Fin 5`; existing forgetful functor and cardinality; the false reverse-order relation |
| RX-02 | `rx02-two-subsets.cas` | The actual inclusion into `𝒫_fin(Fin 5)`; direct image on every complete specified bijection; full functor identity/composition equations; singleton exclusion |
| RX-03 | `rx03-cyclic-automorphisms.cas` | Both selected group-comparison directions, complete `Aut` map actions and inverse composites, actual unit inputs, group operations and order four; entire automorphism coordinate and conjugation equations |
| RX-04 | `rx04-square-bound.cas` | Exact predicate on all integers; classifier at its original subtype; finite refinement; full original admission/inclusion equation; all integers not finite |
| RX-05 | `rx05-carrier-diamond.cas` | Both complete routes, actual `cmp.rings.carrier` at the forgotten selected field, both component directions, whole coefficient-map naturality, distinct operations, and all declaration-environment controls |
| RX-06 | `rx06-reindexing.cas` | Exact quotient coefficient map, actual family reindexing and cartesian map, complete scalar action, complete nonidentity module arrow and its reindexed action |
| RX-07 | `rx07-f9-transport.cas` | Actual nonidentity comparison, inverse equations and coefficient maps; element reuse and whole-map reuse with original domain `ZMod 3` |
| RX-08 | `rx08-ordinary-kernel.cas` | Actual nonsquare row, complete ordinary kernel/inclusion, selected restriction and generalized coordinate map, full pairing; ordinary universal property and impossibility for every target form |
| RX-09 | `rx09-successor-series.cas`; `rx09-constant-one-rejection.cas` | Whole infinite function, exact topology and summability evidence, actual admitted record and old binder, every coefficient; nonsummability and nonexistence of an admission for constant one |
| RX-10 | `rx10-fixed-execution-question.cas` | One complete question and whole returned callable under all six execution conditions and the separate ownership controls |
| RX-LIFT | `rx-lift-prescribed-stages.cas`; `selected-lift-requirements.md` | Factor-two prescribed kernel, genuine formed arrow, successive use of the actual first inclusion, composed comparisons, nonzero full-domain cones, both universal factorizations and uniqueness |

`expected-facts.lean` contains mathematical-only examples for the full formulas and
universal negatives. They add no local mathematical definition or registry entry.
Their role is to state and source expected facts; they do not replace public-language
execution or the full interpretation review.

`coordinate-presentations.md` records the exact upstream carrier reductions for
RX-08 and RX-LIFT. Their vector domains are `Fin 2 → ℚ`; the paired forms' value
module has carrier `ℚ × ℚ`. The existing vector bindings and expected values
remain unchanged, and the separate complete formed cone-source comparison is
still required.

## Public specification consumed

`[P07]` is `SPEC.md` at kernel document commit
`0d546c549f5aa650f90c675706237cf0a7f02056`, read with `git show` only.
It explicitly supplies both

```text
view X along identifier(parameters)
map f along identifier(parameters)
```

for exact registered functor identifiers and classifier identifiers. A classifier
identifier selects its already accepted forgetful action. These operations preserve
complete endpoints and retain ambiguity among applicable declarations. Empty map
parameter lists use `()`.

This closes the original surface requirements S02/S03 concerning explicit
classifier-forgetful routes and the commutative-ring map action. In particular,
the RingCat quotient map in RX-06 is the forgetful action on the existing
`integerCoefficients`, not a reconstructed residue function. RX-05 explicitly
retains the field forgetful step before its ring receiver and each subsequent
route step. The complete-map presentation selectors, ordinary structured-result
fields, reindexing, cartesian maps and explicit admitted binder form were already
supplied in `SPEC.md` at the worktree base `7df8d13`.

The earlier `[P01]` explicit single-data-field admission paragraph also remains a
public source for the generalized subtype input in RX-08 and the range point in
RX-LIFT. Each proof covers the actual original domain. No proof term is used to
smuggle an unregistered data input through the computational boundary.

`[P08]` is `SPEC.md` at
`f91870b6009cd0e3cd041488066ea1b898d4689c`, also read with `git show` only.
Its generic member rule selects a whole morphism family from a complete receiver,
as in `X.pairing()`. The receiver's full dependent type fixes the scalar and value
module. The explicit `composite_lift(second)` follows the retained link from the
actual first defining map; it supplies the composed comparisons and factor while
the ordinary second-stage fields keep their own endpoints. RX-LIFT uses these
public forms, preserving the separate cone-domain comparison requirement.

## Source-derived expected values and separating facts

### RX-01 and RX-02

`ordinary_carrier_card 5` and `reverse_carrier_card 5` both specialize
`Cardinal.mk (Fin 5)=5`. `ordinary_five_zero_le_one` is true, while
`reverse_five_not_zero_le_one` says that this same pair of finite ordinals does
not satisfy the reversed relation. The equal cardinalities therefore do not
identify the selected order data. `[M01,M13]`

Two-element subsets are unordered subsets with two distinct members. Their number
is `choose(5,2) = 5*4/2 = 10`. The source `map_extent` fixes the entire action as
direct image, and `singleton_not_member` excludes a repeated element. A generic
set map that identifies two members does not belong to the required core-arrow
domain. `[M02]`

### RX-03

The quotient comparison sends `[k]` to the residue of `k`. Every group
automorphism is multiplication by a unit of `ZMod 5`, whose four units are
`1,2,3,4`. The selected coefficient two has inverse three because `2*3=6≡1`.
Its square is four, not one; its fourth power is one. An element whose fourth
power is one and whose square is not one has order four, since its order must
divide four and neither proper divisor is possible. Thus the two power
assertions preserve the exact `orderOf(a)=4` expectation without introducing
an unregistered order operation. `[M03]`

The admitted unit with underlying value two is the source's `unitTwo`: units
are determined by their values (`Units.ext`), and an inverse is unique. This
does not choose a new automorphism. `cyclic_quotient_aut_by_unit(5)` is the
existing full group morphism and sends that actual unit to the source's
`byUnit 5 unitTwo`.

The existing generic `Aut` map is `Aut.autMulEquivOfIso e`, with complete
action `v ↦ e ∘ v ∘ e⁻¹`. Its inverse is the action at the retained inverse
isomorphism. The `.cas` files select both actual presentation maps and both
construction-map actions. The residue group is publicly named `ZMod(5) in Groups`;
the mathematical phrase `Cyclic(5)` in the original question refers to
`FiniteGroups.cyclic 5`, not an additional public name. `[M03,M04]`

### RX-04 and RX-05

For integers, `n²≤9` is equivalent to `-3≤n≤3`, yielding exactly the seven
specified integers. The finite refinement forgets to that original subtype;
`admission_retains_subset` retains the complete point and its original inclusion
into the power set of all integers. The final RX-04 assertion is read in that
ambient power set, so its interpretation must use the declared
`FiniteSubsets.inclusion`; it is not equality of two independently generated
lists. The entire integer set remains infinite. `[M05]`

At the selected prime-residue field, both carrier routes have five elements and
the actual carrier comparison and its inverse are identity functions at their
specified endpoints. Naturality holds on every ring homomorphism. The chosen
integer coefficient map supplies a concrete nontrivial-source full-map
observation; `7≡2 (mod 5)`. Addition and multiplication remain different because
`1+1=2` while `1*1=1`. `[M06,M07,M08]`

The four declaration environments in `../observation-controls.md` remain
mandatory. Reordering declarations cannot select a route. Omitting the cell,
while retaining both complete routes and supplying no resolving comparison,
must leave the semantic ambiguity visible. A computation manifest does not
select these mathematical environments.

### RX-06 and RX-10

The selected quotient is the actual forgetful image of `integerCoefficients`.
The regular module over `ZMod 5` has dimension one. Reindexing keeps its additive
carrier and changes scalar action to `r•m=q(r)m`. Therefore its cardinality is
five, and the three fixed samples are `2•3=1`, `5•1=0`, and `(-1)•2=3`.
These equations neither give freeness over the integers nor assert integer
dimension one. `[M08]`

`reindex_map_apply` retains the whole function of every actual source module
map. At the fixed nonidentity arrow `2 • LinearMap.id`, every residue is doubled,
and three goes to one. The type of the lambda in both files must therefore be
that **module** arrow, not merely an equally displayed set function. Its
linear-map formation is an interpretation obligation, not a request for a new
specialized doubling registration.

`cartesian(N,q)` retains the selected base map by construction;
`five_cartesian_base` fixes its base-projection equation and
`five_cartesian_carrier` fixes its complete identity carrier function. The
original quotient must remain in the complete interpreted question even though
the carrier observation is an identity function.

RX-10 has exactly one assertion. All six report conditions use its unchanged
file, mathematical inputs and expected residue one. Neither a wrong returned
residue nor an exception changes its proposition. The ownership controls still
require reuse of the actual computed callable on its original live session.

### RX-07

The selected quotient relations give `x²+1=0` and `y²+y+2=0` in characteristic
three. Since `e(x)=y+2`, one has `e(x+1)=y`; then `y²=2y+1`; applying the
selected inverse gives `2(x-2)+1=2x`. These are independent ring calculations.
The source comparison fixes every coefficient, so the entire maps on `ZMod 3`
have the three formulas in the original question, not just the sample at one.
Each later binding in the file consumes the preceding actual map or value.
`comparison_root_ne` retains the nonidentity control. `[M09,M10]`

### RX-08

The actual row `[1,0]` sends `(a,b)` to `a`, so its kernel consists of `(0,t)`.
The coordinate equivalence gives dimension one. Substituting `(0,s),(0,t)` in
`2ac+3bd` yields `3st`, hence the fixed value three at `(1,1)`. The coordinate
admission in the file retains the entire map `t↦(0,t)` into the actual restriction
carrier; its proof is the source's complete `mem_kernel` equivalence. `[M11,M12]`

For every linear `h:T→ℚ²` with `p∘h=0`, each first coordinate is zero; its unique
factor through the kernel is the second coordinate of `h`. This establishes
the full ordinary universal property in the original question. Independently,
every target bilinear form has value zero on `(0,0)`. A formed arrow with
underlying `p` would therefore force `0=B_X((0,1),(0,1))=3`. This excludes **all**
target forms, and is the quantified `projection_not_formed` example, not a
rejection test for only one target form. `[M11]`

### RX-09

The original whole family is `a(n)=C(n+1)X^n`. Its coefficient at degree `d` is
zero unless `d=n`, where it is `n+1`. The source's actual summability theorem
admits this entire function in the chosen `(X)`-adic topology. The old binder's
sum is `PowerSeries.mk (d↦d+1)`, giving coefficients `1,2,4,6` at degrees
`0,1,3,5`. The expected coefficient function is ordinary integer arithmetic;
it is not another call to the same summation operation. `[M14,M15]`

The constant-one family fails already at degree zero: it induces the constant
sequence one in discrete integers, which is not summable. Consequently no
admitted-family record can have that full function. The negative `.cas` file
contains the attempted admission alone; it is run separately and has no false
numeric equality or fabricated proof. The two distinct full negative
propositions remain in `expected-facts.lean`.

### RX-LIFT

The first form is `2(a+b)(c+d)` and the formed arrow is `(a,b)↦(a+b,0)`.
Its genuine kernel is parametrized by the prescribed `(2t,-2t)`. The first
comparison is therefore `(a,-a)↦a/2`; this accounts for the independently fixed
`alpha1(4,-4)=2`, rather than an identity-coordinate convention. Its restricted
first pairing is zero. The additional dot product gives the second component
`8st` after the **actual first defining map** is used at stage two. Both full
factorization cones and all required typed comparisons are in
`selected-lift-requirements.md`. `[M16a,M16b,M16c]`

## Exact remaining source/observer questions

1. **RX-02 core-arrow input:** the whole-map selector is now documented. The
   full two-subsets action still needs a complete specified bijection on the
   existing `Fin 5`, with both directions retained. `rev(5)` is publicly a set
   morphism; calling it a core arrow without its accepted isomorphism structure
   would change the input. A public generic invertible-map construction is
   sufficient; no specialized reversal registration is prescribed.
2. **RX-03 underlying automorphism action:** group operations and the complete
   `Aut(e)` action are concrete. Direct observations of the entire doubling and
   tripling functions, and of `e∘v∘e⁻¹` for an automorphism *element*, require
   the public projection/application of that element's actual isomorphism
   arrows. The ordinary whole-Arrow projection contract does not itself
   specify projection from an `Aut` element. The complete expected equations
   remain in the original question and `expected-facts.lean`.
3. **RX-LIFT comparison and input interpretation:** `[P08]` supplies complete
   pairing selection and the composite selector. The fixed first-projection
   lambda still needs interpretation at its exact declared linear-map type.
   The existing general `pulledBackIso` at the paired-cone source needs public
   exposure for the separately retained whole-map comparison with the first
   returned factor. The complete endpoints and arguments are fixed in
   `selected-lift-requirements.md`; carrier equality is not a replacement.
4. **External controls:** the four RX-05 declaration environments and the
   RX-10 internal-fault/foreign-session fixtures still require independently
   provided observation inputs. This acceptance source does not create them.
5. **Interpretation:** all concrete proposal files require interpretation-only
   checking at their fixed expected types before any frozen run is counted.
   This includes structured lambdas, generalized admission, negative
   proposition observations, the original `Fin 1` admission domain, and the
   exact module/ring/category parameters. A parsing or typing failure is
   recorded at its responsible interface; it does not permit weakening the
   mathematical question.

No source statement in this directory claims that these obligations have been
discharged by a build, runtime output, source commit, or author's description.
