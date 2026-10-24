# Public surface status at this proposal checkpoint

This records only public specifications and upstream mathematical interfaces. It is not an
implementation inspection, an execution finding, or an instruction to change upstream mathematics.
All mathematical questions in `questions.md` remain fixed.

## Public forms supplied during reconstruction

The additional public `SPEC.md` [P05] supplies the following generic forms:

```text
<construction>(parameters..., X)
map f along <construction>(parameters...)
view X along <functor-id>(parameters...)
component(<cell-id>(parameters...), X, [constructor-path...])
inverse_component(<cell-id>(parameters...), X, [constructor-path...])
let L := lift(X) along <lift-id>(parameters...) with m using proof(p)
L.obj()
L.hom()
L.forward()
L.backward()
factor(g) through L with f using proof(q)
```

These are specification schemata, not complete trial expressions. The document also specifies
that `f(u)` for `f : A -> B` and `u : D -> A` keeps the whole domain `D`, and that a core
construction requires an actual isomorphism with both directions. `Aut(C)` can infer the
category from a selected `C in Groups`; that concrete cardinality excerpt is now included.

The root `SPEC.md` [P01] additionally supplies the formal `proof(...)` argument and the
single-data-field proof-bearing value form `t in X using (proof(...),...)`. Proofs are checked
against their complete obligations, and generalized-point proofs cover the whole domain.

## Exact remaining requirements

| Dependency | Trials | Required public term or observation |
| --- | --- | --- |
| S01: actual presentation as a complete map | RX-03, RX-07 | Bind the registered `cyclic_quotient_residue(5)` or `F9translation` as the actual typed arrow/isomorphism, including its inverse when used in a core action; then use that term in construction map action, composition and generalized application. The existing `map t along P` element form alone does not state the spelling of that arrow term. |
| S02: selected structure and forgetful route | RX-04, RX-05, RX-07 | Select the appropriate structured object when a registered display name has several meanings; retain classifier-forgetful steps, including `clf.commutative_rings.field`, before the selected ring receiver of `cmp.rings.carrier`. A named functor view is documented; an explicit classifier-forgetful route or an equivalent public typed selection still needs a spelling. |
| S03: a family reindexing with its whole map action | RX-06, RX-10 | Select the existing module fibration at `R=Z`, `S=ZMod 5`, the actual integer coefficient map, and the regular `S`-module; form its cartesian arrow and apply the same reindexing to the complete nonidentity regular-module arrow. The registered new object can name the resulting module, but cannot replace the required cartesian/map observations. |
| S04: selected ordinary kernel and its actual points | RX-08 | Bind the actual `1 x 2` row as a module arrow, its complete kernel/inclusion, the five-parameter ordinary-kernel restriction and its actual defining map; form points in that actual kernel and use the existing registered `pairing(R,W,X_K)`. Generic lift projections are documented, but do not by themselves define ordinary-kernel fields. The mathematical pairing selector itself exists; see [M11]. |
| S05: whole successor family, proof admission and old binder | RX-09 | Pass `successor_power_series_terms(Z)` as the whole function into `Summable(powerSeriesTAdic Z,N)` using its proved summability, then apply the old power-series binder to that actual admitted value. The full index object/topology/function and proof proposition must survive. Sum notation and the general proof-bearing value form are documented separately; their complete binding at this dependent interface remains to be spelled. |
| S06: full selected data for the two lifts and composed factor | RX-LIFT | Supply the actual module map `i0(t)=(2t,-2t)` with its complete endpoints, the selected coefficient/value modules, the first lift, and the second lift at the actual `firstInclusion`; retain the nonidentity first comparison in an explicit composed lift/factor invocation. The existing upstream `kernelInclusion` is a mathematical declaration, not a registered public morphism name. A data term is not a proof term. |
| S07: external observation controls | RX-05, RX-10 | [P06] now supplies the fixed-suite/inventory harness, separate realization manifests, exact outcome names and session boundary. Remaining requirements are the separate mathematical declaration environments for RX-05 and the independently provided internal-fault/foreign-session engineering fixtures. A realization manifest cannot omit a mathematical comparison cell. |

These dependencies do not demand one particular new notation. They identify exactly what a
publicly documented form must denote. If an existing documented form supplies one, the acceptance
author can use that form without implementation inspection. No new mathematical object, map,
operation, cell, or proof is proposed to fill a language gap.

## Further type-specific inputs

RX-03 must form the actual unit of coefficient two and its selected doubling automorphism,
not a set function labelled an automorphism. The source declarations `unitTwo` and `byUnit`
fix their meanings, and `cyclic_quotient_aut_by_unit(5)` is the registered full group morphism.
A public expression must supply a point in its actual unit-group domain using the existing
unit construction/admission, or another already public typed data form. This is an input-term
obligation, not a reason to introduce a new inversion operation.

RX-08 and RX-LIFT use unbounded rational morphisms. The generic lambda and composition forms
must denote the complete arrows at the required module/formed endpoints if used for those
bindings. Displayed vectors or observations at two points do not constitute such arrows.

The registered two-subsets functor already has its complete bijection action [M02]. [P05]
explicitly documents `map f along <construction>` and `view X along <functor-id>`; its text does
not explicitly settle the corresponding whole-map spelling for a registered functor which is
not a direct-construction row. The mathematical action in RX-02 remains specified pending its
public expression.

## Validation boundary

The `.cas.proposal` excerpts are source-authored and unexecuted. Reading a syntax description
does not certify parsing, elaboration, actual execution or interpretation preservation.
The remaining requirements are recorded as blocked surface/observer bindings, not marked
passed, omitted, or satisfied by an implementation's self-description.
