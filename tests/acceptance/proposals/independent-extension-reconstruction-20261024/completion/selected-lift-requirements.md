# Exact selected-lift obligations and remaining comparison

The concrete proposal for both stages and the composed factor is
`rx-lift-prescribed-stages.cas`. It uses `composite_lift(second)` and receiver-based
selection of `X2.pairing()` from the public `SPEC.md` at
`f91870b6009cd0e3cd041488066ea1b898d4689c` (`[P08]`). The sources remain unparsed and
unexecuted. This document retains the exact separate cone-source comparison and
all universal obligations beyond the individual observations.

## The independently fixed maps and their types

Write `R = ℚ`, `W = ModuleCat.of ℚ ℚ`, and
`Wplus = ModuleCat.of ℚ (ℚ × ℚ)`, with their usual componentwise module operations.
The selected value map is the actual `LinearMap.fst ℚ ℚ ℚ : Wplus →ₗ[ℚ] W`.
Its source is the exact value module retained by `DegeneratePlaneWithDot`.
The two entries of a vector in `Vec(ℚ,2)` do not, by themselves, identify this module
or supply an accepted comparison with it.

At `Xplus = DegeneratePlaneLifts.pairedSource`, select

```text
V = changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)
L2 = ChangeValueLifts.changeValueMonoLift ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
```

The second actual inclusion is **the previously computed `i1`**, with type
`X1 → V(Xplus)`. `pairedSource_first` proves that `V(Xplus) = X` by `rfl`; this
identification retains the selected scalar, carrier and first form. The input
monicity is the independently proved `DegeneratePlaneLifts.firstInclusion_mono`.

The selected mathematical second stage is `L2.obj Xplus i1`, with defining arrow
`L2.hom Xplus i1`. These are exactly `finalObject` and `finalInclusion`, by
`final_object_is_successive` and `final_inclusion_is_second`.

If `c2 : V(X2) → X1` and `d2 : X1 → V(X2)` are this stage's actual forward and
backward maps, the complete composed comparisons are

```text
alpha2 = alpha1 ∘ U(c2)
beta2  = U(d2) ∘ beta1
```

where `U = forget ℚ ℚ`. They are the fields of `secondLift.comp firstLift` in the
source, in that order. Thus for every actual final-carrier point `(a,-a)` and every
`s,t : ℚ`, the unchanged requirements are

```text
alpha2(a,-a) = a/2
beta2(t) = (2t,-2t)
beta2 ∘ alpha2 = id
alpha2 ∘ beta2 = id
U(V(i2)) = i0 ∘ alpha2
B_X2(beta2(s),beta2(t)) = (0,8st)
```

The independent fixed samples remain `(0,8)` at `s=t=1` and
`i2(beta2(3/2)) = (3,-3)`. The coefficient eight comes from the selected dot
product, `(2s)(2t)+(-2s)(-2t)=8st`. It is unrelated to RX-08's coefficient three.

## The cone-domain comparison is not a carrier identification

The first whole cone is the registered
`cone : zeroSource → X`, and the first returned factor is
`h1 : zeroSource → X1`. The paired cone is
`pairedCone : pairedConeSource → Xplus`.

For a separate second-stage factor call, the base map must have type
`V(pairedConeSource) → X1`. The first factor has a different complete source.
The existing mathematical comparison that relates them is

```lean
ChangeValueLifts.pulledBackIso
  ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
  DegeneratePlaneLifts.pairedSource
  DegeneratePlaneFactorization.cone
  : V.obj DegeneratePlaneFactorization.pairedConeSource ≅
      DegeneratePlaneFactorization.zeroSource
```

Its forward map must precede the **actual first returned factor**. With that
map denoted `c`, the correct second-stage base arrow is `h1 ∘ c`, and its
compatibility is

```text
V(pairedCone) = i1 ∘ h1 ∘ c.
```

The example at the end of `expected-facts.lean` states this full equality from the
source declarations. A composed universal factor may construct its intermediate
factor directly at `V(pairedConeSource)` using the actual mapped cone; an independent
interpretation must then retain that exact source and its relation to `h1` through
`c`. It cannot describe this as literal reuse of `h1` at a different source merely
because the carriers agree.

In particular, for the actual returned composed factor `h2`, the retained whole-map
comparison is

```text
second.forward() ∘ V(h2) = h1 ∘ c
  : V(pairedConeSource) → X1.
```

The independent second-stage factor of `h1 ∘ c` must equal the composed factor by
the full unique-factor property. Selecting `composite_lift(second)` supplies the
composed factor but does not make the separate observation of `c` disappear.

### Why the objects are not definitionally the same

This is a source-derived analysis, not a metaprogramming or runtime experiment.
`ChangeValueLifts.pulledBack` is `BilinModuleCat.ofBilinMap` of
`X.bilinMap.compl₁₂ underlying(i) underlying(i)`. At the fixed cone, its first
component evaluates to

```text
2*((3s-2t)+(-3s+2t))*((3u-2v)+(-3u+2v)),
```

whereas `zeroSource` is defined from the zero bilinear map. Reduction of the
definitions does not perform the ring cancellations needed to equate these
expressions with free rational variables. Those cancellations occur in `cone`'s
form-preservation proof. The source consequently defines `pulledBackIso` by
`isoMk (LinearEquiv.refl ...)` with `(map_pairing i x y).symm`, rather than by
`Iso.refl`. Thus the supplied complete interface is the actual isomorphism,
including its form-preservation proof; equality of carriers does not replace it.
In contrast, `pairedSource_first` is explicitly proved by `rfl` and applies at
`Xplus`, not at the pulled-back cone source.

Neither field of the second selected lift supplies `c`: its forward field has
source `V(X2)` and target `X1`, and its backward field has the reverse endpoints.
Applying the monomorphism lift directly to the rank-one cone would require a
false monicity statement: the nonzero vector `(2,3)` maps to zero.

## Public source bindings and remaining interface questions

1. **Complete pairing parameters — public binding supplied.** `[P08]` selects
   the whole registered family through `X2.pairing()`, or its application through
   `X2.pairing(a,b)`. The complete receiver type fixes its exact `R` and `Wplus`.
   This fills the module-valued parameter of the existing pairing declaration;
   it does not pass a bare carrier or an unrelated vector presentation in its
   place. Ordinary positional `pairing(X2)` still cannot skip leading arguments.
2. **The fixed linear value map — interpretation question.** The proposal puts
   `(a,b) ↦ a` directly in the registered evidence/functor's dependent linear-map
   slot. It must be read as exactly `LinearMap.fst ℚ ℚ ℚ`, with the canonical
   complete module structures retained by the objects. The preceding `ℚ × ℚ`
   is a carrier-type argument in that declaration, not a substitute for the
   pairing family's module-valued parameter. A failure to form this lambda at
   its exact structured type is a public input limitation to report; it does
   not permit using `Vec(ℚ,2)` or a plain set function instead. No specialized
   first-projection registration is prescribed.
3. **Composite selector — public binding supplied.** `[P08]` explicitly supplies
   `composite_lift(second)`, its four retained fields, and `factor` through that
   selection. It follows the retained link from the actual `first.hom()` used
   as the second input. The ordinary second-stage comparisons remain separate.
   No specialized `compositeLift` registration is needed.
4. **Existing general cone-source comparison — missing public mathematical
   exposure.** When the first factor's original `zeroSource` is reused at stage
   two, the existing general `pulledBackIso` must be publicly selectable with the
   exact complete parameters and endpoints above. No registry schema or
   implementation mechanism is prescribed by this requirement.

Sources: `[M16a]` `DegeneratePlaneLifts.lean`, `[M16b]` `ChangeValueLifts.lean`, and
`[M16c]` `DegeneratePlaneFactorization.lean`, at the supplied mathematical extension
revision. These questions do not authorize this acceptance author to edit those
sources or supply a new mathematical interface.
