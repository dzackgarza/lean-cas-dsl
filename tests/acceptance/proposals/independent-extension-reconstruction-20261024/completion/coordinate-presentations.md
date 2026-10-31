# Exact coordinate presentations in RX-08 and RX-LIFT

This source-only review uses the mathematical definitions at
`766fc2c20c0f293f7e5f3151584534f40f7af806`. It changes no question, expected value,
cone, form, scalar action, or coordinate order. It uses no interpreter result.

## Carrier vectors and paired values

The existing public set object `Vec(Q,2)` selects
`CasCatalogue.Algebra.LinearAlgebra.vectors Q 2`, defined by

```lean
abbrev vectors (X : Type) (n : ℕ) := Fin n → X
```

Its registered `vectorArity` and `vectorComponent` retain the ordered indices
`0,1`. At the selected rational coefficient ring, its carrier is `Fin 2 → ℚ`.
It is not the product type `ℚ × ℚ`.

The corresponding complete module is
`LinearAlgebra.vectorModule (RingCat.of ℚ) 2 = ModuleCat.of ℚ (Fin 2 → ℚ)`
by definition, with the ordinary pointwise additive group and scalar action.
The existing `vectorModuleIdentification` is `Iso.refl` between its forgotten
set and `vectors ℚ 2`.

The paired forms instead have **value module** `ModuleCat.of ℚ (ℚ × ℚ)`, with
ordered componentwise operations. No use of `Vec(Q,2)` supplies this module.
`X2.pairing()` retains it from the complete formed receiver. The proposal's
`valuePairs := (ℚ in Sets) × (ℚ in Sets)` names its exact underlying set only
when comparing the ordered pair of returned values.

## Reduction of the exact formed carriers

The mathematical constructors explicitly give

```lean
BilinModuleCat.ofBilinMap (B : LinearMap.BilinMap R M W)
  := op ⟨op (ModuleCat.of R M), ...⟩
BilinModuleCat.carrierObj L := (unop L).1.unop
```

Thus extracting the carrier of `ofBilinMap B` reduces to the same
`ModuleCat.of R M`, with the same supplied module instances. This concerns
the complete underlying module, not only a bijection of its carrier.

| Selected formed object | Definition fixing its carrier | Carrier module |
| --- | --- | --- |
| `DegeneratePlaneLifts.source` | `ofBilinMap` of the matrix form `[[2,2],[2,2]]` | `ModuleCat.of ℚ (Fin 2 → ℚ)` |
| `DegeneratePlaneLifts.target` | `ofBilinMap` of the matrix form `[[2,0],[0,5]]` | `ModuleCat.of ℚ (Fin 2 → ℚ)` |
| `RationalProjection.diagonalSource` | `ofBilinMap` of the matrix form `[[2,0],[0,3]]` | `ModuleCat.of ℚ (Fin 2 → ℚ)` |
| `DegeneratePlaneFactorization.zeroSource` | `ofBilinMap (0 : LinearMap.BilinMap ℚ (Fin 2 → ℚ) ℚ)` | `ModuleCat.of ℚ (Fin 2 → ℚ)` |
| `DegeneratePlaneLifts.pairedSource` | Its definition explicitly stores `ModuleCat.of ℚ (Fin 2 → ℚ)` | `ModuleCat.of ℚ (Fin 2 → ℚ)` |
| `DegeneratePlaneFactorization.pairedConeSource` | `pulledBack` applies `ofBilinMap` on `zeroSource.carrier`, retaining that module | `ModuleCat.of ℚ (Fin 2 → ℚ)` |

The first and final lifted carriers are the actual range subtype of
`t ↦ ![2*t,-2*t]`. They are not identified with all of `Vec(Q,2)`: the first
raw point is admitted with its range proof, and the returned backward
comparisons supply subsequent subtype points.

These reductions do not identify complete formed objects whose forms differ.
In particular, they do not remove the `pulledBackIso` requirement between
`V(pairedConeSource)` and `zeroSource`. Its complete endpoints and whole-map
obligation remain in `selected-lift-requirements.md`.

## Review of each coordinate use

**Whole pairing domains.** RX-LIFT's `pairOfVectors` has type
`(Fin 2 → ℚ) × (Fin 2 → ℚ)`, exactly the source of `X.pairing()`. The outer
pair `(v,w)` contains two finite-index vectors. The image pairing uses the
actual `f` and the actual target pairing. Neither input is a point of the
paired form's value module. RX-08's `pairDomain` and RX-LIFT's `scalarPairs`
instead contain two scalar parameters. Their maps first apply `kappa` or
the returned `beta`, then pair points in the actual restricted carrier.

**Raw constrained points.** In RX-LIFT, `(4,-4) in vectorSet` must denote
`![4,-4] : Fin 2 → ℚ`. The source proof `(firstPoint 4).property` concerns
that very vector in the range of the prescribed kernel inclusion. In RX-08,
the complete `coordinateData` map must denote `t ↦ ![0,t]`, with domain `ℚ`
and codomain `Fin 2 → ℚ`. Admission into `restrictionCarrier` adds the
kernel-membership proof for each original `t`. Both `mem_kernel` and
`kernelCoordinates` use exactly this finite-vector type and coordinate order.
No product-to-vector transport is being silently applied.

**Factor and inclusion samples.** The samples `(2,1)` and `(1,3)` are read at
the first factor's exact `zeroSource` carrier or the final factor's exact
`pairedConeSource` carrier. Both carrier types are `Fin 2 → ℚ`, so the
required literals are `![2,1]` and `![1,3]`. The factors retain their distinct
complete formed domains. Results `(4,-4)`, `(-3,3)`, and `(3,-3)` are compared
in `vectorSet`, the exact forgotten carrier of the relevant ambient target.
These set observations do not retype a formed factor at another formed source.

**Rectangular row maps.** `RectangularMatrices(1,2,Q)` is declared as
`Matrix (Fin 1) (Fin 2) Q`. The rows `[1,0]` and `[3/2,-1]` must retain one
row and two ordered columns. The actual declaration is

```lean
rowLinearMap (columns : ℕ) (R : CommRingCat)
    (M : Matrix (Fin 1) (Fin columns) R) :
  LinearAlgebra.vectorModule (RingCat.of R) columns ⟶
    CatalogueRegistration.regularModule (RingCat.of R)
```

At the fixed inputs, its complete source is
`ModuleCat.of ℚ (Fin 2 → ℚ)` and its complete target is `ModuleCat.of ℚ ℚ`.
The target is exactly `RegularModule(Qring)`, with its canonical self action.
The independent source defines `RationalProjection.projection` by the very
call `rowLinearMap 2 (CommRingCat.of ℚ) !![1,0]` at domain
`diagonalSource.carrierObj`. It defines `baseMediator` by
`rowLinearMap 2 (CommRingCat.of ℚ) !![3/2,-1]` at domain
`zeroSource.carrierObj`. These definitions fix the full endpoints directly.
Neither use needs a comparison with `ModuleCat.of ℚ (ℚ × ℚ)`.

## Public interpretation and mathematical sources

The existing carrier bindings remain unchanged. No additional comparison is
mathematically required for these particular `Vec` uses: the displayed
definitions give the same exact types. Reading tuple literals and tuple-pattern
lambdas at those finite-vector types remains an interpretation obligation.
This source review supplies no parse, build, or execution result.

The declarations are in these mathematical sources at the fixed revision:

- `LeanCategories/Catalogue/Semantics/Algebra/LinearAlgebra.lean`:
  `vectors`, `vectorModule`, `vectorModuleIdentification`, and vector components.
- `LeanCategories/Catalogue/Semantics/Algebra/RectangularLinearAlgebra.lean`:
  `rectangularMatrices` and `rowLinearMap`.
- `LeanCategories/Modules/Bilinear/Valued/Fixed.lean`:
  `BilinModuleCat.ofBilinMap`, `carrierObj`, and `forget`.
- `LeanCategories/Catalogue/Semantics/Modules/CatalogueRegistration.lean`:
  `regularModule`.
- `[M11]` `ModuleKernelRestriction.lean`: `diagonalSource`, `projection`,
  `mem_kernel`, and `kernelCoordinates`.
- `[M16a]` `DegeneratePlaneLifts.lean`: `source`, `target`, `pairedSource`,
  `firstPoint`, and the selected lift carriers.
- `[M16b]` `ChangeValueLifts.lean`: `pulledBack` and `pulledBackIso`.
- `[M16c]` `DegeneratePlaneFactorization.lean`: `zeroSource`, `baseMediator`,
  `pairedConeSource`, and both factorization domains.
