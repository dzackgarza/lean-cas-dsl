# Five newly readable inverse questions: independent source assessment

## Inputs and scope

The sole new interpretation input is
`/tmp/b0-poc-5410e70/inverses-opaque-interpretations.json`, SHA-256
`c65b4ad16af122b12f3521dd95c49cfbbd733be0989706666ca331eb006544aa`.
It has exactly five rows and only `file`, `id`, `question`, `proposition`.
Every question label is `805208138f016368f6a4eac415f25f3922a5807d`.
These are supplied claims, not trusted runtime or computation evidence.
No sibling diagnostics, implementations, outcomes or leaves were inspected.

The expectations precede this input: [fixed question specifications](question-specifications.md),
originally committed in `a6311e1ab86b8aa31741a91c5040a236677edb72`, and unchanged
[inverses.cas](inverses.cas). The latter was compared byte for byte with original
assertion revision `76d37bbfab783eecd3383f965aad1e34d9027fc2` and is identical.
Published mathematical source inspected is `lean-categories/main`
`805208138f016368f6a4eac415f25f3922a5807d`; its Mathlib checkout is
`db584cd6d46c92f209a44c0f1c829460d327499d`.

## Mathematical structures, domains and identifications

Write `K = NamedCommutativeRings.rationals` and
`R = LinearAlgebra.matrixRing 2 K`. Published
`Catalogue/Semantics/Algebra/LinearAlgebra.lean`, declarations `matrixRing`,
`matrixRingIdentification` and `matrixRing_mul_apply`, give precisely
`Matrix (Fin 2) (Fin 2) ℚ`, with matrix multiplication
`(AB)ᵢⱼ = ∑ₖ AᵢₖBₖⱼ`. This is not the pointwise product ring.
The selected multiplicative monoid is
`P = Ports.ringsMultiplicative.obj R`; the question retains this functor.
The underlying-set route is `monoidsSemigroup`, then associative-structure
forgetting, then binary-operation forgetting. These forget structure, without
changing matrix entries or multiplication. No endpoint substitution is required.

All five graphs construct the same point `m : fin 1 → Units(P)` by
`Units.admit P M h`, with `M = [[1,2],[3,4]]`. Entries are canonical integer
casts into the selected rational ring. Admission data are
`h = Matrix.invertibleOfDetInvertible M`, supplied with
`invertibleOfNonzero (det M ≠ 0)`. Mathlib
`LinearAlgebra/Matrix/NonsingularInverse.lean: Matrix.invertibleOfDetInvertible`
defines its inverse as `(det M)⁻¹ • adjugate M` and proves both inverse laws.
`Matrix.det_fin_two` gives `det M = 1·4 - 2·3 = -2`, so the retained side
condition is true. `Algebra/Units.lean: admit`, `admit_inclusion`,
`groupUnits`, `groupInverse`, `unitsIdentification` and
`groupUnitsIdentification` identify the selected unit group and its carrier;
`groupInverse` is group inversion, and `inclusion` is `Units.val`.
Thus `j = m ≫ groupInverse(groupUnits P) ≫ inclusion P` is exactly the point
of the underlying matrix inverse. The ordinary matrix point is
`a = m ≫ inclusion P`. Admission is not replaced by unrestricted matrix inversion.
`Invertible` is subsingleton; different valid inverse witnesses cannot change
this selected unit or its inverse.

Vector construction is the published `empty` and repeated `cons` with
`Matrix.vecCons`, so it retains the ordered vectors `v=(1,2)` and `b=(5,11)`
in `Fin 2 → ℚ`. `rows 2 K` is `Matrix.of` on the ordered rows;
`apply 2 K` is `Matrix.mulVec`, not right-vector multiplication;
`det 2 K` is `Matrix.det`. Every pairing is the selected set-product
limit lift of `BinaryFan.mk`, retaining both its ordered components.
Canonical numerals use the integer/natural initial ring maps, not an
arbitrary embedding. `NamedRings.rationals` and the carrier of `K` are the
same rational carrier with its declared structure.

Division uses `Units.divide` with domain `ℚ × Units(ℚ)` and value
`(x,u) ↦ x·Units.val(u⁻¹)`, not an unrestricted denominator operation.
The right-hand matrix rows are `(-2,1)` and `(3/2,-1/2)` in that order.
Their denominators are admissions of the rational number `2` with
`invertibleOfNonzero`; the extra `ℕ → ℤ → ℚ` cast wrappers in the latter
fraction preserve exactly `2`. The determinant's right side is `(-1)/2`
with the same admitted denominator, not the integer quotient of `-1` by `2`.

## Complete per-identity assessment

The actual root propositions are equalities of set morphisms from `fin 1`,
not scalar `Eq` roots. Evaluation at the sole element of `Fin 1` and function
extensionality give a canonical equivalence with each fixed value equality;
this keeps the entire point map, rather than discarding its application route.
Each second root is `Sort 0`, so the first root is a proposition.

| Identity | Entire point-map proposition and fixed mathematical comparison | Disposition |
| --- | --- | --- |
| `inverses.value` | `Eq_Hom(fin 1, underlying P)(j, rows∘((-2,1),(3/2,-1/2)))`. The ordered rows give `J=[[-2,1],[3/2,-1/2]]`; explicit multiplication gives `MJ=JM=I₂`, identifying `j` with `J`. | Source-grounded match |
| `inverses.solve` | `Eq_Hom(fin 1, ℚ²)(⟨j,b⟩≫apply, v)`. Exactly `M⁻¹b=v`; coordinates are `(-10+11,15/2-11/2)=(1,2)`. | Source-grounded match |
| `inverses.left` | `Eq_Hom(fin 1, ℚ²)(⟨j,⟨a,v⟩≫apply⟩≫apply, v)`. The inner application is `Mv`; the outer application is `M⁻¹(Mv)`. It retains this order, rather than substituting `b` or cancelling the two maps in the question. | Source-grounded match |
| `inverses.right` | `Eq_Hom(fin 1, ℚ²)(⟨a,⟨j,b⟩≫apply⟩≫apply, b)`. The inner application is `M⁻¹b`; the outer application is `M(M⁻¹b)`. This retains the opposite inverse law and original right side `(5,11)`. | Source-grounded match |
| `inverses.det` | `Eq_Hom(fin 1, ℚ)(j≫det, ⟨-1,admit(2)⟩≫divide)`. Exactly `det(M⁻¹)=-1/2`; direct determinant of `J` is `1-3/2=-1/2`. | Source-grounded match |

## Proof proposition types retained in the supplied graphs

In the first (`homs`) graph, proof nodes encode their proposition types, not proof bodies. Every such node
was inspected; none is treated as computation evidence. Node numbers below
are local to the respective complete question's `terms` array. Normalized
notation in this table retains the full operand matrix or scalar as defined
above, its rational domain and the original nonzero predicate.

| Identity | Proof node → type node | Exact mathematical proposition after the declared canonical casts |
| --- | --- | --- |
| `inverses.value` | `538 → 537`; `799 → 798`; `885 → 884` | `Ne (Matrix.det M) (0:ℚ)`; `Ne ((Int.castRingHom ℚ) (2:ℤ)) (0:ℚ)`; `Ne (ℚ-cast (ℤ-cast ((Nat.castRingHom ℕ) 2))) (0:ℚ)` |
| `inverses.solve` | `594 → 593` | `Ne (Matrix.det M) (0:ℚ)` |
| `inverses.left` | `594 → 593` | `Ne (Matrix.det M) (0:ℚ)` |
| `inverses.right` | `593 → 592` | `Ne (Matrix.det M) (0:ℚ)` |
| `inverses.det` | `541 → 540`; `743 → 742` | `Ne (Matrix.det M) (0:ℚ)`; `Ne (ℚ-cast (ℤ-cast ((Nat.castRingHom ℕ) 2))) (0:ℚ)` |

All side conditions follow independently from `-2≠0` or `2≠0` in `ℚ`.
The `Invertible M` data itself is retained as a term built by the declared
Mathlib constructors, not collapsed to a proposition or omitted proof node.
Their defining inverse formula is precisely the independently fixed adjugate
formula. No comparison here requires a claim from an implementation.

## Operation and route appendix of each complete question

The assessment also reads the entire second `operations` graph; parsing both
JSON graphs consumes each complete question without a remaining suffix. It is
not an assessment of the pretty-printed proposition alone. The distinct named
mathematical entries are the rational field/ring/set objects, natural semiring
and set, `fin`, vectors, matrices and the matrix ring, units, natural-to-integer
and integer-to-rational inclusions, tuple cons, matrix rows, matrix determinant,
matrix application, division, ring negation and group inverse. Each has the
same selected mathematical arguments as described above. All retained routes
are the stated multiplicative forgetful route or its suffixes, preceded where
needed by forgetting commutativity or the field classifier; no additive-monoid
route is substituted for the matrix multiplicative monoid.

In particular `op.groups.inverse` has parameter `groupUnits P`, the admitted
matrix point as its argument and `units P` as both source and target carrier.
Matrix application is `obj.sets.matrices#application` with parameters `2,K`;
the corresponding typed term is `LinearAlgebra.apply 2 K`. Matrix determinant
and rows have the same parameters. Product mediators, identities and morphism
compositions retain the ordered terms described in the per-ID table, including
both nested application orders. Repeated admission/product records do not
change their operands. This is a source-level reading of their mathematical
terms and stated routes, not a proof of the interpreter's record-consumption
algorithm or its serialization schema.

The additional operation-graph proof nodes are:

| Identity | Proof node → type node and mathematical proposition |
| --- | --- |
| `inverses.value` | `512→511`: cast-chain `2≠0` in ℚ; `782→781`: integer-cast `2≠0` in ℚ; `854→853`: equality of the selected rational multiplicative monoid with itself; `864→863`: equality of the selected rational carrier with itself; `1073→1072`: `det M≠0` in ℚ. |
| `inverses.solve` | `938→937`: `det M≠0` in ℚ. |
| `inverses.left` | `912→911`: `det M≠0` in ℚ. |
| `inverses.right` | `922→921`: `det M≠0` in ℚ. |
| `inverses.det` | `500→499`: cast-chain `2≠0` in ℚ; `999→998`: `det M≠0` in ℚ; `1025→1024`: equality of the selected rational carrier with itself. |

The rational `parameterEquivalence` records in `value` and `det` cite
`NamedCommutativeRings.rationalsCarrierIdentification`,
`Fields.rationalsIdentification` and `NamedRings.ringRationalsIdentification`.
Their actual published definitions are `Iso.refl _`; they identify this exact
rational carrier, without replacing it by an unspecified isomorphic set.
The monoid equality retains the composite commutative-ring-to-ring-to-monoid
functor on the chosen rational object. These reflexive parameter equalities
and nonzero side conditions are independent mathematical truths. They are not
leaf certificates. The uninspected proof bodies cannot establish a checked
migration; the assessment is of their retained proposition types.

## Extent of the finding

Five supplied interpretations have source-grounded mathematical matches;
zero concrete mathematical discrepancies or undetermined source-level
comparisons were found in these five complete graphs. The two point/value
presentations are related by the explicit singleton-domain comparison above;
this is mathematical source assessment, not a newly Lean-checked migration.
It does not independently check the serialized graph's typing in Lean or
authenticate the compiled environment behind its revision label.

The earlier empty rows and failed matrix binding in the separate full payload
remain historical missing-question observations. This separately supplied
five-row input provides readable questions for comparison; it does not
rewrite the earlier payload, establish a successful binding execution, or
combine the two runs into a coherent accepted full-suite record. No assertion,
authoritative record, expected answer or execution requirement was changed.
No computation was assessed, proposed assertion admitted, protected acceptance
issued, or B0 completion inferred.
