# Independent RX09 constant-one admission assessment

## Finding

The supplied interpretation-only observation satisfies the fixed negative's mathematical
admission requirement. It identifies the actual final binding at its original source
location and retains the entire attempted constant-one map, its original endpoints, the
selected summable-family domain, and the exact summability proposition from the diagnostic.
That proposition is the one excluded by the independently supplied mathematics.

The conclusion is not inferred from the word `invalid` or from a printed error fragment.
The complete typed attempted expression and diagnostic obligation were compared with the
fixed source and the upstream nonsummability theorem. The observation reports no dispatches.
No runtime answer, kernel implementation, leaf implementation, or runner implementation was
read for this assessment.

This is an unnamed negative binding, not a successful value assertion or a new member of
the 134 positive-question inventory. It does not establish the separate positive successor
series computations. Artifact-level provenance for a final frozen rerun remains required.

## Exact inputs and provenance scope

The fixed input is [rx09-constant-one-rejection.cas](rx09-constant-one-rejection.cas).
Its SHA-256 is `22205f7339e59c092e8fcc85219accb6280fc4943701260bed218372ec2add8f`.
The producing kernel revision contains exactly those same source bytes. The attempted
binding is line 9:

```text
let impossibleAdmission := constantOne in Summable(Y, indices)
```

The four preceding bindings select the integer commutative ring, the whole natural-number
index object, the integer power-series object with its selected topology, and the whole
constant-one map. The report records four successful prerequisites and contains their
actual mathematical data in the attempted map and domain. It is not a category-name or
parser rejection before the requested admission.

| Supplied artifact | SHA-256 |
| --- | --- |
| `/tmp/kernel-frozen-rx09-admission-20261024.json` | `e77604163536f90362da98964365726bf86e9d415bce05cd18706b6392785992` |
| `/tmp/kernel-frozen-rx09-admission-provenance-20261024.json` | `b6bed572dff4c6f3d486e9b682d7394a963eff215ae6d25ea72a4385e7c43a14` |

The supplied source provenance identifies:

| Component | Git commit | Git tree |
| --- | --- | --- |
| Kernel producer | `e1a77d3cd5e95ce03b3e4878ae3e969e25b23d93` | `a0232a6079c1ebe64bb0137fcc531241d7cab1d9` |
| Runner checkpoint | `2516005bde0b3decc7dd9c63ac308d5c6e114d5a` | `62a349f1e8802da3fbd6d684e45479c53a98dc4a` |
| Mathematics | `b08e6b3cac7b2464d21419e05b27c89c2c6858d5` | `0ed39a7c95a6c33fcfb0f545d76dac4b78970d25` |
| Contract checkout | `469f5d90bbef964a2b19d407f81d9ca52a5f033d` | `4633972a6cdf788bb22ed7ca77a0ba478c1b2396` |

Full commits and trees were resolved as Git metadata; no implementation source was read.
Unlike the RX05 receipt, this RX09 provenance file contains source labels only. It does not
retain the actual resolved semantic module paths and artifact hashes, complete import list,
or toolchain and package-selection receipt. The mathematical assessment below applies to
the identified raw record; these labels alone do not authenticate a final producing build.

## Complete typed reading

The `actualAttempt` table has 159 terms and six separately typed roots. The
`independentObligation` table has 46 terms and three separately typed roots. Every local
term reference and every value/type root was checked for validity and closed binding scope.
The complete structures were inspected; their readable displays were only an aid.

| Actual root | Mathematical content |
| --- | --- |
| `originalMap` | The complete map from the original natural-number object, composed with the terminal map and the numeral-one map of the selected integer power-series ring |
| `originalDomain` | The whole natural-number object |
| `originalCodomain` | `powerSeries NamedCommutativeRings.integers` |
| `familyFunction` | A lambda on that entire domain with the constant value given by the actual integer-to-power-series ring homomorphism applied to one |
| `admissionDomain` | `summableFamilies (powerSeriesTAdic NamedCommutativeRings.integers) naturals` |
| `actualDiagnosticObligation` | `Summable` of that whole function, with the selected additive structure, selected topology, and `SummationFilter.unconditional naturals` |

The independent roots separately retain the whole family `fun _ : ℕ => (1 : PowerSeries ℤ)`,
the corresponding `SummableFamily` domain, and its exact `Summable` proposition. The actual
obligation uses the formal ring-numeral map rather than writing the value as a primitive
one. Its meaning agrees by preservation of one by that ring homomorphism. This comparison
uses the retained original scalar map and coefficient ring; it is not equality of a
computed answer with an expected answer.

Upstream `Catalogue/Semantics/Algebra/Series.lean` defines `summableFamilies` as the actual
`SummableFamily`, with fields `toFun` and `summable : Summable toFun`. Its `powerSeriesTAdic`
object has the topology `tAdic`, the product topology with discrete coefficient topology.
Those exact data occur in the actual diagnostic proposition. Neither a finite prefix, a
different index set, a coarser topology, nor a different family's evidence replaces them.

## Independent mathematical reason for rejection

The already supplied `Algebra/SuccessorSeries.lean` proves
`integer_constant_one_not_summable` for the whole constant-one family over the integer
power-series ring in this topology. Its proof takes the zeroth coefficient of a purported
sum. This would make the constant-one family summable in the discrete additive group of
integers, forcing one to be zero. The contradiction is independent of the attempted
admission and of every implementation.

The companion theorem `no_constant_one_admission` excludes any object in the selected
`SummableFamily` domain whose full `toFun` is this family. These are exactly the separating
requirements in the [fixed RX09 question](../questions.md). The diagnostic's failure to
establish summability would not alone prove nonsummability; the independent theorem applies
to the complete retained family and supplies that mathematical conclusion.

The observed stage is `admission`, the kind is `invalid`, and the `dispatches` array is empty.
There is no successful admitted value or numeric sum in the record. The failure therefore
has the required location and mathematical obligation, with no missing-implementation
observation substituted for it. This assessment changes no source question, expected
mathematics, or protected baseline.
