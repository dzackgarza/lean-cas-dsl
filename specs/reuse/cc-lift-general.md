# Reuse record: `cc-lift-general`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `CreatesLimit liftLimit liftedLimitMapsToOriginal` | mathlib4 `Limits/Creates.lean`, `Limits/Final.lean` |
| `createsLimitsOfShape forget GrpCat` | mathlib4 `Algebra/Category/Grp/Limits.lean` (`forget_createsLimit`, `Forget₂.createsLimit`) |
| `forget creates limits Grp` | lean-liquid only (Lean 3) |
| `IsCartesian fibration lift` | UniMath, PolyFun; Mathlib checked directly |
| `PreservesLimit isLimitOfPreserves` | downstream users of Mathlib `PreservesLimit` |

Direct checks in Mathlib: `CategoryTheory/Limits/Creates.lean` (`CreatesLimit`, `liftLimit`,
`liftedLimitIsLimit`, `liftedLimitMapsToOriginal`), `CategoryTheory/FiberedCategory/Cartesian.lean`
(`Functor.IsCartesian`), `Limits/Preserves/Basic.lean` (`PreservesLimit`, `ReflectsLimit`),
`Adjunction/Limits.lean` (right adjoints preserve limits).

## Owner
- Returning a limit computed downstairs to the source category is Mathlib's `CreatesLimit`:
  `liftLimit` (the lifted cone), `liftedLimitIsLimit`, and `liftedLimitMapsToOriginal` (its image
  is the downstairs limit). Forgetful functors of algebraic categories carry these instances.
- Cartesian lifts are Mathlib's `Functor.IsCartesian`/`IsFibered`; preservation and reflection are
  `PreservesLimit`/`ReflectsLimit`.

## New code, and why no dependency supplies it
A registry row naming the creation datum between registered functors and categories, its
validation, and the lift on presented values (the preimage of Mathlib's lifted cone), as for
`realizedLimitCone`.

### Construction checkpoint (2026-10-02)

Direct source queries: `standardCone` and `decodeFamily` in `CasCatalogue/Semantic.lean`
and `CasCatalogue/Realize.lean`; `CreatesLimit.lifts`, `liftLimit`, and
`LiftableCone.validLift` in Mathlib `CategoryTheory/Limits/Creates.lean`.

`CasCatalogue/StructuredResult.lean` packages the complete decoded cone/cocone, its diagram,
apex and original constructor response. `Realize.Wire` retains the complete response and diagram
alongside the cone, rather than retaining only the apex wire presentation. Decoding still uses
Mathlib's shape constructors and the existing dependent-field decoder; no new mathematical
constructor or semantic row is introduced. The creation helper consumes the registered creation
evidence and an independently supplied upstream presentation only when its cone is definitionally
the decoded cone. This limited helper is not completion of generic computational lifting.

The remaining creation-lift input is an independent reconstruction of `IsLimit` for an arbitrary
well-typed decoded cone. `CreatesLimit.lifts` requires that input; commutation of the legs alone
is insufficient. The existing cone response contains apex and legs, not that input, and no leaf
proof can supply trusted mathematical evidence. The positive execution obligation remains open.

Focused validation: `lake build CasCatalogue.StructuredResult` succeeds. The combined
`StructuredResult`/`Realize` build reaches the integration but fails in independently edited
question-record sections of `Realize`, outside this construction's owned sections. No execution
acceptance is established by these compilation checks.

### Created-cone apex comparison (2026-10-03)

Corpus queries `IsLimit.extendIso` and `Cone.extend` locate Mathlib's existing
`CategoryTheory/Limits/IsLimit.lean` and `CategoryTheory/Limits/Cones.lean` constructions.
`Cone.extend` retains the actual legs by composing the checked apex comparison;
`IsLimit.extendIso` supplies its universal evidence. `StructuredResult.extendCreated` only
assembles these declarations from the exact retained closed creation presentation and an
independently checked isomorphism with the full expected endpoints. It introduces no cone,
comparison or universal property of its own. Compilation and execution of this addition are
still required.

The additional corpus query `Functor.preimageIso` locates Mathlib's existing fully faithful
isomorphism reflection in `CategoryTheory/Functor/FullyFaithful.lean`.
`reconstructCreatedAt` checks the entire source-image comparison and retained creation-image
comparison, then applies that declaration only with the exact functor's existing `Full` and
`Faithful` instances. The source cone extension uses the same `extendCreated` assembly; its
returned image comparison is updated to the current source apex. No carrier or cardinality
comparison supplies either isomorphism.

### Complete subobject comparison (2026-10-03)

Direct dependency queries locate `CategoryTheory.Arrow.isoMk` in
`CategoryTheory/Comma/Arrow.lean` and `CategoryTheory.ObjectProperty.isoMk` in
`CategoryTheory/ObjectProperty/FullSubcategory.lean`. `subobjectComparison` assembles
those existing constructors from the checked apex isomorphism, fixed ambient identity
and actual inclusion square. It retains an isomorphism of the complete subobjects,
with independently fixed expected and returned endpoints. The cone extension additionally
supplies its actual retained cone and the original isomorphism's `IsIso` evidence explicitly;
neither is inferred from an incidental carrier.

Focused helper execution passed the nonidentity created-apex and full-subobject comparison
cases, with wrong endpoint, missing presentation, different diagram/ambient and unrelated
square rejected. `CasAcceptance.StructuredComparisonProbes` retains these engineering
regressions. Current complete gate/native and downstream composition checks remain required.

### Comparisons through the prescribed subobject lift (2026-10-03)

Direct source queries of the accepted `CasCatalogue.MonoLift` locate `hom`, `hom_mono`,
`iso`, `fac`, and `universal` in the mathematical dependency. The last declaration supplies
the cartesian universal factorization over an arbitrary prescribed base map, including
uniqueness. `StructuredResult.liftSubobjectComparison` assembles its two directions from
that existing evidence, actual ambient and base comparisons, and the exact defining maps.
Both base ambient components must be the image of the supplied full ambient comparison.
Inverse equations use the actual accepted monomorphism evidence. The final complete
subobject-category comparison is independently kernel checked; no carrier matching supplies
selected structure or a proof.

The isolated helper and exact durable probe body passed nonidentity apex/ambient changes,
both inverse equations, and different chosen pairings on the same carrier; wrong endpoints,
defining maps, ambient actions and chosen forms are rejected. Runtime replay and propagation
remain integration obligations. Replay must bind the ordered lift identifiers to the
independently fixed operation's prescribed route, beyond checking that the rows are registered.
