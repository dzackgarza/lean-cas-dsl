# Reuse record: `cc-lift-general`

Current production boundary: backend answers do not supply reconstructed cones,
subobjects, isomorphisms, or their laws. The older comparison helpers described
below are formal-side tools, not obligations imposed on a computational answer.
For complete cone packets, `validateData` uses Mathlib's existing public
`BinaryFan.mk`, `BinaryCofan.mk`, `PullbackCone.mk`, `PushoutCocone.mk`,
`Fork.ofι`, and `Cofork.ofπ` schemas. Their dependent slots are instantiated only
from the independently retained formal presentation. Computational port
validators return `Unit`, never a backend-derived Lean term or proof. Direct
dependency source search of those constructors and `LimitCone.cone` /
`ColimitCocone.cocone` establishes the owners; this changes protocol validation,
not the mathematics of limits.

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

### Computational packets through the prescribed subobject lift (2026-10-03)

The public upstream owners are `LiftEntry.computation` and
`MonoLiftComputation.obj`, `.hom`, `.forward`, and `.backward` in the
mathematical catalogue. The corpus query `MonoLiftComputation` returned zero
indexed files; direct dependency source search located those actual declarations.
The selected computation's dependent family is checked upstream against the
selected formal lift, whose laws remain on the formal side.

`LiftedSubobjectData` retains the independent source, base, selected route and
formal result together with one opaque source/base packet. Its ordered component
plans instantiate the public signatures solely from those formal inputs. They
are pending computations, not backend answers or proved comparisons. Intermediate
computational data do not yet exist: execution must obtain them from actual
preceding component outputs. Copying the original downstairs packet into every
step would not compute those intermediate objects or maps.

Source/base validators return `Unit` and check representation and declared
endpoints. They do not decode a backend into a monomorphism, lift, isomorphism,
or universal property. Existing three-field packet framing is retained; it does
not assert that the required component computations have run. Integration builds
and ordinary registered execution of the required components remain necessary.

`ComputationalData` supplies the shared `Unit`-returning framing validator.
Corpus search for computational data validation found general runtime examples,
not a CAS contract owner. Direct sources identify the published `ObjectEntry`,
`LiteralEntry`, `GraphLiteralEntry`, and existing functor-action frames as the
owners of the declared schemas. Dependent context comes from the formal request;
validation never reconstructs backend objects or maps into law-bearing terms.
Opaque callables remain computational claims at their declared types rather than
requiring eager enumeration or proof recovery.
