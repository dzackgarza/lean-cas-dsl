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

## Kernel assembly and current limits

The kernel retains an independently established formal construction and its
computational packet. Backend answers do not establish a cone, monomorphism,
isomorphism, or universal property in Lean. Mathlib's `Cone.extend`,
`IsLimit.extendIso`, `Functor.preimageIso`, `Arrow.isoMk`, and
`ObjectProperty.isoMk` are existing formal constructions; their formal-side
availability does not impose proof recovery on returned computational data.

`StructuredResult.dataPlan` reads the public shape constructor telescope.
`validatePlannedData` checks complete ordered fields with `Unit` callbacks.
The original constructor slots distinguish returned-apex and input-object roles,
even when their formal values coincide. Computational graph completeness uses
actual endpoint keys. Wrong but well-framed returned objects and defining maps
remain computational claims to be tested by the unchanged mathematical assertions.

The replacement `CasAcceptance.StructuredComparisonProbes` exercises a wrong
`Fin 3` computational apex against an independent `Fin 2` formal presentation,
retains distinct returned leg graphs, and rejects incomplete or out-of-range
computational graphs. Its integrated build and execution remain pending at this
source checkpoint. Earlier proof-reconstruction probes are not evidence for this
replacement boundary.

The production caller migration and actual lift-component consumption must be
checked together. A completed result container alone does not demonstrate that
all consumers preserve this separation or that the mathematical assertions hold.

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

Port dependency provenance uses Lean's existing `forallMetaTelescopeReducing`,
`inferType`, and expression traversal. Corpus queries for constructor binder
dependency provenance found no CAS planner; the telescope query located existing
Lean/Mathlib metavariable elaboration examples. `DataPlan` preserves original
public constructor binder indices before formal unification. Equal formal
objects therefore do not merge distinct computational roles: a returned apex
and an input-diagram object can both formally be `Fin 2` while carrying different
actual data. `validatePlannedData` gives the validator earlier actual fields by
those roles. External diagram bindings stay identified separately and must be
resolved from retained input data, never guessed from canonical formal values.

External input roles are captured from the public diagram declaration's ordered
explicit arguments before formal unification. Each original constructor binder
retains argument/source/target positions; callers resolve those positions from
actual input wires. This adds context provenance rather than selecting an input
by equality with a canonical formal object. Compilation and production wiring
of this addition are pending.
