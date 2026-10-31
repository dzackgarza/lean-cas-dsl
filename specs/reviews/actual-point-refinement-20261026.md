# Scoped actual-point refinement barrier: bounded source review

## Reviewed candidate and finding

Reviewed the pending one-file change in
`/tmp/kernel-record-consumer-20261026/CasCatalogue/ComputationalData.lean` against
immutable commit `eeb8fb208dc825bd985536396dd3b1037066e7eb`, tree
`fcc6677837a891b74773e4fed402c4ec8a5ab04a`.

- Base file SHA-256:
  `b0740dbc0f70cdaaa2c846090c569c5de1f82b231a49ddd1b88d213a342ee3b6`.
- Reviewed pending file SHA-256:
  `ca6039257522a18b9c6477cc4bff2b9d9948ea112ba656d28bfbd8a951ba01e1`.
- Exact reviewed patch SHA-256:
  `9dfaf522c1fde553e0d931cf102a4422b760509e02112b2279e096cfb12c586b`.

**No concrete source blocker found in this bounded delta.** The implementation
addresses the reported endpoint-membership reconstruction at the intended caller
boundary and retains ordinary literal validation. The both-mode closedness guard
correctly handles the existing direct `pointSchema` control.

This finding is source-only. I did not compile, run a probe, inspect leaf code or
fixed mathematical answers, edit source, or modify compiled artifacts. Root owns
the focused execution and integrated build. No passing execution or acceptance
claim is inferred here.

## Actual-point mode is selected from fixed caller roles

The new optional `actualPoints` argument defaults to `false` and is propagated
through list, quotient, function, and constructor data-field recursion. Only two
production entry points select `true`:

1. `objectPointSchema` after the fixed concrete-category dictionary supplies its
   carrier (`ComputationalData.lean:525-529` in the reviewed candidate).
2. `validateGraphAtKeys` when an actual codomain inventory is unavailable
   (lines 555-556). A supplied codomain inventory still uses `.keys`.

Neither public JSON nor a backend chooses the mode or its type. The ordinary
`validatePort` literal/record and callable schema calls, and `interfaceExtent`'s
published subset-literal schema, keep the default mode. Existing exact endpoint
comparisons, descriptor retention, actual inventory equality, uniqueness, graph
coverage, and ownership code are not changed by this patch.

## Constrained-data barrier and recursive literals

In actual-point mode, after the unchanged atomic codecs, the candidate consults
`ConstrainedPoint.schema?` on the independently fixed type. That unchanged helper
requires a closed, type-correct, nonrecursive structure with one constructor, no
indices, exactly one independently fixed data field, and only propositions in
the remaining fields. The new branch also requires `fieldCount > 1`.

The branch recursively derives a schema for that exact `dataType` and wraps it
in `.constrainedData`. `validatePoint` delegates to the wrapped schema and returns
only `Except String Unit`; it constructs neither a refinement witness nor a
replacement packet. `constrainedData.scalarLiteral` is always false. Consequently
the barrier propagates through enclosing list and record scalar classification,
preventing an outer `.literal` wrapper from reconstructing the excluded proof.

`Rat` does not enter this branch: its existing constructor has two data fields.
It still acquires its own complete literal wrapper in either mode. For a wholly
inline rational subtree, the child validates its field shapes and then calls the
unchanged `Codec.decode Rat`, preserving nonzero-denominator and reduced-form
checks. An opaque field prevents only full literal decoding; ordinary shape and
opaque-token validation remain in force. The thirteen original nested-rational
fixture cases are byte-identical to the base.

## Unresolved data parameters remain unsupported

The final rule is now:

```lean
if !ConstrainedPoint.closed type then .constrainedData schema
else if schema.scalarLiteral then .literal type schema else schema
```

This executes only after constructor unification and **every non-proposition
field's recursive schema derivation succeeds**. It does not turn a missing schema
into a successful one.

- An unresolved scalar bound such as `Fin ?bound` still returns `none` in the
  atomic branch because `type.hasMVar` is true.
- An unresolved data-field type still fails its recursive type/constructor
  inspection. Unresolved universe levels and loose bound variables are still
  rejected at entry.
- A subtype whose predicate is unresolved but whose `Fin 3` data field is fixed
  retains the bounded atomic child schema without acquiring a full subtype
  literal decoder. Both modes need this guard because the unchanged
  `PortableExtentDataProbes.lean:94` calls default `pointSchema` directly.

The new guard does not claim the unresolved predicate is true or choose a value
for it. It preserves only the independently derivable computational data slots.

## Ordinary Finset constraints are preserved

The mode default is load-bearing. A closed ordinary `Finset Int` does not enter
the actual-point constrained-record branch. Its multiset/list data shape is
scalar, the complete type is closed, and the final rule still produces
`.literal (Finset Int) ...`. Validation therefore reaches the unchanged full
`Codec.decode` and its `nodup` proposition check. This applies recursively in an
ordinary callable or record schema, as well as to direct `Codec.decode`.

This is distinct from actual-endpoint mode, where the public one-data-field
refinement protocol is intentionally treated as computational data. The review
does not assert that a Finset refinement predicate is checked in that mode.
`CodecConditionProbes.lean` and its duplicate-rejection assertion are unchanged.

## Exact endpoint and ownership boundaries

The reviewed patch changes no endpoint selection or equality. `finiteData` still
validates its descriptor before deriving a schema, rejects repeated inventory
points, and checks independently declared actual keys. `validateGraphAtKeys`
retains supplied codomain `.keys`, exact domain inventories, graph coverage, and
the existing rejection of dependent callable bodies. The lifted-subobject path
still permits only inventory enrichment of the exact original descriptor and
then retains the returned comparison's actual endpoints for the reverse map.

The barrier does not modify JSON. Existing value wrappers and opaque-token
validation remain before schema dispatch. DataOwnership and the lifted-subobject
consumer are byte-identical to the base. No source in the prior R1/R2 structural
projection repair is modified by this delta.

## Preservation and proposed additive control

The manifest records identical base and reviewed bytes for ConstrainedPoint,
Codec, LiftedSubobjectData, DataOwnership, and these existing controls:

- LiftedSubobjectDataProbes;
- PortableExtentDataProbes;
- CodecConditionProbes;
- NestedScalarLiteralProbes;
- ComputationalContractProbes;
- RecordProjectionBoundaryProbes.

`git diff --check` for the reviewed file returned exit 0. This is a source-format
check, not a build or execution test.

A minimal additive control, without changing any original assertion, can derive
`pointSchema` with `actualPoints := true` for the existing type expression
`ULift { q : Rat // q = 0 } × Nat`. With the existing one-field elision, use:

| Actual packet | Required framing result |
| --- | --- |
| `[[-3,7],5]` | Accept reduced Rat data without proving `q = 0` |
| `[[1,0],5]` | Reject zero denominator |
| `[[2,4],5]` | Reject nonreduced representation |
| `[["bad",7],5]` | Reject malformed Int data |
| `[[opaqueData("owned-numerator"),7],5]` | Accept the nested opaque data field, without full Rat decoding |

The packet notation is descriptive; `opaqueData` uses its existing public
envelope. This control checks that a nested Rat retains its own representation
checks while the surrounding product/ULift cannot recover a refinement proof.
The reviewer has not created or executed this probe. Root separately owns the
original focused controls and any additive execution.

## Limits

The conclusion applies to the source bytes and patch hashes above. It is not a
claim that a pending file was committed, compiled, or accepted. The prior
`scalar-refinement-design-review.md` preserves the failure diagnosis, the rejected
global-exemption design, and the closedness clarification. This report is an
independent engineering source review, not mathematical or authoritative CI
acceptance.
