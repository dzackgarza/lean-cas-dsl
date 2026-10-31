# Original operation recipe validation: V7b/V8 follow-up source review

## Scope and finding

**No concrete blocker found in the bounded original-recipe validator delta.**
Reviewed the exact V6-to-V7b change and the subsequent V7b-to-V8 correction in
the immutable snapshots under
`/workspace/scratch/c3e234b1b92d/kernel-verification-20261026/operation-presentation-eeb8fb2`.
The snapshots' hashes match their supplied manifests. I also verified that each
saved delta is exactly the unified diff of its named source snapshots.

This review covers the original recipe versus actual graph validators and their
local owner/dependency bindings. It does not reopen the separately reviewed V4
presentation mechanism, assess the full candidate, inspect leaves or fixed
answers, or judge mathematical meaning. No Lean execution, build, source edit,
or compiled-artifact change was performed by this reviewer. Compilation and
any subsequent engineering trial belong to root/workflow_execution.

## Exact reviewed sources

| Artifact | SHA-256 |
| --- | --- |
| V6 Realize snapshot | `0ddce655a65e976de13759edc2c72cbf29ff3257f05132b01a2a5b3ae16fbb03` |
| V7b Realize snapshot | `dbf68780fea57534b9ec4d86911aac25d471ed88ed9676c6a3e834132af4d87b` |
| V7b-minus-V6 delta | `350882d66e28840ceed5cb153e92aac51da60e3b480c82683f15bee4cc2bb4e2` |
| V8 Realize snapshot | `fc863d9b04351cf0dfa247031c3a625cc29fbdd3922bd12dc82e05ac8e313102` |
| V8-minus-V7b delta | `93566870839206a34f3512a0702fffc3265ca431d192600cb95cc1a2ba765f6e` |

Supporting validators were read using `git show` at immutable local commit
`5e948913e71cdcb1c2b5d3ba9a95d1d47f3c13ca`, tree
`a6f6f3569c1b6386c9ee5a4a158ac2ed27dc2eb8`, through
`/tmp/kernel-native-20261026`. This tree equals published `8f454d6`.

## Complete owner and positioned dependency binding

V8 `operationPointRecipeInputs` at lines 6991-7017 first excludes a completed
callable or completed point-data interface. For an `element` recipe it requires
the exact `point.value` trace node to be `elementNumeral` or `operationApply` and
takes that node's retained `selected` owner. The unchanged Trace constructors
separately store `target` and `selected`; a reduced target carrier is not used
as the owner.

`realizeUnobserved` receives that exact selected expression. The helper then
checks both the complete type and value against the trace selection, under
`withoutModifyingState`. It compares the resulting owner's full fragment with
the original `args[0]` position. This is `DataOwnership.Data` equality, including
the supplier table, rather than equality of JSON alone. No cache scan by carrier,
descriptor, or convenient matching value chooses the owner.

The original expression is separately projected from `args[1]`. The helper
rederives the expression through the existing `elementFragment` traversal and
requires full fragment equality before returning its dependencies. That traversal
uses the trace's ordered operation parameters and operands (V8 lines 4484-4519);
completed child results remain exact dependencies. Reordered data, changed
suppliers, or a different actual child representation cannot be silently rebound
while satisfying this complete positioned equality.

The supporting DataOwnership implementation (`DataOwnership.lean:129-132,
186-195`) derives equality over JSON plus ownership and validates coverage before
and after a positioned projection. Thus these checks do not merely compare
tokens or recover owners by searching JSON.

## Local cache copy does not erase the outer computation

The helper allocates a new IO reference containing the current immutable result
map with only the exact `point.value` key removed. It does not erase a key from
the original `h.results` reference. This avoids `elementFragment`'s shortcut
that would otherwise encode the outer recipe itself as a cached `point` while
trying to inspect that recipe's original expression.

This is guarded at both the caller and helper: a callable with
`callableObserved` or `pointDataInterface` cannot enter the recipe-inspection
path. Every other cached entry, including completed children, remains in the
copy. Reconstructed expression data and ownership must still exactly equal the
original expression slot.

The enclosing `operationPointEndpoints?` supplies an inspection harness with no
admitted implementations, backends, deferred implementation, derivation, or
dispatch sink, and object-action demand disabled (V8 lines 7145-7155). It may
reuse retained results; this metadata inspection cannot dispatch a new outer
computation. The scope of this finding is the local results-reference removal;
it is not a claim that every existing metadata helper performs no cache writes.

## Duplicate descriptors cannot select by order

Before constructing `InterfaceObjects`, the caller checks every source, target,
owner, and dependency Wire. If two JSON descriptors are equal but their complete
operation-point presentations differ, it raises `ambiguousRealization` (V8
lines 7063-7071). It does not choose the first such context or discard one.

`sameOperationPointPresentation` includes exact formal expression, JSON,
ownership, point-data interface, comparisons, payload representation, form,
observation/framing flags, service handles, category context, and construction
input metadata through its existing helpers (V8 lines 415-425 and 3693-3706).
Unsupported lift/refinement/construction provenance is conservatively refused by
`checkOperationPointPresentation`. Consequently the existing first-match lookup
inside `interfaceObject`/`interfaceArgument` cannot pick different complete
contexts merely by the new input vector's order.

The caller returns `#[point] ++ inputs`; it does not replace the original point
with its owner or a reconstructed expression. Those dependencies feed the
existing invocation payload and service-operand retention path (V8 lines
7308-7318).

## Recipe validation and actual graph validation remain distinct

The point's already checked complete `typedMap` framing supplies source and
target data. The new dispatch opens transparent value wrappers in its callable
payload and recognizes raw arrays or the canonical `finiteGraph` payload. Those
actual graph cases call the unchanged `validateEndpointPort` on the complete
original frame, exact formal point, and retained actual endpoint descriptors.

At immutable supporting `ComputationalData.lean:1163-1186`, that validator:

- checks typed-map endpoint descriptors against the selected computational ones;
- requires actual source keys from `endpointKeys`;
- checks an explicit graph inventory against those actual keys;
- retains the actual codomain keys when present; and
- passes the graph to `validateGraphAtKeys` for coverage and output checks.

No preceding generic function decoder replaces those graph keys with the formal
carrier's enumeration. The new branch neither omits nor catches failures from
this actual-graph check.

Symbolic callable recipes instead use the existing `validateCallableAt` at the
point's complete independently inferred type and the exact local input map. Its
`typedMap` branch checks the complete endpoint interfaces, and its `element`
branch checks the selected object's carrier plus the original expression
(`ComputationalData.lean:2440-2446, 2575-2583`). This supplies the appropriate
declaration/interface validation for a recipe; it is not an unconditional
acceptance path. Other nested symbolic forms continue to use that existing
validator's recursive rules. This bounded review does not claim a fresh audit
of the complete underlying symbolic grammar.

## V8 correction

The exact V8 delta contains two changes only:

1. Put the `noImplementation` message on the same match-arm expression.
2. Infer `pointType` before validator selection, then pass that value to the
   symbolic branch instead of using a nested monadic action there.

The point type still comes from `point.value`, not from data. This is the same
formal point whose type and categorical endpoints were already checked earlier
in the function. Neither change alters selection, equality requirements,
dependency retention, graph classification, or failure handling. This report
does not itself assert that V8 compiled or executed successfully.

## Limits and retained evidence

Root reported V7b's compiler failure as message-layout/nested-action syntax; the
V8 patch manifest records the corresponding syntax retry. Failed attempts remain
in the producer evidence directory. No result from a later compile or trial is
inferred in this source review.

`operation-recipe-v8-source-manifest.json` records the supporting source hashes,
exact reviewed deltas, stable snapshot guards, and scope. The two reviewed delta
copies are saved beside this report. This is an independent engineering source
finding, not a mathematical-meaning verdict or authoritative acceptance.
