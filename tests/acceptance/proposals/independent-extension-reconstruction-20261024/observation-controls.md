# Observation controls for the reconstructed proposals

This file fixes independently specified observations around the mathematical questions in
[questions.md](questions.md). It is a proposal, not an execution report, an admitted fixture,
or authority to modify a permanent assertion or protected baseline. It contains no computation
provider identity and no wire data.

## RX-05: presence, absence, and registration order of the actual carrier cell

The mathematical receiver remains `PrimeResidues(5,hp)` and the selected forgotten ring remains
the old `ZMod 5`. All edges of the multiplicative and additive routes listed in RX-05 remain
present. The ordinary set-cardinality operation remains the same operation.

| Independently selected declaration environment | Required interpretation observation |
| --- | --- |
| Both full routes and the actual invertible `cmp.rings.carrier` | Retain both routes and the actual component at the selected receiver; reconcile them with this cell, whose designated source route is multiplicative |
| The same declarations in another registration order, with the cell present | The same mathematical receiver, routes, component, designated source, operation and question as in the preceding case |
| Both full routes, with `cmp.rings.carrier` omitted and no other supplied comparison resolving them | Retain both unresolved route candidates and report ambiguity; do not invent a component from equal endpoints or equal carriers |
| The same cell-absent declarations with the competing routes registered in reverse order | The same unresolved ambiguity and the same complete candidates |

Reordering is a permutation of the same selected declarations, not an opportunity to add a new
comparison or change a route. The cell-absent controls require a separately provided mathematical
declaration environment; this author has not created one by editing upstream mathematics.

For either coherent order, the fixed numerical answer is five, the component and inverse act
as the identity on residues, and both functor actions retain every selected ring morphism's
complete function. The distinct additive and multiplicative operations remain distinct in
every environment. An ambiguity observation is not success on a value assertion and must not
erase that assertion from any later fixed execution scope. [M06, M07, P02]

**Public-interface dependency:** the runner needs an independently specified way to select
these declaration environments and observe the complete route/cell interpretation. This
proposal does not define kernel internals or a replacement interpretation record.

## RX-10: fix the question before observing six execution conditions

The sole mathematical question is the one in RX-10:

`(q*.map ((2 : ZMod 5) • LinearMap.id))(3) = (1 : ZMod 5)`.

Its mathematical truth is independently established by `reindex_double_three`. The complete
selected coefficient rings, coefficient map, regular module, reindexed module, original linear
map, complete reindexed map, input residue, equality relation and expected residue are retained
before evaluation. All six conditions use that same question and required computation.

| Execution condition selected by the independent runner | Required observation | What remains fixed |
| --- | --- | --- |
| The required computations produce the correct complete data and value | Report `holds`; subsequent map use retains the actual computed callable | The original complete question |
| No applicable computation is installed for a required step | Report `gap` with the missing-implementation reason (`NoImplementation`); the mathematical operation and its domain remain available | The same question, with a reported execution gap |
| An applicable computation cannot be reached or its execution fails | Report `unavailable`; no mathematical invalidity judgment | The same question and expected answer |
| An answer fails the independently declared result interface | Report `malformed`, with no successful assertion and no substituted data | The same question and selected result type |
| A well-typed value disagrees with the proved answer | Report `wrong` and assertion failure; no redefinition of the operation or expected value | The same question and the proved residue one |
| The interpreter encounters an unexpected internal failure | Report `internal`, distinct from mathematical invalidity, ambiguity, missing implementation, execution failure and malformed result | The same required identity and its obligation to receive a result in the report |

“Correct” is established only by comparison with the independent source-grounded assertions.
A computation's own declaration that its answer is correct does not select that row or count
as evidence. The exact outcome names are from the newly supplied public observer specification
[P06]. “Malformed” and “wrong answer” are different observations: a well-typed wrong
residue is not reclassified as malformed merely because it fails the equality. [P01, P02]

The following controls apply to all six observations:

1. Do not replace the original equality by its truth value or by a proposition equivalent
   merely because both happen to be true.
2. Do not rebuild expected interpretation data from the current candidate's output. Compare
   against the full independently established mathematical question.
3. Do not remove an assertion from the fixed observation scope because its interpretation,
   infrastructure, or computation failed.
4. A failure must not commit a successful `assert`. The public specification commits that
   form only on a true observation.
5. Installing, removing, or changing a computation changes only execution availability or
   observed answers, never the selected mathematical operation, its domain, or its meaning.

The runner must select the six execution conditions outside the mathematical assertion. No
special operation, new proof input, provider label, or response encoding belongs in that assertion.
The `internal` condition is produced by a separate kernel engineering fault fixture. It is not
a verdict a computation is allowed to send; an error reported by a computation remains an execution
failure. The public observer specification also distinguishes realization ambiguity (`gap` with
its own reason) from semantic route ambiguity, which is determined before implementation
selection. RX-05's missing-cell environment is the latter. [P06]

### Public harness selection

The public observer interface [P06] is now supplied. It accepts an independently provided
assertion file and inventory, selects a computation environment separately with `--manifest`,
and writes a report using `--report`. The `--computation-only` option requests execution of
the same interpreted question instead of first discharging it in Lean. No command is run as
part of this reconstruction, and this proposal does not fabricate the missing admitted inventory.

The specified report fields are `id`, `question`, `proposition`, `kind`, `detail`, `fails` and
`dispatches`. A fixed-question observation must retain the independently specified full
question; equal readable displays or equal answers do not establish this. Actual dispatches
are necessary observations when execution is required, and are engineering observations rather
than mathematical correctness evidence. A proof-only `holds` does not discharge required
execution. [P06]

Changing a realization manifest cannot omit a mathematical cell. The independently specified
cell-absent and reordered declaration environments of RX-05 still require their own public
selection mechanism; they must not be implemented by modifying the mathematical assertion.

## Session ownership and full-map reuse

The selected callable is the actual reindexed arrow `d_R : M -> M` of RX-06/RX-10.
An independently supplied execution control must exercise a computed, session-owned callable
and reuse it in subsequent declared computations. A purely formal reference to `d_R` does
not by itself discharge the requirement to retain and consume a returned callable.

| Session observation | Required result |
| --- | --- |
| Reuse the computed complete map while its owning session remains live | Its original mathematical endpoints, parameters and ownership are retained; the fixed question can be answered by the required computations on that owning session |
| Carry that map inside a structured result, a selected transport/reindexing expression, or a later composition | Ownership follows the actual computed data through the wrapper; the wrapper does not detach or reassign it |
| Try to consume those owned data on a different session without an independently supplied valid transfer/re-realization | Reject that use at the computational ownership boundary; do not reinterpret it as local data or change the mathematical question |
| Close the owning session and establish a new session | The old owned data are not revived by reconnection; reuse cannot masquerade as successful computation |
| Independently compute a fresh realization of the same complete mathematical arrow in the new session | It is a new computational value with that new ownership; it does not retroactively validate use of the old owned data |

These observations apply when the returned data are session-owned. Portable values are a
separate permitted case; the control must not pretend that a genuinely portable value is
session-bound. Ownership belongs to the host-held connection context, not to a claim supplied
by the computation. Session failure does not turn the independently true equality into a
semantically invalid mathematical statement. [P03]

The public observer specification [P06] confirms that a fresh harness invocation opens fresh
sessions and imports no owned data from an earlier report. Deliberate foreign-session checks
are separate kernel engineering fixtures, not leaf verdicts or mathematical assertions.

**Remaining fixture dependency:** the precise triggers for the internal-fault and foreign-session
engineering fixtures have not been supplied to this author. Their required boundaries are fixed
above; no test-only execution hook is invented. Their eventual results must be reported separately
from the mathematical equality's correctness observation.

## Complete-result reuse in RX-07, RX-08 and RX-LIFT

The same completeness principle applies beyond RX-10. In RX-07, square and inverse transport
consume the previously returned element or whole map. In RX-08, the pairing and zero-composite
observations consume the actual kernel, inclusion and restricted form. In RX-LIFT, the second
stage consumes `firstInclusion`, the factorization equations consume the returned defining maps,
and the second universal factor consumes the actual first factor. The two finite factorization
samples are additional observations of maps on their whole rational domains.

A formal proof of an expected equation is its mathematical source. It cannot stand in for any
of these explicitly required execution/reuse observations, and a returned proof claim cannot
admit a new formed arrow, a new summable family, or a new comparison.
