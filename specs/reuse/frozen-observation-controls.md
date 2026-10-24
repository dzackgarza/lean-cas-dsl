# Frozen extension engineering observations

`CasAcceptance/Kernel/FrozenObservationControls.lean` is an optional runner against
the independently supplied mathematical extension imports. It does not change the
`.cas` inputs, register a mathematical row, or supply a leaf's expected answer.
Run it from the integrated repository root with the recorded package overrides.
`CAS_EXTENSION_CONTROL=RX05` or `RX09` selects one control; omitting the variable
runs both. `CAS_EXTENSION_CONTROL_REPORT` names the output JSON file.

## RX05 declaration selections

The public resolver accepts an explicit immutable `RegistryState`. The runner uses
the current accepted state, a permutation of that same state, the state with only
`cmp.rings.carrier` omitted, and the permutation of that omission. This tests the
generic resolution mechanism directly. It does not change Lean's imported
environment or claim to run the full assertion file in an alternate import graph.
The unchanged mathematical assertions have their separate execution scope.

The report contains four independent `environments` records, in that order. Each
record contains its own `selectedInventory`, complete typed receiver, and actual
resolution result. The inventory preserves the selected row order, every row's
stable identifier, referenced declarations and complete metadata; `cells` also
exposes each actual cell's endpoints, ordered sides and direction explicitly.
The cell-absent records retain all other accepted rows, including the additional
additive-commutative-monoid carrier route and its comparison. They therefore retain
three complete ambiguity candidates.

A coherent record has `resolutionKind: "resolved"`, a full `resolution`, and its
own `typedRequest`. An incoherent record has `resolutionKind: "ambiguous"` and its
own ordered `candidates`, each with a full resolution and typed request. The runner
does not copy the first environment's result into the second. The separate
`crossEnvironmentChecks` report comparisons of those independently obtained
results. Complete typed terms are compared by the independent structural typed
comparison, not by equal readable displays or a common truth value. Candidate
comparison ignores only candidate enumeration order and retains multiplicity.

## Typed term records

Each typed record is a self-contained term DAG with top-level `roots` and `terms`,
using the public question-identity term schema. A root is an index into that
record's own `terms` array, not an index into another record.

| Root field | Meaning |
| --- | --- |
| `roots.values[i]` | The complete retained Lean term at position `i`. |
| `roots.types[i]` | The independently inferred full type of that same term. |
| `roots.labels[i]` | The role of that term; labels are explanatory and do not establish equality. |

Every value and type is checked to be closed and well typed before encoding.
Proof bodies follow the existing question-identity quotient through their complete
proposition types. Data, ordered parameters, universes, selected dictionaries,
applications and maps retain their structural terms.

The ordered request values are the original selected receiver, complete route
functor, each actual route-step application, route image, operation functor,
operation input and operation result. They are followed by triples containing each
accepted comparison, its actual forward component at the receiver, and its inverse
component at that receiver. The labels identify every step and comparison by its
accepted identifier. Receiver records separately retain the prime-residue field's
forgotten selected ring and the existing residue ring in the independent source
theorem.

## RX09 exact negative admission

The runner reads the unchanged negative file with original one-based source
locations. All four prerequisite bindings must elaborate before the final binding
is attempted. It records the attempted original map, original endpoints, family
function and complete admission domain, including the selected topology.

The rejection must be mathematical invalidity at admission. The actual diagnostic
must contain a closed typed expression definitionally equal to the independently
published nonsummability theorem's exact `Summable` proposition. That expression is
extracted from Lean's typed diagnostic info, including lazy expression diagnostics;
matching printed error text is insufficient. The attempted family and domain are
also checked against the independent negative theorem. A parser error, unresolved
category name, unrelated type error, missing implementation, or internal failure
cannot satisfy this control. No summation or backend dispatch occurs.

The actual diagnostic obligation and the independent expected obligation have
separate complete typed records. `sourceLine` and `source` identify the rejected
binding even though this negative input deliberately contains no named `test`.

## RX10 fixed-question execution conditions

`CasAcceptance/Kernel/FixedQuestionExecutionControls.lean` reads the original fixed
question before selecting a computational environment. Its second independent
reading must preserve the complete typed question, and its actual operands and
whole reindexed map are compared with the independently supplied formal source.
It first materializes the complete selected callable and requires the later
original equality computation to consume the actual returned data.

Select the independent manifest with `CAS_FROZEN_LEAF_MANIFEST` and an output file
with `CAS_FIXED_QUESTION_REPORT`. `CAS_CONDITION_PROTOCOL_DIR` optionally selects
the directory containing `probe_reply_conditions.py`. Each of the six observations
retains the same question and proposition, its selected environment, actual result,
complete dispatches and returned callable ownership. A reader failure prevents all
six observations; it is never reported as one of the execution outcomes.

The correct environment is the independent manifest. The missing-registration
environment removes only registrations of the original generalized operation.
Unavailable and malformed conditions use an external public-port proxy: one
disconnects during that invocation, and one supplies invalid result data. The
wrong-result proxy owns an opaque callable backed by deliberately wrong computation
data; later requests consume that actual callable in the same process. The host
does not accept a supplied finite inventory as authority. The internal control
uses Lean's existing execution resource limit with an outer error handler. No new
kernel fault hook or leaf-provided internal status is introduced.

After a correct computation, the same selected map is retained inside its complete
Arrow and a subsequent composition. A second live session and a reconnected session
must reject the old callable before it crosses the process boundary. A fresh
realization in the replacement session must preserve the formal arrow and answer
the same original question. Backend token text may repeat across processes; the
host-owned connection identity determines ownership.

These are engineering controls of the public interface. The supplied mathematical
assertion and independent formal source remain the correctness authority. The
runner fails if any required outcome, actual callable reuse or session boundary is
missing; source compilation or a proxy's own smoke check is not a completed trial.
