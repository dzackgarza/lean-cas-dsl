# Reuse record: `cc-memo-resolve`

## Scope

The search and implementation description below record the **2026-09-29** specimen.
They are not a current implementation inventory or a theorem about arbitrary registered
computations. Reconciliation on 2026-10-29 applies the selected-result distinctions of
[CC-MEMO](../computational-core.md) and [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69).

## Queries

Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `memoization cache functor application` | Lean-blaster `Optimize/Env.lean` (a tactic cache; not a model) |
| `memo table hash map cache Lean` | SizzLean `Cache/Box.lean`, verso `HashMap` tutorial |

Those searches supplied cache implementation references. Their results do not establish that
no reusable evaluator or retention mechanism exists. Current implementation work uses the
source-appropriate searches required by CC-REUSE and the existing `cc-realize-2cat` record.

## Owner

The historical specimen used Lean core's `Std.HashMap` in an `IO.Ref`, then located in
`CasCatalogue/Memo.lean`, keyed by the explicit application. Its `memoApply none` path was the
unmemoized call. The plan records agreement for that dated specimen; it does not establish
that every backend execution repeats its answer or that every selected result is disposable.
`Memo.lean` is absent from both inspected current trees: main
[`d0162dd`](https://github.com/dzackgarza/lean-cas-dsl/tree/d0162dd4c2bb795dec223a48252db9df6cb51a9e/CasCatalogue)
and candidate
[`8e9ad08`](https://github.com/dzackgarza/lean-cas-dsl/tree/8e9ad083dd214cbbe4538c8bfcbf34a0eb22e465/CasCatalogue).

The current obligation is to retain the actual result and its defining data through later
use. A lookup index can be discarded while preserving that result. Re-executing a computation
is different: arbitrary untrusted executions need not agree, and an operation that selects
noncanonical data may admit different choices. A formal single-valued operation remains that
operation; implementation variability never changes its question. The selected result,
its associated maps and the ownership needed to use them cannot be replaced by a fresh choice
under the description of cache recovery.

## New code, and why the obligation remains

The original work routed resolved calls through a memo table and compared memoized and plain
runs. Current #69 work reuses adequate retention and occurrence mechanisms, removes competing
result-recovery paths, and distinguishes reuse, fresh evaluation and explicit replay in its
existing difficult chain. It creates no separate cache framework.

Where recomputation is used as an optimization, state the declared relation and the conditions
under which it preserves the required observation and dependent data. Cache agreement alone
is not mathematical correctness evidence. The independently fixed acceptance questions and
expected values remain authoritative in both modes; loss of an unrecoverable owned result
reports its actual availability failure instead of silently supplying another selection.
