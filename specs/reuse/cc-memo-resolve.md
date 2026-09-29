# Reuse record: `cc-memo-resolve`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `memoization cache functor application` | Lean-blaster `Optimize/Env.lean` (a tactic cache; not a model) |
| `memo table hash map cache Lean` | SizzLean `Cache/Box.lean`, verso `HashMap` tutorial |

No formalization supplies memoization of realized functor applications; it is a runtime
optimization, not mathematics.

## Owner
- The table is Lean core's `Std.HashMap` in an `IO.Ref` (`CasCatalogue/Memo.lean`, CC-MEMO), keyed by
  the explicit application (action, handle).
- Values are the realized actions' images; semantics are unchanged (`memoApply none` computes the
  same value).

## New code, and why no dependency supplies it
Routing the resolver's realized calls (the images of handles along registered actions) through the
existing memo table, and the probe comparing memoized and unmemoized runs.
