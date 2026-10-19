# Question identity encoder reuse

## Queries

- `expression binder abstraction memoization`
- `Lean Expr abstract FVar cache`
- `de Bruijn proof irrelevant serialization`

These queries were run through `lean-categories/scripts/formalization_corpus.py search` on
2026-10-19. The corpus includes an expression-substitution implementation that caches
each content-addressed subexpression with its binder depth. It does not supply this
repository's typed-question serialization or proof-irrelevance rule.

## Owner

- Lean `Expr.abstract` and `instantiateRev` own conversion between local free variables
  and de Bruijn indices.
- `CasCatalogue.QuestionIdentity` owns complete, proof-irrelevant term serialization
  for the kernel's preserved question. `CasCatalogue.Realize.TermTable` owns sharing
  and the existing byte format.

## New code

Cache contextual encoding by the unopened expression and its binder context, so
fresh local IDs from repeated openings do not force another traversal. Retain
the existing canonical node descriptions, proof proposition types, and full
question identity.
