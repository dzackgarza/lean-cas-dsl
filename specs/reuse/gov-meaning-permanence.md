# Question identity encoder reuse

## Queries

- `expression binder abstraction memoization`
- `Lean Expr abstract FVar cache`
- `de Bruijn proof irrelevant serialization`

These queries were run through `lean-categories/scripts/formalization_corpus.py search` on
2026-10-19. The corpus includes an expression-substitution implementation that caches
each content-addressed subexpression with its binder depth. It does not supply this
repository's typed-question serialization or proof-irrelevance rule.

The 2026-10-24 direct reading-comparison work searched the same corpus for
`typed expression structural equality proof irrelevance` and
`operation trace comparison parameter transport`. The results include generic
kernel definitional-equality implementations and unrelated trace computations;
none supplies this repository's typed request/operation-tree comparison. Data
reduction by definitional equality would not preserve the specified question
identity and is not used as that comparison.

The same date's snapshot-ordering repair searched for `canonical serialization sort
duplicate keys` and `stable sort secondary key`. The returned compiler partitioning
and Lisp sorting code does not own this snapshot schema. Lean `Array.qsort` supplies
ordering; the kernel supplies the complete retained-record keys.

## Owner

- Lean `Expr.abstract` and `instantiateRev` own conversion between local free variables
  and de Bruijn indices.
- `CasCatalogue.QuestionIdentity` owns complete, proof-irrelevant term serialization
  for the kernel's preserved question. `CasCatalogue.Realize.TermTable` owns sharing
  and the existing byte format.
- Lean `Meta.isTypeCorrect`, `inferType`, `withLocalDecl` and `withLetDecl` own typed
  traversal. The independent comparator consumes these directly, not the serializer.
- Upstream `CategoryExpr.syntacticEq` owns exact symbolic category comparison.
- Lean `Array.qsort` owns sorting. `QuestionIdentity.orderByCompleteKey` preserves the
  previous primary order and requests full canonical keys only for colliding groups.
- `Language.Claim`, `CasCatalogue.Node` and `CasCatalogue.ParameterPresentation` own the existing
  retained reading data; `QuestionComparison` compares every field they preserve.

## New code

Cache contextual encoding by the unopened expression and its binder context, so
fresh local IDs from repeated openings do not force another traversal. Retain
the existing canonical node descriptions, proof proposition types, and full
question identity.

Directly compare the complete prepared claim and its retained operations, including
expected decisions, selected parameters, actual structural applications, defining
maps, presentation orientation and proof proposition types. Trace maps and alternative
parameter presentations are compared by a bijection with multiplicities, while each
route and parameter vector remains ordered. The outer operation match is exhaustive,
so an added trace constructor requires an explicit comparison. Neither serialized
identities, cached display strings, runtime results nor revision labels decide the
comparison. The comparison in the current environment does not assess changed
declaration definitions across mathematical revisions or admit any migration.

The integrated trace comparison also retains directly selected construction and
construction-map parameters, category/functor parameters, complete derived category
contexts, core objects/isomorphisms, selected lift/factor data and constructor-induced
cell components/endpoints. Structured projections retain their receiver, named field
and optional ordered port; cartesian transport retains its functor, parameters,
actual base morphism, receiver and selected field. A category context compares the
upstream symbolic expression and the actual selected typed bundle; equal printed
endpoints are insufficient.

Snapshot ordering now uses the complete operation record to break equal canonical
root keys, and every presentation field to break equal source/route/parameter keys.
There is one operation encoder and one presentation encoder for both final output
and complete tie keys, using the same shared source term table and proof-proposition
quotient. No operation or presentation is deduplicated. The key strings order a
serialization only; the independent typed comparison remains a separate traversal.

The interpretation boundary also rejects conflicting failure tags in nested diagnostic
context as internal errors. An arbitrary tag order cannot promote a computational
failure to semantic invalidity; legacy and published semantic-ambiguity tags denote
the same failure kind.

The read-only question exporter wraps the existing file-item parser, fixed binding scope,
`Realize.interpret` and its unchanged complete identity. It adds inventory coverage and
separate stage-tagged interpretation diagnostics without constructing a computational harness,
evaluating a claim, editing the fixed inventory or admitting a reading. Lean module loading
and the existing parser/serializer own interpretation; this tool adds invocation and reporting
only. Actual imported source/build provenance must accompany each export.
