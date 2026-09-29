# Reuse record: `cc-param-constants`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `family fibre concrete parameter instantiate` | none relevant |

## Owner
- A family's fibre at a parameter is its registered realization applied to that parameter (the
  pseudofunctor's value); the parameter objects are Lean terms (`ℤ` with its `CommRing` instance).
- Sort checking of a named parameter is Lean elaboration against the schema's parameter kind.

## New code, and why no dependency supplies it
A `ParameterExpr` constructor naming a Lean constant as a parameter object, its sort by
elaboration, and its manifest encoding; registry syntax only.
