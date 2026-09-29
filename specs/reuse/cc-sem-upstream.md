# Reuse record: `cc-sem-upstream`

## Queries
`formalization_corpus.py search`:
- "environment extension registry of declarations attribute": no owner in the corpus.
- `lean-categories` has no registry: no `LeanCategories/Registry`, and no module mentions one
  except two lattice files, in prose.

## Owner
- The rows' mathematics is already `lean-categories`' and Mathlib's: every semantic row names a
  declaration there, or in `CasCatalogue/Semantics/*` where it is to move.
- Lean core's `SimplePersistentEnvExtension` carries rows across imports, as it does today.

## New code, and why no dependency supplies it
None new. The semantic half of the registry (schema, validators, the write command and the rows)
moves unchanged in meaning from `lean-cas-dsl` to `lean-categories`. The split separates it from
the realization half, which stays.
