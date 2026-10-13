# Reuse record: `gov-registry-gates`

The totality gate in `lean-categories` (`Registry/Totality.lean`), run by `normalized_registry`.

## Queries
- `formalization_corpus.py search "partial function option valued"`: Isabelle's partial functions, no gate;
- `search "total function domain subtype"`: mathcomp's function theory, no gate;
- `search "linter forbid constant in declaration"`: no Lean linter forbids constants in a declaration's closure; Mathlib's linters are syntactic style checks;
- `search "Units inverse group structure IsUnit"`: Mathlib `Units`, `IsUnit`, `Group` — the gate asks instance search for `Group α`.

## Owner
- Lean's `Expr.getUsedConstants`, `Meta.transform`, `synthInstance?`; Mathlib's `Group`.

## New code
The closure over this repository's definitions and the refusal at registration: no linter owns a semantic check at registration.
