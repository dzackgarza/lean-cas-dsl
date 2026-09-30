# Reuse record: `gov-kernel-lc14`

`scripts/check_kernel_totality.py`, and the kernel repair of `Language.lean` (numerals from rows, explicit domain formation, evidence proved when read, `functionOf`).

## Queries
- `search "Continuous fun_prop composition"`: Mathlib's `fun_prop`, `Continuous.comp` — used for continuity evidence;
- Mathlib `isUnit_iff_ne_zero`, `Matrix.isUnit_iff_isUnit_det` — used for unit evidence;
- Lean `Term.withSynthesize`, `withoutErrToSorry` — used to scope and fail proofs.

## Owner
- Mathlib's tactics and lemmas; the catalogue's numeral, inclusion and admission rows.

## New code
The kernel's reading rules (which the catalogue does not own) and a line-level gate over `catch`.
