# Reuse record: `cc-acceptance-permanent`

## Queries
`formalization_corpus.py search`:
- "golden test expected value immutable": no owner;
- "regression test oracle": test files only (proofnet-ir);
- "guard_msgs test expected output": Mathlib's `MathlibTest/*` convention.

This node authors no mathematics. Its assertions state facts whose proofs or citations it records.

## Owner
- Lean's `#guard`, and `decide` or `rfl` for Lean-checked equations.
- The language's public surfaces, which run whatever computations are installed, for the value
  under test; an assertion names no leaf, backend or handle, and is never established from a
  leaf's definitions.
- The expected values' mathematical owners:
  - A₂ discriminant group: Conway–Sloane, *SPLAG* ch. 4 §6.1 (`A_n^*/A_n ≅ ℤ/(n+1)`).
  - `card((ℤ/n)^k) = n^k`: Mathlib `ZMod.card` and `Fintype.card_fun`.

## New code, and why no dependency supplies it
The append-only manifest of admitted assertions, and the gate script that refuses to modify or
delete them. No dependency supplies this repository's immutability policy.
