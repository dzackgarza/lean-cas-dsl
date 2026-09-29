# Reuse record: `cc-failure-strata`

## Queries
- `formalization_corpus.py search`:
  - "Except error type stratified": no owner;
  - "computation outcome no implementation": no owner;
  - "Decision proved refuted unknown": verifier outcome enums (Strata), no reusable owner.
- This node authors no mathematics. It types the outcomes of the kernel's own resolution and
  execution (`specs/architecture.md`, "Failure is stratified").

## Owner
- Lean core `Except` for the carrier of a result or its failure.
- `CasCatalogue.Decision`, the three-valued decision outcome, unchanged.
- `CasCatalogue.Backend.PortError`, the runtime failures of a port. They map into strata 3
  (`unavailable`, `backend`) and 4 (`protocol`, and decoder rejections).

## New code, and why no dependency supplies it
- The kernel's outcome type: not applicable, ambiguous, `NoImplementation` with its gap datum,
  unavailable, and malformed.
- Its production by the resolver in place of string errors.
- The derived gap report.

These are the kernel's language-mechanics responsibility, and no library has this vocabulary.
