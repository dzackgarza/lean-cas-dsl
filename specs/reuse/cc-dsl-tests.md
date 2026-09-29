# Reuse record: `cc-dsl-tests`

## Queries
`formalization_corpus.py search`:
- "test suite runner file of statements": no owner;
- "append-only assertion admission hash": no owner;
- "golden test expected output Lean": Lean's `#guard_msgs` (message equality, not propositions).

## Owner
- The language (`CasCatalogue.Language`) and its runner (`CasCatalogue.TestSuite`).
- Lake's `input_dir` target, which rebuilds `CasAcceptance.Suite` when a test file changes.
- `scripts/check_acceptance_permanent.py`, which admits each test with the `let`s before it.

## New code, and why no dependency supplies it
Only test files: the facts of `CasAcceptance/Permanent/*.lean` restated in the language, and
the syntax those facts need (morphisms and limit diagrams) when the language lacks it, each form
resolved through catalogue rows.
