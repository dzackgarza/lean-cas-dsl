# Reuse record: `cc-harness`

## Queries
`formalization_corpus.py search`:
- "importModules run command elaborator from executable": etheorem's proof-coverage script (reads
  an environment; no test runner);
- "withImportModules Frontend runCommandElabM": no owner;
- "test runner executable Lean environment": no owner.

## Owner
- Lean's `importModules`, `Lean.Elab.Command.liftTermElabM` and `Lean.Elab.Frontend`.
- The runner `CasCatalogue.TestSuite` (`runFile`), which the harness calls unchanged.

## New code, and why no dependency supplies it
An executable that loads the catalogue, the language and a given set of installed leaves (each
written against the intake contract only), runs every file of `tests/acceptance/`, and writes the
outcome of each test and the derived gaps. Leaves never import it or the suite.
