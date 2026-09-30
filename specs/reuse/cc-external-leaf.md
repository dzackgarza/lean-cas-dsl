# Reuse record: `cc-external-leaf`

## Queries
`formalization_corpus.py search`:
- "external package plugin extension registered from dependency": no owner;
- "lake package depends import extension entries": Lake manifests (verso), no owner.

No mathematics is authored. The realization it adds realizes a registered forgetful functor
already in `lean-categories`.

## Owner
- Lake for the external leaf package, which depends on the leaf contract only.
- The contract's `register_leaf`, and the harness's gap report.

## New code, and why no dependency supplies it
- The intake contract: which modules are leaves (`isLeafModule`) and what they may import. The
  suite is run only by `lean-cas-dsl`'s harness over installed leaves (workflow step 8); a leaf
  package never runs it.
