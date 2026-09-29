# Reuse record: `cc-external-leaf`

## Queries
`formalization_corpus.py search`:
- "external package plugin extension registered from dependency": no owner;
- "lake package depends import extension entries": Lake manifests (verso), no owner.

No mathematics is authored. The realization it adds realizes a registered forgetful functor
already in `lean-categories`.

## Owner
- Lake for the external package and its pinned dependency on `lean-cas-dsl`.
- The kernel's `register_leaf`, `#accept` and gap report.
- Lean's persistent environment extensions for rerunning admitted assertions in another package.

## New code, and why no dependency supplies it
- `#acceptance_rerun`: re-elaborates every admitted assertion in the current environment, so an
  external package with more realizations runs the same, unchanged assertions (workflow step 8).
- The external leaf itself (in `research`).
