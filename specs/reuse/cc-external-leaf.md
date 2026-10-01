# Reuse record: `cc-external-leaf`

## Queries
`formalization_corpus.py search`:
- "external package plugin extension registered from dependency": no owner;
- "lake package depends import extension entries": Lake manifests (verso), no owner.

No mathematics is authored. The realization it adds realizes a registered forgetful functor
already in `lean-categories`.

## Owner
- The leaf package: any package with a manifest `leaves.json` at its root and the programs it
  names. It depends on nothing Lean, and the contract only describes it.
- The kernel's admission (`CasCatalogue.Admission`), which reads the manifest named by
  `CAS_LEAVES` at run time and admits each registration against the catalogue; and the harness's
  gap report.

## New code, and why no dependency supplies it
- The manifest reader (`CasContract.Registration`) and the admission check: a registration names
  a catalogue operation and a declared input form, and its backend is declared in the manifest.
  Nothing else in a manifest is read. The suite is run only by `lean-cas-dsl`'s harness over a
  manifest (workflow step 8); a leaf package never runs it.
