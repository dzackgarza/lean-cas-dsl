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

## Published callable registration completion (2026-10-03)

Queries: corpus search `BinderEntry ObjectEntry application registration`, `published callable declaration`, and `finite sum product binder`. The corpus index returned zero indexed files, so its lack of matches is not absence evidence. Direct source search established the existing owners below.

Owner: upstream `Registry/Entry.lean` exports `ObjectEntry.application` and `BinderEntry.operation`; `Semantics/Algebra/FiniteSums.lean` declares `sumOver`/`prodOver` and binder rows, while polynomial, matrix and smooth-function owners declare their typed application fields. No new mathematics or semantic row is needed.

New code: Admission resolves those existing published callable fields to concrete port addresses and complete request forms. Binder addresses use their published ids; application fields use `ownerID#application`. Full signature instantiation remains the generic caller's responsibility. Registrations declare computations, not formal meaning or law proofs. The previous lookup demanded a separate morphism row and could not invoke the actual published binder operation.
