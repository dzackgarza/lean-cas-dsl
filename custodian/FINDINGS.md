# Custodian findings, 2026-09-30

This file is inside the sealed boundary. Revisions cited: lean-cas-dsl `0ba53dab`, lean-categories
`c06aeedc` (the pin), lean-cas-dsl-leaf-contracts `6588a86c` (the pin), lean-cas-dsl-leaves
`c4cff164` (the pin). Some line numbers come from the sibling branch heads (lean-categories
`6b2750c9`, contracts `9fd3c176`) and are marked (head).

The owner's `specs/owner/convergence-process.md` matches the stated sha256 `fb3fe73c…`.
`Lean-Cas-DSL-Intent.md` is not in any branch or commit of `dzackgarza/research`.

## A. Holes in the orchestrator's gates

The seal (`CONTAINMENT.md`) makes each of these moot as a route to acceptance, because the gate
files, the kernel and the pins can no longer change without a new seal. The holes are still there,
and they are the orchestrator's record.

1. `scripts/check_authorship.py` (retired 2026-10-02; the findings below are why)
   - Identity is self-declared.
   - A commit with neither `Agent-Id` nor `Claude-Session` is "a person's" and is not checked
     (`commits()`, `if agent is None: continue`). Omitting the trailer bypasses the gate.
   - `CUTOFF` exempts all earlier history.
   - `chain()` silently skips any sibling repository that is absent.
   - The gate assigns the orchestrator `LeanCategories/Catalogue/Registry/*`, the admission
     validator for the mathematics it consumes.
2. `scripts/check_acceptance_permanent.py`
   - `--correct` rewrites or deletes any admitted assertion as soon as the `lean_categories` pin
     differs from the recorded one. Any re-pin satisfies that, including one to an arbitrary
     upstream commit the orchestrator can push.
   - Its authority is `AGENT_ROLE=acceptance`, an environment variable anyone sets.
   - A missing `admitted.json` is recreated empty.
   - The ledger is plain JSON, editable by hand.
3. `scripts/check_kernel_totality.py` exempted any `catch` next to the comment
   `-- not a reading fallback:`, so the author certified its own exemption, and it saw only the token
   `catch`. It is withdrawn (B0 Policy 5). The obligation it named, that no failure is reread into
   another meaning, is carried by the one outcome model (`cc-failure-strata`: every failure is
   reported as its stratum, an untagged one as an internal error) and by the acceptance comparison.
4. `CasGates/KernelPurity.lean`
   - `evidenceRunner.isPrefixOf d` exempts every declaration named `CasCatalogue.Language.establish.*`.
   - `CasContract.Probes` is skipped.
   - If `.lake/packages/cas_leaf_contracts/CasContract` is absent, `moduleFiles` returns `#[]`,
     so contract coverage passes vacuously.
   - `kernelRoots` excludes `CasDsl` and `CasTools`.
   - `allowedModules` admits `LeanCategories.Catalogue.Registry`, which the orchestrator writes.
5. `scripts/check_reuse_records.py` is keyed on the "Delivered"/"Next" markers the orchestrator
   writes in its own plan, and is not run in CI.
6. `.github/workflows/gates.yml` is taken from the pushed commit, and no branch is protected, so
   CI judges a change with rules that the change can edit.

## B. Mathematics admission (lean-categories, at the pin)

7. `Registry/Semantic.lean:2310`: the totality closure ends in `| _ => #[]`, so categories,
   functors, methods, properties, lifts, cells, limits and the other kinds are never
   totality-checked (introduced in `d4d6f1a`).
   - The ban list (head) is `Option, Part, PFun, Ring.inverse, Matrix.nonsing_inv, Matrix.inv`.
     It omits `Except`, `sorryAx`, `default`/`Inhabited` and `WithTop`/`WithBot`.
   - The `⁻¹`/`/` check skips types with loose bound variables (head `Totality.lean:71`), so
     `fun {K} [Field K] (x : K) => x⁻¹` passes.
   - The gate's own docstring says it "does not certify that a row is well defined". This is the
     owner's "ill-defined spec" hole, still open.
8. `Registry/Semantic.lean:2290,2375`: the author of a semantic row is decided by the module's
   root name (`LeanCategories`). Any package, a leaf included, can name a module
   `LeanCategories.X` and write semantic rows. The seal closes this for lean-cas-dsl and for leaves
   at the pin (path checks); upstream it is still open.

## C. The leaf contract (at the pin)

9. A leaf self-declares `trust := .trustedAssertion` on an unproved implementation (head
   `Extension.lean:464`), and it is accepted with a label.
10. `isLeafModule` is a denylist: any root not in `nonLeafRoots` is a leaf.
11. `RealizerEntry.category` is a leaf-declared parent category. The owner's step 2 names exactly
    this as the wrong design.
12. The contract repository has no gate and no CI.

## D. The kernel (sealed at the baseline, recorded as debt)

13. `CasCatalogue/Language.lean` has 43 `unreachable!` (the full list is `banned_baseline` in the
    seal). The ratchet forbids new ones. Removing them is a kernel proposal. A `partial def` is not
    on this list: it is implementation recursion that Lean keeps opaque, not a mathematical
    operation given a value outside its domain (B0 Policy 5), so the ratchet no longer bans it. Where
    a pure algorithm must terminate on valid input, that is shown for the algorithm; an effectful
    failure is reported as an implementation failure, never as a mathematical one.
14. `CasAcceptance/Standard.lean:380` proves an acceptance probe with `native_decide`, which trusts
    the compiler rather than the kernel.
15. `lakefile.lean` requires `nbdsl-worker` at `main`, a floating ref. The seal fixes the manifest
    revision.

## E. Leaves (at the pin)

16. The leaves put algebraic structure on handle types: `instance Group`/`CommRing` on tables
    (head `Algebra/Actions.lean:44–72`, `RingTables.lean:55`, `RingActions.lean:63`), and
    `ValueRing.castHom : … → Option` (`Modules/Bilinear/Valued/WForms.lean`).
17. `Algebra/RelabeledRings.lean` and `HostileSubgroup` (`Subgroups.lean`) are test-shaped
    fixtures, and `b818e4c` ("probe") has no role trailer.
18. The leaf scan against the seal's rules at the pin is clean (`leaf_baseline` in the seal).

## F. Judgment of `specs/proposals/extension-language.md`

**Not adopted as written.** Row by row:

- **Leaf: delete the forbidden constructors of `LeafContribution`.** Accepted in direction. It is
  what step 2 requires: unrepresentable, not rejected. It changes the sealed contract pin, so it
  enters only through a new seal. The negative probes must become a statement about the type's
  constructors, as proposed.
- **Leaf: remove `ImplementationEntry.trust`.** Accepted in direction, for the same reason (finding 9).
- **Leaf: keep `RealizerEntry.category`.** Rejected. The owner's text: "A leaf-facing 'declare
  parent category' field is already the wrong design if the category should follow from the
  construction." The proposal concedes that "the field could also be derived" and keeps it anyway.
  The category must be derived from the denotation's type.
- **Leaf: keep `backendOperation` and the dependent `presentation`.** No objection. The dependent
  check is still "build pending", so it is not delivered.
- **Leaf: realization ambiguity.** The step 3 argument is owed and not supplied. It remains an open
  obligation, not a kept interface.
- **Formalization: the validator is trusted core.** Agreed. The seal implements it: the
  `lean_categories` pin cannot move without a new seal. The proposal omits findings 7 and 8, the
  concrete admission holes.
- **Formalization: the orchestrator relays only a requirement's location.** A goal with no
  mechanism. The orchestrator spawns the formalization agent and writes its prompt, and nothing
  the orchestrator cannot forge separates the two. Recorded as unsolved.
- **Kernel: split `RegistryState` so the semantic reading cannot receive realization rows.**
  Sound, and structural as step 3 asks. It is a kernel proposal under the seal.
- **Kernel: `establish` and `KernelPurity` are trusted core.** Agreed. The proposal does not
  mention the gate's own exemptions (finding 4).
- **Acceptance: meaning permanence and prompts.** Meaning is now protected by sealing the kernel
  and the `#accept` elaborator. Prompt authorship is the same unsolved identity problem as above.
- **Omitted by the proposal:** every hole in section A. Those are the orchestrator's own
  exemptions. The proposal inventories the subagents' interfaces and not the orchestrator's.

## G. What remains unsolved (owner decision needed)

- **Independent authorship.** Every subagent is spawned by the orchestrator. Only keys the
  orchestrator never holds can separate roles: a formalization session and an acceptance session
  that the owner starts directly, each signing its deliverable. Until then, "independent" can mean
  only "sealed by the owner after review".
- **Successor signer.** The custodian's key dies with this session. Either the owner signs future
  seals with a key of their own, or the owner names a new custodian session and receives its
  fingerprint.
