# Custodian findings, 2026-09-30

## 2026-10-13 — Current B0 construction defects

- Resolved in kernel construction source on 2026-10-18: neither the anonymous
  `Nat.Primes` parameter of `primeFactors` nor the anonymous `Fin n → K`
  parameter of `ker` requires new upstream mathematics. A parameter-free
  registered admission can form a point at an anonymous endpoint without
  assigning that endpoint a named alias; all applicable admission points must
  agree. A registered result constructor can be recovered from the direct
  declared parameters of the actual operand, but only when a registered point
  family names that constructor as its codomain. This recovers `Vec(K,n)` from
  the matrix's retained `K,n`, and the vector-zero family is then applied with
  those exact parameters. The unchanged prime-factor and matrix-kernel claims
  both read successfully against `lean-categories` `fd2cd45f` and contracts
  `3c2159b`; no carrier-only alias selection or assertion change was used.
- Performance defect observed on 2026-10-18: the matrix-kernel claim reads
  with trace recording in 12--40 seconds and produces 99 roots, but production
  `interpret` spent more than three minutes canonicalizing that trace. The
  identity encoder takes about 63 seconds before its 2--4 ms final JSON
  compression. An instrumented unchanged pass made 2,097,785 recursive proof
  checks and interner calls to produce only 640 canonical nodes; proof checks
  accounted for 10.9 seconds and interning 28.2 seconds. An exact contextual
  cache had zero hits because fresh local IDs distinguish the raw terms; making
  a fully abstracted key at every node repeated the expensive traversal. A
  function-spine proof-check optimization preserved the focused proof-identity
  probes but left exact encoding at 64.2 seconds and was reverted. The repair
  now encodes one source DAG and remaps its canonical nodes to reproduce the
  legacy standalone sort keys and final insertion order byte-for-byte. This
  removes the independent per-root expression pass: exact production
  interpretation completes in 149.890 seconds, with 65.178 seconds in source
  encoding, 0.988 seconds in remapped keys and 65.222 seconds in operation
  fields. Pre-encoding all operation fields made the exact run exceed three
  minutes because fields and roots do not share raw cache identities, and was
  reverted. A 2026-10-19 kernel candidate caches unopened syntax with binder
  context, so fresh local IDs no longer force those two repeated traversals.
  On the admitted 2×2 matrix-kernel assertion at latest-main mathematical
  revision `a2123729`, source and operation-field encoding each take 34--60 ms
  and the complete 28,383-byte question identity matches the previous encoder
  byte for byte. Semantic reading still takes about 10 seconds. A further
  generic morphism repair retained the first argument after it failed the
  declared leading-parameter check, instead of rereading it as the first
  operand. The 3×3 `subspaces.kernel` bindings now pass the ordinary budget,
  and its full 39,816-byte diagnostic identity is unchanged, but the assertion
  itself reaches a 200,000-heartbeat `whnf` timeout. Full protected acceptance
  has not run. Issue
  lean-cas-dsl#66 remains open for those integrated obligations; no timeout
  increase or weaker identity is acceptable.
- Diagnosed formal-side dependency on 2026-10-18: the registered
  `Units.invertibleEvidence` proves invertibility for the same matrix over
  literal `ℚ`, but refuses it over the selected rational-ring object used by
  the catalogue. Running the registered numeral normalization first changes
  the displayed entries to `1,2,3,4` and still fails. A definitionally valid
  `change` from that selected carrier to
  `Matrix (Fin 2) (Fin 2) ℚ` makes the unchanged evidence tactic succeed.
  Thus the determinant and unit evidence already suffice; the formal evidence
  tactic fails to normalize the selected-object construction before selecting
  its field/unit route. This is an upstream evidence implementation defect,
  not missing mathematics and not a kernel admission to reformulate. The six
  inverse readings remain blocked on lean-categories#92 until the formal owner
  repairs it.
- Repaired in controller construction source: a signed decision without
  `findings`, or with `findings: null`, could advance accepted inputs. Red
  regressions reproduce both failures; decisions now require an explicit list.
  Required request artifacts, signed discussion reconsiderations and MCP call
  arguments likewise cannot be replaced by empty runtime defaults.
- Repaired the mocked context test by exercising the production context's real
  file materialization and cleanup. It establishes transport of the complete
  payload, not the independent reviewer's mathematical or technical judgment.
- Open (2026-10-14): that test exercises `materialized_context` only, and
  `custodian/review/test_review.py` substitutes `call_reviewer`. No check
  observes the actual external reviewer reading the complete
  `requirements.txt`, `change.txt` and `explanation.txt` through its scoped
  read interface, or the retrieval directory removed after that real call.
- Resolved at the owning QC boundary: the lexical `lean-shim-suffix-decl`
  rule was specified as a reviewer tripwire, but its ERROR severity rejected
  nine engineering declarations. Independently reviewed PR ai-review-ci#469
  integrated as `9b43a56c23518412dd4aa145441f0d4bc6425cb7`; the ordinary
  installed `just test-push` now passes. No declaration was renamed or excluded.
  Every native suffix finding remains visible for review. Independent source
  assessment classified the equation-reader fixtures, computational envelopes,
  and packet planning/validation/projection as engineering, not catalogue
  mathematics. Three retained native partial-parsing diagnostics affect the
  workflow's curl-to-shell rule; independent inspection of each affected clone,
  Python invocation and commit command found no such pipeline. These individual
  dispositions establish neither surrounding workflow correctness nor B0 acceptance.


The dated findings below retain their historical revisions.

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
   `catch`. It is withdrawn (B0 policy 2). The obligation it named, that no failure is reread into
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

13. The former construct ratchet counted `unreachable!` occurrences as mathematical defects,
    including ordinary computational failure branches. Withdrawn 2026-10-03: `unsafe`,
    `extern`, `implemented_by`, `panic!`, `unreachable!`, and implementation recursion are
    assessed against their live role, not their count. Proof escapes remain prohibited.
    A computational failure does not redefine the mathematical request; returned computational
    data does not supply mathematical authority. Neither syntax absence nor source review
    establishes observed answer correctness.
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
