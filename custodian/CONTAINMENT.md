# Containment of the orchestrator (custodian, branch `custodian/containment`)

Written by the custodian session `session_01GTQeWD4KCqYCeVd4SygciY` on 2026-09-30. This file is
inside the sealed boundary: a copy with different bytes is not this file.

## Operating phase

The phase is `custodian/phase.json` on `main`, read by the review from the base only: a candidate
cannot select it. It is `construction` until B0 is accepted (specs/architecture.md, "Operating
phase: B0 construction"). In construction:
- the seal, its verdict chain and the rejection log are construction material, not applied, and
  the orchestrator replaces this controller like any other part of B0;
- the fixed obligations still fail every change: the ratchets, no leaf in the DSL, the leaf rules,
  no semantic rows downstream, packages at their manifest revisions, and the admitted assertions
  (`verify.py --construction` checks exactly these);
- every other change to the boundary gets an independent technical review, which reports findings
  and signs nothing.

The phase becomes `steady` only after B0 is accepted at one revision tuple and the completed
workflow has shown both its required rejections and ordinary development. The rest of this file
describes the steady phase, except where it says otherwise.

## Trust anchor

The seal `custodian/seal.json` is signed (`custodian/seal.json.sig`) with the owner's SSH key, by
`ssh-keygen -Y sign` in the namespace `lean-cas-custodian`. The private key stays on the owner's
machine. The orchestrator runs on cloud machines and never has it. `custodian/root.pub` is the
public key.

The key's SHA256 fingerprint comes from outside the repository: the owner's machine
(`ssh-keygen -lf ~/.ssh/id_ed25519.pub`) or the owner's GitHub keys
(https://github.com/dzackgarza.keys):

    SHA256:IO3YM5setrWvSESXaXEr+7CB1YR8BOjKTP2SzTLFZbI

The copy above is informational. A verifier trusts only the fingerprint its caller supplies from
outside the repository. The orchestrator can rewrite this file, the key and the verifier on any
branch. It cannot make them verify under the owner's fingerprint.

## What is fixed

The seal fixes the following at lean-cas-dsl `0ba53dab` (the owner's convergence process verified
at sha256 `fb3fe73c…`):

1. **The acceptance boundary, byte for byte** (`custodian/boundary.json`). This is the evaluator
   and kernel (`CasCatalogue`), the surface language (`CasDsl`), the gates (`CasGates`,
   `scripts/check_*.py`), the harness and audits (`CasTools`), the build definition
   (`justfile`, `lakefile.lean`, `lean-toolchain`), the acceptance meaning and assertions
   (`CasAcceptance`, `tests/acceptance`), the owner's text (`specs/owner`), and this directory.
2. **The upstream rule files, byte for byte.** `lean_categories`' catalogue
   (`LeanCategories/Catalogue.lean`, `LeanCategories/Catalogue/*`: the admission rules) and the
   leaf contract (`cas_leaf_contracts`' `CasContract.lean`, `CasContract/*`), read from the
   package checkouts in `.lake/packages/<package>/`. No revision is sealed: `lakefile.lean` requires `lean_categories`,
   `cas_leaf_contracts` and `cas_leaves` at `main`, and `lake-manifest.json` records the resolved
   commit. A revision that leaves the rule files unchanged passes with no review; a change to a
   rule file is reviewed.
3. **The packages are what the manifest records.** Each package in `.lake/packages` is a checkout
   at its `lake-manifest.json` revision with no changed tracked file, never a link to a working
   tree (`pin_dev.py` made such links). `lean_categories`, `cas_leaf_contracts` and `cas_leaves`
   must be checked out: an absent package leaves its sealed files and its leaves unchecked.
   `scripts/ci_chain.py <checkout>` makes the checkouts.
4. **The admission ledger** `CasAcceptance/Permanent/admitted.json`. It may only grow: sealed
   assertion hashes and `corrections` never change.
5. **Ratchets that only tighten**, each with a baseline in the seal:
   - no new `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern`,
     `panic!`, `unreachable!`, `native_decide` or `ofReduceBool` anywhere in lean-cas-dsl;
   - outside the boundary, no syntax, elaborator, macro, `initialize` or global attribute, and no
     semantic registration or `LeanCategories/` module;
   - no leaf in lean-cas-dsl;
   - leaves (`.lake/packages/cas_leaves`) are subject to all of the above, and may also not define
     syntax or elaborators, import the kernel or the tests, read `tests/acceptance`, register
     semantic rows, place modules outside `CasLeaves/`, or require lean-cas-dsl.

## Interventions that are now detectably invalid

After `python3 scripts/ci_chain.py`, with `python3 custodian/verify.py --trusted-fpr <owner's
copy>`, each of the following fails verification:

| Intervention | Why it fails |
| --- | --- |
| Edit, delete, or add to the gates, their exemption markers or allowlists, `justfile`, `lakefile.lean` | sealed bytes |
| Change the kernel, evaluator, `#accept` meaning, harness or axiom audit, and call it accepted | sealed bytes |
| Edit or delete an admitted assertion, or rewrite `admitted.json` | sealed bytes and sealed ledger |
| Use the `--correct` path to rewrite assertions | sealed ledger |
| Change, add, remove or rename an upstream rule file: new admission rules, a relaxed contract | sealed bytes of the rule files |
| Build against a dev-linked working tree, or a package not at its manifest revision (`pin_dev.py`) | package check |
| Ship a leaf or a probe leaf in lean-cas-dsl | leaf check |
| Write semantic rows downstream (`LeanCategories.*` module, `normalized_registry`) | outside-boundary check |
| Redefine `#accept` or any syntax from a leaf, or from an unsealed file here | syntax ratchet |
| Make an example pass with `sorry`, an axiom, `native_decide` or `implemented_by` | banned-construct ratchet |
| Let a leaf see the tests or the kernel | leaf import and read checks |
| Edit the owner's text | sealed bytes |

A failing example can turn green on a verifying head only through what stays free: a leaf at a new
`cas_leaves` revision and mathematics at a new `lean_categories` revision, judged by the sealed
catalogue, contract, kernel and suite; and files outside the boundary, which cannot define syntax.

## The acceptance loop (closed, agent-driven)

The seal in force is the root seal, extended by a chain of signed verdicts in
`custodian/verdicts/NNNNNN.json`. Each verdict names the sha256 of its predecessor and carries the
next seal. The root seal names the only keys that may extend the chain:

- **review key** (fingerprint `SHA256:c5KRoTxWaBGLmRjZIJZlyzjO3Y4L8hap0TXK6SnjB8A`), an SSH key that exists only as the secret
  `CUSTODIAN_REVIEW_KEY` of the `custodian-review` GitHub environment;
- **escalation key**: the owner's SSH key, the same key as the root (`custodian/root.pub`).

Every signature is an SSH signature in the namespace `lean-cas-custodian`.

A change reaches `main` only through a pull request, and `.github/workflows/custodian-review.yml`
judges each one. That workflow runs on `pull_request_target`, so its code is `main`'s, and it only
reads the pull request's head. It gives one of five outcomes:

| Outcome | When | What happens |
| --- | --- | --- |
| PASS | the head satisfies the seal in force | mergeable (once the other checks pass) |
| FAIL (hard) | a fixed obligation is violated (a ratchet, a leaf rule, semantic rows downstream, a package check, an admitted assertion); in steady phase also a replaced root seal, a rewritten or truncated chain, a verdict signed by an unnamed key | nothing can accept it |
| APPROVED (steady) / NO BLOCKING FINDING (construction) | boundary files changed, and the review found no blocking finding | steady: the signed verdict is posted; committing it unchanged makes the head PASS. Construction: the check passes; nothing is signed |
| REJECTED (defect) (steady) / CHANGES NEEDED (construction) | the review demonstrated a defect: requirement, code path, correction | repair it; the revision is reviewed again. Steady: signed into the `custodian/rejections` log |
| EVIDENCE NEEDED | a fact or argument is not established | supply it and re-run; not a rejection, nothing recorded |
| REQUIREMENT DECISION NEEDED | the change would alter a requirement, completion standard or reserved authority | the owner decides that choice (steady: an escalation verdict) |
| REVIEW NOT COMPLETED | the reviewer call failed, timed out or returned nothing usable | re-run it; no outcome was produced and nothing is recorded |

### Reconsideration

The identical change against the same seal is not reviewed again merely to obtain another answer.
It is reviewed again when it carries a substantive revision, or a pull-request comment beginning
`Custodian reconsideration:` that names new evidence, corrected context or an error in a finding,
followed by a re-run of the review job; the reviewer then sees the earlier findings and the
request, as untrusted claims to verify. Each reconsideration text reopens a rejection once. The
discussion stays in the pull request.

The reviewer decides every boundary change, wherever it is: the kernel, an upstream rule file, a
gate, a probe, an acceptance file or `custodian/` itself. A path is never evidence of a violation.
The owner is involved only for a change of requirement, completion standard or reserved
authority. A change that preserves the governing obligations may remove, narrow, replace or
relocate the control implementing them (specs/architecture.md, Policy 5).

The reviewer is a Claude Code call (`claude -p`) with no tools, no settings and no MCP servers,
authenticated with the owner's subscription (`CLAUDE_CODE_OAUTH_TOKEN`), one per batch of a large
change. It gets the prompt `custodian/review/prompt.md` and, read from the base: the owner's texts
(`specs/owner/`, `custodian/owner-intent.md`), these rules, the B0 policies and the B0 section of
the plan. It gets each changed boundary file's diff and full text, upstream rule files included,
and the unchanged helpers they name. It gets the pull request's description as the author's
explanation: a claim to verify, never authority. A review never grows a ratchet's baseline.

Escalation is the human-plus-agent review: the owner and an agent review the change together, then
the owner signs:

```
python3 scripts/ci_chain.py
just -f custodian/justfile escalate ~/.ssh/id_ed25519 "<what is accepted and why>"
```

This writes a verdict of kind `escalation` for the head; commit it. The workflow's first step
refuses a head manifest whose chain entries are not a GitHub HTTPS URL and a full commit id,
before `scripts/ci_chain.py` passes them to `git`.

`custodian/review/test_review.py` exercises the loop with the model stubbed. The
`custodian/rejections` branch and the verdict chain are append-only by construction; deleting
either only makes heads fail.

## What the orchestrator must do

1. Work from `main`, which carries `custodian/`, and change `main` only through pull requests.
2. Treat a head as accepted only if `python3 scripts/ci_chain.py` and then
   `just -f custodian/justfile verify` pass under the owner's fingerprint. "Delivered" markers,
   trailers and documents carry no acceptance.
3. Never write a verdict. Commit exactly the verdict the review posted, unchanged. Never ask a
   subagent to review in the reviewer's place, and never resubmit a rejected change unchanged
   without a reconsideration.
4. A control that blocks required work is repaired like any defect: replaced by one that enforces
   the actual obligation, through review. A requirement change goes to the owner.
5. The controller (`custodian/`) is repaired through the same review as any other boundary change.
   During construction the orchestrator writes it; it never writes a verdict or selects the phase
   of the review that judges its own change (the phase is read from `main`).

## GitHub setup

`custodian/SETUP.md` gives the commands. The loop depends on:

1. The environment `custodian-review`, which only `main` may deploy to, with two secrets:
   `CUSTODIAN_REVIEW_KEY` (the review private key) and `CLAUDE_CODE_OAUTH_TOKEN` (from
   `claude setup-token`).
2. A ruleset on `main`: pull requests only, the required status checks `Custodian review`, `seal`
   and the green `Gates` jobs with GitHub Actions as their source, pull requests up to date with
   `main`, no force push or deletion, an empty bypass list.
3. A ruleset on `custodian/rejections`: no force push or deletion, an empty bypass list.

`custodian/adversarial.sh` applies each intervention in the table above to a copy and checks the
verdict. `.github/workflows/custodian.yml` runs the verifier on every pull request and every push
to `main`. That is feedback only, because a pushed commit can edit the workflow. The anchor is a verification under the owner's
fingerprint.

## Limits (not closed by this seal; see `custodian/FINDINGS.md`)

- The reviewer is a model. It can approve a bad kernel change. What bounds the damage: only the
  kernel and the upstream rule files are reviewable, every ratchet still applies,
  every steady-phase approval is signed and attributable, and an identical change is not reviewed
  again without a reconsideration. `custodian/review/test_review.py` tests the
  loop with the model stubbed; the end-to-end pull requests in `custodian/SETUP.md` test the live
  workflow and the real model call.
- The loop rests on the one-time setup above. Without the `main` ruleset and the environment's
  branch restriction, the orchestrator can merge without review, or run another branch's workflow
  with the review key.

- Author identity. `Agent-Role`/`Agent-Id` trailers, `AGENT_ROLE=acceptance` and module-root checks
  are self-declared. The seal does not rely on them. The formalization → tests → implementation
  separation is not enforced by anything the orchestrator cannot forge, because every subagent is
  spawned by the orchestrator.
- The sealed baseline includes everything that existed at `0ba53dab`. Integrity is not provenance:
  the existing assertions are frozen, not certified independent.
- The sealed rule files keep their known defects (`FINDINGS.md`). Fixing them is a reviewed
  change.
- Only the rule files are sealed. The rest of each upstream package moves with `main`
  unreviewed: its mathematics is checked by its own repository's gates, not here.
- The checks are syntactic scans plus hashes. No Lean-level axiom audit of the chain and no Lean
  build is part of verification.
