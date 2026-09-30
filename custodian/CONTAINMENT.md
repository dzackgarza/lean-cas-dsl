# Containment of the orchestrator (custodian, branch `custodian/containment`)

Written by the custodian session `session_01GTQeWD4KCqYCeVd4SygciY` on 2026-09-30. This file is
inside the sealed boundary: a copy with different bytes is not this file.

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
   `scripts/check_*.py`, CI), the harness and audits (`CasTools`), the build definition
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
   - no new `sorry`, `admit`, `axiom`, `partial def`, `unsafe`, `implemented_by`, `extern`,
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
| Edit, delete, or add to the gates, their exemption markers or allowlists, CI, `justfile`, `lakefile.lean` | sealed bytes |
| Change the kernel, evaluator, `#accept` meaning, harness or axiom audit, and call it accepted | sealed bytes |
| Edit or delete an admitted assertion, or rewrite `admitted.json` | sealed bytes and sealed ledger |
| Use the `--correct` path to rewrite assertions | sealed ledger |
| Change, add, remove or rename an upstream rule file: new admission rules, a relaxed contract | sealed bytes of the rule files |
| Build against a dev-linked working tree, or a package not at its manifest revision (`pin_dev.py`) | package check |
| Ship a leaf or a probe leaf in lean-cas-dsl | leaf check |
| Write semantic rows downstream (`LeanCategories.*` module, `normalized_registry`) | outside-boundary check |
| Redefine `#accept` or any syntax from a leaf, or from an unsealed file here | syntax ratchet |
| Make an example pass with `sorry`, an axiom, `native_decide`, `implemented_by`, or `partial` | banned-construct ratchet |
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
| FAIL (hard) | a ratchet or structural violation, a package that fails the package check, a replaced root seal, a rewritten or truncated chain, a verdict signed by an unnamed key | nothing can accept it |
| ESCALATE | the change touches what judges changes: `custodian/`, CI, the owner's text, existing acceptance assertions, the ledger, gates, harness, build definition | an escalation verdict is required |
| APPROVED | only the kernel (`CasCatalogue`, `CasDsl`) or an upstream rule file changed, and the reviewer approved | the signed verdict is posted on the pull request; committing it unchanged makes the head PASS |
| REJECTED | the reviewer rejected, refused, or could not review (too large: split it) | signed and appended to the `custodian/rejections` log; the same change against the same seal is never reviewed again |

The reviewer is a single Claude Code call (`claude -p`) with no tools, no settings and no MCP
servers, authenticated with the owner's subscription (`CLAUDE_CODE_OAUTH_TOKEN`). It gets the
fixed prompt `custodian/review/prompt.md`, the owner's text, these rules and the diff of every
changed sealed file, upstream rule files included. It never gets the orchestrator's description
or argument. It approves only if every criterion holds, and a review never grows a ratchet's
baseline.

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

1. Merge `custodian/containment` into every branch it works on, and change `main` only through
   pull requests.
2. Treat a head as accepted only if `python3 scripts/ci_chain.py` and then
   `just -f custodian/justfile verify` pass under the owner's fingerprint. "Delivered" markers,
   trailers and documents carry no acceptance.
3. Never write a verdict. Commit exactly the verdict the review posted, unchanged. Never ask a
   subagent to review in the reviewer's place, and never resubmit a rejected change unchanged.
4. When an obligation looks inconsistent or unsolvable, say so in a pull request that names it. Do
   not weaken it. That pull request escalates by construction.
5. Never write under `custodian/`, except to commit a verdict the review posted.

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
verdict. `.github/workflows/custodian.yml` runs the verifier on every push. That is feedback only,
because a pushed commit can edit the workflow. The anchor is a verification under the owner's
fingerprint.

## Limits (not closed by this seal; see `custodian/FINDINGS.md`)

- The reviewer is a model. It can approve a bad kernel change. What bounds the damage: only the
  kernel and the upstream rule files are reviewable, every ratchet still applies,
  every approval is signed and attributable, and a rejection is final. `custodian/review/test_review.py` tests the
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
