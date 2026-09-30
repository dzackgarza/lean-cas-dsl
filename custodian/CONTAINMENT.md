# Containment of the orchestrator (custodian, branch `custodian/containment`)

Written by the custodian session `session_01GTQeWD4KCqYCeVd4SygciY` on 2026-09-30. This file is
inside the sealed boundary: a copy with different bytes is not this file.

## Trust anchor

The seal `custodian/seal.json` is signed (`custodian/seal.json.sig`, Ed25519, OpenSSL) with a
private key generated in the custodian's container and never written to any repository. When that
session ends, the key no longer exists. Nobody, including the custodian, can sign another seal
under it.

The public key's fingerprint (sha256 of its DER encoding) was given to the owner in the custodian
session, outside every repository:

    b0f8f4da4efc1fbe8da4e89568200c277edf1b1c01f48346c166dee45ec6d5f4

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
2. **Every dependency pin except `cas_leaves`**. That covers `lean_categories` (semantic-release
   admission and all accepted mathematics), `cas_leaf_contracts` (the leaf contract), `mathlib`
   and `nbdsl-worker`.
3. **The admission ledger** `CasAcceptance/Permanent/admitted.json`. It may only grow: sealed
   assertion hashes, `corrections` and `lean_categories` never change.
4. **Ratchets that only tighten**, each with a baseline in the seal:
   - no new `sorry`, `admit`, `axiom`, `partial def`, `unsafe`, `implemented_by`, `extern`,
     `panic!`, `unreachable!`, `native_decide` or `ofReduceBool` anywhere in lean-cas-dsl;
   - outside the boundary, no syntax, elaborator, macro, `initialize` or global attribute, and no
     semantic registration or `LeanCategories/` module;
   - no leaf in lean-cas-dsl;
   - leaves (at the `cas_leaves` pin) are subject to all of the above, and may also not define
     syntax or elaborators, import the kernel or the tests, read `tests/acceptance`, register
     semantic rows, place modules outside `CasLeaves/`, or require lean-cas-dsl.

## Interventions that are now detectably invalid

With `python3 custodian/verify.py --trusted-fpr <owner's copy> --leaves <leaves checkout>`, each of
the following fails verification:

| Intervention | Why it fails |
| --- | --- |
| Edit, delete, or add to the gates, their exemption markers or allowlists, CI, `justfile`, `lakefile.lean` | sealed bytes |
| Change the kernel, evaluator, `#accept` meaning, harness or axiom audit, and call it accepted | sealed bytes |
| Edit or delete an admitted assertion, or rewrite `admitted.json` | sealed bytes and sealed ledger |
| Use the `--correct` path (re-pin lean-categories, then rewrite assertions) | the pin is sealed |
| Re-pin `lean_categories` or `cas_leaf_contracts`: new admission rules, new or changed mathematics, a relaxed contract | sealed pins |
| Build against a dev-linked working tree instead of the pin (`pin_dev.py`) | `.lake/packages` is checked against the pin |
| Ship a leaf or a probe leaf in lean-cas-dsl | leaf check |
| Write semantic rows downstream (`LeanCategories.*` module, `normalized_registry`) | outside-boundary check |
| Redefine `#accept` or any syntax from a leaf, or from an unsealed file here | syntax ratchet |
| Make an example pass with `sorry`, an axiom, `native_decide`, `implemented_by`, or `partial` | banned-construct ratchet |
| Let a leaf see the tests or the kernel | leaf import and read checks |
| Edit the owner's text | sealed bytes |

A failing example can turn green on a verifying head only through what stays free: a leaf at a new
`cas_leaves` pin, judged by the sealed contract, kernel and suite; and files outside the boundary,
which cannot define syntax.

## The acceptance loop (closed, agent-driven)

The seal in force is the root seal, extended by a chain of signed verdicts in
`custodian/verdicts/NNNNNN.json`. Each verdict names the sha256 of its predecessor and carries the
next seal. The root seal names the only keys that may extend the chain:

- **review key** (fingerprint `bcd85dd2c758b032057211636734a2407fe275d32ef2e76df9d8c60cae80dd79`),
  held only in the `custodian-review` GitHub environment;
- **escalation key** (fingerprint `77bbd8a24c41b333f496cf5c638456f4a85908916202b1e62d48a62ad1bb9508`),
  held only by the owner.

A change reaches `main` only through a pull request, and `.github/workflows/custodian-review.yml`
judges each one. That workflow runs on `pull_request_target`, so its code is `main`'s, and it only
reads the pull request's head. It gives one of five outcomes:

| Outcome | When | What happens |
| --- | --- | --- |
| PASS | the head satisfies the seal in force | mergeable (once the other checks pass) |
| FAIL (hard) | a ratchet or structural violation, a replaced root seal, a rewritten or truncated chain, a verdict signed by an unnamed key | nothing can accept it |
| ESCALATE | the change touches what judges changes: `custodian/`, CI, the owner's text, existing acceptance assertions, the ledger, gates, harness, build definition | an escalation verdict is required |
| APPROVED | only the kernel (`CasCatalogue`, `CasDsl`) or the `lean_categories` / `cas_leaf_contracts` pins changed, and the reviewer approved | the signed verdict is posted on the pull request; committing it unchanged makes the head PASS |
| REJECTED | the reviewer rejected, refused, or could not review (too large: split it) | signed and appended to the `custodian/rejections` log; the same change against the same seal is never reviewed again |

The reviewer is a single model call. It gets the fixed prompt `custodian/review/prompt.md`, the
owner's text, these rules and the diff (plus the upstream diff for a moved pin). It never gets the
orchestrator's description or argument. It approves only if every criterion holds, and a review
never grows a ratchet's baseline.

Escalation is the human-plus-agent review: the owner and an agent review the change together, then
the owner signs:

```
just -f custodian/justfile escalate <leaves checkout> <escalation key> "<what is accepted and why>"
```

This commits a verdict of kind `escalation` to the head.

`custodian/review/test_review.py` exercises the loop with the model stubbed. The
`custodian/rejections` branch and the verdict chain are append-only by construction; deleting
either only makes heads fail.

## What the orchestrator must do

1. Merge `custodian/containment` into every branch it works on, and change `main` only through
   pull requests.
2. Treat a head as accepted only if `just -f custodian/justfile verify <leaves>` passes under the
   owner's fingerprint. "Delivered" markers, trailers and documents carry no acceptance.
3. Never write a verdict. Commit exactly the verdict the review posted, unchanged. Never ask a
   subagent to review in the reviewer's place, and never resubmit a rejected change unchanged.
4. When an obligation looks inconsistent or unsolvable, say so in a pull request that names it. Do
   not weaken it. That pull request escalates by construction.
5. Never write under `custodian/`, except to commit a verdict the review posted.

## One-time setup (owner, in the GitHub UI)

1. Merge `custodian/containment` into `main`.
2. Create the environment `custodian-review` (Settings → Environments). Restrict deployment
   branches to `main`. Add two secrets: `ANTHROPIC_API_KEY`, and `CUSTODIAN_REVIEW_KEY` (the
   review private key, delivered to the owner by the custodian session).
3. Add a ruleset for `main`: require a pull request, and require the status checks
   `Custodian review`, `Custodian seal / seal` and the `Gates` jobs, with GitHub Actions as their
   source. Block force pushes and deletions. Leave the bypass list empty.
4. Add a ruleset for `custodian/rejections`: block force pushes and deletions, with an empty bypass
   list.
5. Keep the escalation private key off every repository and every agent session.

`custodian/adversarial.sh` applies each intervention in the table above to a copy and checks the
verdict. `.github/workflows/custodian.yml` runs the verifier on every push. That is feedback only,
because a pushed commit can edit the workflow. The anchor is a verification under the owner's
fingerprint.

## Limits (not closed by this seal; see `custodian/FINDINGS.md`)

- The reviewer is a model. It can approve a bad kernel change. What bounds the damage: only the
  kernel and the two semantic pins are reviewable, every ratchet still applies, every approval is
  signed and attributable, and a rejection is final. The live workflow and the real model call were
  not run in the custodian session (no API key, no GitHub settings access). Only the stubbed loop
  was tested.
- The loop rests on the one-time setup above. Without the `main` ruleset and the environment's
  branch restriction, the orchestrator can merge without review, or run another branch's workflow
  with the review key.

- Author identity. `Agent-Role`/`Agent-Id` trailers, `AGENT_ROLE=acceptance` and module-root checks
  are self-declared. The seal does not rely on them. The formalization → tests → implementation
  separation is not enforced by anything the orchestrator cannot forge, because every subagent is
  spawned by the orchestrator.
- The sealed baseline includes everything that existed at `0ba53dab`. Integrity is not provenance:
  the existing assertions are frozen, not certified independent.
- The pinned `lean_categories` and `cas_leaf_contracts` revisions are frozen with their known
  defects (`FINDINGS.md`). Fixing them is a proposal that needs a new seal.
- The checks are syntactic scans plus hashes. A Lean-level axiom audit of the leaves at the pin was
  not run in this session. No Lean build was performed.
