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

## What the orchestrator must do

0. Merge `custodian/containment` into every branch it works on. A branch without the sealed
   `custodian/` files fails verification.
1. Run the verifier on every head it calls accepted, delivered or done. A head that does not verify
   under the owner's fingerprint is not accepted, whatever any plan, trailer or document says.
   "Delivered" markers in the plan carry no acceptance.
2. Put every change to the boundary on a branch named `proposal/<name>`. Such a branch fails
   verification by construction, and that is correct: it is a proposal. Only a new seal signed by a
   key the owner trusts accepts it. The orchestrator never signs a seal, never asks a subagent it
   spawned to sign one, and never presents a seal signed by any other key as accepted.
3. When an obligation looks inconsistent or unsolvable under the sealed boundary, say so in a
   `proposal/` branch that names the obligation. Do not weaken it.
4. Never write under `custodian/`, on any branch.

`custodian/adversarial.sh` applies each intervention in the table to a copy and checks the verdict.
`.github/workflows/custodian.yml` runs the verifier in CI. That is feedback only: a pushed commit
can edit the workflow. The anchor is the owner's own run.

## How a seal is renewed (owner, or a custodian the owner names)

```
python3 custodian/verify.py --make-seal --leaves <leaves checkout> --seal custodian/seal.json \
    --note "<what is accepted and why>"
git diff custodian/seal.json      # review every changed hash: each one is a change to the judges
openssl pkeyutl -sign -inkey <private key> -rawin -in custodian/seal.json -out custodian/seal.json.sig
```

Then verify with the new key's fingerprint, held outside the repositories.

## Limits (not closed by this seal; see `custodian/FINDINGS.md`)

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
