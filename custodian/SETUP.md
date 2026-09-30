# Setting up the custodian acceptance loop

This file gives the commands that put in place the loop of `custodian/CONTAINMENT.md` for
`dzackgarza/lean-cas-dsl`. The owner, or an agent on the owner's machine, runs them with the
owner's GitHub credentials. The orchestrator runs on cloud machines and must never run them.

Three keys and one token take part:

| Item | What it is | Where it lives |
| --- | --- | --- |
| root and escalation key | the owner's SSH key (`~/.ssh/id_ed25519`) | the owner's machine; public half in `custodian/root.pub` |
| review key | an SSH key made only for the reviewer | the secret `CUSTODIAN_REVIEW_KEY` of the `custodian-review` environment; public half in the seal |
| reviewer token | `claude setup-token` output (the owner's subscription) | the secret `CLAUDE_CODE_OAUTH_TOKEN` of the same environment |

Never print, paste, commit or log a private key or the token.

## 1. The review environment, restricted to `main`

```
jq -n '{deployment_branch_policy: {protected_branches: false, custom_branch_policies: true}}' > env.json
gh api -X PUT repos/dzackgarza/lean-cas-dsl/environments/custodian-review --input env.json
gh api -X POST repos/dzackgarza/lean-cas-dsl/environments/custodian-review/deployment-branch-policies \
    -f name=main -f type=branch
```

## 2. The review key and the reviewer token

Make the review key in a private scratch directory, store the private half as the secret, and keep
only the public half:

```
ssh-keygen -q -t ed25519 -N '' -C custodian-review -f "$SCRATCH/review_key"
gh secret set CUSTODIAN_REVIEW_KEY --env custodian-review --repo dzackgarza/lean-cas-dsl < "$SCRATCH/review_key"
trash "$SCRATCH/review_key"
```

The owner makes the token and types it into the hidden prompt:

```
claude setup-token
gh secret set CLAUDE_CODE_OAUTH_TOKEN --env custodian-review --repo dzackgarza/lean-cas-dsl
```

## 3. The root seal

`custodian/root.pub` holds the owner's public key, and its fingerprint is the `root` of
`custodian/justfile` and the `--trusted-fpr` of both custodian workflows. Seal the committed state,
sign the seal with the owner's key, and commit both files:

```
python3 scripts/ci_chain.py
python3 custodian/verify.py --make-seal \
    --reviewer-key "$SCRATCH/review_key.pub" --escalation-key custodian/root.pub --note "<note>"
ssh-keygen -Y sign -f ~/.ssh/id_ed25519 -n lean-cas-custodian custodian/seal.json
just -f custodian/justfile verify
```

## 4. Rulesets

`main`: pull requests only; required checks `Custodian review`, `seal` and every `Gates` job that
is green on `main`, each with `integration_id` 15368 (GitHub Actions); pull requests up to date
with `main`; no force push or deletion; an empty bypass list.

```
gh api -X POST repos/dzackgarza/lean-cas-dsl/rulesets --input main-ruleset.json
gh api -X POST repos/dzackgarza/lean-cas-dsl/rulesets --input rejections-ruleset.json
gh api repos/dzackgarza/lean-cas-dsl/rules/branches/main --jq '.[].type'
```

`custodian/rejections`: no force push or deletion, an empty bypass list.

## 5. End-to-end checks

Each reviewed pull request makes one reviewer call on the owner's subscription. Open each pull
request against `main`, read the `Custodian review` comment, then close it and delete its branch.

| Pull request | Expected comment |
| --- | --- |
| add `theorem custodianTestFalse : False := sorry` to `CasCatalogue/Semantic.lean` | `FAIL (hard)`, naming `banned construct` |
| add a comment line to `CasCatalogue/Semantic.lean` | `APPROVED` or `REJECTED`; a rejection adds a commit to `custodian/rejections` |

For an `APPROVED` result, download the verdict (`gh run download <run-id> -n custodian-verdict`)
and check it offline with `custodian/verify.py`. Never merge a test.
