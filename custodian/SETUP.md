# Setting up the custodian acceptance loop (instructions for a local agent)

You are an agent running on the owner's machine with the owner's GitHub credentials. Your task is
to put in place the acceptance loop described in `custodian/CONTAINMENT.md` for
`dzackgarza/lean-cas-dsl`. Follow the steps in order. Stop and report at the first step whose check
fails. Do not work around a failure, and do not weaken any setting to get past it.

Four rules hold throughout:

- **Secrets.** Never print, paste, echo, cat or log the contents of a private key or API key. Never
  commit one. Pass them to commands only by file redirection or an interactive prompt.
- **The escalation key.** Never open, read, copy or move the escalation private key. Only the owner
  handles it (step 9).
- **Owner steps.** A step marked OWNER is done by the owner. You wait, then run its check.
- **Irreversible actions.** Step 3 rewrites the default branch. Do it only after the owner confirms
  in the same conversation, after you have shown them the step 2 report.

## 0. Prerequisites

```
gh auth status                  # logged in as dzackgarza, with the repo and admin:org/admin scopes
git --version
python3 --version               # 3.10 or later
openssl version                 # OpenSSL 3
gh api repos/dzackgarza/lean-cas-dsl --jq .permissions.admin      # must print true
```

Check: every command succeeds, and the last prints `true`. If the last does not, the settings
steps below are impossible with these credentials. Stop.

## 1. Fetch and check the trust root

```
WORK=$(mktemp -d) && cd "$WORK"
git clone https://github.com/dzackgarza/lean-cas-dsl && cd lean-cas-dsl
git fetch origin main claude/gallant-mccarthy-oglg4j custodian/containment
git checkout -q origin/custodian/containment
openssl pkey -pubin -in custodian/custodian.pub.pem -outform DER | sha256sum
openssl pkeyutl -verify -pubin -inkey custodian/custodian.pub.pem -rawin \
    -in custodian/seal.json -sigfile custodian/seal.json.sig
```

Check:

1. The fingerprint equals the one the owner holds from the custodian session:
   `b0f8f4da4efc1fbe8da4e89568200c277edf1b1c01f48346c166dee45ec6d5f4`. Ask the owner to confirm it
   from their own copy. The copy in this file does not count, because anyone who can push can
   edit this file.
2. OpenSSL prints `Signature Verified Successfully`.
3. `sha256sum custodian/verify.py` equals the `verifier_sha256` field of `custodian/seal.json`.

## 2. Prepare the new `main` (no changes pushed yet)

`main` currently holds an earlier prototype whose history is unrelated to the current work. The
current work is on `claude/gallant-mccarthy-oglg4j`.

```
git checkout -q -b new-main origin/claude/gallant-mccarthy-oglg4j
git merge --no-edit origin/custodian/containment       # must merge without conflicts
rev=$(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='cas_leaves'][0])")
git clone -q https://github.com/dzackgarza/lean-cas-dsl-leaves "$WORK/leaves"
git -C "$WORK/leaves" checkout -q "$rev"
python3 custodian/verify.py --trusted-fpr b0f8f4da4efc1fbe8da4e89568200c277edf1b1c01f48346c166dee45ec6d5f4 \
    --leaves "$WORK/leaves"
git log --oneline -1 origin/main
git log --oneline -1 new-main
```

Check: the merge has no conflicts, and the verifier prints `seal holds: … 0 verdicts after the root`.

Report to the owner:

- the current `origin/main` commit, and that it will be kept as the tag
  `archive/main-before-custodian`;
- the `new-main` commit that will become `main`.

Ask for explicit confirmation to replace `main`. Without it, stop here.

## 3. Replace `main` (after the owner confirms)

```
git tag archive/main-before-custodian origin/main
git push origin archive/main-before-custodian
git push --force-with-lease=main:$(git rev-parse origin/main) origin new-main:main
gh api repos/dzackgarza/lean-cas-dsl --jq .default_branch          # must print main
```

Check: `git ls-remote origin main` shows the `new-main` commit, and the tag exists on the remote.

## 4. Create the review environment, restricted to `main`

```
gh api -X PUT repos/dzackgarza/lean-cas-dsl/environments/custodian-review --input - <<'JSON'
{"deployment_branch_policy": {"protected_branches": false, "custom_branch_policies": true}}
JSON
gh api -X POST repos/dzackgarza/lean-cas-dsl/environments/custodian-review/deployment-branch-policies \
    -f name=main -f type=branch
gh api repos/dzackgarza/lean-cas-dsl/environments/custodian-review/deployment-branch-policies \
    --jq '.branch_policies[].name'
```

Check: the last command prints exactly `main`.

## 5. Store the review key (the file the custodian session delivered)

The owner saved the file `custodian-review-SECRET.pem.txt`. Ask them for its path. Do not ask for
its contents.

```
KEY=<path given by the owner>
sed -n '/-----BEGIN/,/-----END/p' "$KEY" | openssl pkey -pubout -outform DER | sha256sum
sed -n '/-----BEGIN/,/-----END/p' "$KEY" | \
    gh secret set CUSTODIAN_REVIEW_KEY --env custodian-review --repo dzackgarza/lean-cas-dsl
```

Check: the fingerprint is
`bcd85dd2c758b032057211636734a2407fe275d32ef2e76df9d8c60cae80dd79`. It must match the
`reviewer_keys` entry in `custodian/seal.json`:
`python3 -c "import json;print(list(json.load(open('custodian/seal.json'))['reviewer_keys']))"`.
Then tell the owner to delete the downloaded file.

## 6. OWNER: store the reviewer's API key

The owner runs this interactively. It prompts, with hidden input, for an Anthropic API key:

```
gh secret set ANTHROPIC_API_KEY --env custodian-review --repo dzackgarza/lean-cas-dsl
```

Check (agent):

```
gh secret list --env custodian-review --repo dzackgarza/lean-cas-dsl
```

It must list both `ANTHROPIC_API_KEY` and `CUSTODIAN_REVIEW_KEY`.

## 7. Protect `main`

Find the check names that exist on `main`:

```
gh api repos/dzackgarza/lean-cas-dsl/commits/main/check-runs --jq '.check_runs[] | "\(.name)\t\(.conclusion)"'
```

`Custodian review` runs only on pull requests, so it will not appear here. `seal` (from
`custodian.yml`) must appear with conclusion `success`. Require every check that is green on
`main`. Report any red one to the owner instead of requiring it or silencing it.

```
gh api -X POST repos/dzackgarza/lean-cas-dsl/rulesets --input - <<'JSON'
{
  "name": "custodian-main",
  "target": "branch",
  "enforcement": "active",
  "conditions": {"ref_name": {"include": ["refs/heads/main"], "exclude": []}},
  "bypass_actors": [],
  "rules": [
    {"type": "deletion"},
    {"type": "non_fast_forward"},
    {"type": "pull_request", "parameters": {
      "required_approving_review_count": 0, "dismiss_stale_reviews_on_push": false,
      "require_code_owner_review": false, "require_last_push_approval": false,
      "required_review_thread_resolution": false}},
    {"type": "required_status_checks", "parameters": {
      "strict_required_status_checks_policy": true,
      "required_status_checks": [
        {"context": "Custodian review", "integration_id": 15368},
        {"context": "seal", "integration_id": 15368}
      ]}}
  ]
}
JSON
```

Add one `{"context": "<name>", "integration_id": 15368}` entry for each other check that was green
on `main`. `15368` is GitHub Actions, so only Actions can satisfy these checks. Keep
`strict_required_status_checks_policy` true: a pull request must be up to date with `main`, so each
verdict extends the chain in force. Leave `bypass_actors` empty.

If the API rejects a field, remove only that field and retry. Report what you removed.

## 8. Protect the rejection log

```
gh api -X POST repos/dzackgarza/lean-cas-dsl/rulesets --input - <<'JSON'
{
  "name": "custodian-rejections",
  "target": "branch",
  "enforcement": "active",
  "conditions": {"ref_name": {"include": ["refs/heads/custodian/rejections"], "exclude": []}},
  "bypass_actors": [],
  "rules": [{"type": "deletion"}, {"type": "non_fast_forward"}]
}
JSON
gh api repos/dzackgarza/lean-cas-dsl/rules/branches/main --jq '.[].type'
gh api repos/dzackgarza/lean-cas-dsl/rules/branches/custodian/rejections --jq '.[].type'
```

Check: `main` lists `deletion`, `non_fast_forward`, `pull_request` and `required_status_checks`.
`custodian/rejections` lists `deletion` and `non_fast_forward`. Do not test protection by pushing
to `main`: if it were misconfigured, that push would land.

## 9. OWNER: store the escalation key

The owner saved `custodian-escalation-SECRET.pem.txt`. Encrypt it with a passphrase, keep it
outside every repository, and delete the download:

```
sed -n '/-----BEGIN/,/-----END/p' custodian-escalation-SECRET.pem.txt | \
    openssl pkey -aes256 -out ~/.lean-cas-escalation.key.pem     # prompts for a passphrase
chmod 600 ~/.lean-cas-escalation.key.pem
openssl pkey -in ~/.lean-cas-escalation.key.pem -pubout -outform DER | sha256sum
rm custodian-escalation-SECRET.pem.txt
```

Check (owner): the fingerprint is
`77bbd8a24c41b333f496cf5c638456f4a85908916202b1e62d48a62ad1bb9508`. An agent never holds the
passphrase.

## 10. End-to-end checks (these cost one or two reviewer calls)

Tell the owner that each reviewed pull request makes one API call to `claude-opus-5-5`. Proceed only
if they agree.

**a. A hard failure is refused without a review.**

```
git checkout -q -b custodian-test-hard origin/main
printf '\ntheorem custodianTestFalse : False := sorry\n' >> CasCatalogue/Semantic.lean
git commit -qam "custodian test: a banned construct (do not merge)"
git push -q origin custodian-test-hard
gh pr create --base main --head custodian-test-hard --title "custodian test: hard" --body "test"
```

Wait for the `Custodian review` run (`gh pr checks <n> --watch`). Check: the check fails, and the
comment reads `Custodian review: FAIL (hard)` and names `banned construct`. Close the pull request
and delete the branch.

**b. A kernel change is reviewed.**

```
git checkout -q -b custodian-test-review origin/main
printf '\n-- custodian test: a comment-only kernel change\n' >> CasCatalogue/Semantic.lean
git commit -qam "custodian test: comment-only kernel change (do not merge)"
git push -q origin custodian-test-review
gh pr create --base main --head custodian-test-review --title "custodian test: review" --body "test"
```

Check: the comment reads `APPROVED` or `REJECTED`. Either shows the live loop works: the environment
released both secrets, the model call succeeded, and the verdict was signed. Anything else, such as
a missing secret, an API error, or a failure to deploy to the environment, means setup is wrong.
Report it verbatim.

- If APPROVED: download the artifact (`gh run download <run-id> -n custodian-verdict`) and check it
  offline with `custodian/verify.py`. Do not merge a test.
- If REJECTED: confirm that a new commit appeared on `custodian/rejections`
  (`git ls-remote origin custodian/rejections`).

Close the pull request and delete the branch.

**c. The workflow cannot be replaced by a pull request.**

```
git checkout -q -b custodian-test-workflow origin/main
sed -i 's/--trusted-fpr [0-9a-f]*/--trusted-fpr 00/' .github/workflows/custodian-review.yml
git commit -qam "custodian test: tamper with the review workflow (do not merge)"
git push -q origin custodian-test-workflow
gh pr create --base main --head custodian-test-workflow --title "custodian test: workflow" --body "test"
```

Check: the run uses `main`'s workflow, so the fingerprint is unchanged, and the outcome is
`ESCALATE` (the pull request changed `.github/`). Close the pull request and delete the branch.

## 11. Report

Report to the owner:

- the commit now on `main`;
- the two ruleset IDs (`gh api repos/dzackgarza/lean-cas-dsl/rulesets --jq '.[] | "\(.id) \(.name)"'`);
- the required check names;
- the outcomes of 10a–10c;
- anything that failed or was skipped.

Then tell the orchestrator, in its own session or through its plan, that from now on:

- `main` changes only through pull requests;
- acceptance is the `Custodian review` check plus a verifier pass under the owner's fingerprint;
- `custodian/CONTAINMENT.md`, "What the orchestrator must do", governs.
