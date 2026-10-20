# Deploying the protected custodian loop

Construction `main` remains an ordinary integration branch. The following configuration
is reviewable source and must be independently reviewed before deployment. Deployment
is an external authority operation, distinct from the already authorized construction.
The operator must supply the real independent assignment and reviewer public identity;
examples are not credentials or accepted releases. Never print or commit private keys.

1. Independently assess the controller and judging source, then bootstrap its reviewed
   immutable revision as `accepted/controller`. Keep acceptance/judging source, governing
   requirements and public metadata under their existing independent protection. Mathematics,
   contract, leaves and notebook source dependencies are consumed from their latest `main`
   at each build, harness or author invocation, without separate accepted dependency releases
   or re-pin transactions. Do not mark a construction candidate accepted merely because an
   engineering check passes. `deployment.example.json` identifies construction inputs;
   replace protected authority placeholders with independently admitted identities.
2. Commit `custodian/deployment.json` on the controller release with fixed repository URLs,
   fixed requirements/judging revisions, independently supplied assignment, public reviewer
   key and fingerprint, isolated author checkout, and existing signed review history branch.
   Source dependency commits record reproducibility snapshots; the resolver fetches current
   `main` from the configured trusted URL or protected input origin before consumption.
   Both committed and external public metadata need a full content digest and exact
   mathematics AND contract provenance. Provision the independently fixed artifact in the
   protected deployment. If either source main has advanced beyond that provenance, only
   consumers of that artifact stop; do not relabel it or regenerate it from a candidate.
   An unsigned construction export is not an accepted public release.
3. Apply the reviewed `accepted-ruleset.json` in each applicable repository. Its `accepted/**`
   scope requires independent PR review and the trusted `Custodian review` check, with no
   bypass actors, deletion or force pushes. Provision independent CODEOWNERS before using
   its code-owner requirement. Ensure the named GitHub Actions check is actually emitted
   on the protected publication PR. Do not apply accepted-reference rules to construction
   main or treat its existing deletion/non-fast-forward protection as admission.
4. Configure `custodian-review` with `reviewer-environment.json`. Its custom deployment
   policy must permit only `accepted/controller`: remove the existing `main` policy and
   add `reviewer-branch-policy.json`. Keep `CUSTODIAN_REVIEW_KEY` and
   `CLAUDE_CODE_OAUTH_TOKEN` only in that environment. Verify the installed public signing
   fingerprint against independently supplied authority. Preserve owner/root/escalation
   keys under the existing seal protocol; author launchers receive none of these keys.
5. Dispatch `custodian-authority.yml` at `accepted/controller` for a full candidate commit.
   The trusted workflow materializes Git objects without checking out candidate programs,
   resolves the full source dependency tuple, reviews one complete request, signs its actual
   judgment, and records it in the existing discussion branch. Retain its
   `resolved-configuration.json` and request as the exact reproducibility snapshot. Download the `custodian-independent-assessment` artifact and verify the signature.
   A missing credential, invocation failure or blocking finding cannot advance inputs.
6. Run `publish_assessment.py --configuration ... --request ... --decision ... --signature ...
   --deployment-repository ...` to inspect the exact publication plan. After applicable
   authorization, add `--publish` to open its conventional PR against `accepted/controller`.
   Independent protected review and merge admit changes to the protected configuration;
   source dependency resolution itself needs no such transaction. Signed request replay
   uses the captured source commits without refetching or changing protected judging inputs.
   Never direct-push an accepted configuration or treat a subagent's technical finding as
   a signing credential.
7. Launch a fresh author with `launch_author.py --configuration ...`. Confirm the tool list
   is only its assigned MCP operations and validation. Capture the permitted-input revision
   snapshot on the role server's stderr. The launcher resolves only that role's input
   dependencies; checking public metadata also resolves its mathematics/contract provenance
   sources without exposing mathematical source to a leaf author. Then exercise source write/read and
   immutable submission. Run source checks and the existing 79 fixtures before deployment;
   run genuine independently assessed acceptance with the fixed denominator separately.

Read-only observations on 2026-10-02: DSL main ruleset 24252144 has deletion and
non-fast-forward protection, empty bypass and no mandatory review/checks; upstream main
has no applied rules; accepted refs are absent. Review environment branch policy 61535459
currently permits main. Local GH_TOKEN is present, but local review SSH/OAuth credentials
are absent. Remote environment secret-name listing returned HTTP 403, so remote secret
absence is not inferred. No protection, secret, reference or publication write was made
as part of these observations.

The protected GitHub API payloads are `accepted-ruleset.json`,
`reviewer-environment.json` and `reviewer-branch-policy.json`. Creating accepted refs,
applying those payloads, replacing policy 61535459, provisioning the actual signing and
inference identities and merging independently assessed releases remain deployment
operations. These facts do not prevent completing and reviewing the local controller source.

The reviewed protection payloads have these exact API destinations (operator substitutes
only the independently approved repository when applying the accepted-reference rule):

```sh
gh api --method POST repos/dzackgarza/lean-cas-dsl/rulesets --input custodian/accepted-ruleset.json
gh api --method PUT repos/dzackgarza/lean-cas-dsl/environments/custodian-review --input custodian/reviewer-environment.json
gh api --method DELETE repos/dzackgarza/lean-cas-dsl/environments/custodian-review/deployment-branch-policies/61535459
gh api --method POST repos/dzackgarza/lean-cas-dsl/environments/custodian-review/deployment-branch-policies --input custodian/reviewer-branch-policy.json
```

These are authority writes, not steps performed by source tests. Before applying them,
inspect the current API response again and confirm the independently reviewed controller
revision, CODEOWNERS and required check are provisioned. Bootstrap accepted refs only to
those independently reviewed full revision IDs; no source author may choose its own
accepted status. The actual secret inputs must be provisioned without values appearing
in command output or review artifacts. Dispatch uses the protected controller revision:

```sh
gh workflow run custodian-authority.yml --ref accepted/controller -f candidate=<independently-authored-full-commit>
```

The uploaded artifact is named `custodian-independent-assessment`.
