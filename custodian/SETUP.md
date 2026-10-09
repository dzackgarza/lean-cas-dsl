# Deploying the protected custodian loop

Construction `main` remains an ordinary integration branch. The following configuration
is reviewable source and must be independently reviewed before deployment. Deployment
is an external authority operation, distinct from the already authorized construction.
The operator must supply the real independent assignment and reviewer public identity;
examples are not credentials or accepted releases. Never print or commit private keys.

1. Independently assess the controller and judging source, then bootstrap its reviewed
   immutable revision as `accepted/controller`. Bootstrap separately reviewed mathematics,
   contract, acceptance and public metadata releases as protected accepted references in
   their respective repositories. Do not mark a construction candidate accepted merely
   because an engineering check passes. `deployment.example.json` identifies retained
   construction inputs; replace its placeholders with independently admitted identities.
2. Commit `custodian/deployment.json` on the controller release with fixed repository URLs,
   immutable input revisions, independently supplied assignment, public reviewer key and
   fingerprint, isolated author checkout, and the existing signed review history branch.
   External public metadata additionally needs the immutable file, full digest and exact
   mathematics/contract provenance. Provision that file in the protected deployment; an
   unsigned construction export is not an accepted public release.
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
   reviews one complete request, signs its actual judgment, and records it in the existing
   discussion branch. Download the `custodian-independent-assessment` artifact and verify the signature.
   A missing credential, invocation failure or blocking finding cannot advance inputs.
6. Run `publish_assessment.py --configuration ... --request ... --decision ... --signature ...
   --deployment-repository ...` to inspect the exact publication plan. After applicable
   authorization, add `--publish` to open its conventional PR against `accepted/controller`.
   Independent protected review and merge admit the configuration. Never direct-push an
   accepted configuration or treat a subagent's technical finding as a signing credential.
7. Launch a fresh author with `launch_author.py --configuration ...`. Confirm the tool list
   is only its assigned MCP operations and validation, then exercise source write/read and
   immutable submission. Run source checks and the existing 70 fixtures before deployment;
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
