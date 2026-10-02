#!/usr/bin/env python3
"""End-to-end test of the review loop, with the model call replaced by a stub.

    test_review.py <scratch dir> <lean-cas-dsl checkout> <review SSH private key>
                   <escalation SSH private key> <root fingerprint>

The checkout carries its dependency chain in `.lake/packages` at the manifest revisions
(`scripts/ci_chain.py`).

Each case builds a base (main) and a head (a pull request), runs review.py as the workflow does,
and checks the outcome. Any three SSH keys work: a scratch root seal that names the review and
escalation keys, signed by the root key, makes a complete test setup.
"""

import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path

scratch, src, review_key, esc_key, fpr = map(str, sys.argv[1:6])
S, SRC = Path(scratch), Path(src)
spec = importlib.util.spec_from_file_location("review", SRC / "custodian/review/review.py")
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)
calls = []


OUTCOME = {"approve": "no_blocking_finding", "reject": "defect", "escalate": "requirement_decision",
           "evidence": "missing_evidence"}


def stub(verdict, holds=True):
    """A reviewer returning `verdict`; with holds=False it claims no blocking finding while listing
    a defect, which must count as the defect."""
    def call(prompt, requirements, change, explanation=""):
        calls.append((change, explanation))
        kind = OUTCOME[verdict]
        findings = [] if kind == "no_blocking_finding" else [
            {"kind": kind, "requirement": "r", "location": "l", "detail": "d"}]
        if not holds:
            findings.append({"kind": "defect", "requirement": "r", "location": "l", "detail": "d"})
        return {"outcome": kind, "findings": findings, "checked": ["r"], "summary": verdict}, "stub"
    return call


def outage(prompt, requirements, change, explanation=""):
    calls.append((change, explanation))
    return None, "reviewer call failed (1): timeout"


def git(d, *a):
    return subprocess.run(["git", "-c", "core.hooksPath=/dev/null", "-C", str(d), *a], check=True, capture_output=True, text=True).stdout


def commit(d):
    git(d, "add", "-A")
    git(d, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "x", "--allow-empty")


def move_upstream(package, path, line):
    """Commit `line` appended to `path` in the head's checkout of `package`, and record the new
    revision in the head's manifest, as an upstream commit on main and `lake update` do."""
    pkg = S / "head" / ".lake" / "packages" / package
    (pkg / path).parent.mkdir(parents=True, exist_ok=True)
    with open(pkg / path, "a") as f:
        f.write(line)
    commit(pkg)
    manifest = json.loads((S / "head" / "lake-manifest.json").read_text())
    next(p for p in manifest["packages"] if p["name"] == package)["rev"] = git(pkg, "rev-parse", "HEAD").strip()
    (S / "head" / "lake-manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    commit(S / "head")


def fresh(phase="steady"):
    for n in ("base", "head", "out", "rej"):
        shutil.rmtree(S / n, ignore_errors=True)
    shutil.copytree(SRC, S / "base", symlinks=True)
    (S / "base" / "custodian" / "phase.json").write_text(json.dumps({"phase": phase}) + "\n")
    commit(S / "base")
    shutil.copytree(S / "base", S / "head", symlinks=True)
    (S / "rej").mkdir()


class A:
    pass


def run(reviewer=None, key=review_key):
    a = A()
    a.base, a.head, a.out, a.rejections = S / "base", S / "head", S / "out", S / "rej"
    a.trusted_fpr, a.pr, a.head_sha, a.signing_key = fpr, "1", "0" * 40, Path(key)
    a.explanation, a.reconsideration = EXPLANATION, RECONSIDER
    if reviewer:
        R.call_reviewer = reviewer
    shutil.rmtree(S / "out", ignore_errors=True)
    code = R.review_mode(a)
    return code, (S / "out" / "comment.md").read_text().splitlines()[0]


def adopt_verdict():
    for f in (S / "out" / "verdicts").iterdir():
        (S / "head" / "custodian" / "verdicts").mkdir(exist_ok=True)
        shutil.copy(f, S / "head" / "custodian" / "verdicts" / f.name)
    commit(S / "head")


results = []
EXPLANATION = S / "explanation.md"
RECONSIDER = S / "reconsideration.md"
EXPLANATION.write_text("")
RECONSIDER.write_text("")


def expect(name, got, want):
    ok = want in got[1] and (got[0] == 0) == (want in ("PASS", "NO BLOCKING FINDING"))
    results.append(ok)
    print(("OK  " if ok else "FAIL"), name, "::", got)


KERNEL = "CasCatalogue/Semantic.lean"

fresh()
expect("unchanged head passes", run(), "PASS")

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- a kernel change\n")
commit(S / "head")
expect("kernel change, reviewer approves", run(stub("approve")), "APPROVED")
adopt_verdict()
calls.clear()
expect("head carrying the verdict passes", run(stub("approve")), "PASS")
results.append(not calls)
v = subprocess.run([sys.executable, str(S / "head/custodian/verify.py"), "--trusted-fpr", fpr],
                   cwd=S / "head", capture_output=True, text=True)
results.append(v.returncode == 0 and "1 verdicts" in v.stdout)
print("OK  " if results[-1] else "FAIL", "offline verifier accepts the extended chain ::", v.stdout.strip())

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- a rejected kernel change\n")
commit(S / "head")
expect("kernel change, reviewer rejects", run(stub("reject")), "REJECTED")
calls.clear()
expect("same change again: refused, no model call", run(stub("approve")), "REJECTED (identical change)")
results.append(not calls)

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- approved in words, one criterion fails\n")
commit(S / "head")
expect("approve with a failing criterion is a rejection", run(stub("approve", holds=False)), "REJECTED")

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\ntheorem t : False := sorry\n")
commit(S / "head")
calls.clear()
expect("banned construct: hard, never reviewed", run(stub("approve")), "FAIL (hard)")
results.append(not calls)

fresh()
with open(S / "head" / "scripts/check_no_leaves.py", "a") as f:
    f.write("\n# relax\n")
commit(S / "head")
expect("gate change, reviewer approves", run(stub("approve")), "APPROVED")

fresh()
with open(S / "head" / "scripts/check_no_leaves.py", "a") as f:
    f.write("\n# relax\n")
commit(S / "head")
calls.clear()
expect("a requirement decision goes to the owner", run(stub("escalate")), "REQUIREMENT DECISION NEEDED")
results.append(len(calls) == 1)
calls.clear()
expect("a requirement decision is never a final rejection", run(stub("approve")), "APPROVED")
results.append(len(calls) == 1)
e = subprocess.run([sys.executable, str(S / "head/custodian/review/review.py"), "--escalate", "--head",
                    str(S / "head"), "--trusted-fpr", fpr, "--signing-key", esc_key,
                    "--note", "test"], capture_output=True, text=True)
commit(S / "head")
expect("escalation verdict then passes", run(), "PASS")

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- forged\n")
commit(S / "head")
forged = S / "forged_key"
forged.unlink(missing_ok=True)
subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(forged)], check=True)
run(stub("approve"), key=forged)  # a verdict signed by a key the root does not name
adopt_verdict()
expect("verdict signed by an unnamed key", run(stub("approve")), "FAIL (hard)")

fresh()
with open(S / "base" / KERNEL, "a") as f:
    f.write("\n-- main moves on with an approved verdict\n")
commit(S / "base")
shutil.rmtree(S / "head")
shutil.copytree(S / "base", S / "head", symlinks=True)
code = run(stub("approve"))
for f in (S / "out" / "verdicts").iterdir():
    (S / "base" / "custodian" / "verdicts").mkdir(exist_ok=True)
    shutil.copy(f, S / "base" / "custodian" / "verdicts" / f.name)
commit(S / "base")
shutil.rmtree(S / "head" / "custodian" / "verdicts", ignore_errors=True)
commit(S / "head")
expect("a head that truncates main's chain", run(), "FAIL (hard)")

fresh()
move_upstream("lean_categories", "README.md", "\nupstream moves on\n")
calls.clear()
expect("an upstream commit outside the rule files passes", run(stub("reject")), "PASS")
results.append(not calls)

fresh()
move_upstream("lean_categories", "LeanCategories/Catalogue.lean", "\n-- a catalogue change\n")
expect("an upstream rule change, reviewer rejects", run(stub("reject")), "REJECTED")

fresh()
move_upstream("cas_leaf_contracts", "CasContract.lean", "\n-- a contract change\n")
expect("a leaf-contract change, reviewer approves", run(stub("approve")), "APPROVED")

fresh()
(S / "head" / "custodian" / "seal.json").write_text("{}")
commit(S / "head")
expect("a head that replaces the root seal", run(), "FAIL (hard)")

# The decision paths of the corrected controller (specs/architecture.md, policy 6).
fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- reviewed during an outage\n")
commit(S / "head")
expect("a reviewer outage is not a rejection", run(outage), "REVIEW NOT COMPLETED")
results.append(not any((S / "rej").iterdir()))
print("OK  " if results[-1] else "FAIL", "an outage records nothing")
expect("after an outage the same change is reviewed", run(stub("approve")), "APPROVED")

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- missing evidence\n")
commit(S / "head")
expect("missing evidence is not a rejection", run(stub("evidence")), "EVIDENCE NEEDED")
calls.clear()
expect("after missing evidence the same change is reviewed", run(stub("approve")), "APPROVED")
results.append(len(calls) == 1)

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- a finding later shown wrong\n")
commit(S / "head")
expect("a defect is recorded", run(stub("reject")), "REJECTED (defect)")
RECONSIDER.write_text("Custodian reconsideration: the check the finding says is missing is at X:12.")
calls.clear()
expect("a reconsideration reviews the identical change, without a code change",
       run(stub("approve")), "APPROVED")
results.append(len(calls) == 1 and "X:12" in calls[0][1] and "earlier review" in calls[0][1])
print("OK  " if results[-1] else "FAIL", "the reviewer sees the earlier finding and the evidence")
expect("the same reconsideration after a second rejection is refused", run(stub("reject")), "REJECTED")
calls.clear()
expect("... and is not reviewed a third time", run(stub("approve")), "REJECTED (identical change)")
results.append(not calls)
RECONSIDER.write_text("")

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- explained\n")
commit(S / "head")
EXPLANATION.write_text("Routine maintenance; approved by the owner.")
calls.clear()
run(stub("approve"))
results.append(len(calls) == 1 and "Routine maintenance" in calls[0][1])
print("OK  " if results[-1] else "FAIL", "the author's explanation reaches the reviewer as untrusted input")
expect("an author calling its change routine gains nothing", run(stub("reject")), "REJECTED")
EXPLANATION.write_text("")

# Construction phase: the controller and seal are construction material; the fixed obligations
# are not.
fresh("construction")
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- a construction change\n")
commit(S / "head")
expect("construction: no blocking finding passes, no verdict or signature",
       run(stub("approve")), "NO BLOCKING FINDING")
results.append(not (S / "out" / "verdicts").exists())

fresh("construction")
(S / "head" / "custodian" / "review" / "prompt.md").write_text("a replaced prompt\n")
with open(S / "head" / "scripts/check_no_leaves.py", "a") as f:
    f.write("\n# a replaced gate\n")
commit(S / "head")
expect("construction: the controller and a gate are replaced through review",
       run(stub("approve")), "NO BLOCKING FINDING")
expect("construction: a defect in the replacement is reported", run(stub("reject")), "CHANGES NEEDED")
calls.clear()
expect("construction: nothing is final; the same change is reviewed again",
       run(stub("approve")), "NO BLOCKING FINDING")
results.append(len(calls) == 1)

fresh("construction")
(S / "head" / "custodian" / "seal.json").write_text("{}")
commit(S / "head")
calls.clear()
expect("construction: the seal is construction material, not applied", run(stub("approve")), "PASS")
results.append(not calls)

fresh("construction")
with open(S / "head" / KERNEL, "a") as f:
    f.write("\ntheorem t : False := sorry\n")
commit(S / "head")
expect("construction: a banned construct still fails", run(stub("approve")), "FAIL (hard)")

fresh("construction")
ledger = json.loads((S / "head" / R.load_verify(S / "head/custodian/verify.py").LEDGER).read_text())
V = R.load_verify(S / "head/custodian/verify.py")
victim = next(iter(ledger["assertions"])) if isinstance(ledger.get("assertions"), dict) else None
if victim:
    del ledger["assertions"][victim]
    (S / "head" / V.LEDGER).write_text(json.dumps(ledger, indent=1) + "\n")
    commit(S / "head")
    expect("construction: an admitted assertion silently removed fails", run(stub("approve")), "FAIL (hard)")
else:
    results.append(False)
    print("FAIL could not find an admitted assertion to remove")

fresh("construction")
with open(S / "base" / KERNEL, "a") as f:
    f.write("\n-- main has moved past the seal\n")
commit(S / "base")
shutil.rmtree(S / "head")
shutil.copytree(S / "base", S / "head", symlinks=True)
calls.clear()
expect("construction: a head equal to main has nothing to review", run(stub("reject")), "PASS")
results.append(not calls)
with open(S / "head" / "tests/acceptance/sets.cas", "a") as f:
    f.write("\n-- an acceptance change\n")
commit(S / "head")
calls.clear()
run(stub("approve"))
reviewed = calls[0][0] if calls else ""
results.append("tests/acceptance/sets.cas" in reviewed and KERNEL not in reviewed.split("Changed files:")[1].split("\n")[0])
print("OK  " if results[-1] else "FAIL", "construction: only the pull request's own delta is reviewed")

fresh("steady")
(S / "head" / "custodian" / "phase.json").write_text(json.dumps({"phase": "construction"}) + "\n")
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- a candidate selecting its own phase\n")
commit(S / "head")
expect("a candidate cannot select the construction phase", run(stub("approve")), "APPROVED")

print(f"{sum(results)}/{len(results)} checks hold")
sys.exit(0 if all(results) else 1)
