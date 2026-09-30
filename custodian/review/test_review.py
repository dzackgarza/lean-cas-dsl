#!/usr/bin/env python3
"""End-to-end test of the review loop, with the model call replaced by a stub.

    test_review.py <scratch dir> <lean-cas-dsl checkout> <leaves clone at the pin>
                   <review SSH private key> <escalation SSH private key> <root fingerprint>

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

scratch, src, leaves, review_key, esc_key, fpr = map(str, sys.argv[1:7])
S, SRC = Path(scratch), Path(src)
spec = importlib.util.spec_from_file_location("review", SRC / "custodian/review/review.py")
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)
calls = []


def stub(verdict, holds=True):
    def call(prompt, owner, change):
        calls.append(change)
        crit = [{"criterion": f"c{i}", "holds": holds, "evidence": "e"} for i in range(6)]
        return {"verdict": verdict, "criteria": crit, "summary": verdict}, "stub"
    return call


def git(d, *a):
    return subprocess.run(["git", "-c", "core.hooksPath=/dev/null", "-C", str(d), *a], check=True, capture_output=True, text=True).stdout


def commit(d):
    git(d, "add", "-A")
    git(d, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "x", "--allow-empty")


def fresh():
    for n in ("base", "head", "out", "rej"):
        shutil.rmtree(S / n, ignore_errors=True)
    shutil.copytree(SRC, S / "base", symlinks=True)
    commit(S / "base")
    shutil.copytree(S / "base", S / "head", symlinks=True)
    (S / "rej").mkdir()


class A:
    pass


def run(reviewer=None, key=review_key):
    a = A()
    a.base, a.head, a.leaves, a.out, a.rejections = S / "base", S / "head", Path(leaves), S / "out", S / "rej"
    a.trusted_fpr, a.pr, a.head_sha, a.signing_key = fpr, "1", "0" * 40, Path(key)
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


def expect(name, got, want):
    ok = want in got[1] and (got[0] == 0) == (want == "PASS")
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
v = subprocess.run([sys.executable, str(S / "head/custodian/verify.py"), "--trusted-fpr", fpr,
                    "--leaves", leaves], cwd=S / "head", capture_output=True, text=True)
results.append(v.returncode == 0 and "1 verdicts" in v.stdout)
print("OK  " if results[-1] else "FAIL", "offline verifier accepts the extended chain ::", v.stdout.strip())

fresh()
with open(S / "head" / KERNEL, "a") as f:
    f.write("\n-- a rejected kernel change\n")
commit(S / "head")
expect("kernel change, reviewer rejects", run(stub("reject")), "REJECTED")
calls.clear()
expect("same change again: final, no model call", run(stub("approve")), "REJECTED (final)")
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
with open(S / "head" / "scripts/check_kernel_totality.py", "a") as f:
    f.write("\n# relax\n")
commit(S / "head")
calls.clear()
expect("gate change escalates, never reviewed", run(stub("approve")), "ESCALATE")
results.append(not calls)
e = subprocess.run([sys.executable, str(S / "head/custodian/review/review.py"), "--escalate", "--head",
                    str(S / "head"), "--leaves", leaves, "--trusted-fpr", fpr, "--signing-key", esc_key,
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
(S / "head" / "custodian" / "seal.json").write_text("{}")
commit(S / "head")
expect("a head that replaces the root seal", run(), "FAIL (hard)")

print(f"{sum(results)}/{len(results)} checks hold")
sys.exit(0 if all(results) else 1)
