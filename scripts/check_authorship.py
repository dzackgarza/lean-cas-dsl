#!/usr/bin/env python3
"""Authors are separated by layer (specs/architecture.md, "Authors: one role per agent").

Every commit an agent makes, from the cutoff on, in any repository of the chain (this one and the
packages `lean_categories`, `cas_leaf_contracts`, `cas_leaves` it links), must:

1. declare its author's role in an `Agent-Role:` trailer (`orchestrator`, `formalization`,
   `acceptance` or `leaf`);
2. touch only paths of that role (`LAYERS` below; `NEUTRAL` paths are anyone's);
3. come from an author (its `Agent-Id:` trailer, else its `Claude-Session:` trailer) who, over all
   the repositories, writes in that role and no other.

A commit with neither trailer is a person's and is not checked. The owner's commits are theirs to
make. Admitting or correcting acceptance assertions (`CasAcceptance/Permanent/admitted.json`'s
`assertions` and `corrections`) is the acceptance role's. Recording the `lean_categories` pin there
is anyone's.

    check_authorship.py            check the chain; exit 1 with every violation
    check_authorship.py --self-test
                                   run the gate against synthetic repositories that reproduce
                                   the violations it exists to refuse
"""

from __future__ import annotations

import fnmatch
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# Commits from here on are checked: after the owner's correction of 2026-09-30 separating authors
# and the documents recording it.
CUTOFF = "2026-09-30T09:55:00+00:00"
# `custodian`: only paths inside the custodian seal (custodian/CONTAINMENT.md), so declaring the role
# grants no write the seal does not refuse.
ROLES = ("orchestrator", "formalization", "acceptance", "leaf", "custodian")
ADMITTED = "CasAcceptance/Permanent/admitted.json"

# (repository, role) -> path patterns; the first matching role wins.
LAYERS: dict[str, list[tuple[str, list[str]]]] = {
    "lean-cas-dsl": [
        ("custodian", ["custodian/*", ".github/workflows/custodian.yml"]),
        ("acceptance", ["tests/acceptance/*", "CasAcceptance/Permanent/*.lean"]),
        ("leaf", ["CasLeaves/*"]),
        ("orchestrator", ["*"]),
    ],
    "lean_categories": [
        ("orchestrator", ["LeanCategories/Catalogue/Registry/*", "*.md", "scripts/*",
                          "justfile", ".github/*", "lakefile.toml", "lake-manifest.json"]),
        ("formalization", ["*"]),
    ],
    "cas_leaf_contracts": [("orchestrator", ["*"])],
    "cas_leaves": [
        ("leaf", ["CasLeaves/*", "CasLeaves.lean"]),
        ("orchestrator", ["*"]),
    ],
}
# Anyone's: aggregating import lists and the findings log.
NEUTRAL: dict[str, list[str]] = {
    # This gate is inside the custodian seal: whoever writes it, a change fails the seal.
    "lean-cas-dsl": ["scripts/check_authorship.py"],
    "lean_categories": ["LeanCategories.lean", "LeanCategories/Catalogue.lean", "COMPLAINTS.md"],
    "cas_leaf_contracts": [],
    "cas_leaves": [],
}
# Overrides of the patterns above, checked first.
EXACT: dict[str, dict[str, str]] = {
    "lean_categories": {
        "COMPLAINTS.md": "neutral",
        "TODO.md": "formalization",
        # The totality gate's probes (plan node gov-registry-gates).
        "LeanCategories/Catalogue/Semantics/TotalityProbes.lean": "orchestrator",
    },
}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True).stdout


def role_of(repo: str, path: str) -> str:
    if (exact := EXACT.get(repo, {}).get(path)) is not None:
        return exact
    if any(fnmatch.fnmatch(path, p) for p in NEUTRAL[repo]):
        return "neutral"
    for role, patterns in LAYERS[repo]:
        if any(fnmatch.fnmatch(path, p) for p in patterns):
            return role
    return "orchestrator"


def trailer(message: str, key: str) -> str | None:
    found = re.findall(rf"^{key}:\s*(.+?)\s*$", message, re.MULTILINE)
    return found[-1] if found else None


def admitted_role(repo: Path, commit: str) -> str:
    """The role of a change to the admission manifest: acceptance if it admits or corrects."""
    def load(rev: str) -> dict:
        try:
            return json.loads(git(repo, "show", f"{rev}:{ADMITTED}"))
        except (subprocess.CalledProcessError, json.JSONDecodeError):
            return {}
    before, after = load(f"{commit}^"), load(commit)
    keys = ("assertions", "corrections")
    return ("acceptance" if any(before.get(k) != after.get(k) for k in keys) else "neutral")


def commits(name: str, repo: Path) -> list[dict]:
    if subprocess.run(["git", "-C", str(repo), "rev-parse", "-q", "--verify", "HEAD"],
                      capture_output=True).returncode != 0:
        return []
    log = git(repo, "log", f"--since={CUTOFF}", "--format=%H%x1f%cI%x1f%B%x1e")
    out = []
    for record in log.split("\x1e"):
        record = record.strip("\n")
        if not record:
            continue
        sha, date, message = record.split("\x1f", 2)
        if date < CUTOFF:
            continue
        session = trailer(message, "Claude-Session")
        agent = trailer(message, "Agent-Id") or session
        if agent is None:
            continue
        files = [f for f in git(repo, "diff-tree", "--no-commit-id", "--name-only", "-r",
                                "--root", sha).splitlines() if f]
        roles = set()
        for f in files:
            role = admitted_role(repo, sha) if (name == "lean-cas-dsl" and f == ADMITTED) \
                else role_of(name, f)
            if role != "neutral":
                roles.add(role)
        out.append({"repo": name, "sha": sha[:9], "agent": agent,
                    "declared": trailer(message, "Agent-Role"), "roles": roles,
                    "subject": message.splitlines()[0] if message else ""})
    return out


def check(repos: dict[str, Path]) -> list[str]:
    problems = []
    by_agent: dict[str, dict[str, list[str]]] = {}
    for name, repo in repos.items():
        for c in commits(name, repo):
            where = f"{c['repo']} {c['sha']} ({c['subject']})"
            declared = c["declared"]
            if declared not in ROLES:
                problems.append(f"{where}: no valid Agent-Role trailer (one of {', '.join(ROLES)})")
            else:
                for role in sorted(c["roles"] - {declared}):
                    problems.append(f"{where}: declared {declared} but writes {role} paths")
            for role in c["roles"] | ({declared} if declared in ROLES else set()):
                by_agent.setdefault(c["agent"], {}).setdefault(role, []).append(where)
    for agent, roles in by_agent.items():
        if len(roles) > 1:
            detail = "; ".join(f"{r}: {', '.join(w)}" for r, w in sorted(roles.items()))
            problems.append(f"author {agent} writes in {len(roles)} roles ({detail})")
    return problems


def chain() -> dict[str, Path]:
    packages = ROOT / ".lake" / "packages"
    repos = {"lean-cas-dsl": ROOT}
    for name in ("lean_categories", "cas_leaf_contracts", "cas_leaves"):
        path = (packages / name).resolve()
        if (path / ".git").exists():
            repos[name] = path
    return repos


def self_test() -> int:
    """The gate refuses this session's pattern and accepts separated authors."""
    def commit(repo: Path, path: str, message: str) -> None:
        (repo / path).parent.mkdir(parents=True, exist_ok=True)
        (repo / path).write_text(message)
        git(repo, "add", path)
        git(repo, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", message)

    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        repos = {}
        for name in LAYERS:
            repos[name] = Path(tmp) / name
            repos[name].mkdir()
            git(repos[name], "init", "-q")
        cases = [
            # (repository, path, role, agent, expected to be refused)
            ("lean_categories", "LeanCategories/Catalogue/Semantics/X.lean", "formalization",
             "f1", False),
            ("lean-cas-dsl", "tests/acceptance/x.cas", "acceptance", "a1", False),
            ("cas_leaves", "CasLeaves/X.lean", "leaf", "l1", False),
            ("lean-cas-dsl", "CasCatalogue/Language.lean", "orchestrator", "o1", False),
            # One author formalizing and implementing (this session's pattern).
            ("lean_categories", "LeanCategories/Catalogue/Semantics/Y.lean", "formalization",
             "o1", True),
            # An orchestrator commit writing a test.
            ("lean-cas-dsl", "tests/acceptance/y.cas", "orchestrator", "o2", True),
            # A commit with no role.
            ("cas_leaves", "CasLeaves/Z.lean", None, "l2", True),
        ]
        for i, (name, path, role, agent, _) in enumerate(cases):
            lines = [f"case {i}", ""] + ([f"Agent-Role: {role}"] if role else []) + \
                [f"Agent-Id: {agent}"]
            commit(repos[name], path, "\n".join(lines))
        problems = "\n".join(check(repos))
        if "author o1 writes in 2 roles" not in problems:
            failures.append("one author formalizing and implementing is not refused")
        if "declared orchestrator but writes acceptance paths" not in problems:
            failures.append("an orchestrator commit to the tests is not refused")
        if "no valid Agent-Role" not in problems:
            failures.append("a commit without a role is not refused")
        for agent in ("f1", "a1", "l1"):
            if f"author {agent} " in problems:
                failures.append(f"separated author {agent} is refused")
    if failures:
        print("check_authorship self-test failed:\n  " + "\n  ".join(failures), file=sys.stderr)
        return 1
    return 0


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        raise SystemExit(__doc__)
    problems = check(chain())
    if problems:
        print("authors are separated by layer (specs/architecture.md, \"Authors: one role per "
              "agent\"):", file=sys.stderr)
        print("\n".join("  " + p for p in problems), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
