#!/usr/bin/env python3
"""Custodian verifier: the acceptance boundary of lean-cas-dsl, checked against a signed seal.

Trust does not come from this file. It comes from the seal's signature, checked by OpenSSL against a
public-key fingerprint that the verifier's *caller* supplies from outside the repository (the
owner received it in the custodian session). Bootstrap before trusting this script:

    openssl pkey -pubin -in custodian/custodian.pub.pem -outform DER | sha256sum    # == trusted fpr
    openssl pkeyutl -verify -pubin -inkey custodian/custodian.pub.pem -rawin \
        -in custodian/seal.json -sigfile custodian/seal.json.sig                    # Signature Verified
    sha256sum custodian/verify.py                        # == "verifier_sha256" in custodian/seal.json

Then:

    python3 custodian/verify.py --trusted-fpr <sha256 of the DER public key> \
        [--repo .] [--leaves <checkout of lean-cas-dsl-leaves>] [--key <pub.pem>] [--seal <json>]

Exit 0 iff every check passes. Any change to a sealed path, a sealed pin, or a new banned construct
is reported and fails. Nothing here has an exemption mechanism: the only way to change what is
checked is a new seal signed by a key the caller chooses to trust.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from fnmatch import fnmatch
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Pins whose revision may move without a new seal: leaves are ordinary downstream work.
FREE_PINS = {"cas_leaves"}
# The require line of a free pin in lakefile.lean is normalized before hashing.
FREE_REQUIRE = re.compile(
    r'(require cas_leaves from git\s*\n\s*"[^"]+"\s*@\s*)"[0-9a-f]{40}"')

# Constructs that make a result undefined, unchecked or unsound, or that let code rewrite how other
# code (an assertion, a contract command) is elaborated.
BANNED_EVERYWHERE = {
    "sorry": r"\bsorry\b",
    "admit": r"(?<!def )(?<!\()\badmit\b(?!\s*[\w(←:])",
    "axiom": r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\s",
    "partial": r"\bpartial\s+def\b",
    "unsafe": r"\bunsafe\b",
    "implemented_by": r"\bimplemented_by\b",
    "extern": r"@\[\s*extern\b",
    "panic": r"\bpanic!",
    "unreachable": r"\bunreachable!",
    "native_decide": r"\bnative_decide\b",
    "ofReduceBool": r"\bLean\.ofReduceBool\b|\bofReduceBool\b",
    "debug.skipKernelTC": r"skipKernelTC",
}
# Additionally banned in leaves: a leaf realizes registered operations and nothing else, so it may
# not define syntax, elaborators, macros or global attributes (a `macro_rules` for `#accept` would
# make every assertion pass), and may not see the kernel or the tests.
BANNED_IN_LEAVES = {
    "syntax": r"^\s*(?:@\[[^\]]*\]\s*)?(?:scoped\s+|local\s+)?(?:syntax|macro|macro_rules|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|declare_syntax_cat)\b",
    "elab-attribute": r"@\[\s*(?:command_elab|term_elab|tactic|macro|builtin_\w+)\b",
    "initialize": r"^\s*(?:builtin_)?initialize\b",
    "global-attribute": r"^\s*attribute\s*\[",
    "imports-kernel-or-tests": r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(?:CasCatalogue|CasAcceptance|CasDsl|CasDslTests|CasTools|CasGates)\b",
    "reads-tests": r"tests/acceptance|\.cas\b",
    "semantic-registration": r"\bnormalized_registry\b|\baddSemanticEntryChecked\b|\bpersistSemanticEntry\b",
}
# In lean-cas-dsl, outside the sealed boundary: no syntax or elaborator may be (re)defined (it could
# change how a sealed assertion elaborates), and no semantic row may be written downstream.
BANNED_OUTSIDE_BOUNDARY = {k: BANNED_IN_LEAVES[k] for k in
                           ("syntax", "elab-attribute", "initialize", "global-attribute",
                            "semantic-registration")}
# The admission ledger may only grow: sealed entries keep their hashes, corrections never change.
LEDGER = "CasAcceptance/Permanent/admitted.json"
LEAF_IMPORT_ROOTS = ("Init", "Std", "Lean", "Mathlib", "CasContract", "LeanCategories", "CasLeaves",
                     "Batteries", "Qq", "Aesop")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", re.MULTILINE)
REGISTER_LEAF = re.compile(r"(^\s*register_leaf\b)|\b(registerLeaf|addLeafRegistryEntryChecked)\b",
                           re.MULTILINE)


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True).stdout


def tracked(repo: Path) -> list[str]:
    return [f for f in git(repo, "ls-files", "-z").split("\0") if f]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalized(path: str, data: bytes) -> bytes:
    if path == "lakefile.lean":
        return FREE_REQUIRE.sub(r'\1"<free>"', data.decode()).encode()
    return data


def strip_comments(text: str) -> str:
    """Lean source with comments and string literals blanked (line structure kept)."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1; i += 2; continue
            if text.startswith("-/", i):
                depth -= 1; i += 2; continue
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text.startswith("/-", i):
            depth = 1; i += 2; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('"' + " " * max(0, j - i - 1) + '"'); i = j + 1; continue
        out.append(text[i]); i += 1
    return "".join(out)


def occurrences(repo: Path, files: list[str], rules: dict[str, str], raw_rules: set[str] = frozenset()
                ) -> list[str]:
    """`file:rule:sha(line)` for every hit; the line hash makes a baseline entry specific."""
    found = []
    for f in files:
        if not f.endswith(".lean"):
            continue
        raw = (repo / f).read_text(errors="replace")
        code = strip_comments(raw)
        for rule, pattern in rules.items():
            text = raw if rule in raw_rules else code
            for m in re.finditer(pattern, text, re.MULTILINE):
                line = text[text.rfind("\n", 0, m.start()) + 1:text.find("\n", m.start())]
                found.append(f"{f}:{rule}:{sha(' '.join(line.split()).encode())[:16]}")
    return sorted(found)


def scan_leaves(leaves: Path) -> list[str]:
    files = [f for f in tracked(leaves) if f.endswith(".lean") and f != "lakefile.lean"]
    rules = dict(BANNED_EVERYWHERE, **BANNED_IN_LEAVES)
    found = occurrences(leaves, files, rules, raw_rules={"reads-tests"})
    for f in files:
        for m in IMPORT.finditer(strip_comments((leaves / f).read_text(errors="replace"))):
            if m.group(1).split(".")[0] not in LEAF_IMPORT_ROOTS:
                found.append(f"{f}:import:{m.group(1)}")
    lake = (leaves / "lakefile.lean")
    if lake.exists() and re.search(r'/lean-cas-dsl(?:\.git)?"', lake.read_text()):
        found.append("lakefile.lean:requires-lean-cas-dsl")
    for f in tracked(leaves):
        if f.startswith("tests/") or f.endswith(".cas"):
            found.append(f"{f}:test-file-in-leaves")
        if f.endswith(".lean") and f not in ("lakefile.lean", "CasLeaves.lean") \
                and not f.startswith("CasLeaves/"):
            found.append(f"{f}:module-outside-CasLeaves")
    return sorted(found)


def manifest_pins(repo: Path) -> dict[str, str]:
    m = json.loads((repo / "lake-manifest.json").read_text())
    return {p["name"]: p.get("rev", "") for p in m["packages"]}


def in_boundary(path: str, seal: dict) -> bool:
    return any(fnmatch(path, p) for p in seal["boundary"])


def current_boundary(repo: Path, seal: dict) -> dict[str, str]:
    return {f: sha(normalized(f, (repo / f).read_bytes())) for f in tracked(repo)
            if in_boundary(f, seal) and (repo / f).is_file() and f != LEDGER}


def outside_hits(repo: Path, seal: dict) -> list[str]:
    files = [f for f in tracked(repo) if f.endswith(".lean") and not in_boundary(f, seal)]
    found = occurrences(repo, files, BANNED_OUTSIDE_BOUNDARY)
    found += [f"{f}:semantic-module-downstream" for f in tracked(repo)
              if f.startswith("LeanCategories/") or f == "LeanCategories.lean"]
    return sorted(found)


def build_seal(repo: Path, leaves: Path | None, boundary: list[str], append_only: list[str],
               verifier_sha: str, note: str) -> dict:
    seal = {"format": 1, "boundary": boundary, "append_only": append_only}
    seal["files"] = current_boundary(repo, seal)
    seal["pins"] = {k: v for k, v in manifest_pins(repo).items() if k not in FREE_PINS}
    lean = [f for f in tracked(repo) if f.endswith(".lean")]
    seal["banned_baseline"] = occurrences(repo, lean, BANNED_EVERYWHERE)
    seal["leaf_baseline"] = scan_leaves(leaves) if leaves else []
    seal["outside_baseline"] = outside_hits(repo, seal)
    seal["ledger"] = json.loads((repo / LEDGER).read_text())
    seal["sealed_commit"] = git(repo, "rev-parse", "HEAD").strip()
    seal["verifier_sha256"] = verifier_sha
    seal["note"] = note
    return seal


def check(repo: Path, seal: dict, leaves: Path | None) -> list[str]:
    problems = []
    now = current_boundary(repo, seal)
    for f, h in sorted(seal["files"].items()):
        if f not in now:
            problems.append(f"sealed file removed: {f}")
        elif now[f] != h:
            problems.append(f"sealed file changed: {f}")
    for f in sorted(set(now) - set(seal["files"])):
        if any(fnmatch(f, p) for p in seal["append_only"]):
            print(f"note: unsealed addition (not accepted until a new seal): {f}")
        else:
            problems.append(f"new file inside the sealed boundary: {f}")
    ledger = json.loads((repo / LEDGER).read_text()) if (repo / LEDGER).exists() else None
    if ledger is None:
        problems.append(f"sealed ledger removed: {LEDGER}")
    else:
        for key in sorted(set(seal["ledger"]) | set(ledger)):
            if key == "assertions":
                continue
            if ledger.get(key) != seal["ledger"].get(key):
                problems.append(f"sealed ledger field changed: {LEDGER} {key}")
        for ident, h in sorted(seal["ledger"]["assertions"].items()):
            if ledger.get("assertions", {}).get(ident) != h:
                problems.append(f"sealed assertion changed or removed in the ledger: {ident}")
        for ident in sorted(set(ledger.get("assertions", {})) - set(seal["ledger"]["assertions"])):
            print(f"note: unsealed assertion (not accepted until a new seal): {ident}")
    for hit in sorted(set(outside_hits(repo, seal)) - set(seal["outside_baseline"])):
        problems.append(f"outside the boundary: {hit}")
    pins = manifest_pins(repo)
    for name, rev in sorted(seal["pins"].items()):
        if pins.get(name) != rev:
            problems.append(f"sealed pin moved: {name} {rev[:12]} -> {str(pins.get(name))[:12]}")
    for name in sorted(set(pins) - set(seal["pins"]) - FREE_PINS):
        problems.append(f"new unsealed dependency: {name}")
    # Development links: a local package checkout must be the pinned revision.
    for name, rev in sorted(pins.items()):
        pkg = repo / ".lake" / "packages" / name
        if pkg.is_symlink():
            problems.append(f".lake/packages/{name} is a link to a working tree, not the pin")
        elif (pkg / ".git").exists():
            head = git(pkg, "rev-parse", "HEAD").strip()
            dirty = git(pkg, "status", "--porcelain", "--untracked-files=no").strip()
            if head != rev or dirty:
                problems.append(f".lake/packages/{name} is not the pinned revision {rev[:12]}")
    # No leaf in lean-cas-dsl.
    for f in tracked(repo):
        if f.startswith("CasLeaves/"):
            problems.append(f"leaf file in lean-cas-dsl: {f}")
        elif f.endswith(".lean"):
            for m in REGISTER_LEAF.finditer(strip_comments((repo / f).read_text(errors="replace"))):
                problems.append(f"leaf registration in lean-cas-dsl: {f}")
    # Banned constructs: the baseline can only shrink.
    lean = [f for f in tracked(repo) if f.endswith(".lean")]
    for hit in sorted(set(occurrences(repo, lean, BANNED_EVERYWHERE)) - set(seal["banned_baseline"])):
        problems.append(f"banned construct: {hit}")
    if leaves is not None:
        rev = pins.get("cas_leaves")
        head = git(leaves, "rev-parse", "HEAD").strip()
        if head != rev or git(leaves, "status", "--porcelain", "--untracked-files=no").strip():
            problems.append(f"--leaves checkout is {head[:12]}, not the pinned {str(rev)[:12]}")
        for hit in sorted(set(scan_leaves(leaves)) - set(seal["leaf_baseline"])):
            problems.append(f"leaf violation: {hit}")
    else:
        print("note: --leaves not given; the leaves were not checked")
    return problems


def verify_signature(seal_path: Path, sig: Path, key: Path, trusted: str) -> None:
    der = subprocess.run(["openssl", "pkey", "-pubin", "-in", str(key), "-outform", "DER"],
                         check=True, capture_output=True).stdout
    if sha(der) != trusted.lower():
        raise SystemExit(f"UNTRUSTED: {key} has fingerprint {sha(der)}, not {trusted}")
    r = subprocess.run(["openssl", "pkeyutl", "-verify", "-pubin", "-inkey", str(key), "-rawin",
                        "-in", str(seal_path), "-sigfile", str(sig)], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"INVALID SIGNATURE on {seal_path}: {r.stdout}{r.stderr}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--repo", type=Path, default=HERE.parent)
    ap.add_argument("--seal", type=Path, default=HERE / "seal.json")
    ap.add_argument("--key", type=Path, default=HERE / "custodian.pub.pem")
    ap.add_argument("--trusted-fpr", help="sha256 of the signer's DER public key, from outside the repo")
    ap.add_argument("--leaves", type=Path)
    ap.add_argument("--make-seal", action="store_true",
                    help="write an unsigned seal of the current state to --seal (for the signer)")
    ap.add_argument("--note", default="")
    args = ap.parse_args()
    repo = args.repo.resolve()
    verifier_sha = sha(Path(__file__).read_bytes())
    if args.make_seal:
        # The boundary is custodian/boundary.json, itself a sealed file.
        spec = json.loads((repo / "custodian" / "boundary.json").read_text())
        boundary, append_only = spec["boundary"], spec["append_only"]
        seal = build_seal(repo, args.leaves, boundary, append_only, verifier_sha, args.note)
        args.seal.write_text(json.dumps(seal, indent=1, sort_keys=True) + "\n")
        print(f"wrote {args.seal}; sign it: openssl pkeyutl -sign -inkey <key> -rawin "
              f"-in {args.seal} -out {args.seal}.sig")
        return 0
    if not args.trusted_fpr:
        raise SystemExit("--trusted-fpr is required: the fingerprint comes from outside the repo")
    verify_signature(args.seal, Path(str(args.seal) + ".sig"), args.key, args.trusted_fpr)
    seal = json.loads(args.seal.read_text())
    if seal["verifier_sha256"] != verifier_sha:
        raise SystemExit("this verifier is not the sealed verifier")
    problems = check(repo, seal, args.leaves.resolve() if args.leaves else None)
    if problems:
        print("CONTAINMENT VIOLATED (custodian seal):")
        print("\n".join("  " + p for p in problems))
        return 1
    print(f"seal holds: {len(seal['files'])} sealed files, {len(seal['pins'])} sealed pins")
    return 0


if __name__ == "__main__":
    sys.exit(main())
