#!/usr/bin/env python3
"""Custodian review: extend the verdict chain of custodian/verify.py, or refuse to.

Review mode runs in `.github/workflows/custodian-review.yml` on `pull_request_target`. The code is
the base branch's (main's), the pull request's head is only read as data, and it never runs.

    review.py --base <main checkout> --head <PR head checkout>
              --trusted-fpr <root fingerprint> --signing-key <review SSH private key>
              --out <dir> --rejections <rejection log checkout> [--pr N --head-sha SHA]

Outcomes (exit 0 only for PASS):
  PASS        the head satisfies the seal in force (the root seal, or the chain's last verdict).
  FAIL hard   a ratchet or structural violation (banned construct, leaf in the DSL, leaf
              violation, semantic rows downstream, a package that is missing, linked, or not at
              its manifest revision, a rewritten root or chain). No review can accept it.
  ESCALATE    the change touches what judges changes: the custodian's files, CI, the owner's text,
              existing acceptance assertions or the ledger. An escalation verdict is required,
              signed with the escalation key after a human-plus-agent review (--escalate below).
  REVIEWED    other sealed files changed: the kernel, or an upstream rule file
              (the catalogue of lean_categories, the leaf contract). The independent reviewer (a
              single model call with the fixed prompt custodian/review/prompt.md, the owner's text
              and the diff, never the orchestrator's argument) approves or rejects. An approval is
              a signed verdict, written to <out>/verdicts/ and posted on the pull request; the head
              must commit it to pass. A rejection is signed, appended to the rejection log, and is
              final for that exact change: the same change against the same seal is never reviewed
              again.

Escalation mode (the owner's machine, with an agent reviewing alongside):

    review.py --escalate --head . --trusted-fpr <root fingerprint>
              --signing-key <the owner's SSH private key, e.g. ~/.ssh/id_ed25519>

Both checkouts carry their dependency chain in `.lake/packages` at their manifest revisions
(`scripts/ci_chain.py <checkout>`). Every signature is an SSH signature (`ssh-keygen -Y sign`,
namespace `lean-cas-custodian`).
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from fnmatch import fnmatch
from pathlib import Path

MODEL = "claude-opus-5-5"
DIFF_LIMIT = 600_000  # characters; a larger change must be split
# Changes to these judge changes: escalation only. Every other sealed file (the kernel, the
# upstream rule files) is reviewed by the agent.
ESCALATE = ["custodian/*", "specs/owner/*", "tests/acceptance/*", "CasAcceptance*",
            "CasGates/*", "CasTools/*", "lakefile.lean", "lean-toolchain", "justfile", "scripts/*"]
SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string", "enum": ["approve", "reject"]},
        "criteria": {"type": "array", "items": {
            "type": "object",
            "properties": {"criterion": {"type": "string"}, "holds": {"type": "boolean"},
                           "evidence": {"type": "string"}},
            "required": ["criterion", "holds", "evidence"], "additionalProperties": False}},
        "summary": {"type": "string"},
    },
    "required": ["verdict", "criteria", "summary"],
    "additionalProperties": False,
}
CRITERIA = 6  # the number of criteria in prompt.md


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def load_verify(path: Path):
    spec = importlib.util.spec_from_file_location("custodian_verify", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sign(V, data: Path, key: Path) -> None:
    """Write <data>.sig with the SSH private key at `key` (ssh-agent and passphrases work)."""
    Path(str(data) + ".sig").unlink(missing_ok=True)  # ssh-keygen asks before overwriting
    subprocess.run(["ssh-keygen", "-q", "-Y", "sign", "-f", str(key), "-n", V.NAMESPACE, str(data)],
                   check=True)


def public_fpr(key: Path) -> str:
    """The SHA256 fingerprint of the SSH key at `key` (a private key, or its .pub)."""
    return subprocess.run(["ssh-keygen", "-lf", str(key)], check=True, capture_output=True,
                          text=True).stdout.split()[1]


def classify(problems: list[str]) -> tuple[list[str], list[str], list[str]]:
    hard, escalate, review = [], [], []
    for p in problems:
        m = re.match(r"(sealed file changed|sealed file removed|new file inside the sealed boundary): (.+)$", p)
        if m:
            (escalate if any(fnmatch(m.group(2), e) for e in ESCALATE) else review).append(p)
        elif p.startswith(("sealed ledger", "sealed assertion")):
            escalate.append(p)
        else:
            hard.append(p)
    return hard, escalate, review


def chain_head(V, root_path: Path, chain) -> str:
    return V.sha(chain[-1][0].read_bytes()) if chain else V.sha(root_path.read_bytes())


def next_verdict(V, root_path: Path, chain, kind: str, signer: str, seal: dict,
                 review: dict) -> dict:
    prev = chain_head(V, root_path, chain)
    return {"format": 1, "seq": len(chain) + 1, "prev": prev, "kind": kind, "signer": signer,
            "seal": seal, "review": review}


def tightened(V, head: Path, tip: dict) -> dict:
    """The head's seal, with every baseline intersected with the tip's: a review never grows one."""
    seal = V.build_seal(head, tip["boundary"], tip["append_only"], tip["verifier_sha256"],
                        "review verdict")
    for k in ("banned_baseline", "leaf_baseline", "outside_baseline"):
        seal[k] = sorted(set(seal[k]) & set(tip[k]))
    return seal


def change_text(base: Path, head: Path, review: list[str]) -> str:
    parts = []
    for p in review:
        f = p.split(": ", 1)[1]
        a = (base / f).read_text(errors="replace").splitlines(True) if (base / f).is_file() else []
        b = (head / f).read_text(errors="replace").splitlines(True) if (head / f).is_file() else []
        parts.append("".join(difflib.unified_diff(a, b, f"a/{f}", f"b/{f}")))
    return "\n".join(parts)


def call_reviewer(prompt: Path, owner: str, change: str) -> tuple[dict | None, str]:
    """One Claude Code call with no tools, no settings and no MCP servers: the fixed prompt as the
    system prompt, the owner's text and the change as the only input, the verdict as structured
    output. Authenticates with CLAUDE_CODE_OAUTH_TOKEN (the owner's subscription)."""
    # No refusal fallback: a decline is a rejection, never a silent switch to another reviewer.
    r = subprocess.run(
        ["claude", "-p", "--model", MODEL, "--effort", "high", "--tools", "", "--setting-sources", "",
         "--strict-mcp-config", "--no-session-persistence", "--system-prompt-file", str(prompt),
         "--json-schema", json.dumps(SCHEMA), "--output-format", "json"],
        input="<owner_requirement>\n" + owner + "\n</owner_requirement>\n\n"
              "<untrusted_change>\n" + change + "\n</untrusted_change>\n",
        capture_output=True, text=True)
    if r.returncode != 0:
        return None, f"reviewer call failed ({r.returncode}): {(r.stderr or r.stdout).strip()[-500:]}"
    out = json.loads(r.stdout)
    if out.get("is_error") or out.get("subtype") != "success" or "structured_output" not in out:
        return None, f"reviewer stopped: {out.get('subtype')}: {str(out.get('result'))[:500]}"
    return out["structured_output"], ",".join(out["modelUsage"])


def review_mode(a) -> int:
    base, head, out = a.base.resolve(), a.head.resolve(), a.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    V = load_verify(base / "custodian" / "verify.py")
    root_path = base / "custodian" / "seal.json"
    V.verify_signature(root_path, Path(str(root_path) + ".sig"), base / "custodian" / "root.pub",
                       a.trusted_fpr)
    root = json.loads(root_path.read_text())
    comment = []

    def finish(code: int, title: str, lines: list[str]) -> int:
        body = [f"### Custodian review: {title}", ""] + [f"- {l}" for l in lines] + comment
        (out / "comment.md").write_text("\n".join(body) + "\n")
        print("\n".join(body))
        return code

    for f in ("seal.json", "seal.json.sig"):
        if (head / "custodian" / f).read_bytes() != (base / "custodian" / f).read_bytes():
            return finish(1, "FAIL (hard)", [f"the root seal custodian/{f} was changed"])
    try:
        base_chain = V.load_chain(base, root_path, root)
        chain = V.load_chain(head, root_path, root)
    except SystemExit as e:
        return finish(1, "FAIL (hard)", [str(e)])
    if len(chain) < len(base_chain) or any(
            x.read_bytes() != y.read_bytes() for (x, _), (y, _) in zip(base_chain, chain)):
        return finish(1, "FAIL (hard)", ["the verdict chain of main was rewritten or truncated"])
    tip = V.tip_seal(root, chain)
    problems = V.check(head, tip)
    if not problems:
        return finish(0, "PASS", [f"the head satisfies the seal in force ({len(chain)} verdicts)"])
    hard, escalate, review = classify(problems)
    if hard:
        return finish(1, "FAIL (hard)", hard + ["no review can accept these"])
    if escalate:
        return finish(1, "ESCALATE", escalate + [
            "these change what judges changes: an escalation verdict is required "
            "(custodian/CONTAINMENT.md, \"Escalation\")"])
    boundary = V.current_boundary(head, tip)
    key = sha(json.dumps({"tip": chain_head(V, root_path, chain), "files": boundary},
                         sort_keys=True).encode())
    if a.rejections and (a.rejections / f"{key}.json").exists():
        return finish(1, "REJECTED (final)", [f"this exact change was already rejected ({key[:16]}); "
                                              "a rejection is never re-reviewed"])
    change = change_text(base, head, review)
    here = base / "custodian"
    prompt = here / "review" / "prompt.md"
    owner = "\n\n".join((base / p).read_text() for p in
                        ("specs/owner/convergence-process.md", "custodian/owner-intent.md",
                         "custodian/CONTAINMENT.md"))
    record = {"model": MODEL, "prompt_sha256": sha(prompt.read_bytes()), "change_sha256": sha(change.encode()),
              "change_key": key, "pr": a.pr, "head_sha": a.head_sha, "problems": review}
    if len(change) > DIFF_LIMIT:
        result, why = None, f"the change is {len(change)} characters; split it (limit {DIFF_LIMIT})"
    else:
        result, why = call_reviewer(prompt, owner, change)
    approved = (result is not None and result["verdict"] == "approve"
                and len(result["criteria"]) >= CRITERIA and all(c["holds"] for c in result["criteria"]))
    record["result"] = result
    record["served_by"] = why if result is not None else None
    lines = review + ([result["summary"]] if result else [why])
    if result is not None:
        lines += [f"{'holds' if c['holds'] else 'FAILS'}: {c['criterion']} -- {c['evidence']}"
                  for c in result["criteria"]]
    if approved:
        v = next_verdict(V, root_path, chain, "review", public_fpr(a.signing_key),
                         tightened(V, head, tip), record)
        d = out / "verdicts"
        d.mkdir(exist_ok=True)
        path = d / f"{v['seq']:06d}.json"
        path.write_text(json.dumps(v, indent=1, sort_keys=True) + "\n")
        sign(V, path, a.signing_key)
        comment.extend(["", f"Commit `custodian/verdicts/{path.name}` and `{path.name}.sig` from this "
                        "run's `custodian-verdict` artifact (also below) to the head, unchanged.", "",
                        "```json", path.read_text(), "```", "", "Signature:", "```",
                        Path(str(path) + ".sig").read_text(), "```"])
        return finish(1, "APPROVED (commit the verdict to pass)", lines)
    if a.rejections:
        rec = a.rejections / f"{key}.json"
        rec.write_text(json.dumps({"key": key, "signer": public_fpr(a.signing_key), "record": record},
                                  indent=1, sort_keys=True) + "\n")
        sign(V, rec, a.signing_key)
    return finish(1, "REJECTED (final for this change)", lines)


def escalate_mode(a) -> int:
    head = a.head.resolve()
    V = load_verify(head / "custodian" / "verify.py")
    root_path = head / "custodian" / "seal.json"
    V.verify_signature(root_path, Path(str(root_path) + ".sig"), head / "custodian" / "root.pub",
                       a.trusted_fpr)
    root = json.loads(root_path.read_text())
    chain = V.load_chain(head, root_path, root)
    tip = V.tip_seal(root, chain)
    hard, _, _ = classify(V.check(head, tip))
    if hard:
        print("refused: hard violations cannot be escalated:\n  " + "\n  ".join(hard))
        return 1
    spec = json.loads((head / "custodian" / "boundary.json").read_text())
    seal = V.build_seal(head, spec["boundary"], spec["append_only"],
                        V.sha((head / "custodian" / "verify.py").read_bytes()), a.note)
    v = next_verdict(V, root_path, chain, "escalation", public_fpr(a.signing_key), seal,
                     {"note": a.note})
    path = head / V.VERDICTS / f"{v['seq']:06d}.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(v, indent=1, sort_keys=True) + "\n")
    sign(V, path, a.signing_key)
    print(f"wrote {path} and its signature; commit both to the head")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--base", type=Path)
    ap.add_argument("--head", type=Path, required=True)
    ap.add_argument("--trusted-fpr", required=True)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--rejections", type=Path)
    ap.add_argument("--pr")
    ap.add_argument("--head-sha")
    ap.add_argument("--escalate", action="store_true")
    ap.add_argument("--signing-key", type=Path, required=True)
    ap.add_argument("--note", default="")
    a = ap.parse_args()
    return escalate_mode(a) if a.escalate else review_mode(a)


if __name__ == "__main__":
    sys.exit(main())
