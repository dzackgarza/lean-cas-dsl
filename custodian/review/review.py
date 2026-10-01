#!/usr/bin/env python3
"""Custodian review: extend the verdict chain of custodian/verify.py, or refuse to.

Review mode runs in `.github/workflows/custodian-review.yml` on `pull_request_target`. The code is
the base branch's (main's), the pull request's head is only read as data, and it never runs.

    review.py --base <main checkout> --head <PR head checkout>
              --trusted-fpr <root fingerprint> --signing-key <review SSH private key>
              --out <dir> --rejections <findings log checkout> [--pr N --head-sha SHA]
              [--description FILE] [--comments FILE]

The author's explanation is the pull request's description: --description, else the
`pull_request.body` of the event at $GITHUB_EVENT_PATH. --comments is a JSON list of the pull
request's comments (strings, or objects with a `body`). Both are untrusted data.

Outcomes (exit 0 only for PASS):
  PASS             the head satisfies the seal in force (the root seal, or the chain's last verdict).
  FAIL (hard)      a ratchet or structural violation (banned construct, leaf in the DSL, leaf
                   violation, semantic rows downstream, a package that is missing, linked, or not at
                   its manifest revision, a rewritten root or chain). No review can accept it.
  ESCALATE         a reserved requirement changes: an admitted assertion or the sealed ledger
                   changes, or an admitted assertion leaves the suite (decided here, without a
                   model call); or the reviewer found a reserved-requirement change or evidence of
                   evasion. The owner decides: an escalation verdict (--escalate below), or no merge.
  APPROVED         the reviewer approved: a signed verdict, written to <out>/verdicts/ and posted
                   on the pull request; the head commits it unchanged to pass.
  REJECTED         the reviewer found a demonstrated defect. Repair it and push the revision.
  NEEDS EVIDENCE   the reviewer named evidence the change needs. Supply it (a revision, or a
                   reconsideration below).
  REVIEW FAILED    the review operation failed (no run, unusable output, missing context, an input
                   over the size bound). No verdict was given, nothing is recorded, and the same
                   change is reviewed again on the next run once the operation is repaired.
  REFUSED          this exact change was already decided against the same seal, and no new
                   reconsideration accompanies it.

The findings log (the `custodian/rejections` branch) keeps every substantive negative outcome,
signed, keyed by the seal in force and the head's sealed files. The same change against the same
seal is reviewed again only with a reconsideration: a fenced block in the description or a comment,

    ```custodian-reconsideration
    finding: F2
    basis: new-evidence | corrected-context | finding-error
    <the evidence, the corrected context, or the error in the finding>
    ```

naming a finding of the latest record. The reviewer judges it against the controlling requirements;
a reconsideration already decided for that change is refused. A substantive revision changes the
sealed files, so it is a new change and is reviewed. Nothing the candidate writes is a verdict.

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
import os
import re
import subprocess
import sys
from pathlib import Path

MODEL = "claude-opus-5-5"
DIFF_LIMIT = 600_000  # characters of sealed diffs; over it the invocation, not the change, is repaired
CONTEXT_LIMIT = 300_000  # characters of unchanged and unsealed context; files past it are named
FINDING_KINDS = ["defect", "missing_evidence", "review_operation", "correction",
                 "reserved_requirement", "evasion"]
SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string",
                    "enum": ["approve", "reject", "needs_evidence", "escalate", "review_failed"]},
        "criteria": {"type": "array", "items": {
            "type": "object",
            "properties": {"criterion": {"type": "string"}, "holds": {"type": "boolean"},
                           "evidence": {"type": "string"}},
            "required": ["criterion", "holds", "evidence"], "additionalProperties": False}},
        "findings": {"type": "array", "items": {
            "type": "object",
            "properties": {"kind": {"type": "string", "enum": FINDING_KINDS},
                           "requirement": {"type": "string"}, "location": {"type": "string"},
                           "evidence": {"type": "string"}, "action": {"type": "string"}},
            "required": ["kind", "requirement", "location", "evidence", "action"],
            "additionalProperties": False}},
        "reconsideration": {
            "type": "object",
            "properties": {"outcome": {"type": "string",
                                       "enum": ["not_applicable", "withdrawn", "upheld"]},
                           "reason": {"type": "string"}},
            "required": ["outcome", "reason"], "additionalProperties": False},
        "summary": {"type": "string"},
    },
    "required": ["verdict", "criteria", "findings", "reconsideration", "summary"],
    "additionalProperties": False,
}
CRITERIA = 8  # the number of criteria in prompt.md
# The controlling requirements, read from the base. specs/owner/* comes first, in name order.
OWNER_FILES = ("custodian/owner-intent.md", "custodian/CONTAINMENT.md")
OWNER_SECTIONS = (("specs/architecture.md", "## B0 policies"),
                  ("specs/computational-core-plan.md", "## B0:"))
BASES = ("new-evidence", "corrected-context", "finding-error")
RECONSIDER = re.compile(r"^```custodian-reconsideration[ \t]*\n(.*?)^```", re.MULTILINE | re.DOTALL)
TAGS = ("controlling_requirements", "runner_facts", "untrusted_change", "untrusted_context",
        "untrusted_author_explanation")
PATH_REF = re.compile(r"[\w.@+-]+(?:/[\w.@+-]+)*\.(?:py|sh|lean|json|toml|yml|yaml|cas|md|txt)\b")
LEAN_IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.MULTILINE)


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


def classify(problems: list[str]) -> tuple[list[str], list[str]]:
    """Hard violations, and the sealed changes the reviewer decides."""
    hard, review = [], []
    for p in problems:
        changed = re.match(r"(sealed file changed|sealed file removed|new file inside the sealed boundary): ", p)
        (review if changed or p.startswith(("sealed ledger", "sealed assertion")) else hard).append(p)
    return hard, review


def reserved_changes(head: Path, tip: dict, review: list[str]) -> list[str]:
    """Changes to an obligation the runner can establish without a model: an admitted assertion or
    the ledger's sealed fields change (the accepted mathematical question), or an admitted assertion
    no longer appears in the suite. Only the owner decides these."""
    found = [p for p in review if p.startswith(("sealed ledger", "sealed assertion"))]
    texts = [f.read_text(errors="replace") for d, pat in (("tests/acceptance", "*.cas"),
                                                          ("CasAcceptance/Permanent", "*.lean"))
             if (head / d).is_dir() for f in sorted((head / d).glob(pat))]
    for ident in sorted(tip["ledger"]["assertions"]):
        item = re.compile(r"^\s*(?:test|#accept|#accept_backend)\s+" + re.escape(ident) + r"(?=\s)",
                          re.MULTILINE)
        if not any(item.search(t) for t in texts):
            found.append(f"admitted assertion no longer in the suite: {ident}")
    return found


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


def read(d: Path, f: str) -> list[str]:
    return (d / f).read_text(errors="replace").splitlines(True) if (d / f).is_file() else []


def diff(base: Path, head: Path, f: str) -> str:
    return "".join(difflib.unified_diff(read(base, f), read(head, f), f"a/{f}", f"b/{f}"))


def sealed_files(V, review: list[str]) -> list[str]:
    return sorted({V.LEDGER if p.startswith(("sealed ledger", "sealed assertion")) else p.split(": ", 1)[1]
                   for p in review})


def change_text(V, base: Path, head: Path, review: list[str]) -> str:
    return "\n".join(diff(base, head, f) for f in sealed_files(V, review))


def section(text: str, heading: str) -> str | None:
    """The markdown section whose heading line starts with `heading`, up to the next heading of the
    same or a higher level outside a code fence."""
    lines, out, level, fence = text.splitlines(True), None, 0, False
    for line in lines:
        if line.startswith("```"):
            fence = not fence
        if out is None:
            if line.startswith(heading):
                out, level = [line], len(line) - len(line.lstrip("#"))
            continue
        m = re.match(r"(#+) ", line)
        if not fence and m and len(m.group(1)) <= level:
            break
        out.append(line)
    return "".join(out) if out is not None else None


def controlling(base: Path) -> tuple[str, dict]:
    """The controlling requirements, from the base only: the owner's text, the containment rules and
    the controlling plan's B0 sections. A source absent on the base is named as not in force; the
    candidate's copy is never promoted to authority (it is part of the change, and untrusted)."""
    parts, digests = [], {}
    owner = sorted(p.relative_to(base).as_posix() for p in (base / "specs" / "owner").glob("*.md")) \
        if (base / "specs" / "owner").is_dir() else []
    for f in owner + list(OWNER_FILES):
        if (base / f).is_file():
            text = (base / f).read_text()
            parts.append(f"=== {f} ===\n{text}")
            digests[f] = sha(text.encode())
        else:
            parts.append(f"=== {f} ===\n[absent on the base: not in force]\n")
            digests[f] = None
    for f, heading in OWNER_SECTIONS:
        text = section((base / f).read_text(), heading) if (base / f).is_file() else None
        name = f"{f} \"{heading.lstrip('# ')}\""
        parts.append(f"=== {name} ===\n" + (text or "[absent on the base: not in force]\n"))
        digests[name] = sha(text.encode()) if text else None
    return "\n\n".join(parts), digests


def context_text(V, base: Path, head: Path, sealed: list[str]) -> tuple[str, list[str]]:
    """Unchanged and unsealed context, within CONTEXT_LIMIT: the post-change text of each changed
    sealed file, the diffs of the other changed tracked files, and the files any changed file
    references by path or imports (a script a recipe runs, a helper a gate calls), sealed or not.
    Returns the text and the files omitted for size."""
    head_files = set(V.tracked(head))

    def changed(f: str) -> bool:
        if f in sealed or f.startswith(V.VERDICTS + "/"):
            return False
        x, y = base / f, head / f
        return x.is_file() != y.is_file() or x.is_file() and x.read_bytes() != y.read_bytes()

    others = sorted(f for f in head_files | set(V.tracked(base)) if changed(f))
    pieces = [(f"post-change text: {f}", "".join(read(head, f))) for f in sealed if (head / f).is_file()]
    pieces += [(f"diff (not sealed): {f}", diff(base, head, f)) for f in others]
    seen = set(sealed) | set(others)
    for f in [f for f in sealed + others if (head / f).is_file()]:
        text = (head / f).read_text(errors="replace")
        refs = PATH_REF.findall(text) + [m.replace(".", "/") + ".lean" for m in LEAN_IMPORT.findall(text)]
        for r in refs:
            r = r.removeprefix("./")
            if r in head_files and r not in seen:
                seen.add(r)
                pieces.append((f"referenced by {f}: {r}", "".join(read(head, r))))
    out, size, omitted = [], 0, []
    for title, text in pieces:
        if size + len(text) > CONTEXT_LIMIT:
            omitted.append(title)
            continue
        out.append(f"=== {title} ===\n{text}")
        size += len(text)
    if omitted:
        out.append("=== omitted for size ===\n" + "\n".join(omitted) + "\n")
    return "\n\n".join(out), omitted


def neutral(text: str) -> str:
    """Untrusted text cannot open or close a delimiter of the reviewer's input."""
    return re.sub(r"<(/?)(" + "|".join(TAGS) + r")", r"&lt;\1\2", text)


def description(a) -> str:
    if getattr(a, "description", None):
        return Path(a.description).read_text(errors="replace")
    event = os.environ.get("GITHUB_EVENT_PATH")
    if event and Path(event).is_file():
        return (json.loads(Path(event).read_text()).get("pull_request") or {}).get("body") or ""
    return ""


def comments(a) -> list[str]:
    if not getattr(a, "comments", None):
        return []
    return [c if isinstance(c, str) else str(c.get("body", "")) for c in json.loads(Path(a.comments).read_text())]


def findings_of(entry: dict) -> list[dict]:
    """The findings of a log entry, numbered F1.. by the runner. An entry from the earlier runner
    has no findings: each failed criterion stands for one."""
    result = entry["record"].get("result") or {}
    fs = result.get("findings")
    if fs is None:
        fs = [{"kind": "defect", "requirement": c["criterion"], "location": "",
               "evidence": c["evidence"], "action": ""} for c in result.get("criteria", []) if not c["holds"]]
    return [dict(f, id=f"F{i}") for i, f in enumerate(fs, start=1)]


def load_log(rejections: Path | None, key: str) -> dict | None:
    """The log record of this change, normalized; None when there is none or when its only entries
    record a failed review operation (the earlier runner logged those as rejections; they are not
    verdicts)."""
    if not rejections or not (rejections / f"{key}.json").exists():
        return None
    rec = json.loads((rejections / f"{key}.json").read_text())
    if "entries" not in rec:  # the earlier runner: one entry, every outcome a rejection
        rec = {"key": key, "entries": [{"outcome": "reject", "signer": rec.get("signer"),
                                        "record": rec["record"], "reconsideration": None}]}
    rec["entries"] = [e for e in rec["entries"] if e["record"].get("result") is not None]
    return rec if rec["entries"] else None


def reconsideration(texts: list[str]) -> tuple[dict | None, str | None]:
    """The last reconsideration block in the author's texts, parsed; or the reason it is unusable."""
    blocks = [m.group(1) for t in texts for m in RECONSIDER.finditer(t.replace("\r\n", "\n"))]
    if not blocks:
        return None, None
    lines = blocks[-1].strip().splitlines()
    fields = {}
    while lines and re.match(r"(finding|basis):", lines[0]):
        k, v = lines.pop(0).split(":", 1)
        fields[k] = v.strip()
    evidence = "\n".join(lines).strip()
    if "finding" not in fields or fields.get("basis") not in BASES or not evidence:
        return None, ("the reconsideration block needs `finding: F<n>`, `basis: " + " | ".join(BASES)
                      + "` and the evidence after them")
    return {"finding": fields["finding"], "basis": fields["basis"], "evidence": evidence}, None


def decide(result: dict | None, reconsidering: bool) -> tuple[str, str]:
    """The outcome a structured review establishes: approve, reject, needs_evidence, escalate, or
    operation (no verdict: the review failed or its output is unusable or inconsistent)."""
    if result is None:
        return "operation", "no review output"
    kinds = {f["kind"] for f in result["findings"]}
    v, recon = result["verdict"], result["reconsideration"]["outcome"]
    if reconsidering and recon == "not_applicable":
        return "operation", "the reviewer did not answer the reconsideration"
    if v == "approve":
        if len(result["criteria"]) < CRITERIA or not all(c["holds"] for c in result["criteria"]):
            return "operation", "an approval with a missing or failing criterion is inconsistent"
        if kinds - {"correction"} or (reconsidering and recon != "withdrawn"):
            return "operation", "an approval with an open finding is inconsistent"
        return "approve", ""
    want = {"reject": {"defect"}, "needs_evidence": {"missing_evidence"},
            "escalate": {"reserved_requirement", "evasion"}, "review_failed": {"review_operation"}}[v]
    if not kinds & want or v == "needs_evidence" and "defect" in kinds:
        return "operation", f"a verdict `{v}` without a matching finding is inconsistent"
    return ("operation", "the reviewer could not complete the review") if v == "review_failed" else (v, "")


def call_reviewer(prompt: Path, inputs: str) -> tuple[dict | None, str]:
    """One Claude Code call with no tools, no settings and no MCP servers: the fixed prompt as the
    system prompt, the assembled inputs as the only input, the verdict as structured output.
    Authenticates with CLAUDE_CODE_OAUTH_TOKEN (the owner's subscription)."""
    # No refusal fallback: a decline is a failed review operation, never a switch to another reviewer.
    r = subprocess.run(
        ["claude", "-p", "--model", MODEL, "--effort", "high", "--tools", "", "--setting-sources", "",
         "--strict-mcp-config", "--no-session-persistence", "--system-prompt-file", str(prompt),
         "--json-schema", json.dumps(SCHEMA), "--output-format", "json"],
        input=inputs, capture_output=True, text=True)
    if r.returncode != 0:
        return None, f"reviewer call failed ({r.returncode}): {(r.stderr or r.stdout).strip()[-500:]}"
    try:
        out = json.loads(r.stdout)
    except ValueError:
        return None, f"reviewer output is not JSON: {r.stdout[:500]}"
    if out.get("is_error") or out.get("subtype") != "success" or "structured_output" not in out:
        return None, f"reviewer stopped: {out.get('subtype')}: {str(out.get('result'))[:500]}"
    return out["structured_output"], ",".join(out.get("modelUsage", {}))


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
    hard, review = classify(problems)
    if hard:
        return finish(1, "FAIL (hard)", hard + ["no review can accept these"])
    reserved = reserved_changes(head, tip, review)
    if reserved:
        return finish(1, "ESCALATE (reserved requirement)", reserved + [
            "an admitted assertion is the accepted mathematical question: only the owner changes it "
            "(custodian/CONTAINMENT.md, \"Escalation\"); no model review can accept this"])
    boundary = V.current_boundary(head, tip)
    key = sha(json.dumps({"tip": chain_head(V, root_path, chain), "files": boundary},
                         sort_keys=True).encode())
    log = load_log(a.rejections, key)
    recon, prior = None, None
    if log:
        prior = log["entries"][-1]
        if prior["outcome"] == "approve":
            return finish(1, "REFUSED (already approved)", [
                f"this exact change was approved after a reconsideration ({key[:16]}): commit the "
                "verdict that run posted"])
        fs = findings_of(prior)
        listing = [f"{f['id']} ({f['kind']}): {f['requirement']} -- {f['evidence']}" for f in fs]
        recon, bad = reconsideration([description(a)] + comments(a))
        if bad:
            return finish(1, "REFUSED (unusable reconsideration)", [bad] + listing)
        if recon is None:
            return finish(1, f"REFUSED (already decided: {prior['outcome']})", [
                f"this exact change was already decided against the same seal ({key[:16]}); it is "
                "reviewed again after a substantive revision, or with a reconsideration naming a "
                "finding below (review.py, \"custodian-reconsideration\")"] + listing)
        if recon["finding"] not in {f["id"] for f in fs}:
            return finish(1, "REFUSED (unusable reconsideration)", [
                f"the reconsideration names {recon['finding']}, which the latest record does not have"] + listing)
        recon["sha256"] = sha(json.dumps([key, recon["finding"], recon["basis"],
                                          " ".join(recon["evidence"].split())]).encode())
        if any((e.get("reconsideration") or {}).get("sha256") == recon["sha256"] for e in log["entries"]):
            return finish(1, "REFUSED (reconsideration already decided)", [
                "this reconsideration was already decided for this change; a different one needs new "
                "evidence, corrected context or an identified error"] + listing)
    sealed = sealed_files(V, review)
    change = change_text(V, base, head, review)
    context, omitted = context_text(V, base, head, sealed)
    owner, digests = controlling(base)
    explanation = description(a)
    facts = ["The sealed changes:"] + [f"- {p}" for p in review] + [f"Change key: {key}"]
    if recon:
        facts += ["", "A reconsideration of this record, by the author (the evidence below is untrusted):",
                  neutral(json.dumps({"outcome": prior["outcome"], "findings": findings_of(prior),
                                      "summary": prior["record"]["result"].get("summary")}, indent=1)),
                  f"It names {recon['finding']} on the basis {recon['basis']}."]
        explanation += "\n\n--- reconsideration evidence ---\n" + recon["evidence"]
    inputs = "".join(f"<{t}>\n{x}\n</{t}>\n\n" for t, x in (
        ("controlling_requirements", owner), ("runner_facts", "\n".join(facts)),
        ("untrusted_change", neutral(change)), ("untrusted_context", neutral(context)),
        ("untrusted_author_explanation", neutral(explanation) or "(none)")))
    prompt = base / "custodian" / "review" / "prompt.md"
    record = {"model": MODEL, "prompt_sha256": sha(prompt.read_bytes()), "change_sha256": sha(change.encode()),
              "inputs_sha256": sha(inputs.encode()), "controlling_sha256": digests,
              "context_omitted": omitted, "change_key": key, "pr": a.pr, "head_sha": a.head_sha,
              "problems": review}
    if len(change) > DIFF_LIMIT:
        result, why = None, (f"the sealed diff is {len(change)} characters, over the runner's bound "
                             f"{DIFF_LIMIT}: the invocation is repaired (custodian/review/review.py); "
                             "the change is not refused for its size")
    else:
        result, why = call_reviewer(prompt, inputs)
    outcome, inconsistent = decide(result, recon is not None)
    record["result"] = result
    record["served_by"] = why if result is not None else None
    fs = findings_of({"record": record}) if result is not None else []
    lines = review + [result["summary"] if result else why]
    if result is not None:
        lines += [f"{'holds' if c['holds'] else 'FAILS'}: {c['criterion']} -- {c['evidence']}"
                  for c in result["criteria"]]
        lines += [f"{f['id']} ({f['kind']}): {f['requirement']} at {f['location']} -- {f['evidence']}"
                  f" -> {f['action']}" for f in fs]
        if recon:
            lines.append(f"reconsideration of {recon['finding']}: {result['reconsideration']['outcome']} "
                         f"-- {result['reconsideration']['reason']}")
    if outcome == "operation":
        return finish(1, "REVIEW FAILED (no verdict; re-reviewable)", lines + [
            inconsistent or why, "nothing is recorded: the same change is reviewed on the next run "
            "once the review operation is repaired"])

    def log_entry() -> None:
        if not a.rejections:
            return
        rec = log or {"key": key, "entries": []}
        rec["entries"].append({"outcome": outcome, "signer": public_fpr(a.signing_key),
                               "record": record, "reconsideration": recon})
        path = a.rejections / f"{key}.json"
        path.write_text(json.dumps(rec, indent=1, sort_keys=True) + "\n")
        sign(V, path, a.signing_key)

    if outcome == "approve":
        if log:
            log_entry()  # the reconsideration is decided; the record keeps the history
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
    log_entry()
    again = ("A substantive revision is reviewed as a new change. To contest a finding without one, add "
             "a `custodian-reconsideration` block naming it (review.py).")
    if outcome == "escalate":
        return finish(1, "ESCALATE", lines + [
            "the reviewer found a reserved-requirement change or evidence of evasion: the owner "
            "decides (custodian/CONTAINMENT.md, \"Escalation\")", again])
    title = "REJECTED (defect)" if outcome == "reject" else "NEEDS EVIDENCE"
    return finish(1, title, lines + [again])


def escalate_mode(a) -> int:
    head = a.head.resolve()
    V = load_verify(head / "custodian" / "verify.py")
    root_path = head / "custodian" / "seal.json"
    V.verify_signature(root_path, Path(str(root_path) + ".sig"), head / "custodian" / "root.pub",
                       a.trusted_fpr)
    root = json.loads(root_path.read_text())
    chain = V.load_chain(head, root_path, root)
    tip = V.tip_seal(root, chain)
    hard, _ = classify(V.check(head, tip))
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
    ap.add_argument("--description", type=Path)
    ap.add_argument("--comments", type=Path)
    ap.add_argument("--escalate", action="store_true")
    ap.add_argument("--signing-key", type=Path, required=True)
    ap.add_argument("--note", default="")
    a = ap.parse_args()
    return escalate_mode(a) if a.escalate else review_mode(a)


if __name__ == "__main__":
    sys.exit(main())
