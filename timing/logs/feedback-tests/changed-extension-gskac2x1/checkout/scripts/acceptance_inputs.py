#!/usr/bin/env python3
"""Resolve complete public suite inputs without admitting extension observations."""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from check_acceptance_permanent import MANIFEST, suite_assertions

ACCEPTANCE = Path("tests/acceptance")
EXTENSIONS = ACCEPTANCE / "proposals/independent-extension-reconstruction-20261024/completion"
CHECKPOINT = EXTENSIONS / "source-checkpoint.json"
# These complete source files and their checkpoint entered this history together.
# This is input provenance, not a regenerated outcome or assertion baseline.
SOURCE_REVISION = "9a640af2d2c5910dc0aed1e60eaaf0c9e4c4b1df"
ADDED_EXTENSIONS = {
    "rx02-complete-core-action", "rx03-complete-automorphism-arrows",
    "rx-lift-source-comparison",
}
STEM = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]*")


def parse_selection(arguments: list[str]) -> tuple[str | None, list[dict]]:
    """Resolve names only; the same paths feed preflight, execution and timing."""
    manifest = None
    selected = []
    remaining = iter(arguments)
    for argument in remaining:
        extension = argument == "--extension"
        if argument == "--manifest":
            if manifest is not None:
                raise ValueError("select one manifest")
            manifest = next(remaining, None)
            if manifest is None or manifest.startswith("--"):
                raise ValueError("--manifest requires its original file")
            continue
        if argument == "--all":
            selected.extend({"stem": path.stem, "source": str(path), "kind": "admitted",
                             "key": path.stem} for path in sorted(ACCEPTANCE.glob("*.cas")))
            continue
        stem = next(remaining, None) if extension else argument
        if stem is None or STEM.fullmatch(stem) is None:
            raise ValueError("--extension requires a completion stem" if extension
                             else f"not an acceptance stem: {stem}")
        directory = EXTENSIONS if extension else ACCEPTANCE
        selected.append({"stem": stem, "source": str(directory / f"{stem}.cas"),
                         "kind": "extension" if extension else "admitted",
                         "key": f"extension--{stem}" if extension else stem})
    paths = [item["source"] for item in selected]
    keys = [item["key"] for item in selected]
    if len(set(paths)) != len(paths) or len(set(keys)) != len(keys):
        raise ValueError("select each complete source file once")
    return manifest, selected


def original_blob(path: Path) -> bytes:
    return subprocess.check_output(["git", "show", f"{SOURCE_REVISION}:{path}"])


def checked_input(selected: dict) -> dict:
    """Check the original authority before deriving a completeness-only inventory."""
    source = Path(selected["source"])
    if not source.is_file():
        raise ValueError(f"no {selected['kind']} file {source}")
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if selected["kind"] == "extension":
        original = original_blob(CHECKPOINT)
        if CHECKPOINT.read_bytes() != original:
            raise ValueError(f"extension source checkpoint changed: {CHECKPOINT}")
        checkpoint = json.loads(original)["completion_file_sha256"]
        if source.name in checkpoint:
            expected = checkpoint[source.name]
            authority = {"kind": "source-checkpoint", "file": str(CHECKPOINT),
                         "revision": SOURCE_REVISION,
                         "checkpoint_sha256": hashlib.sha256(original).hexdigest()}
        elif selected["stem"] in ADDED_EXTENSIONS:
            data = original_blob(source)
            expected = hashlib.sha256(data).hexdigest()
            authority = {"kind": "added-blob", "revision": SOURCE_REVISION,
                         "blob": subprocess.check_output(
                             ["git", "rev-parse", f"{SOURCE_REVISION}:{source}"],
                             text=True).strip()}
        else:
            raise ValueError(f"no original completion source authority for {source}")
        if digest != expected:
            raise ValueError(f"extension source changed: {source}; "
                             f"expected sha256 {expected}, received {digest}")
        assertions = suite_assertions([source])
        return {**selected, "sha256": digest, "authority": authority,
                "admitted": False, "computing": True, "assertions": assertions}
    admitted = json.loads(MANIFEST.read_text())["assertions"]
    assertions = suite_assertions([source])
    if not assertions:
        raise ValueError(f"no named assertions in {source}")
    for identity, digest_ in assertions.items():
        if admitted.get(identity) != digest_:
            raise ValueError(f"selected assertion is not the unchanged admitted input: {identity}")
    return {**selected, "sha256": digest,
            "authority": {"kind": "admitted-assertions", "file": str(MANIFEST)},
            "admitted": True, "computing": False, "assertions": assertions}


def main() -> int:
    if len(sys.argv) < 2:
        raise SystemExit("usage: acceptance_inputs.py OUTPUT [--manifest FILE] "
                         "[STEM | --extension STEM | --all] ...")
    output = Path(sys.argv[1])
    manifest, selected = parse_selection(sys.argv[2:])
    if not selected:
        raise ValueError("select at least one complete source file")
    document = {"manifest": manifest, "files": selected, "complete": False}
    output.write_text(json.dumps(document, ensure_ascii=False, indent=2) + "\n")
    checked = []
    for item in selected:
        checked.append(checked_input(item))
        document["files"] = checked + selected[len(checked):]
        output.write_text(json.dumps(document, ensure_ascii=False, indent=2) + "\n")
    document["complete"] = True
    output.write_text(json.dumps(document, ensure_ascii=False, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, FileNotFoundError, KeyError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error))
