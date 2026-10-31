"""Check that provenance labels do not change a production mathematical identity.

Run from a built kernel checkout with its complete LEAN_PATH and an optional Lean
executable argument. Both isolated processes import the same compiled modules.
Only a copied manifest's revision label differs. No admission baseline, source
dependency, leaf, mathematical expected answer, or actual manifest is modified.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


PROBE = """module
import CasCatalogue.Realize
meta import CasCatalogue.Realize
open Lean Elab Command Term
open CasCatalogue CasCatalogue.Realize

run_cmd liftTermElabM do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt "assert Fin(2) in Sets"
    | throwError "the provenance fixture did not parse"
  let question ← interpret {} parsed
  IO.println <| (Json.mkObj [("identity", toJson question.identity.1),
    ("revision", toJson question.mathematicalRevision)]).compress
"""


def observe(lean: str, manifest: dict, revision: str, directory: Path) -> dict:
    directory.mkdir()
    changed = json.loads(json.dumps(manifest))
    mathematics = [p for p in changed["packages"] if p["name"] == "lean_categories"]
    if len(mathematics) != 1:
        raise RuntimeError("the fixture requires exactly one mathematical dependency")
    mathematics[0]["rev"] = revision
    (directory / "lake-manifest.json").write_text(json.dumps(changed), encoding="utf-8")
    source = directory / "QuestionProvenance.lean"
    source.write_text(PROBE, encoding="utf-8")
    result = subprocess.run(
        [lean, str(source)], cwd=directory, env=os.environ.copy(),
        text=True, capture_output=True, check=True,
    )
    observations = []
    for line in result.stdout.splitlines():
        try:
            observation = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(observation, dict) and set(observation) == {"identity", "revision"}:
            observations.append(observation)
    if len(observations) != 1:
        raise RuntimeError(f"the production probe emitted no unique observation: {result.stdout}")
    return observations[0]


def main() -> None:
    lean = sys.argv[1] if len(sys.argv) == 2 else "lean"
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    manifest = json.loads(Path("lake-manifest.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory(prefix="cas-question-provenance-") as temporary:
        root = Path(temporary)
        first = observe(lean, manifest, "provenance-mechanics-first", root / "first")
        second = observe(lean, manifest, "provenance-mechanics-second", root / "second")
    if first["identity"] != second["identity"]:
        raise AssertionError("a revision label changed the unchanged typed question's identity")
    if first["revision"] == second["revision"]:
        raise AssertionError("the interpreted question lost its separate source provenance")
    print("PASS: production question identity is independent of its retained revision label")


if __name__ == "__main__":
    main()
