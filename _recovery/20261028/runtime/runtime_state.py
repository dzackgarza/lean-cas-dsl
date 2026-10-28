"""External source/provenance helpers reconstructed after the workspace reset."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

RUNTIME = Path(__file__).resolve().parent
KERNEL = RUNTIME.parents[1] / "lean-cas-dsl-kernel"
EVIDENCE = RUNTIME / "evidence"
TOOLCHAIN = RUNTIME / "toolchains/lean-4.33.0-linux"


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def record(path):
    path = Path(path)
    return {"path": str(path), "sha256": sha256(path), "bytes": path.stat().st_size}


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def environment():
    result = dict(os.environ)
    result["PATH"] = str(TOOLCHAIN / "bin") + os.pathsep + result["PATH"]
    result["MATHLIB_CACHE_DIR"] = str(RUNTIME / "mathlib-cache")
    result["GIT_OPTIONAL_LOCKS"] = "0"
    result["GIT_TERMINAL_PROMPT"] = "0"
    return result


def git(path, *args):
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(path), *args],
        env=environment(), text=True).strip()


def selected_packages():
    return {row["name"]: Path(row["dir"]).resolve() for row in
            json.loads((RUNTIME / "packages.json").read_text())["packages"]}


def source_roots():
    return {"kernel": KERNEL, **selected_packages()}


def source_state():
    result = {}
    for name, selected in source_roots().items():
        root = Path(git(selected, "rev-parse", "--show-toplevel"))
        changed = subprocess.check_output(
            ["git", "--no-optional-locks", "-C", str(root), "diff", "--name-only", "-z", "HEAD"],
            env=environment()).decode().split("\0")
        untracked = subprocess.check_output(
            ["git", "--no-optional-locks", "-C", str(root), "ls-files", "--others", "--exclude-standard", "-z"],
            env=environment()).decode().split("\0")
        hashes = {}
        for relative in sorted(set(changed + untracked) - {""}):
            path = root / relative
            hashes[relative] = sha256(path) if path.is_file() else None
        result[name] = {
            "selectedDirectory": str(selected), "repository": str(root),
            "commit": git(root, "rev-parse", "HEAD"),
            "tree": git(root, "rev-parse", "HEAD^{tree}"),
            "status": git(root, "status", "--porcelain"),
            "changedFileSha256": hashes,
        }
    return result


def owned_sources():
    roots = {"kernel": KERNEL, "contract": selected_packages()["cas_leaf_contracts"]}
    result = {}
    for label, root in roots.items():
        for path in sorted(root.rglob("*.lean")):
            relative = path.relative_to(root)
            if relative.parts[0].startswith("Cas"):
                result[label + ":" + str(relative)] = sha256(path)
    return result


def configuration():
    paths = [RUNTIME / name for name in (
        "packages.json", "lake.sh", "runtime_state.py", "focused_build.py",
        "artifact_consistency.py", "artifact_hash.lean")]
    paths += [KERNEL / "lake-manifest.json", KERNEL / "lean-toolchain"]
    return {str(path): record(path) for path in paths if path.is_file()}
