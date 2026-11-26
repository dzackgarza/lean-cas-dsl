#!/usr/bin/env python3
"""Preserve an owned feedback checkout as ordinary source and diagnostic files.

The literal Git metadata retains its original external-store dependencies.
Queried authority blobs are also retained directly; unrelated history is neither
exported nor repaired. A missing-object inventory records the observed state.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import tarfile
import tempfile
import time

from feedback_records import atomic_json

OID = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})")


def _hash(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def _inventory(root: Path, *, worktree: bool = False) -> dict:
    result = {}
    for directory, names, files in os.walk(root, followlinks=False):
        if worktree and Path(directory) == root:
            names[:] = [name for name in names if name != ".git"]
            files = [name for name in files if name != ".git"]
        for name in sorted(names + files):
            path = Path(directory) / name
            info = path.lstat()
            entry = {"mode": stat.S_IMODE(info.st_mode), "mtime_ns": info.st_mtime_ns}
            if stat.S_ISREG(info.st_mode):
                entry.update(kind="file", size=info.st_size, sha256=_hash(path))
            elif stat.S_ISDIR(info.st_mode):
                entry.update(kind="directory")
            elif stat.S_ISLNK(info.st_mode) and worktree:
                entry.update(kind="symlink", target=os.readlink(path))
            else:
                raise ValueError(f"unsupported evidence entry: {path}")
            result[path.relative_to(root).as_posix()] = entry
    return result


def _git(checkout: Path, *arguments: str, gitdir: Path | None = None,
         input: bytes | None = None) -> bytes:
    environment = dict(os.environ)
    for name in ("GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
                 "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES"):
        environment.pop(name, None)
    environment.update(GIT_OPTIONAL_LOCKS="0", GIT_NO_LAZY_FETCH="1")
    command = ["git", "--no-optional-locks", "--git-dir", str(gitdir or checkout / ".git"),
               "--work-tree", str(checkout), *map(str, arguments)]
    result = subprocess.run(command, input=input, capture_output=True, env=environment)
    if result.returncode:
        raise RuntimeError(f"{command!r} exited {result.returncode}:\n"
                           f"{result.stderr.decode(errors='replace')}")
    return result.stdout


def _state(checkout: Path, revision: str, gitdir: Path | None = None) -> dict:
    rows = _git(checkout, "rev-list", "--objects", "--no-object-names",
                "--missing=print", "--all", "--reflog", "--indexed-objects",
                "HEAD", revision, gitdir=gitdir).decode().splitlines()
    if any(OID.fullmatch(row.removeprefix("?")) is None for row in rows):
        raise ValueError("Git returned an invalid object inventory")
    directory = gitdir or checkout / ".git"
    return {
        "head": _git(checkout, "rev-parse", "HEAD", gitdir=gitdir).decode().strip(),
        "refs": _git(checkout, "for-each-ref",
                     "--format=%(objectname) %(refname) %(symref)", gitdir=gitdir).decode(),
        "index_sha256": _hash(directory / "index") if (directory / "index").exists() else None,
        "status_porcelain_v1_z_base64": base64.b64encode(
            _git(checkout, "status", "--porcelain=v1", "-z", "--untracked-files=all",
                 gitdir=gitdir)).decode(),
        "available_reachable_objects": sorted({row for row in rows if not row.startswith("?")}),
        "missing_reachable_objects": sorted({row[1:] for row in rows if row.startswith("?")}),
    }


def _extract(evidence: Path, destination: Path, document: dict, *, worktree: bool = False) -> Path:
    root_name = "worktree" if worktree else ".git"
    archive_name = "worktree.tar.gz" if worktree else "metadata.tar.gz"
    entries = document["worktree" if worktree else "git_metadata"]
    with tarfile.open(evidence / archive_name, "r:gz") as archive:
        for entry in archive.getmembers():
            path = PurePosixPath(entry.name)
            if (not path.parts or path.parts[0] != root_name or ".." in path.parts
                    or not (entry.isfile() or entry.isdir() or (worktree and entry.issym()))):
                raise ValueError(f"invalid checkout evidence archive: {archive_name}")
        archive.extractall(destination, filter="data")
    restored = destination / root_name
    restored.mkdir(exist_ok=True)
    # Restore modes/times stripped by the safe extraction filter, then compare
    # every original metadata file, including HEAD, config, index and alternates.
    for name, entry in sorted(entries.items(),
                              key=lambda item: len(Path(item[0]).parts), reverse=True):
        path = restored / name
        if entry["kind"] != "symlink":
            os.chmod(path, entry["mode"])
        os.utime(path, ns=(entry["mtime_ns"], entry["mtime_ns"]), follow_symlinks=False)
    if _inventory(restored, worktree=worktree) != entries:
        raise ValueError(f"restored checkout evidence differs: {archive_name}")
    return restored


def _verify(evidence: Path, document: dict) -> None:
    for name, digest in document["artifacts"].items():
        if _hash(evidence / name) != digest:
            raise ValueError(f"damaged retained evidence: {name}")
    with tempfile.TemporaryDirectory(prefix="verify-", dir=evidence) as temporary:
        restored = _extract(evidence, Path(temporary), document, worktree=True)
        gitdir = _extract(evidence, restored, document)
        if _state(restored, document["authority_revision"], gitdir) != document["git_state"]:
            raise ValueError("restored metadata does not reproduce the recorded Git state")
        for name, entry in document["authority_inputs"].items():
            data = (evidence / "authority" / name).read_bytes()
            if (_git(restored, "hash-object", "--stdin", gitdir=gitdir, input=data).decode().strip()
                    != entry["object"]):
                raise ValueError(f"retained authority object identity differs: {name}")
            if _git(restored, "show", f"{document['authority_revision']}:{name}", gitdir=gitdir) != data:
                raise ValueError(f"restored authority query differs: {name}")


def retain_checkout(checkout: Path, revision: str, paths: list[str]) -> Path:
    """Finalize a quiescent owned clone after verifying all retained evidence."""
    checkout = checkout.resolve()
    if (not (checkout / ".git").is_dir() or (checkout / ".git").is_symlink()
            or OID.fullmatch(revision) is None or not paths or len(set(paths)) != len(paths)):
        raise ValueError("supply an owned standalone clone and its exact queried authority")
    common = _git(checkout, "rev-parse", "--git-common-dir").decode().strip()
    if Path(common).resolve() != (checkout / ".git").resolve():
        raise ValueError("a linked worktree is not an owned execution clone")
    evidence = Path(tempfile.mkdtemp(prefix=f"{checkout.name}-evidence-", dir=checkout.parent))
    document = {"schema": 1, "state": "started", "checkout": str(checkout),
                "authority_revision": revision, "started_ns": time.time_ns()}
    atomic_json(evidence / "manifest.json", document)
    retirement_started = False
    try:
        document.update(git_metadata=_inventory(checkout / ".git"),
                        worktree=_inventory(checkout, worktree=True),
                        git_state=_state(checkout, revision), authority_inputs={})
        document["external_object_stores"] = {
            name: (checkout / ".git/objects/info" / name).read_text()
            for name in ("alternates", "http-alternates")
            if (checkout / ".git/objects/info" / name).exists()}
        authority = {}
        for name in paths:
            path = PurePosixPath(name)
            if path.is_absolute() or not path.parts or ".." in path.parts:
                raise ValueError(f"not a repository authority path: {name}")
            value = _git(checkout, "show", f"{revision}:{name}")
            oid = _git(checkout, "rev-parse", "--verify", f"{revision}:{name}").decode().strip()
            if OID.fullmatch(oid) is None:
                raise ValueError("Git returned an invalid authority blob identity")
            authority[name] = value
            document["authority_inputs"][name] = {
                "object": oid, "sha256": hashlib.sha256(value).hexdigest(), "size": len(value)}
        entries = [*document["git_metadata"].values(), *document["worktree"].values()]
        archive_bytes = sum(entry.get("size", 0) for entry in entries)
        # Account for archive headers, extraction, JSON journals and source blobs.
        required = (4 * archive_bytes + 8192 * len(entries)
                    + 2 * len(json.dumps(document).encode())
                    + sum(map(len, authority.values())) + 1048576)
        document["space_check"] = {"metadata_and_worktree_bytes": archive_bytes,
                                  "authority_bytes": sum(map(len, authority.values())),
                                  "required_free_bytes": required,
                                  "available_bytes": shutil.disk_usage(checkout).free}
        atomic_json(evidence / "manifest.json", document)
        if document["space_check"]["available_bytes"] < required:
            raise RuntimeError("insufficient space for verified checkout evidence")
        with tarfile.open(evidence / "metadata.tar.gz", "w:gz", dereference=True) as archive:
            archive.add(checkout / ".git", arcname=".git")
        with tarfile.open(evidence / "worktree.tar.gz", "w:gz") as archive:
            for path in sorted(checkout.iterdir()):
                if path.name != ".git":
                    archive.add(path, arcname=f"worktree/{path.name}")
        for name, value in authority.items():
            target = evidence / "authority" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(value)
        document["artifacts"] = {
            path.relative_to(evidence).as_posix(): _hash(path)
            for path in evidence.rglob("*")
            if path.is_file() and path != evidence / "manifest.json"}
        _verify(evidence, document)
        if (_inventory(checkout / ".git") != document["git_metadata"]
                or _inventory(checkout, worktree=True) != document["worktree"]
                or _state(checkout, revision) != document["git_state"]):
            raise ValueError("the execution checkout changed during finalization")
        document.update(state="verified", verified_ns=time.time_ns())
        atomic_json(evidence / "manifest.json", document)
        for path in evidence.rglob("*"):
            if path.is_file():
                with path.open("rb") as stream:
                    os.fsync(stream.fileno())
        descriptor = os.open(evidence, os.O_RDONLY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        # All working-tree source/log bytes stay in place. Only the verified,
        # archived execution metadata is retired, so Git sees ordinary evidence.
        retirement_started = True
        shutil.rmtree(checkout / ".git")
        document.update(state="retained", finished_ns=time.time_ns())
        atomic_json(evidence / "manifest.json", document)
        return evidence
    except BaseException as failure:
        document.update(state="retirement-failed" if retirement_started else "failed",
                        finished_ns=time.time_ns(),
                        error=f"{type(failure).__name__}: {failure}")
        atomic_json(evidence / "manifest.json", document)
        raise


def restore_checkout(evidence: Path, destination: Path) -> None:
    """Restore tested files and literal metadata, including its external dependencies."""
    evidence = evidence.resolve()
    document = json.loads((evidence / "manifest.json").read_text())
    if (document["schema"] != 1
            or document["state"] not in ("verified", "retained", "retirement-failed")
            or "verified_ns" not in document):
        raise ValueError("the checkout archive was not verified")
    _verify(evidence, document)
    if destination.exists():
        raise ValueError("restore only into a new destination")
    with tempfile.TemporaryDirectory(prefix="restore-", dir=destination.parent) as temporary:
        restored = _extract(evidence, Path(temporary), document, worktree=True)
        _extract(evidence, restored, document)
        restored.rename(destination)
    if (_inventory(destination, worktree=True) != document["worktree"]
            or _state(destination, document["authority_revision"]) != document["git_state"]):
        raise ValueError("restored checkout differs from the recorded execution")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("retain", "restore"))
    parser.add_argument("path", type=Path)
    parser.add_argument("--authority-revision")
    parser.add_argument("--authority-path", action="append", default=[])
    parser.add_argument("--destination", type=Path)
    arguments = parser.parse_args()
    if arguments.action == "restore":
        if arguments.destination is None:
            parser.error("restore requires --destination")
        restore_checkout(arguments.path, arguments.destination)
    else:
        if not arguments.authority_revision or not arguments.authority_path:
            parser.error("supply the exact authority revision and queried paths")
        result = retain_checkout(arguments.path, arguments.authority_revision, arguments.authority_path)
        print(json.dumps({"evidence": str(result)}))


if __name__ == "__main__":
    main()
