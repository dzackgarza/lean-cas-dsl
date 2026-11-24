#!/usr/bin/env python3
"""Exercise the actual notebook worker and CAS session, not a substitute executor.

The integer statements and SDK peer are the original ScopedDeclarationTests controls.
Run against the built CasDsl.Notebook prelude with the installed notebook adapter.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import tempfile

from nbdsl_kernel.protocol import InspectOk
from nbdsl_kernel.worker.client import WorkerClient


def retained_integer(client: WorkerClient, name: str, expected: int, snapshot: int) -> dict[str, object]:
    """Check the actual frozen binding and value, without executing a query."""
    reply = client.inspect(name, len(name), snapshot=snapshot)
    assert isinstance(reply, InspectOk) and reply.found, reply
    assert reply.name == name and reply.details is not None, reply
    details = reply.details
    binding = details["binding"]
    assert isinstance(binding, dict), details
    runtime = details["runtime"]
    assert isinstance(runtime, dict) and runtime["hasPacket"], details
    assert runtime["packet"] == expected, details
    assert isinstance(runtime["reference"], dict), details
    assert isinstance(details["source"], dict), details
    assert isinstance(details["candidates"], list), details
    return details


def require_routines(details: dict[str, object], expected: set[tuple[str, str]]) -> None:
    """The committed receipt, not the registration name, supplies the actual routines."""
    runtime = details["runtime"]
    assert isinstance(runtime, dict)
    completions = runtime["completions"]
    assert isinstance(completions, list)
    actual: list[tuple[str, str]] = []
    for completion in completions:
        producer = completion["producer"]
        if producer["kind"] == "kernel":
            assert not completion["routines"], completion
            continue
        assert len(completion["routines"]) == 1, completion
        frame = completion["routines"][0]
        for key in ("connection", "occurrence", "requestId"):
            assert frame[key] == producer[key], completion
        observations = frame["observations"]
        assert len(observations) == 1, frame
        routine = observations[0]
        assert routine["role"] == "entrypoint", routine
        assert routine["code_sha256"] and len(routine["code_sha256"]) == 64, routine
        actual.append((producer["target"]["operation"], routine["qualified_name"]))
    assert len(actual) == len(expected) and set(actual) == expected, actual


def run(root: Path, contract: Path) -> None:
    python = contract / ".venv/bin/python"
    assert python.is_file(), python
    peer = root / "scripts/probes/kernel_session_peer.py"
    with tempfile.TemporaryDirectory(prefix="cas-notebook-cell-") as directory:
        manifest = Path(directory) / "leaves.json"
        manifest.write_text(json.dumps({
            "backends": [{"name": "peer", "command": str(python), "args": [str(peer)]}],
            "registrations": [
                {"operation": op, "input": op + "#input", "backend": "peer"}
                for op in ("op.rings.add", "op.rings.mul")
            ],
        }))
        previous = os.environ.get("CAS_LEAVES")
        os.environ["CAS_LEAVES"] = str(manifest)
        client = WorkerClient(root, prelude="CasDsl.Notebook",
                              on_stream=lambda stream, line: print(f"[{stream}] {line}", end="", flush=True))
        try:
            print("Importing and negotiating CasDsl.Notebook", flush=True)
            ready = client.start()
            print("Negotiated", flush=True)
            nonce = ready.worker_nonce
            assert ready.protocol == 2 and nonce
            assert ready.snapshot == 0
            parent = client.execute('#cas "let outer := 17 + 29 in ℤ"', "parent")
            assert parent.status == "ok", parent
            assert parent.commit is not None
            assert parent.outputs and parent.commit.result_refs
            assert parent.worker_nonce == nonce
            committed = parent.snapshot
            assert committed is not None
            outer = retained_integer(client, "outer", 46, committed)
            require_routines(outer, {("op.rings.add", "add")})
            print("Parent committed with frozen integer observation", flush=True)

            staged = client.execute_at(
                '#cas "let localSum := outer + 1 in ℤ"\n'
                '#cas "let localProduct := localSum · 2 in ℤ"\n'
                '#cas "assert localProduct = 94 in ℤ"',
                "staged", committed,
            )
            assert staged.status == "ok", staged
            assert staged.commit is not None and staged.commit.result_refs
            assert len(staged.outputs) == 3, staged
            assert staged.parent_snapshot == committed
            assert staged.snapshot != committed
            assert staged.commit.transaction_id != parent.commit.transaction_id
            assert staged.commit.output_batch_id != parent.commit.output_batch_id
            assert len({item.result_id for item in staged.outputs}) == 3
            assert staged.snapshot is not None
            retained_integer(client, "localSum", 47, staged.snapshot)
            product = retained_integer(client, "localProduct", 94, staged.snapshot)
            require_routines(product, {("op.rings.mul", "multiply"), ("op.rings.add", "add")})
            assert retained_integer(client, "outer", 46, staged.snapshot)["binding"] == outer["binding"]
            print("Multi-command cell committed with retained values", flush=True)

            rolled_back = client.execute_at(
                '#cas "let temporary := outer + 3 in ℤ"\n'
                '#cas "assert neverDeclaredHere = 0 in ℤ"',
                "rollback", staged.snapshot,
            )
            assert rolled_back.status == "error", rolled_back
            assert rolled_back.snapshot == staged.snapshot
            assert rolled_back.commit is None and not rolled_back.outputs
            assert rolled_back.stratum == "invalid", rolled_back
            hidden = client.inspect("temporary", len("temporary"))
            assert hidden.status == "ok" and not hidden.found, hidden
            assert retained_integer(client, "localProduct", 94, staged.snapshot) == product
            print("Failed cell preserved the committed observation", flush=True)

            reuse = client.execute_at(
                '#cas "assert localProduct = 94 in ℤ"', "reuse", staged.snapshot,
            )
            assert reuse.status == "ok", reuse
            assert reuse.commit is not None
            old_branch = client.execute_at(
                '#cas "assert outer = 46 in ℤ"', "older-parent", committed,
            )
            assert old_branch.status == "ok", old_branch
            assert old_branch.snapshot != reuse.snapshot
            assert old_branch.snapshot is not None
            assert retained_integer(client, "outer", 46, old_branch.snapshot)["binding"] == outer["binding"]
            missing = client.inspect("localProduct", len("localProduct"))
            assert missing.status == "ok" and not missing.found, missing
            assert retained_integer(client, "localProduct", 94, staged.snapshot) == product
            lost = client.execute_at(
                '#cas "assert localProduct = 94 in ℤ"', "missing-branch", old_branch.snapshot,
            )
            assert lost.status == "error" and lost.snapshot == old_branch.snapshot, lost
            assert lost.commit is None and not lost.outputs
            print("Notebook cell boundary: actual staging, commit, rollback, reuse and branching passed")
        finally:
            client.shutdown()
            if previous is None:
                os.environ.pop("CAS_LEAVES", None)
            else:
                os.environ["CAS_LEAVES"] = previous


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--contract", type=Path, required=True)
    args = parser.parse_args()
    run(args.root.resolve(), args.contract.resolve())
