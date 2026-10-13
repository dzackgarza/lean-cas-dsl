"""Re-execute the committed notebooks against the live casdsl kernel.

Standards enforced (owner rulings, 2026-08-06, recorded in the vault):
- a23ee30: every code cell's committed outputs are genuine kernel output,
  never hand-written;
- the runnable-trail rule: the document model refuses to build on a failed
  cell, so the DEMO may contain no live error cell — any error there fails
  this gate loudly (deliberate refusals ship commented, with live anchors);
- refusals are not notebook content: they are checked at build time
  (CasDslTests.Boundary), and the demo's cells are also built as
  CasDslTests.Cells from the same generator (scripts/demo_notebook.py).

The kernel's worker resolves its environment with `lake`, so elan's bin
directory is put on PATH here.
"""

import os
import sys
from pathlib import Path

import nbclient
import nbformat

# (path, errors allowed?)
NOTEBOOKS = [
    (Path("notebooks/demo.ipynb"), False),
]


def reexec(path: Path, allow_errors: bool) -> int:
    nb = nbformat.read(path, as_version=4)
    client = nbclient.NotebookClient(
        nb,
        kernel_name="casdsl",
        timeout=300,
        allow_errors=allow_errors,
    )
    try:
        client.execute()
    except nbclient.exceptions.CellExecutionError as exc:
        print(f"{path}: FAILED — a cell errored, which the runnable-trail "
              f"rule forbids here (comment the offending line, or move it "
              f"to boundaries.ipynb):\n{exc}")
        return 1
    nbformat.write(nb, path)

    code = [c for c in nb.cells if c.cell_type == "code"]
    execd = sum(1 for c in code if c.get("execution_count") is not None)
    otypes: dict[str, int] = {}
    for c in code:
        for o in c.outputs:
            otypes[o.output_type] = otypes.get(o.output_type, 0) + 1
    print(f"{path}: code cells: {len(code)}, executed: {execd}, "
          f"output types: {otypes}")
    if allow_errors and otypes.get("error", 0) == 0:
        print(f"{path}: SUSPECT — the refusal catalogue produced no error "
              f"output; its demonstrations have gone stale")
        return 1
    return 0 if execd == len(code) else 1


def main() -> int:
    elan = str(Path.home() / ".elan" / "bin")
    os.environ["PATH"] = elan + os.pathsep + os.environ.get("PATH", "")
    return max(reexec(p, allow) for p, allow in NOTEBOOKS)


if __name__ == "__main__":
    sys.exit(main())
