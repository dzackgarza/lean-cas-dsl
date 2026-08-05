"""Re-execute the committed notebooks against the live casdsl kernel.

Two standards enforced together:
- a23ee30: every code cell's committed outputs are genuine kernel output,
  never hand-written;
- the runnable-trail rule (owner, 2026-08-06): the document model refuses
  to build on a failed cell, so NO committed notebook may contain a live
  error cell — deliberate refusals ship commented out, catalogued in
  notebooks/boundaries.ipynb. Any error output fails this gate loudly.
"""

import sys
from pathlib import Path

import nbclient
import nbformat

NOTEBOOKS = [Path("notebooks/demo.ipynb"), Path("notebooks/boundaries.ipynb")]


def reexec(path: Path) -> int:
    nb = nbformat.read(path, as_version=4)
    client = nbclient.NotebookClient(
        nb,
        kernel_name="casdsl",
        timeout=300,
        allow_errors=False,
    )
    try:
        client.execute()
    except nbclient.exceptions.CellExecutionError as exc:
        print(f"{path}: FAILED — a cell errored, which the runnable-trail "
              f"rule forbids (comment the offending line or move it to "
              f"boundaries.ipynb):\n{exc}")
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
    return 0 if execd == len(code) else 1


def main() -> int:
    return max(reexec(p) for p in NOTEBOOKS)


if __name__ == "__main__":
    sys.exit(main())
