"""Re-execute notebooks/demo.ipynb against the live casdsl kernel.

Mirrors the a23ee30 standard: every code cell's outputs must be genuine
kernel output. allow_errors=True so the notebook's two DELIBERATE error
cells (bad syntax lesson, NoImplementation refusal) are recorded as error
outputs instead of aborting the run.
"""

import sys
from pathlib import Path

import nbclient
import nbformat

NB = Path("notebooks/demo.ipynb")


def main() -> int:
    nb = nbformat.read(NB, as_version=4)
    client = nbclient.NotebookClient(
        nb,
        kernel_name="casdsl",
        timeout=300,
        allow_errors=True,
    )
    client.execute()
    nbformat.write(nb, NB)

    # report
    code = [c for c in nb.cells if c.cell_type == "code"]
    counts = [c.get("execution_count") for c in code]
    execd = sum(1 for n in counts if n is not None)
    otypes: dict[str, int] = {}
    errors: list[tuple[int, str]] = []
    for i, c in enumerate(code):
        for o in c.outputs:
            otypes[o.output_type] = otypes.get(o.output_type, 0) + 1
        for o in c.outputs:
            if o.output_type == "error":
                errors.append((i, f"{o.ename}: {o.evalue}"[:120]))
    print(
        f"code cells: {len(code)}, executed: {execd}, unexecuted: {len(code) - execd}"
    )
    print("output types:", otypes)
    print("error cells:", len(errors))
    for i, msg in errors:
        print(f"  cell {i}: {msg}")
    return 0 if execd == len(code) else 1


if __name__ == "__main__":
    sys.exit(main())
