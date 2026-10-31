#!/usr/bin/env python3
"""Execute an external notebook copy through the existing Jupyter adapter.

The source notebook is never edited. Retain the actual output even if a cell
fails; a missing execution or an error output makes this invocation fail.
"""

import argparse
import traceback

import nbclient
import nbformat


def main():
    from pathlib import Path

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cwd', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('Refuse to replace a prior notebook execution')
    notebook = nbformat.read(args.input, as_version=4)
    client = nbclient.NotebookClient(
        notebook, kernel_name='casdsl', timeout=None, startup_timeout=600,
        allow_errors=False, resources={'metadata': {'path': str(args.cwd)}})
    code = 0
    try:
        client.execute()
    except BaseException:
        traceback.print_exc()
        code = 1
    finally:
        nbformat.write(notebook, args.output)
    cells = [cell for cell in notebook.cells if cell.cell_type == 'code']
    executed = sum(cell.get('execution_count') is not None for cell in cells)
    errors = sum(output.get('output_type') == 'error'
                 for cell in cells for output in cell.get('outputs', []))
    print(f'Notebook: {len(notebook.cells)} cells, {len(cells)} code cells, '
          f'{executed} executed, {errors} error outputs', flush=True)
    return 1 if not cells or executed != len(cells) or errors else code


if __name__ == '__main__':
    raise SystemExit(main())
