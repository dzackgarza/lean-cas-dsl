#!/usr/bin/env python3
"""Check that the roadmap and reuse records point to their owning issues.

This validates navigation only. Research evidence and work decisions live in the
issues; this check does not assess research quality or certify completion.
"""
import importlib.util
from pathlib import Path
import sys

root = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('issue_context', root / 'custodian/issue_requirements.py')
context = importlib.util.module_from_spec(spec)
spec.loader.exec_module(context)
records = sorted((root / 'specs/reuse').glob('*.md'))
paths = [root / 'specs/computational-core-plan.md', *records]
bad = []
if not records:
    bad.append('no reuse pointers found in specs/reuse')
for path in paths:
    if not path.is_file() or not context.issue_numbers(path.read_text()):
        bad.append(str(path.relative_to(root)) + ': missing owning issue pointer')
if bad:
    print('issue pointers missing:', file=sys.stderr)
    print('\n'.join('  ' + item for item in bad), file=sys.stderr)
    raise SystemExit(1)
print(f'Checked {len(paths)} roadmap and reuse issue pointers.')
