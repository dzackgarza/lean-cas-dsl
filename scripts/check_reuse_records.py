#!/usr/bin/env python3
"""Gate: the plan's **Next** node, and every node delivered from 2026-09-30 on, has a reuse record
`specs/reuse/<node>.md` with non-empty `## Queries` and `## Owner` sections (corpus search before
code; AGENTS.md "Search before authoring"). Fails the build otherwise."""
import re, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
plan = (root / "specs/computational-core-plan.md").read_text()
bad = []
for line in plan.splitlines():
    m = re.match(r"^\| `([a-z0-9-]+)` \| (.*)", line)
    if not m:
        continue
    node, rest = m.groups()
    d = re.search(r"\*\*Delivered (\d{4}-\d{2}-\d{2})", rest)
    if "**Next.**" not in rest and not (d and d.group(1) >= "2026-09-30"):
        continue
    rec = root / "specs/reuse" / f"{node}.md"
    if not rec.exists():
        bad.append(f"{node}: no specs/reuse/{node}.md"); continue
    text = rec.read_text()
    for sec in ("Queries", "Owner"):
        body = re.search(rf"^## {sec}\n(.*?)(?=^## |\Z)", text, re.M | re.S)
        if not body or not body.group(1).strip():
            bad.append(f"{node}: empty ## {sec} in specs/reuse/{node}.md")
if bad:
    print("reuse records missing (search the formalization corpus before writing code):")
    print("\n".join("  " + b for b in bad)); sys.exit(1)
