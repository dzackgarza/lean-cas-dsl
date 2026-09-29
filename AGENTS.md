# Search before authoring (gate-enforced)

Before writing any Lean definition for a plan node, search the formalization corpus
(`python <lean-categories>/scripts/formalization_corpus.py search '<query>'`, several spellings;
it indexes Mathlib, infinity-cosmos, agda-categories and more) and write
`specs/reuse/<node>.md` with `## Queries`, `## Owner` (the existing declarations that own the
mathematics), and `## New code` (only what no dependency supplies). `just build` runs
`scripts/check_reuse_records.py` and fails when the plan's **Next** node, or a node delivered from
2026-09-30 on, has no such record. Categories, functors, natural transformations, whiskering,
pasting, adjunctions and limits are Mathlib's (`Cat` is a strict bicategory; `CatCommSq`,
`TwoSquare`); never write a second calculus of them. Failure of record: `cc-cells`, 2026-09-29.

<!-- agent-memory:start -->
# Agent memory

This repository uses the central agent memory vault at `/home/dzack/.agent-memory-vault`.

Project memory key: `projects/github.com__dzackgarza__lean-cas-dsl/index`.

Repository `.agents` and `.hermes` paths are symlinks to the same vault-owned project directory.

Before changing architecture, search both project and global memory:

```bash
agent-memory search --scope both "<task or subsystem>"
```

Record durable repo-specific lessons with:

```bash
agent-memory add --scope project --type decision --title <title> --content <content>
agent-memory add --scope project --type trap --title <title> --content <content>
agent-memory add --scope project --type advice --title <title> --content <content>
agent-memory add --scope project --type context --title <title> --content <content>
agent-memory add --scope project --type reference --title <title> --content <content>
```

Plan work is card-backed. Create and update plan cards with `agent-memory plan add` and `agent-memory plan update`, not `agent-memory add --type plan`.

Use `agent-memory retrieve <key>`, `agent-memory update <key>`, and `agent-memory delete <key>` for memory CRUD.

The vault should be committed at all times. Treat staged or unstaged vault changes as an ephemeral error state. Before normal memory work resumes, load the bundled vault-maintenance skill with `agent-memory maintain skill vault-maintenance` and follow its referenced check, repair, and commit workflows.

Move reusable lessons during maintenance with:

```bash
agent-memory maintain move <key> --to global/advice
```
<!-- agent-memory:end -->
