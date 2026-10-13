# Reuse record: `gov-roles`

The role split (orchestrator; formalization, acceptance and leaf subagents) and the one-way flow, written into architecture.md and each repository's AGENTS.md.

## Queries
- existing text: `specs/architecture.md` "The one-way workflow" (blindness per step, no reverse arrows) — reused and extended, not duplicated;
- `lean-categories/AGENTS.md` "Blind to computation", `lean-cas-dsl-leaves/AGENTS.md` "Blind to the tests" — linked, not restated.

## Owner
- `specs/architecture.md` owns the separation of concerns; the new section extends it.

## New code
Documentation only: the missing rule that authors are distinct agents (blindness is a property of who writes).
