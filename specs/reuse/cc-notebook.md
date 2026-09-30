# Reuse record: `cc-notebook`

## Queries
No mathematics is authored in this node: the notebook surface is syntax over the finished core
(`method%`, `ask%`, `refine%`, `eq%`, `cell%`, `memo%`, `exec%`, registered limits and colimits).

## Owner
- Every value: a kernel term from a registered constructor; every operation: a registered
  semantic operation; equality: the category's equality in `lean-categories`.
- The notebook kernel is `nbdsl` (lean-jupyter-kernel), unchanged.

## New code, and why no dependency supplies it
Notebook syntax only (elaborators to the core surfaces); the old `CasDsl` categories, typing
rules, codecs and executors are removed.
