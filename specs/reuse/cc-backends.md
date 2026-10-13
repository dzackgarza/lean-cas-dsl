# Reuse record: `cc-backends`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `GAP computer algebra interface Lean` | none |
| `SageMath oracle certificate Lean tactic` | none |
| `external solver certificate checking decode` | acl2 release notes, evm-asm (neither a CAS bridge) |

No formalization supplies a Lean bridge to Sage or GAP.

## Owner
- The process boundary is the repository's framed port (`CasDsl/Port.lean`: length-prefixed JSON
  frames, request ids, a ready frame with capabilities) and `backends/sage_adapter.py`.
- Engines: Sage and GAP themselves (GAP through Sage's `libgap`, or `passagemath` wheels where
  Sage is not installed); their answers are untrusted and read by the kernel into the declared
  result form, or rejected as malformed.
- Nothing checks or certifies an answer except the permanent acceptance suite.

## New code, and why no dependency supplies it
Port capabilities keyed by registered semantic operations, the kernel's reading of wire values
into declared result forms (a subgroup with its inclusion, a kernel with its arrow), and the
hostile backend probe.
