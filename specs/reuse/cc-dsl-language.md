# Reuse record: `cc-dsl-language`

## Queries
`formalization_corpus.py search`:
- "custom syntax category DSL elaborator declare_syntax_cat": no owner;
- "parse external file runParserCategory": a file-extraction tactic (tcslib), no owner;
- "surface notation registry name lookup": no owner.

The language authors no mathematics. Every name it accepts is a catalogue row's surface name
(`lc-api-names`), and every literal is a catalogue literal (`lc-api-literals`).

## Owner
- Lean's `declare_syntax_cat`, `Parser.runParserCategory` and term elaboration.
- The catalogue rows (`lean-categories`), and the kernel's resolution of methods, objects and
  limits (`method%`, `obj%`, `limit%`).

## New code, and why no dependency supplies it
The syntax category of SPEC.md's statements and its elaboration through the catalogue.
