# Reuse record: `cc-constructor-surface`

## Queries
`formalization_corpus.py search`:
- "smart constructor presented object registry": no owner;
- "ZMod pi finite free module constructor": free abelian group instances (Rocq category-theory).

The objects are Mathlib's (`ZMod n`, `Fin k → ZMod n`, `Fin n`, products). This node authors no
mathematics.

## Owner
- The registered constructors (`ConstructorEntry`, `cc-constructors`) and their Mathlib
  denotations.
- The kernel's selection of the registered computation for a receiver's input form.

## New code, and why no dependency supplies it
- A surface that builds an input by a registered constructor in its declared input form, so that
  assertions and notebooks name no leaf handle constructor.
