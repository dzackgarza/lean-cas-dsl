# Reuse record: `lc-api-spec`

`lc-api-spec` formalizes SPEC.md's vocabulary upstream section by section. Its first section is
"Exact number systems": the rings `ℤ`, `ℚ`, `ℤ/n` and their elements, with the ring operations
on elements (`2 + 3 = 0 in ℤ/5`, `gcd(84, 30) = 6`) and the containments `ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ`.

## Queries
`formalization_corpus.py search`:
- "element of a ring object addition as morphism of underlying set": no owner;
- "internal ring object in category": no owner;
- "RingCat forget carrier add": Mathlib's `RingCat` and its forgetful functor.

## Owner
- Mathlib: `RingCat`, `RingCat.of ℤ`, `ZMod n`, `ℚ`, `Int.gcd`, `forget RingCat`, and the ring
  operations of each carrier.
- The catalogue: `cat.rings` (`Rings`), the forgetful route to `Sets`, element literals
  (`lc-api-elements`) and object refinements (`lc-api-refined-names`): `ℤ` in `Rings` refines
  `ℤ` in `Sets`.

## New code, and why no dependency supplies it
Catalogue rows only: the named rings as refinements of the named sets; element operations of a
category as morphism families of its underlying sets (`add : |R| × |R| → |R|`), named for the
language (`+`, `·`, `gcd`); and the language's element terms and infix operators, resolved through
those rows.
