# Reuse record: `lc-api-refined-names`

## Queries
`formalization_corpus.py search`:
- "same object in a full subcategory lift name": no owner;
- "FintypeCat of Fin": no owner beyond Mathlib's `FintypeCat.of`;
- "object of subcategory induced lift forget": Mathlib's category modules only.

## Owner
- Mathlib: `FintypeCat.of (Fin n)`, `FintypeCat.incl`, and the forgetful functor's action on
  objects (`FintypeCat.incl.obj (FintypeCat.of X) = X`, by `rfl`).
- The catalogue's forgetful functor rows (`fun.finite_sets.forget`) and object rows.

## New code, and why no dependency supplies it
An object row's refinement field (the base row, the structural functor, and the identification of
the image), its validation, and the language's rule that `X in C` selects a refinement. Only the
naming of objects across a structural functor is new; the objects and functor are Mathlib's.
