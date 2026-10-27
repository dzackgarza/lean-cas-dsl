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

## Computational consumption

The kernel consumes the accepted `refines.identification` as a presentation
`U(X(p)) ≅ B(p)`. It keeps `U(X(p))` as the interpreted value and the exact
`B(p)` constructor parameters as its computational representation. Public
`objectField` selectors `refinement` and `inverseRefinement` expose the existing
identification's `hom` and `inv` in the route's target category. They declare no
new mathematical comparison and do not mark either map as executed.

The retained producer captures the original source, each positioned parameter,
the complete route applications and both comparison endpoints. Actual execution
and prospective admission refresh only those captures. A checked transparent
alias forwards the producer; copying its old anchor onto another value or packet
cannot authorize reconstruction. Ordinary methods preserve the original route
and relate a canonical-base request's suffix to it by an explicit action offset.
The admission policy remains based on the accepted canonical base.
