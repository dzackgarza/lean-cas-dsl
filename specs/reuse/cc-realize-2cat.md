# Reuse record: `cc-realize-2cat`

## Queries
The corpus queries of [`cc-cells.md`](cc-cells.md) (same layer), 2026-09-29.
Additional searches on 2026-10-20: `presentation element structural encoding` and
`selected object computational form`. The returned algebraic-element storage and
unrelated implementation matches provide no owner for this kernel wire protocol.

## Owner
Mathlib: `Functor` for the catalogue's functors, `CatCommSq` and its pasting for commuting squares
between them, `Cat` as a strict bicategory. Presentation forms and what each denotes are
`lean-categories`'.

## New code, and why no dependency supplies it
The kernel's composition of a route's steps over the declared presentation forms. A leaf supplies
no category of handles, no denotation and no square: it registers opaque computations against
each step's declared type.

An element's computational form retains the entire form of its independently
selected object, including a registered functor or structural-edge image. Its
registration identity and category are those of that supplied form; no carrier
lookup selects a replacement named object. The element envelope carries the full
selected descriptor and retains its computational ownership. This is protocol
composition over the existing formal point and route, not new mathematics.

## Current execution replacement: software references (2026-10-28)

The earlier corpus queries do not establish absence of reusable execution machinery. The [#79 disposition](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6476550921) uses direct software-source inspection for the current common-program trial.

- CAP_project `fb48c41`, [MethodRecord.gi 285–361](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/MethodRecord.gi#L285-L361): WithGiven variants receive the actual universal object. Adapt this exact-apex discipline; it does not require retaining a private backend representation locally.
- The same revision, [Derivations.gi 387–453](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/Derivations.gi#L387-L453): additive prerequisite-cost propagation is implementation prior art where an admitted derivation requires it. Reject importing its registration-order tie break as semantic coherence. Its [CanCompute check](https://github.com/homalg-project/CAP_project/blob/fb48c41/CAP/gap/Derivations.gi#L53-L55) is a warning, not an enforced formal boundary.
- The [current library survey](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6475309126) identifies cslib FreeM/PFunctor.Free and PolyFun program/handler constructions. Their current lean-toolchain files inspected on 2026-10-28 are respectively `v4.36.0-rc1` and `v4.35.0`, versus this candidate's `v4.33.0`. They are candidates for reuse, not built dependencies here. Inspect a suitable revision or bounded adaptation before an adoption decision; current version mismatch does not imply every option requires a toolchain upgrade.
- Lean `v4.33.0`, [LocalContext](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/LocalContext.lean) and [withLetDecl](https://github.com/leanprover/lean4/blob/v4.33.0/src/Lean/Meta/Basic.lean#L1905-L1918): test existing scoped bindings for prepared execution occurrences. Preserve or close their context deliberately; normalized RHS equality is not identity.

The trial still owns inspectable checked requests, exact operand/output bindings, actual result retention, completion/failure and session ownership. These obligations are not supplied by a monad datatype alone. Record the actual import/port/adaptation decision, compiling deletion and measured chain result here when implemented; no compatibility or runtime pass is claimed by this source review.
