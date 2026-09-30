# Binding operators: the generic rule `lim` is missing (convergence process, step 4)

Specimen: `lim_{t → 0} sin(t)/t = 1` and `lim_{t → ∞} 1/t = 0` (`tests/acceptance/calculus.cas`;
lean-cas-dsl#46). The kernel refuses both: "`lim`: no registered domain of maps convergent at a
point" (`CasCatalogue/Language.lean`, `casLimit`).

## What the specimen exposes

`lim` is not missing a case. The kernel has no generic rule for any binding operator: a notation
that binds a variable `t`, forms a map `t ↦ e`, and applies a registered operation to that map. The
binding operators it does read are each a domain-specific kernel case:

| Notation | Kernel code | Mathematics the kernel supplies itself |
| --- | --- | --- |
| `∫_{a}^{b} e dt` | `definite` | the morphism named `∫ₐᵇ`; `t` ranges over the object named `ℝ`; the map is admitted into the object named `C` |
| `∑_{t ∈ A} e`, `∏_{t ∈ A} e` | `bigOperator` | the morphisms named `∑`, `∏`; `A` must lie in the object named `𝒫_fin`, and `t` ranges over its parameter |
| `∑_{n ∈ ℕ} c · t^n` | `formalSeries?` | a syntactic pattern read as the morphism named `Σ tⁿ` |
| `lim_{t → a} e` | refusal | none, and so it cannot be read |

Each row is mathematics chosen by the kernel: which set the variable ranges over, which subobject of
maps the operation is total on, and which argument is which. Under the owner's rule, "teaching the
kernel about math" is impossible unless it is purely categorical and completely general, and a
specimen is never fixed with a domain-specific kernel case. So `lim` cannot be fixed by adding a
fifth case beside these four.

## The rule

A binding operator is a registered **binder** row of the catalogue. Its fields are all
`lean-categories`' mathematics:
- `notation`: the surface token (`∫`, `lim`, `∑`, `∏`);
- `operation`: a family of morphisms `∀ params, M params × P params ⟶ Y params`. Here
  `M ↪ Hom(D, Y')` is the registered object of maps the operation is total on (integrable maps,
  maps convergent at `a`, maps on a finite set), and `P` holds the remaining arguments (bounds, the
  point `a`, the index set);
- `binderDomain`: `∀ params, D params`, the object the bound variable ranges over. For
  `lim_{t → a}` this is the punctured domain `D ∖ {a}`: `sin(t)/t` is a map there, and it is not a
  map on `ℝ`, because `t` is not a unit of `ℝ`;
- `M` is an ordinary object row with its admission and registered evidence (LC-18): continuity,
  convergence at `a`, finiteness.

The kernel's reading is one code path for every binder, and it names nothing:
1. Find the unique binder row whose `notation` is the token. If there is none, or more than one, the
   statement is invalid.
2. Read `P` (the point, the bounds, the index set) from the notation's arguments, in the row's
   declared order. This determines `params`.
3. Read the body at a stage in `binderDomain params`: `t` is a generic element of `D`. An operation
   that needs `t` in a subdomain reaches it only along a registered inclusion (`ℝ ∖ {0} ↪ ℝˣ`),
   never by admission, because a variable is never admitted.
4. Form the map `t ↦ e : D → Y'`, admit it into `M` through `M`'s admission and registered
   evidence, and apply `operation`. If the evidence is not established, the statement is invalid.

`∫`, `∑`, `∏` and the formal series become binder rows read by this path, and their kernel cases are
deleted. That is the test that the rule is general: one path, four mathematically different
operators, and a fifth (`lim`) that needs no kernel code of its own.

## Work, by owner

1. The binder row's schema and its registration checks. `operation` must take `M × P`, `M` must be
   a subobject of maps out of `binderDomain`, and the row must be total in the LC-14 sense. This
   is `lean-categories` registry code, which the seal covers.
2. Binder rows, with their domains and evidence, for `∫`, `∑`, `∏`, the formal series and `lim`.
   For `lim` this includes the point `∞` (the limit at the top of `ℝ`), the punctured domain, its
   inclusion into the units, and the object of maps convergent at a point with its evidence. This
   is formalization-agent work, in `lean-categories`, from this mathematical requirement alone.
3. The kernel's single binder path, which replaces `definite`, `bigOperator` and `formalSeries?`.
   This is the orchestrator's, reviewed as a kernel change.

Acceptance: `calculus.limit_sinc` and `calculus.limit_infinity` are established or remain invalid
only because evidence is missing, never because the kernel lacks a case. The existing `∫` and `∑`
assertions read unchanged through the one path. `Language.lean` names none of `ℝ`, `C`, `𝒫_fin`,
`∫ₐᵇ`, `∑`, `∏` or `Σ tⁿ`.

## The same pattern outside binders (recorded, not in this node)

`Language.lean` names 24 catalogue entries by surface name (`object state "…"`, `.name == "…"`).
They are of two kinds:
- Notation bindings: `R[x]` ↦ `Poly`, `ℤ/n` ↦ `ZMod`, `Xⁿ` ↦ `Vec`, `Mat`, `Fin`, `()`, `•`,
  `image`, `derivative`. Surface syntax is the language's, which the kernel owns. They belong in a
  notation table read as data, so that the kernel code names no entry.
- Mathematical choices: a bare numeric term defaults to `ℤ`, or to `ℚ` for a fraction or decimal
  (the initial ring, and the initial field of characteristic 0). This is mathematics about initial
  objects, and belongs in catalogue rows.
