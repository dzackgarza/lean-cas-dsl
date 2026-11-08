/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.Language

/-- `N₂₃` as `N` and `23`. -/
def subscripted? (s : String) : Option (String × Nat) :=
  let digits := "₀₁₂₃₄₅₆₇₈₉".toList
  let chars := s.toList
  let suffix := (chars.reverse.takeWhile digits.contains).reverse
  let base := chars.take (chars.length - suffix.length)
  if suffix.isEmpty || base.isEmpty then none
  else some (String.ofList base, suffix.foldl (fun n c => 10 * n + digits.idxOf c) 0)

declare_syntax_cat cas_term
syntax:max num : cas_term
/-- A decimal `1.4142`: the fraction `14142/10⁴`. -/
syntax:max scientific : cas_term
syntax:max ident : cas_term
syntax:max (name := casAtom) ("ℤ" <|> "ℕ" <|> "ℚ" <|> "ℝ" <|> "ℂ") : cas_term
syntax:max "ℵ₀" : cas_term
syntax:max ident noWs "(" cas_term,* ")" : cas_term
syntax:max "(" cas_term ")" : cas_term
syntax:max "|" cas_term "|" : cas_term
syntax:max cas_term:max noWs "." rawIdent noWs "(" ")" : cas_term
/-- `f.m(a, …)`: the registered family `m` at `f` (a map, or an element), applied to `a, …`. -/
syntax:max (name := casCallWith) cas_term:max noWs "." rawIdent noWs "(" cas_term,+ ")" : cas_term
syntax:75 cas_term:76 " ^ " cas_term:75 : cas_term
syntax:70 cas_term:70 " / " cas_term:71 : cas_term
syntax:65 cas_term:65 " × " cas_term:66 : cas_term
syntax:65 cas_term:65 " ⊔ " cas_term:66 : cas_term
syntax:80 cas_term:80 " ∘ " cas_term:81 : cas_term
syntax:65 cas_term:65 " + " cas_term:66 : cas_term
syntax:65 cas_term:65 " - " cas_term:66 : cas_term
syntax:70 cas_term:70 " · " cas_term:71 : cas_term
syntax:75 "-" cas_term:75 : cas_term
syntax:50 cas_term:51 " in " cas_term:51 : cas_term
/-- An independently supplied Lean proof, checked at the declaration's actual proposition. -/
syntax:max (name := casFormalProof) "proof(" term ")" : cas_term
/-- Independent proofs for the actual proposition fields of a constrained point. -/
syntax:50 (name := casInProof) cas_term:51 " in " cas_term:51 " using "
  "(" cas_term,+ ")" : cas_term
syntax:45 cas_term:46 " ⊆ " cas_term:46 : cas_term
syntax:45 cas_term:46 " ∈ " cas_term:46 : cas_term
syntax:35 cas_term:36 " and " cas_term:35 : cas_term
syntax:45 cas_term:46 " ∉ " cas_term:46 : cas_term
/-- `a = b`: asserted, a comparison (`assert`); within a term, the predicate `=` into `Ω`. -/
syntax:45 cas_term:46 " = " cas_term:46 : cas_term
syntax:45 cas_term:46 " ≤ " cas_term:46 : cas_term
syntax:45 cas_term:46 " < " cas_term:46 : cas_term
syntax:65 cas_term:65 " ∪ " cas_term:66 : cas_term
syntax:70 cas_term:70 " ∩ " cas_term:71 : cas_term
syntax:65 cas_term:65 " \\ " cas_term:66 : cas_term
syntax:65 cas_term:65 " △ " cas_term:66 : cas_term
syntax:max cas_term:max noWs "²" : cas_term
syntax:max cas_term:max noWs "³" : cas_term
/-- `2n`, `3x²`: a numeral times a variable (or its square or cube). -/
syntax:max (name := casScaled) num noWs ident (noWs ("²" <|> "³"))? : cas_term
/-- `2√2`: a numeral times a square root. -/
syntax:max (name := casScaledRoot) num noWs "√" noWs cas_term:max : cas_term
syntax:max "𝒫" noWs "(" cas_term ")" : cas_term
/-- The set of maps `X → Y`. -/
syntax:55 cas_term:56 " → " cas_term:55 : cas_term
/-- The map `t ↦ e`, of the maps `X → Y` of an enclosing `in X → Y`. -/
syntax:51 ident " ↦ " cas_term:51 : cas_term
/-- A set literal `{x₁, …, xₙ}`, a subset of an enclosing `𝒫(X)`, else of `𝒫(ℤ)`. -/
syntax:max "{" cas_term,* "}" : cas_term
/-- `{a₀, a₁, …, ...}`: the arithmetic progression its numerals begin, `{a₀ + d k | k ∈ ℕ}` with
`d = a₁ - a₀`; the numerals must have that constant difference. -/
syntax:max (name := casProgression) "{" sepBy1(cas_term, ", ", ", ", allowTrailingSep) "..." "}" :
  cas_term
/-- `2ℕ`: the multiples `{2k | k ∈ ℕ}` of a numeral in a named set. -/
syntax:max (name := casMultiples) num noWs ("ℤ" <|> "ℕ" <|> "ℚ" <|> "ℝ" <|> "ℂ") : cas_term
/-- The subset `{t ∈ X | P}` a predicate classifies. -/
syntax:max "{" ident " ∈ " cas_term " | " cas_term "}" : cas_term
/-- The image `{e | t ∈ X}` of `t ↦ e`. -/
syntax:max "{" cas_term " | " ident " ∈ " cas_term "}" : cas_term
/-- The application of a map to arguments. -/
syntax:max "(" cas_term ")" noWs "(" cas_term,* ")" : cas_term
/-- Any already formed expression can be used as a callable. -/
syntax:max (name := casApplication) cas_term:max noWs "(" cas_term,* ")" : cas_term
/-- The polynomials `R[x]` over `R` in the variable `x`: `Poly(R)`, whose generator `x` names. -/
syntax:max (name := casRing) cas_term:max noWs "[" ident "]" : cas_term
/-- A variable of a polynomial ring in several variables, or `...` between two indexed ones. -/
declare_syntax_cat cas_var
syntax ident : cas_var
syntax "..." : cas_var
/-- `R[x, y]`, `R[x_0, x_1, ..., x_9]`: the polynomials over `R` in these variables, `MvPoly(n, R)`;
`...` runs through the indices between its neighbours. -/
syntax:max (name := casMvRing) cas_term:max noWs "[" ident "," sepBy1(cas_var, ",") "]" : cas_term
/-- `Spec A`: the registered object `Spec N` of the algebra `A = N(…)`. -/
syntax:max (name := casSpec) "Spec " cas_term:max : cas_term
/-- `a is b`: `a = b`. -/
syntax:45 (name := casIs) cas_term:46 " is " cas_term:46 : cas_term
/-- `√x`: `sqrt(x)`. -/
syntax:max "√" noWs cas_term:max : cas_term
/-- `map p to S[x]`: the registered `map` landing in `S[x]`. (`map` is a keyword of the language:
a module importing it does not use `map` as a bare identifier.) -/
syntax:max (name := casMap) "map " cas_term:max " to " cas_term:max : cas_term
syntax:max (name := casPresentationForward) "map " cas_term:max " along " ident : cas_term
syntax:max (name := casPresentationBack) "map " cas_term:max " back " "along " ident : cas_term
/-- Apply the exact registered functor, optionally supplying its declaration's explicit
arguments. -/
syntax:max (name := casFunctorView) "view " cas_term:max " along " ident : cas_term
syntax:max (name := casFunctorViewArgs) "view " cas_term:max " along " ident
  "(" sepBy(cas_term, ",") ")" : cas_term
syntax:max (name := casConstructionMap) "map " cas_term:max " along " ident
  "(" sepBy(cas_term, ",") ")" : cas_term
syntax:max (name := casSelectedLift) "lift(" cas_term ")" " along " ident
  "(" sepBy(cas_term, ",") ")" " with " cas_term:max " using " cas_term:max : cas_term
syntax:max (name := casLiftFactor) "factor(" cas_term ")" " through " cas_term:max
  " with " cas_term:max " using " cas_term:max : cas_term
syntax:max (name := casCompositeLift) "composite_lift(" cas_term ")" : cas_term
syntax:max (name := casCellComponent) "component(" ident "(" sepBy(cas_term, ",") ")"
  "," cas_term "," "[" ident,* "]" ")" : cas_term
syntax:max (name := casCellComponentInverse) "inverse_component(" ident
  "(" sepBy(cas_term, ",") ")" "," cas_term "," "[" ident,* "]" ")" : cas_term
syntax:max (name := casSelectedPresentation) "presentation(" ident
  "(" sepBy(cas_term, ",") ")" ")" : cas_term
syntax:max (name := casSelectedPresentationInverse) "inverse_presentation(" ident
  "(" sepBy(cas_term, ",") ")" ")" : cas_term
syntax:max (name := casSelectedBinder) "binder(" ident
  "(" sepBy(cas_term, ",") ")" "," cas_term ")" : cas_term
/-- `(a)x`, `(a)x²`: a parenthesized coefficient times a variable (or its square or cube). -/
syntax:max (name := casCoefficient) "(" cas_term ")" noWs ident (noWs ("²" <|> "³"))? : cas_term
/-- `a dx`, `f dx`: juxtaposition, the product in a set both are in, else the registered action
`•` (a polynomial times a differential). -/
syntax:70 (name := casActed) cas_term:71 ident : cas_term
/-- `M * v`: juxtaposition written out. -/
syntax:70 (name := casTimes) cas_term:70 " * " cas_term:71 : cas_term
/-- Explicit application of a registered action, with its independently typed operands. -/
syntax:70 (name := casAction) cas_term:70 " • " cas_term:71 : cas_term
/-- A tuple `(x₁, …, xₙ)`, an element of `Xⁿ`. -/
syntax:max (name := casTuple) "(" cas_term ", " cas_term,+ ")" : cas_term
/-- A map argument may bind a tuple of patterns, recursively, at its declared components. -/
syntax:51 (name := casPatternLambda) "(" cas_term ", " cas_term,+ ")" " ↦ " cas_term:51 : cas_term
/-- A matrix `[a, b; c, d]`, by its rows. -/
syntax:max (name := casMatrix) "[" sepBy1(sepBy1(cas_term, ", "), "; ") "]" : cas_term
/-- `∑_{a ∈ A} e`, `∏_{a ∈ A} e`: over a finite subset `A`. -/
syntax:60 (name := casBig) ("∑" <|> "∏") "_{" ident " ∈ " cas_term "} " cas_term:60 : cas_term
/-- `lim_{t → a} e`, `lim_{t → ∞} e`. -/
syntax:60 (name := casLimit) "lim_{" ident " → " cas_term "} " cas_term:60 : cas_term
/-- `∞`, the end of `ℝ` a limit may be taken at. -/
syntax:max (name := casInfinity) "∞" : cas_term
/-- `∫_{a}^{b} e dt`: the definite integral of `t ↦ e`. -/
syntax:60 (name := casDefinite) "∫_{" cas_term "}^{" cas_term "} " cas_term:71 ident : cas_term
/-- The formal power series `R[[t]]` over `R` in the variable `t`. -/
syntax:max (name := casSeries) cas_term:max noWs "[" noWs "[" ident "]" noWs "]" : cas_term
/-- `M⁻¹`, and `M⁻¹(v)` applied. -/
syntax:max (name := casInverse) cas_term:max noWs "⁻¹" (noWs "(" cas_term,* ")")? : cas_term
/-- `Xˣ`: the units of `X` (the registered `Units`), `Matₙ(K)ˣ = GLₙ(K)`,
`Kˣ = K ∖ {0}` for a field. -/
syntax:max (name := casUnits) cas_term:max noWs "ˣ" : cas_term
/-- `X ∖ 0`: the registered domain `N∖0` of the nonzero elements of `X = N(…)` (`ℚ[x] ∖ 0`). -/
syntax:max (name := casNonzero) cas_term:max " ∖ " num : cas_term
/-- `𝒫_fin(X)`: the finite subsets of `X`. -/
syntax:max (name := casFiniteSubsets) "𝒫_fin" noWs "(" cas_term ")" : cas_term
/-- Named domains whose names are not identifiers: `C^∞`, `ℕ⁺`, `ℙ`. -/
syntax:max (name := casDomainAtom) ("C^∞" <|> "ℕ⁺" <|> "ℙ") : cas_term
/-- `[tⁿ]f`, `[t^n]f`, `[t]f`: the coefficient of `tⁿ` in a power series. -/
syntax:max (name := casCoefficientOf) "[" cas_term "]" noWs cas_term:max : cas_term
/-- `∫ ω`: the primitives of a differential. -/
syntax:60 (name := casIntegral) "∫ " cas_term:60 : cas_term

/-- A pair `x ↦ y` of a graph literal. -/
declare_syntax_cat cas_pair
syntax cas_term:51 " ↦ " cas_term:51 : cas_pair
syntax:40 "{" cas_pair,* "}" " : " cas_term:51 : cas_term

declare_syntax_cat cas_stmt
syntax "let " ident " := " cas_term : cas_stmt
syntax "let " ident " : " cas_term " := " cas_term : cas_stmt
/-- `let f(t) := e in X → Y`: `let f := t ↦ e in X → Y`. -/
syntax (name := casLetPattern) "let " ident noWs "(" cas_term ")" " := " cas_term : cas_stmt
syntax (name := casLetArgs) "let " ident noWs "(" ident ", " ident,+ ")" " := " cas_term : cas_stmt
syntax (priority := high) "assert " &"implemented " cas_term : cas_stmt
syntax "assert " cas_term : cas_stmt

/-- A test item: a statement with its id and the provenance of its expected value. -/
declare_syntax_cat cas_item
syntax "test " ident str ": " cas_stmt : cas_item
syntax cas_stmt : cas_item

end CasCatalogue.Language
