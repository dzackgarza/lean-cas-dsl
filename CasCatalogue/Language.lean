/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantic
public import CasCatalogue.ProofRefinement
public import CasCatalogue.EvidencePresentation
public import CasCatalogue.Admission
public import CasCatalogue.DirectConstruction
public import CasCatalogue.DeclaredAdmission
public import CasCatalogue.SelectedLift
public import CasCatalogue.CellAction
public import CasCatalogue.CategoryContext
public import CasCatalogue.OperationAgreement
public import CasCatalogue.StructuredProjection
public import CasCatalogue.ReindexAction
public import CasCatalogue.ConstrainedPoint
-- The whole pinned semantic release: what the language can say never depends on which leaves are
-- installed.
public import LeanCategories.Catalogue

@[expose] public section

/-!
# The language (SPEC.md): statements about the catalogue's mathematics

The language states mathematics through the catalogue alone. Every name it accepts is a catalogue
row's surface name: an object (`ℤ`, `Fin(3)`, `ZMod(4)`), a category (`in Sets`), a method
(`X.cardinality()`), or a property (`X.is_finite()`). Every literal is a value of a category's
registered literal form (`64`, `ℵ₀` in `Card`). It names no category id, handle, realizer or leaf:
the kernel resolves each call and selects its realization.

Terms:
* `N` or `N(a, …)`: the registered object named `N` at the numeral parameters `a, …`: its
  unrefined default when present, otherwise its unique named binding; an enclosing `in C`
  selects its refinement in `C` (`Fin(3) in FiniteSets`);
* `ℤ/n` and `(ℤ/n)^k` select the exact families published for those notation tokens;
* `X × Y`, `X ⊔ Y`: the registered product and coproduct in the category of `X` and `Y`;
* `m(a, …)`: the registered morphism family named `m` at the numeral parameters `a, …`;
* `{x ↦ y, …} : X → Y`: the morphism with that graph, by the category's registered graph literal;
  `x`, `y` are numerals of the sets `X` and `Y` are;
* `id(X)` and `f ∘ g`: identities and composites;
* `x + y`, `x · y`, `-x`, `x - y` (`x + -y`): the registered operations of the category whose
  refinement of the set `X` the elements are in (the ring `ℤ/5` for elements of `ℤ/5`). An element
  of `X` is a morphism `1 → X` from the registry's selected terminal source; a numeral is the image of `k` under
  the registered map out of the initial object of a category refining its set (`ℕ → S`, `ℤ → R`),
  or the point `k` of `Fin n` (`k < n` decided), in the set of the other operands, of an enclosing
  `in X`, or else `ℤ`; an operation is its registered morphism composed
  with the product mediator of its operands;
* `S(f, …)` for a registered limit or colimit shape `S` (`pullback`, `pushout`, `equalizer`,
  `coequalizer`, `kernel`, `cokernel`): the apex of the registered (co)limit of the standard
  diagram on `f, …` in their category;
* `R[x]`: `Poly(R)`, in which `x` names the registered generator; `t ↦ e in R[x]` is `e` with `t`
  the generator; `p(a)` is the registered application of the element `p` (evaluation), a numeral
  `a` being an element of `R`;
* `f(x)` and `x.f()` for a registered morphism family `f`: its parameters are unified from the
  sets of its operands (`deg` on `ℤ[x]` is `deg ℤ`), and `map p to S[x]` also from the set it lands
  in; `√x` is `sqrt(x)`;
* `X - Y` for named sets `Y ⊆ X`: the complement in `𝒫(X)` of the registered inclusion's image;
  `p + Y`: the coset `{p + c | c ∈ Y}`;
* elements of a set `Y` included in `X` (registered constants `R ↪ R[x]`, or inclusions `ℚ ⊆ ℝ`)
  are elements of `X` where one is needed (`(1/2)x²`, `1/3 = t` in `ℝ`);
* `a / b`: the registered division `M × Mˣ → M`; the divisor is an element of `Mˣ`, or a numeral
  formed there with its evidence decided (`2 ∈ ℚˣ`);
* `d(p)`, `dx` (`d(x)` for a variable `x`), `d/dx`, `∫ ω`: the registered differential, derivative
  and primitives; juxtaposition `a b` is the product in a set both are in, else the registered
  action `•` (`(6x + 1) dx`);
* `a = b` within a term: the registered equality predicate `X × X → Ω`;
* `t in C/Y` for a registered category family `C/` or `C` over an object (`Algebras/ℂ`,
  `Schemes/ℚ`): `t`, or its registered refinement, in that family at the object its set parameter
  `Y` determines; `Spec A` is the registered `Spec N` at `A = N(…)`; `a is b` is `a = b`;
* `R[x, y]`, `R[x_0, x_1, ..., x_9]`: `MvPoly(n, R)`, whose variables are its indexed generators;
  `X.m()` of an object `X` without such a method is its registered invariant `m : 1 → T`
  (`R.dimension()`);
* `[t^n]f`: the registered coefficient; `∑_{n ∈ X} e` of power series is the registered formal
  (`t`-adic) sum, over a named set or a subset; `x^n` for `n ∈ ℕ` an element: the registered power;
  a statement's bound generator read inside a map is carried to its stage;
* a decimal `1.4142` is the fraction `14142/10⁴`; a numeral receives families (`(360).m()`);
* `M⁻¹`: the inverse of the group `Mˣ`, of an element formed there (`M in Mat₂(ℚ)ˣ`); `x⁻¹` of an
  element not in the units is not a term;
* `x in D` for a domain `D ↪ B` with a registered admission (`Mˣ`, `ℕ⁺`, `ℙ`, `R[x] ∖ 0`,
  `Monic(n, K)`, `C`, `C^∞`): `x` read in `B` (or as a map) and formed in `D`, its evidence
  (`IsUnit`, monicity, continuity, …) established when the statement is read, else the statement is
  invalid. Nothing is admitted into a domain implicitly because an operation needs it there, and no
  term is read again another way when a reading fails (LC-14); a numeral needed in a domain is
  formed there, its evidence decided (LC-15);
* a term of numerals alone is read in the enclosing set, else its siblings' set, else `ℚ` (with a
  fraction or decimal: the initial field of characteristic `0`) or `ℤ` (the initial ring);
* `{a₀, a₁, …, ...}`: the arithmetic progression `{a₀ + d k | k ∈ ℕ}` its numerals begin; `kℕ`:
  `{k n | n ∈ ℕ}`; a named set compared with a subset is its image there (`{0, 1, 2, ...} = ℕ`);
* binding notation resolves its token and arguments against registered binder rows; the row
  determines the bound variable's domain, the operation's source admission and the obligations
  of the map formed from the body. The same rule reads integrals, limits and indexed operators;
* `f.m(a, …)`: a family with the map `f` as its parameter, or at an element of its domain
  (`(f in C^∞).taylor_expansion(0)`); `R[[t]]`;
* `Xⁿ` (`ℚ²`) for a set `X`: `Vec(X, n)`; `(x₁, …, xₙ)`: the tuple by the registered `()` and
  `cons`; `[a, b; c, d]`: the matrix with these rows (`rows`); `N₂(…)` is `N(2, …)` (`Mat₂(ℚ)`);
  `M v`, `M * v`, `M(v)`: the registered application of `M`'s set;
* `X.m()`: the registered method or property `m`, resolved from the category of `X`;
* `|X|`: `X.cardinality()`;
* `X in C`: `X` in the category named `C`; `t in X` for a set `X`: `t` with its numerals in `X`;
* numerals and identifiers not bound to anything else are literals.

Statements:
* `let x := X`;
* `assert X = L`: the value of `X` is the literal `L` of its category's literal form: the
  proposition `X = denote L`, decided in Lean, or else the value computed by the admitted
  registration and decoded in the form, compared with `L` by the form's decidable equality
  (`CasCatalogue.Realize`);
* `X ⊆ Y` for named sets: decided by the registered inclusions alone (a chain of registered
  monomorphisms `X ↪ … ↪ Y`, or `X = Y`); no realization is consulted;
* `x ∈ Y`: `x`, with its numerals in `Y`, is an element of `Y` or of a set registered in `Y`;
* `P and Q`: both decisions (three-valued);
* `assert f = g` for morphisms: the category's registered equality decides it (an asserted
  equation is this comparison, not the predicate `=`);
* `assert P`, `assert P = true | false | unknown`: the decision of a property;
* `assert implemented X`: a realization computes `X`.

Each statement is read once, semantically (`CasCatalogue.Semantic`): it elaborates from the
catalogue alone, whatever leaves are installed, into its claim (`Claim`); failing that, it is not
a valid statement. The claim is then discharged in Lean where Lean decides it, and otherwise
realized by evaluating the same term through the admitted registrations
(`CasCatalogue.Realize`): it holds, it is wrong, its computation is a gap (no registration, or an
ambiguous one), its backend is unavailable, or its answer is malformed. `CasCatalogue.TestSuite`
runs files of statements. Nothing here reads a term any other way: no reading through a leaf's
handles, denotations or decisions exists.
-/

open Lean Meta Elab Term

namespace CasCatalogue.Language

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
syntax:50 (name := casInProof) cas_term:51 " in " cas_term:51 " using " "(" cas_term,+ ")" : cas_term
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
/-- Apply the exact registered functor, optionally supplying its declaration's explicit arguments. -/
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
/-- `Xˣ`: the units of `X` (the registered `Units`), `Matₙ(K)ˣ = GLₙ(K)`, `Kˣ = K ∖ {0}` for a field. -/
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

/-- The reader's unreduced question tree. Atomic judgements retain their typed operands
and upstream declarations; logical constructors are retained before any decision. -/
inductive Question
  | proposition (term : Expr)
  | judgement (relation : String) (terms : Array Expr) (route : Array Name := #[]) (declarations : Array Name := #[])
      (types : Array Expr := #[])
  | conjunction (left right : Question)
  | negation (question : Question)
  deriving Inhabited, Hashable, Repr

/-- The value of a term. -/
inductive Value
  /-- An explicit proof artifact, elaborated only at an independently fixed obligation. -/
  | formalProof (proofSyntax : Syntax)
  /-- A numeral: a parameter, or a literal. -/
  | nat (n : Nat)
  /-- An identifier bound to nothing: a literal of the form it is compared with. -/
  | literal (name : Name)
  /-- An object: its term, the registered category it is an object of, and the object row and
  numeral parameters it was named by, if it was named. -/
  | object (handle : Expr) (category : NamedCategoryEntry)
      (origin : Option (ObjectEntry × Array Value))
      (selected : Option Value)
      (viewData : Option (Array Value × Value × Array EdgeRef × Array ParameterPresentation × Array (EdgeRef × Array Expr)))
  /-- A morphism `source ⟶ target` of a registered category. -/
  | morphism (hom : Expr) (source target : Expr) (category : NamedCategoryEntry)
      (sets : Option (Value × Value))
  /-- An object in the complete category of an accepted action, without a named-row requirement. -/
  | derivedObject (handle : Expr) (context : CategoryContext) (known : Array Value)
  /-- A complete map at the same actual category bundle and retained endpoint contexts. -/
  | derivedMorphism (hom : Expr) (source target : Expr) (context : CategoryContext)
      (sets : Value × Value)
  /-- The set of maps `source → target` of `Sets`: the ambient of a map `t ↦ e`. -/
  | homSet (source target : Value)
  /-- An element of the set `object` (an `.object` value): a morphism `1 ⟶ object` from
  the registry's selected terminal source. -/
  | element (hom : Expr) (object : Value)
  /-- The decision of a property: an `Option Bool`. -/
  | answer (answer : Expr)
  | judged (question : Question) (answer : Expr)
  deriving Inhabited

/-- Syntactic comparison of retained presentations, before any mathematical unfolding. -/
def sameParameterPresentation (left right : ParameterPresentation) : Bool :=
  left.source == right.source && left.sourceCategory == right.sourceCategory &&
    left.targetCategory == right.targetCategory && left.params == right.params &&
    left.route == right.route && left.applications == right.applications &&
    left.carrierRoute == right.carrierRoute && left.identifications == right.identifications &&
    left.object == right.object && left.image == right.image && left.identity == right.identity

/-- Exact context duplicates may be shared; equal carriers never discard different origins,
selected objects, routes, full parameters, or retained comparison witnesses. -/
partial def Value.sameSource (left right : Value) : Bool :=
  let sameValues := fun (left right : Array Value) =>
    left.size == right.size && (left.zip right).all (fun (a, b) => a.sameSource b)
  match left, right with
  | .nat a, .nat b => a == b
  | .literal a, .literal b => a == b
  | .object a ac ao asel av, .object b bc bo bsel bv =>
      a == b && ac.id == bc.id && ac.declaration == bc.declaration &&
        (match ao, bo with
        | none, none => true
        | some (ar, ap), some (br, bp) => ar.id == br.id && sameValues ap bp
        | _, _ => false) &&
        (match asel, bsel with
        | none, none => true
        | some a, some b => a.sameSource b
        | _, _ => false) &&
        (match av, bv with
        | none, none => true
        | some (aa, asrc, ar, ap, af), some (ba, bsrc, br, bp, bf) =>
            sameValues aa ba && asrc.sameSource bsrc && ar == br && af == bf &&
              ap.size == bp.size && (ap.zip bp).all (fun (a, b) => sameParameterPresentation a b)
        | _, _ => false)
  | .element a ao, .element b bo => a == b && ao.sameSource bo
  | .morphism a asrc atgt ac av, .morphism b bsrc btgt bc bv =>
      a == b && asrc == bsrc && atgt == btgt && ac.id == bc.id &&
        (match av, bv with
        | none, none => true
        | some (asrc, atgt), some (bsrc, btgt) => asrc.sameSource bsrc && atgt.sameSource btgt
        | _, _ => false)
  | .derivedObject a ac ak, .derivedObject b bc bk =>
      a == b && ac.expression.syntacticEq bc.expression && ac.bundle == bc.bundle && sameValues ak bk
  | .derivedMorphism a asrc atgt ac av, .derivedMorphism b bsrc btgt bc bv =>
      a == b && asrc == bsrc && atgt == btgt && ac.expression.syntacticEq bc.expression &&
        ac.bundle == bc.bundle && av.1.sameSource bv.1 && av.2.sameSource bv.2
  | .homSet asrc atgt, .homSet bsrc btgt => asrc.sameSource bsrc && atgt.sameSource btgt
  | .answer a, .answer b => a == b
  | _, _ => false

/-- An exact selected value may carry additional context without becoming another selection.
All constructor arguments and selected structures are compared syntactically; only the context
payload is omitted here, and callers must retain both payloads when coalescing such values. -/
partial def Value.sameSelection (left right : Value) : Bool :=
  let sameValues := fun (left right : Array Value) =>
    left.size == right.size && (left.zip right).all (fun (a, b) => a.sameSelection b)
  match left, right with
  | .nat a, .nat b => a == b
  | .literal a, .literal b => a == b
  | .object a ac ao asel _, .object b bc bo bsel _ =>
      a == b && ac.id == bc.id && ac.declaration == bc.declaration &&
        (match ao, bo with
        | none, none => true
        | some (ar, ap), some (br, bp) => ar.id == br.id && sameValues ap bp
        | _, _ => false) &&
        (match asel, bsel with
        | none, none => true
        | some a, some b => a.sameSelection b
        | _, _ => false)
  | .element a ao, .element b bo => a == b && ao.sameSelection bo
  | .derivedObject a ac _, .derivedObject b bc _ =>
      a == b && ac.expression.syntacticEq bc.expression && ac.bundle == bc.bundle
  | .homSet asrc atgt, .homSet bsrc btgt => asrc.sameSelection bsrc && atgt.sameSelection btgt
  | _, _ => left.sameSource right

/-- Expand each exact supplied witness once, preserving declaration order and distinct aliases. -/
partial def collectSourceParameterValues (pending : List Value) (found : Array Value) : Array Value :=
  match pending with
  | [] => found
  | value :: rest =>
      if found.any (·.sameSource value) then collectSourceParameterValues rest found else
      let children : Array Value := match value with
        | .object _ _ origin selected viewData =>
            selected.toArray ++
              (viewData.map fun (original, source, _, _, _) => Array.push original source).getD #[] ++
              (origin.map fun (_, parameters) => parameters).getD #[]
        | .element _ object => #[object]
        | .morphism _ _ _ _ (some (source, target)) | .homSet source target => #[source, target]
        | .derivedObject _ _ known => known
        | .derivedMorphism _ _ _ _ (source, target) => #[source, target]
        | _ => #[]
      collectSourceParameterValues (children.toList ++ rest) (found.push value)

/-- Actual constructor arguments available as typed source witnesses, in declaration order. -/
def sourceParameterValues (value : Value) : Array Value :=
  collectSourceParameterValues [value] #[]

/-- Keep the complete supplied arguments of a declared endpoint. This is context
retention only: it does not change the object, its selected structure, or any
existing comparison and action data. -/
def retainObjectContext (value : Value) (known : Array Value) : Value :=
  let existing := sourceParameterValues value
  let known := known.foldl (fun retained witness =>
    if existing.any (·.sameSource witness) || retained.any (·.sameSource witness) then retained
    else retained.push witness) #[]
  if known.isEmpty then value else
  match value with
  | .object handle category origin selected viewData =>
      let retained := match viewData with
        | none => (known, value, #[], #[], #[])
        | some (original, source, route, alternatives, applications) =>
            (original ++ known, source, route, alternatives, applications)
      .object handle category origin selected (some retained)
  | .derivedObject handle context previous =>
      .derivedObject handle context (previous ++ known)
  | _ => value

/-- The terms a value is (its object, morphism, element or answer), for the question of a judgement
about it. -/
partial def Value.terms : Value → Array Expr
  | .formalProof _ => #[]
  | .nat n => #[mkNatLit n]
  | .literal name => #[mkStrLit name.toString]
  | .object handle _ origin selected viewData =>
      #[handle] ++ (origin.map fun (_, parameters) => parameters.flatMap Value.terms).getD #[] ++
        (selected.map Value.terms).getD #[] ++
        (viewData.map fun (original, source, _, alternatives, applications) =>
          original.flatMap Value.terms ++ source.terms ++
            (alternatives.flatMap fun presentation =>
              presentation.params ++ #[presentation.object, presentation.image, presentation.identity]) ++
            applications.flatMap (·.2)).getD #[]
  | .morphism hom source target _ _ => #[hom, source, target]
  | .derivedObject handle context known => #[handle, context.bundle] ++ known.flatMap Value.terms
  | .derivedMorphism hom source target context sets =>
      #[hom, source, target, context.bundle] ++ sets.1.terms ++ sets.2.terms
  | .homSet s t => s.terms ++ t.terms
  | .element hom set => #[hom] ++ set.terms
  | .answer a | .judged _ a => #[a]

/-- Formal declaration identities attached to an operand, retained separately from
its carrier term so a selected structure cannot disappear when the carrier is shared. -/
partial def Value.declarations : Value → Array Name
  | .object _ category origin selected viewData =>
      #[category.declaration] ++ (selected.map Value.declarations).getD #[] ++
        (viewData.map fun (original, source, _, alternatives, _) =>
          original.flatMap Value.declarations ++ source.declarations ++
            alternatives.flatMap (·.identifications)).getD #[] ++ match origin with
        | none => #[]
        | some (entry, parameters) =>
            #[entry.declaration] ++ parameters.flatMap Value.declarations ++
              (entry.refines.map fun refinement => #[refinement.identification]).getD #[]
  | .morphism _ _ _ category sets =>
      #[category.declaration] ++ (sets.map fun (source, target) =>
        source.declarations ++ target.declarations).getD #[]
  | .derivedObject _ context known =>
      context.bundle.getAppFn.constName?.toArray ++ known.flatMap Value.declarations
  | .derivedMorphism _ _ _ context sets =>
      context.bundle.getAppFn.constName?.toArray ++ sets.1.declarations ++ sets.2.declarations
  | .element _ set => set.declarations
  | .homSet source target => source.declarations ++ target.declarations
  | _ => #[]

/-- A judgement is formed with the operands' full terms and formal identities at reading time. -/
def judgement (relation : String) (operands : Array Value) (route : Array Name := #[]) : Question :=
  .judgement relation (operands.flatMap Value.terms) route (operands.flatMap Value.declarations)

/-- Preserve a question already formed by the reader, or the exact typed proposition. -/
def Value.question (value : Value) (prop : Expr) : Question :=
  match value with
  | .judged question _ => question
  | _ => .proposition prop

/-- The `let` bindings of a file: each name's term, evaluated where it is used, so that a use of a
binding whose computation is a gap is itself a gap. -/
abbrev Scope := Std.HashMap Name Syntax

/-- The context of an evaluation: its stage `S`, when the elements being handled are generalized
elements `S → X` (inside `t ↦ e` or `{t ∈ S | P}`, where `t` is `𝟙 S`) rather than global ones
`1 → X`. A term is read one way, for its mathematics alone (`CasCatalogue.Semantic`): objects are
their declarations, and morphisms, limits, methods and properties are the catalogue's; a failure
is invalidity. -/
structure Ctx where
  stage : Option Value := none
  /-- Variables bound to values: `t` in `t ↦ e` and `{t ∈ X | P}` (the generic element of the
  stage), and a statement's free variables. -/
  bound : List (Name × Value) := []
  /-- Where the semantic reading records the operations that form its values
  (`CasCatalogue.Trace`), for the realized reading to evaluate the same term. -/
  trace : Option Trace := none
  /-- Closed readings shared only within one fixed question scope and trace. -/
  closedTerms : Option (IO.Ref (Std.HashMap String Value)) := none
  deriving Inhabited

/-- The language's evaluation monad: elaboration in a reading. -/
abbrev M := ReaderT Ctx TermElabM

/-- Optional reader profiling; ordinary interpretation executes the action directly. -/
def profileReader {α : Type} (name : String) (action : M α) : M α := do
  let opts ← getOptions
  if profiler.get opts then profileitM Exception s!"cas {name}" opts action else action

/-- The morphism `f : a ⟶ b` of `category`, elaborated there. -/
def homIn (f : Term) (a b : Expr) (_category : NamedCategoryEntry) : M Expr :=
  Semantic.hom f a b

/-- The registered limit (colimit, if `colimit`) of `shape` at the diagram `D` of `category`. -/
def limitIn (colimit : Bool) (shape : String) (D : Term) (category : NamedCategoryEntry) :
    M Expr := do
  let diagram ← instantiateMVars (← elabTermAndSynthesize D none)
  Semantic.limit colimit shape diagram category.id.raw (← read).trace

/-- The apex of a limit cone or colimit cocone. -/
def apexOf (colimit : Bool) (L : Expr) : MetaM Expr :=
  if colimit then do
    mkAppM ``CategoryTheory.Limits.Cocone.pt
      #[← mkAppM ``CategoryTheory.Limits.ColimitCocone.cocone #[L]]
  else do
    mkAppM ``CategoryTheory.Limits.Cone.pt #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[L]]

/-- The registered category named `name`. -/
def categoryNamed (state : RegistryState) (name : String) : TermElabM NamedCategoryEntry := do
  let some entry := state.categories.find? (·.name == name)
    | throwStratum .invalid m!"no registered category is named {name}"
  return entry

/-- Named bindings keep the existing unrefined default when one is published.
A separately named refinement is still a binding in its own right; if all rows
with that name are refined, they remain eligible and ambiguity is checked normally. -/
def objectBindings (state : RegistryState) (name : String)
    (category? : Option NamedCategoryEntry) : Array ObjectEntry :=
  let named := state.objects.filter (·.name == name)
  match category? with
  | some category => named.filter (·.category == category.id)
  | none =>
      let unrefined := named.filter (·.refines.isNone)
      if unrefined.isEmpty then named else unrefined

/-- The registered object named `name`, at its explicit category or its admitted
default binding. A unique separately named refinement needs no repeated category. -/
def objectNamed (state : RegistryState) (name : String) (category? : Option NamedCategoryEntry) :
    TermElabM ObjectEntry := do
  let candidates := objectBindings state name category?
  match candidates with
  | #[object] => return object
  | #[] => throwStratum .invalid m!"no registered object is named {name}{match category? with
      | some c => m!" in {c.name}" | none => m!""}"
  | _ => throwSemanticAmbiguity m!"several registered objects are named {name}: state its \
      category (`in C`)"

/-- A surface form selects the exact family declared by the mathematical registry. -/
def objectNotation (state : RegistryState) (surfaceForm : String) : TermElabM ObjectEntry := do
  match state.objects.filter (·.notations.contains surfaceForm) with
  | #[entry] => return entry
  | #[] => throwStratum .invalid m!"no registered object owns the notation {surfaceForm}"
  | _ => throwSemanticAmbiguity m!"several registered objects own the notation {surfaceForm}"

/-- Power-object structure is selected by its registered category, never by row order. -/
def powerObjectIn (state : RegistryState) (category : CategoryId) : TermElabM PowerObjectEntry := do
  let rows := state.powerObjects.filter fun power =>
    state.objects.any fun object => object.id == power.object && object.category == category
  match rows with
  | #[entry] => return entry
  | #[] => throwStratum .invalid m!"no registered power object in {category.raw}"
  | _ => throwSemanticAmbiguity m!"several registered power objects in {category.raw}"

/-- The exact terminal source published with the registry's power-object structure. -/
def globalPointSource : M Expr := do
  let power ← powerObjectIn (← registryState) CategoryId.sets
  let truth ← instantiateFresh power.truth
  let type ← whnfR (← inferType truth)
  unless type.isAppOf ``Quiver.Hom do
    throwStratum .invalid m!"the registered truth map has no terminal source"
  return type.appFn!.appArg!

/-- The selected point of the registered global-element source. Computational decoding uses
this same declaration, so its concrete representation is not part of the protocol. -/
def globalPoint : M Expr := do
  let power ← powerObjectIn (← registryState) CategoryId.sets
  let point ← instantiateFresh power.point
  unless ← isDefEq (← inferType point) (← globalPointSource) do
    throwStratum .invalid m!"the registered global point has a different terminal source"
  return point

/-- A term for an elaborated expression. -/
def quoteExpr (e : Expr) : TermElabM Term := exprToSyntax e

/-- A term as written. -/
def shown (stx : Syntax) : String := (stx.reprint.getD (toString stx)).trimAscii.toString

/-- The component pattern carried by the parenthesized map syntax. -/
def lambdaPattern (stx : Syntax) : Syntax := mkNode ``casTuple (stx.getArgs.extract 0 5)

/-- Names bound by a component pattern. Its shape and arity are checked against the selected
object when it is bound, so syntax never supplies a coordinate map. -/
partial def patternNames (stx : Syntax) : Array Name :=
  match stx with
  | `(cas_term| $name:ident) => #[name.getId]
  | `(cas_term| ($pattern)) => patternNames pattern
  | _ => if stx.getKind == ``casTuple then
      (#[stx[1]] ++ stx[3].getSepArgs).flatMap patternNames
    else #[]

/-- Numeral expressions and literals composed of them can use a supplied domain. Recognize
their syntax explicitly: a named mathematical atom has its own domain even when its notation
contains no identifier. Roots, absolute values and other named operations determine their own
domains; literals otherwise use the registered default when no context supplies one. -/
partial def numeric (stx : Syntax) : Bool :=
  match stx with
  | `(cas_term| $_:num) | `(cas_term| $_:scientific) => true
  | `(cas_term| ($t)) | `(cas_term| -$t) | `(cas_term| $t²) | `(cas_term| $t³) => numeric t
  | `(cas_term| $a + $b) | `(cas_term| $a - $b) | `(cas_term| $a · $b)
  | `(cas_term| $a / $b) | `(cas_term| $a ^ $b) => numeric a && numeric b
  | `(cas_term| {$xs,*}) => xs.getElems.all fun x => numeric x
  | _ =>
      if stx.getKind == nullKind then stx.getArgs.all numeric
      else if stx.getKind == ``casTimes then numeric stx[0] && numeric stx[2]
      else if stx.getKind == ``casTuple then
        (#[stx[1]] ++ stx[3].getSepArgs).all numeric
      else if stx.getKind == ``casMatrix then
        stx[1].getSepArgs.all fun row => row.getSepArgs.all numeric
      else false

/-- Whether a term names a registered object (`ℤ`, `Fin(3)`, `ℤ/5`, a binding of one), read from
its syntax and the registry: an object named is then read by `namedObject`, whose failures are
invalidity, never a cue to read the term some other way. -/
partial def namesObject (scope : Scope) (stx : Syntax) : M Bool := do
  let state ← registryState
  match stx with
  | `(cas_term| ($t)) => namesObject scope t
  | `(cas_term| $t in $_:ident) => namesObject scope t
  | `(cas_term| $x:ident) =>
      if ((← read).bound.lookup x.getId).isSome then return false
      if let some t := scope.get? x.getId then return ← namesObject scope t
      return state.objects.any (·.name == x.getId.toString)
  | `(cas_term| $f:ident($_,*)) => return state.objects.any (·.name == f.getId.toString)
  | `(cas_term| ℤ / $_) => return true
  | `(cas_term| (ℤ / $_) ^ $_) => return true
  | _ => return stx.getKind == ``casAtom

/-- Select a registered object row from its head without interpreting its parameters.
Refinement selection needs only the row name; the selected constructor subsequently checks
every argument against its complete dependent signature. -/
partial def namedObjectEntry (scope : Scope) (stx : Syntax) : M ObjectEntry := do
  let state ← registryState
  match stx with
  | `(cas_term| ($t)) => namedObjectEntry scope t
  | `(cas_term| $t in $c:ident) =>
      let entry ← namedObjectEntry scope t
      return ← objectNamed state entry.name (some (← categoryNamed state c.getId.toString))
  | `(cas_term| $x:ident) =>
      if let some t := scope.get? x.getId then return ← namedObjectEntry scope t
      return ← objectNamed state x.getId.toString none
  | `(cas_term| $f:ident($_,*)) => return ← objectNamed state f.getId.toString none
  | `(cas_term| ℤ / $_) => return ← objectNotation state "ℤ/"
  | `(cas_term| (ℤ / $_) ^ $_) => return ← objectNotation state "(ℤ/)^"
  | _ =>
      match stx.getKind == ``casAtom, stx.find? (·.isAtom) with
      | true, some atom => return ← objectNamed state atom.getAtomVal none
      | _, _ => throwStratum .invalid m!"{shown stx} does not name a registered object"

/-- Whether a numeric term is a fraction or a decimal, whose numerals are those of `ℚ`. -/
partial def fractional (stx : Syntax) : Bool :=
  stx.isOfKind `scientific || (stx.isAtom && stx.getAtomVal == "/") || stx.getArgs.any fractional

/-- The object of the catalogue a set value is. -/
def semanticObject (v : Value) : M Expr := do
  match v with
  | .object handle .. | .derivedObject handle .. => return handle
  | _ => throwStratum .invalid m!"a set is expected"

/-- The actual selected category of an object, including an unnamed derived context. -/
def objectContext (value : Value) : M CategoryContext := do
  match value with
  | .object object category .. => CategoryContext.ofNamed category object
  | .derivedObject object context _ =>
      CategoryContext.checkObject context object
      return context
  | _ => throwStratum .invalid "a complete selected object context is required"

def objectInContext (object : Expr) (context : CategoryContext)
    (known : Array Value := #[]) : M Value := do
  let context ← CategoryContext.presented context
  CategoryContext.checkObject context object
  if let some category := CategoryContext.named? (← registryState) context.expression then
    return retainObjectContext (.object object category none none none) known
  return .derivedObject object context known

def morphismInContext (value source target : Expr) (context : CategoryContext)
    (endpoints : Value × Value) : M Value := do
  let context ← CategoryContext.presented context
  CategoryContext.checkMorphism context value source target
  if let some category := CategoryContext.named? (← registryState) context.expression then
    return .morphism value source target category (some endpoints)
  return .derivedMorphism value source target context endpoints

def morphismContext (value : Value) :
    M (Expr × Expr × Expr × CategoryContext × Value × Value) := do
  match value with
  | .morphism hom source target category endpoints =>
      let context ← CategoryContext.ofNamed category source
      CategoryContext.checkMorphism context hom source target
      let (first, second) := endpoints.getD
        (.object source category none none none, .object target category none none none)
      return (hom, source, target, context, first, second)
  | .derivedMorphism hom source target context (first, second) =>
      CategoryContext.checkMorphism context hom source target
      return (hom, source, target, context, first, second)
  | _ => throwStratum .invalid "a complete typed morphism is required"

/-- The parameters of a family, as terms of its mathematics: numerals, the objects of sets, and
elements. -/
def paramTerms (values : Array Value) : M (Array Term) :=
  values.mapM fun
    | .nat n => pure (Syntax.mkNumLit (toString n) : Term)
    | v@(.object ..) | v@(.derivedObject ..) => do exprToSyntax (← semanticObject v)
    | .element handle _ | .morphism handle .. | .derivedMorphism handle .. => exprToSyntax handle
    | _ => throwStratum .invalid m!"a parameter is a numeral, an object, an element or a morphism"

/-- Exact registered refinement ancestry; shared carriers confer no identity. -/
def refinesObject (state : RegistryState) (entry : ObjectEntry) (base : ObjectId) : Bool := Id.run do
  let mut current := entry
  for _ in [0:state.objects.size + 1] do
    if current.id == base then return true
    let some refinement := current.refines | return false
    let some parent := state.objects.find? (·.id == refinement.base) | return false
    current := parent
  return false

/-- The complete carrier route and identifications actually declared by refinement ancestry. -/
def declaredCarrierRoute (state : RegistryState) (entry : ObjectEntry) :
    Option (Array EdgeRef × Array Name) := Id.run do
  let mut current := entry
  let mut route := #[]
  let mut identifications := #[]
  for _ in [0:state.objects.size + 1] do
    if current.category == CategoryId.sets then return some (route, identifications)
    let some refinement := current.refines | return none
    route := route ++ refinement.route
    identifications := identifications.push refinement.identification
    let some parent := state.objects.find? (·.id == refinement.base) | return none
    current := parent
  return none

/-- Isolate speculative unification and suppress speculative trace records. -/
def parameterTrial {α : Type} (action : M α) : M α := do
  let context ← read
  liftM (withoutModifyingState (action.run { context with trace := none }))

/-- Only declared inapplicability discards a trial; ambiguity and interpreter failures survive. -/
def parameterCompatible (action : M Bool) : M Bool := do
  try parameterTrial action
  catch error =>
    if (CasCatalogue.Exception.interpretationKind error) == .invalid then pure false else throw error

/-- Commit a successful reading once. Only declared inapplicability restores the full
elaborator, operation trace and closed-term cache before another interpretation is tried. -/
def optionalReading {α : Type} (action : M α) : M (Option α) := do
  let saved ← liftM Term.saveState
  let context ← read
  let recorded ← context.trace.mapM fun trace => do pure (trace, ← trace.get)
  let cached ← context.closedTerms.mapM fun cache => do pure (cache, ← cache.get)
  try return some (← action)
  catch error =>
    unless CasCatalogue.Exception.interpretationKind error == .invalid do throw error
    liftM (saved.restore true)
    for (trace, entries) in recorded.toArray do trace.set entries
    for (cache, entries) in cached.toArray do cache.set entries
    return none

/-- A dependent category's carrier parameter can prevent unification before the selected
object is known. Its rigid type constructor and closed arguments still rule out unrelated
categories. The complete route image must subsequently satisfy the actual expected type. -/
def parameterCategoryCompatible (expected : Expr) (category : NamedCategoryEntry) : M Bool :=
  parameterCompatible do
    let family ← instantiateFresh category.declaration
    let objectType ← mkAppM ``CategoryTheory.Bundled.α #[family]
    if ← parameterTrial (isDefEq objectType expected) then return true
    let objectType ← instantiateMVars objectType
    unless objectType.hasExprMVar do return false
    let actual ← withTransparency .all <| whnf objectType
    let required ← withTransparency .all <| whnf expected
    let actualHead := actual.getAppFn
    let requiredHead := required.getAppFn
    if actualHead.hasExprMVar || requiredHead.hasExprMVar then return true
    unless ← isDefEq actualHead requiredHead do return false
    let actualArguments := actual.getAppArgs
    let requiredArguments := required.getAppArgs
    unless actualArguments.size == requiredArguments.size do return false
    for (actualArgument, requiredArgument) in actualArguments.zip requiredArguments do
      unless actualArgument.hasExprMVar || requiredArgument.hasExprMVar do
        unless ← isDefEq actualArgument requiredArgument do return false
    return true

/-- A result type with a rigid function, inductive, or primitive quotient head cannot
become a different such type by filling declaration parameters. An unresolved projection or eliminator
is deliberately inconclusive. This checks inapplicability before parameter reading;
it neither supplies a structure from a carrier nor identifies complete parameters. -/
def incompatibleTypeShapes (left right : Expr) : M Bool := parameterTrial do
  unless (← isType left) && (← isType right) do return false
  let left ← withTransparency .all <| whnf (← instantiateMVars left)
  let right ← withTransparency .all <| whnf (← instantiateMVars right)
  let rigidTypeHead? (value : Expr) : MetaM (Option Name) := do
    let some head := value.getAppFn.constName? | return none
    match ← getConstInfo head with
    | .inductInfo _ => return some head
    | .quotInfo info =>
        match info.kind with
        | .type => return some head
        | _ => return none
    | _ => return none
  match left, right with
  | .forallE .., .forallE .. | .sort .., .sort .. => return false
  | .forallE .., .sort .. | .sort .., .forallE .. => return true
  | .forallE .., _ | .sort .., _ => return (← rigidTypeHead? right).isSome
  | _, .forallE .. | _, .sort .. => return (← rigidTypeHead? left).isSome
  | _, _ =>
      match ← rigidTypeHead? left, ← rigidTypeHead? right with
      | some a, some b => return a != b
      | _, _ => return false

/-- Replay complete retained edge applications without inferring new edge parameters. -/
partial def retainedActions (state : RegistryState) (source : Expr) (route : Array EdgeRef)
    (arguments : Array (EdgeRef × Array Expr)) : M (Expr × Array Expr) := do
  unless route.size == arguments.size do
    throwStratum .invalid m!"the structural view lost an actual edge application"
  let mut image := source
  let mut applications : Array Expr := #[]
  for (edge, (retainedEdge, params)) in route.zip arguments do
    unless edge == retainedEdge do
      throwStratum .invalid m!"the retained structural action has a different edge order"
    let registered ← Semantic.edgeFunctor state edge
    let actual := mkAppN registered.getAppFn params
    unless ← isTypeCorrect actual do
      throwStratum .invalid m!"a retained structural action is outside its full declaration type"
    unless ← isDefEq registered actual do
      throwStratum .invalid m!"a retained action is not its accepted registered edge"
    image ← Semantic.objOf actual image
    let actual ← instantiateMVars actual
    unless !actual.hasMVar && !actual.hasLevelMVar do
      throwStratum .invalid m!"a retained structural action is not fully instantiated"
    applications := applications.push actual
  return (image, applications)

/-- The remaining declared carrier route of an exact retained structured view.
Each source prefix is checked at the complete selected object before taking its suffix. -/
partial def retainedCarrierRoute (state : RegistryState) (value : Value) :
    M (Option (Array EdgeRef)) := do
  let .object handle _ origin viewSelected viewData := value | return none
  if let some (entry, _) := origin then
    if let some (route, _) := declaredCarrierRoute state entry then return some route
  if let some (_, source, route, _, arguments) := viewData then
    let some carrierRoute ← retainedCarrierRoute state source | return none
    if route.size > carrierRoute.size || carrierRoute.extract 0 route.size != route then
      return none
    let .object receiver .. := source | return none
    let (image, _) ← retainedActions state receiver route arguments
    unless ← isDefEq image handle do
      throwStratum .invalid m!"the retained structural prefix does not give this complete object"
    return some (carrierRoute.extract route.size carrierRoute.size)
  if let some selected := viewSelected then
    let .object selectedHandle selectedCategory .. := selected | return none
    let .object _ category .. := value | return none
    if selectedCategory.id == category.id && (← isDefEq selectedHandle handle) then
      return ← retainedCarrierRoute state selected
  return none


/-- Apply the same accepted route construction whose complete edge arguments are retained.
The receiver and expected endpoint close its actual parameters before any trace is recorded. -/
def checkedRouteAction (state : RegistryState) (source target : CategoryId)
    (route : Array EdgeRef) (receiver expected : Expr) : M (Expr × Array Expr) := do
  let (image, applications) ← if route.isEmpty then pure (receiver, #[]) else do
    let (functor, applications) ← Semantic.routeFunctorWithApplications state route
    let image ← Semantic.objOf functor receiver
    pure (image, applications)
  unless ← isDefEq (← inferType image) expected do
    throwStratum .invalid m!"an actual structural action is outside its declared endpoint type"
  let image ← instantiateMVars image
  let applications ← applications.mapM instantiateMVars
  unless !image.hasMVar && !image.hasLevelMVar && (← isTypeCorrect image) &&
      applications.all (fun action => !action.hasMVar && !action.hasLevelMVar) &&
      (← applications.allM fun action => isTypeCorrect action) do
    throwStratum .invalid m!"a structural action has undetermined complete edge parameters"
  unless route.isEmpty do
    Trace.record (← read).trace image (.retainedRoute source target route applications receiver)
  return (image, applications)

/-- Every structural route from `source` to `target` (`RegistryState.completeRoutes`). -/
def routesBetween (state : RegistryState) (source target : CategoryExpr) : M (Array Route) := do
  match state.completeRoutes source target with
  | .ok routes => return routes
  | .error error => throwResolutionError state error

mutual
/-- Read explicit parameters sequentially at the declaration's dependent binder types. -/
partial def typedParamTerms (declaration : Name) (values : Array Value) : M (Array Term) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (args.zip infos).filterMap fun (a, i) => if i.isExplicit then some a else none
  unless values.size ≤ explicit.size do
    throwStratum .invalid m!"{declaration} takes {explicit.size} explicit parameters"
  let mut terms := #[]
  for (parameter, value) in explicit.zip values do
    let expected ← instantiateMVars (← inferType parameter)
    let argument ← typedParameter expected value
    unless ← isDefEq (← inferType argument) expected <&&> isDefEq parameter argument do
      throwStratum .invalid m!"a parameter of {declaration} is outside its declared type"
    terms := terms.push (← quoteExpr (← instantiateMVars argument))
  return terms

/-- Transport one already selected structured object at a declared object type. Every candidate
is an actual registered structural composite, and only admitted comparisons identify routes. -/
partial def transportedStructure (expected : Expr) (value : Value)
    (demandedCategory : Option CategoryId := none) : M Expr := do
  let .object receiver sourceCategory _ _ _ := value
    | throwStratum .invalid m!"a selected structural parameter is an object"
  let state ← registryState
  let mut candidates : Array (NamedCategoryEntry × Route) := #[]
  for target in state.categories do
    if demandedCategory.any (· != target.id) then continue
    let targetTyped ← parameterCategoryCompatible expected target
    unless targetTyped do continue
    for route in (← routesBetween state sourceCategory.expression target.expression) do
      if ← parameterCompatible (do
          let image ← if route.steps.isEmpty then pure receiver else
            Semantic.objOf (← Semantic.routeFunctor state route.refs) receiver
          isDefEq (← inferType image) expected) then
        candidates := candidates.push (target, route)
  let classifiedCandidates := match ← retainedCarrierRoute state value with
    | none => candidates
    | some carrierRoute =>
        let prefixes := candidates.filter fun (_, route) =>
          route.refs.size ≤ carrierRoute.size &&
            decide (route.refs = carrierRoute.extract 0 route.refs.size)
        if prefixes.isEmpty then candidates else prefixes
  letI : Inhabited (NamedCategoryEntry × Route) :=
    ⟨(sourceCategory, { source := sourceCategory.expression, target := sourceCategory.expression, steps := #[] })⟩
  do
    let (target, route) ← match state.classify classifiedCandidates (fun c => c.1.id.raw) (·.2) with
      | #[cls] =>
        unless cls.ambiguities.isEmpty do
          throwSemanticAmbiguity m!"several comparisons determine a selected structural route"
        discard <| Semantic.validateRouteComparisons state cls.comparisonWitnesses (some receiver)
        let #[candidate] := cls.sources
          | throwSemanticAmbiguity m!"the selected object has no unique structural route"
        pure candidate
      | #[] => throwStratum .invalid m!"the selected object has no registered structure at this type"
      | _ => throwSemanticAmbiguity m!"several routes give the selected object this structure \
          (source {sourceCategory.id.raw}, demanded type {expected}, receiver {receiver})"
    let (image, _) ← checkedRouteAction state sourceCategory.id target.id route.refs receiver expected
    return image

partial def typedParameter (expected : Expr) (value : Value) : M Expr := do
  if let .formalProof proofSyntax := value then
    unless ← isProp expected do
      throwStratum .invalid "an explicit proof supplies a proposition-valued parameter only"
    let proof ← instantiateMVars (← elabTermAndSynthesize proofSyntax (some expected))
    let expected ← instantiateMVars expected
    unless ConstrainedPoint.closed proof && ConstrainedPoint.closed expected &&
        (← Decide.kernelAccepts expected proof) do
      throwStratum .invalid "the explicit parameter proof is not a closed proof accepted by Lean"
    return proof
  let direct ← match value with
    | .nat n => pure (mkNatLit n)
    | .object handle .. | .element handle _ | .morphism handle .. |
        .derivedObject handle .. | .derivedMorphism handle .. => pure handle
    | _ => throwStratum .invalid m!"a parameter is a numeral, an object or an element"
  if ← parameterTrial (isDefEq (← inferType direct) expected) then
    unless ← isDefEq (← inferType direct) expected do unreachable!
    return direct
  if let .element point X@(.object target _ _ selected _) := value then
    let type ← whnfR (← inferType point)
    unless type.isAppOf ``Quiver.Hom &&
        (← isDefEq type.appFn!.appArg! (← globalPointSource)) &&
        (← isDefEq type.appArg! target) && (← isDefEq target expected) do
      throwStratum .invalid m!"only a closed point of the declared type is an element parameter"
    let scalar ← instantiateMVars (← elabTermAndSynthesize
      (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr point)
        $(← quoteExpr (← globalPoint)))) (some expected))
    unless !scalar.hasMVar && !scalar.hasLevelMVar && (← isTypeCorrect scalar) do
      throwStratum .invalid m!"the closed element parameter is outside its declared type"
    let chosen := selected.getD X
    Trace.record (← read).trace scalar (.elementValue point target (← semanticObject chosen))
    return scalar
  if let .morphism hom _ _ category _ := value then
    unless category.id == CategoryId.sets do
      throwStratum .invalid m!"the map parameter has no selected function carrier at this type"
    let function ← instantiateMVars (← elabTermAndSynthesize
      (← `(fun x => CategoryTheory.ConcreteCategory.hom (C := Type)
        $(← quoteExpr hom) x)) (some expected))
    unless !function.hasMVar && !function.hasLevelMVar && (← isTypeCorrect function) &&
        (← isDefEq (← inferType function) expected) do
      throwStratum .invalid m!"the closed map parameter is outside its declared function type"
    Trace.alias (← read).trace hom function
    return function
  let .object _ selectedCategory origin? selected _ := value
    | throwStratum .invalid m!"a parameter has no selected object at its declared type"
  if (← whnfR expected).isSort then
    let state ← registryState
    let image ← match ← retainedCarrierRoute state value with
      | some route => do
          let (image, _) ← checkedRouteAction state selectedCategory.id CategoryId.sets route direct expected
          pure image
      | none => transportedStructure expected value (some CategoryId.sets)
    let image ← instantiateMVars image
    unless !image.hasMVar && !image.hasLevelMVar && (← isTypeCorrect image) &&
        (← isDefEq (← inferType image) expected) do
      throwStratum .invalid m!"the selected object's actual carrier is outside its declared type"
    return image
  if let some chosen := selected then return ← typedParameter expected chosen
  let some (origin, parameters) := origin?
    | return ← transportedStructure expected value
  let state ← registryState
  -- An explicitly selected structure supplies its own outgoing routes. An unstructured named
  -- set may acquire only structures whose registered refinement ancestry reaches that exact row.
  let sources := if selectedCategory.id == CategoryId.sets then
      state.objects.filter (refinesObject state · origin.id)
    else #[origin]
  let targetCategories ← state.categories.filterM (parameterCategoryCompatible expected)
  let mut routeCandidates : Array (ObjectEntry × Route) := #[]
  for source in sources do
    let some sourceCategory := state.categories.find? (·.id == source.category) | continue
    -- Reachability depends only on the registered category expressions. A source with no
    -- route to the required object type cannot supply this parameter, and constructing all
    -- of its own dependent parameters would add no candidate or ambiguity evidence.
    let mut possibleRoutes : Array Route := #[]
    for targetCategory in targetCategories do
      possibleRoutes := possibleRoutes ++
        (← routesBetween state sourceCategory.expression targetCategory.expression)
    if possibleRoutes.isEmpty then continue
    let sourceTerm? ← parameterTrial do
      try
        let term ← Semantic.object source (← typedParamTerms source.declaration parameters)
        if term.hasMVar || term.hasLevelMVar then return none
        return some term
      catch error =>
        if Exception.interpretationKind error == .invalid then return none else throw error
    let some sourceTerm := sourceTerm? | continue
    for route in possibleRoutes do
      let applicable ← parameterCompatible do
        let image ← if route.steps.isEmpty then pure sourceTerm else
          Semantic.objOf (← Semantic.routeFunctor state route.refs) sourceTerm
        isDefEq (← inferType image) expected
      if applicable then routeCandidates := routeCandidates.push (source, route)
  let declaredPrefixes := routeCandidates.filter fun (source, route) =>
    (declaredCarrierRoute state source).any fun (carrierRoute, _) =>
      route.refs.size ≤ carrierRoute.size &&
        decide (route.refs = carrierRoute.extract 0 route.refs.size)
  let candidates := if declaredPrefixes.isEmpty then routeCandidates else declaredPrefixes
  letI : Inhabited (ObjectEntry × Route) :=
    ⟨(origin, { source := selectedCategory.expression, target := selectedCategory.expression, steps := #[] })⟩
  do
    -- Every eligible declared source participates in the full structured-image check.
    -- A zero-step path is not evidence that another source selects the same structure.
    let sourceIds := (candidates.map (·.1.id)).foldl (fun found id =>
      if found.contains id then found else found.push id) #[]
    let mut sourceChoices : Array (ObjectEntry × Route) := #[]
    let mut checkedSources : Array (ObjectId × Expr) := #[]
    for sourceId in sourceIds do
      let sourceCandidates := candidates.filter (·.1.id == sourceId)
      let classes := state.classify sourceCandidates (fun c => c.1.id.raw) (·.2)
      let (candidate, selected) ← match classes with
        | #[cls] =>
          unless cls.ambiguities.isEmpty do
            throwSemanticAmbiguity m!"several registered comparisons determine a parameter route"
          let #[candidate] := cls.sources
            | throwSemanticAmbiguity m!"a parameter has no unique registered source route"
          let selected ← Semantic.object candidate.1
            (← typedParamTerms candidate.1.declaration parameters) (← read).trace
          discard <| Semantic.validateRouteComparisons state cls.comparisonWitnesses (some selected)
          pure (candidate, selected)
        | _ => throwSemanticAmbiguity m!"a selected source has unresolved parameter routes"
      checkedSources := checkedSources.push (candidate.1.id, selected)
      sourceChoices := sourceChoices.push candidate
    if sourceChoices.isEmpty then
      throwStratum .invalid m!"{origin.name} has no registered structure at the parameter's type \
        {expected}: refining sources {sources.map (·.id.raw)}, route candidates \
        {routeCandidates.size}"
    let selectedCandidates := sourceChoices.qsort fun left right =>
      let leftKey := left.1.id.raw ++ reprStr left.2.refs
      let rightKey := right.1.id.raw ++ reprStr right.2.refs
      leftKey < rightKey
    let mut presentations : Array ParameterPresentation := #[]
    let mut representative? : Option Expr := none
    for (source, route) in selectedCandidates do
      let some (_, sourceTerm) := checkedSources.find? (·.1 == source.id)
        | throwError "a classified parameter source lost its exact recorded application"
      let some target := state.categories.find? (·.expression.syntacticEq route.target)
        | throwStratum .invalid m!"a parameter route has no registered target category"
      let (image, applications) ← checkedRouteAction state source.category target.id
        route.refs sourceTerm expected
      unless !image.hasMVar && (← isDefEq (← inferType image) expected) && (← isTypeCorrect image) do
        throwStratum .invalid m!"a structural parameter is outside its complete declared type"
      let representative := representative?.getD image
      unless ← withTransparency .all <| isDefEq image representative do
        throwSemanticAmbiguity m!"several distinct full structures determine a parameter of {origin.name}"
      representative? := some representative
      let identity ← mkEqRefl representative
      unless (← isTypeCorrect identity) &&
          (← withTransparency .all <| isDefEq (← inferType identity) (← mkEq image representative)) do
        throwStratum .invalid m!"a complete structure identity failed kernel conversion"
      let infos ← forallTelescopeReducing (← getConstInfo source.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let mut application := sourceTerm.consumeMData
      while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
      let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
        if info.isExplicit then some arg else none
      let (carrierRoute, identifications) := (declaredCarrierRoute state source).getD (#[], #[])
      presentations := presentations.push
        { source := source.id, sourceCategory := source.category, targetCategory := target.id,
          params := params, route := route.refs, carrierRoute := carrierRoute,
          identifications := identifications, object := sourceTerm, image := image,
          applications := applications, identity := identity }
    let some representative := representative? | unreachable!
    if presentations.size == 1 then
      let some presentation := presentations[0]? | unreachable!
      if presentation.route.isEmpty then
        Trace.record (← read).trace representative
          (.object presentation.source presentation.params)
      else
        Trace.record (← read).trace representative
          (.retainedRoute presentation.sourceCategory presentation.targetCategory
            presentation.route presentation.applications presentation.object)
    else
      Trace.record (← read).trace representative
        (.parameterEquivalence (← instantiateMVars expected) representative presentations)
    return representative
end

/-- The numerals among `values`, as terms. -/
def numeralTerms (name : String) (values : Array Value) : TermElabM (Array Term) :=
  values.mapM fun
    | .nat n => pure (Syntax.mkNumLit (toString n) : Term)
    | _ => throwStratum .invalid m!"the parameters of {name} are numerals"

/-- Read the diagram owned by a registered presentation, at its actual dependent arguments.
In particular, a shape label does not choose a distinguished second arrow. -/
def declaredDiagram (row : LimitEntry) (values : Array Value) : M Expr := do
  let constant ← mkConstWithFreshMVarLevels row.declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (args.zip infos).filterMap fun (p, info) => if info.isExplicit then some p else none
  unless values.size ≤ explicit.size do
    throwStratum .invalid m!"the registered presentation takes fewer arguments"
  let supplied := explicit.extract (explicit.size - values.size) explicit.size
  for (parameter, value) in supplied.zip values do
    let expected ← instantiateMVars (← inferType parameter)
    let term ← typedParameter expected value
    unless ← isDefEq parameter term do
      throwStratum .invalid m!"a presentation argument is outside its declared type"
  for (arg, info) in args.zip infos do
    unless info.isInstImplicit && (← instantiateMVars arg).isMVar do continue
    let expected ← instantiateMVars (← inferType arg)
    if expected.hasMVar then continue
    if let some synthesized ← synthInstance? expected then discard <| isDefEq arg synthesized
  let presentation ← instantiateMVars (mkAppN constant args)
  if presentation.hasMVar then
    throwStratum .invalid m!"the presentation parameters are not determined"
  unless ← isTypeCorrect presentation do
    throwStratum .invalid m!"a presentation argument is outside its dependent signature"
  let type ← whnfR (← instantiateMVars type)
  return type.appArg!

/-- The standard diagram of the shape `shape` on the values `args` (Mathlib's standard forms). -/
def standardDiagram (shape : String) (args : Array Value) : M Term := do
  let handle : Value → M Expr
    | .object handle .. | .derivedObject handle .. => pure handle
    | .morphism hom .. | .derivedMorphism hom .. => pure hom
    | _ => throwStratum .invalid m!"the diagram of a {shape} is of objects and morphisms"
  let state ← registryState
  let context? : Option CategoryContext ← args[0]?.mapM fun (value : Value) => do
    match value with
    | .object .. | .derivedObject .. => objectContext value
    | .morphism .. | .derivedMorphism .. => do
        let (_, _, _, context, _, _) ← morphismContext value
        pure context
    | _ => throwStratum .invalid m!"the diagram of a {shape} requires a complete category context"
  let category? := context?.bind fun context => CategoryContext.named? state context.expression
  if let some category := category? then
    let rows := state.limits.filter fun row => row.shape == shape && row.category == category.id
    match rows with
    | #[row] => return ← quoteExpr (← declaredDiagram row args)
    | #[] => pure ()
    | _ => throwSemanticAmbiguity m!"several registered presentations own this diagram"
  let values ← args.mapM handle
  -- A lower presentation supplies the constructor of its diagram. Reapply that constructor
  -- to the actual source arguments: lower objects are never unified with source objects, and
  -- a shape string never manufactures distinguished arrows such as zero or the trivial map.
  let construct (name : Name) : M Expr := do
    let constant ← mkConstWithFreshMVarLevels name
    let (parameters, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
    let explicit := (parameters.zip infos).filterMap fun (p, info) =>
      if info.isExplicit then some p else none
    unless explicit.size == values.size do
      throwStratum .invalid m!"the registered diagram constructor takes {explicit.size} arguments"
    if let some context := context? then
      let (_, target) ← functorCategoryBundles (mkAppN constant parameters)
      unless ← withTransparency .all <| isDefEq target context.bundle do
        throwStratum .invalid "the diagram constructor changes its complete selected category"
    for (parameter, value) in explicit.zip values do
      unless ← isDefEq (← inferType parameter) (← inferType value) <&&> isDefEq parameter value do
        throwStratum .invalid m!"a source argument is outside the registered diagram signature"
    for (parameter, info) in parameters.zip infos do
      unless info.isInstImplicit && (← instantiateMVars parameter).isMVar do continue
      let expected ← instantiateMVars (← inferType parameter)
      if expected.hasMVar then continue
      if let some synthesized ← synthInstance? expected then discard <| isDefEq parameter synthesized
    let diagram ← instantiateMVars (mkAppN constant parameters)
    if diagram.hasMVar || !(← isTypeCorrect diagram) then
      throwStratum .invalid m!"the registered diagram constructor has undetermined parameters"
    unless (← whnfR (← inferType diagram)).isAppOf ``CategoryTheory.Functor do
      throwStratum .invalid m!"the registered constructor does not form a diagram"
    return diagram
  let mut constructors : Array Name := #[]
  for row in state.limits.filter (·.shape == shape) do
    if let some name ← Semantic.diagramConstructor row then
      unless constructors.contains name do constructors := constructors.push name
  let mut diagrams : Array Expr := #[]
  for constructor in constructors do
    if ← parameterCompatible (do discard <| construct constructor; pure true) then
      let diagram ← construct constructor
      unless ← diagrams.anyM (fun previous => parameterTrial (isDefEq previous diagram)) do
        diagrams := diagrams.push diagram
  match diagrams with
  | #[diagram] => quoteExpr diagram
  | #[] => throwStratum .invalid m!"a {shape} of {args.size} arguments has no registered diagram"
  | _ => throwSemanticAmbiguity m!"several registered constructions form this {shape} diagram"

/-- Whether a chain of registered inclusions leads from the object `sub` to `super` (at the same
parameters), or they are the same object. -/
def includes (state : RegistryState) (sub super : ObjectId) : Bool := Id.run do
  let mut reached : Array ObjectId := #[sub]
  let mut frontier : Array ObjectId := #[sub]
  for _ in [0:state.inclusions.size + 1] do
    let next := frontier.flatMap fun o =>
      (state.inclusions.filter (·.sub == o)).map (·.super) |>.filter (!reached.contains ·)
    reached := reached ++ next
    frontier := next
  return reached.contains super

/-- The registered inclusions `sub ↪ … ↪ super`, shortest first; `#[]` when they are the same. -/
def inclusionChain (state : RegistryState) (sub super : ObjectId) :
    Option (Array InclusionEntry) := Id.run do
  let mut paths : Array (ObjectId × Array InclusionEntry) := #[(sub, #[])]
  for _ in [0:state.inclusions.size + 1] do
    for (o, path) in paths do
      if o == super then return some path
    let next := paths.flatMap fun (o, path) =>
      (state.inclusions.filter (·.sub == o)).map fun e => (e.super, path.push e)
    paths := paths ++ next.filter fun (o, _) => !paths.any (·.1 == o)
  return none

/-- The ends of a morphism type `x ⟶ y`. -/
def homEnds? (type : Expr) : Option (Expr × Expr) :=
  match type.getAppFn.constName?, type.getAppArgs with
  | some ``Quiver.Hom, #[_, _, x, y] => some (x, y)
  | _, _ => none

/-- `C/Y` for a registered category family `C` over an object `Y` (`Algebras/ℂ`). -/
def categoryOver? (state : RegistryState) (stx : Syntax) : Option (NamedCategoryEntry × Syntax) :=
  match stx with
  | `(cas_term| $C:ident / $Y) =>
      -- The family named `C/` (`Schemes/`, beside the category `Schemes`), else `C`.
      let name := C.getId.toString
      (state.categories.find? (·.name == name ++ "/") <|>
        state.categories.find? (·.name == name)).map (·, Y.raw)
  | _ => none

/-- `x_7` as `x_` and `7`. -/
def indexed? (n : Name) : Option (String × Nat) :=
  let chars := n.toString.toList
  let digits := (chars.reverse.takeWhile Char.isDigit).reverse
  if digits.isEmpty || digits.length == chars.length then none
  else some (String.ofList (chars.take (chars.length - digits.length)), String.toNat! (String.ofList digits))

/-- The variables `x, y` or `x_0, x_1, ..., x_9` of `R[…]`: `...` runs through the indices between
its neighbours, which share their prefix. -/
def mvVariables (stx : Syntax) : Except String (Array Name) := do
  let items := #[stx[2]] ++ stx[4].getSepArgs.map fun v => if v[0].isIdent then v[0] else v[0]
  let mut names : Array Name := #[]
  let mut i := 0
  while i < items.size do
    let item := items[i]!
    if item.isIdent then
      names := names.push item.getId
      i := i + 1
    else
      let (some a, some b) := (names.back?, items[i + 1]?) | throw "`...` stands between variables"
      let (some (p, j), some (q, k)) := (indexed? a, indexed? b.getId)
        | throw "`...` stands between indexed variables `x_i, ..., x_k`"
      unless p == q && j < k do throw "`...` runs up between variables of one prefix"
      for m in [j + 1:k] do names := names.push (.mkSimple s!"{p}{m}")
      i := i + 1
  return names

/-- The polynomial rings `R[v]` a term writes, with those of the `let` bindings it uses: each with
its variable. -/
partial def ringsIn (scope : Scope) (seen : Array Name) (stx : Syntax) :
    Array (Name × Syntax × Option Nat) :=
  if stx.getKind == ``casRing || stx.getKind == ``casSeries then
    #[((if stx.getKind == ``casSeries then stx[3] else stx[2]).getId, stx, none)] ++
      ringsIn scope seen stx[0]
  else if stx.getKind == ``casMvRing then
    let names := (mvVariables stx).toOption.getD #[]
    names.mapIdx (fun i v => (v, stx, some i)) ++ ringsIn scope seen stx[0]
  else if stx.isIdent then
    -- `p.m` is the method `m` of `p`.
    let x := stx.getId.getRoot
    match scope.get? x with
    | some t => if seen.contains x then #[] else ringsIn scope (seen.push x) t
    | none => #[]
  else stx.getArgs.flatMap (ringsIn scope seen)

/-- The variable `v` that the name `dv` is the differential of. -/
def differentialOf? (n : Name) : Option Name :=
  match n with
  | .str .anonymous s =>
      if s.startsWith "d" && s.length > 1 then some (.mkSimple (String.ofList (s.toList.drop 1))) else none
  | _ => none


/-- The identifiers of a term, except the variables `v` of its rings `R[v]`. -/
partial def looseIdentifiers (stx : Syntax) : Array Name :=
  if stx.getKind == ``casRing || stx.getKind == ``casSeries || stx.getKind == ``casMvRing then
    looseIdentifiers stx[0]
  else if stx.getKind == ``casBig then
    looseIdentifiers stx[4] ++ (looseIdentifiers stx[6]).filter (· != stx[2].getId)
  else if stx.getKind == ``casLimit then
    looseIdentifiers stx[3] ++ (looseIdentifiers stx[5]).filter (· != stx[1].getId)
  else if stx.getKind == ``casDefinite then
    looseIdentifiers stx[1] ++ looseIdentifiers stx[3] ++
      (looseIdentifiers stx[5]).filter fun name =>
        name != stx[6].getId && differentialOf? stx[6].getId != some name
  else if stx.getKind == ``casPatternLambda then
    (looseIdentifiers stx[6]).filter (!(patternNames (lambdaPattern stx)).contains ·)
  else match stx with
    | `(cas_term| $bound:ident ↦ $body) =>
        (looseIdentifiers body).filter (· != bound.getId)
    | `(cas_term| {$bound:ident ∈ $domain | $body}) =>
        looseIdentifiers domain ++ (looseIdentifiers body).filter (· != bound.getId)
    | `(cas_term| {$body | $bound:ident ∈ $domain}) =>
        looseIdentifiers domain ++ (looseIdentifiers body).filter (· != bound.getId)
    | _ => if stx.isIdent then #[stx.getId] else stx.getArgs.flatMap looseIdentifiers

/-- `N₂₃` as `N` and `23`. -/
def subscripted? (s : String) : Option (String × Nat) :=
  let digits := "₀₁₂₃₄₅₆₇₈₉".toList
  let chars := s.toList
  let suffix := (chars.reverse.takeWhile digits.contains).reverse
  let base := chars.take (chars.length - suffix.length)
  if suffix.isEmpty || base.isEmpty then none
  else some (String.ofList base, suffix.foldl (fun n c => 10 * n + digits.idxOf c) 0)

/-- A three-valued decision as a value. -/
def answerOf (b : Option Bool) : Value := .answer (toExpr b)

/-- A fact the catalogue itself decides (a registered inclusion): `True`. No leaf is consulted. -/
def decided (question : Question) : M Value := return .judged question (mkConst ``True)

/-- The object of sets a named object refines, or itself if it is one: the set whose numerals are
its elements' names (`Fin n` of finite sets is the set `Fin n`). -/
def setOf (state : RegistryState) (entry : ObjectEntry) : TermElabM ObjectEntry := do
  let mut entry := entry
  for _ in [0:state.objects.size] do
    if entry.category == CategoryId.sets then return entry
    let some refinement := entry.refines
      | throwStratum .invalid m!"{entry.name} is not a set, nor refines one"
    let some base := state.objects.find? (·.id == refinement.base) | unreachable!
    entry := base
  throwStratum .invalid m!"the refinements of {entry.name} do not reach a set"

/-- Check one declared component refinement at the entire supplied structured
object. A valid row without a set/component presentation is simply inapplicable;
its unrelated base cannot obstruct another candidate's reading. -/
def componentRefinement? (state : RegistryState) (row : ObjectEntry) (actual : Expr) :
    TermElabM (Option (DirectConstruction.Application × ObjectEntry × ObjectComponents)) :=
  withoutModifyingState do
    try
      let application ← DirectConstruction.instantiate row.declaration #[]
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType application.value) (← inferType actual)) do
        CategoryContext.exposeStructureParameters application.value
      unless ← withTransparency .all <|
          isDefEq (← inferType application.value) (← inferType actual) <&&>
            isDefEq application.value actual do return none
      let application ← DirectConstruction.close application
      let base ← setOf state row
      let some components := base.components | return none
      return some (application, base, components)
    catch error =>
      if Exception.interpretationKind error == .invalid then return none else throw error

/-- The proof of the decidable proposition `p` by evaluating its decision: `decide p` reduces to
`true`. The one proof the kernel forms itself; it names no mathematics (`p` is a registered
row's side condition, such as `k < n` for the point `k` of `Fin n`), and a `p` whose decision does
not evaluate to `true` is not established. -/
def decideObligation (p : Expr) : MetaM (Option Expr) := do
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    if ← withoutModifyingState (isDefEq args[1]! args[2]!) then
      return some (← mkEqRefl args[1]!)
  let decision ← mkDecide p
  unless (← withAtLeastTransparency .default <| whnf decision).isConstOf ``Bool.true do
    return none
  some <$> mkDecideProof p

/-- The registered numeral `k` of the set `x` (a semantic object of sets), `1 ⟶ x`: the image of `k`
under the map out of the initial object of a category refining `x` (`ℕ → S` of a semiring, `ℤ → R`
of a ring), or the point `k` of `Fin n` (LC-15). `refinements` are the objects refining `x`, at its
parameters. The obligations of the numeral (`k < n`) are decided when the statement is read; one
that fails makes the statement invalid. `none` when no registered numeral lands in `x`. -/
def numeralIn (state : RegistryState) (k : Nat) (one x : Expr)
    (refinements : Array (CategoryId × Expr)) : TermElabM (Option Expr) := do
  let expected ← mkAppM ``Quiver.Hom #[one, x]
  let candidates : Array (NumeralEntry × Option Expr) := state.numerals.flatMap fun row =>
    match row.over with
    | none => #[(row, none)]
    | some c => (refinements.filter (·.1 == c)).map fun (_, R) => (row, some R)
  for (row, object?) in candidates do
    let c ← mkConstWithFreshMVarLevels row.declaration
    let (args, infos, type) ← forallMetaTelescopeReducing (← inferType c)
    let explicit := (List.range args.size).toArray.filter (infos[·]!.isExplicit)
    -- `k` is its last explicit numeral; the explicit propositions after it are its obligations.
    let some ki ← explicit.reverse.findM? fun i => return (← inferType args[i]!).isConstOf ``Nat
      | continue
    let lands ← withoutModifyingState do
      if let some R := object? then
        let some first := explicit[0]? | return false
        unless ← isDefEq args[first]! R do return false
      unless ← isDefEq args[ki]! (mkNatLit k) do return false
      isDefEq type expected
    unless lands do continue
    if let some R := object? then
      unless ← isDefEq args[explicit[0]!]! R do continue
    unless ← isDefEq args[ki]! (mkNatLit k) do continue
    unless ← isDefEq type expected do continue
    for i in explicit.filter (· > ki) do
      let obligation ← instantiateMVars (← inferType args[i]!)
      let some proof ← decideObligation obligation
        | throwStratum .invalid m!"{k} is not a numeral of {x}: {obligation} does not hold"
      unless ← isDefEq args[i]! proof do
        throwStratum .invalid m!"{k} is not a numeral of {x}"
    let value ← instantiateMVars (mkAppN c args)
    if value.hasMVar || value.hasLevelMVar then
      throwStratum .invalid m!"the numeral {row.id.raw} is not determined at {x}"
    unless ← isTypeCorrect value do
      throwStratum .invalid m!"the numeral {row.id.raw} is outside its complete declared type"
    let some (actualSource, actualTarget) := homEnds? (← inferType value) | continue
    unless ← withTransparency .all <| isDefEq actualSource one <&&> isDefEq actualTarget x do
      continue
    unless ← withTransparency .all <| isDefEq (← inferType value) expected do continue
    return some value
  return none

/-- The instance arguments of a family, synthesized once its operands have determined their
types (the `Monoid M` of division at `M = ℚ`). -/
def synthesizeInstances (args : Array Expr) (infos : Array BinderInfo) : TermElabM Unit := do
  for (a, i) in args.zip infos do
    unless i.isInstImplicit do continue
    unless (← instantiateMVars a).isMVar do continue
    let type ← instantiateMVars (← inferType a)
    if type.hasMVar then continue
    if let some inst ← synthInstance? type then
      discard <| isDefEq a inst

/-- The heads whose unfolding is the categorical and representational plumbing the kernel builds
values with (composites, identities, `ofHom`, limit presentations and their mediators, the
catalogue's definitions, function application of maps), as opposed to the mathematics a value is
made of (`Polynomial.X`, `Matrix.det`, `Real.exp`, a ring's operations). -/
def plumbingRoots : List Name :=
  [`CasCatalogue, `LeanCategories, `CategoryTheory, `TypeCat, `DFunLike, `FunLike, `Function,
   `id, `Prod.fst, `Prod.snd, `Prod.map, `inferInstance, `inferInstanceAs]

/-- Whether `e`, headed by a plumbing root, is plumbing to unfold. A coercion of a map to a
function (`DFunLike.coe F x`) is the kernel's plumbing only when `F` is a morphism the kernel
built (its type is a categorical hom); a ring homomorphism applied to a value (`Int.castRingHom R
2`, the numeral row's image) is mathematics, kept so that evidence is stated of it rather than of
`RingHom.toFun` (b0-domain-preservation). -/
def plumbingApplication (e : Expr) : MetaM Bool := do
  unless e.isAppOf ``DFunLike.coe do return true
  let some F := e.getAppArgs[4]? | return true
  let type ← whnfR (← inferType F)
  return type.isAppOf ``Quiver.Hom || (type.getAppFn.constName?.map
    (fun c => [`CategoryTheory, `TypeCat].any (·.isPrefixOf c))).getD false

/-- A value with its plumbing unfolded (`plumbingRoots`), its mathematics kept: `!![1, 2; 3, 4]`
for a matrix assembled from rows of tuples through product mediators, `X ^ 3 - 2 X + 1` for a
polynomial assembled by the ring operations of `ℚ[x]`. Definitionally the value it was given
(every step is an unfolding or a reduction); the caller checks that. -/
partial def plumbingValue (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e with
  | .lam .. => lambdaTelescope e fun xs body => do mkLambdaFVars xs (← plumbingValue body)
  | .proj name index value =>
      let env ← getEnv
      let projection? := do
        let info ← getStructureInfo? env name
        let field ← info.fieldNames[index]?
        getProjFnForField? env name field
      unless plumbingRoots.any (·.isPrefixOf name) ||
          projection?.any (fun projection => plumbingRoots.any (·.isPrefixOf projection)) do
        return e
      let projected := Expr.proj name index (← plumbingValue value)
      let reduced ← whnfCore projected
      if reduced != projected then plumbingValue reduced else pure projected
  | .app .. | .const .. =>
      let f := e.getAppFn
      if let .const c _ := f then
        if plumbingRoots.any (·.isPrefixOf c) && (← plumbingApplication e) then
          if let some e' ← unfoldDefinition? e then return ← plumbingValue e'
          if let some e' ← unfoldProjInst? e then return ← plumbingValue e'
      let args ← e.getAppArgs.mapM fun a => do
        if (← isProp (← inferType a)) || (← isType a) then pure a else plumbingValue a
      let f ← if f.isProj then plumbingValue f else pure f
      let e' := mkAppN f args
      -- A projection may now meet its constructor.
      let r ← whnfCore e'
      if r != e' then plumbingValue r else pure e'
  | _ => pure e

/-- `plumbingValue v`, checked to be `v`: what an obligation is stated of must be the value. -/
def normalizedValue (v : Expr) : MetaM Expr := do
  let v' ← plumbingValue v
  unless ← withTransparency .default (isDefEq v' v) do
    throwError "the kernel's normal form of {v} is not the value itself"
  return v'

/-- The function a map of sets built by the kernel is (definitionally): composites are composed
functions, identities the identity, `ofHom f` is `f`, and a definition of the catalogue is unfolded
to its value. Anything else is left as the map's action `ConcreteCategory.hom h`. It is what an
obligation about a map (continuity, smoothness) is stated of, so that the obligation is about
`Real.sin` rather than about the categorical term it was assembled as. -/
partial def functionOf (h : Expr) : TermElabM Expr := do
  let h ← instantiateMVars h
  match h.getAppFn.constName?, h.getAppArgs with
  | some ``id, #[_, e] => functionOf e
  | some ``CategoryTheory.CategoryStruct.comp, #[_, _, _, _, _, f, g] =>
      let F ← functionOf f
      let G ← functionOf g
      let some (domain, _) := (← inferFunctionType F) | actionOf h
      withLocalDeclD `x domain fun x => do
        mkLambdaFVars #[x] (← whnfCore (mkApp G (← whnfCore (mkApp F x))))
  | some ``CategoryTheory.CategoryStruct.id, #[_, _, X] =>
      withLocalDeclD `x (← whnf X) fun x => mkLambdaFVars #[x] x
  | some ``TypeCat.ofHom, #[_, _, f] => pure f
  | some name, _ =>
      if name.getRoot == `CasCatalogue then
        if let some unfolded ← unfoldDefinition? h then return ← functionOf unfolded
      actionOf h
  | none, _ => actionOf h
where
  actionOf (h : Expr) : TermElabM Expr := do
    let e ← elabTermAndSynthesize
      (← `(fun x => CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax h) x)) none
    instantiateMVars e
  inferFunctionType (F : Expr) : TermElabM (Option (Expr × Expr)) := do
    let type ← whnf (← inferType F)
    let .forallE _ domain codomain _ := type | return none
    return some (domain, codomain)

/-- The one place the kernel runs a proof procedure it did not write (`CasGates.KernelPurity`,
`evidenceRunner`): `procedure`, a `meta` procedure `TacticM Unit` of `lean-categories` registered
there and validated there, a domain's evidence registered with its admission (LC-18) or a literal
form's evaluation registered with the form, run on the goal `goal`. The result is the goals it
leaves, or, when it fails or logs an error, why. The kernel names no lemma and no tactic, and runs
no proof search of its own (`specs/architecture.md`, "What must be impossible"). A failed
procedure is not recovered into `sorry`, and its attempt leaves no message behind: its failure is
reported once, by the caller. -/
def runProcedure (procedure : Name) (goal : MVarId) :
    TermElabM (Except String (List MVarId)) := do
  let procedure ← unsafe evalConst (Lean.Elab.Tactic.TacticM Unit) procedure
  let messages := (← getThe Core.State).messages
  let restore : TermElabM Unit := modifyThe Core.State fun st => { st with messages }
  let outcome ← withoutErrToSorry <| Term.withoutErrToSorry do
    try
      let remaining ← Term.withSynthesize (postpone := .no) <|
        Lean.Elab.Tactic.run goal procedure
      pure (Except.ok remaining : Except String (List MVarId))
    -- A failed procedure is returned as its failure, which the caller reports.
    -- not a reading fallback: the failure is returned, never retried
    catch e => pure (Except.error (← e.toMessageData.toString))
  let logged := (← getThe Core.State).messages.hasErrors && !messages.hasErrors
  match outcome with
  | .error message =>
      restore
      return .error message
  | .ok remaining =>
      if logged then
        let errors := (← getThe Core.State).messages.toList.filter (·.severity == .error)
        let detail ← match errors.getLast? with
          | some msg => msg.data.toString
          | none => pure ""
        restore
        return .error s!"its proof has a hole: {detail}"
      return .ok remaining

/-- The evidence of the hypothesis `p` of the admission of a domain (a proposition, `IsUnit x`,
`Continuous f`, or data with at most one value, `Invertible x`, the inverse an admitted unit
keeps), established when a statement is read (LC-14) by the domain's registered evidence and by
nothing else: a `meta` proof procedure `TacticM Unit` of `lean-categories`, registered with the
domain's admission (LC-18), run through `runProcedure` on the goal `p`. The result is the closed
term the procedure built, a proof or the data, which the admission takes directly. A statement
whose obligation is not established is invalid: without the evidence, the value is not in the
domain it is used in. -/
def establish (evidence : Name) (p : Expr) (what : MessageData) : TermElabM Expr := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then
    throwStratum .invalid m!"{what}: the hypothesis {p} is not determined"
  let presented ← evidencePresentation (← registryState) p
  let goal ← mkFreshExprMVar presented .syntheticOpaque
  match ← runProcedure evidence goal.mvarId! with
  | .error message =>
      let detail := if message.length ≤ 300 then message else
        s!"{message.take 300}\n{String.intercalate "\n" ((message.splitOn "\n").reverse.take 8).reverse}"
      throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
        ({detail})"
  | .ok remaining =>
      let term ← instantiateMVars goal
      -- Evidence with a hole is no evidence.
      if !remaining.isEmpty || term.hasSorry || term.hasSyntheticSorry then
        throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
          (its term has a hole)"
      if term.hasMVar || term.hasLevelMVar then
        throwStratum .invalid m!"{what}: {p} is not established (its term is not closed: {term})"
      let original ← mkExpectedTypeHint term p
      unless ← isTypeCorrect original do
        throwStratum .invalid m!"{what}: the evidence does not inhabit the original target {p}"
      return original

/-- The morphism `a → b` of the registered graph literal of their category with the graph `pairs`
of numerals, each an element of the set `a` or `b` is (its registered numeral, `numeralIn`). -/
def graphOf (a b : Value) (pairs : Array (Nat × Nat)) : M Value := do
  let state ← registryState
  let sourceValue := a
  let targetValue := b
  let .object a category (some (source, sourceParams)) _ _ := a
    | throwStratum .invalid m!"the domain of a graph is a named object"
  let .object b category' (some (target, targetParams)) _ _ := b
    | throwStratum .invalid m!"the codomain of a graph is a named object"
  unless category.id == category'.id do
    throwStratum .invalid m!"a graph from {category.name} to {category'.name}"
  let some form := state.graphLiterals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered graph literals"
  let one ← globalPointSource
  -- The element `k` of the named object: its numeral in the set it is, at the point of `1`.
  let element (object : ObjectEntry) (params : Array Value) (k : Nat) : M Term := do
    let set ← setOf state object
    let params ← paramTerms params
    let x ← Semantic.object set params
    let refinements ← (state.objects.filter (·.refines.any (·.base == set.id))).mapM fun o =>
      return (o.category, ← Semantic.object o params)
    let some numeral ← numeralIn state k one x refinements
      | throwStratum .invalid m!"no registered numeral lands in {object.name}"
    `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr numeral)
      $(← quoteExpr (← globalPoint)))
  let entries ← pairs.mapM fun (x, y) => do
    `(($(← element source sourceParams x), $(← element target targetParams y)))
  let X ← `($(mkCIdent source.declaration) $(← paramTerms sourceParams)*)
  let Y ← `($(mkCIdent target.declaration) $(← paramTerms targetParams)*)
  -- The literal's side conditions (a graph of a function on the listed points) are decided.
  let literal ← instantiateMVars (← elabTermAndSynthesize
    (← `($(mkCIdent form.denotation) (X := $X) (Y := $Y) [$entries,*])) none)
  let (conditions, _, _) ← forallMetaTelescope (← inferType literal)
  for h in conditions do
    let condition ← instantiateMVars (← inferType h)
    let some proof ← decideObligation condition
      | throwStratum .invalid m!"the graph does not define a map: {condition} does not hold"
    discard <| isDefEq h proof
  let semantic ← quoteExpr (← instantiateMVars (mkAppN literal conditions))
  let hom ← homIn semantic a b category
  -- The morphism is the literal of its graph: the realized reading sends the graph.
  Trace.record (← read).trace hom (.literal form.id (← instantiateMVars literal.appArg!))
  return .morphism hom a b category (some (sourceValue, targetValue))

-- Compilation of this mutually recursive reader needs additional reduction work as its
-- provenance payload grows. This local option does not alter caller/probe interpretation budgets.
set_option maxHeartbeats 800000 in
mutual

/-- Reuse closed readings only within this question's unchanged context. -/
partial def eval (scope : Scope) (stx : Syntax) (category? : Option NamedCategoryEntry := none)
    (ambient? : Option Value := none) : M Value := do
  let ctx ← read
  -- Accepted comparisons and selected constructions are semantic inputs even when
  -- the caller does not request an execution trace. Keep their local records in
  -- an isolated reading; a speculative caller's trace and cache remain untouched.
  if ctx.trace.isNone then
    let trace ← Trace.new
    return ← withReader (fun context =>
      { context with trace := some trace, closedTerms := none })
      (eval scope stx category? ambient?)
  let cache? := if category?.isNone && ambient?.isNone && ctx.stage.isNone &&
      ctx.bound.isEmpty then ctx.closedTerms else none
  if let some cache := cache? then
    if let some value := (← cache.get)[shown stx]? then return value
  let value ← if profiler.get (← getOptions) then
    profileitM Exception s!"cas reader {stx.getKind}" (← getOptions)
      (evalUncached scope stx category? ambient?)
  else evalUncached scope stx category? ambient?
  if let some cache := cache? then
    match value with
    | .object .. | .element .. =>
        if value.terms.all (fun term => !term.hasMVar && !term.hasLevelMVar) then
          cache.modify (·.insert (shown stx) value)
    | _ => pure ()
  return value

/-- The uncached value of a term, in the category `category?` of an enclosing `in C`. -/
partial def evalUncached (scope : Scope) (stx : Syntax)
    (category? : Option NamedCategoryEntry := none)
    (ambient? : Option Value := none) : M Value := do
  let state ← registryState
  if stx.getKind == ``casFormalProof then return .formalProof stx[1]
  if stx.getKind == ``casInProof then
    return ← evalInUsing scope stx[0] stx[2] stx[5].getSepArgs category?
  match stx with
  | `(cas_term| presentation($selectedName:ident($parameters,*))) =>
      selectedPresentation scope (selectedName.getId.toString false) parameters.getElems false
  | `(cas_term| inverse_presentation($selectedName:ident($parameters,*))) =>
      selectedPresentation scope (selectedName.getId.toString false) parameters.getElems true
  | `(cas_term| binder($selectedName:ident($parameters,*), $family)) =>
      selectedBinder scope (selectedName.getId.toString false) parameters.getElems family
  | `(cas_term| lift($source) along $selectedName:ident($parameters,*) with $inclusion using $proof) =>
      selectedLift scope (selectedName.getId.toString false) parameters.getElems source inclusion proof
  | `(cas_term| factor($baseMap) through $selected with $cone using $proof) =>
      selectedLiftFactor scope selected baseMap cone proof
  | `(cas_term| composite_lift($selected)) => selectedLiftComposite scope selected
  | `(cas_term| map $morphism along $construction:ident($parameters,*)) =>
      directConstructionMap scope (construction.getId.toString false) parameters.getElems morphism
  | `(cas_term| component($cell:ident($parameters,*), $receiver, [$constructors:ident,*])) =>
      selectedCell scope (cell.getId.toString false) parameters.getElems receiver
        (constructors.getElems.map fun constructor => ⟨constructor.getId.toString false⟩) false
  | `(cas_term| inverse_component($cell:ident($parameters,*), $receiver, [$constructors:ident,*])) =>
      selectedCell scope (cell.getId.toString false) parameters.getElems receiver
        (constructors.getElems.map fun constructor => ⟨constructor.getId.toString false⟩) true
  | `(cas_term| view $receiver along $functor:ident) =>
      registeredEdgeView scope receiver (functor.getId.toString false) #[]
  | `(cas_term| view $receiver along $functor:ident($arguments,*)) =>
      registeredEdgeView scope receiver (functor.getId.toString false) arguments.getElems
  | `(cas_term| $n:num) => return .nat n.getNat
  | `(cas_term| $d:scientific) =>
      let (mantissa, _, exponent) := d.getScientific
      divide (.nat mantissa) (.nat (Nat.pow 10 exponent)) (← numeralSet stx ambient?)
  | `(cas_term| ($t)) => eval scope t category? ambient?
  | `(cas_term| $t in $c) => evalIn scope t c category? ambient?
  | `(cas_term| $x ⊆ $y) =>
      -- Named sets: the registered inclusions decide it; nothing is realized. Otherwise subsets:
      -- the order of the Boolean algebra `𝒫(X)`.
      unless (← namesObject scope x) && (← namesObject scope y) do
        return ← operate scope "⊆" #[x, y] ambient?
      let (sub, subParams) ← namedObject scope x
      let (super, superParams) ← namedObject scope y
      unless subParams == superParams do
        throwStratum .invalid m!"`⊆` relates named sets at the same parameters"
      if let some route := inclusionChain state sub.id super.id then
        return ← decided (judgement "⊆" #[← eval scope x, ← eval scope y] (route.map (·.declaration)))
      throwStratum .invalid m!"no registered inclusion of {sub.name} in {super.name}"
  | `(cas_term| $x ∈ $y) =>
      let Y ← eval scope y
      if let some (po, X) ← powerSetOf? Y then return ← member po X (← eval scope x none (some X)) Y
      let .object y _ (some (super, _)) _ _ := Y
        | throwStratum .invalid m!"`∈` is membership in a named set"
      -- `x` where it is formed (`-3 ∈ ℕ` asks whether `-3 ∈ ℤ` lies in the image of `ℕ`); a numeral
      -- names an element of `Y` itself.
      let x' ← match ← eval scope x with
        | v@(.nat _) => toElement v Y
        | v => pure v
      match x' with
      | .element _ (.object a _ (some (sub, _)) _ _) =>
          -- The same family: the same set, at the same parameters.
          if sub.id == super.id then
            if ← withTransparency .all <| isDefEq a y then
              return ← decided (judgement "∈" #[x', Y])
            throwStratum .invalid m!"`{shown x}` is an element of another {sub.name}"
          if let some route := inclusionChain state sub.id super.id then
            return ← decided (judgement "∈" #[x', Y] (route.map (·.declaration)))
          -- `Y` included in the set `Z` of `x` (`ℕ ⊆ ℤ`, `Mˣ ↪ M`): membership in its image.
          if let .element _ Z := x' then
            let v := x'
            if let some (some ι) ← coercionMap Y Z then
              let po ← powerObjectIn state CategoryId.sets
              return ← member po Z v (← imageOfMap ι Y Z)
          throwStratum .invalid m!"no registered inclusion of {sub.name} in {super.name}"
      | _ => throwStratum .invalid m!"`∈` relates an element and a named set"
  | `(cas_term| $p and $q) =>
      let left ← eval scope p
      let right ← eval scope q
      let lp ← asAnswer left
      let rp ← asAnswer right
      return .judged (.conjunction (left.question lp) (right.question rp)) (mkAnd lp rp)
  | `(cas_term| $x ∉ $y) =>
      let value ← eval scope (← `(cas_term| $x ∈ $y)) category? ambient?
      let prop ← asAnswer value
      return .judged (.negation (value.question prop)) (mkNot prop)
  | `(cas_term| $x ∪ $y) => operate scope "∪" #[x, y] ambient?
  | `(cas_term| $x ∩ $y) => operate scope "∩" #[x, y] ambient?
  | `(cas_term| $x \ $y) => operate scope "\\" #[x, y] ambient?
  | `(cas_term| $x △ $y) => operate scope "△" #[x, y] ambient?
  | `(cas_term| $x ≤ $y) => operate scope "≤" #[x, y] ambient?
  | `(cas_term| $x = $y) =>
      let (elements, _) ← operands scope #[x, y] ambient?
      applyNamed state "=" elements
  | `(cas_term| $x < $y) => operate scope "<" #[x, y] ambient?
  | `(cas_term| $x²) => power scope (← eval scope x none ambient?) 2 ambient?
  | `(cas_term| $x³) => power scope (← eval scope x none ambient?) 3 ambient?
  | `(cas_term| 𝒫($x)) => powerSetOf (← asObject (← eval scope x))
  | `(cas_term| $a → $b) =>
      return .homSet (← asObject (← eval scope a)) (← asObject (← eval scope b))
  | `(cas_term| $t:ident ↦ $e) =>
      match ambient? with
      | some (.homSet X Y) => lambda scope t.getId e X Y
      | some P@(.object ..) =>
          -- `t ↦ e` in `R[x]`: the element `e` with `t` the generator.
          let g ← generatorOf P
          withReader (fun ctx => { ctx with bound := (t.getId, g) :: ctx.bound }) do
            toElement (← eval scope e none (some P)) P
      | _ => throwStratum .invalid m!"`{t.getId} ↦ …` needs its set of maps (`in X → Y`) or its \
          polynomials (`in R[x]`)"
  | `(cas_term| √$x) => applyNamed state "sqrt" #[← eval scope x]
  | `(cas_term| {$xs,*}) => setLiteral scope xs.getElems ambient?
  | `(cas_term| {$t:ident ∈ $X | $p}) =>
      -- A supplied power-object target also fixes the subset domain's presentation.
      -- Keep that expected result through its declared application before binding t.
      let A ← eval scope X none ambient?
      -- `{t ∈ A | P}` for a subset `A ⊆ X` is `A ∩ {t ∈ X | P}`.
      if let some (_, base) ← powerSetOf? A then
        let P ← powerSetOf base
        return ← applyOperation "∩" #[A, ← comprehension scope t.getId base p] P
      comprehension scope t.getId (← asObject A) p
  | `(cas_term| {$e | $t:ident ∈ $X}) => imageOf scope e t.getId (← eval scope X)
  | `(cas_term| ($f)($args,*)) => apply scope (← eval scope f category?) args.getElems
  | `(cas_term| $x + $y) =>
      -- `p + Y` for a named set `Y` of constants: the coset `{p + c | c ∈ Y}`.
      if ← namesObject scope y then
        return ← cosetOf (← eval scope x none ambient?) (← eval scope y)
      operate scope "+" #[x, y] ambient?
  | `(cas_term| $x · $y) => operate scope "·" #[x, y] ambient?
  | `(cas_term| -$x) => operate scope "-" #[x] ambient?
  | `(cas_term| $x - $y) =>
      -- For named sets `Y ⊆ X`: the complement of `Y` in `X`.
      if ← namesObject scope x then
        return ← complementOf (← eval scope x) (← eval scope y)
      -- `x - y` is `x + -y`.
      let (elements, X) ← operands scope #[x, y] ambient?
      applyOperation "+" #[elements[0]!, ← applyOperation "-" #[elements[1]!] X] X
  | `(cas_term| ℵ₀) => return .literal `«ℵ₀»
  | `(cas_term| $x:ident) =>
      if let some v := (← read).bound.lookup x.getId then return ← restage v
      if let some t := scope.get? x.getId then
        let rings ← ringBindings scope t
        return ← withReader (fun ctx => { ctx with bound := rings ++ ctx.bound }) do
          restage (← eval scope t category? ambient?)
      let name := x.getId.toString
      -- `dv` for a variable `v`: its differential `d(v)`.
      if let some v ← differentialVariable? x.getId then return ← applyNamed state "d" #[v]
      if state.objects.any (·.name == name) then object state name #[] category?
      else if state.morphisms.any (·.name == name) then named scope name #[] category?
      else return .literal x.getId
  | `(cas_term| $f:ident($args,*)) =>
      -- `x.m()` lexes as the identifier `x.m` applied to no arguments.
      match f.getId, args.getElems.isEmpty with
      | .str receiver method, true =>
          if receiver.isAnonymous then
            applyIdentifier scope f args.getElems category?
          else if state.objects.any (·.name == f.getId.toString) then
            object state f.getId.toString #[] category?
          else call scope (← `(cas_term| $(mkIdent receiver):ident)) method category?
      -- `x.m(a, …)` lexes as the identifier `x.m` applied to `a, …`.
      | .str receiver method, false =>
          if !receiver.isAnonymous && (scope.contains receiver ||
              ((← read).bound.lookup receiver).isSome) then
            return ← callWith scope (← `(cas_term| $(mkIdent receiver):ident)) method args.getElems
          applyIdentifier scope f args.getElems category?
      | _, _ => applyIdentifier scope f args.getElems category?
  | `(cas_term| {$pairs,*} : $st) =>
      let `(cas_term| $s → $t) := st | throwStratum .invalid m!"a graph is a map `X → Y`"
      graph scope pairs.getElems s t category?
  | `(cas_term| $f ∘ $g) =>
      let second ← eval scope f category?
      let (f', b, c, context, _, targetValue) ← morphismContext second
      let category? := CategoryContext.named? state context.expression
      let first ← eval scope g category?
      let (g', a, b', sourceContext, sourceValue, _) ← morphismContext first
      unless context.expression.syntacticEq sourceContext.expression &&
          (← withTransparency .all <| isDefEq context.bundle sourceContext.bundle) &&
          (← isDefEq b b') do
        throwStratum .invalid m!"`{shown f} ∘ {shown g}`: the target of {shown g} is not the \
          source of {shown f}"
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[g', f']
      let node := match category? with
        | some category => Node.morphismComposition category.id g' f' a b c
        | none => Node.contextualComposition context g' f' a b c
      Trace.record (← read).trace composite node
      return ← morphismInContext composite a c context (sourceValue, targetValue)
  | `(cas_term| |$t|) =>
      -- `|x|` of an element is its absolute value; of an object, its cardinality.
      match ← eval scope t category? ambient? with
      | v@(.element ..) =>
          if (← powerSetOf? v).isSome then return ← cardinality (← asObject v)
          applyNamed state "abs" #[v]
      | value@(.object ..) => cardinality value
      | _ => call scope t "cardinality" category?
  | `(cas_term| $t.$m:ident()) => call scope t m.getId.toString category?
  | `(cas_term| $a / $n) =>
      match a, n with
      | `(cas_term| ℤ), _ =>
          -- The notation binds its declared ring row, rather than the unrefined set of
          -- the same surface name. Expose its carrier while retaining that full structure.
          let declared ← objectNotation state "ℤ/"
          let some quotientCategory := state.categories.find? (·.id == declared.category)
            | throwStratum .invalid m!"quotient arithmetic has no registered category"
          let quotient ← object state declared.name #[← eval scope n] (some quotientCategory)
          match category? with
          | none => carrierObject quotient
          | some category =>
              let family ← instantiateFresh category.declaration
              let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
              let image ← typedParameter expected quotient
              structuredParameterView quotient image category
      | `(cas_term| d), `(cas_term| $v:ident) =>
          if let some x ← differentialVariable? v.getId then return ← derivativeAt x
          throwStratum .invalid m!"`d/{v.getId}`: {v.getId} is not d of a variable"
      | _, _ =>
          let K? ← numeralSet stx ambient?
          divide (← eval scope a none K?) (← eval scope n) K?
  | `(cas_term| $b ^ $k) => evalPower scope b k category? ambient?
  | `(cas_term| $a × $b) => product scope false a b category?
  | `(cas_term| $a ⊔ $b) => product scope true a b category?
  | _ => evalKinds scope stx category? ambient?

/-- The terms of the language named by their syntax kind. -/
partial def evalKinds (scope : Scope) (stx : Syntax) (category? : Option NamedCategoryEntry)
    (ambient? : Option Value) : M Value := do
  let state ← registryState
  if stx.getKind == ``casApplication then
    if stx[0].isIdent then
      return ← applyIdentifier scope ⟨stx[0]⟩ stx[2].getSepArgs category?
    return ← apply scope (← eval scope stx[0] category?) stx[2].getSepArgs
  if stx.getKind == ``casPatternLambda then
    let some (.homSet X Y) := ambient?
      | throwStratum .invalid m!"a destructured map needs its declared domain and codomain"
    return ← patternMap scope (lambdaPattern stx) stx[6] X Y
  if stx.getKind == ``casRing then
    return ← object state "Poly" #[← asObject (← eval scope stx[0])] none
  if stx.getKind == ``casMap then
    let value ← eval scope stx[1]
    let target ← eval scope stx[3]
    let endpointOrigin : Value → Option ObjectId := fun value =>
      let object := match value with | .element _ X => X | _ => value
      match object with
      | .object _ _ _ (some (.object _ _ (some (entry, _)) _ _)) _ => some entry.id
      | .object _ _ (some (entry, _)) _ _ => some entry.id
      | _ => none
    let matchesEndpoint := fun value row =>
      (endpointOrigin value).any (refinesObject state row ·)
    let mut presentations := #[]
    for presentation in state.presentations do
      let some source := state.objects.find? (·.id == presentation.source) | continue
      let some destination := state.objects.find? (·.id == presentation.target) | continue
      if matchesEndpoint value source && matchesEndpoint target destination then
        presentations := presentations.push (presentation, false)
      if matchesEndpoint value destination && matchesEndpoint target source then
        presentations := presentations.push (presentation, true)
    match presentations.toList with
    | [] => return ← applyNamed state "map" #[value] (some target)
    | [(presentation, inverse)] =>
        let result ← presentationMapValue value presentation inverse
        return ← coerceTo result (← carrierObject target)
    | _ => throwSemanticAmbiguity m!"several registered presentations map these selected endpoints"
  if stx.getKind == ``casPresentationForward || stx.getKind == ``casPresentationBack then
    return ← presentationMap scope stx[1]
      stx[if stx.getKind == ``casPresentationBack then 4 else 3].getId.toString
      (stx.getKind == ``casPresentationBack)
  if stx.getKind == ``casCoefficient then
    let b ← eval scope (← `(cas_term| $(⟨stx[3]⟩):ident)) none ambient?
    let b ← match stx[4].find? (·.isAtom) |>.map (·.getAtomVal) with
      | some "²" => power scope b 2 ambient?
      | some "³" => power scope b 3 ambient?
      | _ => pure b
    return ← juxtapose (← eval scope stx[1]) b ambient?
  if stx.getKind == ``casTimes then
    return ← juxtapose (← eval scope stx[0]) (← eval scope stx[2] none ambient?) ambient?
  if stx.getKind == ``casAction then
    return ← registeredAction (← eval scope stx[0])
      (← eval scope stx[2] none ambient?) ambient?
  if stx.getKind == ``casTuple then
    return ← tuple scope (#[stx[1]] ++ stx[3].getSepArgs) ambient?
  if stx.getKind == ``casMatrix then
    return ← matrix scope (stx[1].getSepArgs.map (·.getSepArgs)) ambient?
  evalAnalysis scope stx category? ambient?

/-- The terms of the language named by their syntax kind: analysis and the remaining forms. -/
partial def evalAnalysis (scope : Scope) (stx : Syntax) (category? : Option NamedCategoryEntry)
    (ambient? : Option Value) : M Value := do
  let state ← registryState
  if stx.getKind == ``casBig then
    let name := (stx[0].find? (·.isAtom)).map (·.getAtomVal) |>.getD "∑"
    return ← binder scope name stx[2].getId #[stx[4]] stx[6] ambient?
  if let some v ← evalNotation scope stx then return v
  if stx.getKind == ``casMvRing then
    let names ← match mvVariables stx with
      | .ok names => pure names
      | .error message => throwStratum .invalid m!"{message}"
    return ← object state "MvPoly" #[.nat names.size, ← asObject (← eval scope stx[0])] none
  if stx.getKind == ``casSpec then
    let .object _ _ (some (entry, params)) _ _ ← eval scope stx[1]
      | throwStratum .invalid m!"`Spec` is of a named ring"
    return ← object state s!"Spec {entry.name}" params none
  if stx.getKind == ``casIs then
    let (elements, _) ← operands scope #[stx[0], stx[2]] ambient?
    return ← applyNamed state "=" elements
  if stx.getKind == ``casSeries then
    return ← object state "PowerSeries" #[← asObject (← eval scope stx[0])] none
  if stx.getKind == ``casCallWith then
    return ← callWith scope stx[0] stx[2].getId.toString stx[4].getSepArgs
  if stx.getKind == ``casLimit then
    return ← binder scope "lim" stx[1].getId #[stx[3]] stx[5] ambient?
  if stx.getKind == ``casDefinite then
    let some boundName := differentialOf? stx[6].getId
      | throwStratum .invalid m!"a binding differential must name its variable"
    return ← binder scope "∫" boundName #[stx[1], stx[3]] stx[5] ambient?
  if stx.getKind == ``casIntegral then
    return ← applyNamed state "∫" #[← eval scope stx[1]] ambient?
  if stx.getKind == ``casActed then
    let b ← eval scope (← `(cas_term| $(⟨stx[1]⟩):ident)) none ambient?
    return ← juxtapose (← eval scope stx[0]) b ambient?
  -- `2n`, `3x²`, `2√2`: a numeral times a term.
  if stx.getKind == ``casScaled || stx.getKind == ``casScaledRoot then
    let factor ← if stx.getKind == ``casScaledRoot then `(cas_term| √$(⟨stx[2]⟩)) else
      let v : Ident := ⟨stx[1]⟩
      match stx[2].find? (·.isAtom) |>.map (·.getAtomVal) with
        | some "²" => `(cas_term| $v:ident²)
        | some "³" => `(cas_term| $v:ident³)
        | _ => `(cas_term| $v:ident)
    return ← operate scope "·" #[← `(cas_term| $(⟨stx[0]⟩):num), factor] ambient?
  -- The atoms `ℤ`, `ℕ`, `ℚ`, `ℝ`, `ℂ`: objects named by their notation.
  match stx.getKind == ``casAtom, stx.find? (·.isAtom) with
  | true, some atom => object state atom.getAtomVal #[] category?
  | _, _ =>
      -- Surface atoms may name a registered constant without being identifier syntax.
      let spelling := shown stx
      if state.morphisms.any (·.name == spelling) then
        named scope spelling #[] category?
      else throwStratum .invalid m!"not a term of the language: {stx}"

/-- `f(a, …)` for an identifier `f`: a bound map or element applied, else the registered row
named `f`. -/
partial def applyIdentifier (scope : Scope) (f : Ident) (args : Array Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  if ((← read).bound.lookup f.getId).isSome || scope.contains f.getId then
    return ← apply scope (← eval scope (← `(cas_term| $f:ident)) category?) args
  if let .str receiver method := f.getId then
    if !receiver.isAnonymous && (scope.contains receiver ||
        ((← read).bound.lookup receiver).isSome) then
      let receiver ← `(cas_term| $(mkIdent receiver):ident)
      if args.isEmpty then return ← call scope receiver method category?
      return ← callWith scope receiver method args
  named scope f.getId.toString args category?

/-- The set a term's numerals are read in: the enclosing one; for a term of numerals alone, else
`ℚ` (a fraction or decimal: the initial field of characteristic `0`) or `ℤ` (the initial ring). -/
partial def numeralSet (stx : Syntax) (ambient? : Option Value) : M (Option Value) := do
  if ambient?.isSome || !numeric stx then return ambient?
  some <$> notationObject
    (if fractional stx then "literal.fractional.domain" else "literal.integral.domain")

/-- A distinguished generator binds a local variable only inside its explicit selected object. -/
partial def localGeneratorBindings (scope : Scope) (term objectSyntax : Syntax) (X : Value) :
    M (List (Name × Value)) := do
  let .object targetHandle _ (some (entry, parameters)) _ _ := X | return []
  if entry.generator.isNone then return []
  let state ← registryState
  let context ← read
  -- Explicit generator names retain their declaration-owned indices. They are not competing
  -- aliases for one generator, and never replace an externally supplied binding.
  let mut written : List (Name × Value) := []
  for (name, ring, index) in ringsIn scope #[] objectSyntax do
    if scope.contains name || (context.bound.lookup name).isSome then continue
    let object ← carrierObject (← eval scope ring)
    let .object handle _ (some (source, sourceParameters)) _ _ := object | continue
    if source.id != entry.id then continue
    unless ← parameterTrial <| withTransparency .all <| isDefEq handle targetHandle do continue
    let left ← typedParamTerms source.declaration sourceParameters
    let right ← typedParamTerms entry.declaration parameters
    unless left.size == right.size do continue
    let identical ← parameterTrial do
      for (l, r) in left.zip right do
        let l ← elabTermAndSynthesize l none
        let r ← elabTermAndSynthesize r none
        unless ← withTransparency .all <| isDefEq (← inferType l) (← inferType r) do
          return false
        unless ← withTransparency .all <| isDefEq l r do return false
      return true
    unless identical do continue
    written := written ++ [(name, ← generatorOf X index)]
  if !written.isEmpty then return written
  let names := (looseIdentifiers term).filter fun name =>
    name.isAtomic && !scope.contains name && (context.bound.lookup name).isNone &&
      !state.objects.any (·.name == name.toString) &&
      !state.morphisms.any (·.name == name.toString) &&
      !state.categories.any (·.name == name.toString) &&
      !state.presentations.any (·.name == name.toString) &&
      !state.methods.any (·.name == name.toString) &&
      !state.properties.any (·.name == name.toString) &&
      !#[`id, `generator, `reindex, `cartesian, `true, `false, `unknown].contains name
  let names := names.foldl (fun found name =>
    if found.contains name then found else found.push name) #[]
  match names.toList with
  | [] => return []
  | [name] => return [(name, ← generatorOf X)]
  | _ => throwSemanticAmbiguity m!"a distinguished generator has several local variable names"

/-- Explicit generator scopes remove only their locally bound occurrences from free variables. -/
partial def contextualIdentifiers (scope : Scope) (term : Syntax) : M (Array Name) := do
  if term.getKind == ``casFormalProof then return #[]
  if term.getKind == ``casInProof then
    let ordinary ← `(cas_term| $(⟨term[0]⟩) in $(⟨term[2]⟩))
    return ← contextualIdentifiers scope ordinary
  if term.getKind == ``casRing || term.getKind == ``casSeries || term.getKind == ``casMvRing then
    return looseIdentifiers term
  if term.getKind == ``casBig then
    return (← contextualIdentifiers scope term[4]) ++
      (← contextualIdentifiers scope term[6]).filter (· != term[2].getId)
  if term.getKind == ``casLimit then
    return (← contextualIdentifiers scope term[3]) ++
      (← contextualIdentifiers scope term[5]).filter (· != term[1].getId)
  if term.getKind == ``casDefinite then
    return (← contextualIdentifiers scope term[1]) ++
      (← contextualIdentifiers scope term[3]) ++
      (← contextualIdentifiers scope term[5]).filter (fun name =>
        name != term[6].getId && differentialOf? term[6].getId != some name)
  if let `(cas_term| $bound:ident ↦ $body) := term then
    return (← contextualIdentifiers scope body).filter (· != bound.getId)
  if term.getKind == ``casPatternLambda then
    return (← contextualIdentifiers scope term[6]).filter
      (!(patternNames (lambdaPattern term)).contains ·)
  if let `(cas_term| {$bound:ident ∈ $domain | $body}) := term then
    return (← contextualIdentifiers scope domain) ++
      (← contextualIdentifiers scope body).filter (· != bound.getId)
  if let `(cas_term| {$body | $bound:ident ∈ $domain}) := term then
    return (← contextualIdentifiers scope domain) ++
      (← contextualIdentifiers scope body).filter (· != bound.getId)
  if let `(cas_term| $body in $objectSyntax) := term then
    let state ← registryState
    if let `(cas_term| $category:ident) := objectSyntax then
      if state.categories.any (·.name == category.getId.toString) then
        return ← contextualIdentifiers scope body
    if (categoryOver? state objectSyntax).isSome then
      return (← contextualIdentifiers scope body) ++ (← contextualIdentifiers scope objectSyntax)
    let ambient ← eval scope objectSyntax
    let X ← match ambient with | .object .. => carrierObject ambient | _ => pure ambient
    let locals ← localGeneratorBindings scope body objectSyntax X
    let bodyNames ← contextualIdentifiers scope body
    let objectNames ← contextualIdentifiers scope objectSyntax
    return bodyNames.filter (fun name => (locals.lookup name).isNone) ++ objectNames
  if term.isIdent then return #[term.getId]
  let mut names := #[]
  for child in term.getArgs do
    names := names ++ (← contextualIdentifiers scope child)
  return names

partial def evalIn (scope : Scope) (t c : Syntax) (category? : Option NamedCategoryEntry)
    (ambient? : Option Value) : M Value := do
  let state ← registryState
  if let `(cas_term| $name:ident) := c then
    if state.categories.any (·.name == name.getId.toString) then
      let target ← categoryNamed state name.getId.toString
      -- Existing explicitly registered named refinements keep their own identity.
      if ← namesObject scope t then
        let entry ← namedObjectEntry scope t
        if state.objects.any (fun row => row.name == entry.name && row.category == target.id) then
          return ← eval scope t (some target) ambient?
      if let .classifierTotal classifier := target.expression then
        let some owner := state.classifier? classifier
          | throwStratum .invalid "the selected classifier total has no registered classifier"
        let some host := state.category? owner.host
          | throwStratum .invalid "the classifier's complete host category is not registered"
        let original ← asObject (← eval scope t (some host) ambient?)
        let .object source sourceCategory .. := original
          | throwStratum .invalid "only a supplied object is retyped by a property proof"
        if sourceCategory.id == target.id then return original
        unless sourceCategory.id == host.id do
          throwStratum .invalid "the supplied object is outside the classifier's complete host"
        let result ← ProofRefinement.construct state classifier target source
        Trace.record (← read).trace result.value
          (.proofRefinement classifier sourceCategory.id target.id source result.action result.identity)
        return .object result.value target none none none
      let value ← eval scope t (some target) ambient?
      match value with
      | .object .. => return ← objectInCategory value target
      | _ => return value
  if let some (C, Y) := categoryOver? state c then return ← inCategoryOver scope t C Y
  -- `t in X` for a set `X`: `t` with its numerals in `X`.
  let ambient ← eval scope c
  let X ← match ambient with
    | .object .. => carrierObject ambient
    | _ => pure ambient
  let locals ← localGeneratorBindings scope t c X
  withReader (fun context => { context with bound := locals ++ context.bound }) do
  if let .object _ _ none none data := X then
    -- An explicit structural view still supplies its original point interpretation,
    -- even after reaching Sets. Unfolding its carrier into a record must not replace
    -- the retained source's registered numerals with that record's data field.
    if !(data.any fun (_, _, route, _, _) => !route.isEmpty) then
      if let some dataCarrier ← constrainedCarrier? X then
        let value ← eval scope t category? (some dataCarrier)
        if let .element _ source := value then
          if (← coercionMap source X).isSome then return ← coerceTo value X
        return ← admitConstrainedPoint X (← toElement value dataCarrier)
  match X with
  | .homSet .. => eval scope t category? (some X)
  | .object _ _ (some (entry, _)) _ _ =>
      if entry.admission.isSome then
        -- `t in D` for a domain `D ↪ B` with an admission (`M in GL₂(ℚ)`, `f in C^∞`): `t` read in
        -- `B` (or as a map), then formed in `D` with its evidence established now.
        let .object _ category _ _ _ := X | unreachable!
        let B? ← match ← inclusionOut? X with
          | some (_, b) => some <$> inclusionTargetValue X b category
          | none => pure none
        let v ← eval scope t category? B?
        -- Already an element of `D` (or of a set included in it): carried there.
        if let .element _ Y := v then
          if (← coercionMap Y X).isSome then return ← coerceTo v X
        let v ← match B?, v with
          | some B, .nat _ => toElement v B
          | _, _ => pure v
        return ← admit X v
      -- `t` is an element of `X`, or of a set included in `X`.
      match ← toElement (← eval scope t category? (some X)) X with
      | v@(.element _ Y) =>
          if (← coercionMap Y X).isNone then
            throwStratum .invalid m!"`{shown t}` is not an element of `{shown c}`"
          coerceTo v X
      | v => pure v
  | .object _ _ none _ _ =>
      let value ← toElement (← eval scope t category? (some X)) X
      let .element _ Y := value
        | throwStratum .invalid m!"a selected carrier receives an element"
      if (← coercionMap Y X).isNone then
        throwStratum .invalid m!"the element has no registered map into the selected carrier"
      coerceTo value X
  | _ => throwStratum .invalid m!"`in` takes a category, a set or a set of maps"

/-- `b ^ k`: `(ℤ/n)^k`, `2^X` of a set, `x^k` of an element with a numeral or `ℕ` exponent. -/
partial def evalPower (scope : Scope) (b k : Syntax) (category? : Option NamedCategoryEntry)
    (ambient? : Option Value) : M Value := do
  let state ← registryState
  match b with
  | `(cas_term| (ℤ / $n)) =>
      let entry ← objectNotation state "(ℤ/)^"
      object state entry.name #[← eval scope n, ← eval scope k] category?
  | _ =>
    match ← eval scope b none ambient?, ← eval scope k with
    | .nat 2, X@(.object ..) => powerSetOf X
    | base, .nat e => power scope base e ambient?
    -- An exponent that is an element of `ℕ`: the registered power of a monoid.
    | base@(.element ..), e@(.element ..) => applyNamed state "^" #[base, e]
    | _, _ => throwStratum .invalid m!"`^` is `2^X` of a set or `x^k` of an element"

/-- Domains (`Xˣ`, `X ∖ 0`, `𝒫_fin(X)`, `C^∞`, `ℕ⁺`, `ℙ`), progressions, multiples, inverses and
coefficients, by syntax kind. -/
partial def evalNotation (scope : Scope) (stx : Syntax) : M (Option Value) := do
  let state ← registryState
  if stx.getKind == ``casUnits then
    return some (← object state "Units" #[← asObject (← eval scope stx[0])] none)
  if stx.getKind == ``casNonzero then
    unless stx[2].isNatLit? == some 0 do
      throwStratum .invalid m!"`X ∖ n` is written for `n = 0` only (the nonzero elements)"
    let .object _ _ (some (entry, params)) _ _ ← asObject (← eval scope stx[0])
      | throwStratum .invalid m!"`X ∖ 0` is of a named set"
    return some (← object state s!"{entry.name}∖0" params none)
  if stx.getKind == ``casFiniteSubsets then
    return some (← object state "𝒫_fin" #[← asObject (← eval scope stx[2])] none)
  if stx.getKind == ``casDomainAtom then
    let some atom := stx.find? (·.isAtom) | unreachable!
    return some (← object state atom.getAtomVal #[] none)
  if stx.getKind == ``casProgression then
    return some (← progression scope stx[1].getSepArgs)
  if stx.getKind == ``casMultiples then
    let k : NumLit := ⟨stx[0]⟩
    let atom := (stx[1].find? (·.isAtom)).map (·.getAtomVal) |>.getD "ℕ"
    let set : Syntax := mkNode ``casAtom #[mkAtom atom]
    let e ← `(cas_term| $k:num · $(mkIdent `«multiple index»):ident)
    return some (← imageOf scope e `«multiple index» (← eval scope set))
  if stx.getKind == ``casInverse then
    let operand ← eval scope stx[0]
    let .element _ X := operand
      | throwStratum .invalid m!"inversion is applied to an element of a registered group"
    let inverse ← applyOperation "⁻¹" #[operand] X
    if stx[2].getNumArgs == 0 then return some inverse
    return some (← apply scope inverse (stx[2][1].getSepArgs))
  if stx.getKind == ``casCoefficientOf then
    let n ← match stx[1] with
      | `(cas_term| $_:ident ^ $k:num) => pure k.getNat
      | `(cas_term| $_:ident²) => pure 2
      | `(cas_term| $_:ident³) => pure 3
      | `(cas_term| $_:ident) => pure 1
      | m => throwStratum .invalid m!"`[{shown m}]` is a monomial `tⁿ`"
    return some (← applyNamed state "coefficient" #[← eval scope stx[3], .nat n])
  return none

/-- A lambda supplied to a dependent declaration is read at that declaration's
complete function type or registered admission interface. No carrier chooses a
new structured morphism, and the original admitted computational point survives
the public codec's single-data-field wrapper projections. -/
partial def selectedTypedParameter (scope : Scope) (expected : Expr)
    (written : Syntax) : M Expr := do
  if let `(cas_term| ($body)) := written then
    return ← selectedTypedParameter scope expected body
  let isLambda := written.getKind == ``casPatternLambda ||
    (match written with | `(cas_term| $_:ident ↦ $_) => true | _ => false)
  unless isLambda do return ← typedParameter expected (← eval scope written)
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwStratum .invalid "a typed map parameter requires its registered category of sets"
  let type ← whnfR expected
  if type.isForall && !type.bindingBody!.hasLooseBVars then
    let source ← declaredEndpointObject type.bindingDomain! sets #[]
    let target ← declaredEndpointObject type.bindingBody! sets #[]
    return ← typedParameter expected
      (← eval scope written none (some (.homSet source target)))
  if let some (source, target) := homEnds? expected then
    if (← isType source) && (← isType target) then
      let context ← CategoryContext.ofNamed sets source
      if ← parameterTrial (withTransparency .all <|
          isDefEq (← CategoryContext.hom context source target) expected) then
        let source ← declaredEndpointObject source sets #[]
        let target ← declaredEndpointObject target sets #[]
        return ← typedParameter expected
          (← eval scope written none (some (.homSet source target)))
  if let some plan ← DeclaredAdmission.resolve? CategoryId.sets expected true then
    let domain ← recognize state plan.application.value sets #[] plan.application.explicit
    let some (_, endpoint) ← inclusionOut? domain
      | throwStratum .invalid "the registered typed map admission has no underlying data inclusion"
    let ambient ← inclusionTargetValue domain endpoint sets
    let admitted ← admit domain (← eval scope written none (some ambient))
    let value ← typedParameter plan.application.value admitted
    let projected ← DeclaredAdmission.project plan value
    Trace.alias (← read).trace value projected
    return projected
  throwStratum .invalid "the typed map parameter has no registered complete admission"

/-- Explicit category and functor parameters name accepted complete declarations. All other
parameters use the language's ordinary dependent parameter reader, including formal proofs. -/
partial def selectedParameterTerms (scope : Scope) (declaration : Name)
    (writtenArguments : Array Syntax) : M (Array Term) := do
  let state ← registryState
  let application ← DirectConstruction.instantiate declaration #[]
  unless writtenArguments.size <= application.explicit.size do
    throwStratum .invalid "the selected declaration has too many explicit parameters"
  let mut terms := #[]
  for (argument, written) in application.explicit.zip writtenArguments do
    for parameter in application.arguments do
      let parameter ← instantiateMVars parameter
      unless parameter.isMVar do continue
      let type ← instantiateMVars (← inferType parameter)
      if !type.hasMVar && (← isClass? type).isSome then
        if let some instanceValue := (← trySynthInstance type).toOption then
          discard <| isDefEq parameter instanceValue
    let expected ← instantiateMVars (← inferType argument)
    let named? := match written with
      | `(cas_term| $name:ident) => some (name.getId.toString false, (#[] : Array Syntax))
      | `(cas_term| $name:ident($parameters,*)) => some (name.getId.toString false, parameters.getElems)
      | _ => none
    let mut selected : Option Expr := none
    if let some (name, parameters) := named? then
      if let some category := state.categories.find? (fun row => row.name == name || row.id.raw == name) then
        let candidate ← DirectConstruction.instantiate category.declaration
          (← selectedParameterTerms scope category.declaration parameters)
        if ← parameterTrial (isDefEq (← inferType candidate.value) expected) then
          unless ← isDefEq (← inferType candidate.value) expected do unreachable!
          Trace.record (← read).trace candidate.value (.categoryParameter category.id candidate.explicit)
          selected := some candidate.value
      if selected.isNone then
        if let some functor := state.functors.find? (·.id.raw == name) then
          let candidate ← DirectConstruction.instantiate functor.declaration
            (← selectedParameterTerms scope functor.declaration parameters)
          let value ← Semantic.asFunctor candidate.value
          if ← parameterTrial (isDefEq (← inferType value) expected) then
            unless ← isDefEq (← inferType value) expected do unreachable!
            Trace.record (← read).trace value (.functorParameter functor.id candidate.explicit)
            selected := some value
    let supplied ← match selected with
      | some value => pure value
      | none => selectedTypedParameter scope expected written
    unless ← isDefEq argument supplied do
      throwStratum .invalid "the selected parameter differs from its dependent declaration slot"
    terms := terms.push (← quoteExpr (← instantiateMVars supplied))
  return terms

/-- The receiver's own registered category can fill a missing category argument, never
a category reconstructed from the receiver's carrier. -/
partial def constructionSelection (scope : Scope) (entry : ConstructionEntry)
    (parameters : Array Syntax) (receiver : Value) : M (DirectConstruction.Action × Expr) := do
  let original ← semanticObject receiver
  let context ← objectContext receiver
  let application ← DirectConstruction.instantiate entry.declaration
    (← selectedParameterTerms scope entry.declaration parameters)
  let functor ← Semantic.asFunctor application.value
  let (declaredSource, _) ← functorCategoryBundles functor
  let direct ← parameterTrial (withTransparency .all <| isDefEq declaredSource context.bundle)
  if direct then
    unless ← withTransparency .all <| isDefEq declaredSource context.bundle do unreachable!
  else
    let selectedCategory := context.bundle
    for argument in application.explicit do
      if (← instantiateMVars argument).isMVar then
        if ← parameterTrial (isDefEq (← inferType argument) (← inferType selectedCategory)) then
          unless ← isDefEq argument selectedCategory do
            throwStratum .invalid "the construction requires a different selected category"
  let type ← whnfR (← inferType functor)
  unless type.isAppOf ``CategoryTheory.Functor do
    throwStratum .invalid "the selected construction has no complete functor source"
  let sourceType ← whnfR type.getAppArgs[0]!
  let actual ← if ← parameterTrial (isDefEq (← inferType original) sourceType) then
    typedParameter sourceType receiver
  else if sourceType.isAppOf ``CategoryTheory.Core then do
    let wrapped ← mkAppM ``CategoryTheory.Core.mk #[original]
    unless ← withTransparency .all <| isDefEq (← inferType wrapped) sourceType do
      throwStratum .invalid "the construction core source has different complete parameters"
    Trace.record (← read).trace wrapped (.coreObject context original)
    pure wrapped
  else
    typedParameter sourceType receiver
  let action ← DirectConstruction.select entry
    (← application.explicit.mapM fun argument => do quoteExpr (← instantiateMVars argument)) actual
  return (action, actual)

partial def directConstruction (scope : Scope) (entry : ConstructionEntry)
    (arguments : Array Syntax) : M Value := do
  let some receiverSyntax := arguments.back?
    | throwStratum .invalid "a direct construction requires its selected receiver"
  let receiver ← eval scope receiverSyntax
  let (action, actual) ← constructionSelection scope entry
    (arguments.extract 0 (arguments.size - 1)) receiver
  let result ← DirectConstruction.obj action actual
  Trace.record (← read).trace result (.construction entry.id action.parameters actual)
  objectInContext result action.target #[receiver]

/-- A core map is admitted only from an actual accepted isomorphism, retaining both
directions. A plain map is never upgraded merely because its endpoint carriers agree. -/
partial def constructionCoreMap (morphism source target : Expr) : M (Expr × Expr × Expr) := do
  let some trace := (← read).trace
    | throwStratum .invalid "a core map requires retained accepted comparison data"
  let some node ← trace.node? morphism
    | throwStratum .invalid "the core map has no selected accepted isomorphism"
  let comparison ← match node with
    | .presentation id params inverse => do
      let some entry := (← registryState).presentations.find? (·.id == id)
        | throwStratum .invalid "the selected isomorphism is not registered"
      let value ← elabTermAndSynthesize
        (← `($(mkCIdent entry.declaration) $(← params.mapM fun value => exprToSyntax value)*)) none
      if inverse then mkAppM ``CategoryTheory.Iso.symm #[value] else pure value
    | .cellComponent id params constructors inverse receiver => do
      let some entry := (← registryState).cells.find? (·.id == id)
        | throwStratum .invalid "the selected cell comparison is not registered"
      let action ← CellAction.select entry (← params.mapM fun value => exprToSyntax value)
        constructors inverse receiver
      CellAction.componentIso action receiver
    | .morphismIdentity _ object => mkAppM ``CategoryTheory.Iso.refl #[object]
    | .contextualIdentity _ object => mkAppM ``CategoryTheory.Iso.refl #[object]
    | _ => throwStratum .invalid "the selected morphism has no accepted inverse data"
  let forward ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
  let backward ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
  unless ← withTransparency .all <| isDefEq forward morphism <&&>
      isDefEq (← inferType forward) (← mkAppM ``Quiver.Hom #[source, target]) do
    throwStratum .invalid "the core comparison changes its selected complete endpoints"
  if let .presentation id params inverse := node then
    Trace.record (← read).trace forward (.presentation id params inverse)
    Trace.record (← read).trace backward (.presentation id params (!inverse))
  if let .cellComponent id params constructors inverse receiver := node then
    Trace.record (← read).trace forward (.cellComponent id params constructors inverse receiver)
    Trace.record (← read).trace backward (.cellComponent id params constructors (!inverse) receiver)
  let coreSource ← mkAppM ``CategoryTheory.Core.mk #[source]
  let coreTarget ← mkAppM ``CategoryTheory.Core.mk #[target]
  let arrow ← mkAppOptM ``CategoryTheory.CoreHom.mk
    #[none, none, some coreSource, some coreTarget, some comparison]
  return (arrow, forward, backward)

partial def directConstructionMapAt (scope : Scope) (entry : ConstructionEntry) (parameters : Array Syntax)
    (morphismSyntax : Syntax) : M Value := do
  let morphismValue ← eval scope morphismSyntax
  let (morphism, source, target, context, sourceValue, targetValue) ← morphismContext morphismValue
  let (action, actualSource) ← constructionSelection scope entry parameters sourceValue
  let (actualTarget, actualMap) ← if ← parameterTrial (isDefEq (← inferType source) action.source) then
    pure (target, morphism)
  else if (← whnfR action.source).isAppOf ``CategoryTheory.Core then do
    let actualTarget ← mkAppM ``CategoryTheory.Core.mk #[target]
    let (actualMap, forward, backward) ← constructionCoreMap morphism source target
    Trace.record (← read).trace actualTarget (.coreObject context target)
    Trace.record (← read).trace actualMap (.coreIso context source target forward backward)
    pure (actualTarget, actualMap)
  else pure (target, morphism)
  let result ← DirectConstruction.map action actualSource actualTarget actualMap
  let imageSource ← DirectConstruction.obj action actualSource
  let imageTarget ← DirectConstruction.obj action actualTarget
  Trace.record (← read).trace imageSource (.construction entry.id action.parameters actualSource)
  Trace.record (← read).trace imageTarget (.construction entry.id action.parameters actualTarget)
  Trace.record (← read).trace result
    (.constructionMap entry.id action.parameters actualSource actualTarget actualMap)
  morphismInContext result imageSource imageTarget action.target
    (← objectInContext imageSource action.target #[sourceValue],
      ← objectInContext imageTarget action.target #[targetValue])

partial def directConstructionMap (scope : Scope) (name : String) (parameters : Array Syntax)
    (morphismSyntax : Syntax) : M Value := do
  let state ← registryState
  let entries := state.constructions.filter (fun row => row.name == name || row.id.raw == name)
  let edges := (state.functors.filter (·.id.raw == name)).map (EdgeRef.functor ∘ (·.id)) ++
    (state.classifiers.filter (·.id.raw == name)).map (EdgeRef.classifierForget ∘ (·.id))
  let actions := (entries.map fun entry =>
      directConstructionMapAt scope entry parameters morphismSyntax) ++
    (edges.map fun edge => registeredEdgeMapAt scope edge parameters morphismSyntax)
  if let #[action] := actions then return ← action
  let applicable ← actions.filterM fun action => parameterCompatible do
    discard action
    pure true
  match applicable with
  | #[action] => action
  | #[] => throwStratum .invalid "no registered action maps these complete arguments"
  | _ => throwSemanticAmbiguity "several registered actions map these complete arguments"

/-- Select the whole accepted isomorphism by its declaration, preserving both
directions for later core constructions and the exact registered endpoints. -/
partial def selectedPresentation (scope : Scope) (name : String) (parameters : Array Syntax)
    (inverse : Bool) : M Value := do
  let state ← registryState
  let #[entry] := state.presentations.filter (fun row => row.name == name || row.id.raw == name)
    | throwStratum .invalid "the selected presentation is absent or ambiguous"
  let application ← DirectConstruction.instantiate entry.declaration
    (← selectedParameterTerms scope entry.declaration parameters)
  let application ← DirectConstruction.close application
  let arrow ← Semantic.presentationArrow entry application.value inverse (← read).trace
  let some (source, target) := homEnds? (← inferType arrow)
    | throwStratum .invalid "the selected presentation lost its complete map endpoints"
  let sourceId := if inverse then entry.target else entry.source
  let targetId := if inverse then entry.source else entry.target
  let some sourceRow := state.objects.find? (·.id == sourceId)
    | throwStratum .invalid "the selected presentation source is not registered"
  let some targetRow := state.objects.find? (·.id == targetId)
    | throwStratum .invalid "the selected presentation target is not registered"
  let some category := state.categories.find? (·.id == sourceRow.category)
    | throwStratum .invalid "the selected presentation category is not registered"
  unless targetRow.category == category.id do
    throwStratum .invalid "the selected presentation has different endpoint categories"
  let endpoint (object : Expr) : M Value := do
    if let some value ← optionalReading (recognize state object category) then return value
    -- The accepted comparison already fixes the whole endpoint, including its
    -- universe and dependent parameters. A fresh named call must not discard them.
    objectInContext object (← CategoryContext.ofNamed category object)
  let sourceValue ← endpoint source
  let targetValue ← endpoint target
  discard <| Semantic.recordNamedObject source (← read).trace
  discard <| Semantic.recordNamedObject target (← read).trace
  return .morphism arrow source target category (some (sourceValue, targetValue))

partial def retainedLiftPlans (receiver : Expr) : M (Array SelectedLift.Plan) := do
  let some trace := (← read).trace | throwStratum .invalid "the lift has no retained selection"
  return (← SelectedLift.recorded trace receiver).plans

partial def selectedLiftComposite (scope : Scope) (selected : Syntax) : M Value := do
  let receiverValue ← eval scope selected
  let receiver ← semanticObject receiverValue
  let some trace := (← read).trace | throwStratum .invalid "the lift has no retained selection"
  let recorded ← SelectedLift.recorded trace receiver true
  let some first := recorded.plans[0]?
    | throwStratum .invalid "the composed lift has no selected stage"
  let context ← SelectedLift.context first
  let object ← SelectedLift.port recorded.plans 0
  let result ← SelectedLift.retainSelection object (some receiver)
  Trace.record (some trace) result (.liftProjection receiver "composed")
  objectInContext result context #[receiverValue]

partial def selectedLift (scope : Scope) (name : String) (parameters : Array Syntax)
    (sourceSyntax inclusionSyntax proofSyntax : Syntax) : M Value := do
  let state ← registryState
  let some entry := state.lifts.find? (·.id.raw == name)
    | throwStratum .invalid "the selected lift is not registered"
  let sourceValue ← eval scope sourceSyntax
  let source ← semanticObject sourceValue
  let sourceContext ← objectContext sourceValue
  let (inclusion, domain, _, _, _, _) ← morphismContext (← eval scope inclusionSyntax)
  let monic ← typedParameter (← mkAppM ``CategoryTheory.Mono #[inclusion])
    (← eval scope proofSyntax)
  let plan ← SelectedLift.select entry
    (← selectedParameterTerms scope entry.evidence parameters) source inclusion monic
    (domain? := some domain)
  let context ← SelectedLift.context plan
  unless context.expression.syntacticEq sourceContext.expression &&
      (← withTransparency .all <| isDefEq context.bundle sourceContext.bundle) do
    throwStratum .invalid "the explicit lift changed the complete selected source context"
  let object ← SelectedLift.retainSelection plan.ports[0]!
  Trace.record (← read).trace object (.selectedLift entry.id plan.parameters source inclusion monic)
  objectInContext object context #[sourceValue]

partial def selectedLiftField (receiver : Value) (name : String) : M (Option Value) := do
  unless #["obj", "hom", "forward", "backward"].contains name do return none
  let object ← match receiver with
    | .object object .. | .derivedObject object .. => pure object
    | _ => return none
  let some trace := (← read).trace | return none
  let selected := match ← trace.node? object with
    | some (.selectedLift ..) | some (.methodWithLifts ..) |
        some (.liftProjection _ "obj") | some (.liftProjection _ "composed") => true
    | _ => false
  unless selected do return none
  let plans ← retainedLiftPlans object
  let some plan := plans[0]? | throwStratum .invalid "the retained lift has no output ports"
  let some index := LiftField.all.findIdx? (·.label == name) | unreachable!
  let value ← SelectedLift.port plans index
  if name == "obj" && (← isDefEq object value) then return some receiver
  let value ← StructuredProjection.retainPortValue object value index
  let sourceContext ← SelectedLift.context plan
  Trace.record (← read).trace value (.liftProjection object name)
  if index == 0 then return some (← objectInContext value sourceContext #[receiver])
  let context ← if index == 1 then pure sourceContext else do
    let some last := plans.back? | unreachable!
    SelectedLift.context last true
  let some (source, target) := homEnds? (← inferType value)
    | throwStratum .invalid "the selected lift field lost its complete endpoints"
  return some (← morphismInContext value source target context
    (← objectInContext source context #[receiver], ← objectInContext target context #[receiver]))

/-- Public fields consume the entire accepted structured result. Their data-constructor
addresses, full endpoint category and original receiver remain in the reading. -/
partial def structuredField (receiver : Value) (name : String) (index : Option Nat := none) :
    M (Option Value) := do
  unless #["obj", "source", "target", "hom", "inclusion", "field"].contains name do return none
  if ((receiver matches .morphism ..) || (receiver matches .derivedMorphism ..)) &&
      !(index.isNone && (name == "source" || name == "target")) then return none
  -- A typed map already fixes both complete objects. Read its endpoints through
  -- the accepted Arrow construction, retaining the actual callable and category.
  let receiver ← match receiver with
    | .morphism .. | .derivedMorphism .. => do
        let (hom, source, target, context, first, second) ← morphismContext receiver
        let #[constructor] := (← registryState).constructors.filter
            (·.semantics == `CasCatalogue.Constructors.arrow)
          | throwStratum .invalid "the complete Arrow context is absent or ambiguous"
        let arrowContext ← CategoryContext.construct context constructor.id
        let arrow ← mkAppOptM ``CategoryTheory.Arrow.mk
          #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
            some source, some target, some hom]
        Trace.record (← read).trace arrow (.contextualArrow context hom source target)
        objectInContext arrow arrowContext #[receiver, first, second]
    | _ => pure receiver
  let object ← match receiver with
    | .object object .. | .derivedObject object .. => pure object
    | _ => return none
  let context ← objectContext receiver
  if index.isNone then
    if let some plan ← StructuredProjection.arrow? object context then
      let (value, resultContext, morphism) ← plan.field name
      if value == object then return some receiver
      let endpoint := fun field value => do
        unless value == object do
          Trace.record (← read).trace value (.structuredProjection object field none)
        objectInContext value plan.base #[receiver]
      let endpoints ← if morphism then
        pure (some (← endpoint "source" plan.source, ← endpoint "target" plan.target))
        else pure none
      Trace.record (← read).trace value (.structuredProjection object name none)
      if let some endpoints := endpoints then
        return some (← morphismInContext value plan.source plan.target resultContext endpoints)
      return some (← objectInContext value resultContext #[receiver])
  unless name == "obj" || name == "hom" || name == "field" do return none
  let some plan ← StructuredProjection.construction? object context (← read).trace | return none
  if name == "obj" then return some receiver
  let port ← plan.selectPort index
  let value ← StructuredProjection.retainPortValue object port.formalField port.index
  Trace.record (← read).trace value (.structuredProjection object "field" (some port.index))
  if let some (source, target) := homEnds? port.expectedType then
    CategoryContext.checkMorphism context value source target
    let endpoint := fun value => do
      if ← withTransparency .all <| isDefEq value object then return receiver
      objectInContext value context #[receiver]
    return some (← morphismInContext value source target context
      (← endpoint source, ← endpoint target))
  CategoryContext.checkObject context value
  return some (← objectInContext value context #[receiver])

/-- Reindex whole objects or whole fibre maps, and select the canonical cartesian
map of the same accepted family transport. The original base map is never inferred
back from its result or erased from the retained invocation. -/
partial def reindexValue (receiver baseValue : Value) (cartesian : Bool) : M Value := do
  let (base, _, _, _, _, _) ← morphismContext baseValue
  let sourceContext : CategoryContext ← match receiver with
    | .morphism .. | .derivedMorphism .. => do
      let (_, _, _, context, _, _) ← morphismContext receiver
      pure context
    | _ => objectContext receiver
  let plan ← ReindexAction.resolve base sourceContext
  if cartesian then
    let object ← semanticObject receiver
    let (value, source, target) ← ReindexAction.cartesian plan object
    Trace.record (← read).trace source (.cartesian plan.entry.id plan.parameters base object "source")
    Trace.record (← read).trace target (.cartesian plan.entry.id plan.parameters base object "target")
    Trace.record (← read).trace value (.cartesian plan.entry.id plan.parameters base object "hom")
    return ← morphismInContext value source target plan.total
      (← objectInContext source plan.total #[receiver, baseValue],
        ← objectInContext target plan.total #[receiver, baseValue])
  if (receiver matches .morphism ..) || (receiver matches .derivedMorphism ..) then
    let (hom, source, target, _, sourceValue, targetValue) ← morphismContext receiver
    let value ← ReindexAction.map plan hom (some (source, target))
    let sourceImage ← ReindexAction.object plan source
    let targetImage ← ReindexAction.object plan target
    for (formal, original) in #[(sourceImage, source), (targetImage, target)] do
      unless formal == original do
        Trace.record (← read).trace formal (.functor plan.entry.id plan.parameters original)
    Trace.record (← read).trace value (.contextualRoute sourceContext plan.target
      #[.functor plan.entry.id] #[plan.action] hom true)
    return ← morphismInContext value sourceImage targetImage plan.target
      (← objectInContext sourceImage plan.target #[sourceValue, baseValue],
        ← objectInContext targetImage plan.target #[targetValue, baseValue])
  let object ← semanticObject receiver
  let value ← ReindexAction.object plan object
  Trace.record (← read).trace value (.functor plan.entry.id plan.parameters object)
  objectInContext value plan.target #[receiver, baseValue]

partial def selectedLiftFactor (scope : Scope) (receiverSyntax baseMapSyntax coneSyntax proofSyntax : Syntax) :
    M Value := do
  let receiverValue ← eval scope receiverSyntax
  let receiver ← semanticObject receiverValue
  let plans ← retainedLiftPlans receiver
  let (baseMap, _, _, _, _, _) ← morphismContext (← eval scope baseMapSyntax)
  let (cone, domain, _, context, domainValue, _) ← morphismContext (← eval scope coneSyntax)
  let mut mapped := cone
  for plan in plans do mapped ← Semantic.mapOf plan.action mapped
  let some last := plans.back? | throwStratum .invalid "a factor requires a nonempty selected lift"
  let equation ← mkEq mapped (← mkAppM ``CategoryTheory.CategoryStruct.comp #[baseMap, last.inclusion])
  let proof ← typedParameter equation (← eval scope proofSyntax)
  let steps ← SelectedLift.factors plans baseMap cone proof
  let some step := steps.back? | throwStratum .invalid "the factor has no selected computation"
  let some (factorDomain, factorTarget) := homEnds? (← inferType step.factor)
    | throwStratum .invalid "the factor has no complete categorical result type"
  unless ← isDefEq factorDomain domain do
    throwStratum .invalid "the factor changed its original generalized domain"
  let targetValue ← objectInContext factorTarget context #[receiverValue]
  unless ← isDefEq factorTarget receiver do
    Trace.record (← read).trace factorTarget (.liftProjection receiver "obj")
  let factor ← SelectedLift.retainSelection step.factor (some receiver)
  Trace.record (← read).trace factor (.liftFactor receiver baseMap cone proof)
  morphismInContext factor factorDomain factorTarget context (domainValue, targetValue)

partial def selectedCell (scope : Scope) (name : String) (parameters : Array Syntax)
    (receiverSyntax : Syntax) (constructors : Array ConstructorId) (inverse : Bool) : M Value := do
  let state ← registryState
  let some entry := state.cells.find? (·.id.raw == name)
    | throwStratum .invalid "the selected natural cell is not registered"
  let receiverValue ← eval scope receiverSyntax
  let receiver ← match receiverValue with
    | .object value .. | .derivedObject value .. => pure value
    | .morphism .. | .derivedMorphism .. => do
      let (value, source, target, context, _, _) ← morphismContext receiverValue
      let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[value]
      Trace.record (← read).trace arrow (.contextualArrow context value source target)
      pure arrow
    | _ => throwStratum .invalid "a cell component requires its exact selected object"
  let action ← CellAction.select entry
    (← selectedParameterTerms scope entry.declaration parameters) constructors inverse receiver
  let value ← CellAction.component action receiver
  let (source, target) ← CellAction.objects action receiver
  let context : CategoryContext := { expression := action.target, bundle := action.targetBundle }
  unless source == receiver do
    Trace.record (← read).trace source
      (.cellEndpoint entry.id action.parameters constructors inverse false receiver)
  unless target == receiver do
    Trace.record (← read).trace target
      (.cellEndpoint entry.id action.parameters constructors inverse true receiver)
  Trace.record (← read).trace value
    (.cellComponent entry.id action.parameters constructors inverse receiver)
  morphismInContext value source target context
    (← objectInContext source context #[receiverValue],
      ← objectInContext target context #[receiverValue])

/-- Select the complete accepted action at its exact source bundle. Explicit
parameters belong to the registered declaration; no structural search selects an action. -/
partial def selectedEdgeAction (scope : Scope) (edge : EdgeRef) (parameters : Array Syntax)
    (context : CategoryContext) : M (Expr × Array Expr × CategoryContext) := do
  let state ← registryState
  let (declaration, target) ← match edge with
    | .functor id =>
        let some entry := state.functor? id
          | throwStratum .invalid "the selected functor is not registered"
        pure (entry.declaration, entry.target)
    | .classifierForget id =>
        let some entry := state.classifier? id
          | throwStratum .invalid "the selected classifier forgetful action is not registered"
        pure (entry.declaration, entry.host)
    | _ => throwStratum .invalid "this selector requires one complete registered action"
  let application ← DirectConstruction.instantiate declaration
    (← selectedParameterTerms scope declaration parameters)
  let action ← match edge with
    | .classifierForget _ => do
        let type ← whnfR (← inferType application.value)
        let classifier ← if type.isAppOf ``LeanCategories.PropertyClassifier then
            mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[application.value]
          else if type.isAppOf ``LeanCategories.StructureClassifier then
            mkAppM ``LeanCategories.StructureClassifier.toClassifier #[application.value]
          else pure application.value
        let forgetful ← mkAppM ``LeanCategories.Classifier.forget #[classifier]
        Semantic.asFunctor forgetful
    | _ => Semantic.asFunctor application.value
  let (sourceBundle, _) ← functorCategoryBundles action
  unless ← parameterTrial (withTransparency .all <| isDefEq sourceBundle context.bundle) do
    CategoryContext.exposeStructureParameters application.value
  unless ← withTransparency .all <| isDefEq sourceBundle context.bundle do
    throwStratum .invalid "the selected action has a different complete source category"
  let application ← DirectConstruction.close application
  let action ← instantiateMVars action
  let (_, bundle) ← functorCategoryBundles action
  let target ← CategoryContext.presented { expression := target, bundle }
  return (action, application.explicit, target)

partial def registeredEdgeViewAt (scope : Scope) (edge : EdgeRef)
    (parameters : Array Syntax) (receiverSyntax : Syntax) : M Value := do
  let receiver ← eval scope receiverSyntax
  let object ← semanticObject receiver
  let context ← objectContext receiver
  let (action, arguments, target) ← selectedEdgeAction scope edge parameters context
  let image ← Semantic.objOf action object
  CategoryContext.checkObject target image
  -- Preserve the existing named-functor question record. Contextual actions retain
  -- complete categories for classifier forgetful actions and unnamed derived contexts.
  if let .functor id := edge then
    if receiver matches .object .. then
      if (CategoryContext.named? (← registryState) target.expression).isSome then
        Trace.record (← read).trace image (.functor id arguments object)
      else
        Trace.record (← read).trace image
          (.contextualRoute context target #[edge] #[action] object false)
    else
      Trace.record (← read).trace image
        (.contextualRoute context target #[edge] #[action] object false)
  else
    Trace.record (← read).trace image
      (.contextualRoute context target #[edge] #[action] object false)
  let value ← objectInContext image target #[receiver]
  match value with
  | .object handle category origin selected _ =>
      return .object handle category origin selected
        (some (#[receiver], receiver, #[edge], #[], #[(edge, action.getAppArgs)]))
  | _ => return value

partial def registeredEdgeView (scope : Scope) (receiver : Syntax) (id : String)
    (parameters : Array Syntax) : M Value := do
  let state ← registryState
  let edges := (state.functors.filter (·.id.raw == id)).map (EdgeRef.functor ∘ (·.id)) ++
    (state.classifiers.filter (·.id.raw == id)).map (EdgeRef.classifierForget ∘ (·.id))
  if let #[edge] := edges then return ← registeredEdgeViewAt scope edge parameters receiver
  let applicable ← edges.filterM fun edge => parameterCompatible do
    discard <| registeredEdgeViewAt scope edge parameters receiver
    pure true
  match applicable with
  | #[edge] => registeredEdgeViewAt scope edge parameters receiver
  | #[] => throwStratum .invalid "no registered action accepts this complete selected object"
  | _ => throwSemanticAmbiguity "several registered actions accept this complete selected object"

partial def registeredEdgeMapAt (scope : Scope) (edge : EdgeRef)
    (parameters : Array Syntax) (receiverSyntax : Syntax) : M Value := do
  let receiver ← eval scope receiverSyntax
  let (hom, source, target, context, sourceValue, targetValue) ← morphismContext receiver
  let (action, _, imageContext) ← selectedEdgeAction scope edge parameters context
  let imageSource ← Semantic.objOf action source
  let imageTarget ← Semantic.objOf action target
  let result ← Semantic.mapOf action hom
  CategoryContext.checkMorphism imageContext result imageSource imageTarget
  for (image, original) in #[(imageSource, source), (imageTarget, target)] do
    unless image == original do
      Trace.record (← read).trace image
        (.contextualRoute context imageContext #[edge] #[action] original false)
  Trace.record (← read).trace result
    (.contextualRoute context imageContext #[edge] #[action] hom true)
  morphismInContext result imageSource imageTarget imageContext
    (← objectInContext imageSource imageContext #[sourceValue],
      ← objectInContext imageTarget imageContext #[targetValue])

partial def structuredParameterView (original : Value) (actual : Expr)
    (category : NamedCategoryEntry) : M Value := do
  if let .object handle sourceCategory origin selected _ := original then
    if sourceCategory.id == category.id && !actual.hasMVar && !actual.hasLevelMVar &&
        (← isTypeCorrect actual) &&
        (← isDefEq (← inferType handle) (← inferType actual)) &&
        (← withTransparency .all <| isDefEq handle actual) then
      Trace.alias (← read).trace handle actual
      return .object actual category origin selected
        (some (#[original], original, #[], #[], #[]))
  let chosen := match original with
    | .object _ _ _ (some selected) _ => selected
    | _ => original
  if let .object handle sourceCategory origin selected _ := chosen then
    if sourceCategory.id == category.id && !actual.hasMVar &&
        (← isTypeCorrect actual) &&
        (← isDefEq (← inferType handle) (← inferType actual)) &&
        (← withTransparency .all <| isDefEq handle actual) then
      Trace.alias (← read).trace handle actual
      return .object actual category origin selected
        (some (#[original], chosen, #[], #[], #[]))
  let recorder ← Trace.new
  let expected ← inferType actual
  let recorded ← withReader (fun context => { context with trace := some recorder }) do
    typedParameter expected original
  unless ← isDefEq recorded actual do
    throwStratum .invalid m!"a structural view differs from its accepted parameter"
  let some node ← recorder.node? recorded
    | throwStratum .invalid m!"a converted structure has no retained registered source"
  let state ← registryState
  let (sourceCategoryId, receiver, route, alternatives, fullApplications) ← match node with
    | .object id parameters => do
        let some entry := state.objects.find? (·.id == id)
          | throwStratum .invalid m!"a direct structural source object is not registered"
        unless entry.category == category.id do
          throwStratum .invalid m!"a direct structural source has the wrong category"
        let receiver ← Semantic.object entry
          (← parameters.mapM fun parameter => do pure (← quoteExpr parameter)) none
        unless !receiver.hasMVar && (← isTypeCorrect receiver) &&
            (← isDefEq (← inferType receiver) expected) && (← isDefEq receiver actual) do
          throwStratum .invalid m!"the registered direct source is not the complete parameter"
        pure (entry.category, receiver, #[], #[], #[])
    | .retainedRoute sourceCategory _ route applications receiver =>
        pure (sourceCategory, receiver, route, #[], applications)
    | .parameterEquivalence _ representative alternatives => do
        unless ← isDefEq representative actual do
          throwStratum .invalid m!"the complete equivalent parameter differs from the view"
        let some presentation := alternatives[0]?
          | throwStratum .invalid m!"an equivalent parameter has no source presentations"
        pure (presentation.sourceCategory, presentation.object, presentation.route,
          alternatives, presentation.applications)
    | _ => throwStratum .invalid m!"a converted parameter is not a registered structural view"
  let some sourceCategory := state.categories.find? (·.id == sourceCategoryId)
    | throwStratum .invalid m!"a structural view source category is not registered"
  let source ← try recognize state receiver sourceCategory catch error =>
    if (CasCatalogue.Exception.interpretationKind error) != .invalid then throw error
    let candidates := sourceParameterValues original
    let some source ← candidates.findM? fun candidate => parameterTrial do
      let .object handle candidateCategory .. := candidate | return false
      return candidateCategory.id == sourceCategory.id && (← isDefEq handle receiver)
      | throwStratum .invalid m!"an anonymous structural source value was not retained"
    pure source
  unless route.size == fullApplications.size do
    throwStratum .invalid m!"a structural view lost its exact ordered edge applications"
  let applications := route.zip (fullApplications.map Expr.getAppArgs)
  let (image, _) ← retainedActions state receiver route applications
  unless ← isDefEq image actual <&&> isDefEq (← inferType image) expected do
    throwStratum .invalid m!"the structural source route does not give the complete parameter"
  let value ← try recognize state actual category catch error =>
    if (CasCatalogue.Exception.interpretationKind error) == .invalid then
      pure (Value.object actual category none none none)
    else throw error
  let .object handle target origin selected _ := value | unreachable!
  return .object handle target origin selected (some (#[original], source, route, alternatives, applications))

partial def registeredObject (state : RegistryState) (entry : ObjectEntry)
    (args : Array Value) : M Value := do
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the object {entry.name} has an unregistered category"
  let params ← typedParamTerms entry.declaration args
  let handle ← Semantic.object entry params (← read).trace
  let family ← instantiateFresh category.declaration
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
  unless ← isDefEq (← inferType handle) expected do
    throwStratum .invalid m!"the parameters of {entry.name} do not form an object of {category.name}"
  -- A category family may have an object universe independent of its base parameter.
  -- Its actual object's full type fixes that universe before closure is required.
  let handle ← instantiateMVars handle
  let family ← instantiateMVars family
  if handle.hasMVar || handle.hasLevelMVar || family.hasMVar || family.hasLevelMVar then
    throwStratum .invalid m!"the object parameters of {entry.name} are not determined"
  unless ← isTypeCorrect handle do
    throwStratum .invalid m!"an object parameter is outside its declared dependent signature"
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (parameters, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (parameters.zip infos).filterMap fun (parameter, info) =>
    if info.isExplicit then some parameter else none
  let mut retained : Array Value := #[]
  for (parameter, value) in explicit.zip args do
    let expected ← instantiateMVars (← inferType parameter)
    let actual ← typedParameter expected value
    discard <| isDefEq parameter actual
    let value ← match value with
      | .object original _ _ _ _ =>
          if ← parameterTrial (isDefEq (← inferType original) expected) then pure value
          else do
            let mut categories := #[]
            for candidate in state.categories do
              if ← parameterCompatible (do
                  let family ← instantiateFresh candidate.declaration
                  isDefEq (← inferType actual) (← mkAppM ``CategoryTheory.Bundled.α #[family])) then
                categories := categories.push candidate
            let selectedCategory ← match categories.toList with
              | [candidate] => pure candidate
              | [] => throwStratum .invalid m!"a selected constructor parameter has no category"
              | _ => throwSemanticAmbiguity m!"a selected constructor parameter has several categories"
            if selectedCategory.id == CategoryId.sets then carrierObject value
            else structuredParameterView value actual selectedCategory
      | _ => pure value
    retained := retained.push value
  return .object handle category (some (entry, retained)) none none

partial def object (state : RegistryState) (name : String) (args : Array Value)
    (category? : Option NamedCategoryEntry) : M Value := do
  registeredObject state (← objectNamed state name category?) args

/-- A notation's default object is the exact published row, including its category. -/
partial def notationObject (surfaceForm : String) : M Value := do
  let state ← registryState
  registeredObject state (← objectNotation state surfaceForm) #[]

/-- Read an explicit category context by an accepted structural action on the complete object.
The retained source supplies the parameters and provenance of a computed object's new view. -/
partial def objectInCategory (value : Value) (target : NamedCategoryEntry) : M Value := do
  let .object _ sourceCategory .. := value
    | throwStratum .invalid m!"a category context requires an object"
  if sourceCategory.id == target.id then return value
  if target.id == CategoryId.sets then return ← carrierObject value
  let family ← instantiateFresh target.declaration
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
  let actual ← typedParameter expected value
  structuredParameterView value actual target

/-- The method or property `name` of the object `t`. -/
partial def call (scope : Scope) (t : Syntax) (name : String)
    (category? : Option NamedCategoryEntry) : M Value := do
  let state ← registryState
  let receiver ← eval scope t category?
  if let some field ← selectedLiftField receiver name then return field
  if let some field ← structuredField receiver name then return field
  if let .derivedMorphism hom source target context _ := receiver then
    let #[constructor] := state.constructors.filter
        (·.semantics == `CasCatalogue.Constructors.arrow)
      | throwStratum .invalid "the complete Arrow context is absent or ambiguous"
    let arrowContext ← CategoryContext.construct context constructor.id
    let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[hom]
    Trace.record (← read).trace arrow (.contextualArrow context hom source target)
    let (value, resultContext) ← Semantic.methodIn name arrow arrowContext.expression (← read).trace
    return ← objectInContext value resultContext #[receiver]
  if let .derivedObject handle context _ := receiver then
    CategoryContext.checkObject context handle
    if name == "hom" then
      if let .construct constructor #[.category base] := context.expression then
        if (state.constructor? constructor).any
            (·.semantics == `CasCatalogue.Constructors.arrow) then
          let type ← whnfR (← inferType handle)
          unless type.isAppOfArity ``CategoryTheory.Arrow 2 do
            throwStratum .invalid "the derived Arrow context changed its full type"
          let bundle ← mkAppOptM ``CategoryTheory.Cat.of
            #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
          let baseContext ← CategoryContext.presented { expression := base, bundle }
          let source ← mkAppM ``CategoryTheory.Arrow.left #[handle]
          let target ← mkAppM ``CategoryTheory.Arrow.right #[handle]
          let hom ← mkAppM ``CategoryTheory.Arrow.hom #[handle]
          Trace.record (← read).trace hom (.arrowProjection handle)
          return ← morphismInContext hom source target baseContext
            (← objectInContext source baseContext #[receiver],
              ← objectInContext target baseContext #[receiver])
    if state.properties.any (·.name == name) && !state.methods.any (·.name == name) then
      return .answer (← Semantic.propertyIn name handle context.expression (← read).trace)
    let (value, resultContext) ← Semantic.methodIn name handle context.expression (← read).trace
    return ← objectInContext value resultContext #[receiver]
  -- A method of sets on a subset: of its extent.
  let receiver ← if (← powerSetOf? receiver).isSome && state.methods.any (·.name == name) &&
      !state.morphisms.any (·.name == name) then
      asObject receiver
    else pure receiver
  if let .element .. := receiver then return ← applyNamed state name #[receiver]
  -- `(360).prime_factors()`: a numeral, in the set the family takes.
  if let .nat _ := receiver then return ← applyNamed state name #[receiver]
  -- `f.image()`: the image of a map, by the registered power object.
  if let .morphism h _ _ _ (some (X, Y)) := receiver then
    if name == "image" then return ← imageOfMap h X Y
  -- A map is an object of the registered arrow category; its methods follow the same
  -- structural closure and prescribed lifts as every other object's methods.
  if let .morphism hom source target sourceCategory _ := receiver then
    let some arrowExpression := state.arrowsOf? sourceCategory.expression
      | throwStratum .invalid "the arrow-category constructor is not registered"
    let arrowCategories := state.categories.filter (·.expression.syntacticEq arrowExpression)
    let arrowCategory ← match arrowCategories with
      | #[category] => pure category
      | #[] => throwStratum .invalid m!"the map's arrow category is not registered"
      | _ => throwSemanticAmbiguity m!"several registered categories identify this map's arrow category"
    let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[hom]
    discard <| Semantic.recordNamedObject source (← read).trace
    discard <| Semantic.recordNamedObject target (← read).trace
    Trace.record (← read).trace arrow (.arrow sourceCategory.id hom source target)
    let (value, target) ← Semantic.method name arrow arrowCategory (← read).trace
    return .object value target none none none
  let .object handle category _ _ _ := receiver
    | throwStratum .invalid m!"`{name}` is called on an object or an element"
  -- The registered arrow constructor retains its actual typed endpoints and stored map.
  if name == "hom" then
    if let .construct constructor #[.category base] := category.expression then
      if (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) then
        let sourceCategory ← Semantic.namedCategoryFor state base
        let source ← mkAppM ``CategoryTheory.Arrow.left #[handle]
        let target ← mkAppM ``CategoryTheory.Arrow.right #[handle]
        let hom ← mkAppM ``CategoryTheory.Arrow.hom #[handle]
        unless ← isTypeCorrect hom do
          throwStratum .invalid m!"the stored arrow is outside its selected category"
        let endpoint (term : Expr) : M Value := do
          try recognize state term sourceCategory #[receiver]
          catch error =>
            if (CasCatalogue.Exception.interpretationKind error) == .invalid then
              pure (.object term sourceCategory none none none)
            else throw error
        let X ← endpoint source
        let Y ← endpoint target
        Trace.record (← read).trace hom (.arrowProjection handle)
        return .morphism hom source target sourceCategory (some (X, Y))
  -- An invariant of the object (`R.dimension()`): a registered family of elements `1 → T`
  -- indexed by the object.
  if !state.methods.any (·.name == name) && !state.properties.any (·.name == name) then
    if state.morphisms.any (·.name == name) then
      return ← invariantNamed state name receiver
  let isProperty := state.properties.any (·.name == name) && !state.methods.any (·.name == name)
  if isProperty then return .answer (← Semantic.property name handle category (← read).trace)
  let (value, target) ← Semantic.method name handle category (← read).trace
  return .object value target none none none

/-- Full structured arguments supplied by an accepted named morphism's public field
presentation. Only registered morphism heads are expanded; mathematical value heads are
not inspected. Equivalent named witnesses are compared as complete structures, never as
carriers, and all such witnesses are retained. -/
partial def suppliedFieldWitnesses (state : RegistryState) (entry : MorphismEntry)
    (semantic : Expr) : M (Array Value) := do
  let fields := state.objects.flatMap fun object =>
    #[object.constants, object.application, object.generator, object.inclusion].filterMap id
  let mut current := semantic
  let mut visited : Array Name := #[]
  while true do
    -- Trace/cache addresses are transparent wrappers around the same complete
    -- supplied declaration. Inspect its public field without replacing the
    -- original addressed map or dropping the selected primitive identity.
    current := current.consumeMData
    while current.isAppOfArity ``id 2 || current.isAppOfArity ``Trace.operationResult 3 do
      current := current.appArg!.consumeMData
    let some head := current.getAppFn.constName? | return #[]
    if fields.contains head then
      let infos ← forallTelescopeReducing (← getConstInfo head).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      unless infos.size == current.getAppNumArgs do
        throwStratum .invalid "the supplied public field is not fully applied"
      let mut witnesses := #[]
      for (actual, info) in current.getAppArgs.zip infos do
        unless info.isExplicit do continue
        if (← isType actual) || (← isProof actual) then continue
        let actualType ← inferType actual
        let mut categories := #[]
        for category in state.categories do
          if category.id == CategoryId.sets then continue
          if ← parameterCompatible do
              let type ← mkAppHere ``CategoryTheory.Bundled.α #[← instantiateFresh category.declaration]
              withTransparency .all <| isDefEq actualType type then
            categories := categories.push category
        if categories.isEmpty then continue
        let #[category] := categories
          | throwSemanticAmbiguity "a supplied public field argument has several complete categories"
        let mut views := #[]
        for object in state.objects do
          unless object.category == category.id do continue
          let named? ← parameterTrial do
            let named ← instantiateFresh object.declaration
            unless ← withTransparency .all <| isDefEq (← inferType named) actualType do return none
            unless ← withTransparency .all <| isDefEq named actual do return none
            let named ← instantiateMVars named
            if named.hasMVar || named.hasLevelMVar then return none
            return some named
          if let some named := named? then
            views := views.push (← recognize state named category)
        if views.isEmpty then
          witnesses := witnesses.push (.object actual category none none none)
        else
          let evidence ← coalesceSelectedParameterViews actualType actual views
          let (_, _, _, presentations, _) := evidence
          Trace.record (← read).trace actual (.parameterEquivalence actualType actual presentations)
          witnesses := witnesses.push (.object actual category none none (some evidence))
      return witnesses
    unless head == entry.declaration || state.morphisms.any (·.declaration == head) do
      return #[]
    if visited.contains head then
      throwStratum .invalid "a registered morphism's head expansion is cyclic"
    let some expanded ← unfoldDefinition? current | return #[]
    unless ← withTransparency .all <| isDefEq expanded semantic do
      throwStratum .invalid "the public field presentation changed its supplied map"
    visited := visited.push head
    current := expanded
  return #[]

/-- The identifier `name` applied to `args`: `id`, or the unique registered object, morphism family or
(co)limit shape of that name. -/
partial def named (scope : Scope) (name : String) (args : Array Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let state ← registryState
  if name == "generator" then
    let #[objectSyntax] := args
      | throwStratum .invalid m!"`generator` takes one registered object"
    return ← generatorOf (← eval scope objectSyntax category?)
  if name == "reindex" || name == "cartesian" then
    let #[objectSyntax, morphismSyntax] := args
      | throwStratum .invalid m!"`{name}` takes a complete fibre value and a base morphism"
    return ← reindexValue (← eval scope objectSyntax category?) (← eval scope morphismSyntax)
      (name == "cartesian")
  if name == "id" then
    let #[x] := args | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let X ← eval scope x category?
    let a ← semanticObject X
    let context ← objectContext X
    let hom ← elabTermAndSynthesize
      (← `(CategoryTheory.CategoryStruct.id $(← exprToSyntax a)))
      (some (← CategoryContext.hom context a a))
    let node := match CategoryContext.named? state context.expression with
      | some category => Node.morphismIdentity category.id a
      | none => Node.contextualIdentity context a
    Trace.record (← read).trace hom node
    return ← morphismInContext hom a a context (X, X)
  -- `Mat₂(ℚ)`: a subscript is the leading numeral parameter.
  if let some (base, k) := subscripted? name then
    if state.objects.any (·.name == base) && !state.objects.any (·.name == name) then
      return ← object state base (#[.nat k] ++ (← args.mapM (eval scope · none))) category?
  let inScope (c : CategoryId) := category?.all (c == ·.id)
  let objects := objectBindings state name category?
  let morphisms := state.morphisms.filter fun m => m.name == name && inScope m.category
  let shapes := state.limits.filter (·.shape == name)
  let mut actions : Array (M Value) := #[]
  for entry in state.constructions.filter (·.name == name) do
    actions := actions.push (do
      let result ← directConstruction scope entry args
      if let some expected := category? then
        let .object _ actual .. := result | unreachable!
        unless actual.id == expected.id do
          throwStratum .invalid "the construction has a different selected result category"
      return result)
  let mut objectCategories : Array CategoryId := #[]
  for entry in objects do
    unless objectCategories.contains entry.category do
      if let some category := state.categories.find? (·.id == entry.category) then
        -- Reject a partial constructor whose declared type cannot be an object
        -- before evaluating its operands. No argument value participates here.
        let applicable ← parameterTrial do
          let declaration ← mkConstWithFreshMVarLevels entry.declaration
          let (parameters, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
          let mut supplied := #[]
          let mut explicit := 0
          for (parameter, info) in parameters.zip infos do
            if info.isExplicit then
              if explicit == args.size then break
              explicit := explicit + 1
            supplied := supplied.push parameter
          unless explicit == args.size do return false
          let partialApplication := mkAppN declaration supplied
          let family ← instantiateFresh category.declaration
          let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
          isDefEq (← inferType partialApplication) expected
        unless applicable do continue
        objectCategories := objectCategories.push entry.category
        actions := actions.push (do
          object state name (← args.mapM (eval scope · none)) (some category))
  for entry in morphisms do
    actions := actions.push (morphism state entry args scope)
  if args.size == 1 && state.methods.any (·.name == name) then
    actions := actions.push (do
      let receiver ← eval scope args[0]! category?
      match receiver with
      | .object .. | .morphism .. => call scope args[0]! name category?
      | _ => throwStratum .invalid m!"a registered method requires its typed receiver")
  let mut orientations : Array Bool := #[]
  for row in shapes do
    unless orientations.contains row.colimit do
      orientations := orientations.push row.colimit
      actions := actions.push (do
        let values ← args.mapM (eval scope · category?)
        let category ← match (values[0]? : Option Value) with
          | some (.object _ c _ _ _) | some (.morphism _ _ _ c _) => pure c
          | _ => throwStratum .invalid m!"a {name} is of objects or morphisms"
        match state.resolveLimitDetailed category.id name row.colimit with
        | .error error => liftM (Semantic.limitResolutionFailure error)
        | .ok _ => pure ()
        let presentation ← limitIn row.colimit name (← standardDiagram name values) category
        let apex ← apexOf row.colimit presentation
        Trace.alias (← read).trace presentation apex
        let source := Value.object apex category none none none
        return .object apex category none none (some (values, source, #[], #[], #[])))
  -- One declared signature has no competing reading. Execute its full typed
  -- action once; speculative execution is needed only to select among rows.
  if let #[action] := actions then return ← action
  let mut compatible : Array (M Value) := #[]
  for action in actions do
    if ← parameterCompatible (do discard action; pure true) then
      compatible := compatible.push action
  match compatible.toList with
  | [action] => action
  | [] => throwStratum .invalid m!"no registered signature named {name} applies to these arguments"
  | _ => throwSemanticAmbiguity m!"several complete registered signatures named {name} apply to these arguments"

/-- The registered morphism family `entry` at `args`: its leading arguments are its numeral
parameters, and the rest are elements it is applied to (`gcd(84, 30)`, `rev(3, 0)`). Unapplied, it
is a morphism between the named objects it relates, or an element if its source is `1`
(`i : 1 → ℂ`). -/
partial def morphism (state : RegistryState) (entry : MorphismEntry) (args : Array Syntax)
    (scope : Scope) : M Value := do
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the morphism {entry.name} has an unregistered category"
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  -- A family over sets (`d` over the rings `R`): its parameters come from its operands.
  let overSets ← forallTelescopeReducing (← inferType declaration) fun xs _ =>
    xs.anyM fun x => return !(← inferType x).isConstOf ``Nat
  if overSets then
    let (declarationArgs, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let explicit := (declarationArgs.zip infos).filterMap fun (arg, info) =>
      if info.isExplicit then some arg else none
    let mut parameters : Array Value := #[]
    let mut firstOperand : Option Value := none
    for parameter in explicit do
      let some argumentSyntax := args[parameters.size]? | break
      let value ← eval scope argumentSyntax
      let expected ← instantiateMVars (← inferType parameter)
      -- A parameter whose declared type is the object type of a registered category can only
      -- be supplied by an object value.  In particular, an operand such as `F : R[x]` must not
      -- be speculatively transported through every structured route merely because it is the
      -- first written argument of a family such as `d : ∀ R, R[x] ⟶ Ω¹_R`.
      -- Ordinary data types can themselves carry categories (for example from
      -- an order). Only an actual registered category's object schema identifies
      -- a bundled-object parameter; a typeclass instance is not such a schema.
      let expectsObject ← if expected.hasExprMVar then pure false else
        state.categories.anyM fun registered => parameterTrial do
          let carrier ← categoryCarrierInstance registered
          withTransparency .all <| isDefEq expected carrier
      if expectsObject && !(value matches .object ..) then
        firstOperand := some value
        break
      unless ← parameterCompatible (do
          let term ← typedParameter expected value
          isDefEq parameter term) do
        firstOperand := some value
        break
      let term ← typedParameter expected value
      discard <| isDefEq parameter term
      parameters := parameters.push value
    -- The first rejected parameter is exactly the first operand, in the same evaluation
    -- context. Retain its value and trace rather than reading it a second time.
    let mut elements := #[]
    if let some value := firstOperand then elements := elements.push value
    elements := elements ++ (← (args.extract (parameters.size + elements.size) args.size).mapM
      (eval scope · none))
    return ← applyFamily entry.declaration category
      elements
      (parameters := parameters) (callableAddress := some entry.id.raw)
  let arity ← forallTelescopeReducing (← inferType declaration) fun xs _ => pure xs.size
  unless arity ≤ args.size do
    throwStratum .invalid m!"{entry.name} takes {arity} parameters"
  let params ← numeralTerms entry.name (← (args.extract 0 arity).mapM (eval scope · none))
  let family ← `($(mkCIdent entry.declaration) $params*)
  let semantic ← instantiateMVars (← elabTermAndSynthesize family none)
  if semantic.hasMVar then
    throwStratum .invalid m!"the morphism parameters of {entry.name} are not determined"
  unless ← isTypeCorrect semantic do
    throwStratum .invalid m!"a morphism parameter is outside its declared dependent signature"
  let semantic ← retainNamedMorphism entry semantic
  let type ← instantiateMVars (← inferType semantic)
  let some (source, target) := match type.getAppFn.constName?, type.getAppArgs with
      | some ``Quiver.Hom, #[_, _, x, y] => some (x, y)
      | _, _ => none
    | throwStratum .invalid m!"{entry.name} is not a family of morphisms"
  let applied := args.extract arity args.size
  let endpoints ← if applied.size == 2 then
    match (← whnfR source).getAppFn.constName?, (← whnfR source).getAppArgs with
    | some ``Prod, #[x, y] => pure #[x, y, target]
    | _, _ => pure #[source, target]
  else pure #[source, target]
  let declaredEndpoint := fun (endpoint : Expr) => state.objects.any fun object =>
    object.category == category.id && some object.declaration == endpoint.getAppFn.constName?
  -- Existing named endpoint readings keep their operation trees unchanged. A raw endpoint
  -- receives context only from full objects already supplied in this accepted map's body.
  let known ← if endpoints.all declaredEndpoint then pure #[]
    else suppliedFieldWitnesses state entry semantic
  let targetValue ← declaredEndpointObject target category known
  if !applied.isEmpty then
    -- The sets of the operands: the factors of a product source, or the source.
    let sources ← if applied.size == 2 then
      match (← whnfR source).getAppFn.constName?, (← whnfR source).getAppArgs with
      | some ``Prod, #[x, y] => pure #[x, y]
      | _, _ => pure #[source]
    else pure #[source]
    unless sources.size == applied.size do
      throwStratum .invalid m!"{entry.name} is applied to {sources.size} elements"
    let elements ← (sources.zip applied).mapM fun (set, arg) => do
      let X ← recognize state set category known
      toElement (← eval scope arg none (some X)) X
    let numerals ← (args.extract 0 arity).mapM fun parameterSyntax => do
      let .nat n ← eval scope parameterSyntax
        | throwStratum .invalid m!"a leading family parameter is a numeral"
      return n
    return ← applyFamily entry.declaration category elements (some targetValue) (numerals := numerals)
      (callableAddress := some entry.id.raw)
  let .object b _ _ _ _ := targetValue
    | throwStratum .invalid m!"the target of {entry.name} is not an object"
  let sourceValue ← declaredEndpointObject source category known
  let .object a _ _ _ _ := sourceValue
    | throwStratum .invalid m!"the source of {entry.name} is not an object"
  let hom ← homIn (← quoteExpr semantic) a b category
  let hom ← retainNamedMorphism entry hom
  if category.id == CategoryId.sets then
    let one ← globalPointSource
    if ← isDefEq a one then return .element (← staged hom) targetValue
    if let some comparison ← operationPointComparison a then
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, hom]
      unless ← isTypeCorrect composite do
        throwStratum .invalid m!"the declared terminal comparison does not form this point"
      Trace.record (← read).trace composite
        (.morphismComposition category.id comparison hom one a b)
      return .element (← staged composite) targetValue
  return .morphism hom a b category (some (sourceValue, targetValue))

/-- Merge already constructed selected views at one independently fixed complete parameter.
The caller stores *all* returned original views in its provenance, not only the representative.
Existing route classification occurs when each selectedView is constructed, before this helper. -/
partial def coalesceSelectedParameterViews (expected actual : Expr)
    (views : Array Value) : M
    (Array Value × Value × Array EdgeRef × Array ParameterPresentation × Array (EdgeRef × Array Expr)) := do
  unless !actual.hasMVar && (← isDefEq (← inferType actual) expected) &&
      (← isTypeCorrect actual) do
    throwStratum .invalid m!"the selected dependent parameter is not completely typed"
  let state ← registryState
  let mut checked : Array (Value × Value × Array EdgeRef × Array ParameterPresentation × Array (EdgeRef × Array Expr)) := #[]
  for selectedView in views do
    let .object handle category _ _ data := selectedView
      | throwStratum .invalid m!"a selected parameter view is an object"
    unless !handle.hasMVar && (← isTypeCorrect handle) &&
        (← isDefEq (← inferType handle) expected) &&
        (← withTransparency .all <| isDefEq handle actual) do
      throwSemanticAmbiguity m!"distinct full structures supply a declaration parameter"
    let (source, route, alternatives, applications) := match data with
      | some (_, source, route, alternatives, applications) =>
          (source, route, alternatives, applications)
      | none => (selectedView, #[], #[], #[])
    let .object receiver sourceCategory sourceOrigin .. := source
      | throwStratum .invalid m!"a retained parameter source is not an object"
    unless !receiver.hasMVar && (← isTypeCorrect receiver) &&
        !(applications.any fun (_, args) => args.any (·.hasMVar)) do
      throwStratum .invalid m!"a retained selected source or action is not fully instantiated"
    let (sourceImage, fullApplications) ← retainedActions state receiver route applications
    unless ← withTransparency .all <| isDefEq sourceImage handle do
      throwStratum .invalid m!"the retained source action differs from its complete selected image"
    let mut alternatives := alternatives
    if alternatives.isEmpty then
      if let some (entry, values) := sourceOrigin then
        let named ← Semantic.object entry (← typedParamTerms entry.declaration values) none
        unless !named.hasMVar && !named.hasLevelMVar && (← isTypeCorrect named) &&
            (← isDefEq (← inferType named) (← inferType receiver)) &&
            (← withTransparency .all <| isDefEq named receiver) do
          throwStratum .invalid m!"the named source does not give its full retained object"
        let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
          xs.mapM (·.fvarId!.getBinderInfo)
        let mut application := named.consumeMData
        while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
        unless application.getAppFn.constName? == some entry.declaration do
          throwStratum .invalid m!"a retained source differs from its registered declaration"
        let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
          if info.isExplicit then some arg else none
        let identity ← mkEqRefl actual
        unless (← isTypeCorrect identity) &&
            (← withTransparency .all <| isDefEq (← inferType identity) (← mkEq handle actual)) do
          throwStratum .invalid m!"a full selected structure identity failed kernel conversion"
        let (carrierRoute, identifications) := (declaredCarrierRoute state entry).getD (#[], #[])
        alternatives := #[
          { source := entry.id
            sourceCategory := sourceCategory.id
            targetCategory := category.id
            params := params
            route := route
            carrierRoute := carrierRoute
            identifications := identifications
            object := receiver
            image := handle
            applications := fullApplications
            identity := identity }]
    checked := checked.push (selectedView, source, route, alternatives, applications)
  unless !checked.isEmpty do
    throwStratum .invalid m!"the parameter has no retained selected sources"
  -- Only serialization order is canonicalized, after every full image was checked.
  let ordered := checked.qsort fun left right =>
    reprStr (left.1.declarations, left.1.terms) < reprStr (right.1.declarations, right.1.terms)
  let some (_, source, route, _, applications) := ordered[0]? | unreachable!
  let alternatives := ordered.flatMap fun (_, _, _, alternatives, _) => alternatives
  return (ordered.map (·.1), source, route, alternatives, applications)

/-- Retain complete structured views supplied by the caller at one fixed parameter.
No object is selected from a carrier, and all checked source presentations are preserved. -/
partial def selectedParameterFromWitnesses (state : RegistryState) (actual : Expr)
    (parameterCategory : NamedCategoryEntry) (known : Array Value) : M (Option Value) := do
  let mut witnesses : Array Value := #[]
  let sourceValues := known.flatMap sourceParameterValues
  let selected := sourceValues.filter fun
    | .object _ candidateCategory origin selected _ =>
        candidateCategory.id != CategoryId.sets || selected.isSome || origin.isSome
    | _ => false
  for candidate in (if selected.isEmpty then sourceValues else selected) do
    if ← parameterCompatible (do
        let image ← typedParameter (← inferType actual) candidate
        isDefEq image actual) then
      unless witnesses.any (fun existing =>
          existing.declarations == candidate.declarations && existing.terms == candidate.terms) do
        witnesses := witnesses.push candidate
  if witnesses.isEmpty then return none
  let views ← witnesses.mapM fun original => do
    let chosen := match original with
      | .object _ _ _ (some selected) _ => selected
      | _ => original
    if let .object handle chosenCategory origin selected _ := chosen then
      if chosenCategory.id == parameterCategory.id &&
          (← isDefEq (← inferType handle) (← inferType actual)) &&
          (← withTransparency .all <| isDefEq handle actual) then
        return Value.object handle chosenCategory origin selected
          (some (#[original], chosen, #[], #[], #[]))
    structuredParameterView original actual parameterCategory
  let evidence ← coalesceSelectedParameterViews (← inferType actual) actual views
  let (_, _, _, alternatives, _) := evidence
  unless alternatives.isEmpty do
    Trace.record (← read).trace actual
      (.parameterEquivalence (← inferType actual) actual alternatives)
  return some (.object actual parameterCategory none none (some evidence))

/-- Recognize a retained complete object or its actual registered declaration application.
A carrier expression alone does not select a named presentation. -/
partial def recognize (state : RegistryState) (x : Expr) (category : NamedCategoryEntry)
    (known : Array Value := #[]) (fixedParameters : Array Expr := #[])
    (expandParameters : Bool := true) :
    M Value := do
  if !x.hasMVar then
    let mut matchedValues : Array Value := #[]
    let mut supplied := known
    let mut position := 0
    while position < supplied.size do
      let candidate := supplied[position]!
      position := position + 1
      -- A supplied constructor retains its actual declared parameters. They
      -- are witnesses for result endpoints, not structures guessed from carriers.
      if expandParameters then
        if let .object _ _ (some (_, parameters)) _ _ := candidate then
          supplied := supplied ++ parameters
      let candidate ← try
        match candidate with
        | .object .. => if category.id == CategoryId.sets then carrierObject candidate else pure candidate
        | _ => continue
      catch error =>
        if (CasCatalogue.Exception.interpretationKind error) == .invalid then continue else throw error
      let .object handle candidateCategory origin .. := candidate | continue
      unless candidateCategory.id == category.id do continue
      let declared := state.objects.filter (fun row =>
        row.category == category.id && some row.declaration == x.getAppFn.constName?)
      if !declared.isEmpty && !origin.any (fun (entry, _) => declared.any (·.id == entry.id)) then
        continue
      if ← parameterTrial (withTransparency .all <| isDefEq handle x) then
        if let some index := matchedValues.findIdx? (·.sameSelection candidate) then
          matchedValues := matchedValues.set! index
            (retainObjectContext matchedValues[index]! #[candidate])
          continue
        unless ← matchedValues.anyM (fun existing => parameterTrial do
            unless existing.declarations == candidate.declarations do return false
            let left := existing.terms
            let right := candidate.terms
            unless left.size == right.size do return false
            (left.zip right).allM fun (a, b) => withTransparency .all <| isDefEq a b) do
          matchedValues := matchedValues.push candidate
    if category.id != CategoryId.sets && matchedValues.size > 1 then
      -- The endpoint fixes a complete structured object, not its carrier.
      -- Retain every checked presentation of that same full object.
      let evidence ← coalesceSelectedParameterViews (← inferType x) x matchedValues
      let (_, _, _, alternatives, _) := evidence
      unless alternatives.isEmpty do
        Trace.record (← read).trace x
          (.parameterEquivalence (← inferType x) x alternatives)
      return .object x category none none (some evidence)
    if category.id == CategoryId.sets && matchedValues.size > 1 then
      -- A declared operation fixes complete structure parameters before its
      -- endpoints are read. Compare those full values, never just their carriers.
      -- Without that context, distinct selections remain ambiguous.
      let mut fixedViews : Array (Expr × NamedCategoryEntry × Array Value) := #[]
      for parameter in fixedParameters do
        if parameter.hasMVar || parameter.hasLevelMVar then continue
        let mut views := #[]
        let mut parameterCategory? : Option NamedCategoryEntry := none
        for candidate in matchedValues do
          let .object _ _ _ (some selected@(.object handle selectedCategory ..)) _ := candidate
            | continue
          if selectedCategory.id == CategoryId.sets then continue
          if ← parameterTrial (do
              withTransparency .all <|
                isDefEq (← inferType handle) (← inferType parameter) <&&>
                  isDefEq handle parameter) then
            if let some previousCategory := parameterCategory? then
              unless previousCategory.id == selectedCategory.id do
                throwSemanticAmbiguity m!"the fixed parameter has several selected categories"
            views := views.push selected
            parameterCategory? := some selectedCategory
        if let some parameterCategory := parameterCategory? then
          unless ← fixedViews.anyM (fun (previous, _, _) => parameterTrial do
              withTransparency .all <|
                isDefEq (← inferType previous) (← inferType parameter) <&&>
                  isDefEq previous parameter) do
            fixedViews := fixedViews.push (parameter, parameterCategory, views)
      if let #[(parameter, parameterCategory, views)] := fixedViews then
        let (originals, source, route, alternatives, applications) ←
          coalesceSelectedParameterViews (← inferType parameter) parameter views
        unless alternatives.isEmpty do
          Trace.record (← read).trace parameter
            (.parameterEquivalence (← inferType parameter) parameter alternatives)
        let selected := Value.object parameter parameterCategory none none
          (some (originals, source, route, alternatives, applications))
        let carrier ← carrierObject selected
        unless ← withTransparency .all <| isDefEq (← semanticObject carrier) x do
          throwStratum .invalid m!"the fixed structure parameter has a different endpoint"
        return carrier
    if category.id == CategoryId.sets && matchedValues.size > 1 then
      -- Reuse the checked forward carrier relation. A retained structural
      -- view is not a second selection when one supplied full source gives
      -- every view along its actual declared carrier route.
      let maximal ← matchedValues.filterM fun candidate => do
        let .object _ _ _ (some (.object _ selectedCategory ..)) _ := candidate
          | return false
        if selectedCategory.id == CategoryId.sets then return false
        matchedValues.allM fun other => identityCarrierView candidate other
      if let #[candidate] := maximal then return candidate
      if let some representative := maximal[0]? then
        let .object _ _ _ (some (.object actual selectedCategory ..)) _ := representative
          | unreachable!
        let mut views := #[]
        for candidate in maximal do
          let .object _ _ _ (some selected@(.object handle candidateCategory ..)) _ := candidate
            | unreachable!
          unless candidateCategory.id == selectedCategory.id &&
              (← parameterTrial (withTransparency .all <|
                isDefEq (← inferType handle) (← inferType actual) <&&>
                  isDefEq handle actual)) do
            throwSemanticAmbiguity m!"distinct complete sources give this declared endpoint"
          views := views.push selected
        let evidence ← coalesceSelectedParameterViews (← inferType actual) actual views
        let (_, _, _, alternatives, _) := evidence
        unless alternatives.isEmpty do
          Trace.record (← read).trace actual
            (.parameterEquivalence (← inferType actual) actual alternatives)
        let carrier ← carrierObject (.object actual selectedCategory none none (some evidence))
        unless ← withTransparency .all <| isDefEq (← semanticObject carrier) x do
          throwStratum .invalid m!"the common full source has a different endpoint"
        return carrier
    match matchedValues.toList with
    | [candidate] => return candidate
    | [] => pure ()
    | _ => throwSemanticAmbiguity m!"several complete selected values give this declared endpoint"
  let mut found : Array (ObjectEntry × Array Expr) := #[]
  -- Identity by declaration (b0-selected-structure): reducible aliases cannot recover an
  -- object's identity from its carrier. In particular, a transparent Vec alias must not
  -- win over the opaque Maps declaration on their shared function carrier.
  let head := (← instantiateMVars x).getAppFn.constName?
  let declared := state.objects.filter fun e => e.category == category.id && some e.declaration == head
  for entry in declared do
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    let (args, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let params? ← (withoutModifyingState do
      let actualArgs := x.getAppArgs
      unless actualArgs.size == args.size do return none
      for (parameter, actual) in args.zip actualArgs do
        unless ← isDefEq (← inferType parameter) (← inferType actual) <&&>
            isDefEq parameter actual do return none
      unless ← isTypeCorrect (← instantiateMVars (mkAppN declaration args)) do return none
      let explicit := (args.zip infos).filterMap fun (a, i) => if i.isExplicit then some a else none
      return some (← explicit.mapM instantiateMVars) : MetaM _)
    if let some params := params? then
      if params.all (!·.hasMVar) then found := found.push (entry, params)
  let #[(entry, params)] := found
    | throwStratum .invalid m!"{x} is not a unique registered object of {category.name}"
  recognizeObjectApplication state entry category params known fixedParameters

/-- Reconstruct the dependent parameters of one already selected object row.
The row identity is carried through construction; declaration aliases do not
trigger a second name/head lookup or replace that independent selection. -/
partial def recognizeObjectApplication (state : RegistryState) (entry : ObjectEntry)
    (category : NamedCategoryEntry) (params : Array Expr)
    (known : Array Value := #[]) (fixedParameters : Array Expr := #[]) : M Value := do
  unless entry.category == category.id do
    throwStratum .invalid "the selected object application changed its registered category"
  -- Its parameters: numerals, or sets (`𝒫(ℤ[x])`), recognized in turn.
  let values ← params.mapM fun p => do
    if let some n ← (Meta.evalNat p).run then return Value.nat n
    if let some (source, target) := homEnds? (← inferType p) then
      let sourceValue ← recognize state source category known fixedParameters
      let targetValue ← recognize state target category known fixedParameters
      let terminal ← semanticObject (← oneObject)
      if ← parameterTrial (isDefEq source terminal) then
        return Value.element p targetValue
      return Value.morphism p source target category (some (sourceValue, targetValue))
    let mut categories := #[]
    for candidate in state.categories do
      let applicable ← parameterCompatible do
        let family ← instantiateFresh candidate.declaration
        let objectType ← mkAppM ``CategoryTheory.Bundled.α #[family]
        isDefEq (← inferType p) objectType
      if applicable then categories := categories.push candidate
    let parameterCategory ← match categories with
      | #[candidate] => pure candidate
      | #[] => throwStratum .invalid m!"a parameter of {entry.name} has no registered category"
      | _ => throwSemanticAmbiguity m!"a parameter of {entry.name} has several registered categories"
    -- A registered declaration may own an exact bundled parameter without giving it
    -- a separate named-object row. Retain that selected value rather than replacing
    -- it with a carrier or guessing a named refinement.
    if let some recognized ← optionalReading
        (recognize state p parameterCategory known fixedParameters) then
      pure recognized
    else
      unless ← isTypeCorrect p do
        throwStratum .invalid m!"a registered object's structure parameter is not typed"
      if let some selected ← selectedParameterFromWitnesses state p parameterCategory known then
        return selected
      else
        -- A declared result can build a named object from parameters already fixed by its
        -- actual operands (`Vec(K,n)` inside `𝒫(Fin n → K)`). This is constructor provenance,
        -- not recovery of a parameter-free alias from a coincident carrier.
        let mut constructed : Array (ObjectEntry × Array Value) := #[]
        let constructorSources := known.flatMap fun value => match value with
          | .object _ _ (some (_, parameters)) _ _ => parameters
          | _ => #[]
        let mut pointTargetHeads : Array Name := #[]
        for row in state.morphisms do
          unless row.category == parameterCategory.id do continue
          let family ← mkConstWithFreshMVarLevels row.declaration
          let (_, _, familyType) ← forallMetaTelescopeReducing (← inferType family)
          let some (_, familyTarget) := homEnds? familyType | continue
          if let some head := familyTarget.getAppFn.constName? then
            unless pointTargetHeads.contains head do pointTargetHeads := pointTargetHeads.push head
        for candidateEntry in state.objects do
          unless candidateEntry.category == parameterCategory.id do continue
          unless pointTargetHeads.contains candidateEntry.declaration do continue
          let declaration ← mkConstWithFreshMVarLevels candidateEntry.declaration
          let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
          let explicit := (arguments.zip infos).filterMap fun (argument, info) =>
            if info.isExplicit then some argument else none
          if explicit.isEmpty then continue
          let rec search (slot : Nat) (chosen : Array Value) : M (Array (Array Value)) := do
            if slot == explicit.size then
              let terms ← typedParamTerms candidateEntry.declaration chosen
              let handle ← Semantic.object candidateEntry terms none
              unless ← withTransparency .all <| isDefEq handle p do return #[]
              return #[chosen]
            let mut results : Array (Array Value) := #[]
            for source in constructorSources do
              let branch ← try
                parameterTrial do
                  let expected ← instantiateMVars (← inferType explicit[slot]!)
                  let actual ← typedParameter expected source
                  unless ← isDefEq explicit[slot]! actual do return #[]
                  search (slot + 1) (chosen.push source)
              catch error =>
                if CasCatalogue.Exception.interpretationKind error == .invalid then pure #[]
                else throw error
              results := results ++ branch
            return results
          for chosen in ← search 0 #[] do
            let duplicate ← constructed.anyM fun (entry, values) => parameterTrial do
              unless entry.id == candidateEntry.id do return false
              let existing ← Semantic.object entry
                (← typedParamTerms entry.declaration values) none
              let candidate ← Semantic.object candidateEntry
                (← typedParamTerms candidateEntry.declaration chosen) none
              withTransparency .all <| isDefEq existing candidate
            unless duplicate do
              constructed := constructed.push (candidateEntry, chosen)
        match constructed.toList with
        | [(constructedEntry, values)] =>
            let terms ← typedParamTerms constructedEntry.declaration values
            let handle ← Semantic.object constructedEntry terms (← read).trace
            unless ← withTransparency .all <| isDefEq handle p do
              throwStratum .invalid m!"the retained constructor does not give this result parameter"
            Trace.alias (← read).trace handle p
            pure (.object p parameterCategory (some (constructedEntry, values)) none none)
        | [] => pure (.object p parameterCategory none none none)
        | _ => throwSemanticAmbiguity m!"several retained constructors give this result parameter: \
            {String.intercalate ", " (constructed.toList.map (·.1.name))}"
  registeredObject state entry values

/-- The named set supplied by the exact registered refinement of a structured object.
The structured value remains the family's parameter; this viewData stages its elements. -/
partial def carrierObject (value : Value) : M Value := do
  if let .derivedObject handle context _ := value then
    let state ← registryState
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwStratum .invalid "the registered set category is absent"
    let routes ← routesBetween state context.expression sets.expression
    let classes :=
      letI : Inhabited Route :=
        ⟨{ source := context.expression, target := sets.expression, steps := #[] }⟩
      state.classify routes (fun _ => sets.id.raw) (fun route => route)
    let #[cls] := classes
      | throwSemanticAmbiguity "the derived object has no unique accepted carrier route"
    unless cls.ambiguities.isEmpty do
      throwSemanticAmbiguity "the derived carrier route has unresolved accepted comparisons"
    discard <| Semantic.validateRouteComparisons state cls.comparisonWitnesses (some handle)
    let #[route] := cls.sources
      | throwSemanticAmbiguity "the derived object has several directed carrier routes"
    let (image, applications, targetContext) ← if route.refs.isEmpty then
      pure (handle, #[], context)
    else do
      let (action, applications) ← Semantic.routeFunctorWithApplications state route.refs
      let image ← Semantic.objOf action handle
      let (sourceBundle, targetBundle) ← functorCategoryBundles action
      unless ← withTransparency .all <| isDefEq sourceBundle context.bundle do
        throwStratum .invalid "the carrier route changed its complete selected source category"
      pure (image, applications, { expression := sets.expression, bundle := targetBundle })
    let image ← instantiateMVars image
    let applications ← applications.mapM instantiateMVars
    let targetContext := { targetContext with bundle := (← instantiateMVars targetContext.bundle) }
    unless image == handle do
      Trace.record (← read).trace image
        (.contextualRoute context targetContext route.refs applications handle false)
    return retainObjectContext (.object image sets none none none) #[value]
  let .object handle category origin selected viewData := value
    | throwStratum .invalid m!"a carrier belongs to a selected structured object"
  let state ← registryState
  if category.id == CategoryId.sets then
    -- An anonymous parameter may already carry the exact source of its declared carrier.
    -- Reuse that forward construction; do not recover a name by matching bare types.
    if origin.isNone && selected.isNone then
      if let some (_, source, route, _, arguments) := viewData then
        if (← retainedCarrierRoute state source) == some route then
          let .object receiver .. := source | unreachable!
          let (image, _) ← retainedActions state receiver route arguments
          unless ← withTransparency .all <| isDefEq image handle do
            throwStratum .invalid m!"the supplied carrier differs from its actual source action"
          let sourceCarrier ← carrierObject source
          let .object sourceHandle _ sourceOrigin sourceSelected _ := sourceCarrier
            | unreachable!
          unless ← withTransparency .all <| isDefEq sourceHandle handle do
            throwStratum .invalid m!"the supplied source does not have this declared carrier"
          return .object handle category sourceOrigin sourceSelected viewData
    return value
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwStratum .invalid m!"no registered category of sets"
  let family ← instantiateFresh sets.declaration
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
  let declaredRoute ← retainedCarrierRoute state value
  let image ← match declaredRoute with
    | none => transportedStructure expected value (some sets.id)
    | some route => do
        let (image, _) ← checkedRouteAction state category.id sets.id route handle expected
        pure image
  let carrierOrigin ← match origin with
    | some (entry, parameters) => do
        -- A named structured object need not separately name its carrier. Its actual
        -- registered forgetful action still supplies that carrier and retains the source.
        if (declaredCarrierRoute state entry).isNone then pure none else do
          let base ← setOf state entry
          let baseObject ← Semantic.object base (← typedParamTerms base.declaration parameters)
          -- A nonidentity declared comparison is retained by the structured source; it does
          -- not make the actual forgotten carrier definitionally that named set.
          if ← isDefEq image baseObject then pure (some (base, parameters)) else pure none
    | none => match viewData with
      | none => pure none
      | some (_, source, route, _, arguments) => do
          let structural : EdgeRef → Bool := fun
            | .functor id => (state.functors.find? (·.id == id)).any (·.structural)
            | .classifierForget _ => true
            | .constructMap _ _ => false
          if !route.all structural then pure none else do
            let .object receiver .. := source | unreachable!
            let some carrierRoute ← retainedCarrierRoute state source | pure none
            if route.size > carrierRoute.size ||
                carrierRoute.extract 0 route.size != route then pure none else do
              let (exactImage, _) ← retainedActions state receiver route arguments
              unless ← isDefEq exactImage handle do
                throwStratum .invalid m!"the source route does not retain this complete structure"
              let suffix := carrierRoute.extract route.size carrierRoute.size
              let exactCarrier ← if suffix.isEmpty then pure handle else
                Semantic.objOf (← Semantic.routeFunctor state suffix) handle
              let sourceCarrier ← carrierObject source
              let .object sourceHandle _ sourceCarrierOrigin .. := sourceCarrier | unreachable!
              unless ← isDefEq exactCarrier image <&&> isDefEq exactCarrier sourceHandle do
                throwStratum .invalid m!"the declared carrier identification does not give this endpoint"
              pure sourceCarrierOrigin
  return .object image sets carrierOrigin (some value) viewData

/-- Constrain an ordered dependent telescope from a complete selected receiver.
Only earlier structured object parameters are expanded; their carrier and every structure field
must be fixed by the actual receiver before any instance synthesis is permitted. -/
partial def bindSelectedReceiver (explicit : Array Expr) (slot : Nat) (receiver : Value)
    (demandedCategory : Option CategoryId := none) : M Bool := do
  let some parameter := explicit[slot]? | return false
  let selected := match receiver with
    | .object _ _ _ (some selected) _ => selected
    | _ => receiver
  let .object actual category origin .. := selected | return false
  if actual.hasMVar then return false
  if category.id == CategoryId.sets then
    -- Any object binder may use the complete package supplied by a named declared
    -- refinement. Its dependent type constrains earlier parameters; a bare carrier
    -- supplies no such package.
    if origin.isNone then return false
    let expected ← instantiateMVars (← inferType parameter)
    let argument ← typedParameter expected selected
    unless !argument.hasMVar && (← isTypeCorrect argument) do return false
    return ← isDefEq parameter argument
  let mut expanded : Array Expr := #[]
  for earlier in explicit.extract 0 slot do
    let earlier ← instantiateMVars earlier
    unless earlier.isMVar do continue
    let expected ← whnfR (← inferType earlier)
    let some typeName := expected.getAppFn.constName? | continue
    unless isStructure (← getEnv) typeName do continue
    let .inductInfo info ← getConstInfo typeName | continue
    let [constructor] := info.ctors | continue
    let constant ← mkConstWithFreshMVarLevels constructor
    let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constant)
    unless ← isDefEq result expected do return false
    let whole := mkAppN constant fields
    unless ← isDefEq earlier whole do return false
    expanded := expanded.push whole
  let expected ← instantiateMVars (← inferType parameter)
  let argument ← if ← isDefEq (← inferType actual) expected then pure actual else
    match demandedCategory with
    | some category => transportedStructure expected selected (some category)
    | none => typedParameter expected selected
  unless ← isDefEq parameter argument do return false
  for whole in expanded do
    let whole ← instantiateMVars whole
    if whole.hasMVar || !(← isTypeCorrect whole) then return false
  return true

/-- The registered morphism family named `name`, applied to elements (see `applyFamily`). -/
partial def applyNamed (state : RegistryState) (name : String) (elements : Array Value)
    (target? : Option Value := none) : M Value := do
  let rows := state.morphisms.filter (·.name == name)
  let entry ← match rows with
    | #[entry] => pure entry
    | _ => do
        let mut candidates := #[]
        for entry in rows do
          let some category := state.categories.find? (·.id == entry.category) | continue
          if ← parameterCompatible (do
              discard <| applyFamily entry.declaration category elements target? (callableAddress := some entry.id.raw)
              pure true) then candidates := candidates.push entry
        match candidates with
        | #[entry] => pure entry
        | #[] => throwStratum .invalid m!"no registered function named {name} takes these elements"
        | _ => throwSemanticAmbiguity m!"several complete registered functions named {name} take these elements"
  let some category := state.categories.find? (·.id == entry.category) | unreachable!
  applyFamily entry.declaration category elements target? (callableAddress := some entry.id.raw)

/-- Select a registered structured parameter through its actual structured forgetful image. -/
partial def registeredStructuredParameter (expected : Expr) (operand : Value) : M (Option Expr) := do
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar || expected.isSort then return none
  let .object operandHandle operandCategory .. := operand | return none
  let state ← registryState
  let originalValues := sourceParameterValues operand
  -- The expected type fixes the possible owner categories before any constructor or route
  -- trial. Universe polymorphism is not an unknown object-category constructor.
  let mut owners : Array (NamedCategoryEntry × Array ObjectEntry) := #[]
  for sourceCategory in state.categories do
    unless ← parameterCategoryCompatible expected sourceCategory do continue
    let entries ← (state.objects.filter (·.category == sourceCategory.id)).filterM fun entry =>
      parameterCompatible do
        let constant ← mkConstWithFreshMVarLevels entry.declaration
        let (_, _, type) ← forallMetaTelescopeReducing (← inferType constant)
        isDefEq type expected
    unless entries.isEmpty do owners := owners.push (sourceCategory, entries)
  let mut candidates : Array (ObjectEntry × Expr × Array Expr) := #[]
  for targetCategory in state.categories do
    if targetCategory.id == CategoryId.sets then continue
    -- Only an already selected source or an explicitly declared refinement can supply
    -- this target structure. Unrelated categories need no route enumeration.
    let originals := originalValues.filter fun
      | .object _ originalCategory origin selected _ =>
          if originalCategory.id == CategoryId.sets then
            selected.isNone && origin.any (fun (base, _) => state.objects.any fun row =>
              row.category == targetCategory.id && refinesObject state row base.id)
          else originalCategory.id == targetCategory.id
      | _ => false
    if originals.isEmpty then continue
    let mut routesByOwner : Array (NamedCategoryEntry × Array ObjectEntry × Array Route) := #[]
    for (sourceCategory, entries) in owners do
      if sourceCategory.id == targetCategory.id then continue
      let routes ← routesBetween state sourceCategory.expression targetCategory.expression
      unless routes.isEmpty do
        routesByOwner := routesByOwner.push (sourceCategory, entries, routes)
    if routesByOwner.isEmpty then continue
    -- Complete selected images depend on the actual operand and target category, not
    -- the constructor being tested. Compute each once, before the constructor trials.
    let mut images : Array Expr := #[]
    for original in originals do
      let actual? ← parameterTrial do
        let .object handle originalCategory _ _ _ := original | return none
        let family ← instantiateFresh targetCategory.declaration
        let targetType ← mkAppM ``CategoryTheory.Bundled.α #[family]
        let directType ← parameterTrial (isDefEq (← inferType handle) targetType)
        unless directType || originalCategory.id == CategoryId.sets do return none
        try
          let actual ← instantiateMVars (← typedParameter targetType original)
          if actual.hasMVar || actual.hasLevelMVar || !(← isTypeCorrect actual) then return none
          -- A coefficient in the provenance is relevant only if its accepted action
          -- reaches this exact operand, rather than merely sharing its carrier type.
          let endpoint ← if originalCategory.id == operandCategory.id then pure handle
            else do
              let endpointType ← inferType operandHandle
              transportedStructure endpointType original (some operandCategory.id)
          unless ← withTransparency .all <| isDefEq endpoint operandHandle do return none
          return some actual
        catch error =>
          if Exception.interpretationKind error == .invalid then return none else throw error
      let some actual := actual? | continue
      unless ← images.anyM (fun other => parameterTrial do
          withTransparency .all <| isDefEq other actual) do
        images := images.push actual
    for (sourceCategory, entries, routes) in routesByOwner do
      for entry in entries do
        for actual in images do
          for route in routes do
            let candidate? ← parameterTrial do
              try
                let constant ← mkConstWithFreshMVarLevels entry.declaration
                let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
                unless ← isDefEq type expected do return none
                let openObject := mkAppN constant args
                let image ← Semantic.objOf (← Semantic.routeFunctor state route.refs) openObject
                -- Infer ordered constructor parameters from the full structured image before
                -- demanding closure. A carrier alone never determines a missing structure.
                unless ← withTransparency .all <| isDefEq image actual do return none
                let mut inferredArrows := #[]
                for parameter in args do
                  let parameter ← instantiateMVars parameter
                  unless parameter.isMVar do continue
                  let some arrow ← registeredArrowParameter (← inferType parameter) | continue
                  unless ← isDefEq parameter arrow do return none
                  inferredArrows := inferredArrows.push arrow
                synthesizeInstances args infos
                let object ← instantiateMVars openObject
                unless !object.hasMVar && !object.hasLevelMVar && (← isTypeCorrect object) &&
                    (← withTransparency .all <| isDefEq (← inferType object) expected) do return none
                -- Recheck the closed candidate using the ordinary route classifier. The trial
                -- route cannot bypass competing routes or select its own comparison.
                let selected := Value.object object sourceCategory (some (entry, #[])) none none
                let checked ← transportedStructure (← inferType actual) selected (some targetCategory.id)
                unless ← withTransparency .all <| isDefEq checked actual do return none
                return some (object, inferredArrows)
              catch error =>
                if Exception.interpretationKind error == .invalid then return none else throw error
            if let some (candidate, arrows) := candidate? then
              unless ← candidates.anyM (fun (otherEntry, other, _) => parameterTrial do
                  return otherEntry.id == entry.id &&
                    (← withTransparency .all <| isDefEq other candidate)) do
                candidates := candidates.push (entry, candidate, arrows)
  let some (_, first, _) := candidates[0]? | return none
  for (_, object, _) in candidates do
    unless ← parameterTrial (withTransparency .all <| isDefEq object first) do
      throwSemanticAmbiguity m!"several registered structures have this exact selected structural image"
  -- Only the serialization representative is ordered, after complete structures agree.
  -- All declaration identities survive in the existing full-parameter equivalence record.
  let ordered := candidates.qsort fun left right => left.1.id.raw < right.1.id.raw
  let some (_, representative, _) := ordered[0]? | unreachable!
  let mut presentations : Array ParameterPresentation := #[]
  for (entry, object, arrows) in ordered do
    for arrow in arrows do
      let some recorded ← registeredArrowParameter (← inferType arrow)
        | throwError "an inferred constructor map lost its declared source"
      unless ← isDefEq recorded arrow do
        throwError "recording an inferred constructor map changed its selected value"
    unless ← Semantic.recordNamedObject object (← read).trace do
      throwError "the selected constructor lost its registered declaration"
    if ordered.size == 1 then continue
    let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
      xs.mapM (·.fvarId!.getBinderInfo)
    let params := (object.getAppArgs.zip infos).filterMap fun (arg, info) =>
      if info.isExplicit then some arg else none
    let identity ← mkEqRefl representative
    unless (← isTypeCorrect identity) &&
        (← withTransparency .all <| isDefEq (← inferType identity)
          (← mkEq object representative)) do
      throwError "the complete constructor equivalence failed kernel conversion"
    let (carrierRoute, identifications) := (declaredCarrierRoute state entry).getD (#[], #[])
    presentations := presentations.push {
      source := entry.id, sourceCategory := entry.category, targetCategory := entry.category
      params, route := #[], applications := #[], carrierRoute, identifications
      object, image := object, identity }
  unless presentations.isEmpty do
    Trace.record (← read).trace representative
      (.parameterEquivalence expected representative presentations)
  return some representative

/-- Infer a missing map from registered declarations and the categorical identity at fixed
endpoints. An identity competes with named maps; it is not a default for an arbitrary endomap. -/
partial def registeredArrowParameter (expected : Expr) : M (Option Expr) := do
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then return none
  let some (source, target) := homEnds? expected | return none
  let state ← registryState
  let instantiate (entry : MorphismEntry) : M Expr := do
    let constant ← mkConstWithFreshMVarLevels entry.declaration
    let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
    unless ← isDefEq type expected do
      throwStratum .invalid m!"the registered map has different selected endpoints"
    synthesizeInstances args infos
    let arrow ← instantiateMVars (mkAppN constant args)
    if arrow.hasMVar || arrow.hasLevelMVar || !(← isTypeCorrect arrow) then
      throwStratum .invalid m!"the registered map's actual parameters are not determined"
    return arrow
  let mut candidates := #[]
  for entry in state.morphisms do
    if ← parameterCompatible (do
        discard <| instantiate entry
        pure true) then candidates := candidates.push entry
  if candidates.size > 1 then
    throwSemanticAmbiguity m!"several registered maps have these selected endpoints"
  let mut identities : Array (Expr × NamedCategoryEntry) := #[]
  if ← parameterTrial (isDefEq source target) then
    for category in state.categories do
      let candidate? ← parameterTrial do
        let family ← instantiateFresh category.declaration
        let objectType ← mkAppM ``CategoryTheory.Bundled.α #[family]
        unless ← isDefEq (← inferType source) objectType do return none
        let identity ← identityAt (.object source category none none none)
        unless !identity.hasMVar && !identity.hasLevelMVar && (← isTypeCorrect identity) &&
            (← isDefEq (← inferType identity) expected) do return none
        return some identity
      if let some identity := candidate? then
        unless ← identities.anyM (fun (other, _) => parameterTrial (isDefEq other identity)) do
          identities := identities.push (identity, category)
  if identities.size > 1 then
    throwSemanticAmbiguity m!"several categorical identities have these selected endpoints"
  if let some entry := candidates[0]? then
    let arrow ← instantiate entry
    if let some (identity, _) := identities[0]? then
      unless ← parameterTrial (withTransparency .all <| isDefEq arrow identity) do
        throwSemanticAmbiguity m!"a registered map and the identity have these selected endpoints"
    let arrow ← retainNamedMorphism entry arrow
    return some arrow
  if let some (_, category) := identities[0]? then
    return some (← identityAt (.object source category none none none))
  return none

/-- Infer declaration arguments from the operand's stored typed constructor parameters before
comparing carriers. Nested registered constructors retain bundled parameters that an abbreviation
may hide when its outer carrier is unified. -/
partial def bindSourceParameter (parameter : Expr) (actual : Value) : M Bool := do
  -- The registered source declaration fixes relationships between its own ordered arguments.
  -- Match these before attempting acquisition from an enclosing structure.
  if let .object _ _ (some (entry, values)) _ _ := actual then
    let reduced ← instantiateMVars parameter
    if reduced.getAppFn.constName? == some entry.declaration then
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let arguments := (reduced.getAppArgs.zip infos).filterMap fun (argument, info) =>
        if info.isExplicit then some argument else none
      unless arguments.size == values.size do return false
      let mut declared ← semanticObject actual
      declared := declared.consumeMData
      while declared.isAppOfArity ``id 2 do declared := declared.appArg!.consumeMData
      let actualArguments := if declared.getAppFn.constName? == some entry.declaration then
        (declared.getAppArgs.zip infos).filterMap fun (argument, info) =>
          if info.isExplicit then some argument else none
        else #[]
      for h : i in [:arguments.size] do
        let argument := arguments[i]
        let value := values[i]!
        let mut matched := false
        if let some supplied := actualArguments[i]? then
          let unknowns ← getMVars argument
          let exactTrial := do
            unless ← isDefEq (← inferType argument) (← inferType supplied) <&&>
                isDefEq argument supplied do return false
            for unknown in unknowns do
              let chosen ← instantiateMVars (mkMVar unknown)
              if chosen.hasMVar || chosen.hasLevelMVar then return false
            isTypeCorrect (← instantiateMVars argument)
          if ← parameterCompatible exactTrial then
            matched ← exactTrial
        unless matched do
          unless ← bindSourceParameter argument value do return false
      return ← isDefEq parameter (← semanticObject actual)
  let actualTerm ← typedParameter (← instantiateMVars (← inferType parameter)) actual
  for id in ← getMVars parameter do
    let unknownArgument ← instantiateMVars (mkMVar id)
    unless unknownArgument.isMVar do continue
    let expected ← instantiateMVars (← inferType unknownArgument)
    let mut witnesses : Array Expr := #[]
    for value in sourceParameterValues actual do
      let candidate? ← parameterTrial do
        let candidate? ← match value with
          | .object handle .. | .morphism handle .. | .element handle .. =>
              if ← isDefEq (← inferType handle) expected then pure (some handle)
              else
                try pure (some (← typedParameter expected value))
                catch error =>
                  if CasCatalogue.Exception.interpretationKind error == .invalid then pure none
                  else throw error
          | .nat _ =>
              try pure (some (← typedParameter expected value))
              catch error =>
                if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
          | _ => pure none
        let some candidate := candidate? | return none
        let candidate ← instantiateMVars candidate
        if candidate.hasMVar || candidate.hasLevelMVar || !(← isTypeCorrect candidate) then
          return none
        unless ← isDefEq unknownArgument candidate <&&> isDefEq parameter actualTerm do return none
        return some candidate
      if let some candidate := candidate? then
        unless ← witnesses.anyM (fun old => parameterTrial do
            withTransparency .all <| isDefEq old candidate) do
          witnesses := witnesses.push candidate
    -- A named argument can acquire a complete package through its registered refinement;
    -- an anonymous carrier cannot create one by an instance or carrier match.
    if witnesses.isEmpty then
      let candidate? ← parameterTrial do
        try
          let candidate ← instantiateMVars (← typedParameter expected actual)
          if candidate.hasMVar || candidate.hasLevelMVar || !(← isTypeCorrect candidate) then
            return none
          unless ← isDefEq unknownArgument candidate <&&> isDefEq parameter actualTerm do return none
          return some candidate
        catch error =>
          if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
      if let some candidate := candidate? then witnesses := #[candidate]
    if witnesses.size > 1 then
      throwSemanticAmbiguity m!"distinct complete source parameter witnesses remain"
    if let some candidate := witnesses[0]? then
      unless ← isDefEq unknownArgument candidate <&&> isDefEq parameter actualTerm do return false
  isDefEq parameter actualTerm

/-- Retain supplied structured sources of parameters of already declared constructors.
Carrier parameters keep their existing identity; this never infers a named object from a type. -/
partial def retainStructuredParameterSources (value : Value) (known : Array Value) : M Unit := do
  let some trace := (← read).trace | return
  let state ← registryState
  for source in sourceParameterValues value do
    let .object handle _ (some (entry, values)) _ _ := source | continue
    let some (.object recorded parameters) ← Trace.node? trace handle | continue
    unless recorded == entry.id && parameters.size == values.size do
      throwError "retained constructor parameters differ from their declared provenance"
    for (actual, selected) in parameters.zip values do
      let .object _ category .. := selected | continue
      let expected ← inferType actual
      if (← whnfR expected).isSort || (← isProp expected) then continue
      if (← Trace.node? trace actual).isSome then continue
      discard <| selectedParameterFromWitnesses state actual category known

/-- An independently selected callable kind and address ends binding lookup. A
generic declaration-only consumer must instead have one compatible accepted
binding across its callable kinds; aliases never acquire storage-order priority. -/
partial def familyBinding (state : RegistryState) (declaration : Name) (category : CategoryId)
    (application : Expr) (arity : Nat) (operationId : Option OperationId)
    (callableAddress : Option String) : M (Option OperationEntry × Option String) := do
  if let some address := callableAddress then
    unless operationId.isNone do
      throwStratum .invalid "an application selected two different callable kinds"
    let some (registeredDeclaration, registeredCategory) := state.callable? address
      | throwStratum .invalid "the selected application has no registered callable address"
    unless registeredDeclaration == declaration && registeredCategory == category do
      throwStratum .invalid "the selected callable is outside its declared category or signature"
    return (none, some address)
  let operation ← OperationAgreement.selectedEntry state declaration application arity operationId
  if operationId.isSome then return (operation, none)
  let morphisms := state.morphisms.filter fun row =>
    row.declaration == declaration && row.category == category
  unless operation.isNone || morphisms.isEmpty do
    throwSemanticAmbiguity "this declaration has distinct operation and morphism bindings; select its callable kind"
  match morphisms with
  | #[] => return (operation, none)
  | #[entry] => return (none, some entry.id.raw)
  | _ => throwSemanticAmbiguity "several accepted morphism IDs share this declaration; select the binding"

/-- Tag the already selected named morphism with its accepted address. Its full
declaration arguments remain the recorded parameters. -/
partial def retainNamedMorphism (entry : MorphismEntry) (value : Expr) : M Expr := do
  let mut application := (← instantiateMVars value).consumeMData
  while application.isAppOfArity ``id 2 || application.isAppOfArity ``Trace.operationResult 3 do
    application := application.appArg!.consumeMData
  unless application.getAppFn.isConstOf entry.declaration &&
      (← withTransparency .all <| isDefEq (← inferType application) (← inferType value)) do
    throwStratum .invalid "the selected morphism lost its full declared application"
  let params ← explicitArguments entry.declaration application
  Trace.recordCallable (← read).trace value (.namedMorphism entry.id params)

/-- The family of morphisms `declaration` of `category` applied to elements. Its parameters are
unified from the sets of the operands and from `target?`, the set it is to land in (`deg` on
`ℤ[x]` is `deg ℤ`); a numeral operand is an element of the set the family then takes there. -/
partial def applyFamily (declaration : Name) (category : NamedCategoryEntry)
    (elements : Array Value) (target? : Option Value := none) (numerals : Array Nat := #[])
    (maps : Array Expr := #[]) (parameters : Array Value := #[])
    (application : Option Expr := none) (callableAddress : Option String := none)
    (operationId : Option OperationId := none) : M Value := do
  let state ← registryState
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let some (source, target) := homEnds? type
    | throwStratum .invalid m!"{declaration} is not a family of morphisms"
  if let some T@(.object ..) := target? then
    if ← incompatibleTypeShapes target (← semanticObject T) then
      throwStratum .invalid m!"{declaration} has a different declared result type"
  if let some supplied := application then
    let mut supplied := supplied.consumeMData
    while supplied.isAppOfArity ``id 2 || supplied.isAppOfArity ``Trace.operationResult 3 do
      supplied := supplied.appArg!.consumeMData
    unless supplied.getAppFn.constName? == some declaration && supplied.getAppArgs.size == args.size do
      throwStratum .invalid m!"the supplied application is not this registered declaration"
    if supplied.hasMVar then
      throwStratum .invalid m!"the supplied application retains unresolved parameters"
    unless ← isTypeCorrect supplied do
      throwStratum .invalid m!"the supplied application is outside its declared dependent signature"
    for (parameter, argument) in args.zip supplied.getAppArgs do
      unless ← isDefEq (← inferType parameter) (← inferType argument) <&&> isDefEq parameter argument do
        throwStratum .invalid m!"a retained application parameter is outside its declared type"
  let explicit := (args.zip infos).filterMap fun (a, i) => if i.isExplicit then some a else none
  -- A supplied point of a product-valued data object is one whole operand.
  -- Only two supplied operands request the product's two source factors.
  let sources ← if elements.size == 2 then
    match (← whnfR source).getAppFn.constName?, (← whnfR source).getAppArgs with
    | some ``Prod, #[x, y] => pure #[x, y]
    | _, _ => pure #[source]
  else pure #[source]
  unless elements.isEmpty || sources.size == elements.size do
    throwStratum .invalid m!"{declaration} takes {sources.size} operands"
  unless parameters.size + numerals.size ≤ explicit.size do
    throwStratum .invalid m!"too many explicit parameters of {declaration} were supplied"
  for (parameter, value) in explicit.zip parameters do
    let expected ← instantiateMVars (← inferType parameter)
    let argument ← typedParameter expected value
    unless ← isDefEq parameter argument do
      throwStratum .invalid m!"an explicit parameter of {declaration} is outside its declared type"
  for (a, k) in (explicit.extract parameters.size explicit.size).zip numerals do
    unless ← isDefEq (← inferType a) (mkConst ``Nat) <&&> isDefEq a (mkNatLit k) do
      throwStratum .invalid m!"{declaration} does not take the numeral {k} there"
  -- Its parameters that are maps (the `f` of `f.taylor_expansion(0)`), in order.
  let mapParams ← explicit.filterM fun a => do
    let type ← instantiateMVars (← inferType a)
    return (homEnds? type).isSome || (← whnfR type).isAppOf ``Quiver.Hom
  unless maps.size ≤ mapParams.size do
    throwStratum .invalid m!"{declaration} takes {mapParams.size} maps"
  for (a, f) in mapParams.zip maps do
    unless ← isDefEq (← inferType a) (← inferType f) <&&> isDefEq a f do
      throwStratum .invalid m!"{declaration} does not apply to this map"
  -- Infer a complete application jointly from actual registered source arguments. Each
  -- speculative assignment is discarded unless all source parameters and the whole family
  -- application are closed and type correct; independent operand conversions do not guess it.
  let joint? ← parameterTrial do
    try
      for (set, operand) in sources.zip elements do
        let .element _ A := operand | return none
        unless ← bindSourceParameter set A do return none
      for parameter in explicit do
        let chosen ← instantiateMVars parameter
        if chosen.hasMVar || chosen.hasLevelMVar then return none
      synthesizeInstances args infos
      let application ← instantiateMVars (mkAppN constant args)
      if application.hasMVar || application.hasLevelMVar || !(← isTypeCorrect application) then
        return none
      for (set, operand) in sources.zip elements do
        let .element _ A := operand | return none
        let set ← instantiateMVars set
        if set.hasMVar || set.hasLevelMVar then return none
        unless ← isDefEq set (← semanticObject A) do return none
      return some (← args.mapM instantiateMVars)
    catch error =>
      if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
  if let some joint := joint? then
    for (parameter, chosen) in args.zip joint do
      unless ← isDefEq parameter chosen do
        throwStratum .invalid m!"a joint source parameter differs from its actual declaration"
  -- A registered inclusion carries its dependent target parameters. Use that actual
  -- arrow before attempting to infer a bundled parameter from a bare carrier.
  for (set, operand) in sources.zip elements do
    let .element _ A@(.object _ _ (some (origin, _)) _ _) := operand | continue
    if set.getAppFn.constName? == some origin.declaration then
      let sourceInfos ← forallTelescopeReducing (← getConstInfo origin.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let declaredParameters := (set.getAppArgs.zip sourceInfos).filterMap fun (argument, info) =>
        if info.isExplicit then some argument else none
      let .object _ _ (some (_, actualParameters)) _ _ := A | unreachable!
      for (parameter, actual) in declaredParameters.zip actualParameters do
        let expected ← instantiateMVars (← inferType parameter)
        if ← parameterCompatible (do
            unless ← bindSourceParameter parameter actual do return false
            isTypeCorrect (← instantiateMVars (mkAppN constant args))) then
          discard <| bindSourceParameter parameter actual
    if !(← instantiateMVars set).hasMVar then continue
    if ← parameterCompatible (do
        unless ← isDefEq set (← semanticObject A) do return false
        isTypeCorrect (← instantiateMVars (mkAppN constant args))) then
      discard <| isDefEq set (← semanticObject A)
      continue
    let head := (← instantiateMVars set).getAppFn.constName?
    let rows := state.objects.filter fun row =>
      row.category == category.id && some row.declaration == head
    if let [row] := rows.toList then
      if let some chain := inclusionChain state origin.id row.id then
        if ← parameterCompatible (do
            let inclusion ← inclusionMap chain A
            let some (_, endpoint) := homEnds? (← inferType inclusion) | return false
            unless ← isDefEq set endpoint do return false
            isTypeCorrect (← instantiateMVars (mkAppN constant args))) then
          let inclusion ← inclusionMap chain A
          let some (_, endpoint) := homEnds? (← inferType inclusion) | continue
          discard <| isDefEq set endpoint
  for parameter in explicit do
    if !(← instantiateMVars parameter).isMVar then continue
    if (source.findMVar? (· == parameter.mvarId!)).isNone then continue
    let expected ← instantiateMVars (← inferType parameter)
    for (operandSource, operand) in sources.zip elements do
      let operandSource ← instantiateMVars operandSource
      if (operandSource.findMVar? (· == parameter.mvarId!)).isNone then continue
      let .element _ A@(.object _ _ _ (some _) _) := operand | continue
      if ← parameterCompatible (do
          let selected ← typedParameter expected A
          unless ← isDefEq parameter selected <&&>
              isDefEq operandSource (← semanticObject A) do return false
          isTypeCorrect (← instantiateMVars (mkAppN constant args))) then
        let selected ← typedParameter expected A
        unless ← isDefEq parameter selected <&&>
            isDefEq operandSource (← semanticObject A) do
          throwStratum .invalid m!"the selected parameter differs from its full operand source"
        break
  for parameter in explicit do
    if !(← instantiateMVars parameter).isMVar then continue
    if (source.findMVar? (· == parameter.mvarId!)).isNone then continue
    let expected ← instantiateMVars (← inferType parameter)
    if (homEnds? expected).isSome then continue
    for (operandSource, operand) in sources.zip elements do
      let operandSource ← instantiateMVars operandSource
      if (operandSource.findMVar? (· == parameter.mvarId!)).isNone then continue
      let .element _ A := operand | continue
      let mut witnesses : Array Expr := #[]
      for actual in sourceParameterValues A do
        let witness? ← parameterTrial do
          try
            unless ← bindSourceParameter parameter actual do return none
            unless ← isDefEq operandSource (← semanticObject A) do return none
            let witness ← instantiateMVars parameter
            if witness.hasMVar || (← instantiateMVars operandSource).hasMVar then return none
            unless ← isTypeCorrect (← instantiateMVars (mkAppN constant args)) do return none
            return some witness
          catch error =>
            if (CasCatalogue.Exception.interpretationKind error) == .invalid then pure none
            else throw error
        if let some witness := witness? then
          unless ← witnesses.anyM (fun existing => parameterTrial (isDefEq existing witness)) do
            witnesses := witnesses.push witness
      if witnesses.size > 1 then
        throwSemanticAmbiguity m!"several full typed constructor parameters determine the source"
      if let some witness := witnesses[0]? then
        unless ← isDefEq parameter witness <&&> isDefEq operandSource (← semanticObject A) do
          throwStratum .invalid m!"the chosen constructor parameter does not give the actual source"
        break
      let inferred? ← parameterTrial do
        let recorder ← Trace.new
        let selected? ← withReader (fun context => { context with trace := some recorder }) do
          registeredStructuredParameter expected A
        let some selected := selected? | return none
        unless ← isDefEq parameter selected <&&>
            isDefEq operandSource (← semanticObject A) do return none
        unless ← isTypeCorrect (← instantiateMVars (mkAppN constant args)) do return none
        return some (selected, ← recorder.get)
      if let some (selected, records) := inferred? then
        unless ← isDefEq parameter selected <&&>
            isDefEq operandSource (← semanticObject A) do
          throwStratum .invalid m!"the actual selected structural parameter differs from its operand source"
        if let some trace := (← read).trace then
          trace.modify fun current => records.fold
            (fun result term node => result.insert term node) current
        break
  -- Its parameters are unified with the sets' objects (semantic, whichever reading).
  if let some T@(.object ..) := target? then
    let t ← semanticObject T
    -- A forgetful carrier does not determine its bundled structure by unification.
    -- Read unresolved structure parameters through the registered selected routes.
    if !(← parameterTrial (isDefEq target t)) then
      for parameter in explicit do
        if !(← instantiateMVars parameter).isMVar then continue
        let expected ← instantiateMVars (← inferType parameter)
        if ← parameterCompatible (do
            discard <| typedParameter expected T
            pure true) then
          let argument ← typedParameter expected T
          unless ← isDefEq parameter argument do
            throwStratum .invalid m!"a result structure parameter is outside its declared type"
    unless ← isDefEq target t do
      throwStratum .invalid m!"{declaration} does not land in {t}"
  -- Endpoint inference precedes selection of a dependent coefficient map. Its complete
  -- registered application is retained; ordinary carrier inclusions are not ring maps.
  for parameter in mapParams do
    if !(← instantiateMVars parameter).isMVar then continue
    if let some arrow ← registeredArrowParameter (← inferType parameter) then
      unless ← isDefEq parameter arrow do
        throwStratum .invalid m!"the selected registered map differs from the dependent parameter"
  -- An operand of a set included in the source is carried there (`Mˣ ↪ M`, `ℕ ⊆ ℤ`). Anything else
  -- is not in the family's domain: an operand is never admitted into a domain because the family
  -- needs it there (it is formed there, `x in D`).
  let operandObjects := elements.filterMap fun | .element _ X => some X | _ => none
  let mut endpointWitnesses := parameters ++ operandObjects ++ target?.toArray
  -- A selected operation already supplies its complete heterogeneous parameters.
  -- Retain those objects before reading the operand endpoints; otherwise a scalar
  -- endpoint can be forced back through an unrelated presentation of its module.
  if let some selected := operationId then
    if callableAddress.isNone then
      let complete ← instantiateMVars (mkAppN constant args)
      if !complete.hasMVar && !complete.hasLevelMVar then
        let some entry ← OperationAgreement.selectedEntry state declaration complete
            elements.size (some selected)
          | throwStratum .invalid "the selected operation lost its complete declared binding"
        endpointWitnesses ← operationParameterObjects entry complete endpointWitnesses
  -- The domain's declared inclusion also fixes its ambient object. Keep that actual
  -- endpoint for dependent result parameters rather than recovering an alias from a carrier.
  for X in operandObjects do
    if let some (_, ambient) ← inclusionOut? X then
      let ambientValue ← try inclusionTargetValue X ambient category catch error =>
        if Exception.interpretationKind error == .invalid then
          -- No named presentation is asserted: the inclusion still supplies this exact object.
          pure (Value.object ambient category none none none)
        else throw error
      endpointWitnesses := endpointWitnesses.push ambientValue
  let elements ← (sources.zip elements).mapM fun (set, v) => do
    let .element _ A@(.object ..) := v | return v
    let a ← semanticObject A
    let declaredHead := (← instantiateMVars set).getAppFn.constName?
    let declaredObjects := state.objects.filter fun row =>
      row.category == category.id && some row.declaration == declaredHead
    let sameDeclaredObject := match A with
      | .object _ _ (some (origin, _)) _ _ =>
          declaredObjects.isEmpty || declaredObjects.any (·.id == origin.id)
      | _ => declaredObjects.isEmpty
    if sameDeclaredObject && (← isDefEq set a) then return v
    if let some (_, b) ← inclusionOut? A then
      if ← isDefEq set b then return ← coerceTo v (← inclusionTargetValue A (← instantiateMVars b) category)
    let set ← instantiateMVars set
    if set.hasMVar || set.hasLevelMVar then
      throwStratum .invalid m!"{declaration} does not apply to an element of {a}"
    let S ← declaredEndpointObject set category endpointWitnesses (← args.mapM instantiateMVars)
    -- This declaration has independently fixed its complete source. An original
    -- generalized point already at that exact endpoint needs no structural coercion.
    -- The original source context remains attached to the declared operand object.
    declaredResult v S
  synthesizeInstances args infos
  let elements ← (sources.zip elements).mapM fun (set, v) => do
    if let .element .. := v then return v
    let set ← instantiateMVars set
    if set.hasMVar then
      throwStratum .invalid m!"the set of an operand of {declaration} is not determined"
    toElement v (← declaredEndpointObject set category endpointWitnesses (← args.mapM instantiateMVars))
  synthesizeInstances args infos
  for parameter in args do
    if !(← instantiateMVars parameter).isMVar then continue
    let obligation ← instantiateMVars (← inferType parameter)
    if obligation.hasMVar || !(← isProp obligation) then continue
    if let some proof ← decideObligation obligation then
      unless ← isDefEq parameter proof do
        throwStratum .invalid m!"a closed operation obligation is outside its declared type"
  let operation ← instantiateMVars (mkAppN constant args)
  if operation.hasMVar then
    throwStratum .invalid m!"the parameters and obligations of {declaration} are not determined"
  -- Retain the complete dependent application, including synthesized instances, implicit
  -- parameters and supplied maps; elaborating only explicit arguments can change the reading.
  unless ← isTypeCorrect operation do
    throwStratum .invalid m!"an argument of {declaration} is outside its declared type"
  let (operationEntry, callableAddress) ←
    familyBinding state declaration category.id operation elements.size operationId callableAddress
  let operation ← if let some address := callableAddress then do
    let fullParameters ← ((args.zip infos).filterMap fun (parameter, info) =>
      if info.isExplicit then some parameter else none).mapM instantiateMVars
    unless fullParameters.all (fun parameter => !parameter.hasMVar && !parameter.hasLevelMVar) do
      throwStratum .invalid m!"the selected callable's full parameters are not determined"
    -- A named morphism keeps its independently selected binding kind when its
    -- complete application is applied to operands. The exact accepted address,
    -- not a declaration match, determines whether this is a named morphism.
    if let some entry := state.morphisms.find? (fun entry => entry.id.raw == address) then
      retainNamedMorphism entry operation
    else
      Trace.recordCallable (← read).trace operation (.namedCallable address category.id fullParameters)
  else pure operation
  if elements.isEmpty then
    let source ← instantiateMVars source
    let target ← instantiateMVars target
    let targetValue ← match target? with
      | some targetValue => pure targetValue
      | none => declaredEndpointObject target category endpointWitnesses (← args.mapM instantiateMVars)
    if category.id == CategoryId.sets then
      if ← parameterTrial (isDefEq source (← semanticObject (← oneObject))) then
        let result ← staged operation
        if let some entry := operationEntry then
          let actualParameters := (operation.getAppArgs.zip infos).filterMap fun (argument, info) =>
            if info.isExplicit then some argument else none
          let chosen := match targetValue with
            | .object _ _ _ (some selected) _ => selected
            | _ => targetValue
          let result ← Trace.recordOperation (← read).trace result
            (.operationApply entry.id actualParameters #[] target (← semanticObject chosen))
          return .element result targetValue
        else Trace.alias (← read).trace operation result
        return .element result targetValue
      if let some comparison ← operationPointComparison source then
        let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, operation]
        unless !composite.hasMVar && !composite.hasLevelMVar &&
            (← isTypeCorrect composite) do
          throwStratum .invalid m!"the admitted terminal comparison does not form this point"
        Trace.record (← read).trace composite
          (.morphismComposition category.id comparison operation (← globalPointSource) source target)
        let result ← staged composite
        if let some entry := operationEntry then
          let actualParameters := (operation.getAppArgs.zip infos).filterMap fun (argument, info) =>
            if info.isExplicit then some argument else none
          let chosen := match targetValue with
            | .object _ _ _ (some selected) _ => selected
            | _ => targetValue
          let result ← Trace.recordOperation (← read).trace result
            (.operationPoint entry.id actualParameters comparison operation target (← semanticObject chosen))
          return .element result targetValue
        else Trace.alias (← read).trace composite result
        return .element result targetValue
    let sourceValue ← declaredEndpointObject source category endpointWitnesses (← args.mapM instantiateMVars)
    return .morphism operation source target category (some (sourceValue, targetValue))
  let family ← quoteExpr operation
  let target ← match target? with
    | some T => pure T
    | none => declaredEndpointObject (← instantiateMVars target) category endpointWitnesses (← args.mapM instantiateMVars)
  let result ← applyTo family elements target
  if let some entry := operationEntry then
    let .element resultMap resultTarget := result | unreachable!
    let operands ← elements.mapM fun
      | .element hom _ => pure hom
      | _ => throwStratum .invalid m!"an operation operand has no element map"
    let actualParameters := (operation.getAppArgs.zip infos).filterMap fun (argument, info) =>
      if info.isExplicit then some argument else none
    let chosen := match target with
      | .object _ _ _ (some selected) _ => selected
      | _ => target
    let resultMap ← Trace.recordOperation (← read).trace resultMap
      (.operationApply entry.id actualParameters operands
        (← semanticObject target) (← semanticObject chosen))
    return .element resultMap resultTarget
  return result

/-- The registered application of the set of the element `f`, its category and the set's
parameters; for an element of a domain `D ↪ B` (an automorphism in `GLₙ(K) ↪ Matₙ(K)`), that of
`B`. -/
partial def applicationOf? (f : Value) :
    M (Option (Name × NamedCategoryEntry × Array Value × String)) := do
  let .element _ D@(.object _ category (some (entry, params)) _ _) := f | return none
  if let some application := entry.application then return some (application, category, params, entry.applicationAddress)
  let some (_, b) ← inclusionOut? D | return none
  applicationOf? (.element (mkConst ``Unit) (← inclusionTargetValue D b category))

/-- The generator of `R[x]` (its registered distinguished element), at the current stage. -/
partial def presentationMap (scope : Scope) (operand : Syntax) (name : String)
    (inverse : Bool) : M Value := do
  let state ← registryState
  let [entry] := (state.presentations.filter (·.name == name)).toList
    | throwStratum .invalid m!"no unique registered presentation is named {name}"
  presentationMapValue (← eval scope operand) entry inverse

/-- Apply precisely the registered presentation selected by its endpoints or explicit name. -/
partial def presentationMapValue (value : Value) (entry : PresentationComparisonEntry)
    (inverse : Bool) : M Value := do
  let state ← registryState
  let .element _ X := value
    | throwStratum .invalid m!"a presentation acts on an element"
  let endpointId := if inverse then entry.target else entry.source
  let some endpoint := state.objects.find? (·.id == endpointId)
    | throwStratum .invalid m!"the presentation endpoint is not registered"
  let some category := state.categories.find? (·.id == endpoint.category)
    | throwStratum .invalid m!"the presentation category is not registered"
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (args, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
  let result ← whnfR result
  let #[_, _, source, target] := result.getAppArgs
    | throwStratum .invalid m!"the presentation does not declare an isomorphism"
  let selected ← typedParameter (← inferType source) X
  let selectedEndpoint := if inverse then target else source
  unless selectedEndpoint.getAppFn.constName? == some endpoint.declaration do
    throwStratum .invalid m!"the presentation does not retain its declared endpoint"
  unless ← isDefEq selectedEndpoint selected do
    throwStratum .invalid m!"the element is outside the selected presentation endpoint"
  synthesizeInstances args infos
  let iso ← instantiateMVars (mkAppN constant args)
  if iso.hasMVar then
    throwStratum .invalid m!"the presentation parameters are not determined"
  unless ← isTypeCorrect iso do
    throwStratum .invalid m!"the presentation is outside its dependent signature"
  let arrow ← Semantic.presentationArrow entry iso inverse (← read).trace
  let sourceValue ← recognize state (← instantiateMVars (if inverse then target else source)) category
  let targetValue ← recognize state (← instantiateMVars (if inverse then source else target)) category
  let sourceCarrier ← carrierObject sourceValue
  let targetCarrier ← carrierObject targetValue
  let .object _ sets _ _ _ := sourceCarrier | unreachable!
  letI : Inhabited Route :=
    ⟨{ source := category.expression, target := sets.expression, steps := #[] }⟩
  do
    let routes := (← routesBetween state category.expression sets.expression)
    let route ← if let some refs ← retainedCarrierRoute state sourceValue then
      match routes.find? (·.refs == refs) with
      | some route => pure route
      | none => throwStratum .invalid m!"the retained presentation carrier route is not registered"
    else do
      let [cls] := (state.classify routes (fun _ => sets.id.raw) id).toList
        | throwSemanticAmbiguity m!"the presentation has no unique carrier route"
      unless cls.ambiguities.isEmpty do
        throwSemanticAmbiguity m!"several comparisons determine the presentation carrier map"
      discard <| Semantic.validateRouteComparisons state cls.comparisonWitnesses
        (some (← semanticObject sourceValue))
      let [route] := cls.sources.toList
        | throwSemanticAmbiguity m!"the presentation has no unique directed carrier route"
      pure route
    let mapped ← if route.steps.isEmpty then pure arrow else
      elabTermAndSynthesize (← `(CategoryTheory.Functor.map
        $(← quoteExpr (← Semantic.routeFunctor state route.refs)) $(← quoteExpr arrow))) none
    unless route.steps.isEmpty do
      Trace.record (← read).trace mapped
        (.morphismTransport category.id sets.id route.refs arrow)
    let argument ← toElement value sourceCarrier
    let result ← applyTo (← quoteExpr mapped) #[argument] targetCarrier
    let .element argumentMap _ := argument | unreachable!
    let .element resultMap _ := result | unreachable!
    let parameters := (iso.getAppArgs.zip infos).filterMap fun (argument, info) =>
      if info.isExplicit then some argument else none
    Trace.record (← read).trace resultMap
      (.presentationApply entry.id parameters inverse
        (← semanticObject sourceValue) (← semanticObject targetValue) argumentMap)
    return result

partial def generatorIndex (applied : Expr) (i : Nat) : M Term := do
  let .forallE _ expected _ info ← whnfR (← inferType applied)
    | throwStratum .invalid m!"the generator has no indexed variables"
  unless info.isExplicit do
    throwStratum .invalid m!"the generator's index is not an explicit parameter"
  let expected ← whnfR expected
  if expected.isConstOf ``Nat then
    pure (Syntax.mkNumLit (toString i) : Term)
  else
    let #[bound] := expected.getAppArgs
      | throwStratum .invalid m!"the generator's index has no finite numeral bound"
    unless expected.isAppOf ``Fin do
      throwStratum .invalid m!"the generator's index is not a numeral index"
    let some n ← (Meta.evalNat bound).run
      | throwStratum .invalid m!"the generator's index bound is not determined"
    unless i < n do throwStratum .invalid m!"the variable {i} of {n} variables"
    let some below ← decideObligation (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n])
      | throwStratum .invalid m!"the variable {i} of {n} variables"
    quoteExpr (mkApp3 (mkConst ``Fin.mk) bound (mkNatLit i) below)

partial def generatorOf (P : Value) (index : Option Nat := none) : M Value := do
  let P ← carrierObject P
  let .object p category (some (entry, params)) _ _ := P
    | throwStratum .invalid m!"only a named set has a generator"
  let some g := entry.generator | throwStratum .invalid m!"{entry.name} has no generator"
  let .object one _ _ _ _ ← oneObject | unreachable!
  let parameterTerms ← typedParamTerms g params
  let applied ← elabTermAndSynthesize (← `($(mkCIdent g) $parameterTerms*)) none
  -- The remaining declaration binder owns the index type and bound. Object parameters
  -- may contain several numerals; none of their positions defines an indexing convention.
  let indexTerm ← match index with
    | none => pure #[]
    | some i => pure #[← generatorIndex applied i]
  let hom ← homIn (← `($(mkCIdent g) $parameterTerms* $indexTerm*)) one p category
  let infos ← forallTelescopeReducing (← getConstInfo g).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let mut application := hom.consumeMData
  while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
  unless application.getAppFn.constName? == some g do
    throwStratum .invalid m!"the generator does not retain its registered declaration"
  let arguments := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none
  Trace.record (← read).trace hom (.generator entry.id arguments)
  match (← read).stage with
  | none => return .element hom P
  | some S => return .element (← throughTerminal S hom) P

/-- The variables of the polynomial rings `R[v]` of `stx` (and of the bindings it uses) that `stx`
uses, bound to their generators: of a ring `stx` writes, else of a ring of a binding it uses. A
variable of two different such rings is ambiguous. -/
partial def ringBindings (scope : Scope) (stx : Syntax) : M (List (Name × Value)) := do
  let rings := ringsIn scope #[] stx
  let loose ← contextualIdentifiers scope stx
  let ctx ← read
  let mut bindings : List (Name × Value) := []
  let mut done : Array Name := #[]
  for (v, _, _) in rings do
    let used := loose.contains v || loose.any (differentialOf? · == some v)
    if done.contains v || !used || scope.contains v || (ctx.bound.lookup v).isSome then
      continue
    done := done.push v
    -- The rings the statement writes itself come before those of the bindings it uses.
    let own := (ringsIn {} #[] stx).filter (·.1 == v)
    let candidates := if own.isEmpty then rings.filter (·.1 == v) else own
    let written := candidates.map (shown ·.2.1)
    unless written.all (· == written[0]!) do
      throwSemanticAmbiguity m!"{v} is the variable of several rings: {written.toList}"
    let some (_, ring, index) := candidates[0]? | unreachable!
    bindings := (v, ← generatorOf (← eval scope ring) index) :: bindings
  return bindings

/-- Identity on an already selected carrier, or its witnessed forward structural view.
This checks the full chosen source and actual carrier-route prefix, not carrier equality alone. -/
partial def identityCarrierView (Y X : Value) : M Bool := do
  let state ← registryState
  let (.object y _ yOrigin ySelected _, .object x _ xOrigin xSelected xData) := (Y, X)
    | return false
  -- A named source can supply its declared refinement at an independently fixed full
  -- target structure. This checks every eligible registered source and compares the whole
  -- resulting object; an unnamed carrier cannot acquire such a structure by conversion.
  let matchingOrigins := match yOrigin, xOrigin with
    | some (left, _), some (right, _) => left.id == right.id
    | _, _ => false
  if ySelected.isNone && yOrigin.isSome && !matchingOrigins then
    if let some (.object target targetCategory ..) := xSelected then
      if targetCategory.id != CategoryId.sets &&
          (← parameterTrial (withTransparency .all <| isDefEq y x)) then
        if ← parameterCompatible (do
            let selected ← typedParameter (← inferType target) Y
            unless !selected.hasMVar && !selected.hasLevelMVar && (← isTypeCorrect selected) do
              return false
            withTransparency .all <| isDefEq selected target <&&> isDefEq y x) then
          return true
  let sameSelection ← match ySelected, xSelected with
    | some left@(.object leftObject leftCategory ..),
        some (.object rightObject rightCategory _ _ rightData) =>
        if leftCategory.id == rightCategory.id then
          parameterTrial <| withTransparency .all <| isDefEq leftObject rightObject
        else parameterCompatible do
          -- A retained forward view may forget structure, but may not recover it from
          -- a carrier. Replay its actual prefix of this source's declared carrier route.
          let some (_, source, route, _, arguments) := rightData | return false
          let .object sourceObject sourceCategory .. := source | return false
          unless sourceCategory.id == leftCategory.id &&
              (← isDefEq (← inferType sourceObject) (← inferType leftObject)) &&
              (← withTransparency .all <| isDefEq sourceObject leftObject) do return false
          let some carrierRoute ← retainedCarrierRoute state left | return false
          unless !route.isEmpty && route.size ≤ carrierRoute.size &&
              route == carrierRoute.extract 0 route.size do return false
          let (image, _) ← retainedActions state sourceObject route arguments
          unless ← isDefEq (← inferType image) (← inferType rightObject) do return false
          withTransparency .all <| isDefEq image rightObject
    | some _, some _ => pure false
    | _, _ => pure true
  -- A bare target asks only for the already fixed carrier. This forward view does not
  -- acquire a name or structure on a bare source; coerceTo retains the supplied provenance.
  let sameOrigin := if xOrigin.isNone && xSelected.isNone && xData.isNone then true else
    match yOrigin, xOrigin with
    | some (left, _), some (right, _) => left.id == right.id
    | none, none => true
    | _, _ => false
  return sameSelection && sameOrigin && (y == x || (← isDefEq y x))

/-- How the elements of the set `Y` are elements of the set `X`: `some none` if they are the same
set, `some (some ι)` along `ι : Y ⟶ X`, the registered constants of `X` from its parameter `Y`
(`ℚ ↪ ℚ[x]`) or a chain of registered inclusions (`ℚ ⊆ ℝ`); `none` otherwise. -/
partial def coercionMap (Y X : Value) : M (Option (Option Expr)) := do
  let state ← registryState
  let (.object y _ yOrigin .., .object x category xOrigin ..) := (Y, X) | return none
  if ← identityCarrierView Y X then return some none
  if let some (entry, params) := xOrigin then
    if let (some constants, some parameter@(.object ..)) :=
        (entry.constants, params.find? (· matches .object ..)) then
      let P ← carrierObject parameter
      let .object p .. := P | unreachable!
      -- The target fixes its complete parameter independently. A coefficient may already
      -- inhabit that parameter's witnessed weaker carrier view. Applying these fixed
      -- constants does not recover a structure on the coefficient's source object.
      let into ← coercionMap Y P
      let into ← if into.isSome then pure into
        else if ← identityCarrierView P Y then pure (some none) else pure none
      if let some into := into then
        let ι ← homIn (← `($(mkCIdent constants) $(← typedParamTerms constants params)*)) p x category
        Trace.record (← read).trace ι
          (.objectField entry.id "constants" entry.category (← explicitArguments constants ι))
        return some (some (← match into with
          | some ι₀ => do
              let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[ι₀, ι]
              Trace.record (← read).trace composite
                (.morphismComposition category.id ι₀ ι y p x)
              pure composite
          | none => pure ι))
  if let (some (sub, _), some (super, _)) := (yOrigin, xOrigin) then
    if let some chain := inclusionChain state sub.id super.id then
      unless chain.isEmpty do
        return some (some (← inclusionMap chain Y (some X)))
  -- A domain's inclusion `Y ↪ B` (`Mˣ ↪ M`), then `B` into `X`.
  if let some (ι, b) ← inclusionOut? Y then
    let B ← inclusionTargetValue Y b category
    let .object bHandle .. := B | unreachable!
    let .object _ _ (some (entry, _)) _ _ := Y | unreachable!
    let some declaration := entry.inclusion | unreachable!
    let params ← explicitArguments declaration ι
    let ι ← homIn (← quoteExpr ι) y bHandle category
    Trace.record (← read).trace ι (.objectField entry.id "inclusion" entry.category params)
    if let some into ← coercionMap B X then
      return some (some (← match into with
        | some ι' => do
            let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[ι, ι']
            Trace.record (← read).trace composite
              (.morphismComposition category.id ι ι' y bHandle x)
            pure composite
        | none => pure ι))
  return none

/-- The composite `Y ↪ … ↪ X` of a chain of registered inclusions out of `Y`. -/
partial def inclusionMap (chain : Array InclusionEntry) (Y : Value)
    (target? : Option Value := none) : M Expr := do
  let .object original category _ _ _ := Y
    | throwStratum .invalid m!"an inclusion starts at a selected object"
  let mut source := original
  let mut composite ← identityAt Y
  Trace.record (← read).trace composite (.morphismIdentity category.id original)
  for (entry, i) in chain.zipIdx do
    let constant ← mkConstWithFreshMVarLevels entry.declaration
    let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
    let some (declaredSource, declaredTarget) := homEnds? type
      | throwStratum .invalid m!"a registered inclusion is not a morphism"
    unless ← isDefEq declaredSource source do
      throwStratum .invalid m!"an inclusion is outside its registered source parameters"
    if i + 1 == chain.size then
      if let some target := target? then
        unless ← isDefEq declaredTarget (← semanticObject target) do
          throwStratum .invalid m!"an inclusion is outside its registered target parameters"
    synthesizeInstances args infos
    for arg in args do
      if !(← instantiateMVars arg).isMVar then continue
      let obligation ← instantiateMVars (← inferType arg)
      unless ← isProp obligation do continue
      let some proof ← decideObligation obligation
        | throwStratum .invalid m!"the registered inclusion's obligation is not established"
      unless ← isDefEq arg proof do
        throwStratum .invalid m!"the inclusion's proof is outside its declared obligation"
    let arrow ← instantiateMVars (mkAppN constant args)
    if arrow.hasMVar then
      throwStratum .invalid m!"the registered inclusion's parameters are not determined"
    unless ← isTypeCorrect arrow do
      throwStratum .invalid m!"the registered inclusion is outside its dependent signature"
    let target ← instantiateMVars declaredTarget
    let parameters ← ((args.zip infos).filterMap fun (arg, info) =>
      if info.isExplicit then some arg else none).mapM instantiateMVars
    unless !arrow.hasLevelMVar && !source.hasMVar && !source.hasLevelMVar &&
        !target.hasMVar && !target.hasLevelMVar do
      throwStratum .invalid m!"the registered inclusion retains unresolved endpoints"
    Trace.record (← read).trace arrow
      (.namedInclusion entry.id entry.category parameters source target)
    let previous := composite
    composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[previous, arrow]
    unless ← isTypeCorrect composite do
      throwStratum .invalid m!"the inclusion composite is outside its dependent signature"
    Trace.record (← read).trace composite
      (.morphismComposition category.id previous arrow original source target)
    source := target
  return composite

/-- `v` as an element of `X`: a numeral's element there, or an element carried along the inclusion
of its set in `X` (`coercionMap`). -/
partial def coerceTo (v : Value) (X : Value) : M Value := do
  match v with
  | .element h Y =>
      let some (_, actualCarrier) := homEnds? (← inferType h)
        | throwStratum .invalid m!"the element retains no actual point morphism"
      unless ← withTransparency .all <| isDefEq actualCarrier (← semanticObject Y) do
        throwStratum .invalid m!"the element's actual carrier differs from its retained set"
      match ← coercionMap Y X with
      | some (some ι) =>
          let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[h, ι]
          let some (source, _) := homEnds? (← inferType h) | unreachable!
          let target ← semanticObject X
          let some (_, actualTarget) := homEnds? (← inferType composite) | unreachable!
          unless !composite.hasMVar && !composite.hasLevelMVar &&
              (← isTypeCorrect composite) && (← isDefEq actualTarget target) do
            throwStratum .invalid m!"the admitted inclusion does not reach the requested element set"
          let .object middle category .. := Y | unreachable!
          Trace.record (← read).trace composite
            (.morphismComposition category.id h ι source middle target)
          return .element composite X
      | some none =>
          -- An identity view through an unstructured carrier keeps the source's chosen data.
          let target := match X, Y with
            | .object _ _ none none none, _ => Y
            | .object _ _ _ none _, .object _ _ _ (some _) _ => Y
            | _, _ => X
          return .element h target
      | none =>
          let source := match Y with
            | .object _ _ _ (some selected) _ => selected
            | _ => Y
          let target := match X with
            | .object _ _ _ (some selected) _ => selected
            | _ => X
          throwStratum .invalid m!"the element has no admitted inclusion into the requested set; \
            source {← semanticObject Y}, selected source {← semanticObject source}; \
            target {← semanticObject X}, selected target {← semanticObject target}"
  | _ => toElement v X

/-- A set among `sets` that each of them is included in. -/
partial def commonSet? (sets : Array Value) : M (Option Value) := do
  for X in sets do
    if ← sets.allM fun Y => return (← coercionMap Y X).isSome then return some X
  return none

/-- The tuple of the elements `values` of `X`, in `Xⁿ`: `cons(x₁, … cons(xₙ, ()))`.
The optional cache is shared only by tuples with the same fixed `X` in a closed reading. -/
partial def tupleOf (values : Array Value) (X : Value)
    (numerals? : Option (IO.Ref (Std.HashMap Nat Value)) := none) : M Value := do
  let X ← carrierObject X
  let state ← registryState
  let ctx ← read
  let numerals? ← if ctx.stage.isNone && ctx.bound.isEmpty then
    match numerals? with
    | some cache => pure (some cache)
    | none => some <$> IO.mkRef ({} : Std.HashMap Nat Value)
  else pure none
  let some empty := state.morphisms.find? (·.name == "()") | throwStratum .invalid m!"no tuples"
  let E ← profileReader "tuple empty object" <| object state "Vec" #[X, .nat 0] none
  let .object e category _ _ _ := E | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let mut hom ← profileReader "tuple empty map" <|
    homIn (← `($(mkCIdent empty.declaration) $(← paramTerms #[X])*)) one e category
  Trace.record (← read).trace hom (.namedMorphism empty.id #[← semanticObject X])
  hom ← staged hom
  let mut acc := Value.element hom E
  for v in values.reverse do
    let element ← profileReader "tuple coerce" <| do
      if let .nat n := v then
        if let some numerals := numerals? then
          if let some element := (← numerals.get)[n]? then return element
          let element ← coerceTo v X
          if element.terms.all (fun term => !term.hasMVar && !term.hasLevelMVar &&
              !term.hasFVar && !term.hasLooseBVars) then
            numerals.modify (·.insert n element)
          return element
      coerceTo v X
    acc ← profileReader "tuple cons" <| applyNamed state "cons" #[element, acc]
  return acc

/-- Read an actual nondependent finite-function type without assigning a named alias to its
coordinate. The complete selected object's declared components can retain its coordinate view. -/
partial def finiteFunctionContext (target : Value) : M (Option (Nat × Value)) := do
  let .object handle category _ _ _ := target | return none
  unless category.id == CategoryId.sets do return none
  -- A declared representation may be a non-reducible type synonym. Read its
  -- actual function shape without inventing an alias or selecting new structure.
  let functionType ← withTransparency .all <| whnf handle
  unless functionType.isForall && !functionType.bindingBody!.hasLooseBVars do return none
  let indexType ← withTransparency .all <| whnf functionType.bindingDomain!
  unless indexType.isAppOfArity ``Fin 1 do return none
  let length ← instantiateMVars indexType.appArg!
  if length.hasMVar || length.hasLevelMVar then
    throwStratum .invalid m!"the declared finite-function length is not determined"
  let some count ← (Meta.evalNat (← withTransparency .all <| whnf length)).run
    | throwStratum .invalid m!"the declared finite-function length is not a numeral"
  let coordinate ← instantiateMVars functionType.bindingBody!
  if coordinate.hasMVar || coordinate.hasLevelMVar then
    throwStratum .invalid m!"the declared finite-function coordinate is not determined"
  -- The whole selected object can supply a declared component presentation even
  -- when its carrier has not yet acquired a named origin. Component discovery
  -- retains that full structure before a coordinate numeral is interpreted.
  if count > 0 then
    let components? : Option (Array Value) ← optionalReading
      (componentElements (.element (← identityAt target) target) count)
    if let some components := components? then
      if let some (Value.element _ component) := components[0]? then
        unless ← isDefEq (← semanticObject component) coordinate do
          throwStratum .invalid m!"the declared component differs from its actual coordinate type"
        return some (count, retainObjectContext component #[target])
  return some (count, retainObjectContext
    (.object coordinate category none none none) #[target])

/-- `(x₁, …, xₙ)`: in the actual declared finite-function object, else in a set its components
are in, else `ℤ`. The construction uses the existing tuple maps at the fixed coordinate type. -/
partial def tuple (scope : Scope) (xs : Array Syntax) (ambient? : Option Value)
    (numerals? : Option (IO.Ref (Std.HashMap Nat Value)) := none) : M Value := do
  if let some target@(.object handle _ none _ _) := ambient? then
    if let some dataCarrier ← constrainedCarrier? target then
      return ← admitConstrainedPoint target (← tuple scope xs (some dataCarrier) numerals?)
    let mut actual := handle.consumeMData
    while actual.isAppOfArity ``id 2 do actual := actual.appArg!.consumeMData
    if actual.isAppOf ``CategoryTheory.Limits.Cone.pt && xs.size == 2 then
      let projections ← componentElements (.element (← identityAt target) target) xs.size
      let values ← (xs.zip projections).mapM fun (termSyntax, projection) => do
        let .element _ component := projection | unreachable!
        declaredResult (← eval scope termSyntax none (some component)) component
      return ← applyTo (← quoteExpr (← identityAt target)) values target
  if let some target := ambient? then
    if let some (count, coordinate) ← finiteFunctionContext target then
      unless count == xs.size do
        throwStratum .invalid m!"the declared tuple has {count} coordinates, but {xs.size} were supplied"
      let values ← xs.mapM (eval scope · none (some coordinate))
      return ← declaredResult (← tupleOf values coordinate numerals?) target
  let X? := match ambient? with
    | some (.object _ _ (some (entry, #[X, .nat n])) _ _) =>
        if entry.name == "Vec" && n == xs.size then some X else none
    | _ => none
  let X? ← X?.mapM carrierObject
  let values ← xs.mapM (eval scope · none X?)
  let X ← match X? with
    | some X => pure X
    | none =>
        let sets := values.filterMap fun | .element _ X => some X | _ => none
        match ← commonSet? sets, sets[0]? with
        | some X, _ | none, some X => pure X
        | none, none => notationObject "literal.integral.domain"
  tupleOf values X numerals?

/-- `[a, b; c, d]`: the registered matrix with these rows, in an enclosing `Matₙ(K)`, else over the
set its entries are in. -/
partial def matrix (scope : Scope) (rows : Array (Array Syntax)) (ambient? : Option Value) :
    M Value := do
  let n := rows.size
  if let some target := ambient? then
    if let some (rowCount, rowObject) ← finiteFunctionContext target then
      let some (columnCount, _) ← finiteFunctionContext rowObject
        | throwStratum .invalid m!"a declared matrix has two finite-function dimensions"
      unless rowCount == n && rows.all (·.size == columnCount) do
        throwStratum .invalid m!"the declared matrix has {rowCount} rows and {columnCount} columns"
      let rowValues ← rows.mapM fun row => tuple scope row (some rowObject)
      return ← declaredResult (← tupleOf rowValues rowObject) target
  unless rows.all (·.size == n) do
    throwStratum .invalid m!"a matrix `[…; …]` is square: {n} rows of {n} entries"
  let K? := match ambient? with
    | some (.object _ _ (some (entry, #[.nat m, K])) _ _) =>
        if entry.name == "Mat" && m == n then some K else none
    | _ => none
  let rowAmbient ← match K? with
    | some K => some <$> object (← registryState) "Vec" #[K, .nat n] none
    | none => pure none
  let ctx ← read
  let numerals? ← if K?.isSome && ctx.stage.isNone && ctx.bound.isEmpty then
    some <$> IO.mkRef ({} : Std.HashMap Nat Value) else pure none
  let rowValues ← rows.mapM fun row => tuple scope row rowAmbient numerals?
  let .element _ V := rowValues[0]! | throwStratum .invalid m!"a row is a tuple"
  applyNamed (← registryState) "rows" #[← tupleOf rowValues V]

/-- `t in C/Y`: the named object `t` as its registered refinement into the category family `C`,
at the object of `C`'s base whose underlying set is `Y` (`ℂ[x] in Algebras/ℂ`: `ℂ[x]` under `ℂ`).
The judgement is the catalogue's: realizations are not consulted. -/
partial def inCategoryOver (scope : Scope) (t : Syntax) (C : NamedCategoryEntry) (Y : Syntax) :
    M Value := do
  let state ← registryState
  let .object _ _ (some (base, params)) _ _ ← eval scope t
    | throwStratum .invalid m!"`{shown t}` is not a named object"
  -- An object of `C` already (`Spec ℚ[x]`), or its refinement there (`ℚ[x]` as an algebra).
  let some refined := if base.category == C.id then some base else state.objects.find? fun o =>
      o.category == C.id && (o.refines.map (·.base == base.id)).getD false
    | throwStratum .invalid m!"{base.name} has no registered refinement in {C.name}"
  let object ← Semantic.object refined (← typedParamTerms refined.declaration params)
  -- The object of the base over which it lies: the family's parameter, read off its type.
  let family ← mkConstWithFreshMVarLevels C.declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let some _ := args[0]?
    | throwStratum .invalid m!"{C.name} is not a category family over an object"
  let carrierType ← mkAppM ``CategoryTheory.Bundled.α #[mkAppN family args]
  unless ← withTransparency .all <| isDefEq (← inferType object) carrierType do
    throwStratum .invalid m!"{refined.name} is not an object of {C.name}"
  -- Over `Y`: the family's parameter is determined by the object's set parameter, which is `Y`.
  let overValue ← eval scope Y
  let some selectedBase := args[0]?
    | throwStratum .invalid m!"{refined.name} has no declared base parameter"
  let y ← typedParameter (← instantiateMVars (← inferType selectedBase)) overValue
  unless ← withTransparency .all <| isDefEq selectedBase y do
    throwStratum .invalid m!"{refined.name} is not over {shown Y} in {C.name}"
  let completeFamily ← instantiateMVars (mkAppN family args)
  if completeFamily.hasMVar || completeFamily.hasLevelMVar then
    throwStratum .invalid m!"the selected category family is not fixed by the object's complete type"
  return .object object C (some (refined, params)) none none

/-- A registered family at its applicable selected receiver binder. Its complete
dependent application determines the other parameters, before any operands are applied. -/
partial def invariantOf (entry : MorphismEntry) (A : Value) : M Value := do
  let state ← registryState
  let some category := state.categories.find? (·.id == entry.category) | unreachable!
  -- The application is admitted only at the declared dependent signature (b0-typed-application):
  -- the applicable explicit parameter takes `A` at its declared type and all other
  -- parameters are determined by that complete application.
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (args.zip infos).filterMap fun (a, i) => if i.isExplicit then some a else none
  let mut receiverSlots : Array (Nat × Expr) := #[]
  for slot in [:explicit.size] do
    let candidate ← try parameterTrial do
      unless ← bindSelectedReceiver explicit slot A do return none
      synthesizeInstances args infos
      let application ← instantiateMVars (mkAppN constant args)
      if application.hasMVar || application.hasLevelMVar || !(← isTypeCorrect application) then
        return none
      return some application
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
    if let some application := candidate then
      unless ← receiverSlots.anyM (fun (_, previous) =>
          sameOperationApplication previous application) do
        receiverSlots := receiverSlots.push (slot, application)
  match receiverSlots.toList with
  | [(slot, application)] =>
      unless ← bindSelectedReceiver explicit slot A do
        throwError "the complete selected receiver application changed during commitment"
      unless ← withTransparency .all <| isDefEq (mkAppN constant args) application do
        throwError "the committed family differs from its complete selected parameter application"
  | [] => throwStratum .invalid m!"the complete parameters of {entry.name} are not fixed by this receiver"
  | _ => throwSemanticAmbiguity m!"several complete declared applications accept this selected receiver"
  synthesizeInstances args infos
  unless ← isTypeCorrect (← instantiateMVars (mkAppN constant args)) do
    throwStratum .invalid m!"an argument of {entry.name} is outside its declared type"
  if (← explicit.mapM instantiateMVars).any (·.hasMVar) then
    throwStratum .invalid m!"the parameters of {entry.name} are not determined by the selected object"
  let .object one _ _ _ _ ← oneObject | unreachable!
  let some (source, _) := homEnds? (← instantiateMVars type)
    | throwStratum .invalid m!"{entry.name} is not an invariant of objects"
  let family ← instantiateMVars (mkAppN constant args)
  let family ← retainNamedMorphism entry family
  let some (_, target) := homEnds? (← instantiateMVars (← inferType family))
    | throwStratum .invalid m!"{entry.name} is not an invariant of objects"
  let endpoint (term : Expr) : M Value := do
    declaredEndpointObject term category #[A] (← args.mapM instantiateMVars)
  let T ← endpoint target
  if ← isDefEq source one then
    let .object t .. := T | unreachable!
    let hom ← homIn (← quoteExpr family) one t category
    Trace.alias (← read).trace family hom
    return .element (← staged hom) T
  if let some comparison ← operationPointComparison source then
    let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, family]
    let .object t .. := T | unreachable!
    let hom ← homIn (← quoteExpr composite) one t category
    Trace.record (← read).trace composite
      (.morphismComposition category.id comparison family one source target)
    Trace.alias (← read).trace composite hom
    return .element (← staged hom) T
  return .morphism family source target category (some (← endpoint source, T))

/-- Member-family declarations compete by their complete dependent applications;
their order in the registry does not choose a meaning. -/
partial def invariantNamed (state : RegistryState) (name : String) (receiver : Value) : M Value := do
  let rows := state.morphisms.filter (·.name == name)
  let applicable ← match rows with
    | #[row] => pure #[row]
    | _ => rows.filterM fun row => parameterCompatible do
        discard <| invariantOf row receiver
        pure true
  match applicable with
  | #[row] => invariantOf row receiver
  | #[] => throwStratum .invalid m!"no complete registered family `{name}` takes this receiver"
  | _ => throwSemanticAmbiguity m!"several complete registered families `{name}` take this receiver"

/-- Decode an ordinal only at the complete actual diagram-index type. -/
partial def constructionIndex (indexType : Expr) (ordinal : Nat) : M Expr := do
  let indexType ← instantiateMVars (← whnfR indexType)
  if indexType.hasMVar || indexType.hasLevelMVar then
    throwStratum .invalid m!"the construction index type is not determined"
  if indexType.isConstOf ``Nat then return mkNatLit ordinal
  if indexType.isAppOf ``Fin then
    let some bound := indexType.getAppArgs[0]? | unreachable!
    let proposition ← mkAppM ``LT.lt #[mkNatLit ordinal, bound]
    let some proof ← decideObligation proposition
      | throwStratum .invalid m!"the construction index is outside its actual bound"
    return mkApp3 (mkConst ``Fin.mk) bound (mkNatLit ordinal) proof
  if indexType.isAppOf ``CategoryTheory.Discrete then
    let index ← constructionIndex indexType.appArg! ordinal
    return ← mkAppM ``CategoryTheory.Discrete.mk #[index]
  let some name := indexType.getAppFn.constName?
    | throwStratum .invalid m!"the construction index is not a closed finite enumeration"
  let .inductInfo info ← getConstInfo name
    | throwStratum .invalid m!"the construction index is not an enumeration"
  for constructor in info.ctors do
    let .ctorInfo constructorInfo ← getConstInfo constructor | unreachable!
    unless constructorInfo.numFields == 0 do
      throwStratum .invalid m!"an ordinal cannot select an indexed or recursive constructor"
  let some constructor := info.ctors[ordinal]?
    | throwStratum .invalid m!"the construction index is outside its actual enumeration"
  let constant ← mkConstWithFreshMVarLevels constructor
  let (params, _, result) ← forallMetaTelescopeReducing (← inferType constant)
  unless ← isDefEq result indexType do
    throwStratum .invalid m!"the index constructor does not inhabit the selected index type"
  let index ← instantiateMVars (mkAppN constant params)
  unless !index.hasMVar && !index.hasLevelMVar && (← isTypeCorrect index) do
    throwStratum .invalid m!"the index constructor retains unresolved parameters"
  return index

/-- Project the actual defining leg of a registered construction, independently of outer tracing. -/
partial def constructionLeg (scope : Scope) (term indexSyntax : Syntax) : M Value := do
  let recorder ← Trace.new
  let receiver ← withReader (fun context => { context with trace := some recorder }) do
    eval scope term
  let .object apex category .. := receiver
    | throwStratum .invalid m!"a defining leg belongs to a constructed object"
  let .nat ordinal ← eval scope indexSyntax
    | throwStratum .invalid m!"a construction index is a typed ordinal"
  let mut exactApex := apex.consumeMData
  while exactApex.isAppOfArity ``id 2 do exactApex := exactApex.appArg!.consumeMData
  let colimit := exactApex.isAppOf ``CategoryTheory.Limits.Cocone.pt
  unless colimit || exactApex.isAppOf ``CategoryTheory.Limits.Cone.pt do
    throwStratum .invalid m!"the object retains no actual construction cone"
  let cone := exactApex.appArg!
  let projection := if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone
  unless cone.isAppOf projection do
    throwStratum .invalid m!"the object does not retain its accepted construction presentation"
  let presentation := cone.appArg!
  let state ← registryState
  let localNode ← recorder.node? apex
  let retainedNode ← match localNode, (← read).trace with
    | some node, _ => pure (some node)
    | none, some trace => trace.node? apex
    | none, none => pure none
  let node ← match retainedNode with
    | some node@(.limit ..) => pure node
    | _ => do
        let diagram := (← instantiateMVars (← inferType presentation)).appArg!
        let direct := state.limits.filter (fun row =>
          row.colimit == colimit && some row.declaration == presentation.getAppFn.constName?)
        let candidates := if direct.isEmpty then state.limits.filter (fun row =>
          row.colimit == colimit && (presentation.find? (fun part =>
            part.getAppFn.constName? == some row.declaration)).isSome) else direct
        let mut identified : Array (LimitId × Option LiftId) := #[]
        for row in candidates do
          let resolution ← match state.resolveLimitDetailed category.id row.shape colimit with
            | .ok resolution => pure resolution
            | .error error@(.ambiguous ..) => liftM (Semantic.limitResolutionFailure error)
            | .error _ => continue
          unless resolution.limit == row.id do continue
          if ← parameterCompatible (do
              let accepted ← Semantic.limit colimit row.shape diagram category.id.raw none
              withTransparency .all <| isDefEq accepted presentation) then
            let identity := (resolution.limit, resolution.lift)
            unless identified.contains identity do identified := identified.push identity
        let [(id, lift)] := identified.toList
          | throwStratum .invalid m!"the cone has no unique exact registered construction provenance"
        pure (.limit id diagram lift)
  let .limit id diagram lift := node | unreachable!
  let some row := state.limits.find? (·.id == id) | unreachable!
  unless row.colimit == colimit do
    throwStratum .invalid m!"the retained construction has the wrong cone orientation"
  let actualDiagram := (← instantiateMVars (← inferType presentation)).appArg!
  unless ← isDefEq actualDiagram diagram do
    throwStratum .invalid m!"the retained construction names a different actual diagram"
  let resolution ← match state.resolveLimitDetailed category.id row.shape colimit with
    | .ok resolution => pure resolution
    | .error error => liftM (Semantic.limitResolutionFailure error)
  unless resolution.limit == id && resolution.lift == lift do
    throwStratum .invalid m!"the retained construction has a different registered creation lift"
  let accepted ← Semantic.limit colimit row.shape diagram category.id.raw none
  unless ← withTransparency .all <| isDefEq accepted presentation do
    throwStratum .invalid m!"the recorded construction does not match the actual presentation"
  let leg ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.ι
    else ``CategoryTheory.Limits.Cone.π) #[cone]
  let app ← mkAppM ``CategoryTheory.NatTrans.app #[leg]
  let (indices, _, _) ← forallMetaTelescopeReducing (← inferType app)
  let #[indexParameter] := indices
    | throwStratum .invalid m!"the defining leg has no unique actual index binder"
  let index ← instantiateMVars (← constructionIndex (← inferType indexParameter) ordinal)
  unless !index.hasMVar && !index.hasLevelMVar && (← isTypeCorrect index) do
    throwStratum .invalid m!"the actual construction index is not completely instantiated"
  let hom ← instantiateMVars (mkApp app index)
  unless !hom.hasMVar && (← isTypeCorrect hom) do
    throwStratum .invalid m!"the defining leg is outside its actual typed diagram"
  let some (source, target) := homEnds? (← inferType hom)
    | throwStratum .invalid m!"the defining leg is not a morphism"
  let endpoint (value : Expr) : M Value := do
    if ← isDefEq value apex then return receiver
    declaredEndpointObject value category #[receiver]
  if let some trace := (← read).trace then
    let entries ← recorder.get
    trace.modify fun current => entries.fold (fun result value record => result.insert value record) current
  Trace.record (← read).trace apex node
  Trace.record (← read).trace hom (.limitProjection apex index)
  return .morphism hom source target category (some (← endpoint source, ← endpoint target))

/-- `t.m(a, …)`: the registered family `m` at `t` (a map is its parameter, an element its first
operand), applied to the operands `a, …`. -/
partial def callWith (scope : Scope) (t : Syntax) (name : String) (args : Array Syntax) :
    M Value := do
  if name == "leg" then
    let #[index] := args | throwStratum .invalid m!"a defining leg takes one actual diagram index"
    return ← constructionLeg scope t index
  if name == "field" then
    let #[index] := args
      | throwStratum .invalid "a structured data field takes one declared port index"
    let .nat index ← eval scope index
      | throwStratum .invalid "the structured field index is an ordinal"
    let some value ← structuredField (← eval scope t) "field" (some index)
      | throwStratum .invalid "the value has no complete registered construction data schema"
    return value
  let state ← registryState
  let rows := state.morphisms.filter (·.name == name)
  let operands ← args.mapM (eval scope ·)
  let receiver ← eval scope t
  let apply (entry : MorphismEntry) : M Value := do
    let some category := state.categories.find? (·.id == entry.category)
      | throwStratum .invalid "the selected family has no accepted category"
    match receiver with
    | .morphism h .. =>
        -- A map parameter must already inhabit the declaration's complete Hom type.
        let constant ← mkConstWithFreshMVarLevels entry.declaration
        let (args, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
        let mapParams ← (args.zip infos).filterM fun (a, i) =>
          return i.isExplicit && (← whnfR (← inferType a)).isAppOf ``Quiver.Hom
        if mapParams.isEmpty then
          throwStratum .invalid m!"`{name}` takes an element of its domain, not a map: form \
            `{shown t}` there first (`{shown t} in D`), where its evidence is established"
        applyFamily entry.declaration category operands (maps := #[h]) (callableAddress := some entry.id.raw)
    | v@(.element ..) | v@(.nat _) =>
        applyFamily entry.declaration category (#[v] ++ operands) (callableAddress := some entry.id.raw)
    | receiver@(.object ..) =>
        let .morphism family .. ← invariantOf entry receiver
          | throwStratum .invalid m!"the selected object's family does not take operands"
        applyFamily entry.declaration category operands (application := some family) (callableAddress := some entry.id.raw)
    | _ => throwStratum .invalid m!"`{name}` is called on a map, an element or a selected object"
  let applicable ← match rows with
    | #[row] => pure #[row]
    | _ => rows.filterM fun row => parameterCompatible do
        discard <| apply row
        pure true
  match applicable with
  | #[row] => apply row
  | #[] => throwStratum .invalid m!"no complete registered family `{name}` takes these inputs"
  | _ => throwSemanticAmbiguity m!"several complete registered families `{name}` take these inputs"

/-- The element `(x, y)` of the product of the sets of `x` and `y` (its registered presentation),
the mediator of the cone `(x, y)`. -/
partial def pairOf (x y : Value) : M Value := do
  let (.element hx (.object a₁ category _ _ _), .element hy (.object a₂ ..)) := (x, y)
    | throwStratum .invalid m!"a pair is of elements"
  let one := (← whnfR (← inferType hx)).appFn!.appArg!
  let diagram ← `(CategoryTheory.Limits.pair $(← quoteExpr a₁) $(← quoteExpr a₂))
  let cone ← limitIn false "product" diagram category
  let apex ← apexOf false cone
  let lift ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
    #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[cone],
      ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[hx, hy]]
  return .element (← mkExpectedTypeHint lift (← mkAppM ``Quiver.Hom #[one, apex]))
    (.object apex category none none none)

/-- Apply a selected binder to an already admitted complete family. The accepted
operation fixes its full source and result; admission is not replayed or inferred
from computational data. The original generalized point domain is retained. -/
partial def selectedBinder (scope : Scope) (name : String) (parameters : Array Syntax)
    (familySyntax : Syntax) : M Value := do
  let state ← registryState
  let some row := state.binders.find? (·.id.raw == name)
    | throwStratum .invalid "the selected binder is not registered"
  let some category := state.categories.find? (·.id == row.category)
    | throwStratum .invalid "the selected binder has no registered category"
  let family ← eval scope familySyntax
  let (admitted, inputObject, asElement) ← match family with
    | .element point object => pure (point, object, true)
    | .morphism .. | .derivedMorphism .. => do
        let (hom, _, _, _, _, target) ← morphismContext family
        pure (hom, target, false)
    | _ => throwStratum .invalid "an explicit binder consumes an already admitted complete family"
  let application ← DirectConstruction.instantiate row.operation
    (← selectedParameterTerms scope row.operation parameters)
  let some (source, target) := homEnds? (← inferType application.value)
    | throwStratum .invalid "the selected binder operation is not a complete categorical map"
  let actualSource ← semanticObject inputObject
  unless ← withTransparency .all <| isDefEq source actualSource do
    throwStratum .invalid "the family does not inhabit this binder's exact declared source"
  let application ← DirectConstruction.close application
  let source ← instantiateMVars source
  let target ← instantiateMVars target
  let some (domain, _) := homEnds? (← inferType admitted)
    | throwStratum .invalid "the admitted family lost its original generalized domain"
  let context ← CategoryContext.ofNamed category source
  CategoryContext.checkMorphism context admitted domain source
  let result ← mkAppM ``CategoryTheory.CategoryStruct.comp #[admitted, application.value]
  CategoryContext.checkMorphism context result domain target
  let known := #[family, inputObject]
  let targetValue ← try recognize state target category known application.explicit
    catch error =>
      if Exception.interpretationKind error == .invalid then
        objectInContext target context known
      else throw error
  let declaredDomain ← instantiateFresh row.domain
  unless declaredDomain.getAppNumArgs == application.arguments.size do
    throwStratum .invalid "the binder domain changed its complete parameter telescope"
  for (argument, selected) in declaredDomain.getAppArgs.zip application.arguments do
    unless ← withTransparency .all <| isDefEq (← inferType argument) (← inferType selected) <&&>
        isDefEq argument selected do
      throwStratum .invalid "the binder domain changed a complete selected parameter"
  let declaredDomain ← instantiateMVars declaredDomain
  unless !declaredDomain.hasMVar && !declaredDomain.hasLevelMVar &&
      (← isTypeCorrect declaredDomain) do
    throwStratum .invalid "the binder lost its complete declared family domain"
  let original ← match (← read).trace with
    | some trace => do
        match ← trace.node? admitted with
        | some (.constrainedPoint _ _ _ _ _ original) => pure original
        | some (.admittedPoint _ _ _ original _ _ _) => pure original
        | _ => pure admitted
    | none => pure admitted
  Trace.record (← read).trace result
    (.binder row.id application.explicit declaredDomain original admitted)
  if asElement then return ← restage (.element result targetValue)
  let (_, _, _, _, domainValue, _) ← morphismContext family
  morphismInContext result domain target context (domainValue, targetValue)

/-- Prepare a registered binding operation. Surface arguments occupy its last explicit
object or morphism parameters. The declaration fixes the domain; the body's codomain supplies
any remaining structure parameters. Evidence is checked only after the unique reading is chosen. -/
partial def binderReading (scope : Scope) (row : BinderEntry) (boundName : Name)
    (arguments : Array Syntax) (body : Syntax) (ambient? : Option Value)
    (sharedArgument? : Option Value := none) :
    M (Expr × Value × Value × Value) := do
  let state ← registryState
  let some category := state.categories.find? (·.id == row.category)
    | throwStratum .invalid m!"a binder has no registered category"
  let constant ← mkConstWithFreshMVarLevels row.operation
  let (params, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let some (source, target) := homEnds? type
    | throwStratum .invalid m!"a binder operation is not a morphism"
  let explicit := (params.zip infos).filterMap fun (p, i) => if i.isExplicit then some p else none
  unless arguments.size ≤ explicit.size do
    throwStratum .invalid m!"a binder has too few declared parameters"
  let supplied := explicit.extract (explicit.size - arguments.size) explicit.size
  let mut knownArguments : Array Value := #[]
  for (parameter, argumentSyntax) in supplied.zip arguments do
    let expected ← instantiateMVars (← inferType parameter)
    let (value, declaredContext) ← if let some (_, target) := homEnds? (← whnfR expected) then
        let target ← instantiateMVars target
        if target.hasMVar then
          let value ← match sharedArgument? with
          | some value => pure value
          | none => eval scope argumentSyntax
          pure (value, #[])
        else do
          let X ← recognize state target category knownArguments (← params.mapM instantiateMVars)
          let value ← toElement (← eval scope argumentSyntax none (some X)) X
          pure (value, #[X])
      else do
        let value ← match sharedArgument? with
          | some value => pure value
          | none => eval scope argumentSyntax
        pure (value, #[])
    let term ← typedParameter expected value
    unless ← isDefEq parameter term do
      throwStratum .invalid m!"a binder argument is outside its declared parameter"
    let retained := if !declaredContext.isEmpty then declaredContext else match value with
      | .element _ X@(.object _ _ origin _ _) =>
          #[X] ++ (origin.map (·.2)).getD #[]
      | v@(.object ..) => #[v]
      | .morphism _ _ _ _ (some (X, Y)) => #[X, Y]
      | _ => #[]
    knownArguments := knownArguments ++ retained
  synthesizeInstances params infos
  let domain ← mkConstWithFreshMVarLevels row.domain
  let domain ← instantiateMVars (mkAppN domain params)
  -- Evaluate the declared domain function, not candidate object aliases. Its returned
  -- object declaration or actual argument keeps its identity and supplied provenance.
  let domain ← match ← unfoldDefinition? domain with
    | some unfolded => instantiateMVars unfolded
    | none => pure domain
  -- The domain may ignore a still unknown codomain parameter. Reduce that dependency only;
  -- recognition retains declaration identity of the domain's registered object.
  let domain ← if domain.hasMVar then instantiateMVars (← whnfR domain) else pure domain
  if domain.hasMVar then
    throwStratum .invalid m!"the binder arguments do not determine its domain"
  let D ← recognize state domain category knownArguments (← params.mapM instantiateMVars)
  let knownTarget ← instantiateMVars target
  let bodyAmbient ← if knownTarget.hasMVar then pure ambient?
    else pure (some (← recognize state knownTarget category knownArguments (← params.mapM instantiateMVars)))
  let value ← atStage scope boundName D body bodyAmbient
  let value ← match value, bodyAmbient with
    | .nat _, some Y => toElement value Y
    | _, _ => pure value
  let .element bodyMap Y := value
    | throwStratum .invalid m!"a binder body must be an element at its declared domain"
  -- First retain parameters that the declared result constructor itself determines. Validate
  -- the dependent application before keeping an assignment: a reducible carrier cannot
  -- assign an untyped object to a structure parameter.
  if ← parameterCompatible (do
      unless ← isDefEq target (← semanticObject Y) do return false
      isTypeCorrect (← instantiateMVars (mkAppN constant params))) then
    discard <| isDefEq target (← semanticObject Y)
  -- Any remaining structured parameters use the exact selected object and registered routes.
  for parameter in explicit.extract 0 (explicit.size - arguments.size) do
    if !(← instantiateMVars parameter).isMVar then continue
    let expected ← instantiateMVars (← inferType parameter)
    if ← parameterCompatible (do
        let term ← typedParameter expected Y
        isDefEq parameter term) then
      let term ← typedParameter expected Y
      discard <| isDefEq parameter term
  unless ← isDefEq target (← semanticObject Y) do
    throwStratum .invalid m!"the binder body has a different codomain"
  synthesizeInstances params infos
  let operation ← instantiateMVars (mkAppN constant params)
  if operation.hasMVar then
    throwStratum .invalid m!"the binder parameters are not determined"
  unless ← isTypeCorrect operation do
    throwStratum .invalid m!"a binder parameter is outside its declared type"
  retainStructuredParameterSources D (knownArguments ++ #[Y])
  let M ← recognize state (← instantiateMVars source) category #[D, Y] (← params.mapM instantiateMVars)
  let retainedSource ← semanticObject M
  let operationSource ← instantiateMVars source
  unless !operationSource.hasMVar && !operationSource.hasLevelMVar &&
      (← withTransparency .all <| isDefEq (← inferType retainedSource) (← inferType operationSource)) &&
      (← withTransparency .all <| isDefEq retainedSource operationSource) do
    throwStratum .invalid m!"the binder's retained input object differs from its complete declared source"
  Trace.alias (← read).trace retainedSource operationSource
  let retainedTarget ← semanticObject Y
  let operationTarget ← instantiateMVars target
  unless !operationTarget.hasMVar && !operationTarget.hasLevelMVar &&
      (← withTransparency .all <| isDefEq (← inferType retainedTarget) (← inferType operationTarget)) &&
      (← withTransparency .all <| isDefEq retainedTarget operationTarget) do
    throwStratum .invalid m!"the binder's retained output object differs from its complete declared target"
  Trace.alias (← read).trace retainedTarget operationTarget
  let (.object d .., .object y ..) := (D, Y) | unreachable!
  let bodyMap ← callableMap category d y bodyMap
  return (operation, M, .morphism bodyMap d y category (some (D, Y)), Y)

/-- One generic reading rule for every registered binder; candidate trials cannot emit traces
or retain metavariable assignments. Absent evidence never chooses another interpretation. -/
partial def binder (scope : Scope) (token : String) (boundName : Name)
    (arguments : Array Syntax) (body : Syntax) (ambient? : Option Value) : M Value := do
  let state ← registryState
  let rows := state.binders.filter (·.token == token)
  -- Share only an identical, context-free reading requested by every candidate. With
  -- one argument no earlier parameter assignment can change its expected context.
  -- Contextual readings and dependent multi-argument readings retain their usual path.
  let sharedArgument? ← if arguments.size == 1 && !rows.isEmpty && (← rows.allM fun row =>
      parameterTrial do
        let constant ← mkConstWithFreshMVarLevels row.operation
        let (params, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
        let explicit := (params.zip infos).filterMap fun (p, i) =>
          if i.isExplicit then some p else none
        let some parameter := explicit.back? | return false
        let expected ← instantiateMVars (← inferType parameter)
        if let some (_, target) := homEnds? (← whnfR expected) then
          return (← instantiateMVars target).hasMVar
        return true) then
      some <$> eval scope arguments[0]!
    else pure none
  -- A sole registered row needs no speculative reading: the selected reading below checks its
  -- complete dependent signature. Multiple rows still require isolated trials for uniqueness.
  let row ← match rows with
  | #[row] => pure row
  | _ => do
    let mut candidates := #[]
    for row in rows do
      if ← parameterCompatible (do
          discard <| binderReading scope row boundName arguments body ambient? sharedArgument?
          pure true) then
        candidates := candidates.push row
    match candidates with
    | #[row] => pure row
    | #[] => throwStratum .invalid m!"no registered binder `{token}` reads these arguments and body"
    | _ => throwSemanticAmbiguity m!"several registered binders `{token}` read these arguments and body"
  let (operation, M, bodyMap, Y) ←
    binderReading scope row boundName arguments body ambient? sharedArgument?
  let admitted ← admit M bodyMap
  let .object _ category _ _ _ := Y | unreachable!
  let result ← applyFamily row.operation category #[admitted] (some Y) (application := some operation)
    (callableAddress := some row.id.raw)
  let .morphism body domain _ _ _ := bodyMap | unreachable!
  let .element admittedMap _ := admitted | unreachable!
  let .element resultMap _ := result | unreachable!
  let infos ← forallTelescopeReducing (← getConstInfo row.operation).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let parameters := (operation.getAppArgs.zip infos).filterMap fun (p, info) =>
    if info.isExplicit then some p else none
  Trace.record (← read).trace resultMap
    (.binder row.id parameters domain body admittedMap)
  return result

/-- `{a₀, a₁, …, ...}`: the image of `k ↦ a₀ + d k` on `ℕ`, `d = a₁ - a₀`. -/
partial def progression (scope : Scope) (xs : Array Syntax) : M Value := do
  let numerals ← xs.mapM fun x => do
    let .nat n ← eval scope x | throwStratum .invalid m!"a progression `…, ...` is of numerals"
    return n
  let (some a, some b) := (numerals[0]?, numerals[1]?)
    | throwStratum .invalid m!"a progression `…, ...` begins with two numerals"
  unless a ≤ b do throwStratum .invalid m!"a progression `…, ...` in ℕ increases"
  let d := b - a
  unless (numerals.toList.zip numerals.toList.tail).all (fun (x, y) => y = x + d) do
    throwStratum .invalid m!"`{numerals.toList}, ...` is not an arithmetic progression"
  let k := mkIdent `«progression index»
  let (a, d) := (Syntax.mkNumLit (toString a), Syntax.mkNumLit (toString d))
  let e ← `(cas_term| $a:num + $d:num · $k:ident)
  imageOf scope e `«progression index» (← object (← registryState) "ℕ" #[] none)

/-- Explicit action dispatch considers every registered operation and morphism with that
surface name at the complete actual input types. No registration order selects an action. -/
partial def registeredAction (a b : Value) (ambient? : Option Value := none) : M Value := do
  let state ← registryState
  let target? := ambient?.orElse fun _ => match b with
    | .element _ X => some X
    | _ => none
  let operationApplies ← match target? with
    | some target => parameterCompatible do
        discard <| applyOperation "•" #[a, b] target
        pure true
    | none => pure false
  let mut morphisms : Array MorphismEntry := #[]
  for row in state.morphisms.filter (·.name == "•") do
    let some category := state.categories.find? (·.id == row.category) | continue
    if ← parameterCompatible (do
        discard <| applyFamily row.declaration category #[a, b] target? (callableAddress := some row.id.raw)
        pure true) then
      morphisms := morphisms.push row
  if operationApplies && !morphisms.isEmpty || morphisms.size > 1 then
    throwSemanticAmbiguity m!"several complete registered actions take these operands"
  if operationApplies then return ← applyOperation "•" #[a, b] target?.get!
  if let some row := morphisms[0]? then
    let some category := state.categories.find? (·.id == row.category) | unreachable!
    return ← applyFamily row.declaration category #[a, b] target? (callableAddress := some row.id.raw)
  throwStratum .invalid m!"no registered action takes these complete operands"

/-- The juxtaposition `a b`: their product in a set both are in (`(1/2)x²`), else the registered
action `•` of `a` on `b` (`(6x + 1) dx`), else the registered application of `a` (`M v`). -/
partial def juxtapose (a b : Value) (ambient? : Option Value) : M Value := do
  let sets := #[a, b].filterMap fun | .element _ X => some X | _ => none
  if #[a, b].all (fun | .element .. | .nat _ => true | _ => false) then
    let inAmbient ← match ambient? with
      | some X => do
          if ← sets.allM fun Y => return (← coercionMap Y X).isSome then pure (some X) else pure none
      | none => pure none
    let common ← match inAmbient with
      | some X => pure (some X)
      | none =>
          if sets.isEmpty then
            some <$> notationObject "literal.integral.domain"
          else commonSet? sets
    if let some X := common then
      if ← parameterCompatible (do
          discard <| applyOperation "·" #[← coerceTo a X, ← coerceTo b X] X
          pure true) then
        return ← applyOperation "·" #[← coerceTo a X, ← coerceTo b X] X
  -- The registered action `•` of `a`'s set on `b`'s, or the registered application of `a`'s set
  -- (a matrix on a vector): whichever takes these operands' sets; both is an ambiguity.
  let acts ← parameterCompatible do
    discard <| registeredAction a b ambient?
    pure true
  let application? ← applicationOf? a
  let applies ← match application? with
    | some (application, category, _, address) => parameterCompatible do
        discard <| applyFamily application category #[a, b] (callableAddress := some address)
        pure true
    | none => pure false
  match acts, applies, application? with
  | true, false, _ => registeredAction a b ambient?
  | false, true, some (application, category, _, address) =>
      applyFamily application category #[a, b] (callableAddress := some address)
  | true, true, _ => throwSemanticAmbiguity m!"`a b` is both the action `•` and an application"
  | _, _, _ => throwStratum .invalid m!"`a b`: no registered product, action or application \
      takes these operands"

/-- The element `declaration params : 1 ⟶ X` of a family of elements, its parameters unified from
`X` (the zero of `Kⁿ` from `K` and `n`). -/
partial def zeroElement (declaration : Name) (X : Value) : M Expr := do
  let .object x category _ _ _ := X | throwStratum .invalid m!"an element is of a named set"
  let c ← mkConstWithFreshMVarLevels declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, target) := homEnds? type | throwStratum .invalid m!"{declaration} is not an element"
  unless ← isDefEq target (← semanticObject X) do
    throwStratum .invalid m!"{declaration} does not land in this set"
  synthesizeInstances args infos
  let value ← instantiateMVars (mkAppN c args)
  if value.hasMVar then throwStratum .invalid m!"{declaration} is not determined by its set"
  let .object one .. ← oneObject | unreachable!
  homIn (← quoteExpr value) one x category

/-- Whether the family of elements `declaration : ∀ params, 1 ⟶ Y` lands in the set `X`. -/
partial def familyLandsIn (declaration : Name) (X : Value) : M Bool := do
  let c ← mkConstWithFreshMVarLevels declaration
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, target) := homEnds? type | return false
  let x ← semanticObject X
  let check : TermElabM Bool := withoutModifyingState (isDefEq target x)
  check

/-- Whether the family `declaration` takes the elements `elements` (their sets, or sets included in
them along a domain's inclusion, unify with its operands), decided without applying it. -/
partial def familyTakes (declaration : Name) (elements : Array Value) : M Bool := do
  let c ← mkConstWithFreshMVarLevels declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType c)
  let some (source, _) := homEnds? type | return false
  -- A supplied point of a product-valued data object is one whole operand.
  -- Only two supplied operands request the product's two source factors.
  let sources ← if elements.size == 2 then
    match (← whnfR source).getAppFn.constName?, (← whnfR source).getAppArgs with
    | some ``Prod, #[x, y] => pure #[x, y]
    | _, _ => pure #[source]
  else pure #[source]
  unless sources.size == elements.size do return false
  let mut operandSets : Array (Expr × Option Expr) := #[]
  for v in elements do
    let .element _ A := v | return false
    operandSets := operandSets.push (← semanticObject A, (← inclusionOut? A).map (·.2))
  let check : TermElabM Bool := withoutModifyingState do
    for (set, (a, b?)) in sources.zip operandSets do
      if ← isDefEq set a then continue
      let some b := b? | return false
      unless ← isDefEq set b do return false
    -- Its instance arguments exist at these sets (an algebra structure for an evaluation).
    for (a, i) in args.zip infos do
      unless i.isInstImplicit do continue
      if (← instantiateMVars a).isMVar then
        let type ← instantiateMVars (← inferType a)
        if type.hasMVar then continue
        let some inst ← synthInstance? type | return false
        unless ← isDefEq a inst do return false
    return true
  check

/-- `p + Y` for a named set `Y` included in the set `X` of `p`: the coset `{p + c | c ∈ Y}`, the
image of `c ↦ p + c` (at the stage `Y`). -/
partial def cosetOf (p Y : Value) : M Value := do
  let .element h X := p | throwStratum .invalid m!"a coset `p + Y` is of an element `p`"
  let some coercion ← coercionMap Y X
    | throwStratum .invalid m!"`+`: the set is not included in the set of the element"
  let ι ← match coercion with
    | some ι => pure ι
    | none => identityAt Y
  let sum ← withReader (fun ctx => { ctx with stage := some Y }) do
    let constant ← throughTerminal Y h
    applyOperation "+" #[.element constant X, .element ι X] X
  let .element s _ := sum | throwStratum .invalid m!"`+` of elements is an element"
  imageOfMap s Y X

/-- The generator `v` that the name `dv` is the differential of, when `v` is bound to one. -/
partial def differentialVariable? (n : Name) : M (Option Value) := do
  let some v := differentialOf? n | return none
  let some g := (← read).bound.lookup v | return none
  let .element _ (.object _ _ (some (entry, _)) _ _) := g | return none
  return if entry.generator.isSome then some g else none

/-- `d/dv : R[v] → R[v]`, the registered `derivative` at the ring of the generator `g`. -/
partial def derivativeAt (g : Value) : M Value := do
  let state ← registryState
  let .element _ P@(.object p category (some (_, params)) _ _) := g
    | throwStratum .invalid m!"`d/dv` is along a variable"
  let some entry := state.morphisms.find? (·.name == "derivative")
    | throwStratum .invalid m!"no registered derivative"
  let h ← homIn (← `($(mkCIdent entry.declaration) $(← typedParamTerms entry.declaration params)*)) p p category
  let h ← retainNamedMorphism entry h
  return .morphism h p p category (some (P, P))

/-- `a / b`: the registered division `M × Mˣ → M`, `(a, u) ↦ a u⁻¹`, in the enclosing set `M`,
else the set of `a`, else the monoid of the unit `b`. The divisor is a unit of `M`: an element of
`Mˣ` already (formed there, `x in Mˣ`), or a numeral, formed in `Mˣ` with the proposition that it
is a unit decided when the statement is read (`2 ∈ ℚˣ`; `2 ∉ ℤˣ`, so `1/2` is not a term of `ℤ`).
Any other divisor is not in the domain: it is never admitted here because division needs it. -/
partial def divide (a b : Value) (ambient? : Option Value := none) : M Value := do
  let state ← registryState
  let unitsOf? (Y : Value) : M (Option Value) := do
    let .object _ category (some (entry, _)) _ _ := Y | return none
    unless entry.admission.isSome do return none
    let some (_, m) ← inclusionOut? Y | return none
    return some (← inclusionTargetValue Y m category)
  let K ← match ambient?, a, b with
    | some K, _, _ | none, .element _ K, _ => pure K
    | none, _, .element _ Y => pure ((← unitsOf? Y).getD Y)
    | none, _, _ => notationObject "literal.integral.domain"
  applyNamed state "/" #[← toElement (← coerceTo a K) K, b] (some K)

/-- `X - Y` for named sets `Y ⊆ X`: the complement in `𝒫(X)` of the image of the registered
inclusion `Y ↪ X`, `univ \ ι(Y)` with `univ` the transpose of `X → 1 → Ω`. -/
partial def complementOf (X Y : Value) : M Value := do
  let state ← registryState
  let .object _ category (some (super, _)) _ _ := X
    | throwStratum .invalid m!"a complement is of named sets"
  let .object _ _ (some (sub, _)) _ _ := Y | throwStratum .invalid m!"a complement is of named sets"
  let some chain := inclusionChain state sub.id super.id
    | throwStratum .invalid m!"no registered inclusion of {sub.name} in {super.name}"
  let po ← powerObjectIn state CategoryId.sets
  let image ← imageOfMap (← inclusionMap chain Y) Y X
  let P ← powerSetOf X
  let .object p _ _ _ _ := P | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let some omega := state.objects.find? (·.id == po.omega) | unreachable!
  let .object ω .. ← object state omega.name #[] none | unreachable!
  let truth ← homIn (mkCIdent po.truth) one ω category
  let everything ← throughTerminal X truth
  let univ ← homIn (← `($(mkCIdent po.transpose) $(← paramTerms #[X])* $(← quoteExpr everything)))
    one p category
  applyOperation "\\" #[.element (← staged univ) P, image] P

/-- The registered object a term names and its numeral parameters, without realizing it. -/
partial def namedObject (scope : Scope) (stx : Syntax) : M (ObjectEntry × Array Nat) := do
  let state ← registryState
  let numerals (args : Array Syntax) : M (Array Nat) := args.mapM fun a => do
    let .nat n ← eval scope a | throwStratum .invalid m!"a parameter is a numeral"
    return n
  match stx with
  | `(cas_term| ($t)) => namedObject scope t
  | `(cas_term| $t in $c:ident) =>
      let (entry, params) ← namedObject scope t
      let some category := state.categories.find? (·.name == c.getId.toString)
        | throwStratum .invalid m!"no registered category is named {c.getId}"
      return (← objectNamed state entry.name (some category), params)
  | `(cas_term| $x:ident) =>
      if let some t := scope.get? x.getId then return ← namedObject scope t
      return (← objectNamed state x.getId.toString none, #[])
  | `(cas_term| $f:ident($args,*)) =>
      return (← objectNamed state f.getId.toString none, ← numerals args.getElems)
  | `(cas_term| ℤ / $n) => return (← objectNotation state "ℤ/", ← numerals #[n])
  | `(cas_term| (ℤ / $n) ^ $k) =>
      return (← objectNotation state "(ℤ/)^", ← numerals #[n, k])
  | _ =>
      match stx.getKind == ``casAtom, stx.find? (·.isAtom) with
      | true, some atom => return (← objectNamed state atom.getAtomVal none, #[])
      | _, _ => throwStratum .invalid m!"{shown stx} does not name a registered object"

/-- The morphism `{x ↦ y, …} : s → t` with that graph, by the registered graph literal of the
category of `s` and `t`, whose elements are the registered element literals of `s` and `t`. -/
partial def graph (scope : Scope) (pairs : Array Syntax) (s t : Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let a ← eval scope s category?
  let .object _ category _ _ _ := a | throwStratum .invalid m!"the domain of a graph is an object"
  let b ← eval scope t (some category)
  let numerals ← pairs.mapM fun pair => do
    -- A pair `x ↦ y`: its arguments 0 and 2.
    let (.nat x, .nat y) := (← eval scope pair[0], ← eval scope pair[2])
      | throwStratum .invalid m!"an element literal is a numeral"
    return (x, y)
  graphOf a b numerals

/-- Read nonnumeric operands once to retain their selected domains. An enclosing domain
supplies their operation only when declared coercions carry all of them there; otherwise their
own common domain determines the operation. Numeric operands are then read in that domain. -/
partial def operands (scope : Scope) (args : Array Syntax) (ambient? : Option Value) :
    M (Array Value × Value) := do
  let ambient? ← ambient?.mapM carrierObject
  let mut known : Array (Option Value) := args.map fun _ => none
  let mut sets : Array Value := #[]
  for i in [:args.size] do
    unless numeric args[i]! do
      let value ← eval scope args[i]! none ambient?
      known := known.set! i (some value)
      if let .element _ domain := value then sets := sets.push domain
  let ambient? ← match ambient? with
    | some ambient =>
        if ← sets.allM (fun domain => return (← coercionMap domain ambient).isSome) then
          pure (some ambient)
        else pure none
    | none => pure none
  let domain ← match ambient? with
    | some ambient => pure ambient
    | none => match ← commonSet? sets, sets[0]? with
      | some common, _ | none, some common => pure common
      | none, none =>
          match ← numeralSet (mkNullNode args) none with
          | some selected => pure selected
          | none => notationObject "literal.integral.domain"
  let values ← (args.zip known).mapM fun
    | (_, some value) => pure value
    | (arg, none) => eval scope arg none (some domain)
  return (← values.mapM (coerceTo · domain), domain)

/-- The registered operation `name` on the operands `args`. -/
partial def operate (scope : Scope) (name : String) (args : Array Syntax)
    (ambient? : Option Value) : M Value := do
  let (elements, X) ← operands scope args ambient?
  applyOperation name elements X

/-- An accepted terminal-source comparison for a global operation or admission point. -/
partial def operationPointComparison (source : Expr) : M (Option Expr) := do
  let state ← registryState
  let one ← semanticObject (← oneObject)
  let mut candidates : Array (PresentationComparisonEntry × Expr × Bool) := #[]
  for entry in state.presentations do
    for inverse in #[false, true] do
      let field := if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom
      let applicable ← parameterCompatible do
        let iso ← instantiateFresh entry.declaration
        let hom ← mkAppM field #[iso]
        let some (left, right) := homEnds? (← inferType hom) | return false
        unless ← isDefEq left one <&&> isDefEq right source do return false
        let iso ← instantiateMVars iso
        return !iso.hasMVar && !iso.hasLevelMVar && (← isTypeCorrect iso)
      unless applicable do continue
      let iso ← instantiateFresh entry.declaration
      let hom ← mkAppM field #[iso]
      let some (left, right) := homEnds? (← inferType hom) | unreachable!
      unless ← isDefEq left one <&&> isDefEq right source do unreachable!
      candidates := candidates.push (entry, ← instantiateMVars iso, inverse)
  match candidates.toList with
  | [] => return none
  | [(entry, iso, inverse)] =>
      return some (← Semantic.presentationArrow entry iso inverse (← read).trace)
  | _ => throwSemanticAmbiguity m!"several admitted terminal comparisons determine the global point"

/-- A numeral of a retained full source, forwarded along its actual structural action.
All source numeral structures are checked before choosing a serialization representative. -/
partial def forwardNumeral (k : Nat) (X : Value) : M (Option Value) := do
  let .object carrier category _ selected _ := X | return none
  let some target := selected | return none
  let .object targetHandle targetCategory .. := target | return none
  let state ← registryState
  let one ← semanticObject (← oneObject)
  let recorder ← Trace.new
  let collect (value : Value) : M (Array (Value × Array EdgeRef × Array Expr)) := do
    let .object handle currentCategory _ _ data := value | return #[]
    unless currentCategory.id == targetCategory.id &&
        (← withTransparency .all <| isDefEq handle targetHandle) do return #[]
    let some (originals, source, route, _, arguments) := data | return #[]
    let .object sourceHandle .. := source | return #[]
    let (image, applications) ← retainedActions state sourceHandle route arguments
    unless ← withTransparency .all <| isDefEq image targetHandle do
      throwStratum .invalid m!"the retained numeral source does not give its full target"
    let mut result := if route.isEmpty then #[] else #[(source, route, applications)]
    for original in originals do
      result := result ++ (← forwardNumeralSources target original)
    return result
  let witnesses ← collect target
  let mut candidates : Array (Value × Array EdgeRef × Array Expr × Expr × Value) := #[]
  for (source, route, applications) in witnesses do
    let .object sourceHandle sourceCategory sourceOrigin _ _ := source | continue
    unless state.numerals.any (·.over == some sourceCategory.id) do continue
    let sourceCarrier ← carrierObject source
    let .object sourceType .. := sourceCarrier | continue
    unless ← withTransparency .all <| isDefEq sourceType carrier do continue
    let sourceNumerals := state.numerals.filter (·.over == some sourceCategory.id)
    let some numeral ← numeralIn { state with numerals := sourceNumerals }
        k one sourceType #[(sourceCategory.id, sourceHandle)]
      | continue
    if let some (entry, params) := sourceOrigin then
      let named ← Semantic.object entry (← typedParamTerms entry.declaration params) none
      unless entry.category == sourceCategory.id && !named.hasMVar && !named.hasLevelMVar &&
          (← isDefEq (← inferType named) (← inferType sourceHandle)) &&
          (← withTransparency .all <| isDefEq named sourceHandle) do
        throwStratum .invalid m!"the numeral's named source differs from its full structure"
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let actualParams := (named.getAppArgs.zip infos).filterMap fun (arg, info) =>
        if info.isExplicit then some arg else none
      Trace.record (some recorder) sourceHandle (.object entry.id actualParams)
    let point ← homIn (← quoteExpr numeral) one sourceType category
    Trace.record (some recorder) point (.elementNumeral k sourceType sourceHandle)
    let hom ← withReader (fun context => { context with trace := some recorder }) do
      staged point
    unless !hom.hasMVar && !hom.hasLevelMVar && (← isTypeCorrect hom) do
      throwStratum .invalid m!"the retained source numeral is not a closed typed point"
    candidates := candidates.push (source, route, applications, hom, sourceCarrier)
  let some (source, route, applications, point, sourceCarrier) := candidates[0]? | return none
  let .object sourceHandle sourceCategory .. := source | unreachable!
  for (other, _, _, otherPoint, _) in candidates do
    let .object otherHandle otherCategory .. := other | unreachable!
    unless sourceCategory.id == otherCategory.id &&
        (← isDefEq (← inferType sourceHandle) (← inferType otherHandle)) &&
        (← withTransparency .all <| isDefEq sourceHandle otherHandle) &&
        (← withTransparency .all <| isDefEq point otherPoint) do
      throwSemanticAmbiguity m!"distinct retained numeral structures determine this point"
  let some (domain, _) := homEnds? (← inferType point) | unreachable!
  let typed ← homIn (← quoteExpr point) domain carrier category
  let hom ← mkAppM ``id #[typed]
  if hom == point then
    throwError "the forward point wrapper did not retain a distinct source construction"
  unless ← withTransparency .all <| isDefEq hom point do
    throwStratum .invalid m!"the forward structure changes its numeral point"
  if let some trace := (← read).trace then
    let entries ← recorder.get
    trace.modify fun current => entries.fold (fun result value node => result.insert value node) current
  Trace.record (← read).trace hom (.pointView sourceHandle targetHandle route applications point)
  let retainedPoints := candidates.map fun (_, _, _, point, sourceCarrier) =>
    Value.element point sourceCarrier
  let X := match X with
    | .object handle category origin selected (some (originals, source, route, alternatives, args)) =>
        Value.object handle category origin selected
          (some (originals ++ retainedPoints, source, route, alternatives, args))
    | .object handle category origin selected none =>
        Value.object handle category origin selected
          (some (retainedPoints, target, #[], #[], #[]))
    | _ => X
  return some (.element hom X)

/-- Traverse equivalent full target views while retaining each actual source action. -/
partial def forwardNumeralSources (target value : Value) :
    M (Array (Value × Array EdgeRef × Array Expr)) := do
  let .object targetHandle targetCategory .. := target | return #[]
  let .object handle category _ _ data := value | return #[]
  unless category.id == targetCategory.id &&
      (← withTransparency .all <| isDefEq handle targetHandle) do return #[]
  let some (originals, source, route, _, arguments) := data | return #[]
  let .object receiver .. := source | return #[]
  let (image, applications) ← retainedActions (← registryState) receiver route arguments
  unless ← withTransparency .all <| isDefEq image targetHandle do
    throwStratum .invalid m!"a numeral witness has a different full target"
  let mut result := if route.isEmpty then #[] else #[(source, route, applications)]
  for original in originals do
    result := result ++ (← forwardNumeralSources target original)
  return result

/-- A declaration-owned coordinate may be anonymous while its context independently supplies
the complete numeral owner. Close that owner before comparing its carrier with the fixed
coordinate target. All aliases of the same full owner remain in the result's context. -/
partial def contextualNumeral (k : Nat) (X : Value) : M (Option Value) := do
  let .object carrier category none _ _ := X | return none
  if carrier.hasMVar || carrier.hasLevelMVar then return none
  let state ← registryState
  let one ← semanticObject (← oneObject)
  let witnesses := sourceParameterValues X
  let mut candidates : Array (Value × Expr × Expr × Expr × Std.HashMap Expr Node) := #[]
  for row in state.numerals do
    let some owner := row.over | continue
    for supplied in witnesses do
      let candidate? ← try parameterTrial do
        let recorder ← Trace.new
        withReader (fun context => { context with trace := some recorder }) do
          let constant ← mkConstWithFreshMVarLevels row.declaration
          let (args, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
          let explicit := (args.zip infos).filterMap fun (arg, info) =>
            if info.isExplicit then some arg else none
          let some parameter := explicit[0]? | return none
          unless ← bindSelectedReceiver explicit 0 supplied (some owner) do return none
          let actual ← instantiateMVars parameter
          let actualType ← instantiateMVars (← inferType actual)
          if actual.hasMVar || actual.hasLevelMVar || actualType.hasMVar ||
              actualType.hasLevelMVar || !(← isTypeCorrect actual) then return none
          -- The target is consulted only after the complete independently supplied owner
          -- has closed. Bare carrier equality cannot fill any field of that owner.
          let some numeral ← numeralIn { state with numerals := #[row] }
              k one carrier #[(owner, actual)] | return none
          let closedPoint ← homIn (← quoteExpr numeral) one carrier category
          Trace.record (some recorder) closedPoint (.elementNumeral k carrier actual)
          let point ← staged closedPoint
          unless !point.hasMVar && !point.hasLevelMVar && (← isTypeCorrect point) do return none
          return some (supplied, actual, numeral, point, ← recorder.get)
      catch error =>
        if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
      if let some candidate := candidate? then candidates := candidates.push candidate
  let some (_, owner, numeral, point, _) := candidates[0]? | return none
  for (_, otherOwner, otherNumeral, _, _) in candidates do
    unless ← parameterTrial (withTransparency .all <|
        isDefEq (← inferType owner) (← inferType otherOwner) <&&> isDefEq owner otherOwner) do
      throwSemanticAmbiguity m!"several complete numeral owners determine this coordinate"
    unless ← sameOperationApplication numeral otherNumeral do
      throwSemanticAmbiguity m!"several full numeral applications determine this coordinate"
  if let some trace := (← read).trace then
    for (_, _, _, _, records) in candidates do
      trace.modify fun current => records.fold
        (fun result term node => result.insert term node) current
  return some (.element point (retainObjectContext X (candidates.map (·.1))))

/-- A numeral admitted through every parameter-free registered domain whose admission has the
anonymous target as its actual endpoint. The endpoint remains anonymous; the admission morphism,
rather than a carrier alias, supplies the point, and all applicable admissions must agree. -/
partial def anonymousAdmissionPoint (k : Nat) (X : Value) : M (Option Value) := do
  let .object target category none none _ := X | return none
  let state ← registryState
  let mut candidates : Array (ObjectId × Expr) := #[]
  for entry in state.objects do
    unless entry.category == category.id && entry.admission.isSome do continue
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    let (_, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
    unless infos.all (!·.isExplicit) do continue
    let candidate? ← try
      parameterTrial do
        let D ← object state entry.name #[] (some category)
        let .object _ _ (some (actual, parameters)) _ _ := D | return none
        unless actual.id == entry.id && parameters.isEmpty do return none
        unless ← withTransparency .all <| isDefEq (← semanticObject D) target do return none
        let some (_, base) ← inclusionOut? D | return none
        let B ← inclusionTargetValue D base category
        let .element point _ ← admit D (← toElement (.nat k) B) | return none
        let some (_, endpoint) := homEnds? (← inferType point) | return none
        unless ← withTransparency .all <| isDefEq endpoint target do return none
        return some point
    catch error =>
      if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
    if let some point := candidate? then candidates := candidates.push (entry.id, point)
  let some (_, point) := candidates[0]? | return none
  for (_, other) in candidates do
    unless ← withTransparency .all <| isDefEq point other do
      throwSemanticAmbiguity m!"distinct registered admissions determine this anonymous point"
  -- Re-run the unique/equivalent construction with tracing enabled.
  for (id, _) in candidates do
    let some entry := state.objects.find? (·.id == id) | unreachable!
    if ← parameterCompatible (do
        let D ← object state entry.name #[] (some category)
        let .object _ _ (some (actual, parameters)) _ _ := D | return false
        unless actual.id == entry.id && parameters.isEmpty do return false
        unless ← withTransparency .all <| isDefEq (← semanticObject D) target do return false
        let some (_, base) ← inclusionOut? D | return false
        let B ← inclusionTargetValue D base category
        let .element admitted _ ← admit D (← toElement (.nat k) B) | return false
        withTransparency .all <| isDefEq admitted point) then
      let D ← object state entry.name #[] (some category)
      let some (_, base) ← inclusionOut? D | unreachable!
      let B ← inclusionTargetValue D base category
      let .element admitted _ ← admit D (← toElement (.nat k) B) | unreachable!
      return some (.element admitted X)
  throwError "an applicable anonymous admission disappeared after selection"

/-- A named set's registered numeral, determined before a numeric token is interpreted as
an inherited nullary operation. The named refinement fixes the complete numeral owner;
the token alone may not replace its value with the unit of another structural view. -/
partial def registeredNamedNumeral (k : Nat) (X : Value) : M (Option Value) := do
  let .object x category (some (entry, params)) _ _ := X | return none
  -- An admitted domain obtains its point through its declared inclusion and evidence.
  if entry.admission.isSome then return none
  let state ← registryState
  let one ← semanticObject (← oneObject)
  let mut refinements : Array (CategoryId × Expr) := #[]
  let directNumerals := state.numerals.filter fun numeral =>
    numeral.over.any fun over => state.objects.any fun candidate =>
      candidate.category == over && refinesObject state candidate entry.id
  let numeralRows := if directNumerals.isEmpty then state.numerals else directNumerals
  for numeral in numeralRows do
    let some over := numeral.over | continue
    if refinements.any (·.1 == over) then continue
    let some target := state.categories.find? (·.id == over) | continue
    let family ← instantiateFresh target.declaration
    let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
    if ← parameterCompatible (do
        discard <| typedParameter expected X
        pure true) then
      refinements := refinements.push (over, ← typedParameter expected X)
  let some numeral ← numeralIn { state with numerals := numeralRows }
      k one (← semanticObject X) refinements | return none
  let X ← match state.numerals.find? (·.declaration == numeral.getAppFn.constName?.getD .anonymous) with
    | some numeralRow => match numeralRow.over with
      | some over => do
          let some (_, actual) := refinements.find? (·.1 == over) | pure X
          let some sourceCategory := state.categories.find? (·.id == over) | pure X
          let selected ← structuredParameterView X actual sourceCategory
          let .object _ _ _ _ originalView := X | unreachable!
          pure (Value.object x category (some (entry, params)) (some selected) originalView)
      | none => pure X
    | none => pure X
  let .object oneHandle .. ← oneObject | unreachable!
  let point ← homIn (← quoteExpr numeral) oneHandle x category
  let chosen := match X with
    | .object _ _ _ (some selected) _ => selected
    | _ => X
  Trace.record (← read).trace point
    (.elementNumeral k (← semanticObject X) (← semanticObject chosen))
  let hom ← staged point
  return some (.element hom X)

/-- `v` as an element of the set `X`: an element already, or the element a numeral names: its
registered numeral in `X` (`numeralIn`); in a set of constants from its parameter `P` without
numerals of its own, the image of the numeral of `P`; in a domain `D ↪ B` with an admission
(`Mˣ ↪ M`), the numeral of `B` admitted, its evidence established. -/
partial def toElement (v : Value) (X : Value) : M Value := do
  match v with
  | .element .. => coerceTo v (← carrierObject X)
  | .nat k =>
      let state ← registryState
      let X ← carrierObject X
      let .object _ category .. := X | unreachable!
      if let some point ← profileReader "numeral forward" (forwardNumeral k X) then
        return point
      -- A complete selected structure supplies a numeral directly, or through an actual
      -- structural action to its registered numeral owner. A matching carrier never supplies
      -- missing structure. Competing inherited numeral constructions must agree as points.
      if let .object carrier _ _ (some chosen@(.object selected selectedCategory ..)) _ := X then
        let directRows := state.numerals.filter (·.over == some selectedCategory.id)
        let owners := if !directRows.isEmpty then #[selectedCategory.id] else
          (state.numerals.filterMap (·.over)).toList.eraseDups.toArray
        let one ← semanticObject (← oneObject)
        let mut points : Array Expr := #[]
        for owner in owners do
          let some ownerCategory := state.categories.find? (·.id == owner) | continue
          let point? ← optionalReading do
            let family ← instantiateFresh ownerCategory.declaration
            let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
            let actual ← if owner == selectedCategory.id then pure selected else
              transportedStructure expected chosen (some owner)
            unless ← isDefEq (← inferType actual) expected do
              throwStratum .invalid m!"the selected numeral owner has a different full type"
            let rows := state.numerals.filter (·.over == some owner)
            let some point ← numeralIn { state with numerals := rows } k one carrier #[(owner, actual)]
              | throwStratum .invalid m!"the selected numeral owner has a different carrier"
            return point
          if let some point := point? then points := points.push point
        if let some numeral := points[0]? then
          for point in points do
            unless ← withTransparency .all <| isDefEq point numeral do
              throwSemanticAmbiguity m!"several registered structural numerals give different points"
          let point ← homIn (← quoteExpr numeral) one carrier category
          Trace.record (← read).trace point (.elementNumeral k carrier selected)
          let hom ← staged point
          return .element hom X
      -- A constructor may fix a selected result with no numeral of its own while
      -- retaining the complete source that supplies its points (for example a regular
      -- module and its scalar ring). Keep the selected result; only an independently
      -- closed owner may supply a point at that already fixed carrier.
      if let some point ← profileReader "numeral context" (contextualNumeral k X) then
        return point
      if let some point ← profileReader "numeral registered search" (registeredNamedNumeral k X) then
        return point
      -- A numeric token can also name a registered nullary operation. Its actual
      -- terminal source must have the accepted global-point comparison; the token
      -- alone never invents a general numeral family on the selected structure.
      let pointName := toString k
      if ← profileReader "numeral nullary operation trial" (parameterCompatible do
          let result ← applyOperation pointName #[] X
          return result matches .element ..) then
        return ← applyOperation pointName #[] X
      if let some point := state.morphisms.find? fun morphism =>
          morphism.name == pointName && morphism.category == category.id then
        if let .object _ _ (some (_, parameters)) _ _ := X then
          if ← profileReader "numeral nullary family trial" (parameterCompatible do
              let result ← applyFamily point.declaration category #[] (some X)
                (parameters := parameters) (callableAddress := some point.id.raw)
              return result matches .element ..) then
            return ← applyFamily point.declaration category #[] (some X)
              (parameters := parameters) (callableAddress := some point.id.raw)
        if ← familyLandsIn point.declaration X then
          let hom ← zeroElement point.declaration X
          return .element (← staged hom) X
      if let some point ← anonymousAdmissionPoint k X then return point
      let .object x category (some (entry, params)) _ _ := X
        | throwStratum .invalid m!"a numeral is an element of a named set"
      if entry.admission.isSome then
        let some (_, b) ← inclusionOut? X
          | throwStratum .invalid m!"{entry.name} has an admission and no inclusion"
        let B ← inclusionTargetValue X b category
        return ← admit X (← toElement v B)
      -- A set of constants from its parameter `P` without numerals of its own: the image of
      -- the numeral of `P`.
      if let (some _, some P@(Value.object ..)) :=
          (entry.constants, params.find? (· matches .object ..)) then
        return ← coerceTo (← toElement v P) X
      -- A set that `ℕ` is registered to include into (`ℕ ↪ ℕ ∪ {-∞}`): the image of the
      -- numeral of `ℕ` along that monomorphism.
      if let some naturals := state.objects.find? (fun o => o.name == "ℕ" && o.refines.isNone) then
        if params.isEmpty && (inclusionChain state naturals.id entry.id).isSome then
          let N ← object state "ℕ" #[] none
          return ← coerceTo (← toElement v N) X
      throwStratum .invalid m!"no registered numeral lands in {entry.name}"
  | _ => return v

/-- The explicit arguments of an application of the declaration `declaration`, the
parameters a trace node retains. -/
partial def explicitArguments (declaration : Name) (application : Expr) : M (Array Expr) := do
  let mut e := application.consumeMData
  while e.isAppOfArity ``id 2 || e.isAppOfArity ``Trace.operationResult 3 do
    e := e.appArg!.consumeMData
  let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  return ((e.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none)

/-- The registered inclusion `D ↪ B` out of the named set `D` (`Mˣ ↪ M`, `𝒫_fin(X) ↪ 𝒫(X)`), read
semantically, and `B`. -/
partial def inclusionOut? (D : Value) : M (Option (Expr × Expr)) := do
  let .object _ _ (some (entry, params)) _ _ := D | return none
  let some inclusion := entry.inclusion | return none
  let ι ← instantiateMVars (← elabTermAndSynthesize
    (← `($(mkCIdent inclusion) $(← typedParamTerms inclusion params)*)) none)
  let some (_, b) := homEnds? (← instantiateMVars (← inferType ι))
    | throwStratum .invalid m!"the inclusion of {entry.name} is not a morphism"
  return some (ι, b)

/-- Prefer complete parameters actually occurring in a dependent endpoint. A nested ring
parameter does not replace the selected module whose carrier that endpoint names. -/
partial def endpointSelection? (value : Value) : Option Expr := match value with
  | .object _ _ _ (some (.object actual ..)) _ => some actual
  | .object actual .. => some actual
  | _ => none

partial def endpointWitnesses (endpoint : Expr) (known : Array Value) :
    M (Array Value × Bool) := do
  let occurring := known.filter fun value => (endpointSelection? value).any fun actual =>
    (endpoint.find? (· == actual)).isSome
  let maximal := occurring.filter fun value => !(endpointSelection? value).any fun actual =>
    occurring.any fun other => (endpointSelection? other).any fun container =>
      container != actual && (container.find? (· == actual)).isSome
  return if maximal.isEmpty then (known, true) else (maximal, false)

/-- An endpoint may name a field of a complete supplied object. If that whole object's
carrier is not the endpoint, its retained parameters remain available as independent witnesses.
Every successful reading keeps the ordinary full-selection ambiguity checks. -/
partial def recognizedEndpoint? (state : RegistryState) (endpoint : Expr)
    (category : NamedCategoryEntry) (known : Array Value)
    (fixedParameters : Array Expr := #[]) : M (Option Value) := do
  let mut available := known.flatMap sourceParameterValues
  -- A declaration-owned constructor already fixes the result's identity. Keep every
  -- retained witness for its dependent parameters, even when a parameter's registered
  -- wrapper was reduced in the declaration's signature (`FiniteSubsets (Polynomial R)`).
  -- Syntactic occurrence of the coefficient alone must not discard the supplied ambient.
  if state.objects.any (fun row => row.category == category.id &&
      some row.declaration == endpoint.getAppFn.constName?) then
    return ← optionalReading (recognize state endpoint category known fixedParameters)
  for _ in [:available.size + 1] do
    let (preferred, expandParameters) ← endpointWitnesses endpoint available
    if let some recognized ← optionalReading
        (recognize state endpoint category preferred fixedParameters expandParameters) then
      return some recognized
    if expandParameters then return none
    let rejected := preferred.filterMap endpointSelection?
    let remaining := available.filter fun value =>
      !(endpointSelection? value).any rejected.contains
    if remaining.size == available.size then return none
    available := remaining
  return none

/-- A declared field path, without reducing its complete owner. Projection functions and
primitive projections denote the same path; no carrier equality identifies the owner. -/
partial def objectFieldPath (env : Environment) (term : Expr) (owners : Array Expr := #[]) :
    M (Expr × Array (Name × Nat)) := do
  let term := term.consumeMData
  if owners.contains term then return (term, #[])
  if term.isAppOfArity ``id 2 then return ← objectFieldPath env term.appArg! owners
  match term with
  | .proj structureName index owner =>
      let (root, fields) ← objectFieldPath env owner owners
      return (root, fields.push (structureName, index))
  | _ =>
      match term.getAppFn.constName? with
      | some name =>
          match env.getProjectionFnInfo? name, env.getProjectionStructureName? name with
          | some info, some structureName =>
              let arguments := term.getAppArgs
              if arguments.size == info.numParams + 1 then
                let (root, fields) ← objectFieldPath env arguments[info.numParams]! owners
                return (root, fields.push (structureName, info.i))
              else return (term, #[])
          | _, _ =>
              if let some expanded ← withReducible <| unfoldDefinition? term then
                if expanded != term then return ← objectFieldPath env expanded owners
              return (term, #[])
      | none => return (term, #[])

/-- Complete supplied owners occurring through proper projections in a declaration body.
A registered full object may repackage fields into a bundle instead of returning one projection. -/
partial def objectFieldOwners (env : Environment) (term : Expr) (owners : Array Expr) :
    M (Array Expr) := do
  let term := term.consumeMData
  if owners.contains term then return #[]
  let (owner, fields) ← objectFieldPath env term owners
  if !fields.isEmpty && owners.contains owner then return #[owner]
  if let some expanded ← withReducible <| unfoldDefinition? term then
    if expanded != term then return ← objectFieldOwners env expanded owners
  let parts := match term with
    | .app function argument => #[function, argument]
    | .proj _ _ owner => #[owner]
    | _ => #[]
  let mut result := #[]
  for part in parts do
    for owner in (← objectFieldOwners env part owners) do
      unless result.contains owner do result := result.push owner
  return result

/-- Retain a registered full object construction from fields of an explicitly supplied owner.
The accepted full construction must occur in the endpoint; only then is its carrier checked.
No owner or complete structure is inferred from equality of underlying carriers. -/
partial def declaredFieldEndpoint? (state : RegistryState) (endpoint : Expr)
    (known : Array Value) : M (Option Value) := do
  let env ← getEnv
  let mut owners : Array Expr := #[]
  for supplied in known.flatMap sourceParameterValues do
    let supplied := match supplied with
      | .object _ _ _ (some selected) _ => selected
      | _ => supplied
    let .object actual actualCategory .. := supplied | continue
    if actualCategory.id == CategoryId.sets || actual.hasMVar then continue
    unless owners.contains actual do owners := owners.push actual
  if owners.isEmpty then return none
  let selections ← IO.mkRef (#[] : Array (Expr × Array Expr))
  endpoint.forEach' fun part => do
    -- The internals of a supplied complete object do not choose a new field owner.
    if owners.contains part then return false
    if part.hasLooseBVars then return true
    let roots ← objectFieldOwners env part owners
    unless roots.isEmpty do
      let type ← whnfR (← inferType part)
      unless type.isSort || type.isForall do
        selections.modify fun found =>
          if found.any (·.1 == part) then found else found.push (part, roots)
    return true
  let selections ← selections.get
  if selections.isEmpty then return none
  let mut found : Array (Expr × NamedCategoryEntry) := #[]
  for row in state.objects do
    if row.category == CategoryId.sets then continue
    let some category := state.categories.find? (·.id == row.category) | continue
    let declaration ← mkConstWithFreshMVarLevels row.declaration
    let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let application := mkAppN declaration arguments
    let some body ← unfoldDefinition? application true | continue
    let receivers ← objectFieldOwners env body arguments
    for receiver in receivers do
      unless (arguments.zip infos).any (fun (argument, info) =>
          info.isExplicit && argument == receiver) do continue
      for actual in owners do
        let candidate? ← parameterTrial do
          unless ← isDefEq (← inferType receiver) (← inferType actual) <&&>
              isDefEq receiver actual do return none
          synthesizeInstances arguments infos
          let candidate ← instantiateMVars application
          let projected ← instantiateMVars body
          if candidate.hasMVar || candidate.hasLevelMVar || !(← isTypeCorrect candidate) then
            return none
          let occurs ← selections.anyM fun (part, roots) => do
            unless roots.contains actual do return false
            parameterTrial <| withTransparency .all <|
              isDefEq (← inferType projected) (← inferType part) <&&> isDefEq projected part
          unless occurs do return none
          let carrier ← carrierObject (.object candidate category none none none)
          unless ← withTransparency .all <| isDefEq (← semanticObject carrier) endpoint do
            return none
          return some candidate
        if let some candidate := candidate? then
          unless found.any (fun (previous, _) => previous == candidate) do
            found := found.push (candidate, category)
  let some (first, category) := found[0]? | return none
  unless found.all (fun (_, other) => other.id == category.id) do
    throwSemanticAmbiguity m!"the declared field has several registered object categories"
  let views ← found.mapM fun (candidate, _) => recognize state candidate category known
  let selected ← match views with
    | #[selectedView] => pure selectedView
    | _ => do
        let evidence ← coalesceSelectedParameterViews (← inferType first) first views
        let (_, _, _, alternatives, _) := evidence
        unless alternatives.isEmpty do
          Trace.record (← read).trace first
            (.parameterEquivalence (← inferType first) first alternatives)
        pure (.object first category none none (some evidence))
  let carrier ← carrierObject selected
  unless ← withTransparency .all <| isDefEq (← semanticObject carrier) endpoint do
    throwStratum .invalid m!"the declared field's registered carrier differs from its endpoint"
  return some carrier

/-- An object endpoint supplied by a checked declaration. Product endpoints are reconstructed
through their registered universal construction, retaining each complete source parameter. -/
partial def declaredEndpointObject (endpoint : Expr) (category : NamedCategoryEntry)
    (known : Array Value) (fixedParameters : Array Expr := #[]) : M Value := do
  let state ← registryState
  let productEndpoint (product : Expr) : M Value := do
    let #[left, right] := product.getAppArgs | unreachable!
    let first ← declaredEndpointObject left category known fixedParameters
    let second ← declaredEndpointObject right category known fixedParameters
    let diagram ← standardDiagram "product" #[first, second]
    let presentation ← limitIn false "product" diagram category
    let apex ← apexOf false presentation
    unless ← isDefEq apex endpoint do
      throwStratum .invalid m!"the declared product endpoint differs from its registered construction"
    Trace.alias (← read).trace presentation apex
    let source := Value.object apex category none none none
    return retainObjectContext
      (.object apex category none none (some (#[first, second], source, #[], #[], #[]))) known
  -- An explicit product in the declaration already supplies its construction. There is
  -- no unknown whole structure to discover by repeatedly trying every component carrier.
  -- A selected object's carrier is recognized first unless the endpoint itself is a product.
  let mut direct := endpoint.consumeMData
  while direct.isAppOfArity ``id 2 do direct := direct.appArg!.consumeMData
  if category.id == CategoryId.sets && direct.isAppOf ``Prod then
    return ← productEndpoint direct
  if category.id == CategoryId.sets then
    if let some projected ← declaredFieldEndpoint? state endpoint known then
      return retainObjectContext projected known
  if let some recognized ← recognizedEndpoint? state endpoint category known fixedParameters then
    return retainObjectContext recognized known
  let reduced ← whnfR endpoint
  if category.id == CategoryId.sets && reduced.isAppOf ``Prod then
    return ← productEndpoint reduced
  unless ← isTypeCorrect endpoint do
    throwStratum .invalid m!"the declared endpoint is outside its actual type"
  return retainObjectContext (.object endpoint category none none none) known

/-- The target of an actual declared inclusion. A function-space target supplies its exact
map domain and codomain; it never borrows a named presentation from a matching carrier. -/
partial def inclusionTargetValue (D : Value) (endpoint : Expr)
    (category : NamedCategoryEntry) : M Value := do
  let state ← registryState
  let known := #[D]
  if let some recognized ← recognizedEndpoint? state endpoint category known then
    return recognized
  let reduced ← whnfR endpoint
  if category.id == CategoryId.sets && reduced.isForall && !reduced.bindingBody!.hasLooseBVars then
    return .homSet (← declaredEndpointObject reduced.bindingDomain! category known)
      (← declaredEndpointObject reduced.bindingBody! category known)
  declaredEndpointObject endpoint category known

/-- Read explicit independent proofs after fixing the actual constrained target and data type. -/
partial def evalInUsing (scope : Scope) (term targetSyntax : Syntax)
    (proofSyntax : Array Syntax) (category? : Option NamedCategoryEntry := none) : M Value := do
  let target ← carrierObject (← eval scope targetSyntax)
  if let .object _ category (some (entry, _)) _ _ := target then
    if entry.admission.isSome then
      let ambient ← match ← inclusionOut? target with
        | some (_, endpoint) => some <$> inclusionTargetValue target endpoint category
        | none => pure none
      let locals ← localGeneratorBindings scope term targetSyntax (ambient.getD target)
      return ← withReader (fun context => { context with bound := locals ++ context.bound }) do
        let value ← eval scope term category? ambient
        let value ← match ambient, value with
          | some source, .nat _ => toElement value source
          | _, _ => pure value
        let proofs ← proofSyntax.mapM fun argument => do
          let proof@(.formalProof _) ← eval scope argument
            | throwStratum .invalid "an admission proof argument is an independent `proof(...)` term"
          pure proof
        admit target value proofs
  let some dataCarrier ← constrainedCarrier? target
    | throwStratum .invalid "explicit point proofs require the selected constrained record interface"
  let locals ← localGeneratorBindings scope term targetSyntax dataCarrier
  withReader (fun context => { context with bound := locals ++ context.bound }) do
    let value ← toElement (← eval scope term category? (some dataCarrier)) dataCarrier
    let proofs ← proofSyntax.mapM fun argument => do
      let .formalProof proofSyntax ← eval scope argument
        | throwStratum .invalid "a constructor proof argument is an independent `proof(...)` term"
      instantiateMVars (← elabTermAndSynthesize proofSyntax none)
    admitConstrainedPoint target value proofs

/-- The actual data field of a fixed unnamed record, retaining all supplied object context. -/
partial def constrainedCarrier? (target : Value) : M (Option Value) := do
  let .object type category .. := target | return none
  unless category.id == CategoryId.sets do return none
  let some schema ← ConstrainedPoint.schema? type | return none
  return some (retainObjectContext (.object schema.dataType category none none none) #[target])

/-- Apply the actual fixed constructor at the original generalized-element domain. -/
partial def admitConstrainedPoint (target value : Value) (proofs : Array Expr := #[]) : M Value := do
  let .object type category .. := target
    | throwStratum .invalid "a constrained point requires its complete selected object"
  unless category.id == CategoryId.sets do
    throwStratum .invalid "a constrained point constructor acts at its declared set of points"
  let .element original source := value
    | throwStratum .invalid "a constrained point requires its original point map"
  let some (domain, dataType) := homEnds? (← instantiateMVars (← inferType original))
    | throwStratum .invalid "a constrained point lost its original generalized domain"
  unless ← withTransparency .all <| isDefEq dataType (← semanticObject source) do
    throwStratum .invalid "a constrained point changed its original data endpoint"
  let result ← ConstrainedPoint.construct type (← functionOf original) proofs
  unless ← withTransparency .all <| isDefEq result.domain domain do
    throwError "the constrained point constructor replaced its original domain"
  let point ← homIn (← quoteExpr result.value) domain type category
  Trace.record (← read).trace point
    (.constrainedPoint result.schema.constructor category.id domain dataType type original)
  return .element point target

/-- The element (or map) `v` admitted into the domain `D` by its registered admission
`∀ params (x : B) (h : P x), 1 ⟶ D params`, the evidence `P x` established when the statement is
read (LC-14): `2 ∈ ℚˣ`, `M ∈ GLₙ(K)`, `p` monic of degree `n`, `f` continuous. The element is the
first explicit binder the admission's target does not depend on, and its hypotheses are the
explicit binders after it, each a proposition or data with at most one value (the registry's
rule): the evidence builds a proof, or the data (`Invertible x`, the inverse of a unit), and the
admission takes the term it built. An element at a stage (a variable) has no such evidence:
`t ↦ 1/t` on `ℝ` is not a map, whatever `t` is. -/
partial def admit (D : Value) (v : Value) (proofs : Array Value := #[]) : M Value := do
  let .object d category (some (entry, _)) _ _ := D
    | throwStratum .invalid m!"a domain is a named set"
  let some admission := entry.admission
    | throwStratum .invalid m!"{entry.name} registers no admission"
  let some evidence := entry.evidence
    | throwStratum .invalid m!"{entry.name} registers no evidence for its admission: nothing is \
        admitted into it (LC-18)"
  -- Retain the supplied map and its selected endpoints before extracting the
  -- carrier value used by the formal admission procedure.
  let (original, originalCategory, originalSource, originalTarget) ← match v with
    | .element hom X@(.object _ sourceCategory ..) =>
        let some (source, target) := homEnds? (← instantiateMVars (← inferType hom))
          | throwStratum .invalid m!"an admitted point has no categorical endpoints"
        unless ← isDefEq target (← semanticObject X) do
          throwStratum .invalid m!"an admitted point is outside its selected target"
        pure (hom, sourceCategory.id, source, target)
    | .morphism hom source target sourceCategory _ =>
        pure (hom, sourceCategory.id, source, target)
    | _ => throwStratum .invalid m!"only an element or a map is admitted into {entry.name}"
  let carrier ← match v with
    | .element h _ =>
        if (← read).stage.isSome then
          throwStratum .invalid m!"a variable is not established to lie in {entry.name}: the \
            evidence of an admission is of a value"
        `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr h)
          $(← quoteExpr (← globalPoint)))
    | .morphism f .. =>
        -- The function the map is, so that its evidence is about that function.
        quoteExpr (← functionOf f)
    | _ => throwStratum .invalid m!"only an element or a map is admitted into {entry.name}"
  let one ← semanticObject (← oneObject)
  let c ← mkConstWithFreshMVarLevels admission
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType c)
  let some (admissionSource, admissionTarget) := homEnds? type
    | throwStratum .invalid m!"the admission of {entry.name} is not a family of points"
  unless ← isDefEq admissionTarget (← semanticObject D) do
    throwStratum .invalid m!"the admission of {entry.name} does not land in it"
  let explicit := (List.range args.size).toArray.filter (infos[·]!.isExplicit)
  -- The element: the first explicit binder the target does not depend on (the parameters of the
  -- domain occur in it). What follows it is its hypotheses.
  let some xi := explicit.find? fun i => (type.findMVar? (· == args[i]!.mvarId!)).isNone
    | throwStratum .invalid m!"the admission of {entry.name} takes no value"
  let hypotheses := explicit.filter (xi < ·)
  let x ← elabTermEnsuringType carrier (← instantiateMVars (← inferType args[xi]!))
  synthesizeSyntheticMVarsNoPostponing
  -- The value itself, its plumbing unfolded: what its evidence is about.
  let x ← normalizedValue (← instantiateMVars x)
  unless ← isDefEq args[xi]! x do
    throwStratum .invalid m!"the value is not in the set {entry.name} is included in"
  synthesizeInstances args infos
  unless proofs.size <= hypotheses.size do
    throwStratum .invalid "too many independent admission proofs were supplied"
  for index in [:hypotheses.size] do
    let i := hypotheses[index]!
    let obligation ← instantiateMVars (← inferType args[i]!)
    let proof ← match proofs[index]? with
      | some supplied => typedParameter obligation supplied
      | none => establish evidence obligation m!"not an element of {entry.name}"
    unless ← isDefEq args[i]! proof do
      throwStratum .invalid m!"the evidence of {entry.name} does not apply"
  let admitted ← instantiateMVars (mkAppN c args)
  if admitted.hasMVar then
    throwStratum .invalid m!"the parameters or evidence of {entry.name} are not determined"
  unless ← isTypeCorrect admitted do
    throwStratum .invalid m!"the admission of {entry.name} is outside its declared signature"
  let parameters ← (explicit.filter (· < xi)).mapM fun i => instantiateMVars args[i]!
  Trace.record (← read).trace admitted
    (.admittedPoint entry.id category.id parameters original originalCategory
      originalSource originalTarget)
  let source ← instantiateMVars admissionSource
  let point ← if ← isDefEq source one then pure admitted else do
    let some comparison ← operationPointComparison source
      | throwStratum .invalid m!"the admission's source has no registered global-point comparison"
    let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, admitted]
    unless ← isTypeCorrect composite do
      throwStratum .invalid m!"the admission's terminal comparison has incompatible endpoints"
    Trace.record (← read).trace composite
      (.morphismComposition category.id comparison admitted one source d)
    pure composite
  let hom ← homIn (← quoteExpr point) one d category
  Trace.alias (← read).trace point hom
  return .element hom D

/-- Compare a declaration and every ordered argument before its result can unfold.
A constant operation may erase distinct selected parameters in its returned function. -/
partial def sameOperationApplication (left right : Expr) : M Bool := parameterTrial do
  let mut left := left.consumeMData
  let mut right := right.consumeMData
  while left.isAppOfArity ``id 2 do left := left.appArg!.consumeMData
  while right.isAppOfArity ``id 2 do right := right.appArg!.consumeMData
  unless left.getAppFn.constName?.isSome &&
      left.getAppFn.constName? == right.getAppFn.constName? &&
      left.getAppArgs.size == right.getAppArgs.size do return false
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar then return false
  for (a, b) in left.getAppArgs.zip right.getAppArgs do
    unless ← withTransparency .all <|
        isDefEq (← inferType a) (← inferType b) <&&> isDefEq a b do return false
  withTransparency .all <|
    isDefEq (← inferType left) (← inferType right) <&&> isDefEq left right

/-- Actual operand domains may already select a structure on a named endpoint.
Follow only retained views of that exact binding, checking every constructor
argument before its carrier can unfold. All such selections remain candidates;
unrelated parameters and independently coincident carriers supply no selection. -/
partial def retainedOperationSelections (entry : ObjectEntry) (named : Expr)
    (pending : List Value) (seen found : Array Value := #[]) : M (Array Value) := do
  let current :: rest := pending | return found
  if seen.any (·.sameSource current) then
    return ← retainedOperationSelections entry named rest seen found
  let seen := seen.push current
  let .object handle category (some (origin, parameters)) selected data := current
    | return ← retainedOperationSelections entry named rest seen found
  unless category.id == entry.category && origin.id == entry.id do
    return ← retainedOperationSelections entry named rest seen found
  let sameBinding ← parameterCompatible do
    let actual ← Semantic.object origin (← typedParamTerms origin.declaration parameters) none
    unless !actual.hasMVar && !actual.hasLevelMVar && (← isTypeCorrect actual) &&
        (← OperationAgreement.sameApplication named actual) do return false
    withTransparency .all <| isDefEq (← inferType handle) (← inferType actual) <&&>
      isDefEq handle actual
  unless sameBinding do
    return ← retainedOperationSelections entry named rest seen found
  if selected.isSome then
    return ← retainedOperationSelections entry named rest seen (found.push current)
  let retained := data.map (fun (originals, source, _, _, _) =>
    originals.toList ++ [source]) |>.getD []
  retainedOperationSelections entry named (retained ++ rest) seen found

/-- Complete sources for the registry's selected-operation binding rule. An explicit
structure or structural view fixes its own source. A named unstructured set may use only
its declared refinements; an anonymous coordinate uses its supplied constructor context. -/
partial def collectOperationSourceValues (state : RegistryState) (pending : List Value)
    (seen sources : Array Value) (demanded : Option (CategoryExpr × String) := none) :
    M (Array Value) := do
  let current :: rest := pending | return sources
  if seen.any (·.sameSource current) then
    return ← collectOperationSourceValues state rest seen sources demanded
  let seen := seen.push current
  match current with
  | .object _ _ _ (some selected) _ =>
      collectOperationSourceValues state (selected :: rest) seen sources demanded
  | .object _ category _ _ _ =>
      if category.id != CategoryId.sets then
        return ← collectOperationSourceValues state rest seen (sources.push current) demanded
      let .object _ _ origin _ data := current | unreachable!
      if let some (_, source, route, _, _) := data then
        if !route.isEmpty then
          return ← collectOperationSourceValues state (source :: rest) seen sources demanded
      if let some (origin, parameters) := origin then
        if let some (originals, source, _, _, _) := data then
          let named ← Semantic.object origin
            (← typedParamTerms origin.declaration parameters) none
          let retained ← retainedOperationSelections origin named
            (originals.toList ++ [source])
          unless retained.isEmpty do
            return ← collectOperationSourceValues state (retained.toList ++ rest)
              seen sources demanded
        let mut refinements : Array Value := #[]
        for entry in state.objects.filter (refinesObject state · origin.id) do
          let some category := state.categories.find? (·.id == entry.category) | continue
          -- An unrelated refinement cannot supply this binding. Check its
          -- declared structural paths before reading any dependent parameters;
          -- ambiguity remains visible for every possibly applicable source.
          if let some (target, surfaceName) := demanded then
            let routes ← routesBetween state category.expression target
            unless routes.any (state.toSemanticState.isFirstOperationBindingRoute surfaceName) do
              continue
          let candidate ← optionalReading do
            let value ← Semantic.object entry (← typedParamTerms entry.declaration parameters)
              (← read).trace
            unless !value.hasMVar && !value.hasLevelMVar && (← isTypeCorrect value) do
              throwStratum .invalid m!"an operation refinement is not completely determined"
            return Value.object value category (some (entry, parameters)) none none
          if let some value := candidate then refinements := refinements.push value
        return ← collectOperationSourceValues state rest seen (sources ++ refinements) demanded
      if let some (originals, source, _, _, _) := data then
        return ← collectOperationSourceValues state
          (originals.toList ++ (source :: rest)) seen sources demanded
      collectOperationSourceValues state rest seen (sources.push current) demanded
  | .derivedObject .. => collectOperationSourceValues state rest seen (sources.push current) demanded
  | .element _ object => collectOperationSourceValues state (object :: rest) seen sources demanded
  | _ => collectOperationSourceValues state rest seen sources demanded

partial def operationSourceValues (receiver : Value)
    (demanded : Option (CategoryExpr × String) := none) : M (Array Value) := do
  collectOperationSourceValues (← registryState) [receiver] #[] #[] demanded

/-- The complete owner images at the first binding on each structural path. The
upstream registry fixes where name lookup stops; its accepted comparison cells still
govern route coherence. No carrier equality or category ordering selects a binding. -/
partial def operationOwnerCandidates (surfaceName : String) (owner : CategoryId)
    (receiver : Value) : M (Array (Value × OperationSource)) := do
  let state ← registryState
  let some ownerCategory := state.categories.find? (·.id == owner)
    | throwStratum .invalid m!"the operation's owner category is not registered"
  let _ : Inhabited Route :=
    ⟨{ source := ownerCategory.expression, target := ownerCategory.expression, steps := #[] }⟩
  let mut views : Array (Value × OperationSource) := #[]
  for source in (← operationSourceValues receiver
      (some (ownerCategory.expression, surfaceName))) do
    let sourceContext ← objectContext source
    let original ← semanticObject source
    let routes := (← routesBetween state sourceContext.expression ownerCategory.expression).filter
      (state.toSemanticState.isFirstOperationBindingRoute surfaceName)
    if routes.isEmpty then continue
    let classes := state.classify routes (fun _ => owner.raw) (fun route => route)
    let #[selected] := classes
      | throwSemanticAmbiguity m!"several routes determine this selected operation owner"
    unless selected.ambiguities.isEmpty do
      throwSemanticAmbiguity m!"several comparisons determine this selected operation owner"
    let comparisonWitnesses ←
      Semantic.validateRouteComparisons state selected.comparisonWitnesses (some original)
    let #[route] := selected.sources
      | throwSemanticAmbiguity m!"the operation owner has no unique directed source route"
    if route.steps.isEmpty then
      let ownerView := match source with
        | .object .. => source
        | _ => .object original ownerCategory none none
            (some (#[source], source, #[], #[], #[]))
      views := views.push (ownerView, {
        context := sourceContext, receiver := original, route := #[], applications := #[]
        comparisons := selected.comparisonWitnesses, comparisonWitnesses })
      continue
    let (action, applications) ← Semantic.routeFunctorWithApplications state route.refs
    let (sourceBundle, targetBundle) ← functorCategoryBundles action
    unless ← withTransparency .all <| isDefEq sourceBundle sourceContext.bundle do
      throwStratum .invalid m!"the operation route changed its complete selected source"
    let image ← instantiateMVars (← Semantic.objOf action original)
    let targetContext : CategoryContext :=
      { expression := ownerCategory.expression, bundle := (← instantiateMVars targetBundle) }
    CategoryContext.checkObject targetContext image
    let applications ← applications.mapM instantiateMVars
    unless !image.hasMVar && !image.hasLevelMVar &&
        applications.all (fun value => !value.hasMVar && !value.hasLevelMVar) do
      throwStratum .invalid m!"the operation route retains incomplete selected parameters"
    Trace.record (← read).trace image
      (.contextualRoute sourceContext targetContext route.refs applications original false)
    let ownerView := Value.object image ownerCategory none none
      (some (#[source], source, route.refs, #[],
        route.refs.zip (applications.map (·.getAppArgs))))
    views := views.push (ownerView, {
      context := sourceContext, receiver := original, route := route.refs, applications
      comparisons := selected.comparisonWitnesses, comparisonWitnesses })
  return views

partial def operationOwnerViews (surfaceName : String) (owner : CategoryId)
    (receiver : Value) : M (Array Value) := do
  return (← operationOwnerCandidates surfaceName owner receiver).map (·.1)

/-- Retain complete object parameters of an already fixed operation application.
The accepted owner slot determines its category. Other supplied parameters keep
all compatible registered category schemas; none is inferred from an operand's
carrier or from a computed answer. These witnesses let heterogeneous operands
use their own declared interfaces even when the result belongs to another set. -/
partial def operationParameterObjects (row : OperationEntry) (application : Expr)
    (known : Array Value := #[]) : M (Array Value) := do
  let state ← registryState
  let parameters := application.getAppArgs
  unless parameters.size > row.numerals do
    throwStratum .invalid "the operation lost its complete declared owner"
  let ownerSlot := parameters.size - 1 - row.numerals
  let mut available := known
  for index in [:parameters.size] do
    let parameter ← instantiateMVars parameters[index]!
    let type ← instantiateMVars (← inferType parameter)
    if parameter.hasMVar || parameter.hasLevelMVar || (← isProp type) then continue
    let categories ← if index == ownerSlot then do
        let some owner := state.categories.find? (·.id == row.category)
          | throwStratum .invalid "the operation's accepted owner category is absent"
        pure #[owner]
      else state.categories.filterM (parameterCategoryCompatible type)
    for category in categories do
      let context ← CategoryContext.ofNamed category parameter
      let value ← match ← optionalReading
          (recognize state parameter category available parameters) with
        | some value => pure value
        | none => objectInContext parameter context available
      available := available.push value
  return available

/-- Instantiate the operation at the owner binder validated by the registry. A selected
receiver fixes that whole owner; retained constructor parameters may not replace it with a
different structure on the same carrier. Anonymous declaration-owned coordinates may still
obtain their owner from their complete supplied context. -/
partial def selectedOperationApplicationsWithSources (declaration : Name) (owner : CategoryId)
    (receiver : Value) (numerals : Array Nat) (surfaceName : Option String := none) :
    M (Array (Expr × Array OperationSource)) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let ownerSlot := args.size - 1 - numerals.size
  let sources : Array (Value × Option OperationSource) ← match surfaceName with
    | some name => do
        let selected ← operationOwnerCandidates name owner receiver
        pure (selected.map fun (value, source) => (value, some source))
    | none => do
        let values := match receiver with
          | .object _ category origin selected _ =>
              if selected.isSome || category.id != CategoryId.sets || origin.isSome then #[receiver]
              else sourceParameterValues receiver
          | _ => sourceParameterValues receiver
        pure (values.map fun value => (value, none))
  let mut applications : Array (Expr × Array OperationSource) := #[]
  for (source, provenance) in sources do
    let candidate ← try parameterTrial do
      unless ← bindSelectedReceiver args ownerSlot source (some owner) do return none
      let numberParameters := args.extract (ownerSlot + 1) args.size
      unless numberParameters.size == numerals.size do return none
      for (parameter, number) in numberParameters.zip numerals do
        unless (← inferType parameter).isConstOf ``Nat &&
            (← isDefEq parameter (mkNatLit number)) do return none
      synthesizeInstances args infos
      for parameter in args do
        let parameter ← instantiateMVars parameter
        unless parameter.isMVar do continue
        let expected ← instantiateMVars (← inferType parameter)
        unless ← isProp expected do continue
        let some proof ← decideObligation expected | return none
        unless ← isDefEq parameter proof do return none
      let application ← instantiateMVars (mkAppN constant args)
      if application.hasMVar || application.hasLevelMVar || !(← isTypeCorrect application) then return none
      return some application
    catch error =>
      if (CasCatalogue.Exception.interpretationKind error) == .invalid then pure none else throw error
    if let some application := candidate then
      let mut retained := false
      for index in [:applications.size] do
        let some (previous, sources) := applications[index]? | unreachable!
        unless ← sameOperationApplication previous application do continue
        let sources ← match provenance with
          | some source => do
              if ← sources.anyM (OperationAgreement.sameSourceData · source) then pure sources
              else pure (sources.push source)
          | none => pure sources
        let representative := if (← Realize.termIdentity application) <
            (← Realize.termIdentity previous) then application else previous
        applications := applications.set! index (representative, sources)
        retained := true
        break
      unless retained do applications := applications.push (application, provenance.toArray)
  return applications

partial def selectedOperationApplications (declaration : Name) (owner : CategoryId)
    (receiver : Value) (numerals : Array Nat) (surfaceName : Option String := none) : M (Array Expr) := do
  return (← selectedOperationApplicationsWithSources declaration owner receiver numerals surfaceName).map
    (·.1)

/-- A selected operation without supplied operands still requires a unique complete application.
The generic caller checks declared inputs before applying this same full-argument comparison. -/
partial def selectedOperationApplication (declaration : Name) (owner : CategoryId)
    (receiver : Value) (numerals : Array Nat) : M (Option Expr) := do
  let applications ← selectedOperationApplications declaration owner receiver numerals
  let some representative := applications[0]? | return none
  for application in applications do
    unless ← sameOperationApplication application representative do
      throwSemanticAmbiguity m!"several full applications accept this selected operation receiver"
  return some representative

/-- The registered operation `name` on elements of the set `X`: the operation of the category of
`X`'s unique refinement that has one of that name, at that refinement. Its morphism
`X^arity → X` is composed with the product mediator of the operands. -/
partial def applyOperation (name : String) (elements : Array Value) (X : Value)
    (extra : Array Value := #[]) : M Value := do
  let state ← registryState
  let receiver := retainObjectContext X
    (elements.filterMap fun | .element _ object => some object | _ => none)
  let numerals ← extra.mapM fun
    | .nat n => pure n
    | _ => throwStratum .invalid m!"an operation's extra parameter is a numeral"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwStratum .invalid m!"an element operation has no registered category of sets"
  let mut applicable : Array (OperationCandidate × Value × Std.HashMap Expr Node) := #[]
  for operation in state.operations.filter (fun operation =>
      operation.name == name && operation.arity == elements.size &&
        operation.numerals == extra.size) do
    let target ← match operation.result with
      | none => pure receiver
      | some id => match state.objects.find? (·.id == id) with
        | some row => object state row.name #[] none
        | none => throwStratum .invalid m!"an operation's result object is not registered"
    for (application, sources) in (← selectedOperationApplicationsWithSources operation.declaration
        operation.category receiver numerals (some name)) do
      let candidate? ← try parameterTrial do
        let recorder ← Trace.new
        let value ← withReader (fun context => { context with trace := some recorder }) do
          applyFamily operation.declaration sets elements (some target)
            (application := some application) (operationId := some operation.id)
        return some (value, ← recorder.get)
      catch error =>
        if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
      if let some (value, records) := candidate? then
        let .element result _ := value
          | throwStratum .invalid "a registered element operation did not produce its declared point"
        let sources ← OperationAgreement.orderSources sources
        applicable := applicable.push ({ operation := operation.id, application, result, sources },
          value, records)
  let keyed ← applicable.mapM fun candidate =>
    return (← OperationAgreement.candidateKey candidate.1, candidate)
  applicable := (keyed.qsort fun left right => left.1 < right.1).map (·.2)
  let some (representative, value, _) := applicable[0]?
    | throwStratum .invalid m!"the selected structure has no registered operation `{name}`"
  let candidates := applicable.map (·.1)
  let mut comparisons : Array OperationFamilyComparison := #[]
  for right in [:candidates.size] do
    for left in [:right] do
      let some leftCandidate := candidates[left]? | unreachable!
      let some rightCandidate := candidates[right]? | unreachable!
      if let some comparison ← OperationAgreement.compare left right leftCandidate rightCandidate then
        comparisons := comparisons.push comparison
  if candidates.size > 1 then
    let mut reached := (Array.replicate candidates.size false).set! 0 true
    for _ in [:candidates.size] do
      for comparison in comparisons do
        if reached[comparison.left]! || reached[comparison.right]! then
          reached := (reached.set! comparison.left true).set! comparison.right true
    unless reached.all id do
      throwSemanticAmbiguity m!"several complete registered operations `{name}` take these declared inputs"
    OperationAgreement.validate representative.result 0 candidates comparisons
  if let some trace := (← read).trace then
    for (_, _, records) in applicable do
      trace.modify fun current => records.fold
        (fun result term node => result.insert term node) current
  if candidates.size > 1 then
    let .element _ target := value | unreachable!
    let wrapper ← mkAppM ``id #[representative.result]
    if wrapper == representative.result then
      throwError "the operation equivalence wrapper did not retain a distinct child"
    Trace.record (← read).trace wrapper
      (.operationEquivalence representative.result 0 candidates comparisons)
    return .element wrapper target
  return value

/-- `f ∘ ⟨x₁, x₂⟩` (or `f ∘ x₁`): the semantic morphism `semantic : A₁ × A₂ → B` (or `A₁ → B`),
realized from the registered product of the operands' sets (or their set) to the set `target`,
composed with the operands' mediator. The result is an element of `target`, typed `1 ⟶ target`. -/
partial def applyTo (semantic : Term) (elements : Array Value) (target : Value)
    (node? : Option Node := none) : M Value := do
  let .object b category _ _ _ := target
    | throwStratum .invalid m!"the value of a function of elements is in a named set"
  let operands ← elements.mapM fun
    | .element hom (.object a ..) => pure (hom, a)
    | _ => throwStratum .invalid m!"a function is applied to elements"
  let some (x₀, _) := operands[0]? | throwStratum .invalid m!"a function takes operands"
  -- The domain `1` of the operands, so that every element is typed `1 ⟶ X` exactly (a mediator's
  -- own type is `(BinaryFan.mk x y).pt ⟶ …`, whose unification compares `x` and `y`).
  let one := (← whnfR (← inferType x₀)).appFn!.appArg!
  let (source, mediator) ← match operands with
    | #[(x, a₁), (y, a₂)] =>
        let diagram ← standardDiagram "product"
          #[.object a₁ category none none none, .object a₂ category none none none]
        let cone ← limitIn false "product" diagram category
        let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt
          #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[cone]]
        -- The apex is the object of the recorded limit; it is realized as that limit.
        Trace.alias (← read).trace cone apex
        let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[x, y]
        let lift ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
          #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[cone], fan]
        let expected ← mkAppM ``Quiver.Hom #[one, apex]
        unless (← isDefEq (← inferType lift) expected) && (← isTypeCorrect lift) do
          throwStratum .invalid m!"the operands do not form a mediator at their common domain"
        Trace.record (← read).trace lift
          (.productMediator category.id cone one x y)
        let mediator ← mkExpectedTypeHint lift expected
        Trace.alias (← read).trace lift mediator
        pure (apex, mediator)
    | #[(x, a₁)] => pure (a₁, x)
    | _ => throwStratum .invalid m!"a function of elements takes one or two operands"
  let f ← homIn semantic source b category
  if let some node := node? then Trace.record (← read).trace f node
  -- `homIn` retains the accepted map under an expected-type hint. Keep that
  -- representation wrapper connected to the original declaration's recorder.
  Trace.alias (← read).trace f.appArg! f
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[mediator, f]
  Trace.record (← read).trace composite
    (.morphismComposition category.id mediator f one source b)
  let result ← mkExpectedTypeHint composite (← mkAppM ``Quiver.Hom #[one, b])
  Trace.alias (← read).trace composite result
  return .element result target

/-- A decision from a value: a property's answer, or a truth value `p ∈ Ω`, compared with `⊤`: the
proposition `p = ⊤`. -/
partial def asAnswer (v : Value) : M Expr := do
  match v with
  | .answer a | .judged _ a => return a
  | .element e Ω =>
      let state ← registryState
      let some (.object ω category _ _ _) := some Ω | unreachable!
      let .object _ _ (some (entry, _)) _ _ := Ω
        | throwStratum .invalid m!"a decision is a property or a truth value"
      let some po := state.powerObjects.find? (·.omega == entry.id)
        | throwStratum .invalid m!"a decision is a property or a truth value"
      let .object one _ _ _ _ ← oneObject | unreachable!
      let truth ← homIn (mkCIdent po.truth) one ω category
      Trace.record (← read).trace truth (.powerObjectMap po.id "truth" #[])
      mkEq e truth
  | _ => throwStratum .invalid m!"a decision is a property or a truth value"

/-- The registered terminal set `1`, the domain of global elements. -/
partial def oneObject : M Value := do
  let state ← registryState
  let source ← globalPointSource
  let some category := state.categories.find? (·.id == CategoryId.sets)
    | throwStratum .invalid m!"no registered category of sets"
  if ← parameterCompatible (do discard <| recognize state source category; pure true) then
    recognize state source category
  else pure (.object source category none none none)

/-- The registered power object whose family `𝒫` the set `P` is a value of, and its `X`. -/
partial def powerOf? (P : Value) : M (Option (PowerObjectEntry × Value)) := do
  let .object _ _ (some (entry, #[X])) _ _ := P | return none
  return (← registryState).powerObjects.find? (·.object == entry.id) |>.map (·, X)

/-- For an element of a power set `𝒫(X)`: the power object and `X`. -/
partial def powerSetOf? (v : Value) : M (Option (PowerObjectEntry × Value)) := do
  let .element _ P := v | return none
  powerOf? P

/-- `𝒫(X)`. -/
partial def powerSetOf (X : Value) : M Value := do
  let state ← registryState
  let po ← powerObjectIn state CategoryId.sets
  let some entry := state.objects.find? (·.id == po.object) | unreachable!
  object state entry.name #[X] none

/-- The terminal map `S → 1`, by the registered power object's structure. -/
partial def terminalAt (S : Value) : M Expr := do
  let state ← registryState
  let po ← powerObjectIn state CategoryId.sets
  let .object s category _ _ _ := S | throwStratum .invalid m!"a stage is a set"
  let .object one _ _ _ _ ← oneObject | unreachable!
  let terminal ← homIn (← `($(mkCIdent po.terminal) $(← paramTerms #[S])*)) s one category
  Trace.record (← read).trace terminal (.powerObjectMap po.id "terminal" #[s])
  return terminal

/-- A value where a set is needed: a set, or the extent of a subset (the set of its members). -/
partial def asObject (v : Value) : M Value := do
  match v with
  | .object .. | .derivedObject .. => return v
  | .element hom _ =>
      let some (po, X) ← powerSetOf? v
        | throwStratum .invalid m!"an element of a set that is not a power set is not a set"
      let extent ← elabTermAndSynthesize
        (← `($(mkCIdent po.extent) $(← paramTerms #[X])* $(← quoteExpr hom))) none
      let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
        | throwStratum .invalid m!"no registered category of sets"
      let extent ← instantiateMVars extent
      -- The extent of a subset formed as a literal is realized as that literal: a method of
      -- sets on it is the method of the extent, by the power object's `extent`.
      Trace.alias (← read).trace hom extent
      return .object extent sets none none none
  | _ => throwStratum .invalid m!"a set is expected"

/-- `|X|`, the cardinality of a set. -/
partial def cardinality (X : Value) : M Value := do
  if let .derivedObject handle context _ := X then
    let (value, target) ← Semantic.methodIn "cardinality" handle context.expression (← read).trace
    return ← objectInContext value target #[X]
  let .object handle category _ _ _ := X | throwStratum .invalid m!"`|·|` of a set"
  let (value, target) ← Semantic.method "cardinality" handle category (← read).trace
  return .object value target none none none

/-- `x ∈ A` for a subset `A ∈ 𝒫(X)`: membership `X × 𝒫X → Ω` at `⟨x, A⟩`. -/
partial def member (po : PowerObjectEntry) (X : Value) (x A : Value) : M Value := do
  let state ← registryState
  let some omega := state.objects.find? (·.id == po.omega) | unreachable!
  let Ω ← object state omega.name #[] none
  applyTo (← `($(mkCIdent po.member) $(← paramTerms #[X])*)) #[← toElement x X, A] Ω
    (some (.powerObjectMap po.id "member" #[← semanticObject X]))

/-- The negation of a decision (`∉`): the negated proposition. -/
partial def negate (a : Expr) : M Value := return .answer (mkNot a)

/-- `x^k`: either the registered literal-parameter power or the registered binary
power family with its exponent supplied at that family's declared coordinate. -/
partial def power (scope : Scope) (base : Value) (k : Nat) (ambient? : Option Value) : M Value := do
  let _ := scope
  -- `Xⁿ` of a set: its `n`-tuples.
  if let .object .. := base then return ← object (← registryState) "Vec" #[base, .nat k] none
  let X ← match base, ambient? with
    | .element _ Y, some X =>
        if (← coercionMap Y X).isSome then pure X else pure Y
    | .element _ X, _ => pure X
    | _, some X => pure X
    | _, none => notationObject "literal.integral.domain"
  let base ← toElement base X
  if ← parameterCompatible (do
      discard <| applyOperation "^" #[base] X #[.nat k]
      pure true) then
    return ← applyOperation "^" #[base] X #[.nat k]
  applyNamed (← registryState) "^" #[base, .nat k] (some X)

/-- The identity `X → X`: the generic element of `X` at the stage `X`. -/
partial def identityAt (X : Value) : M Expr := do
  let .object x category _ _ _ := X | throwStratum .invalid m!"a stage is a set"
  let hom ← homIn (← `(CategoryTheory.CategoryStruct.id _)) x x category
  Trace.record (← read).trace hom (.morphismIdentity category.id x)
  return hom

/-- Retain a callable's original operation tree under a distinct typed wrapper.
The generalized source is part of the recipe; it is never replaced by a singleton point. -/
partial def callableMap (category : NamedCategoryEntry) (domain target body : Expr) : M Expr := do
  let domain ← instantiateMVars domain
  let target ← instantiateMVars target
  let body ← instantiateMVars body
  if #[domain, target, body].any (fun term => term.hasMVar || term.hasLevelMVar) then
    throwStratum .invalid m!"the callable's complete domain, target or body is not determined"
  let expected ← mkAppM ``Quiver.Hom #[domain, target]
  unless ← withTransparency .all <| isDefEq (← inferType body) expected do
    throwStratum .invalid m!"the callable body is outside its retained generalized domain"
  unless ← isTypeCorrect body do
    throwStratum .invalid m!"the callable body is outside its dependent signature"
  -- mkExpectedTypeHint always adds a fresh `id expected body` application. Keeping the
  -- original body as the child prevents replacing its trace by a self-referential recipe.
  let wrapped ← mkExpectedTypeHint body expected
  unless ← withTransparency .all <| isDefEq wrapped body do
    throwStratum .invalid m!"the callable recipe changed its original mathematical map"
  Trace.record (← read).trace wrapped (.callableRecipe category.id domain target body)
  return wrapped

/-- A function body inhabits its independently declared codomain when its actual map already
has that exact carrier type. This retains the codomain's selected structure without changing
the operations used to form the body. Other carrier types require a declared coercion. -/
partial def declaredResult (value target : Value) : M Value := do
  let target ← carrierObject target
  let endpoint ← semanticObject target
  if endpoint.hasMVar || endpoint.hasLevelMVar then
    throwStratum .invalid m!"the declared endpoint is not completely determined"
  if let .element arrow source := value then
    if arrow.hasMVar || arrow.hasLevelMVar || !(← isTypeCorrect arrow) then
      throwStratum .invalid m!"the original generalized point is not completely typed"
    let some (_, actualEndpoint) := homEnds? (← inferType arrow)
      | throwStratum .invalid m!"a function body has no categorical target"
    unless ← isDefEq actualEndpoint (← semanticObject source) do
      throwStratum .invalid m!"a function body differs from its retained target"
    if ← isDefEq actualEndpoint endpoint then
      return .element arrow (retainObjectContext target #[source])
  toElement value target

/-- `e` read at the stage `X` with `t` its generic element: a generalized element `X → Y`. -/
partial def atStage (scope : Scope) (t : Name) (X : Value) (e : Syntax)
    (ambient? : Option Value) : M Value := do
  let generic := Value.element (← identityAt X) X
  withReader (fun ctx => { ctx with stage := some X, bound := (t, generic) :: ctx.bound }) do
    let v ← eval scope e none ambient?
    match v, ambient? with
    | .nat _, some Y => toElement v Y
    | _, _ => pure v

/-- The exact declared components of an element. Named families publish their finite
coordinate maps; constructed products retain their accepted cone and its defining legs. -/
partial def refinedComponentPresentation? (X : Value) : M (Option Value) := do
  let .object carrier sets _ (some selected@(.object actual category ..)) data := X
    | return none
  if category.id == CategoryId.sets then return none
  let state ← registryState
  let mut candidates : Array
      (ObjectEntry × Value × Value × Array Expr × Expr × Expr) := #[]
  for row in state.objects do
    unless row.category == category.id && row.refines.isSome do continue
    let some (application, base, components) ← componentRefinement? state row actual | continue
    let named ← recognizeObjectApplication state row category application.explicit #[] application.explicit
    let presented ← carrierObject named
    let .object presentedCarrier _ (some (presentedBase, parameters)) .. := presented
      | throwStratum .invalid "the component refinement omitted its declared base presentation"
    unless presentedBase.id == base.id &&
        (← withTransparency .all <| isDefEq presentedCarrier carrier) do
      throwStratum .invalid "the full component refinement changed its actual carrier"
    let arity ← instantiateMVars (← elabTermAndSynthesize
      (← `($(mkCIdent components.arity) $(← typedParamTerms components.arity parameters)*)) none)
    let family ← instantiateMVars (← elabTermAndSynthesize
      (← `($(mkCIdent components.projection)
        $(← typedParamTerms components.projection parameters)*)) none)
    unless !arity.hasMVar && !arity.hasLevelMVar && !family.hasMVar &&
        !family.hasLevelMVar && (← isTypeCorrect arity) && (← isTypeCorrect family) do
      throwStratum .invalid "the full component presentation has undetermined parameters"
    candidates := candidates.push (row, named, presented, application.explicit, arity, family)
  let some first := candidates[0]? | return none
  let (_, _, _, firstParameters, firstArity, firstFamily) := first
  for (_, _, _, parameters, arity, family) in candidates do
    unless parameters.size == firstParameters.size do
      throwSemanticAmbiguity "the selected object has distinct complete component presentations"
    for (left, right) in firstParameters.zip parameters do
      unless ← withTransparency .all <|
          isDefEq (← inferType left) (← inferType right) <&&> isDefEq left right do
        throwSemanticAmbiguity "the component presentations have different complete parameters"
    unless ← withTransparency .all <|
        isDefEq (← inferType firstArity) (← inferType arity) <&&>
        isDefEq firstArity arity <&&>
        isDefEq (← inferType firstFamily) (← inferType family) <&&>
        isDefEq firstFamily family do
      throwSemanticAmbiguity "the selected object has different whole component families"
  -- The original actual source remains an independent child. A fresh wrapper
  -- retains every checked full presentation without overwriting its trace/cache.
  let ordered := candidates.qsort (fun left right => left.1.id.raw < right.1.id.raw)
  let some representative := ordered[0]? | unreachable!
  let wrapper ← mkAppM ``id #[actual]
  let expected ← inferType actual
  let views := #[selected] ++ ordered.map (·.2.1)
  let evidence ← coalesceSelectedParameterViews expected wrapper views
  let (_, _, _, alternatives, _) := evidence
  Trace.record (← read).trace wrapper (.parameterEquivalence expected actual alternatives)
  let source := Value.object wrapper category none none (some evidence)
  let .object _ _ origin .. := representative.2.2.1 | unreachable!
  return some (.object carrier sets origin (some source) data)

/-- Read components through their complete declared presentation. A refinement
may supply that presentation only after its entire structured object matches. -/
partial def componentElements (value : Value) (count : Nat) : M (Array Value) := do
  let .element _ X@(.object objectHandle category origin _ _) := value
    | throwStratum .invalid m!"a component pattern binds an element of its declared domain"
  let state ← registryState
  if let some (entry, parameters) := origin then
    if let some components := entry.components then
      let arityTerms ← typedParamTerms components.arity parameters
      let arity ← instantiateMVars (← elabTermAndSynthesize
        (← `($(mkCIdent components.arity) $arityTerms*)) none)
      let normalizedArity ← withTransparency .all <| whnf arity
      let some actualCount ← (Meta.evalNat normalizedArity).run
        | throwStratum .invalid m!"the selected component arity is not determined"
      unless actualCount == count do
        throwStratum .invalid m!"the argument has {actualCount} components, but its pattern has {count}"
      let terms ← typedParamTerms components.projection parameters
      let family ← elabTermAndSynthesize (← `($(mkCIdent components.projection) $terms*)) none
      let signature ← whnfR (← inferType family)
      unless signature.isForall do
        throwStratum .invalid m!"the registered components have no finite index"
      let row ← match state.morphisms.filter (fun row =>
          row.declaration == components.projection && row.category == category.id) with
        | #[row] => pure row
        | #[] => throwStratum .invalid "the registered component projection has no callable morphism row"
        | _ => throwSemanticAmbiguity "the component declaration has several accepted callable addresses"
      return ← (List.range count).toArray.mapM fun ordinal => do
        let index ← constructionIndex signature.bindingDomain! ordinal
        let projection ← instantiateMVars (mkApp family index)
        unless !projection.hasMVar && !projection.hasLevelMVar && (← isTypeCorrect projection) do
          throwStratum .invalid m!"a component map is outside its exact dependent signature"
        let some (source, target) := homEnds? (← inferType projection)
          | throwStratum .invalid m!"the registered component is not a morphism"
        unless ← isDefEq source objectHandle do
          throwStratum .invalid m!"the component belongs to a different selected object"
        let projection ← retainNamedMorphism row projection
        let targetValue ← try recognize state target category parameters
          catch error =>
            if Exception.interpretationKind error == .invalid then
              pure (.object target category none none none)
            else throw error
        let targetValue := retainObjectContext targetValue (#[X] ++ parameters)
        applyTo (← quoteExpr projection) #[value] targetValue
  if let some presented ← refinedComponentPresentation? X then
    let .element point _ := value | unreachable!
    return ← componentElements (.element point presented) count
  -- An independently supplied complete carrier may already be the domain of a
  -- published component family. Instantiate only that family's complete type;
  -- no object name or extra mathematical structure is assigned to the carrier.
  let mut componentFamilies : Array (Expr × Expr × MorphismEntry) := #[]
  for entry in state.objects do
    unless entry.category == category.id do continue
    let some components := entry.components | continue
    let candidate ← try parameterTrial do
      let application ← DirectConstruction.instantiate entry.declaration #[]
      unless ← withTransparency .all <| isDefEq application.value objectHandle do return none
      let application ← DirectConstruction.close application
      let parameters ← (application.explicit.mapM quoteExpr : TermElabM _)
      let arity ← instantiateMVars (← elabTermAndSynthesize
        (← `($(mkCIdent components.arity) $parameters*)) none)
      let family ← instantiateMVars (← elabTermAndSynthesize
        (← `($(mkCIdent components.projection) $parameters*)) none)
      if arity.hasMVar || arity.hasLevelMVar || family.hasMVar || family.hasLevelMVar then
        return none
      let row ← match state.morphisms.filter (fun row =>
          row.declaration == components.projection && row.category == category.id) with
        | #[row] => pure row
        | #[] => throwStratum .invalid "the declared component family has no public morphism row"
        | _ => throwSemanticAmbiguity "the component declaration has several accepted callable addresses"
      return some (arity, family, row)
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
    if let some candidate := candidate then
      let same ← componentFamilies.anyM fun previous => parameterTrial do
        withTransparency .all <| isDefEq previous.1 candidate.1 <&&>
          isDefEq (← inferType previous.2.1) (← inferType candidate.2.1) <&&>
          isDefEq previous.2.1 candidate.2.1
      unless same do componentFamilies := componentFamilies.push candidate
  unless componentFamilies.isEmpty do
    let #[(arity, family, row)] := componentFamilies
      | throwSemanticAmbiguity "several complete declared component families act on this domain"
    let some actualCount ← (Meta.evalNat (← withTransparency .all <| whnf arity)).run
      | throwStratum .invalid "the declared component arity is not determined"
    unless actualCount == count do
      throwStratum .invalid m!"the argument has {actualCount} components, but its pattern has {count}"
    let signature ← whnfR (← inferType family)
    unless signature.isForall do
      throwStratum .invalid "the declared component family lost its finite index"
    return ← (List.range count).toArray.mapM fun ordinal => do
      let index ← constructionIndex signature.bindingDomain! ordinal
      let projection ← instantiateMVars (mkApp family index)
      let some (source, target) := homEnds? (← inferType projection)
        | throwStratum .invalid "the declared component is not a complete morphism"
      unless !projection.hasMVar && !projection.hasLevelMVar && (← isTypeCorrect projection) &&
          (← withTransparency .all <| isDefEq source objectHandle) do
        throwStratum .invalid "the declared component changed its complete supplied source"
      let projection ← retainNamedMorphism row projection
      let targetValue ← declaredEndpointObject target category #[X]
      applyTo (← quoteExpr projection) #[value] targetValue
  let mut apex := objectHandle.consumeMData
  while apex.isAppOfArity ``id 2 do apex := apex.appArg!.consumeMData
  unless apex.isAppOf ``CategoryTheory.Limits.Cone.pt do
    -- A complete selected carrier can reduce to a declared product without retaining
    -- the cone's syntax. Reconstruct that existing universal presentation, preserving
    -- the original whole point and its selected source as context for every component.
    let endpoint ← withTransparency .all <| whnf objectHandle
    -- The component types are fixed by that product itself. Retain X after obtaining
    -- its legs; its unrelated parameters must not choose a structure on a component
    -- merely because one of their carrier types is definitionally equal to it.
    let presented ← declaredEndpointObject endpoint category #[]
    let .object handle .. := presented
      | throwStratum .invalid m!"the selected object declares no component maps"
    let mut candidate := handle.consumeMData
    while candidate.isAppOfArity ``id 2 do candidate := candidate.appArg!.consumeMData
    unless candidate.isAppOf ``CategoryTheory.Limits.Cone.pt &&
        (← withTransparency .all <| isDefEq handle objectHandle) do
      throwStratum .invalid m!"the selected object declares no component maps"
    let .element point _ := value | unreachable!
    let components ← componentElements (.element point presented) count
    return components.map fun
      | .element component target => .element component (retainObjectContext target #[X])
      | component => component
  let cone := apex.appArg!
  let projections ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  let app ← mkAppM ``CategoryTheory.NatTrans.app #[projections]
  let (indices, _, _) ← forallMetaTelescopeReducing (← inferType app)
  let #[parameter] := indices
    | throwStratum .invalid m!"the selected cone has no unique component index"
  let indexType ← instantiateMVars (← inferType parameter)
  if ← parameterCompatible (do discard <| constructionIndex indexType count; pure true) then
    throwStratum .invalid m!"the component pattern does not cover the selected cone's finite diagram"
  let name ← mkFreshUserName `_componentSource
  let identifier := mkIdent name
  let term ← `(cas_term| $identifier:ident)
  return ← (List.range count).toArray.mapM fun ordinal => do
    let index := Syntax.mkNumLit (toString ordinal)
    let projection ← withReader (fun ctx => { ctx with bound := (name, X) :: ctx.bound }) do
      constructionLeg {} term (← `(cas_term| $index:num))
    let .morphism hom _ _ _ (some (_, target)) := projection
      | throwStratum .invalid m!"a component of the selected cone is not a map"
    applyTo (← quoteExpr hom) #[value] target

/-- Bind a pattern through the source's declared maps, retaining every selected component. -/
partial def bindPattern (pattern : Syntax) (value : Value) : M (List (Name × Value)) := do
  match pattern with
  | `(cas_term| $name:ident) => return [(name.getId, value)]
  | `(cas_term| ($inner)) => bindPattern inner value
  | _ =>
      unless pattern.getKind == ``casTuple do
        throwStratum .invalid m!"a map argument pattern contains only names and component tuples"
      let patterns := #[pattern[1]] ++ pattern[3].getSepArgs
      let components ← componentElements value patterns.size
      return (← (patterns.zip components).mapM fun (pattern, value) => bindPattern pattern value).toList.flatten

/-- Form a requested complete morphism through its registered function admission.
The original endpoints determine the full Hom type; their carriers do not choose a
new category, scalar action, or proof procedure. -/
partial def declaredMap (source target original : Value) : M Value := do
  let sourceContext ← objectContext source
  let targetContext ← objectContext target
  unless sourceContext.expression.syntacticEq targetContext.expression &&
      (← parameterTrial (withTransparency .all <|
        isDefEq sourceContext.bundle targetContext.bundle)) do return original
  let sourceObject ← semanticObject source
  let targetObject ← semanticObject target
  let expected ← CategoryContext.hom sourceContext sourceObject targetObject
  let some plan ← DeclaredAdmission.resolve? CategoryId.sets expected | return original
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwStratum .invalid "a declared map admission requires its registered category of sets"
  let domain ← recognize state plan.application.value sets #[source, target]
    plan.application.explicit
  let admitted ← admit domain original
  let value ← typedParameter expected admitted
  morphismInContext value sourceObject targetObject sourceContext (source, target)

/-- A map with a destructured domain argument. Its body is read at the one original stage;
the component variables are its projections, so compositions retain their common domain. -/
partial def patternMap (scope : Scope) (pattern body : Syntax) (X Y : Value) : M Value := do
  let names := patternNames pattern
  unless names.toList.eraseDups.length == names.size do
    throwStratum .invalid m!"a map argument binds each component name once"
  let sourceValue ← carrierObject X
  let targetValue ← carrierObject Y
  let bindings ← bindPattern pattern (.element (← identityAt sourceValue) sourceValue)
  let result ← withReader (fun ctx =>
      { ctx with stage := some sourceValue, bound := bindings ++ ctx.bound }) do
    declaredResult (← eval scope body none (some targetValue)) targetValue
  let .element hom target := result
    | throwStratum .invalid m!"the body of a destructured map is not an element of its codomain"
  let (.object source category .., .object destination ..) := (sourceValue, target) | unreachable!
  let hom ← callableMap category source destination hom
  declaredMap X Y (.morphism hom source destination category (some (sourceValue, target)))

/-- The map `t ↦ e : X → Y`. -/
partial def lambda (scope : Scope) (t : Name) (e : Syntax) (X Y : Value) : M Value := do
  let sourceValue ← carrierObject X
  let targetValue ← carrierObject Y
  let .element body Y' ← declaredResult
      (← atStage scope t sourceValue e (some targetValue)) targetValue
    | throwStratum .invalid m!"the body of `{t} ↦ …` is an element of `{shown e}`'s set"
  let (.object x category _ _ _, .object y _ _ _ _) := (sourceValue, Y') | unreachable!
  let body ← callableMap category x y body
  declaredMap X Y (.morphism body x y category (some (sourceValue, Y')))

/-- The input object of an element's registered application, after its actual callable
object fixes the dependent parameters. An inclusion may supply that callable object. -/
partial def callableInput (declaration : Name) (category : NamedCategoryEntry)
    (value : Value) : M Value := do
  let .element _ original := value
    | throwStratum .invalid m!"a registered application acts on an element"
  let constant ← mkConstWithFreshMVarLevels declaration
  let (parameters, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let some (source, _) := homEnds? type
    | throwStratum .invalid m!"the registered application is not a family of maps"
  let source ← whnfR source
  let (callable, input) ← match source.getAppFn.constName?, source.getAppArgs with
    | some ``Prod, #[callable, input] => pure (callable, input)
    | _, _ => throwStratum .invalid m!"the registered application has no callable and input pair"
  let state ← registryState
  let mut owner := original
  let mut matched := false
  for _ in [:state.objects.size + 1] do
    if ← parameterCompatible (bindSourceParameter callable owner) then
      unless ← bindSourceParameter callable owner do unreachable!
      matched := true
      break
    let some (_, endpoint) ← inclusionOut? owner | break
    owner ← inclusionTargetValue owner endpoint category
  unless matched do
    throwStratum .invalid m!"the selected callable is outside its registered application source"
  synthesizeInstances parameters infos
  let input ← instantiateMVars input
  if input.hasMVar || input.hasLevelMVar then
    throwStratum .invalid m!"the selected callable does not determine its complete input object"
  declaredEndpointObject input category #[owner]

/-- The actual carrier action on a complete selected morphism. This supplies its
function action on a generalized set-valued input without changing its structure. -/
partial def carrierMorphism (value : Value) : M Value := do
  let (hom, source, target, context, sourceValue, targetValue) ← morphismContext value
  let sourceCarrier ← carrierObject sourceValue
  let targetCarrier ← carrierObject targetValue
  let .object sourceObject sets .. := sourceCarrier
    | throwStratum .invalid "a generalized map needs its declared source carrier"
  let .object targetObject targetSets .. := targetCarrier
    | throwStratum .invalid "a generalized map needs its declared target carrier"
  unless sets.id == targetSets.id do
    throwStratum .invalid "the generalized map has different carrier categories"
  if context.expression.syntacticEq sets.expression then return value
  let state ← registryState
  let routes ← routesBetween state context.expression sets.expression
  let classes :=
    letI : Inhabited Route :=
      ⟨{ source := context.expression, target := sets.expression, steps := #[] }⟩
    state.classify routes (fun _ => sets.id.raw) (fun route => route)
  let #[cls] := classes
    | throwSemanticAmbiguity "the generalized map has no unique accepted carrier action"
  unless cls.ambiguities.isEmpty do
    throwSemanticAmbiguity "the generalized map's carrier action has unresolved comparisons"
  discard <| Semantic.validateRouteComparisons state cls.comparisonWitnesses (some source)
  let #[route] := cls.sources
    | throwSemanticAmbiguity "the generalized map has several directed carrier actions"
  let (action, applications) ← Semantic.routeFunctorWithApplications state route.refs
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  unless ← withTransparency .all <| isDefEq sourceBundle context.bundle do
    throwStratum .invalid "the carrier action changed the generalized map's source category"
  let mapped ← instantiateMVars (← Semantic.mapOf action hom)
  let targetContext : CategoryContext := {
    expression := sets.expression, bundle := (← instantiateMVars targetBundle) }
  CategoryContext.checkMorphism targetContext mapped sourceObject targetObject
  unless ← withTransparency .all <|
      isDefEq (← Semantic.objOf action source) sourceObject <&&>
      isDefEq (← Semantic.objOf action target) targetObject do
    throwStratum .invalid "the carrier action changed the generalized map's complete endpoints"
  Trace.record (← read).trace mapped
    (.contextualRoute context targetContext route.refs
      (← applications.mapM instantiateMVars) hom true)
  return .morphism mapped sourceObject targetObject sets (some (sourceCarrier, targetCarrier))

/-- `f(x, …)`: a map applied to elements (composition), or to a set (its image). -/
partial def apply (scope : Scope) (f : Value) (args : Array Syntax) : M Value := do
  -- A complete categorical map can be applied to an original generalized map.
  -- This branch preserves that original domain rather than treating it as a global point.
  if (f matches .morphism ..) || (f matches .derivedMorphism ..) then
    if let #[argumentSyntax] := args then
      let temporary ← Trace.new
      let (_, _, _, _, originalSource, _) ← morphismContext f
      let argumentContext ← carrierObject originalSource
      let candidate ← try
        pure (some (← withReader (fun context =>
          { context with trace := some temporary, closedTerms := none })
          (eval scope argumentSyntax none (some argumentContext))))
      catch error =>
        if CasCatalogue.Exception.interpretationKind error == .invalid then pure none else throw error
      if let some argument := candidate then
        if (argument matches .morphism ..) || (argument matches .derivedMorphism ..) then
          let (_, _, _, functionContext, _, _) ← morphismContext f
          let (_, _, _, argumentContext, _, _) ← morphismContext argument
          let (function, argument) ←
            if functionContext.expression.syntacticEq argumentContext.expression then
              pure (f, argument)
            else do
              let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
                | throwStratum .invalid "the registered set category is absent"
              unless functionContext.expression.syntacticEq sets.expression ||
                  argumentContext.expression.syntacticEq sets.expression do
                throwStratum .invalid "the complete maps have different selected composition categories"
              let function ← carrierMorphism f
              let argument ← withReader (fun context => { context with trace := some temporary })
                (carrierMorphism argument)
              pure (function, argument)
          let (second, middle, target, context, _, targetValue) ← morphismContext function
          let (first, source, actualMiddle, sourceContext, sourceValue, _) ← morphismContext argument
          unless context.expression.syntacticEq sourceContext.expression &&
              (← withTransparency .all <| isDefEq context.bundle sourceContext.bundle) &&
              (← withTransparency .all <| isDefEq middle actualMiddle) do
            throwStratum .invalid "the complete maps have different selected composition endpoints"
          let result ← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]
          CategoryContext.checkMorphism context result source target
          if let some trace := (← read).trace then
            for (value, node) in (← temporary.get).toArray do
              trace.modify (·.insert value node)
          Trace.record (← read).trace result
            (.contextualComposition context first second source middle target)
          return ← morphismInContext result source target context (sourceValue, targetValue)
    if let .derivedMorphism hom source target context (X, Y) := f then
      let sourceCarrier ← carrierObject X
      let targetCarrier ← carrierObject Y
      let .object sourceObject sets .. := sourceCarrier
        | throwStratum .invalid "the selected map has no accepted carrier context"
      let targetObject ← semanticObject targetCarrier
      let state ← registryState
      let routes ← routesBetween state context.expression sets.expression
      let classes :=
        letI : Inhabited Route :=
          ⟨{ source := context.expression, target := sets.expression, steps := #[] }⟩
        state.classify routes (fun _ => sets.id.raw) (fun route => route)
      let #[cls] := classes
        | throwSemanticAmbiguity "the derived map has no unique accepted carrier action"
      unless cls.ambiguities.isEmpty do
        throwSemanticAmbiguity "the derived map's carrier action has unresolved comparisons"
      discard <| Semantic.validateRouteComparisons state cls.comparisonWitnesses (some source)
      let #[route] := cls.sources
        | throwSemanticAmbiguity "the derived map has several directed carrier actions"
      let (mapped, applications, targetContext) ← if route.refs.isEmpty then
        pure (hom, #[], context)
      else do
        let (action, applications) ← Semantic.routeFunctorWithApplications state route.refs
        let (sourceBundle, targetBundle) ← functorCategoryBundles action
        unless ← withTransparency .all <| isDefEq sourceBundle context.bundle do
          throwStratum .invalid "the carrier action changed its actual source category"
        let mapped ← Semantic.mapOf action hom
        pure (mapped, applications, { expression := sets.expression, bundle := targetBundle })
      let mapped ← instantiateMVars mapped
      let targetContext := { targetContext with bundle := (← instantiateMVars targetContext.bundle) }
      CategoryContext.checkMorphism targetContext mapped sourceObject targetObject
      unless mapped == hom do
        Trace.record (← read).trace mapped
          (.contextualRoute context targetContext route.refs
            (← applications.mapM instantiateMVars) hom true)
      return ← apply scope (.morphism mapped sourceObject targetObject sets
        (some (sourceCarrier, targetCarrier))) args
  -- An element of a set with a registered application (a polynomial `p(a)`): that application at
  -- `p` and `a`; a numeral `a` is an element of the set of coefficients, the set's parameter.
  if let .element _ (.object _ _ (some (entry, _)) _ _) := f then
    let some (application, category, params, address) ← applicationOf? f
      | throwStratum .invalid m!"the elements of {entry.name} are not applied"
    if args.isEmpty then throwStratum .invalid m!"a callable element takes its input argument"
    let v ← match args with
      | #[arg] =>
          if let some input ← optionalReading (callableInput application category f) then
            declaredResult (← eval scope arg none (some input)) input
          else
            -- A further dependent structure may be determined by an independently
            -- supplied operand (polynomial evaluation at an algebra). Preserve that
            -- existing reading; only a callable-fixed input supplies a literal context.
            match ← eval scope arg with
            | v@(.element ..) => pure v
            | v => match params.find? (· matches .object ..) with
              | some R => toElement v R
              | none => throwStratum .invalid m!"`{shown arg}` is not an element"
      | _ =>
          let input ← callableInput application category f
          declaredResult (← tuple scope args (some input)) input
    return ← applyFamily application category #[f, v] (callableAddress := some address)
  let .morphism _ _ _ _ (some _) := f
    | throwStratum .invalid m!"only a map `X → Y` is applied"
  if args.isEmpty then throwStratum .invalid m!"a map `X → Y` takes its domain argument"
  -- Reuse the complete selected action: its source dictionary fixes every route
  -- parameter before mapping the original arrow, and the trace retains them all.
  let .morphism mapped source target sets (some (sourceCarrier, targetCarrier)) ← carrierMorphism f
    | throwStratum .invalid "the map has no complete declared carrier action"
  let v ← match args with
    | #[arg] => eval scope arg none (some sourceCarrier)
    | _ => tuple scope args (some sourceCarrier)
  -- A map applied to its whole carrier domain is its image.
  if let .object .. := v then return ← imageOfMap mapped sourceCarrier targetCarrier
  let .element x _ ← declaredResult v sourceCarrier
    | throwStratum .invalid m!"a map is applied to an element"
  let result ← mkAppM ``CategoryTheory.CategoryStruct.comp #[x, mapped]
  unless ← isTypeCorrect result do
    throwStratum .invalid m!"the element is outside the map's exact registered carrier domain"
  let pointType ← inferType x
  let some (pointSource, _) := homEnds? pointType
    | throwStratum .invalid m!"the argument is not a typed generalized element"
  Trace.record (← read).trace result
    (.morphismComposition sets.id x mapped pointSource source target)
  return .element result targetCarrier
/-- The image `f(X) ∈ 𝒫 Y` of a map `f : X → Y`. -/
partial def imageOfMap (f : Expr) (X Y : Value) : M Value := do
  let state ← registryState
  let po ← powerObjectIn state CategoryId.sets
  let P ← powerSetOf Y
  let .object p category _ _ _ := P | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let image ← homIn (← `($(mkCIdent po.image) $(← paramTerms #[X, Y])* $(← quoteExpr f)))
    one p category
  Trace.record (← read).trace image
    (.powerObjectMap po.id "image" #[← semanticObject X, ← semanticObject Y, f])
  return .element (← staged image) P

/-- A bound value at the current stage: a global element `1 → X` (a ring's generator bound for a
whole statement) read inside a map is `S → 1 → X`. -/
partial def restage (v : Value) : M Value := do
  let (.element h X, some (.object s ..)) := (v, (← read).stage) | return v
  let signature ← inferType h
  let endpoints ← match homEnds? signature with
    | some endpoints => pure (some endpoints)
    | none => pure (homEnds? (← whnfR signature))
  let some (domain, _) := endpoints | return v
  let .object one .. ← oneObject | return v
  if (← isDefEq domain s) || !(← isDefEq domain one) then return v
  return .element (← staged h) X

/-- A global element `1 → X` at the current stage `S`: `S → 1 → X`. -/
partial def staged (hom : Expr) : M Expr := do
  match (← read).stage with
  | none => return hom
  | some S => throughTerminal S hom

/-- `S → 1 → X`: the global element `hom : 1 → X` read at the stage `S`, recorded as the
composite of the registered terminal map and `hom`. -/
partial def throughTerminal (S : Value) (hom : Expr) : M Expr := do
  let terminal ← terminalAt S
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[terminal, hom]
  if let (.object s .., some (one, target)) := (S, homEnds? (← inferType hom)) then
    Trace.record (← read).trace composite
      (.morphismComposition CategoryId.sets terminal hom s one target)
  return composite

/-- `{e | t ∈ X}`, the image of the complete map `t ↦ e`. For a subset varying
over an outer stage, use its power object's declared direct-image action and compose
with the original subset map; a generalized subset is never treated as a global point. -/
partial def imageOf (scope : Scope) (e : Syntax) (t : Name) (domain : Value) : M Value := do
  if let some (power, X) ← powerSetOf? domain then
    let some directImage := power.directImage
      | throwStratum .invalid m!"the registered power object has no declared direct-image action"
    let .object source category .. := X
      | throwStratum .invalid m!"the subset's declared ambient is not an object"
    let .element f Y ← atStage scope t X e none
      | throwStratum .invalid m!"`{shown e}` is an element"
    let .object target targetCategory .. := Y
      | throwStratum .invalid m!"the direct image has no fixed object codomain"
    unless category.id == targetCategory.id &&
        (← withTransparency .all <| isDefEq (← inferType f)
          (← mkAppM ``Quiver.Hom #[source, target])) do
      throwStratum .invalid m!"the image body is not a whole map on its declared bound carrier"
    let state ← registryState
    unless state.morphisms.any (fun row =>
        row.declaration == directImage && row.category == category.id) do
      throwStratum .invalid m!"the direct-image action has no registered callable signature"
    let imageMap := Value.morphism f source target category (some (X, Y))
    return ← applyFamily directImage category #[domain] (some (← powerSetOf Y))
      (parameters := #[X, Y, imageMap])
  let X ← asObject domain
  let .element f Y ← atStage scope t X e none
    | throwStratum .invalid m!"`{shown e}` is an element"
  imageOfMap f X Y

/-- `{t ∈ X | P}`, the subset of `X` the predicate `t ↦ P` classifies (its transpose). -/
partial def comprehension (scope : Scope) (t : Name) (X : Value) (p : Syntax) : M Value := do
  let state ← registryState
  let po ← powerObjectIn state CategoryId.sets
  let .element predicate _ ← atStage scope t X p none
    | throwStratum .invalid m!"`{shown p}` is a predicate"
  let P ← powerSetOf X
  let .object pHandle category _ _ _ := P | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let subset ← homIn (← `($(mkCIdent po.transpose) $(← paramTerms #[X])* $(← quoteExpr predicate)))
    one pHandle category
  Trace.record (← read).trace subset
    (.powerObjectMap po.id "transpose" #[← semanticObject X, predicate])
  return .element (← staged subset) P

/-- `{x₁, …, xₙ}` as a literal of the registered subset-literal form `form` of the power object
of `X`, when the form applies to `X` (its instances synthesize: decidable equality of `X`'s
elements); `none` where it does not (`ℝ`). The literal is `{x₁, …, xₙ}` written in Lean's own
notation at the form's type (`Insert`, `Singleton`, `EmptyCollection`), each `xᵢ` the element of
`X` it is, and the value is the form's denotation of it: the element of `𝒫(X)`. It is recorded as
that literal, which the realized reading sends as its elements. -/
partial def subsetLiteral (form : SubsetLiteralEntry) (xs : Array Syntax)
    (X P : Value) (readElement : Syntax → Nat → M Value) : M (Option Value) := do
  let .object p _ _ _ _ := P | unreachable!
  let one ← semanticObject (← oneObject)
  let expected ← mkAppM ``Quiver.Hom #[one, p]
  let denotation ← mkConstWithFreshMVarLevels form.denotation
  let (mvars, infos, type) ← forallMetaTelescopeReducing (← inferType denotation)
  unless ← isDefEq type expected do
    throwStratum .invalid m!"the literal form {form.id.raw} does not land in {p}"
  for (m, info) in mvars.zip infos do
    if info.isInstImplicit && (← instantiateMVars m).isMVar then
      match ← trySynthInstance (← instantiateMVars (← inferType m)) with
      | .some inst => discard <| isDefEq m inst
      | _ => return none
  let some literalMVar ← mvars.findM? fun m => do
      return (← instantiateMVars m).isMVar && (← instantiateMVars (← inferType m)).isAppOf form.type
    | throwStratum .invalid m!"the literal form {form.id.raw} takes no literal of {form.type}"
  let literalType ← instantiateMVars (← inferType literalMVar)
  let elements ← xs.zipIdx.mapM fun (x, i) => do
    let .element h _ ← coerceTo (← readElement x i) X
      | throwStratum .invalid m!"`{shown x}` is not an element of {← semanticObject X}"
    `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr h)
      $(← quoteExpr (← globalPoint)))
  let literal ← if elements.isEmpty then `((∅ : $(← quoteExpr literalType)))
    else `(({$elements:term,*} : $(← quoteExpr literalType)))
  let literal ← instantiateMVars (← elabTermEnsuringType literal literalType)
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq literalMVar literal do
    throwStratum .invalid m!"`{shown (mkNullNode xs)}` is not a literal of {form.id.raw}"
  let hom ← instantiateMVars (mkAppN denotation mvars)
  Trace.record (← read).trace hom (.literal form.id literal)
  return some (.element (← staged hom) P)

/-- A bound term with an explicit non-category `in X` ignores the set literal's ambient: `evalIn`
reads its declared object and evaluates its body there. -/
partial def explicitlyTypedSetElement (scope : Scope) (stx : Syntax) : M Bool := do
  if let `(cas_term| ($t)) := stx then return ← explicitlyTypedSetElement scope t
  if let `(cas_term| $t in $c) := stx then
    if let `(cas_term| $name:ident) := c then
      return !(← registryState).categories.any (·.name == name.getId.toString)
    return true
  if let `(cas_term| $name:ident) := stx then
    if let some t := scope.get? name.getId then
      return ← explicitlyTypedSetElement scope t
  return false

/-- `{x₁, …, xₙ}`, a subset of the enclosing `𝒫(X)` (else of the registered default domain):
the literal of the power
object's registered subset-literal form where it applies (`subsetLiteral`), else the union of
singletons. -/
partial def setLiteral (scope : Scope) (xs : Array Syntax) (ambient? : Option Value) : M Value := do
  let inferred? ← if ambient?.isNone then some <$> xs.mapM (eval scope ·) else pure none
  -- Without an enclosing `𝒫(X)`: the set its elements are in, else the published default.
  let P ← match ambient? with
    | some P => pure P
    | none =>
        let sets := inferred?.get!.filterMap fun | .element _ X => some X | _ => none
        match ← commonSet? sets, sets[0]? with
        | some X, _ | none, some X => powerSetOf X
        | none, none => powerSetOf (← notationObject "literal.finite_subset.domain")
  -- In a domain of subsets (`𝒫_fin(X) ↪ 𝒫(X)`): a set literal is a subset, in `𝒫(X)`, which the
  -- domain's elements are compared in along its inclusion.
  let P ← match ← powerOf? P, ← inclusionOut? P with
    | none, some (_, b) =>
        let .object _ category _ _ _ := P | unreachable!
        inclusionTargetValue P b category
    | _, _ => pure P
  let some (po, X) ← powerOf? P
    | throwStratum .invalid m!"a set literal is a subset: `in 𝒫(X)`"
  let .object p category _ _ _ := P | unreachable!
  let readElement (x : Syntax) (i : Nat) : M Value := do
    if let some inferred := inferred? then
      if ← explicitlyTypedSetElement scope x then return inferred[i]!
    eval scope x none (some X)
  -- The registered subset-literal form of the power object, where it applies to `X`.
  if let some form := (← registryState).subsetLiterals.find? (·.powerObject == po.id) then
    if let some literal ← subsetLiteral form xs X P readElement then return literal
  let singletonOf (x : Syntax) (i : Nat) : M Value := do
    let element ← coerceTo (← readElement x i) X
    applyTo (← `($(mkCIdent po.singleton) $(← paramTerms #[X])*)) #[element] P
  match xs.zipIdx.toList with
  | [] =>
      let .object one _ _ _ _ ← oneObject | unreachable!
      let empty ← homIn (← `($(mkCIdent po.empty) $(← paramTerms #[X])*)) one p category
      return .element (← staged empty) P
  | (x, i) :: rest =>
      let mut acc ← singletonOf x i
      for (y, j) in rest do acc ← applyOperation po.union #[acc, ← singletonOf y j] P
      return acc

/-- The registered product of `a` and `b`, or their coproduct if `colimit`. -/
partial def product (scope : Scope) (colimit : Bool) (a b : Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let symbol := if colimit then "⊔" else "×"
  let first ← asObject (← eval scope a category?)
  let first ← match category? with
    | some category => objectInCategory first category
    | none => pure first
  let .object x category _ _ _ := first
    | throwStratum .invalid m!"`{symbol}` is of objects"
  let second ← objectInCategory (← asObject (← eval scope b (some category))) category
  let .object y category' _ _ _ := second
    | throwStratum .invalid m!"`{symbol}` is of objects"
  unless category.id == category'.id do
    throwStratum .invalid m!"`{symbol}` of objects of {category.name} and {category'.name}"
  let shape := if colimit then "coproduct" else "product"
  let diagram ← standardDiagram shape
    #[.object x category none none none, .object y category none none none]
  let presentation ← limitIn colimit shape diagram category
  let apex ← apexOf colimit presentation
  Trace.alias (← read).trace presentation apex
  let source := Value.object apex category none none none
  return .object apex category none none (some (#[first, second], source, #[], #[], #[]))

end

/-- The outcome of a statement: it holds, or it fails in exactly one of the kinds that are never
collapsed (`specs/architecture.md`, "Failure is stratified"; policy 3). `invalid` and `ambiguous`
are semantic; `gap` (no admitted registration, or several), `unavailable` and `malformed` are
computational; `wrong` is a well-typed answer the statement refutes; `internal` is an exception
without a stratum: an error of the interpreter or exhausted resources, which says nothing about the
statement's mathematics. -/
inductive Outcome
  | holds
  | wrong (message : String)
  | gap (reason : String)
  | unavailable (reason : String)
  | malformed (reason : String)
  | invalid (reason : String)
  | ambiguous (reason : String)
  | internal (reason : String)
  deriving Inhabited, Repr

/-- The kind of an outcome, as the suite reports it. -/
def Outcome.kind : Outcome → String
  | .holds => "holds"
  | .wrong _ => "wrong"
  | .gap _ => "gap"
  | .unavailable _ => "unavailable"
  | .malformed _ => "malformed"
  | .invalid _ => "invalid"
  | .ambiguous _ => "ambiguous"
  | .internal _ => "internal"

/-- The detail of an outcome. -/
def Outcome.detail : Outcome → String
  | .holds => ""
  | .wrong m | .gap m | .unavailable m | .malformed m | .invalid m | .ambiguous m
  | .internal m => m

/-- Whether an outcome fails the suite: everything but a statement that holds, a gap and an
unavailable backend. -/
def Outcome.fails (o : Outcome) : Bool :=
  !(o matches .holds | .gap _ | .unavailable _)

/-- Classify failures at the interpretation boundary. A computational failure before a
complete question exists is an internal reader failure, rather than a missing leaf. -/
def Outcome.ofException (e : Exception) : TermElabM Outcome := do
  let message ← e.toMessageData.toString
  return match Exception.interpretationKind e with
    | .invalid => .invalid message
    | .ambiguous => .ambiguous message
    | .internal => .internal message

/-- `lit` as a value of the literal type `type`. -/
def literalExpr (type : Name) : Value → TermElabM Expr
  | .nat n => do
      let t ← `(($(Syntax.mkNumLit (toString n)) : $(mkIdent type)))
      instantiateMVars (← elabTermAndSynthesize t none)
  | .literal name => do
      let t ← `(($(mkIdent (type ++ name)) : $(mkIdent type)))
      instantiateMVars (← elabTermAndSynthesize t none)
  | _ => throwStratum .invalid m!"the right side of `=` is a literal"

/-- The comparison of the value `X` of `category` with the literal `literal`, read semantically:
the category's registered literal form, the literal as a value `L` of the form's type, and the
proposition `X = denote L`. -/
def literalClaim (state : RegistryState) (X : Expr) (category : NamedCategoryEntry)
    (literal : Value) : TermElabM (LiteralEntry × Expr × Expr) := do
  let some form := state.literals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered literal form"
  let L ← literalExpr form.type literal
  let denoted ← mkAppM form.denotation #[L]
  unless ← withTransparency .all <| isDefEq (← inferType X) (← inferType denoted) do
    throwStratum .invalid m!"a value of {category.name} is compared with a literal of another type"
  return (form, L, ← mkEq X denoted)

/-- The two sides of a comparison `l = r`, read and brought to the same set: elements as morphisms
`1 → X`, a numeral side as an element of the other's set, a named set compared with a subset as
its image there, elements of two included sets in the larger. -/
def comparands (scope : Scope) (l r : Syntax) : M (Value × Value) := do
  -- The side that determines the set is read first: a set literal is a subset of the other side's
  -- set; otherwise the right side's set is the left's.
  let setLiteral := match r with
    | `(cas_term| {$_,*}) => true
    | _ => false
  let (left, right) ← if setLiteral then do
      let left ← eval scope l
      let ambient := match left with
        | .element _ X => some X
        | _ => none
      pure (left, ← eval scope r none ambient)
    else do
      let right ← eval scope r
      let ambient := match right with
        | .element _ X => some X
        | _ => none
      pure (← eval scope l none ambient, right)
  -- Elements are compared as morphisms `1 → X`; a numeral side is an element of `X`.
  let (left, right) ← match left, right with
    | .element .., .element .. => pure (left, right)
    | .element _ X, _ => pure (left, ← toElement right X)
    | _, .element _ X => pure (← toElement left X, right)
    | _, _ => pure (left, right)
  -- A named set `Y` compared with a subset of `Z ⊇ Y`: its image in `Z` (`{0, 1, 2, ...} = ℕ`).
  let asSubset (v : Value) (P : Value) : M Value := do
    let (.object .., some (_, Z)) := (v, ← powerOf? P) | return v
    match ← coercionMap v Z with
    | some (some ι) => imageOfMap ι v Z
    | some none => imageOfMap (← identityAt v) v Z
    | none => return v
  let (left, right) ← match left, right with
    | .object .., .element _ P => pure (← asSubset left P, right)
    | .element _ P, .object .. => pure (left, ← asSubset right P)
    | _, _ => pure (left, right)
  -- Elements of two sets, one included in the other, are compared in the larger.
  match left, right with
  | .element _ X, .element _ Y =>
      if (← coercionMap Y X).isSome then pure (left, ← coerceTo right X)
      else if (← coercionMap X Y).isSome then pure (← coerceTo left Y, right)
      else pure (left, right)
  | _, _ => pure (left, right)

/-- Bind one original argument, possibly destructured, through the ordinary map reader. -/
partial def patternAbstraction (pattern body : Syntax) : TermElabM (TSyntax `cas_term) := do
  let body : TSyntax `cas_term := ⟨body⟩
  match pattern with
  | `(cas_term| $name:ident) => `(cas_term| $name:ident ↦ $body)
  | `(cas_term| ($inner)) => patternAbstraction inner body
  | _ =>
      unless pattern.getKind == ``casTuple do
        throwStratum .invalid "a map argument pattern contains only names and component tuples"
      return ⟨mkNode ``casPatternLambda (pattern.getArgs ++ #[mkAtom "↦", body.raw])⟩

/-- The name and term a `let` binds: `let x := t`; `let x : T := t` binds `t in T`;
`let f(t) := e in X → Y` binds `(t ↦ e) in X → Y`. -/
def letBinding? (stx : Syntax) : TermElabM (Option (Name × Syntax)) := do
  if stx.getKind == ``casLetPattern then
    let function := stx[1].getId
    let pattern := stx[3]
    let expression : TSyntax `cas_term := ⟨stx[6]⟩
    if let `(cas_term| $body in $target) := expression then
      return some (function, ← `(cas_term| $(← patternAbstraction pattern body) in $target))
    return some (function, ← patternAbstraction pattern expression)
  if stx.getKind == ``casLetArgs then
    let function := stx[1].getId
    let first : TSyntax `ident := ⟨stx[3]⟩
    let rest : Array (TSyntax `cas_term) ← stx[5].getSepArgs.mapM fun argument => do
      let argument : TSyntax `ident := ⟨argument⟩
      `(cas_term| $argument:ident)
    let first ← `(cas_term| $first:ident)
    let expression : TSyntax `cas_term := ⟨stx[8]⟩
    let bind (body : TSyntax `cas_term) : TermElabM (TSyntax `cas_term) :=
      `(cas_term| ($first, $rest,*) ↦ $body)
    if let `(cas_term| $body in $target) := expression then
      return some (function, ← `(cas_term| $(← bind body) in $target))
    return some (function, ← bind expression)
  match stx with
  | `(cas_stmt| let $x:ident := $t) => return some (x.getId, t)
  | `(cas_stmt| let $x:ident : $T := $t) => return some (x.getId, ← `(cas_term| $t in $T))
  | _ => return none

/-- The variables a term binds (`t` in `t ↦ e`, `{t ∈ X | P}`, `{e | t ∈ X}`, `∑_{t ∈ A} e`). -/
partial def binders (stx : Syntax) : Array Name :=
  let own : Array Name := match stx with
    | `(cas_term| $t:ident ↦ $_) => #[t.getId]
    | `(cas_term| {$t:ident ∈ $_ | $_}) => #[t.getId]
    | `(cas_term| {$_ | $t:ident ∈ $_}) => #[t.getId]
    | _ =>
      if stx.getKind == ``casPatternLambda then patternNames (lambdaPattern stx)
      else if stx.getKind == ``casBig then #[stx[2].getId]
      else if stx.getKind == ``casLimit then #[stx[1].getId]
      else if stx.getKind == ``casDefinite then
        #[stx[6].getId] ++ (differentialOf? stx[6].getId).toArray
      else #[]
  own ++ stx.getArgs.flatMap binders

/-- Whether a term is the variable `v`. -/
def isVariable (v : Name) (t : Syntax) : Bool :=
  match t with
  | `(cas_term| $x:ident) => x.getId == v
  | _ => false

/-- Every direct argument occurrence of a free variable, with its actual position and the
number of domain components supplied to that map. -/
partial def applicationsOf (v : Name) (stx : Syntax) : Array (Syntax × Nat × Nat) :=
  let own : Array (Syntax × Nat × Nat) := match stx with
    | `(cas_term| $f:ident($args,*)) =>
        args.getElems.zipIdx.filterMap fun (arg, index) =>
          if isVariable v arg then
            some ((Unhygienic.run `(cas_term| $f:ident)).raw, index, args.getElems.size)
          else none
    | `(cas_term| ($f)($args,*)) =>
        args.getElems.zipIdx.filterMap fun (arg, index) =>
          if isVariable v arg then some (f.raw, index, args.getElems.size) else none
    | _ => #[]
  own ++ stx.getArgs.flatMap (applicationsOf v)

/-- Independent variables share a stage formed by the registered products of their exact
domains. The returned elements are the composite projections from that one stage. -/
partial def variableStage (domains : Array Value) : M (Value × Array Value) := do
  let some first := domains[0]?
    | throwStratum .invalid m!"an independent symbol context has a domain"
  if domains.size == 1 then return (first, #[.element (← identityAt first) first])
  let (rest, tailVariables) ← variableStage (domains.extract 1 domains.size)
  let .object _ category .. := first | throwStratum .invalid m!"a symbol domain is an object"
  let diagram ← standardDiagram "product" #[first, rest]
  let presentation ← limitIn false "product" diagram category
  let apex ← apexOf false presentation
  Trace.alias (← read).trace presentation apex
  let source := Value.object apex category none none none
  let stage := Value.object apex category none none (some (#[first, rest], source, #[], #[], #[]))
  let #[head, tail] ← componentElements (.element (← identityAt stage) stage) 2
    | throwStratum .invalid m!"the registered product does not supply two symbol projections"
  let .element tailMap _ := tail | unreachable!
  let restHandle ← semanticObject rest
  let boundValues ← tailVariables.mapM fun symbol => do
    let .element arrow target := symbol | unreachable!
    let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[tailMap, arrow]
    unless ← isTypeCorrect composite do
      throwStratum .invalid m!"independent variables do not retain one common product stage"
    Trace.record (← read).trace composite
      (.morphismComposition category.id tailMap arrow apex restHandle (← semanticObject target))
    return Value.element composite target
  return (stage, #[head] ++ boundValues)

/-- Read `k` with the statement's free variables bound as projections from the registered
product of their selected domains: the statement is then about maps out of one common stage. -/
def withFreeVariables {α : Type} (scope : Scope) (stx : Syntax) (k : M α) : M α := do
  let state ← registryState
  -- The variables of its polynomial rings are their generators.
  let rings ← ringBindings scope stx
  withReader (fun ctx => { ctx with bound := rings ++ ctx.bound }) do
  let bound := binders stx
  let keywords := [`true, `false, `unknown, `«ℵ₀»]
  let ctx ← read
  -- A free symbol is an atomic name that nothing binds and the catalogue does not name.
  let named (n : Name) : Bool :=
    let s := n.toString
    (s == "id" || s == "reindex" || s == "cartesian" || s == "generator") || state.objects.any (·.name == s) || state.morphisms.any (·.name == s) ||
    state.presentations.any (·.name == s) ||
      (subscripted? s).any (fun (base, _) => state.objects.any (·.name == base)) ||
      state.categories.any (·.name == s) || state.methods.any (·.name == s) ||
      state.properties.any (·.name == s) || state.limits.any (·.shape == s)
  let free := (← contextualIdentifiers scope stx).filter fun n =>
    n.isAtomic && !bound.contains n && !scope.contains n && (ctx.bound.lookup n).isNone &&
      !keywords.contains n && !named n &&
      -- `dv`, the differential of a bound symbol `v`.
      !((differentialOf? n).any fun v => (ctx.bound.lookup v).isSome)
  let free := free.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]
  if free.isEmpty then return ← k
  let domains ← free.mapM fun symbol => do
    let uses := applicationsOf symbol stx
    if uses.isEmpty then throwStratum .invalid m!"the free symbol {symbol} is applied to no map"
    let domains ← uses.mapM fun (function, position, count) => do
      let .morphism _ _ _ _ (some (domain, _)) ← eval scope function
        | throwStratum .invalid m!"the free symbol {symbol} is applied to something that is not a map"
      if count == 1 then return domain
      let components ← componentElements (.element (← identityAt domain) domain) count
      let some (.element _ domain) := components[position]?
        | throwStratum .invalid m!"the free symbol has no component at its argument position"
      return domain
    let applicable ← domains.filterM fun domain =>
      domains.allM fun target => return (← coercionMap domain target).isSome
    let some selected := applicable[0]?
      | throwStratum .invalid m!"the maps of {symbol} have no common declared input domain"
    unless ← applicable.allM (identityCarrierView selected) do
      throwSemanticAmbiguity m!"the free symbol {symbol} has distinct selected input domains"
    return selected
  let (stage, boundValues) ← variableStage domains
  let bindings := (free.zip boundValues).toList
  withReader (fun ctx => { ctx with stage := some stage, bound := bindings ++ ctx.bound }) k

/-- What a statement claims, as its semantic reading forms it: the proposition to discharge in
Lean, and what to compute and compare when Lean does not decide it (`CasCatalogue.Realize`). -/
inductive Claim
  /-- A successfully read binding, which is not an assertion or a mathematical question. -/
  | binding
  | judged (question : Question) (prop : Expr) (expected : Option Bool) (shown : String)
  /-- `assert implemented X`: a registration computes the value `X`. -/
  | implemented (value : Expr)
  /-- `assert X = L` for a value `X` of `category` and the literal `L` of its registered literal
  form `form`: the proposition `prop` is `X = denote L`. -/
  | literal (X : Expr) (category : NamedCategoryEntry) (form : LiteralEntry) (L : Expr)
      (prop : Expr) (left right : String)
  /-- `assert f = g` for elements or morphisms of `category`: the proposition `prop` is `f = g`. -/
  | homs (f g : Expr) (category : NamedCategoryEntry) (prop : Expr) (left right : String)
  /-- `assert P`, `assert P = true | false | unknown`: the proposition `prop` and the expected
  decision (`none` for `unknown`). -/
  | decision (prop : Expr) (expected : Option Bool) (shown : String)

/-- The claim of the comparison `l = r`. -/
def claimEqual (scope : Scope) (l r : Syntax) : M Claim := do
  let state ← registryState
  let (left, right) ← comparands scope l r
  match left, right with
  | value@(.element ..), .literal decision =>
      let expected ← match decision with
        | `true => pure (some true)
        | `false => pure (some false)
        | `unknown => pure none
        | _ => throwStratum .invalid m!"a decision is `true`, `false` or `unknown`"
      let answer ← asAnswer value
      return .judged (value.question answer) answer expected s!"{shown l} = {shown r}"
  | .element f (.object _ category _ _ _), .element g _
  | .morphism f _ _ category _, .morphism g _ _ _ _ =>
      unless ← withTransparency .all <| isDefEq (← inferType f) (← inferType g) do
        throwStratum .invalid m!"`{shown l}` and `{shown r}` are not in the same set"
      return .homs f g category (← mkEq f g) (shown l) (shown r)
  | .element .., _ => throwStratum .invalid m!"an element is compared with an element"
  | .morphism .., _ => throwStratum .invalid m!"a morphism is compared with a morphism"
  | .object X category _ _ _, _ =>
      let (form, L, prop) ← literalClaim state X category right
      return .literal X category form L prop (shown l) (shown r)
  | value@(.answer answer), _ | value@(.judged _ answer), _ =>
      let expected ← match right with
        | .literal `true => pure (some true)
        | .literal `false => pure (some false)
        | .literal `unknown => pure none
        | _ => throwStratum .invalid m!"a decision is `true`, `false` or `unknown`"
      return .judged (value.question answer) answer expected s!"{shown l} = {shown r}"
  | _, _ => throwStratum .invalid m!"`{l}` is neither a value nor a decision"

/-- The claim of a statement, read semantically: what it states, from the catalogue alone. Its
failure is the statement's invalidity. -/
def claim (scope : Scope) (stx : Syntax) : M Claim := do
  if let some (_, t) ← letBinding? stx then
    let rings ← ringBindings scope t
    discard <| withReader (fun ctx => { ctx with bound := rings ++ ctx.bound }) (eval scope t)
    return .binding
  withFreeVariables scope stx do
  match stx with
  | `(cas_stmt| assert implemented $t:cas_term) =>
      match ← eval scope t with
      | .object handle .. => return .implemented handle
      | .element hom _ | .morphism hom .. => return .implemented hom
      | .answer answer | .judged _ answer => return .implemented answer
      | _ => throwStratum .invalid m!"`{shown t}` is not a value"
  | `(cas_stmt| assert $t in $X) =>
      -- `X in C/Y`: the object `X` refines into the category `C` over (under) `Y`.
      -- It is the catalogue's judgement.
      if let some (C, Y) := categoryOver? (← registryState) X then
        let v ← inCategoryOver scope t C Y
        let base ← eval scope Y
        return .judged (.judgement "in-over" (v.terms ++ base.terms) #[] (#[C.declaration] ++ v.declarations ++ base.declarations)) (mkConst ``True) (some true) (shown stx)
      -- A typing judgement: `t` is an element of the set `X`.
      match ← eval scope X with
      | .object x .. =>
          let v@(.element _ (.object y ..)) ← eval scope t
            | throwStratum .invalid m!"`{shown t}` is not an element"
          if x == y || (← withTransparency .all <| isDefEq x y) then
            return .judged (judgement "in" #[v, ← eval scope X]) (mkConst ``True) (some true) (shown stx)
          return .judged (judgement "in" #[v, ← eval scope X]) (mkConst ``False) (some true) (shown stx)
      | _ =>
          let v ← eval scope (← `(cas_term| $t in $X))
          return .judged (judgement "in" #[v]) (mkConst ``True) (some true) (shown stx)
  | `(cas_stmt| assert $p) =>
      if let `(cas_term| $l = $r) := p then return ← claimEqual scope l r
      if p.raw.getKind == ``casIs then return ← claimEqual scope p.raw[0] p.raw[2]
      let value ← eval scope p
      let answer ← asAnswer value
      return .judged (value.question answer) answer (some true) (shown p)
  | _ => throwStratum .invalid m!"not a statement of the language: {stx}"

end CasCatalogue.Language
