/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantic
public import CasCatalogue.Admission
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
* `N` or `N(a, …)`: the registered object named `N` at the numeral parameters `a, …`: the unrefined
  object of that name, or in an enclosing `in C` its refinement in `C` (`Fin(3) in FiniteSets`);
* `ℤ/n` is `ZMod(n)`, and `(ℤ/n)^k` is `ZModPower(n, k)`;
* `X × Y`, `X ⊔ Y`: the registered product and coproduct in the category of `X` and `Y`;
* `m(a, …)`: the registered morphism family named `m` at the numeral parameters `a, …`;
* `{x ↦ y, …} : X → Y`: the morphism with that graph, by the category's registered graph literal;
  `x`, `y` are numerals of the sets `X` and `Y` are;
* `id(X)` and `f ∘ g`: identities and composites;
* `x + y`, `x · y`, `-x`, `x - y` (`x + -y`): the registered operations of the category whose
  refinement of the set `X` the elements are in (the ring `ℤ/5` for elements of `ℤ/5`). An element
  of `X` is a morphism `1 → X` from the terminal set `Fin(1)`; a numeral is the image of `k` under
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
syntax:max cas_term:max noWs "." ident noWs "(" ")" : cas_term
/-- `f.m(a, …)`: the registered family `m` at `f` (a map, or an element), applied to `a, …`. -/
syntax:max (name := casCallWith) cas_term:max noWs "." ident noWs "(" cas_term,+ ")" : cas_term
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
/-- `(a)x`, `(a)x²`: a parenthesized coefficient times a variable (or its square or cube). -/
syntax:max (name := casCoefficient) "(" cas_term ")" noWs ident (noWs ("²" <|> "³"))? : cas_term
/-- `a dx`, `f dx`: juxtaposition, the product in a set both are in, else the registered action
`•` (a polynomial times a differential). -/
syntax:70 (name := casActed) cas_term:71 ident : cas_term
/-- `M * v`: juxtaposition written out. -/
syntax:70 (name := casTimes) cas_term:70 " * " cas_term:71 : cas_term
/-- A tuple `(x₁, …, xₙ)`, an element of `Xⁿ`. -/
syntax:max (name := casTuple) "(" cas_term ", " cas_term,+ ")" : cas_term
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
syntax "let " ident noWs "(" ident ")" " := " cas_term : cas_stmt
syntax "assert " &"implemented " cas_term : cas_stmt
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
  /-- The set of maps `source → target` of `Sets`: the ambient of a map `t ↦ e`. -/
  | homSet (source target : Value)
  /-- An element of the named set `object` (an `.object` value): a morphism `1 ⟶ object` from
  the terminal set `Fin(1)`. -/
  | element (hom : Expr) (object : Value)
  /-- The decision of a property: an `Option Bool`. -/
  | answer (answer : Expr)
  | judged (question : Question) (answer : Expr)
  deriving Inhabited

/-- The terms a value is (its object, morphism, element or answer), for the question of a judgement
about it. -/
partial def Value.terms : Value → Array Expr
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
  deriving Inhabited

/-- The language's evaluation monad: elaboration in a reading. -/
abbrev M := ReaderT Ctx TermElabM

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

/-- The registered object named `name`: in `category` when given (a refinement there), and
otherwise the unrefined object of that name. -/
def objectNamed (state : RegistryState) (name : String) (category? : Option NamedCategoryEntry) :
    TermElabM ObjectEntry := do
  let candidates := state.objects.filter fun o =>
    o.name == name && match category? with
      | some c => o.category == c.id
      | none => o.refines.isNone
  match candidates with
  | #[object] => return object
  | #[] => throwStratum .invalid m!"no registered object is named {name}{match category? with
      | some c => m!" in {c.name}" | none => m!""}"
  | _ => throwStratum .semanticAmbiguity m!"several registered objects are named {name}: state its \
      category (`in C`)"

/-- A term for an elaborated expression. -/
def quoteExpr (e : Expr) : TermElabM Term := exprToSyntax e

/-- A term as written. -/
def shown (stx : Syntax) : String := (stx.reprint.getD (toString stx)).trimAscii.toString

/-- Whether a term is written with numerals and arithmetic alone, naming nothing (`-1/2`, `3 · 4`,
`1.4142`): no identifier, root or absolute value. Such a term has no set of its own: it is read in
the enclosing set, else the set of its siblings, else the initial object its numerals come from
(`ℤ`, the initial ring; `ℚ`, the initial field of characteristic `0`, for a fraction or decimal). -/
partial def numeric (stx : Syntax) : Bool :=
  !stx.isIdent && !(stx.isAtom && (stx.getAtomVal == "√" || stx.getAtomVal == "|")) &&
    stx.getArgs.all numeric

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

/-- Whether a numeric term is a fraction or a decimal, whose numerals are those of `ℚ`. -/
partial def fractional (stx : Syntax) : Bool :=
  stx.isOfKind `scientific || (stx.isAtom && stx.getAtomVal == "/") || stx.getArgs.any fractional

/-- The object of the catalogue a set value is. -/
def semanticObject (v : Value) : M Expr := do
  let .object handle _ _ _ _ := v | throwStratum .invalid m!"a set is expected"
  return handle

/-- The parameters of a family, as terms of its mathematics: numerals, the objects of sets, and
elements. -/
def paramTerms (values : Array Value) : M (Array Term) :=
  values.mapM fun
    | .nat n => pure (Syntax.mkNumLit (toString n) : Term)
    | v@(.object ..) => do exprToSyntax (← semanticObject v)
    | .element handle _ | .morphism handle .. => exprToSyntax handle
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
    if (CasCatalogue.Exception.stratum? error) == some .invalid then pure false else throw error

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
    let targetTyped ← parameterCompatible do
      let family ← instantiateFresh target.declaration
      let objectType ← mkAppM ``CategoryTheory.Bundled.α #[family]
      isDefEq objectType expected
    unless targetTyped do continue
    for route in state.routes sourceCategory.expression target.expression do
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
          throwStratum .semanticAmbiguity m!"several comparisons determine a selected structural route"
        let #[candidate] := cls.sources
          | throwStratum .semanticAmbiguity m!"the selected object has no unique structural route"
        pure candidate
      | #[] => throwStratum .invalid m!"the selected object has no registered structure at this type"
      | _ => throwStratum .semanticAmbiguity m!"several routes give the selected object this structure \
          (source {sourceCategory.id.raw}, demanded type {expected}, receiver {receiver})"
    let (image, _) ← checkedRouteAction state sourceCategory.id target.id route.refs receiver expected
    return image

partial def typedParameter (expected : Expr) (value : Value) : M Expr := do
  let direct ← match value with
    | .nat n => pure (mkNatLit n)
    | .object handle .. | .element handle _ | .morphism handle .. => pure handle
    | _ => throwStratum .invalid m!"a parameter is a numeral, an object or an element"
  if ← parameterTrial (isDefEq (← inferType direct) expected) then
    unless ← isDefEq (← inferType direct) expected do unreachable!
    return direct
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
  let mut routeCandidates : Array (ObjectEntry × Route) := #[]
  for source in sources do
    let some sourceCategory := state.categories.find? (·.id == source.category) | continue
    for targetCategory in state.categories do
      let targetTyped ← parameterCompatible do
        let family ← instantiateFresh targetCategory.declaration
        let objectType ← mkAppM ``CategoryTheory.Bundled.α #[family]
        isDefEq objectType expected
      unless targetTyped do continue
      for route in state.routes sourceCategory.expression targetCategory.expression do
        let applicable ← parameterCompatible do
          let sourceTerm ← Semantic.object source (← typedParamTerms source.declaration parameters)
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
    for sourceId in sourceIds do
      let sourceCandidates := candidates.filter (·.1.id == sourceId)
      let classes := state.classify sourceCandidates (fun c => c.1.id.raw) (·.2)
      let candidate ← match classes with
        | #[cls] =>
          unless cls.ambiguities.isEmpty do
            throwStratum .semanticAmbiguity m!"several registered comparisons determine a parameter route"
          let #[candidate] := cls.sources
            | throwStratum .semanticAmbiguity m!"a parameter has no unique registered source route"
          pure candidate
        | _ => throwStratum .semanticAmbiguity m!"a selected source has unresolved parameter routes"
      sourceChoices := sourceChoices.push candidate
    if sourceChoices.isEmpty then
      throwStratum .invalid m!"{origin.name} has no registered structure at the parameter's type"
    let selectedCandidates := sourceChoices.qsort fun left right =>
      let leftKey := left.1.id.raw ++ reprStr left.2.refs
      let rightKey := right.1.id.raw ++ reprStr right.2.refs
      leftKey < rightKey
    let mut presentations : Array ParameterPresentation := #[]
    let mut representative? : Option Expr := none
    for (source, route) in selectedCandidates do
      let sourceTerm ← Semantic.object source (← typedParamTerms source.declaration parameters) (← read).trace
      let some target := state.categories.find? (·.expression.syntacticEq route.target)
        | throwStratum .invalid m!"a parameter route has no registered target category"
      let (image, applications) ← checkedRouteAction state source.category target.id
        route.refs sourceTerm expected
      unless !image.hasMVar && (← isDefEq (← inferType image) expected) && (← isTypeCorrect image) do
        throwStratum .invalid m!"a structural parameter is outside its complete declared type"
      let representative := representative?.getD image
      unless ← withTransparency .all <| isDefEq image representative do
        throwStratum .semanticAmbiguity m!"several distinct full structures determine a parameter of {origin.name}"
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
  let quote : Value → TermElabM Term
    | .object handle .. => quoteExpr handle
    | .morphism hom .. => quoteExpr hom
    | _ => throwStratum .invalid m!"the diagram of a {shape} is of objects and morphisms"
  let state ← registryState
  let category? := args[0]?.bind fun
    | .object _ category _ _ _ | .morphism _ _ _ category _ => some category
    | _ => none
  if let some category := category? then
    let rows := state.limits.filter fun row => row.shape == shape && row.category == category.id
    match rows with
    | #[row] => return ← quoteExpr (← declaredDiagram row args)
    | #[] => pure ()
    | _ => throwStratum .semanticAmbiguity m!"several registered presentations own this diagram"
  let ts ← args.mapM (liftM ∘ quote)
  match shape, ts with
  | "pullback", #[f, g] => `(CategoryTheory.Limits.cospan $f $g)
  | "pushout", #[f, g] => `(CategoryTheory.Limits.span $f $g)
  | "product", #[x, y] | "coproduct", #[x, y] => `(CategoryTheory.Limits.pair $x $y)
  | "equalizer", #[f, g] | "coequalizer", #[f, g] => `(CategoryTheory.Limits.parallelPair $f $g)
  | "kernel", #[f] | "cokernel", #[f] =>
      -- The zero morphism between the handles, as the preimage of the zero of the category.
      let .morphism _ a b category _ := args[0]! | unreachable!
      let zero ← homIn (← `(0)) a b category
      `(CategoryTheory.Limits.parallelPair $f $(← quoteExpr zero))
  | _, _ => throwStratum .invalid m!"a {shape} of {args.size} arguments has no standard diagram"

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
  | .app .. | .const .. =>
      let f := e.getAppFn
      if let .const c _ := f then
        if plumbingRoots.any (·.isPrefixOf c) && (← plumbingApplication e) then
          if let some e' ← unfoldDefinition? e then return ← plumbingValue e'
          if let some e' ← unfoldProjInst? e then return ← plumbingValue e'
      let args ← e.getAppArgs.mapM fun a => do
        if (← isProp (← inferType a)) || (← isType a) then pure a else plumbingValue a
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

/-- Expose the stored action of a supplied closed categorical map, while preserving registered
comparison and operation declarations before any value reduction. -/
def suppliedHomPresentation (state : RegistryState) (p : Expr) : MetaM Expr :=
  Meta.transform p (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
      return .continue
    -- Guard the complete supplied object before any value WHNF or projection reduction.
    let protectedDeclarations := state.presentations.map (·.declaration) ++ state.operations.map (·.declaration)
    if (e.find? fun part => part.constName?.any protectedDeclarations.contains).isSome then
      return .continue
    let originalType ← inferType e
    let type ← withTransparency .all <| whnf originalType
    unless type.isAppOf ``TypeCat.Hom do return .continue
    let bundled ← mkAppM ``TypeCat.Hom.hom #[e]
    let action ← mkAppM ``TypeCat.Fun.toFun #[bundled]
    let action ← withTransparency .all <| whnf action
    let normalized ← mkAppM ``TypeCat.ofHom #[action]
    if normalized.hasMVar || normalized.hasLevelMVar || normalized.hasFVar || normalized.hasLooseBVars then
      throwError "closed Hom action retained unresolved data"
    unless ← isTypeCorrect normalized do throwError "closed Hom action is ill-typed"
    unless ← withTransparency .all <| isDefEq (← inferType normalized) originalType do
      throwError "closed Hom action changed its complete type"
    unless ← withTransparency .all <| isDefEq normalized e do
      throwError "closed Hom action changed its supplied value"
    return .done normalized) (skipConstInApp := true)

/-- Expose only supplied closed data presentations. A class dictionary may use the ordinary
instance presentation only when its complete data are definitionally identical to the supplied
package. Predicate heads, binders and chosen data remain the same original typed statement. -/
def evidencePresentation (state : RegistryState) (p : Expr) : MetaM Expr := do
  let objectTypes ← IO.mkRef ({} : Std.HashMap Expr Bool)
  let expose (p : Expr) : MetaM Expr :=
    Meta.transform p (post := fun e => do
      if e.hasMVar || e.hasLevelMVar || e.hasFVar || (← isProof e) || (← isProp e) then
        return .continue
      let type ← inferType e
      let classData := (← isClass? type).isSome
      let carrierAlias := !e.isConst && (← isType e) && !(← isProp e)
      let mut objectData := false
      unless classData || carrierAlias do
        if let some cached := (← objectTypes.get).get? type then
          objectData := cached
        else
          for category in state.categories do
            if ← withoutModifyingState do
                try
                  let family ← instantiateFresh category.declaration
                  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
                  withTransparency .all <| isDefEq expected type
                catch _ => pure false then
              objectData := true
              break
          unless type.hasMVar || type.hasLevelMVar do
            objectTypes.modify (·.insert type objectData)
      if objectData || classData || carrierAlias then
        let normalized ← if carrierAlias && !objectData && !classData then
          whnfR e
        else withTransparency .all <| whnf e
        unless ← withTransparency .all <| isDefEq normalized e do
          throwError "a supplied data presentation changed its complete object"
        return .done normalized
      return .continue) (skipConstInApp := true)
  let presented ← expose (← expose p)
  let presented ← Meta.transform presented (post := fun e => do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || (← isProof e) then return .continue
    let type ← inferType e
    unless (← isClass? type).isSome do return .continue
    let candidate? ← withoutModifyingState do
      try
        let candidate ← instantiateMVars (← synthInstance type)
        if candidate.hasMVar || candidate.hasLevelMVar || candidate.hasSorry ||
            !(← isTypeCorrect candidate) then return none
        unless ← withTransparency .all <| isDefEq candidate e do return none
        return some candidate
      catch _ => return none
    match candidate? with
    | none => return .continue
    | some candidate =>
        unless ← withTransparency .all <| isDefEq (← inferType candidate) type do
          throwError "a supplied dictionary presentation changed its complete type"
        return .done candidate) (skipConstInApp := true)
  let presented ← Core.betaReduce presented
  let presented ← suppliedHomPresentation state presented
  unless !presented.hasMVar && !presented.hasLevelMVar &&
      (← isTypeCorrect presented) &&
      (← withTransparency .all <| isDefEq presented p) do
    throwError "the evidence presentation is not the original complete target"
  return presented

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
  let .object a category (some (source, sourceParams)) _ _ := a
    | throwStratum .invalid m!"the domain of a graph is a named object"
  let .object b category' (some (target, targetParams)) _ _ := b
    | throwStratum .invalid m!"the codomain of a graph is a named object"
  unless category.id == category'.id do
    throwStratum .invalid m!"a graph from {category.name} to {category'.name}"
  let some form := state.graphLiterals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered graph literals"
  let some one := state.objects.find? (·.id.raw == "obj.sets.fin") | unreachable!
  let one ← Semantic.object one #[Syntax.mkNumLit "1"]
  -- The element `k` of the named object: its numeral in the set it is, at the point of `1`.
  let element (object : ObjectEntry) (params : Array Value) (k : Nat) : M Term := do
    let set ← setOf state object
    let params ← paramTerms params
    let x ← Semantic.object set params
    let refinements ← (state.objects.filter (·.refines.any (·.base == set.id))).mapM fun o =>
      return (o.category, ← Semantic.object o params)
    let some numeral ← numeralIn state k one x refinements
      | throwStratum .invalid m!"no registered numeral lands in {object.name}"
    `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr numeral) 0)
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
  return .morphism hom a b category none

-- Compilation of this mutually recursive reader needs additional reduction work as its
-- provenance payload grows. This local option does not alter caller/probe interpretation budgets.
set_option maxHeartbeats 400000 in
mutual

/-- The value of a term, in the category `category?` of an enclosing `in C`. -/
partial def eval (scope : Scope) (stx : Syntax) (category? : Option NamedCategoryEntry := none)
    (ambient? : Option Value := none) : M Value := do
  let state ← registryState
  match stx with
  | `(cas_term| view $receiver along $functor:ident) =>
      registeredFunctorView (← eval scope receiver) functor.getId.toString #[]
  | `(cas_term| view $receiver along $functor:ident($arguments,*)) =>
      registeredFunctorView (← eval scope receiver) functor.getId.toString
        (← arguments.getElems.mapM (eval scope ·))
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
              let some po := state.powerObjects[0]? | throwStratum .invalid m!"no power object"
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
      return .homSet (← carrierObject (← asObject (← eval scope a)))
        (← carrierObject (← asObject (← eval scope b)))
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
      let A ← eval scope X
      -- `{t ∈ A | P}` for a subset `A ⊆ X` is `A ∩ {t ∈ X | P}`.
      if let some (_, base) ← powerSetOf? A then
        let P ← powerSetOf base
        return ← applyOperation "∩" #[A, ← comprehension scope t.getId base p] P
      comprehension scope t.getId (← asObject A) p
  | `(cas_term| {$e | $t:ident ∈ $X}) => imageOf scope e t.getId (← asObject (← eval scope X))
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
          eval scope t category? ambient?
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
          if receiver.isAnonymous || state.objects.any (·.name == f.getId.toString) then
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
      let .morphism f' b c category fSets ← eval scope f category?
        | throwStratum .invalid m!"`∘` composes morphisms"
      let .morphism g' a b' category' gSets ← eval scope g (some category)
        | throwStratum .invalid m!"`∘` composes morphisms"
      unless category.id == category'.id && (← isDefEq b b') do
        throwStratum .invalid m!"`{shown f} ∘ {shown g}`: the target of {shown g} is not the \
          source of {shown f}"
      let sets := match gSets, fSets with
        | some (X, _), some (_, Z) => some (X, Z)
        | _, _ => none
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[g', f']
      Trace.record (← read).trace composite
        (.morphismComposition category.id g' f' a b c)
      return .morphism composite a c category sets
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
          -- Quotient arithmetic denotes its registered ring; expose its declared carrier
          -- while retaining that full chosen structure when no category is requested.
          let some rings := state.categories.find? (·.id == CategoryId.rings)
            | throwStratum .invalid m!"quotient arithmetic has no registered ring category"
          let quotient ← object state "ZMod" #[← eval scope n] (some rings)
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
    | _ => throwStratum .semanticAmbiguity m!"several registered presentations map these selected endpoints"
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
    return ← applyNamed state "∫" #[← eval scope stx[1]]
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
  named scope f.getId.toString args category?

/-- The set a term's numerals are read in: the enclosing one; for a term of numerals alone, else
`ℚ` (a fraction or decimal: the initial field of characteristic `0`) or `ℤ` (the initial ring). -/
partial def numeralSet (stx : Syntax) (ambient? : Option Value) : M (Option Value) := do
  if ambient?.isSome || !numeric stx then return ambient?
  some <$> object (← registryState) (if fractional stx then "ℚ" else "ℤ") #[] none

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
      !#[`id, `generator, `reindex, `true, `false, `unknown].contains name
  let names := names.foldl (fun found name =>
    if found.contains name then found else found.push name) #[]
  match names.toList with
  | [] => return []
  | [name] => return [(name, ← generatorOf X)]
  | _ => throwStratum .semanticAmbiguity m!"a distinguished generator has several local variable names"

/-- Explicit generator scopes remove only their locally bound occurrences from free variables. -/
partial def contextualIdentifiers (scope : Scope) (term : Syntax) : M (Array Name) := do
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
      return ← eval scope t (some (← categoryNamed state name.getId.toString)) ambient?
  if let some (C, Y) := categoryOver? state c then return ← inCategoryOver scope t C Y
  -- `t in X` for a set `X`: `t` with its numerals in `X`.
  let ambient ← eval scope c
  let X ← match ambient with
    | .object .. => carrierObject ambient
    | _ => pure ambient
  let locals ← localGeneratorBindings scope t c X
  withReader (fun context => { context with bound := locals ++ context.bound }) do
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
  | .object _ _ none (some _) _ =>
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
      object state "ZModPower" #[← eval scope n, ← eval scope k] category?
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

/-- The registered object `name` at the numeral parameters `args`. -/
partial def registeredFunctorView (receiver : Value) (id : String)
    (parameters : Array Value) : M Value := do
  let .object object sourceCategory .. := receiver
    | throwStratum .invalid m!"a functor view acts on an object"
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == id)
    | throwStratum .invalid m!"no registered functor has identity {id}"
  unless sourceCategory.expression.syntacticEq entry.source do
    throwStratum .invalid m!"the selected object is outside the functor's declared source category"
  let recorder ← Trace.new
  let (image, target) ← Semantic.applyRegisteredFunctor entry object
    (← typedParamTerms entry.declaration parameters) (some recorder)
  let some (.functor recordedId arguments recordedReceiver) ← recorder.node? image
    | throwStratum .invalid m!"the functor view has no retained actual application"
  unless recordedId == entry.id && (← isDefEq recordedReceiver object) do
    throwStratum .invalid m!"the recorded functor action differs from the selected source"
  let declared ← instantiateFresh entry.declaration
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let explicit := (declared.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  unless explicit.size == arguments.size do
    throwStratum .invalid m!"the functor view lost its full declaration parameters"
  for (parameter, argument) in explicit.zip arguments do
    unless ← isDefEq parameter argument do
      throwStratum .invalid m!"the functor view changed a chosen declaration parameter"
  let complete ← if (← whnfR (← inferType declared)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declared] else pure declared
  let checked ← Semantic.objOf complete object
  unless ← isDefEq checked image do
    throwStratum .invalid m!"the full retained functor action differs from its actual image"
  let complete ← instantiateMVars complete
  unless !complete.hasMVar && !complete.hasLevelMVar && (← isTypeCorrect complete) do
    throwStratum .invalid m!"the full functor action retains unresolved arguments"
  Trace.record (← read).trace image (.functor entry.id arguments object)
  let value ← try recognize state image target catch error =>
    if (CasCatalogue.Exception.stratum? error) == some .invalid then
      pure (Value.object image target none none none)
    else throw error
  let .object handle category origin selected _ := value | unreachable!
  let edge := EdgeRef.functor entry.id
  return .object handle category origin selected
    (some (#[receiver], receiver, #[edge], #[], #[(edge, complete.getAppArgs)]))

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
    if (CasCatalogue.Exception.stratum? error) != some .invalid then throw error
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
    if (CasCatalogue.Exception.stratum? error) == some .invalid then
      pure (Value.object actual category none none none)
    else throw error
  let .object handle target origin selected _ := value | unreachable!
  return .object handle target origin selected (some (#[original], source, route, alternatives, applications))

partial def object (state : RegistryState) (name : String) (args : Array Value)
    (category? : Option NamedCategoryEntry) : M Value := do
  let entry ← objectNamed state name category?
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the object {name} has an unregistered category"
  let params ← typedParamTerms entry.declaration args
  let handle ← Semantic.object entry params (← read).trace
  let family ← instantiateFresh category.declaration
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[family]
  unless ← isDefEq (← inferType handle) expected do
    throwStratum .invalid m!"the parameters of {entry.name} do not form an object of {category.name}"
  if handle.hasMVar then
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
              | _ => throwStratum .semanticAmbiguity m!"a selected constructor parameter has several categories"
            if selectedCategory.id == CategoryId.sets then carrierObject value
            else structuredParameterView value actual selectedCategory
      | _ => pure value
    retained := retained.push value
  return .object handle category (some (entry, retained)) none none

/-- The method or property `name` of the object `t`. -/
partial def call (scope : Scope) (t : Syntax) (name : String)
    (category? : Option NamedCategoryEntry) : M Value := do
  let state ← registryState
  let receiver ← eval scope t category?
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
    let arrowExpression := CategoryExpr.construct ConstructorId.arrow #[.category sourceCategory.expression]
    let arrowCategories := state.categories.filter (·.expression.syntacticEq arrowExpression)
    let arrowCategory ← match arrowCategories with
      | #[category] => pure category
      | #[] => throwStratum .invalid m!"the map's arrow category is not registered"
      | _ => throwStratum .semanticAmbiguity m!"several registered categories identify this map's arrow category"
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
            if (CasCatalogue.Exception.stratum? error) == some .invalid then
              pure (.object term sourceCategory none none none)
            else throw error
        let X ← endpoint source
        let Y ← endpoint target
        Trace.record (← read).trace hom (.arrowProjection handle)
        return .morphism hom source target sourceCategory (some (X, Y))
  -- An invariant of the object (`R.dimension()`): a registered family of elements `1 → T`
  -- indexed by the object.
  if !state.methods.any (·.name == name) && !state.properties.any (·.name == name) then
    if let some entry := state.morphisms.find? (·.name == name) then
      return ← invariantOf entry receiver
  let isProperty := state.properties.any (·.name == name) && !state.methods.any (·.name == name)
  if isProperty then return .answer (← Semantic.property name handle category (← read).trace)
  let (value, target) ← Semantic.method name handle category (← read).trace
  return .object value target none none none

/-- The identifier `name` applied to `args`: `id`, or the unique registered object, morphism family or
(co)limit shape of that name. -/
partial def named (scope : Scope) (name : String) (args : Array Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let state ← registryState
  if name == "generator" then
    let #[objectSyntax] := args
      | throwStratum .invalid m!"`generator` takes one registered object"
    return ← generatorOf (← eval scope objectSyntax category?)
  if name == "reindex" then
    let #[objectSyntax, morphismSyntax] := args
      | throwStratum .invalid m!"`reindex` takes an object and a base morphism"
    let .object receiver category _ _ _ ← eval scope objectSyntax category?
      | throwStratum .invalid m!"reindexing acts on an object of a registered fibre"
    let .morphism baseMorphism .. ← eval scope morphismSyntax
      | throwStratum .invalid m!"reindexing requires a typed base morphism"
    let (value, target) ← Semantic.reindex receiver category baseMorphism (← read).trace
    return .object value target none none none
  if name == "id" then
    let #[x] := args | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let X ← eval scope x category?
    let .object a category _ _ _ := X
      | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let hom ← homIn (← `(CategoryTheory.CategoryStruct.id _)) a a category
    Trace.record (← read).trace hom (.morphismIdentity category.id a)
    return .morphism hom a a category (some (X, X))
  -- `Mat₂(ℚ)`: a subscript is the leading numeral parameter.
  if let some (base, k) := subscripted? name then
    if state.objects.any (·.name == base) && !state.objects.any (·.name == name) then
      return ← object state base (#[.nat k] ++ (← args.mapM (eval scope · none))) category?
  let inScope (c : CategoryId) := category?.all (c == ·.id)
  let objects := state.objects.filter fun o =>
    o.name == name && inScope o.category && (category?.isSome || o.refines.isNone)
  let morphisms := state.morphisms.filter fun m => m.name == name && inScope m.category
  let shapes := state.limits.filter (·.shape == name)
  let mut actions : Array (M Value) := #[]
  let mut objectCategories : Array CategoryId := #[]
  for entry in objects do
    unless objectCategories.contains entry.category do
      objectCategories := objectCategories.push entry.category
      if let some category := state.categories.find? (·.id == entry.category) then
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
        match state.resolveLimit category.id name row.colimit with
        | .error message => throwStratum .invalid m!"{message}"
        | .ok _ => pure ()
        let presentation ← limitIn row.colimit name (← standardDiagram name values) category
        let apex ← apexOf row.colimit presentation
        Trace.alias (← read).trace presentation apex
        return .object apex category none none none)
  let mut compatible : Array (M Value) := #[]
  for action in actions do
    if ← parameterCompatible (do discard action; pure true) then
      compatible := compatible.push action
  match compatible.toList with
  | [action] => action
  | [] => throwStratum .invalid m!"no registered signature named {name} applies to these arguments"
  | _ => throwStratum .semanticAmbiguity m!"several complete registered signatures named {name} apply to these arguments"

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
    for parameter in explicit do
      let some argumentSyntax := args[parameters.size]? | break
      let value ← eval scope argumentSyntax
      let expected ← instantiateMVars (← inferType parameter)
      unless ← parameterCompatible (do
          let term ← typedParameter expected value
          isDefEq parameter term) do break
      let term ← typedParameter expected value
      discard <| isDefEq parameter term
      parameters := parameters.push value
    return ← applyFamily entry.declaration category
      (← (args.extract parameters.size args.size).mapM (eval scope · none))
      (parameters := parameters)
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
  Semantic.namedMorphism entry semantic (← read).trace
  let type ← instantiateMVars (← inferType semantic)
  let some (source, target) := match type.getAppFn.constName?, type.getAppArgs with
      | some ``Quiver.Hom, #[_, _, x, y] => some (x, y)
      | _, _ => none
    | throwStratum .invalid m!"{entry.name} is not a family of morphisms"
  let targetValue ← recognize state target category
  let applied := args.extract arity args.size
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
      let X ← recognize state set category
      toElement (← eval scope arg none (some X)) X
    let numerals ← (args.extract 0 arity).mapM fun parameterSyntax => do
      let .nat n ← eval scope parameterSyntax
        | throwStratum .invalid m!"a leading family parameter is a numeral"
      return n
    return ← applyFamily entry.declaration category elements (some targetValue) (numerals := numerals)
  let .object b _ _ _ _ := targetValue
    | throwStratum .invalid m!"the target of {entry.name} is not an object"
  let sourceValue ← recognize state source category
  let .object a _ origin _ _ := sourceValue
    | throwStratum .invalid m!"the source of {entry.name} is not an object"
  let hom ← homIn (← quoteExpr semantic) a b category
  Semantic.namedMorphism entry hom (← read).trace
  -- A morphism from the terminal set `Fin(1)` is an element.
  if let some (object, #[.nat 1]) := origin then
    if object.name == "Fin" then return .element hom targetValue
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
      throwStratum .semanticAmbiguity m!"distinct full structures supply a declaration parameter"
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

/-- The object `x` of `category` as the registered object it is (reducibly) at numeral
parameters. -/
partial def recognize (state : RegistryState) (x : Expr) (category : NamedCategoryEntry)
    (known : Array Value := #[]) :
    M Value := do
  if !x.hasMVar then
    let mut matchedValues : Array Value := #[]
    for candidate in known do
      let candidate ← try
        match candidate with
        | .object .. => if category.id == CategoryId.sets then carrierObject candidate else pure candidate
        | _ => continue
      catch error =>
        if (CasCatalogue.Exception.stratum? error) == some .invalid then continue else throw error
      let .object handle candidateCategory origin .. := candidate | continue
      unless candidateCategory.id == category.id do continue
      let declared := state.objects.filter (fun row =>
        row.category == category.id && some row.declaration == x.getAppFn.constName?)
      if !declared.isEmpty && !origin.any (fun (entry, _) => declared.any (·.id == entry.id)) then
        continue
      if ← parameterTrial (withTransparency .all <| isDefEq handle x) then
        unless ← matchedValues.anyM (fun existing => parameterTrial do
            unless existing.declarations == candidate.declarations do return false
            let left := existing.terms
            let right := candidate.terms
            unless left.size == right.size do return false
            (left.zip right).allM fun (a, b) => withTransparency .all <| isDefEq a b) do
          matchedValues := matchedValues.push candidate
    match matchedValues.toList with
    | [candidate] => return candidate
    | [] => pure ()
    | _ => throwStratum .semanticAmbiguity m!"several complete selected values give this declared endpoint"
  let mut found : Array (ObjectEntry × Array Expr) := #[]
  -- Identity by declaration (b0-selected-structure): an expression that is a registered object's
  -- declaration applied to its parameters is that object, never another object whose carrier it
  -- also unfolds to (`(ℤ/n)^k` and `Vec` share `Fin k → ℤ/n`). Only an expression that is no
  -- object's declaration is matched by unfolding, and then only a unique match is an object.
  let head := (← instantiateMVars x).getAppFn.constName?
  let declared := state.objects.filter fun e => e.category == category.id && some e.declaration == head
  for entry in (if declared.isEmpty then state.objects.filter (·.category == category.id) else declared) do
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    let (args, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let params? ← (withoutModifyingState do
      if head == some entry.declaration then
        let actualArgs := x.getAppArgs
        unless actualArgs.size == args.size do return none
        for (parameter, actual) in args.zip actualArgs do
          unless ← isDefEq (← inferType parameter) (← inferType actual) <&&>
              isDefEq parameter actual do return none
        unless ← isTypeCorrect (← instantiateMVars (mkAppN declaration args)) do return none
      else
        unless ← withReducible (isDefEq (mkAppN declaration args) x) do return none
      let explicit := (args.zip infos).filterMap fun (a, i) => if i.isExplicit then some a else none
      return some (← explicit.mapM instantiateMVars) : MetaM _)
    if let some params := params? then
      if params.all (!·.hasMVar) then found := found.push (entry, params)
  let #[(entry, params)] := found
    | throwStratum .invalid m!"{x} is not a unique registered object of {category.name}"
  -- Its parameters: numerals, or sets (`𝒫(ℤ[x])`), recognized in turn.
  let values ← params.mapM fun p => do
    if let some n ← (Meta.evalNat p).run then return Value.nat n
    if let some (source, target) := homEnds? (← inferType p) then
      let sourceValue ← recognize state source category known
      let targetValue ← recognize state target category known
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
      | _ => throwStratum .semanticAmbiguity m!"a parameter of {entry.name} has several registered categories"
    -- A registered declaration may own an exact bundled parameter without giving it
    -- a separate named-object row. Retain that selected value rather than replacing
    -- it with a carrier or guessing a named refinement.
    if ← parameterCompatible (do
        discard <| recognize state p parameterCategory known
        pure true) then
      recognize state p parameterCategory known
    else
      unless ← isTypeCorrect p do
        throwStratum .invalid m!"a registered object's structure parameter is not typed"
      let mut witnesses : Array Value := #[]
      let sourceValues := known.flatMap sourceParameterValues
      let selected := sourceValues.filter fun
        | .object _ candidateCategory _ selected _ =>
            candidateCategory.id != CategoryId.sets || selected.isSome
        | _ => false
      for candidate in (if selected.isEmpty then sourceValues else selected) do
        if ← parameterCompatible (do
            let image ← typedParameter (← inferType p) candidate
            isDefEq image p) then
          unless witnesses.any (fun existing =>
              existing.declarations == candidate.declarations && existing.terms == candidate.terms) do
            witnesses := witnesses.push candidate
      if !witnesses.isEmpty then
        let views ← witnesses.mapM fun original => do
          let chosen := match original with
            | .object _ _ _ (some selected) _ => selected
            | _ => original
          if let .object handle chosenCategory origin selected _ := chosen then
            if chosenCategory.id == parameterCategory.id &&
                (← isDefEq (← inferType handle) (← inferType p)) &&
                (← withTransparency .all <| isDefEq handle p) then
              return Value.object handle chosenCategory origin selected
                (some (#[original], chosen, #[], #[], #[]))
          structuredParameterView original p parameterCategory
        let evidence ← coalesceSelectedParameterViews (← inferType p) p views
        let (_, _, _, alternatives, _) := evidence
        unless alternatives.isEmpty do
          Trace.record (← read).trace p
            (.parameterEquivalence (← inferType p) p alternatives)
        return .object p parameterCategory none none (some evidence)
      else pure (.object p parameterCategory none none none)
  object state entry.name values (some category)

/-- The named set supplied by the exact registered refinement of a structured object.
The structured value remains the family's parameter; this viewData stages its elements. -/
partial def carrierObject (value : Value) : M Value := do
  let .object handle category origin _ viewData := value
    | throwStratum .invalid m!"a carrier belongs to a selected structured object"
  if category.id == CategoryId.sets then return value
  let state ← registryState
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
  let some entry := state.morphisms.find? (·.name == name)
    | throwStratum .invalid m!"no registered function of elements is named {name}"
  let some category := state.categories.find? (·.id == entry.category) | unreachable!
  applyFamily entry.declaration category elements target?

/-- Select a registered structured parameter through its actual structured forgetful image. -/
partial def registeredStructuredParameter (expected : Expr) (operand : Value) : M (Option Expr) := do
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.isSort then return none
  let state ← registryState
  let originalValues := sourceParameterValues operand
  let instantiate (entry : ObjectEntry) : M (Expr × NamedCategoryEntry) := do
    let some category := state.categories.find? (·.id == entry.category)
      | throwStratum .invalid m!"a registered parameter has no category"
    let constant ← mkConstWithFreshMVarLevels entry.declaration
    let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
    unless ← isDefEq type expected do
      throwStratum .invalid m!"the registered parameter has a different declared type"
    synthesizeInstances args infos
    let object ← instantiateMVars (mkAppN constant args)
    if object.hasMVar || !(← isTypeCorrect object) then
      throwStratum .invalid m!"the registered parameter's actual arguments are not determined"
    return (object, category)
  let mut candidates := #[]
  for entry in state.objects do
    if ← parameterCompatible (do
        let (object, sourceCategory) ← instantiate entry
        let selected := Value.object object sourceCategory (some (entry, #[])) none none
        for targetCategory in state.categories do
          if targetCategory.id == CategoryId.sets || targetCategory.id == sourceCategory.id then continue
          if (state.routes sourceCategory.expression targetCategory.expression).isEmpty then continue
          let family ← instantiateFresh targetCategory.declaration
          let targetType ← mkAppM ``CategoryTheory.Bundled.α #[family]
          for original in originalValues do
            let .object originalHandle originalCategory originalOrigin _ _ := original | continue
            let directType ← parameterTrial (isDefEq targetType (← inferType originalHandle))
            let declaredAcquisition := originalCategory.id == CategoryId.sets &&
              (originalOrigin.map fun (origin, _) => state.objects.any fun source =>
                source.category == targetCategory.id && refinesObject state source origin.id).getD false
            -- A full retained original or its declared named refinement supplies the witness.
            -- An anonymous carrier cannot acquire a missing structure.
            unless directType || declaredAcquisition do continue
            if ← parameterCompatible (do
                let actual ← typedParameter targetType original
                let image ← transportedStructure (← inferType actual) selected
                withTransparency .all <| isDefEq image actual) then return true
        return false) then candidates := candidates.push entry
  match candidates.toList with
  | [] => return none
  | [entry] =>
      let (object, category) ← instantiate entry
      discard <| recognize state object category
      return some object
  | _ => throwStratum .semanticAmbiguity m!"several registered structures have this exact selected structural image"

/-- Infer a missing map only from a unique actual registered declaration at fixed endpoints. -/
partial def registeredArrowParameter (expected : Expr) : M (Option Expr) := do
  let expected ← instantiateMVars expected
  if expected.hasMVar || (homEnds? expected).isNone then return none
  let state ← registryState
  let instantiate (entry : MorphismEntry) : M Expr := do
    let constant ← mkConstWithFreshMVarLevels entry.declaration
    let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
    unless ← isDefEq type expected do
      throwStratum .invalid m!"the registered map has different selected endpoints"
    synthesizeInstances args infos
    let arrow ← instantiateMVars (mkAppN constant args)
    if arrow.hasMVar || !(← isTypeCorrect arrow) then
      throwStratum .invalid m!"the registered map's actual parameters are not determined"
    return arrow
  let mut candidates := #[]
  for entry in state.morphisms do
    if ← parameterCompatible (do
        discard <| instantiate entry
        pure true) then candidates := candidates.push entry
  match candidates.toList with
  | [] => return none
  | [entry] =>
      let arrow ← instantiate entry
      Semantic.namedMorphism entry arrow (← read).trace
      return some arrow
  | _ => throwStratum .semanticAmbiguity m!"several registered maps have these selected endpoints"

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
                  if CasCatalogue.Exception.stratum? error == some .invalid then pure none
                  else throw error
          | .nat _ =>
              try pure (some (← typedParameter expected value))
              catch error =>
                if CasCatalogue.Exception.stratum? error == some .invalid then pure none else throw error
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
          if CasCatalogue.Exception.stratum? error == some .invalid then pure none else throw error
      if let some candidate := candidate? then witnesses := #[candidate]
    if witnesses.size > 1 then
      throwStratum .semanticAmbiguity m!"distinct complete source parameter witnesses remain"
    if let some candidate := witnesses[0]? then
      unless ← isDefEq unknownArgument candidate <&&> isDefEq parameter actualTerm do return false
  isDefEq parameter actualTerm

/-- Actual constructor arguments available as typed source witnesses, in declaration order. -/
partial def sourceParameterValues (value : Value) : Array Value :=
  match value with
  | .object _ _ origin selected viewData =>
      #[value] ++ (selected.map sourceParameterValues).getD #[] ++
        (viewData.map fun (original, source, _, _, _) =>
          original.flatMap sourceParameterValues ++ sourceParameterValues source).getD #[] ++
        (origin.map fun (_, parameters) => parameters.flatMap sourceParameterValues).getD #[]
  | _ => #[value]

/-- The family of morphisms `declaration` of `category` applied to elements. Its parameters are
unified from the sets of the operands and from `target?`, the set it is to land in (`deg` on
`ℤ[x]` is `deg ℤ`); a numeral operand is an element of the set the family then takes there. -/
partial def applyFamily (declaration : Name) (category : NamedCategoryEntry)
    (elements : Array Value) (target? : Option Value := none) (numerals : Array Nat := #[])
    (maps : Array Expr := #[]) (parameters : Array Value := #[])
    (application : Option Expr := none) (callableAddress : Option String := none) : M Value := do
  let state ← registryState
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let some (source, target) := homEnds? type
    | throwStratum .invalid m!"{declaration} is not a family of morphisms"
  if let some supplied := application then
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
      if CasCatalogue.Exception.stratum? error == some .invalid then pure none else throw error
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
            if (CasCatalogue.Exception.stratum? error) == some .invalid then pure none
            else throw error
        if let some witness := witness? then
          unless ← witnesses.anyM (fun existing => parameterTrial (isDefEq existing witness)) do
            witnesses := witnesses.push witness
      if witnesses.size > 1 then
        throwStratum .semanticAmbiguity m!"several full typed constructor parameters determine the source"
      if let some witness := witnesses[0]? then
        unless ← isDefEq parameter witness <&&> isDefEq operandSource (← semanticObject A) do
          throwStratum .invalid m!"the chosen constructor parameter does not give the actual source"
        break
      if ← parameterCompatible (do
          let some selected ← registeredStructuredParameter expected A | return false
          unless ← isDefEq parameter selected <&&>
              isDefEq operandSource (← semanticObject A) do return false
          isTypeCorrect (← instantiateMVars (mkAppN constant args))) then
        let some selected ← registeredStructuredParameter expected A | unreachable!
        unless ← isDefEq parameter selected <&&>
            isDefEq operandSource (← semanticObject A) do
          throwStratum .invalid m!"the actual selected structural parameter differs from its operand source"
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
  let endpointWitnesses := parameters ++
    (elements.filterMap fun | .element _ X => some X | _ => none) ++ target?.toArray
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
    if set.hasMVar then
      throwStratum .invalid m!"{declaration} does not apply to an element of {a}"
    let S ← recognize state set category endpointWitnesses
    if (← coercionMap A S).isNone then
      throwStratum .invalid m!"{declaration} does not apply to an element of {a}"
    coerceTo v S
  synthesizeInstances args infos
  let elements ← (sources.zip elements).mapM fun (set, v) => do
    if let .element .. := v then return v
    let set ← instantiateMVars set
    if set.hasMVar then
      throwStratum .invalid m!"the set of an operand of {declaration} is not determined"
    toElement v (← recognize state set category endpointWitnesses)
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
  if let some entry := state.morphisms.find? (·.declaration == declaration) then
    Semantic.namedMorphism entry operation (← read).trace
  if let some address := callableAddress then
    let some (registeredDeclaration, registeredCategory) := state.callable? address
      | throwStratum .invalid m!"the selected application has no registered callable address"
    unless registeredDeclaration == declaration && registeredCategory == category.id do
      throwStratum .invalid m!"the selected callable is outside its declared category or signature"
    let fullParameters ← ((args.zip infos).filterMap fun (parameter, info) =>
      if info.isExplicit then some parameter else none).mapM instantiateMVars
    unless fullParameters.all (fun parameter => !parameter.hasMVar && !parameter.hasLevelMVar) do
      throwStratum .invalid m!"the selected callable's full parameters are not determined"
    Trace.record (← read).trace operation (.namedCallable address category.id fullParameters)
  if elements.isEmpty then
    let source ← instantiateMVars source
    let target ← instantiateMVars target
    let targetValue ← match target? with
      | some targetValue => pure targetValue
      | none => recognize state target category endpointWitnesses
    if category.id == CategoryId.sets then
      if ← parameterTrial (isDefEq source (← semanticObject (← oneObject))) then
        let result ← staged operation
        if let some entry := state.operations.find? (·.declaration == declaration) then
          let actualParameters := (operation.getAppArgs.zip infos).filterMap fun (argument, info) =>
            if info.isExplicit then some argument else none
          let chosen := match targetValue with
            | .object _ _ _ (some selected) _ => selected
            | _ => targetValue
          Trace.record (← read).trace result
            (.operationApply entry.id actualParameters #[] target (← semanticObject chosen))
        else Trace.alias (← read).trace operation result
        return .element result targetValue
      if let some entry := state.operations.find? (·.declaration == declaration) then
        if let some comparison ← operationPointComparison source then
          let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, operation]
          unless !composite.hasMVar && !composite.hasLevelMVar &&
              (← isTypeCorrect composite) do
            throwStratum .invalid m!"the admitted terminal comparison does not form this operation point"
          let result ← staged composite
          let actualParameters := (operation.getAppArgs.zip infos).filterMap fun (argument, info) =>
            if info.isExplicit then some argument else none
          let chosen := match targetValue with
            | .object _ _ _ (some selected) _ => selected
            | _ => targetValue
          Trace.record (← read).trace result
            (.operationPoint entry.id actualParameters comparison operation target (← semanticObject chosen))
          return .element result targetValue
    let sourceValue ← recognize state source category endpointWitnesses
    return .morphism operation source target category (some (sourceValue, targetValue))
  let family ← quoteExpr operation
  let target ← match target? with
    | some T => pure T
    | none => recognize state (← instantiateMVars target) category endpointWitnesses
  let result ← applyTo family elements target
  if let some entry := state.operations.find? (·.declaration == declaration) then
    let .element resultMap _ := result | unreachable!
    let operands ← elements.mapM fun
      | .element hom _ => pure hom
      | _ => throwStratum .invalid m!"an operation operand has no element map"
    let actualParameters := (operation.getAppArgs.zip infos).filterMap fun (argument, info) =>
      if info.isExplicit then some argument else none
    let chosen := match target with
      | .object _ _ _ (some selected) _ => selected
      | _ => target
    Trace.record (← read).trace resultMap
      (.operationApply entry.id actualParameters operands
        (← semanticObject target) (← semanticObject chosen))
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
    let routes := state.routes category.expression sets.expression
    let [cls] := (state.classify routes (fun _ => sets.id.raw) id).toList
      | throwStratum .semanticAmbiguity m!"the presentation has no unique carrier route"
    unless cls.ambiguities.isEmpty do
      throwStratum .semanticAmbiguity m!"several comparisons determine the presentation carrier map"
    let [route] := cls.sources.toList
      | throwStratum .semanticAmbiguity m!"the presentation has no unique directed carrier route"
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
  | some S => return .element (← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[← terminalAt S, hom]) P

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
      throwStratum .semanticAmbiguity m!"{v} is the variable of several rings: {written.toList}"
    let some (_, ring, index) := candidates[0]? | unreachable!
    bindings := (v, ← generatorOf (← eval scope ring) index) :: bindings
  return bindings

/-- How the elements of the set `Y` are elements of the set `X`: `some none` if they are the same
set, `some (some ι)` along `ι : Y ⟶ X`, the registered constants of `X` from its parameter `Y`
(`ℚ ↪ ℚ[x]`) or a chain of registered inclusions (`ℚ ⊆ ℝ`); `none` otherwise. -/
partial def coercionMap (Y X : Value) : M (Option (Option Expr)) := do
  let state ← registryState
  let (.object y _ yOrigin ySelected _, .object x category xOrigin xSelected _) := (Y, X)
    | return none
  let sameSelection ← match ySelected, xSelected with
    | some (.object leftObject leftCategory ..), some (.object rightObject rightCategory ..) =>
        if leftCategory.id != rightCategory.id then pure false else
          parameterTrial <| withTransparency .all <| isDefEq leftObject rightObject
    | some _, some _ => pure false
    | _, _ => pure true
  let sameOrigin := match yOrigin, xOrigin with
    | some (left, _), some (right, _) => left.id == right.id
    | none, none => true
    | _, _ => false
  if sameSelection && sameOrigin && (y == x || (← isDefEq y x)) then return some none
  if let some (entry, params) := xOrigin then
    if let (some constants, some parameter@(.object ..)) :=
        (entry.constants, params.find? (· matches .object ..)) then
      let P ← carrierObject parameter
      let .object p .. := P | unreachable!
      -- Into its parameter `P` (itself, or along a coercion), then its constants `P ↪ X`.
      if let some into ← coercionMap Y P then
        let ι ← homIn (← `($(mkCIdent constants) $(← typedParamTerms constants params)*)) p x category
        return some (some (← match into with
          | some ι₀ => mkAppM ``CategoryTheory.CategoryStruct.comp #[ι₀, ι]
          | none => pure ι))
  if let (some (sub, _), some (super, _)) := (yOrigin, xOrigin) then
    if let some chain := inclusionChain state sub.id super.id then
      unless chain.isEmpty do
        return some (some (← inclusionMap chain Y (some X)))
  -- A domain's inclusion `Y ↪ B` (`Mˣ ↪ M`), then `B` into `X`.
  if let some (ι, b) ← inclusionOut? Y then
    let B ← inclusionTargetValue Y b category
    let .object bHandle .. := B | unreachable!
    let ι ← homIn (← quoteExpr ι) y bHandle category
    if let some into ← coercionMap B X then
      return some (some (← match into with
        | some ι' => mkAppM ``CategoryTheory.CategoryStruct.comp #[ι, ι']
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
            | .object _ _ _ none _, .object _ _ _ (some _) _ => Y
            | _, _ => X
          return .element h target
      | none => throwStratum .invalid m!"the element has no admitted inclusion into the requested set"
  | _ => toElement v X

/-- A set among `sets` that each of them is included in. -/
partial def commonSet? (sets : Array Value) : M (Option Value) := do
  for X in sets do
    if ← sets.allM fun Y => return (← coercionMap Y X).isSome then return some X
  return none

/-- The tuple of the elements `values` of `X`, in `Xⁿ`: `cons(x₁, … cons(xₙ, ()))`. -/
partial def tupleOf (values : Array Value) (X : Value) : M Value := do
  let state ← registryState
  let some empty := state.morphisms.find? (·.name == "()") | throwStratum .invalid m!"no tuples"
  let E ← object state "Vec" #[X, .nat 0] none
  let .object e category _ _ _ := E | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let mut hom ← homIn (← `($(mkCIdent empty.declaration) $(← paramTerms #[X])*)) one e category
  if let some S := (← read).stage then
    hom ← mkAppM ``CategoryTheory.CategoryStruct.comp #[← terminalAt S, hom]
  let mut acc := Value.element hom E
  for v in values.reverse do
    acc ← applyNamed state "cons" #[← coerceTo v X, acc]
  return acc

/-- `(x₁, …, xₙ)`: in an enclosing `Xⁿ`, else in a set its components are in, else `ℤ`. -/
partial def tuple (scope : Scope) (xs : Array Syntax) (ambient? : Option Value) : M Value := do
  let X? := match ambient? with
    | some (.object _ _ (some (entry, #[X, .nat n])) _ _) =>
        if entry.name == "Vec" && n == xs.size then some X else none
    | _ => none
  let values ← xs.mapM (eval scope · none X?)
  let X ← match X? with
    | some X => pure X
    | none =>
        let sets := values.filterMap fun | .element _ X => some X | _ => none
        match ← commonSet? sets, sets[0]? with
        | some X, _ | none, some X => pure X
        | none, none => object (← registryState) "ℤ" #[] none
  tupleOf values X

/-- `[a, b; c, d]`: the registered matrix with these rows, in an enclosing `Matₙ(K)`, else over the
set its entries are in. -/
partial def matrix (scope : Scope) (rows : Array (Array Syntax)) (ambient? : Option Value) :
    M Value := do
  let n := rows.size
  unless rows.all (·.size == n) do
    throwStratum .invalid m!"a matrix `[…; …]` is square: {n} rows of {n} entries"
  let K? := match ambient? with
    | some (.object _ _ (some (entry, #[.nat m, K])) _ _) =>
        if entry.name == "Mat" && m == n then some K else none
    | _ => none
  let rowValues ← rows.mapM fun row => do
    let rowAmbient ← match K? with
      | some K => some <$> object (← registryState) "Vec" #[K, .nat n] none
      | none => pure none
    tuple scope row rowAmbient
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
  return .object object C (some (refined, params)) none none

/-- The invariant `entry : ∀ A, 1 ⟶ T` of the object `A` (its handle): an element of `T`. -/
partial def invariantOf (entry : MorphismEntry) (A : Value) : M Value := do
  let state ← registryState
  let some category := state.categories.find? (·.id == entry.category) | unreachable!
  -- The application is admitted only at the declared dependent signature (b0-typed-application):
  -- the family's first explicit parameter takes `A` at its declared type, its other parameters are
  -- determined, and it is a family of points `1 ⟶ T`.
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (args.zip infos).filterMap fun (a, i) => if i.isExplicit then some a else none
  let mut receiverSlots : Array Nat := #[]
  for slot in [:explicit.size] do
    if ← parameterCompatible (bindSelectedReceiver explicit slot A) then
      receiverSlots := receiverSlots.push slot
  match receiverSlots.toList with
  | [slot] => discard <| bindSelectedReceiver explicit slot A
  | [] =>
      let some parameter := explicit[0]?
        | throwStratum .invalid m!"{entry.name} is not a family indexed by objects"
      let argument ← typedParameter (← inferType parameter) A
      unless ← isDefEq (← inferType parameter) (← inferType argument) <&&> isDefEq parameter argument do
        throwStratum .invalid m!"{entry.name} does not take this selected object at its declared type"
  | _ => throwStratum .semanticAmbiguity m!"several declared parameters accept this selected receiver"
  synthesizeInstances args infos
  unless ← isTypeCorrect (← instantiateMVars (mkAppN constant args)) do
    throwStratum .invalid m!"an argument of {entry.name} is outside its declared type"
  if (← explicit.mapM instantiateMVars).any (·.hasMVar) then
    throwStratum .invalid m!"the parameters of {entry.name} are not determined by the selected object"
  let .object one _ _ _ _ ← oneObject | unreachable!
  let some (source, _) := homEnds? (← instantiateMVars type)
    | throwStratum .invalid m!"{entry.name} is not an invariant of objects"
  let family ← instantiateMVars (mkAppN constant args)
  Semantic.namedMorphism entry family (← read).trace
  let some (_, target) := homEnds? (← instantiateMVars (← inferType family))
    | throwStratum .invalid m!"{entry.name} is not an invariant of objects"
  let endpoint (term : Expr) : M Value := do
    try recognize state term category #[A]
    catch error =>
      if (CasCatalogue.Exception.stratum? error) == some .invalid then
        pure (.object term category none none none)
      else throw error
  let T ← endpoint target
  if ← isDefEq source one then
    let .object t .. := T | unreachable!
    let hom ← staged (← homIn (← quoteExpr family) one t category)
    Trace.alias (← read).trace family hom
    return .element hom T
  return .morphism family source target category (some (← endpoint source, T))

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
          let resolution ← match state.resolveLimit category.id row.shape colimit with
            | .ok resolution => pure resolution
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
  let resolution ← match state.resolveLimit category.id row.shape colimit with
    | .ok resolution => pure resolution
    | .error message => throwStratum .invalid m!"{message}"
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
    try recognize state value category #[receiver]
    catch error =>
      if (CasCatalogue.Exception.stratum? error) == some .invalid then
        pure (.object value category none none none)
      else throw error
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
  let state ← registryState
  let some entry := state.morphisms.find? (·.name == name)
    | throwStratum .invalid m!"no registered family is named {name}"
  let some category := state.categories.find? (·.id == entry.category) | unreachable!
  let operands ← args.mapM (eval scope ·)
  match ← eval scope t with
  | .morphism h .. =>
      -- A family of maps (`f.m(…)` with `f` its parameter). A family on a domain of maps
      -- (`C^∞(ℝ)` for `taylor_expansion`) takes an element of that domain: the map is formed
      -- there first (`f in C^∞`), never admitted because the family needs it.
      let constant ← mkConstWithFreshMVarLevels entry.declaration
      let (args, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
      let mapParams ← (args.zip infos).filterM fun (a, i) =>
        return i.isExplicit && (← whnfR (← inferType a)).isAppOf ``Quiver.Hom
      if mapParams.isEmpty then
        throwStratum .invalid m!"`{name}` takes an element of its domain, not a map: form `{shown t}` \
          there first (`{shown t} in D`), where its evidence is established"
      applyFamily entry.declaration category operands (maps := #[h])
  | v@(.element ..) | v@(.nat _) => applyFamily entry.declaration category (#[v] ++ operands)
  | receiver@(.object ..) =>
      let .morphism family .. ← invariantOf entry receiver
        | throwStratum .invalid m!"the selected object's family does not take operands"
      applyFamily entry.declaration category operands (application := some family)
  | _ => throwStratum .invalid m!"`{name}` is called on a map, an element or a selected object"

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

/-- Prepare a registered binding operation. Surface arguments occupy its last explicit
object or morphism parameters. The declaration fixes the domain; the body's codomain supplies
any remaining structure parameters. Evidence is checked only after the unique reading is chosen. -/
partial def binderReading (scope : Scope) (row : BinderEntry) (boundName : Name)
    (arguments : Array Syntax) (body : Syntax) (ambient? : Option Value) :
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
  for (parameter, argumentSyntax) in supplied.zip arguments do
    let expected ← instantiateMVars (← inferType parameter)
    let value ← if let some (_, target) := homEnds? (← whnfR expected) then
        let target ← instantiateMVars target
        if target.hasMVar then eval scope argumentSyntax
        else do
          let X ← recognize state target category
          toElement (← eval scope argumentSyntax none (some X)) X
      else eval scope argumentSyntax
    let term ← typedParameter expected value
    unless ← isDefEq parameter term do
      throwStratum .invalid m!"a binder argument is outside its declared parameter"
  synthesizeInstances params infos
  let domain ← mkConstWithFreshMVarLevels row.domain
  let domain ← instantiateMVars (mkAppN domain params)
  -- The domain may ignore a still unknown codomain parameter. Reduce that dependency only;
  -- recognition retains declaration identity of the domain's registered object.
  let domain ← if domain.hasMVar then instantiateMVars (← whnfR domain) else pure domain
  if domain.hasMVar then
    throwStratum .invalid m!"the binder arguments do not determine its domain"
  let D ← recognize state domain category
  let knownTarget ← instantiateMVars target
  let bodyAmbient ← if knownTarget.hasMVar then pure ambient?
    else pure (some (← recognize state knownTarget category))
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
  let M ← recognize state (← instantiateMVars source) category
  let (.object d .., .object y ..) := (D, Y) | unreachable!
  return (operation, M, .morphism bodyMap d y category (some (D, Y)), Y)

/-- One generic reading rule for every registered binder; candidate trials cannot emit traces
or retain metavariable assignments. Absent evidence never chooses another interpretation. -/
partial def binder (scope : Scope) (token : String) (boundName : Name)
    (arguments : Array Syntax) (body : Syntax) (ambient? : Option Value) : M Value := do
  let state ← registryState
  let mut candidates := #[]
  for row in state.binders.filter (·.token == token) do
    if ← parameterCompatible (do
        discard <| binderReading scope row boundName arguments body ambient?
        pure true) then
      candidates := candidates.push row
  let row ← match candidates with
    | #[row] => pure row
    | #[] => throwStratum .invalid m!"no registered binder `{token}` reads these arguments and body"
    | _ => throwStratum .semanticAmbiguity m!"several registered binders `{token}` read these arguments and body"
  let (operation, M, bodyMap, Y) ← binderReading scope row boundName arguments body ambient?
  let admitted ← admit M bodyMap
  let .object _ category _ _ _ := Y | unreachable!
  let result ← applyFamily row.operation category #[admitted] (some Y) (application := some operation)
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

/-- The juxtaposition `a b`: their product in a set both are in (`(1/2)x²`), else the registered
action `•` of `a` on `b` (`(6x + 1) dx`), else the registered application of `a` (`M v`). -/
partial def juxtapose (a b : Value) (ambient? : Option Value) : M Value := do
  let sets := #[a, b].filterMap fun | .element _ X => some X | _ => none
  if let .element .. := a then
    let inAmbient ← match ambient? with
      | some X => do
          if ← sets.allM fun Y => return (← coercionMap Y X).isSome then pure (some X) else pure none
      | none => pure none
    let common ← match inAmbient with
      | some X => pure (some X)
      | none => commonSet? sets
    if let some X := common then
      return ← applyOperation "·" #[← coerceTo a X, ← coerceTo b X] X
  -- The registered action `•` of `a`'s set on `b`'s, or the registered application of `a`'s set
  -- (a matrix on a vector): whichever takes these operands' sets; both is an ambiguity.
  let state ← registryState
  let action? := state.morphisms.find? (·.name == "•")
  let acts ← match action? with
    | some entry => familyTakes entry.declaration #[a, b]
    | none => pure false
  let application? ← applicationOf? a
  let applies ← match application? with
    | some (application, _, _, _) => familyTakes application #[a, b]
    | none => pure false
  match acts, applies, action?, application? with
  | true, false, some entry, _ => applyNamed state entry.name #[a, b]
  | false, true, _, some (application, category, _, address) =>
      applyFamily application category #[a, b] (callableAddress := some address)
  | true, true, _, _ => throwStratum .invalid m!"`a b` is both the action `•` and an application"
  | _, _, _, _ => throwStratum .invalid m!"`a b`: no registered product, action or application \
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
    let constant ← mkAppM ``CategoryTheory.CategoryStruct.comp #[← terminalAt Y, h]
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
    | none, _, _ => object state "ℤ" #[] none
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
  let some po := state.powerObjects[0]? | throwStratum .invalid m!"no registered power object"
  let image ← imageOfMap (← inclusionMap chain Y) Y X
  let P ← powerSetOf X
  let .object p _ _ _ _ := P | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let some omega := state.objects.find? (·.id == po.omega) | unreachable!
  let .object ω .. ← object state omega.name #[] none | unreachable!
  let truth ← homIn (mkCIdent po.truth) one ω category
  let everything ← mkAppM ``CategoryTheory.CategoryStruct.comp #[← terminalAt X, truth]
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
  | `(cas_term| ℤ / $n) => return (← objectNamed state "ZMod" none, ← numerals #[n])
  | `(cas_term| (ℤ / $n) ^ $k) =>
      return (← objectNamed state "ZModPower" none, ← numerals #[n, k])
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

/-- The operands `args` as elements of one set: the enclosing one, else that of an operand which
is an element, else `ℤ`. Each operand is evaluated once, and again only if it defaulted to another
set than its siblings'. -/
partial def operands (scope : Scope) (args : Array Syntax) (ambient? : Option Value) :
    M (Array Value × Value) := do
  -- A term of numerals alone (`-1/2`) has no set of its own: it is read in the enclosing set, else
  -- the set of its siblings (`det(M⁻¹) = -1/2` in `ℚ`); numerals alone throughout are read in
  -- `ℚ` if a fraction or decimal is among them, else in `ℤ` (`numeralSet`). Each operand is read
  -- once; an operand in a set not included in the others' is not in the operation's domain.
  let mut known : Array (Option Value) := args.map fun _ => none
  let mut numeralsIn? : Option Value := ambient?
  if ambient?.isNone then
    if args.all numeric then
      let group := mkNullNode args
      numeralsIn? ← numeralSet group none
    else if args.any numeric then
      let mut sets : Array Value := #[]
      for i in [0:args.size] do
        unless numeric args[i]! do
          let v ← eval scope args[i]! none none
          known := known.set! i (some v)
          if let .element _ X := v then sets := sets.push X
      numeralsIn? ← match ← commonSet? sets with
        | some X => pure (some X)
        | none => pure sets[0]?
  let values ← (args.zip known).mapM fun
    | (_, some v) => pure v
    | (arg, none) => eval scope arg none (if numeric arg then numeralsIn? else ambient?)
  let sets := values.filterMap fun | .element _ X => some X | _ => none
  -- The enclosing set, else one all the operands' sets are included in, else the first.
  let X ← match ambient? with
    | some X => pure X
    | none => match ← commonSet? sets, sets[0]? with
      | some X, _ | none, some X => pure X
      | none, none => object (← registryState) "ℤ" #[] none
  return (← values.mapM (coerceTo · X), X)

/-- The registered operation `name` on the operands `args`. -/
partial def operate (scope : Scope) (name : String) (args : Array Syntax)
    (ambient? : Option Value) : M Value := do
  let (elements, X) ← operands scope args ambient?
  applyOperation name elements X

/-- An actual admitted singleton comparison at a nullary operation's complete source. -/
partial def operationPointComparison (source : Expr) : M (Option Expr) := do
  let state ← registryState
  let one ← semanticObject (← oneObject)
  let mut candidates : Array (PresentationComparisonEntry × Expr) := #[]
  for entry in state.presentations do
    let applicable ← parameterCompatible do
      let iso ← instantiateFresh entry.declaration
      let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
      let some (left, right) := homEnds? (← inferType hom) | return false
      unless ← isDefEq left one <&&> isDefEq right source do return false
      let iso ← instantiateMVars iso
      return !iso.hasMVar && !iso.hasLevelMVar && (← isTypeCorrect iso)
    unless applicable do continue
    let iso ← instantiateFresh entry.declaration
    let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
    let some (left, right) := homEnds? (← inferType hom) | unreachable!
    unless ← isDefEq left one <&&> isDefEq right source do unreachable!
    candidates := candidates.push (entry, ← instantiateMVars iso)
  match candidates.toList with
  | [] => return none
  | [(entry, iso)] =>
      return some (← Semantic.presentationArrow entry iso false (← read).trace)
  | _ => throwStratum .semanticAmbiguity m!"several admitted singleton comparisons determine the operation point"

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
    let some numeral ← numeralIn state k one sourceType #[(sourceCategory.id, sourceHandle)]
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
    let hom ← withReader (fun context => { context with trace := some recorder }) do
      staged (← homIn (← quoteExpr numeral) one sourceType category)
    unless !hom.hasMVar && !hom.hasLevelMVar && (← isTypeCorrect hom) do
      throwStratum .invalid m!"the retained source numeral is not a closed typed point"
    Trace.record (some recorder) hom (.elementNumeral k sourceType sourceHandle)
    candidates := candidates.push (source, route, applications, hom, sourceCarrier)
  let some (source, route, applications, point, sourceCarrier) := candidates[0]? | return none
  let .object sourceHandle sourceCategory .. := source | unreachable!
  for (other, _, _, otherPoint, _) in candidates do
    let .object otherHandle otherCategory .. := other | unreachable!
    unless sourceCategory.id == otherCategory.id &&
        (← isDefEq (← inferType sourceHandle) (← inferType otherHandle)) &&
        (← withTransparency .all <| isDefEq sourceHandle otherHandle) &&
        (← withTransparency .all <| isDefEq point otherPoint) do
      throwStratum .semanticAmbiguity m!"distinct retained numeral structures determine this point"
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

/-- `v` as an element of the set `X`: an element already, or the element a numeral names: its
registered numeral in `X` (`numeralIn`); in a set of constants from its parameter `P` without
numerals of its own, the image of the numeral of `P`; in a domain `D ↪ B` with an admission
(`Mˣ ↪ M`), the numeral of `B` admitted, its evidence established. -/
partial def toElement (v : Value) (X : Value) : M Value := do
  match v with
  | .element .. => return v
  | .nat k =>
      let state ← registryState
      let X ← carrierObject X
      if let some point ← forwardNumeral k X then return point
      -- A nullary registered operation can name a point of an anonymous selected structure.
      -- Its actual terminal source must already be the admitted global-point source.
      if k == 0 then
        if ← parameterCompatible (do
            let result ← applyOperation "0" #[] X
            return result matches .element ..) then
          return ← applyOperation "0" #[] X
      let .object x category (some (entry, params)) _ _ := X
        | throwStratum .invalid m!"a numeral is an element of a named set"
      if entry.admission.isSome then
        let some (_, b) ← inclusionOut? X
          | throwStratum .invalid m!"{entry.name} has an admission and no inclusion"
        let B ← inclusionTargetValue X b category
        return ← admit X (← toElement v B)
      let one ← semanticObject (← oneObject)
      let mut refinements : Array (CategoryId × Expr) := #[]
      -- A named numeral refinement already in a registrar's own category supplies its
      -- actual selected structure before any additional outgoing numeral routes.
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
      match ← numeralIn state k one (← semanticObject X) refinements with
      | some numeral =>
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
          let hom ← staged (← homIn (← quoteExpr numeral) oneHandle x category)
          let chosen := match X with
            | .object _ _ _ (some selected) _ => selected
            | _ => X
          Trace.record (← read).trace hom
            (.elementNumeral k (← semanticObject X) (← semanticObject chosen))
          return .element hom X
      | none =>
          -- `0` of a set with a registered zero element (`0 ∈ Kⁿ`, the unit of its addition): that
          -- element, by name.
          if k == 0 then
            if let some zero := state.morphisms.find? fun m =>
                m.name == "0" && m.category == category.id then
              if (← familyLandsIn zero.declaration X) then
                let hom ← zeroElement zero.declaration X
                return .element (← staged hom) X
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

/-- The target value of an actual declared inclusion, retaining structured parameter carriers. -/
partial def inclusionTargetValue (D : Value) (endpoint : Expr)
    (category : NamedCategoryEntry) : M Value := do
  let .object _ _ (some (_, parameters)) .. := D
    | return ← recognize (← registryState) endpoint category
  let mut candidates : Array Value := #[]
  for parameter in parameters do
    unless parameter matches .object .. do continue
    let carrier ← carrierObject parameter
    let .object handle carrierCategory .. := carrier | unreachable!
    if carrierCategory.id == category.id && (← parameterTrial (isDefEq handle endpoint)) then
      candidates := candidates.push carrier
  match candidates.toList with
  | [candidate] =>
      unless ← isDefEq (← semanticObject candidate) endpoint do
        throwStratum .invalid m!"the retained parameter carrier is not the declared inclusion endpoint"
      return candidate
  | [] => recognize (← registryState) endpoint category
  | _ => throwStratum .semanticAmbiguity m!"several retained structures give this inclusion endpoint"

/-- The element (or map) `v` admitted into the domain `D` by its registered admission
`∀ params (x : B) (h : P x), 1 ⟶ D params`, the evidence `P x` established when the statement is
read (LC-14): `2 ∈ ℚˣ`, `M ∈ GLₙ(K)`, `p` monic of degree `n`, `f` continuous. The element is the
first explicit binder the admission's target does not depend on, and its hypotheses are the
explicit binders after it, each a proposition or data with at most one value (the registry's
rule): the evidence builds a proof, or the data (`Invertible x`, the inverse of a unit), and the
admission takes the term it built. An element at a stage (a variable) has no such evidence:
`t ↦ 1/t` on `ℝ` is not a map, whatever `t` is. -/
partial def admit (D : Value) (v : Value) : M Value := do
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
        `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr h) 0)
    | .morphism f .. =>
        -- The function the map is, so that its evidence is about that function.
        quoteExpr (← functionOf f)
    | _ => throwStratum .invalid m!"only an element or a map is admitted into {entry.name}"
  let one ← semanticObject (← oneObject)
  let c ← mkConstWithFreshMVarLevels admission
  let (args, infos, type) ← forallMetaTelescopeReducing (← inferType c)
  unless ← isDefEq type (← mkAppM ``Quiver.Hom #[one, ← semanticObject D]) do
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
  for i in hypotheses do
    let obligation ← instantiateMVars (← inferType args[i]!)
    unless ← isDefEq args[i]! (← establish evidence obligation m!"not an element of {entry.name}") do
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
  let .object oneHandle .. ← oneObject | unreachable!
  let hom ← homIn (← quoteExpr admitted) oneHandle d category
  Trace.alias (← read).trace admitted hom
  return .element hom D

/-- Instantiate an operation from a fully selected receiver at its actual explicit binder.
All expanded structure fields close before ordinary instance and obligation elaboration. -/
partial def selectedOperationApplication (declaration : Name) (owner : CategoryId)
    (receiver : Value) (numerals : Array Nat) : M (Option Expr) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (args.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  let mut applications : Array Expr := #[]
  for slot in [:explicit.size] do
    let candidate ← try parameterTrial do
      unless ← bindSelectedReceiver explicit slot receiver (some owner) do return none
      let numberParameters ← explicit.filterM fun parameter => do
        let parameter ← instantiateMVars parameter
        return parameter.isMVar && (← inferType parameter).isConstOf ``Nat
      unless numberParameters.size == numerals.size do return none
      for (parameter, number) in numberParameters.zip numerals do
        unless ← isDefEq parameter (mkNatLit number) do return none
      synthesizeInstances args infos
      for parameter in args do
        let parameter ← instantiateMVars parameter
        unless parameter.isMVar do continue
        let expected ← instantiateMVars (← inferType parameter)
        unless ← isProp expected do continue
        let some proof ← decideObligation expected | return none
        unless ← isDefEq parameter proof do return none
      let application ← instantiateMVars (mkAppN constant args)
      if application.hasMVar || !(← isTypeCorrect application) then return none
      return some application
    catch error =>
      if (CasCatalogue.Exception.stratum? error) == some .invalid then pure none else throw error
    if let some application := candidate then applications := applications.push application
  let some representative := applications[0]? | return none
  for application in applications do
    unless ← withTransparency .all <| isDefEq application representative do
      throwStratum .semanticAmbiguity m!"several full applications accept this selected operation receiver"
  return some representative

/-- The registered operation `name` on elements of the set `X`: the operation of the category of
`X`'s unique refinement that has one of that name, at that refinement. Its morphism
`X^arity → X` is composed with the product mediator of the operands. -/
partial def applyOperation (name : String) (elements : Array Value) (X : Value)
    (extra : Array Value := #[]) : M Value := do
  let state ← registryState
  let chosen := match X with
    | .object _ _ _ (some selected) _ => selected
    | _ => X
  let numerals ← extra.mapM fun
    | .nat n => pure n
    | _ => throwStratum .invalid m!"an operation's extra parameter is a numeral"
  let mut applicable : Array (OperationEntry × Expr) := #[]
  for operation in state.operations.filter (fun operation =>
      operation.name == name && operation.arity == elements.size &&
        operation.numerals == extra.size) do
    if let some application ← selectedOperationApplication operation.declaration operation.category chosen numerals then
      applicable := applicable.push (operation, application)
  let (operation, application) ← match applicable.toList with
    | [candidate] => pure candidate
    | [] => throwStratum .invalid m!"the selected structure has no registered operation `{name}`"
    | _ => throwStratum .semanticAmbiguity m!"several registered operations `{name}` apply to the selected structure"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwStratum .invalid m!"an element operation has no registered category of sets"
  let target ← match operation.result with
    | none => pure X
    | some id => match state.objects.find? (·.id == id) with
      | some row => object state row.name #[] none
      | none => throwStratum .invalid m!"an operation's result object is not registered"
  return ← applyFamily operation.declaration sets elements (some target)
    (application := some application)

/-- `f ∘ ⟨x₁, x₂⟩` (or `f ∘ x₁`): the semantic morphism `semantic : A₁ × A₂ → B` (or `A₁ → B`),
realized from the registered product of the operands' sets (or their set) to the set `target`,
composed with the operands' mediator. The result is an element of `target`, typed `1 ⟶ target`. -/
partial def applyTo (semantic : Term) (elements : Array Value) (target : Value) :
    M Value := do
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
        let diagram ← `(CategoryTheory.Limits.pair $(← quoteExpr a₁) $(← quoteExpr a₂))
        let cone ← limitIn false "product" diagram category
        let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt
          #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[cone]]
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
      mkEq e truth
  | _ => throwStratum .invalid m!"a decision is a property or a truth value"

/-- The terminal set `1`, the domain of global elements: `Fin(1)`. -/
partial def oneObject : M Value := do object (← registryState) "Fin" #[.nat 1] none

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
  let some po := state.powerObjects[0]? | throwStratum .invalid m!"no registered power object"
  let some entry := state.objects.find? (·.id == po.object) | unreachable!
  object state entry.name #[X] none

/-- The terminal map `S → 1`, by the registered power object's structure. -/
partial def terminalAt (S : Value) : M Expr := do
  let state ← registryState
  let some po := state.powerObjects[0]? | throwStratum .invalid m!"no registered power object"
  let .object s category _ _ _ := S | throwStratum .invalid m!"a stage is a set"
  let .object one _ _ _ _ ← oneObject | unreachable!
  homIn (← `($(mkCIdent po.terminal) $(← paramTerms #[S])*)) s one category

/-- A value where a set is needed: a set, or the extent of a subset (the set of its members). -/
partial def asObject (v : Value) : M Value := do
  match v with
  | .object .. => return v
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
  let .object handle category _ _ _ := X | throwStratum .invalid m!"`|·|` of a set"
  let (value, target) ← Semantic.method "cardinality" handle category (← read).trace
  return .object value target none none none

/-- `x ∈ A` for a subset `A ∈ 𝒫(X)`: membership `X × 𝒫X → Ω` at `⟨x, A⟩`. -/
partial def member (po : PowerObjectEntry) (X : Value) (x A : Value) : M Value := do
  let state ← registryState
  let some omega := state.objects.find? (·.id == po.omega) | unreachable!
  let Ω ← object state omega.name #[] none
  applyTo (← `($(mkCIdent po.member) $(← paramTerms #[X])*)) #[← toElement x X, A] Ω

/-- The negation of a decision (`∉`): the negated proposition. -/
partial def negate (a : Expr) : M Value := return .answer (mkNot a)

/-- `x^k`: the registered power operation with its numeral exponent. -/
partial def power (scope : Scope) (base : Value) (k : Nat) (ambient? : Option Value) : M Value := do
  let _ := scope
  -- `Xⁿ` of a set: its `n`-tuples.
  if let .object .. := base then return ← object (← registryState) "Vec" #[base, .nat k] none
  let X ← match base, ambient? with
    | .element _ Y, some X =>
        if (← coercionMap Y X).isSome then pure X else pure Y
    | .element _ X, _ => pure X
    | _, some X => pure X
    | _, none => object (← registryState) "ℤ" #[] none
  applyOperation "^" #[← toElement base X] X #[.nat k]

/-- The identity `X → X`: the generic element of `X` at the stage `X`. -/
partial def identityAt (X : Value) : M Expr := do
  let .object x category _ _ _ := X | throwStratum .invalid m!"a stage is a set"
  homIn (← `(CategoryTheory.CategoryStruct.id _)) x x category

/-- `e` read at the stage `X` with `t` its generic element: a generalized element `X → Y`. -/
partial def atStage (scope : Scope) (t : Name) (X : Value) (e : Syntax)
    (ambient? : Option Value) : M Value := do
  let generic := Value.element (← identityAt X) X
  withReader (fun ctx => { ctx with stage := some X, bound := (t, generic) :: ctx.bound }) do
    let v ← eval scope e none ambient?
    match v, ambient? with
    | .nat _, some Y => toElement v Y
    | _, _ => pure v

/-- The map `t ↦ e : X → Y`. -/
partial def lambda (scope : Scope) (t : Name) (e : Syntax) (X Y : Value) : M Value := do
  let .element body Y' ← atStage scope t X e (some Y)
    | throwStratum .invalid m!"the body of `{t} ↦ …` is an element of `{shown e}`'s set"
  let (.object x category _ _ _, .object y _ _ _ _) := (X, Y') | unreachable!
  return .morphism body x y category (some (X, Y'))

/-- `f(x, …)`: a map applied to elements (composition), or to a set (its image). -/
partial def apply (scope : Scope) (f : Value) (args : Array Syntax) : M Value := do
  -- An element of a set with a registered application (a polynomial `p(a)`): that application at
  -- `p` and `a`; a numeral `a` is an element of the set of coefficients, the set's parameter.
  if let .element _ (.object _ _ (some (entry, _)) _ _) := f then
    let some (application, category, params, address) ← applicationOf? f
      | throwStratum .invalid m!"the elements of {entry.name} are not applied"
    let #[arg] := args | throwStratum .invalid m!"an element of {entry.name} takes one argument"
    let v ← match ← eval scope arg with
      | v@(.element ..) => pure v
      | v => match params.find? (· matches .object ..) with
        | some R => toElement v R
        | none => throwStratum .invalid m!"`{shown arg}` is not an element"
    return ← applyFamily application category #[f, v] (callableAddress := some address)
  let .morphism h _ _ category (some (X, Y)) := f
    | throwStratum .invalid m!"only a map `X → Y` is applied"
  let #[arg] := args | throwStratum .invalid m!"a map `X → Y` takes one argument"
  let sourceCarrier ← carrierObject X
  let targetCarrier ← carrierObject Y
  let .object source sets .. := sourceCarrier | unreachable!
  let .object target targetSets .. := targetCarrier | unreachable!
  unless sets.id == targetSets.id do
    throwStratum .invalid m!"the map endpoints have different registered carrier categories"
  let state ← registryState
  letI : Inhabited Route :=
    ⟨{ source := category.expression, target := sets.expression, steps := #[] }⟩
  do
    let routes := state.routes category.expression sets.expression
    let classes := state.classify routes (fun _ => sets.id.raw) (fun route => route)
    let cls ← match classes.toList with
      | [entry] => pure entry
      | _ => throwStratum .semanticAmbiguity m!"the map has no unique registered carrier interpretation"
    unless cls.ambiguities.isEmpty do
      throwStratum .semanticAmbiguity m!"the map carrier interpretation has unresolved comparisons"
    let route ← match cls.sources.toList with
      | [entry] => pure entry
      | _ => throwStratum .semanticAmbiguity m!"the map has several directed carrier interpretations"
    let mapped ← if route.steps.isEmpty then pure h else
      elabTermAndSynthesize (← `(CategoryTheory.Functor.map
        $(← quoteExpr (← Semantic.routeFunctor state route.refs)) $(← quoteExpr h))) none
    unless route.steps.isEmpty do
      Trace.record (← read).trace mapped
        (.morphismTransport category.id sets.id route.refs h)
    let v ← eval scope arg none (some sourceCarrier)
    -- A map applied to its whole carrier domain is its image.
    if let .object .. := v then return ← imageOfMap mapped sourceCarrier targetCarrier
    let .element x _ ← toElement v sourceCarrier
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
  let some po := state.powerObjects[0]? | throwStratum .invalid m!"no registered power object"
  let P ← powerSetOf Y
  let .object p category _ _ _ := P | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let image ← homIn (← `($(mkCIdent po.image) $(← paramTerms #[X, Y])* $(← quoteExpr f)))
    one p category
  return .element (← staged image) P

/-- A bound value at the current stage: a global element `1 → X` (a ring's generator bound for a
whole statement) read inside a map is `S → 1 → X`. -/
partial def restage (v : Value) : M Value := do
  let (.element h X, some (.object s ..)) := (v, (← read).stage) | return v
  let some (domain, _) := homEnds? (← whnfR (← inferType h)) | return v
  let .object one .. ← oneObject | return v
  if (← isDefEq domain s) || !(← isDefEq domain one) then return v
  return .element (← staged h) X

/-- A global element `1 → X` at the current stage `S`: `S → 1 → X`. -/
partial def staged (hom : Expr) : M Expr := do
  match (← read).stage with
  | none => return hom
  | some S => mkAppM ``CategoryTheory.CategoryStruct.comp #[← terminalAt S, hom]

/-- `{e | t ∈ X}`, the image of `t ↦ e`. -/
partial def imageOf (scope : Scope) (e : Syntax) (t : Name) (X : Value) : M Value := do
  let .element f Y ← atStage scope t X e none
    | throwStratum .invalid m!"`{shown e}` is an element"
  imageOfMap f X Y

/-- `{t ∈ X | P}`, the subset of `X` the predicate `t ↦ P` classifies (its transpose). -/
partial def comprehension (scope : Scope) (t : Name) (X : Value) (p : Syntax) : M Value := do
  let state ← registryState
  let some po := state.powerObjects[0]? | throwStratum .invalid m!"no registered power object"
  let .element predicate _ ← atStage scope t X p none
    | throwStratum .invalid m!"`{shown p}` is a predicate"
  let P ← powerSetOf X
  let .object pHandle category _ _ _ := P | unreachable!
  let .object one _ _ _ _ ← oneObject | unreachable!
  let subset ← homIn (← `($(mkCIdent po.transpose) $(← paramTerms #[X])* $(← quoteExpr predicate)))
    one pHandle category
  return .element (← staged subset) P

/-- `{x₁, …, xₙ}` as a literal of the registered subset-literal form `form` of the power object
of `X`, when the form applies to `X` (its instances synthesize: decidable equality of `X`'s
elements); `none` where it does not (`ℝ`). The literal is `{x₁, …, xₙ}` written in Lean's own
notation at the form's type (`Insert`, `Singleton`, `EmptyCollection`), each `xᵢ` the element of
`X` it is, and the value is the form's denotation of it: the element of `𝒫(X)`. It is recorded as
that literal, which the realized reading sends as its elements. -/
partial def subsetLiteral (scope : Scope) (form : SubsetLiteralEntry) (xs : Array Syntax)
    (X P : Value) : M (Option Value) := do
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
  let elements ← xs.mapM fun x => do
    let .element h _ ← coerceTo (← eval scope x none (some X)) X
      | throwStratum .invalid m!"`{shown x}` is not an element of {← semanticObject X}"
    `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← quoteExpr h) 0)
  let literal ← if elements.isEmpty then `((∅ : $(← quoteExpr literalType)))
    else `(({$elements:term,*} : $(← quoteExpr literalType)))
  let literal ← instantiateMVars (← elabTermEnsuringType literal literalType)
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq literalMVar literal do
    throwStratum .invalid m!"`{shown (mkNullNode xs)}` is not a literal of {form.id.raw}"
  let hom ← instantiateMVars (mkAppN denotation mvars)
  Trace.record (← read).trace hom (.literal form.id literal)
  return some (.element (← staged hom) P)

/-- `{x₁, …, xₙ}`, a subset of the enclosing `𝒫(X)` (else of `𝒫(ℤ)`): the literal of the power
object's registered subset-literal form where it applies (`subsetLiteral`), else the union of
singletons. -/
partial def setLiteral (scope : Scope) (xs : Array Syntax) (ambient? : Option Value) : M Value := do
  -- Without an enclosing `𝒫(X)`: the set its elements are in, else `ℤ`.
  let P ← match ambient? with
    | some P => pure P
    | none =>
        let sets := (← xs.mapM (eval scope ·)).filterMap fun | .element _ X => some X | _ => none
        match ← commonSet? sets, sets[0]? with
        | some X, _ | none, some X => powerSetOf X
        | none, none => powerSetOf (← object (← registryState) "ℤ" #[] none)
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
  -- The registered subset-literal form of the power object, where it applies to `X`.
  if let some form := (← registryState).subsetLiterals.find? (·.powerObject == po.id) then
    if let some literal ← subsetLiteral scope form xs X P then return literal
  let singletonOf (x : Syntax) : M Value := do
    let element ← coerceTo (← eval scope x none (some X)) X
    applyTo (← `($(mkCIdent po.singleton) $(← paramTerms #[X])*)) #[element] P
  match xs.toList with
  | [] =>
      let .object one _ _ _ _ ← oneObject | unreachable!
      let empty ← homIn (← `($(mkCIdent po.empty) $(← paramTerms #[X])*)) one p category
      return .element (← staged empty) P
  | x :: rest =>
      let mut acc ← singletonOf x
      for y in rest do acc ← applyOperation po.union #[acc, ← singletonOf y] P
      return acc

/-- The registered product of `a` and `b`, or their coproduct if `colimit`. -/
partial def product (scope : Scope) (colimit : Bool) (a b : Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let symbol := if colimit then "⊔" else "×"
  let .object x category _ _ _ ← asObject (← eval scope a category?)
    | throwStratum .invalid m!"`{symbol}` is of objects"
  let .object y category' _ _ _ ← asObject (← eval scope b (some category))
    | throwStratum .invalid m!"`{symbol}` is of objects"
  unless category.id == category'.id do
    throwStratum .invalid m!"`{symbol}` of objects of {category.name} and {category'.name}"
  let diagram ← `(CategoryTheory.Limits.pair $(← quoteExpr x) $(← quoteExpr y))
  let shape := if colimit then "coproduct" else "product"
  let presentation ← limitIn colimit shape diagram category
  let apex ← apexOf colimit presentation
  Trace.alias (← read).trace presentation apex
  return .object apex category none none none

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

/-- The outcome of the failure `e`: its stratum, or, without one, an internal error. -/
def Outcome.ofException (e : Exception) : TermElabM Outcome := do
  let message ← e.toMessageData.toString
  return match Exception.stratum? e with
    | some .invalid => .invalid message
    | some .semanticAmbiguity => .ambiguous message
    | some .noImplementation | some .ambiguousRealization => .gap message
    | some .unavailable => .unavailable message
    | some .malformed => .malformed message
    | none => .internal message

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

/-- The name and term a `let` binds: `let x := t`; `let x : T := t` binds `t in T`;
`let f(t) := e in X → Y` binds `(t ↦ e) in X → Y`. -/
def letBinding? (stx : Syntax) : TermElabM (Option (Name × Syntax)) := do
  match stx with
  | `(cas_stmt| let $x:ident := $t) => return some (x.getId, t)
  | `(cas_stmt| let $x:ident : $T := $t) => return some (x.getId, ← `(cas_term| $t in $T))
  | `(cas_stmt| let $f:ident($t:ident) := $e) =>
      match e with
      | `(cas_term| $body in $T) => return some (f.getId, ← `(cas_term| ($t:ident ↦ $body) in $T))
      | _ => return some (f.getId, ← `(cas_term| $t:ident ↦ $e))
  | _ => return none

/-- The variables a term binds (`t` in `t ↦ e`, `{t ∈ X | P}`, `{e | t ∈ X}`, `∑_{t ∈ A} e`). -/
partial def binders (stx : Syntax) : Array Name :=
  let own : Array Name := match stx with
    | `(cas_term| $t:ident ↦ $_) => #[t.getId]
    | `(cas_term| {$t:ident ∈ $_ | $_}) => #[t.getId]
    | `(cas_term| {$_ | $t:ident ∈ $_}) => #[t.getId]
    | _ =>
      if stx.getKind == ``casBig then #[stx[2].getId]
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

/-- The maps a free variable `v` is applied to in `stx` (`f(v)`). -/
partial def applicationsOf (v : Name) (stx : Syntax) : Array Syntax :=
  let own : Array Syntax := match stx with
    | `(cas_term| $f:ident($args,*)) =>
        if args.getElems.any (isVariable v ·.raw) then #[(Unhygienic.run `(cas_term| $f:ident)).raw]
        else #[]
    | `(cas_term| ($f)($args,*)) =>
        if args.getElems.any (isVariable v ·.raw) then #[f.raw] else #[]
    | _ => #[]
  own ++ stx.getArgs.flatMap (applicationsOf v)

/-- Read `k` with the statement's free variable, if it has one, bound as the generic element of the
domain of the maps it is applied to (`h(-t) = h(t)` for all `t`): the statement is then about maps
out of that domain. -/
def withFreeVariables {α : Type} (scope : Scope) (stx : Syntax) (k : M α) : M α := do
  let state ← registryState
  -- The variables of its polynomial rings are their generators.
  let rings ← ringBindings scope stx
  withReader (fun ctx => { ctx with bound := rings ++ ctx.bound }) do
  let bound := binders stx
  let keywords := [`true, `false, `unknown, `«ℵ₀»]
  let ctx ← read
  -- A free variable is an atomic name that nothing binds and the catalogue does not name.
  let named (n : Name) : Bool :=
    let s := n.toString
    (s == "id" || s == "reindex" || s == "generator") || state.objects.any (·.name == s) || state.morphisms.any (·.name == s) ||
    state.presentations.any (·.name == s) ||
      (subscripted? s).any (fun (base, _) => state.objects.any (·.name == base)) ||
      state.categories.any (·.name == s) || state.methods.any (·.name == s) ||
      state.properties.any (·.name == s) || state.limits.any (·.shape == s)
  let free := (← contextualIdentifiers scope stx).filter fun n =>
    n.isAtomic && !bound.contains n && !scope.contains n && (ctx.bound.lookup n).isNone &&
      !keywords.contains n && !named n &&
      -- `dv`, the differential of a bound variable `v`.
      !((differentialOf? n).any fun v => (ctx.bound.lookup v).isSome)
  let free := free.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]
  match free.toList with
  | [] => k
  | [v] =>
      let some f := (applicationsOf v stx)[0]?
        | throwStratum .invalid m!"the free variable {v} is applied to no map"
      let .morphism _ _ _ _ (some (X, _)) ← eval scope f
        | throwStratum .invalid m!"the free variable {v} is applied to something that is not a map"
      let generic := Value.element (← identityAt X) X
      withReader (fun ctx => { ctx with stage := some X, bound := (v, generic) :: ctx.bound }) k
  | _ => throwStratum .invalid m!"a statement has at most one free variable: {free.toList}"

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
