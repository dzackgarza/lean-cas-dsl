/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.ObjectCall
public import CasCatalogue.LimitCall
public import CasCatalogue.Semantic
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
  `x`, `y` are the registered element literals of `X` and `Y`;
* `id(X)` and `f ∘ g`: identities and composites;
* `x + y`, `x · y`, `-x`, `x - y` (`x + -y`): the registered operations of the category whose
  refinement of the set `X` the elements are in (the ring `ℤ/5` for elements of `ℤ/5`). An element
  of `X` is a morphism `1 → X` from the terminal set `Fin(1)`; a numeral is the element its
  element literal names, in the set of the other operands, of an enclosing `in X`, or else `ℤ`
  (SPEC.md: plain numbers are elements of `ℤ`); an operation is its registered morphism composed
  with the product mediator of its operands;
* `S(f, …)` for a registered limit or colimit shape `S` (`pullback`, `pushout`, `equalizer`,
  `coequalizer`, `kernel`, `cokernel`): the apex of the registered (co)limit of the standard
  diagram on `f, …` in their category;
* `X.m()`: the registered method or property `m`, resolved from the category of `X`;
* `|X|`: `X.cardinality()`;
* `X in C`: `X` in the category named `C`; `t in X` for a set `X`: `t` with its numerals in `X`;
* numerals and identifiers not bound to anything else are literals.

Statements:
* `let x := X`;
* `assert X = L`: the value of `X` is the literal `L` of its category's literal form, compared by
  the result realizer's registered observation, which carries the proof that the handle denotes
  the observed literal;
* `X ⊆ Y` for named sets: decided by the registered inclusions alone (a chain of registered
  monomorphisms `X ↪ … ↪ Y`, or `X = Y`); no realization is consulted;
* `x ∈ Y`: `x`, with its numerals in `Y`, is an element of `Y` or of a set registered in `Y`;
* `P and Q`: both decisions (three-valued);
* `assert f = g` for morphisms: the category's registered equality decides it;
* `assert P`, `assert P = true | false | unknown`: the decision of a property;
* `assert implemented X`: a realization computes `X`.

Each statement is read twice. Its semantic reading (`CasCatalogue.Semantic`) elaborates it from
the catalogue alone, whatever leaves are installed; failing that, it is not a valid statement.
Its realized reading then decides it through realizations: it holds, it is wrong, its computation
is a gap (`NoImplementation` or an ambiguous realization), its backend is unavailable, or its
answer is malformed. `CasCatalogue.TestSuite` runs files of statements.
-/

open Lean Meta Elab Term

namespace CasCatalogue.Language

declare_syntax_cat cas_term
syntax:max num : cas_term
syntax:max ident : cas_term
syntax:max (name := casAtom) ("ℤ" <|> "ℕ" <|> "ℚ" <|> "ℝ" <|> "ℂ") : cas_term
syntax:max "ℵ₀" : cas_term
syntax:max ident noWs "(" cas_term,* ")" : cas_term
syntax:max "(" cas_term ")" : cas_term
syntax:max "|" cas_term "|" : cas_term
syntax:max cas_term:max noWs "." ident noWs "(" ")" : cas_term
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

/-- A pair `x ↦ y` of a graph literal. -/
declare_syntax_cat cas_pair
syntax cas_term:51 " ↦ " cas_term:51 : cas_pair
syntax:40 "{" cas_pair,* "}" " : " cas_term:51 " → " cas_term:51 : cas_term

declare_syntax_cat cas_stmt
syntax "let " ident " := " cas_term : cas_stmt
syntax "assert " &"implemented " cas_term : cas_stmt
syntax "assert " cas_term " = " cas_term : cas_stmt
syntax "assert " cas_term : cas_stmt

/-- A test item: a statement with its id and the provenance of its expected value. -/
declare_syntax_cat cas_item
syntax "test " ident str ": " cas_stmt : cas_item
syntax cas_stmt : cas_item

/-- The value of a term. -/
inductive Value
  /-- A numeral: a parameter, or a literal. -/
  | nat (n : Nat)
  /-- An identifier bound to nothing: a literal of the form it is compared with. -/
  | literal (name : Name)
  /-- A realized object: its handle, the registered category it is an object of, and the object
  row and numeral parameters it was named by, if it was named. -/
  | object (handle : Expr) (category : NamedCategoryEntry)
      (origin : Option (ObjectEntry × Array Nat) := none)
  /-- A realized morphism: a morphism of handles `source ⟶ target` of a registered category. -/
  | morphism (hom : Expr) (source target : Expr) (category : NamedCategoryEntry)
  /-- An element of the named set `object` (an `.object` value): a morphism `1 ⟶ object` from
  the terminal set `Fin(1)`. -/
  | element (hom : Expr) (object : Value)
  /-- The decision of a property: an `Option Bool`. -/
  | answer (answer : Expr)
  deriving Inhabited

/-- The `let` bindings of a file: each name's term, evaluated where it is used, so that a use of a
binding whose computation is a gap is itself a gap. -/
abbrev Scope := Std.HashMap Name Syntax

/-- How a term is read: for its mathematics alone (`semantic`: objects are their declarations,
morphisms, limits, methods and properties are the catalogue's; failure is invalidity), or through
realizations (`realized`: handles of leaves; failure is a gap). Every statement is read both ways,
semantically first (`CasCatalogue.Semantic`). -/
inductive Mode
  | semantic
  | realized
  deriving BEq, Inhabited

/-- The language's evaluation monad: elaboration in a reading. -/
abbrev M := ReaderT Mode TermElabM

/-- The morphism `f : a ⟶ b` of `category`: elaborated there, or realized as the morphism of
handles denoting it. -/
def homIn (f : Term) (a b : Expr) (category : NamedCategoryEntry) : M Expr := do
  match ← read with
  | .semantic => Semantic.hom f a b
  | .realized => elabHomCall f (← exprToSyntax a) (← exprToSyntax b) category.id.raw

/-- The registered limit (colimit, if `colimit`) of `shape` at the diagram `D` of `category`. -/
def limitIn (colimit : Bool) (shape : String) (D : Term) (category : NamedCategoryEntry) :
    M Expr := do
  match ← read with
  | .semantic =>
      let diagram ← instantiateMVars (← elabTermAndSynthesize D none)
      Semantic.limit colimit shape diagram category.id.raw
  | .realized => elabLimitCall colimit shape D category.id.raw

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
  | _ => throwStratum .invalid m!"several registered objects are named {name}: state its \
      category (`in C`)"

/-- A term for an elaborated expression. -/
def quoteExpr (e : Expr) : TermElabM Term := exprToSyntax e

/-- A term as written. -/
def shown (stx : Syntax) : String := (stx.reprint.getD (toString stx)).trimAscii.toString

/-- The numerals among `values`, as terms. -/
def numeralTerms (name : String) (values : Array Value) : TermElabM (Array Term) :=
  values.mapM fun
    | .nat n => pure (Syntax.mkNumLit (toString n) : Term)
    | _ => throwStratum .invalid m!"the parameters of {name} are numerals"

/-- The standard diagram of the shape `shape` on the values `args` (Mathlib's standard forms). -/
def standardDiagram (shape : String) (args : Array Value) : M Term := do
  let quote : Value → TermElabM Term
    | .object handle .. => quoteExpr handle
    | .morphism hom .. => quoteExpr hom
    | _ => throwStratum .invalid m!"the diagram of a {shape} is of objects and morphisms"
  let ts ← args.mapM (liftM ∘ quote)
  match shape, ts with
  | "pullback", #[f, g] => `(CategoryTheory.Limits.cospan $f $g)
  | "pushout", #[f, g] => `(CategoryTheory.Limits.span $f $g)
  | "product", #[x, y] | "coproduct", #[x, y] => `(CategoryTheory.Limits.pair $x $y)
  | "equalizer", #[f, g] | "coequalizer", #[f, g] => `(CategoryTheory.Limits.parallelPair $f $g)
  | "kernel", #[f] | "cokernel", #[f] =>
      -- The zero morphism between the handles, as the preimage of the zero of the category.
      let .morphism _ a b category := args[0]! | unreachable!
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

/-- A three-valued decision as a value. -/
def answerOf (b : Option Bool) : Value := .answer (toExpr b)

/-- A fact the catalogue itself decides (a registered inclusion): `True` read semantically, and
`some true` read through realizations, which it does not consult. -/
def decided : M Value := do
  match ← read with
  | .semantic => return .answer (mkConst ``True)
  | .realized => return answerOf (some true)

unsafe def evalAnswerUnsafe (e : Expr) : TermElabM (Option Bool) :=
  evalExpr (Option Bool) (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) e

@[implemented_by evalAnswerUnsafe]
opaque evalAnswer (e : Expr) : TermElabM (Option Bool)

/-- The morphism `a → b` of the registered graph literal of their category with the graph `pairs`
of numerals, named by the element literals of `a`'s and `b`'s objects. -/
def graphOf (a b : Value) (pairs : Array (Nat × Nat)) : M Value := do
  let state ← registryState
  let .object a category (some (source, sourceParams)) := a
    | throwStratum .invalid m!"the domain of a graph is a named object"
  let .object b category' (some (target, targetParams)) := b
    | throwStratum .invalid m!"the codomain of a graph is a named object"
  unless category.id == category'.id do
    throwStratum .invalid m!"a graph from {category.name} to {category'.name}"
  let some form := state.graphLiterals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered graph literals"
  let element (object : ObjectEntry) (params : Array Nat) (k : Nat) : TermElabM Term := do
    let some literal := state.elementLiterals.find? (·.object == object.id)
      | throwStratum .invalid m!"{object.name} has no registered element literals"
    let params ← numeralTerms object.name (params.map .nat)
    `(Option.get ($(mkCIdent literal.denotation) $params* $(Syntax.mkNumLit (toString k)))
        (by decide))
  let entries ← pairs.mapM fun (x, y) => do
    `(($(← element source sourceParams x), $(← element target targetParams y)))
  let X ← `($(mkCIdent source.declaration) $(← numeralTerms source.name (sourceParams.map .nat))*)
  let Y ← `($(mkCIdent target.declaration) $(← numeralTerms target.name (targetParams.map .nat))*)
  let semantic ← `($(mkCIdent form.denotation) (X := $X) (Y := $Y) [$entries,*] (by decide)
    (by decide))
  let hom ← homIn semantic a b category
  return .morphism hom a b category

mutual

/-- The value of a term, in the category `category?` of an enclosing `in C`. -/
partial def eval (scope : Scope) (stx : Syntax) (category? : Option NamedCategoryEntry := none)
    (ambient? : Option Value := none) : M Value := do
  let state ← registryState
  match stx with
  | `(cas_term| $n:num) => return .nat n.getNat
  | `(cas_term| ($t)) => eval scope t category? ambient?
  | `(cas_term| $t in $c) =>
      if let `(cas_term| $name:ident) := c then
        if state.categories.any (·.name == name.getId.toString) then
          return ← eval scope t (some (← categoryNamed state name.getId.toString)) ambient?
      -- `t in X` for a set `X`: `t` with its numerals in `X`.
      let X ← eval scope c
      let .object .. := X | throwStratum .invalid m!"`in` takes a category or a set"
      toElement (← eval scope t category? (some X)) X
  | `(cas_term| $x ⊆ $y) =>
      -- Semantic: the registered inclusions decide it; nothing is realized.
      let (sub, subParams) ← namedObject scope x
      let (super, superParams) ← namedObject scope y
      unless subParams == superParams do
        throwStratum .invalid m!"`⊆` relates named sets at the same parameters"
      if includes state sub.id super.id then return ← decided
      throwStratum .invalid m!"no registered inclusion of {sub.name} in {super.name}"
  | `(cas_term| $x ∈ $y) =>
      let Y ← eval scope y
      let .object _ _ (some (super, _)) := Y
        | throwStratum .invalid m!"`∈` is membership in a named set"
      match ← toElement (← eval scope x none (some Y)) Y with
      | .element _ (.object _ _ (some (sub, _))) =>
          if includes state sub.id super.id then return ← decided
          throwStratum .invalid m!"no registered inclusion of {sub.name} in {super.name}"
      | _ => throwStratum .invalid m!"`∈` relates an element and a named set"
  | `(cas_term| $p and $q) =>
      if (← read) == .semantic then
        let (.answer a, .answer b) := (← eval scope p, ← eval scope q)
          | throwStratum .invalid m!"`and` joins propositions"
        return .answer (mkAnd a b)
      let answer (t : Syntax) : M (Option Bool) := do
        let .answer e ← eval scope t | throwStratum .invalid m!"`and` joins decisions"
        evalAnswer (← executable e)
      return answerOf <| match ← answer p, ← answer q with
        | some false, _ | _, some false => some false
        | some true, some true => some true
        | _, _ => none
  | `(cas_term| $x + $y) => operate scope "+" #[x, y] ambient?
  | `(cas_term| $x · $y) => operate scope "·" #[x, y] ambient?
  | `(cas_term| -$x) => operate scope "-" #[x] ambient?
  | `(cas_term| $x - $y) =>
      -- `x - y` is `x + -y`.
      let (elements, X) ← operands scope #[x, y] ambient?
      applyOperation "+" #[elements[0]!, ← applyOperation "-" #[elements[1]!] X] X
  | `(cas_term| ℵ₀) => return .literal `«ℵ₀»
  | `(cas_term| $x:ident) =>
      if let some t := scope.get? x.getId then return ← eval scope t category? ambient?
      let name := x.getId.toString
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
      | _, _ => named scope f.getId.toString args.getElems category?
  | `(cas_term| {$pairs,*} : $s → $t) => graph scope pairs.getElems s t category?
  | `(cas_term| $f ∘ $g) =>
      let .morphism f' b c category ← eval scope f category?
        | throwStratum .invalid m!"`∘` composes morphisms"
      let .morphism g' a b' category' ← eval scope g (some category)
        | throwStratum .invalid m!"`∘` composes morphisms"
      unless category.id == category'.id && (← isDefEq b b') do
        throwStratum .invalid m!"`{shown f} ∘ {shown g}`: the target of {shown g} is not the \
          source of {shown f}"
      return .morphism (← mkAppM ``CategoryTheory.CategoryStruct.comp #[g', f']) a c category
  | `(cas_term| |$t|) =>
      -- `|x|` of an element is its absolute value; of an object, its cardinality.
      match ← eval scope t category? ambient? with
      | v@(.element ..) => applyNamed state "abs" #[v]
      | _ => call scope t "cardinality" category?
  | `(cas_term| $t.$m:ident()) => call scope t m.getId.toString category?
  | `(cas_term| $a / $n) =>
      match a with
      | `(cas_term| ℤ) => object state "ZMod" #[← eval scope n] category?
      | _ => throwStratum .invalid m!"`/` is the quotient `ℤ/n` only"
  | `(cas_term| $b ^ $k) =>
      match b with
      | `(cas_term| (ℤ / $n)) =>
          object state "ZModPower" #[← eval scope n, ← eval scope k] category?
      | _ => throwStratum .invalid m!"`^` is the power `(ℤ/n)^k` only"
  | `(cas_term| $a × $b) => product scope false a b category?
  | `(cas_term| $a ⊔ $b) => product scope true a b category?
  | _ =>
      -- The atoms `ℤ`, `ℕ`, `ℚ`, `ℝ`, `ℂ`: objects named by their notation.
      match stx.getKind == ``casAtom, stx.find? (·.isAtom) with
      | true, some atom => object state atom.getAtomVal #[] category?
      | _, _ => throwStratum .invalid m!"not a term of the language: {stx}"

/-- The registered object `name` at the numeral parameters `args`. -/
partial def object (state : RegistryState) (name : String) (args : Array Value)
    (category? : Option NamedCategoryEntry) : M Value := do
  let entry ← objectNamed state name category?
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the object {name} has an unregistered category"
  let params ← args.mapM fun
    | .nat n => pure (Syntax.mkNumLit (toString n) : Term)
    | _ => throwStratum .invalid m!"the parameters of {name} are numerals"
  let handle ← match ← read with
    | .semantic => Semantic.object entry params
    | .realized => elabObjectCall entry.id.raw params category.id.raw none
  let numerals := args.filterMap fun | .nat n => some n | _ => none
  return .object handle category (some (entry, numerals))

/-- The method or property `name` of the object `t`. -/
partial def call (scope : Scope) (t : Syntax) (name : String)
    (category? : Option NamedCategoryEntry) : M Value := do
  let state ← registryState
  let receiver ← eval scope t category?
  if let .element .. := receiver then return ← applyNamed state name #[receiver]
  let .object handle category _ := receiver
    | throwStratum .invalid m!"`{name}` is called on an object or an element"
  let isProperty := state.properties.any (·.name == name) && !state.methods.any (·.name == name)
  if (← read) == .semantic then
    if isProperty then return .answer (← Semantic.property name handle category)
    let (value, target) ← Semantic.method name handle category
    return .object value target
  let receiver ← quoteExpr handle
  if isProperty then
    let decision ← elabPropertyQuery name receiver category.id.raw #[]
    return .answer (← mkAppM ``Decision.answer #[decision])
  let value ← elabMethodCall name receiver category.id.raw #[]
  -- The result category: the target of the method's functor.
  let some resolution := (state.resolveMethod category.expression name).toOption
    | throwStratum .invalid m!"`{name}` does not resolve on {category.name}"
  let some functor := state.functor? resolution.method.functor
    | throwStratum .invalid m!"`{name}` has no registered functor"
  let some target := state.category? functor.target
    | throwStratum .invalid m!"the result category of `{name}` is not a registered category"
  return .object value target

/-- The identifier `name` applied to `args`: `id`, or the unique registered object, morphism family or
(co)limit shape of that name. -/
partial def named (scope : Scope) (name : String) (args : Array Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let state ← registryState
  if name == "id" then
    let #[x] := args | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let .object a category _ ← eval scope x category?
      | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let hom ← homIn (← `(CategoryTheory.CategoryStruct.id _)) a a category
    return .morphism hom a a category
  let inScope (c : CategoryId) := category?.all (c == ·.id)
  let objects := state.objects.filter fun o => o.name == name && inScope o.category
  let morphisms := state.morphisms.filter fun m => m.name == name && inScope m.category
  let shapes := state.limits.filter (·.shape == name)
  match objects.isEmpty, morphisms.isEmpty, shapes[0]? with
  | false, true, none => object state name (← args.mapM (eval scope · none)) category?
  | true, false, none =>
      let #[entry] := morphisms
        | throwStratum .invalid m!"several registered morphisms are named {name}: state their \
            category (`in C`)"
      morphism state entry args scope
  | true, true, some limit =>
      let values ← args.mapM (eval scope · category?)
      let category ← match (values[0]? : Option Value) with
        | some (.object _ c _) | some (.morphism _ _ _ c) => pure c
        | _ => throwStratum .invalid m!"a {name} is of objects or morphisms"
      let presentation ← limitIn limit.colimit name (← standardDiagram name values) category
      return .object (← apexOf limit.colimit presentation) category
  | true, true, none => throwStratum .invalid m!"nothing registered is named {name}"
  | _, _, _ => throwStratum .invalid m!"several kinds of registered rows are named {name}"

/-- The registered morphism family `entry` at `args`: its leading arguments are its numeral
parameters, and the rest are elements it is applied to (`gcd(84, 30)`, `rev(3, 0)`). Unapplied, it
is a morphism between the named objects it relates, or an element if its source is `1`
(`i : 1 → ℂ`). -/
partial def morphism (state : RegistryState) (entry : MorphismEntry) (args : Array Syntax)
    (scope : Scope) : M Value := do
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the morphism {entry.name} has an unregistered category"
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let arity ← forallTelescopeReducing (← inferType declaration) fun xs _ => pure xs.size
  unless arity ≤ args.size do
    throwStratum .invalid m!"{entry.name} takes {arity} parameters"
  let params ← numeralTerms entry.name (← (args.extract 0 arity).mapM (eval scope · none))
  let family ← `($(mkCIdent entry.declaration) $params*)
  let semantic ← instantiateMVars (← elabTermAndSynthesize family none)
  let type ← instantiateMVars (← inferType semantic)
  let some (source, target) := match type.getAppFn.constName?, type.getAppArgs with
      | some ``Quiver.Hom, #[_, _, x, y] => some (x, y)
      | _, _ => none
    | throwStratum .invalid m!"{entry.name} is not a family of morphisms"
  let targetValue ← recognize state target category
  let applied := args.extract arity args.size
  if !applied.isEmpty then
    -- The sets of the operands: the factors of a product source, or the source.
    let sources ← match (← whnfR source).getAppFn.constName?, (← whnfR source).getAppArgs with
      | some ``Prod, #[x, y] => pure #[x, y]
      | _, _ => pure #[source]
    unless sources.size == applied.size do
      throwStratum .invalid m!"{entry.name} is applied to {sources.size} elements"
    let elements ← (sources.zip applied).mapM fun (set, arg) => do
      let X ← recognize state set category
      toElement (← eval scope arg none (some X)) X
    return ← applyTo (← quoteExpr semantic) elements targetValue
  let .object b _ _ := targetValue
    | throwStratum .invalid m!"the target of {entry.name} is not an object"
  let sourceValue ← recognize state source category
  let .object a _ origin := sourceValue
    | throwStratum .invalid m!"the source of {entry.name} is not an object"
  let hom ← homIn (← quoteExpr semantic) a b category
  -- A morphism from the terminal set `Fin(1)` is an element.
  if let some (object, #[1]) := origin then
    if object.name == "Fin" then return .element hom targetValue
  return .morphism hom a b category

/-- The object `x` of `category` as the registered object it is (reducibly) at numeral
parameters. -/
partial def recognize (state : RegistryState) (x : Expr) (category : NamedCategoryEntry) :
    M Value := do
  let mut found : Array (ObjectEntry × Array Nat) := #[]
  for entry in state.objects.filter (·.category == category.id) do
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let numerals? ← (withoutModifyingState do
      unless ← withReducible (isDefEq (mkAppN declaration args) x) do return none
      let values ← args.mapM fun a => do (Meta.evalNat (← instantiateMVars a)).run
      return values.mapM id : MetaM _)
    if let some numerals := numerals? then found := found.push (entry, numerals)
  let #[(entry, numerals)] := found
    | throwStratum .invalid m!"{x} is not a unique registered object of {category.name}"
  object state entry.name (numerals.map .nat) (some category)

/-- The registered morphism named `name` without parameters, applied to elements. -/
partial def applyNamed (state : RegistryState) (name : String) (elements : Array Value) :
    M Value := do
  let some entry := state.morphisms.find? (·.name == name)
    | throwStratum .invalid m!"no registered function of elements is named {name}"
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let semantic ← instantiateMVars declaration
  let type ← inferType semantic
  let some category := state.categories.find? (·.id == entry.category) | unreachable!
  let .some (_, target) := match type.getAppFn.constName?, type.getAppArgs with
      | some ``Quiver.Hom, #[_, _, x, y] => some (x, y)
      | _, _ => none
    | throwStratum .invalid m!"{name} is not a morphism"
  applyTo (← quoteExpr semantic) elements (← recognize state target category)

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
  let .object _ category _ := a | throwStratum .invalid m!"the domain of a graph is an object"
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
  let values ← args.mapM (eval scope · none ambient?)
  let X ← match ambient? with
    | some X => pure X
    | none => match values.findSome? (fun | .element _ X => some X | _ => none) with
      | some X => pure X
      | none => object (← registryState) "ℤ" #[] none
  let handle : Value → Option Expr
    | .object a .. => some a
    | _ => none
  let values ← (args.zip values).mapM fun (arg, v) => do
    match v with
    | .element _ Y =>
        if ambient?.isNone && handle Y != handle X then eval scope arg none (some X) else pure v
    | _ => pure v
  return (← values.mapM (toElement · X), X)

/-- The registered operation `name` on the operands `args`. -/
partial def operate (scope : Scope) (name : String) (args : Array Syntax)
    (ambient? : Option Value) : M Value := do
  let (elements, X) ← operands scope args ambient?
  applyOperation name elements X

/-- `v` as an element of the set `X`: an element already, or the element a numeral names. -/
partial def toElement (v : Value) (X : Value) : M Value := do
  match v with
  | .element .. => return v
  | .nat k =>
      let one ← object (← registryState) "Fin" #[.nat 1] none
      let .morphism hom _ _ _ ← graphOf one X #[(0, k)] | unreachable!
      return .element hom X
  | _ => return v

/-- The registered operation `name` on elements of the set `X`: the operation of the category of
`X`'s unique refinement that has one of that name, at that refinement. Its morphism
`X^arity → X` is composed with the product mediator of the operands. -/
partial def applyOperation (name : String) (elements : Array Value) (X : Value) :
    M Value := do
  let state ← registryState
  let .object _ _ (some (base, params)) := X
    | throwStratum .invalid m!"`{name}` is an operation on the elements of a named set"
  let candidates := state.objects.filterMap fun refined => do
    let refinement ← refined.refines
    guard (refinement.base == base.id)
    let operation ← state.operations.find? fun o =>
      o.category == refined.category && o.name == name && o.arity == elements.size
    return (refined, operation)
  let (refined, operation) ← match candidates with
    | #[c] => pure c
    | #[] => throwStratum .invalid m!"no registered refinement of {base.name} has an operation \
        `{name}` of arity {elements.size}"
    | _ => throwStratum .invalid m!"several refinements of {base.name} have an operation `{name}`"
  let params ← numeralTerms refined.name (params.map .nat)
  let semantic ← `($(mkCIdent operation.declaration) ($(mkCIdent refined.declaration) $params*))
  applyTo semantic elements X

/-- `f ∘ ⟨x₁, x₂⟩` (or `f ∘ x₁`): the semantic morphism `semantic : A₁ × A₂ → B` (or `A₁ → B`),
realized from the registered product of the operands' sets (or their set) to the set `target`,
composed with the operands' mediator. The result is an element of `target`, typed `1 ⟶ target`. -/
partial def applyTo (semantic : Term) (elements : Array Value) (target : Value) :
    M Value := do
  let .object b category _ := target
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
        pure (apex, ← mkExpectedTypeHint lift (← mkAppM ``Quiver.Hom #[one, apex]))
    | #[(x, a₁)] => pure (a₁, x)
    | _ => throwStratum .invalid m!"a function of elements takes one or two operands"
  let f ← homIn semantic source b category
  let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[mediator, f]
  return .element (← mkExpectedTypeHint composite (← mkAppM ``Quiver.Hom #[one, b])) target

/-- The registered product of `a` and `b`, or their coproduct if `colimit`. -/
partial def product (scope : Scope) (colimit : Bool) (a b : Syntax)
    (category? : Option NamedCategoryEntry) : M Value := do
  let symbol := if colimit then "⊔" else "×"
  let .object x category _ ← eval scope a category?
    | throwStratum .invalid m!"`{symbol}` is of objects"
  let .object y category' _ ← eval scope b (some category)
    | throwStratum .invalid m!"`{symbol}` is of objects"
  unless category.id == category'.id do
    throwStratum .invalid m!"`{symbol}` of objects of {category.name} and {category'.name}"
  let diagram ← `(CategoryTheory.Limits.pair $(← quoteExpr x) $(← quoteExpr y))
  let shape := if colimit then "coproduct" else "product"
  let presentation ← limitIn colimit shape diagram category
  return .object (← apexOf colimit presentation) category

end

/-- The outcome of a statement. -/
inductive Outcome
  | holds
  | wrong (message : String)
  | gap (reason : String)
  | unavailable (reason : String)
  | malformed (reason : String)
  deriving Inhabited, Repr

/-- `lit` as a value of the literal type `type`. -/
def literalExpr (type : Name) : Value → TermElabM Expr
  | .nat n => do
      let t ← `(($(Syntax.mkNumLit (toString n)) : $(mkIdent type)))
      instantiateMVars (← elabTermAndSynthesize t none)
  | .literal name => do
      let t ← `(($(mkIdent (type ++ name)) : $(mkIdent type)))
      instantiateMVars (← elabTermAndSynthesize t none)
  | _ => throwStratum .invalid m!"the right side of `=` is a literal"

unsafe def evalBoolUnsafe (e : Expr) : TermElabM Bool := evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe]
opaque evalBool (e : Expr) : TermElabM Bool

/-- Whether the realized value `handle` of `category` observes as `literal`. -/
def observes (state : RegistryState) (handle : Expr) (category : NamedCategoryEntry)
    (literal : Value) : TermElabM Bool := do
  let some form := state.literals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered literal form"
  let handleType ← instantiateMVars (← inferType handle)
  let mut chosen : Option ObservationEntry := none
  for observation in state.observations.filter (·.literal == form.id) do
    let some realizer := state.realizers.find? (·.id == observation.realizer) | continue
    let d ← mkConstWithFreshMVarLevels realizer.denotation
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType d)
    let handles := (← whnfR (← inferType (mkAppN d args))).getAppArgs[0]!
    if ← withoutModifyingState (isDefEq handles handleType) then chosen := some observation
  let some observation := chosen
    | throwStratum .noImplementation m!"no registered observation reads the values of \
        {category.name} as literals"
  let observed ← mkAppM ``Subtype.val #[← mkAppM observation.observe #[handle]]
  let expected ← literalExpr form.type literal
  evalBool (← executable (← mkDecide (← mkEq observed expected)))

/-- The proposition that the value `X` of `category` is the literal `literal`, read semantically:
`X = denote literal` for the category's registered literal form. -/
def literalProp (state : RegistryState) (X : Expr) (category : NamedCategoryEntry)
    (literal : Value) : TermElabM Expr := do
  let some form := state.literals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered literal form"
  let denoted ← mkAppM form.denotation #[← literalExpr form.type literal]
  unless ← withTransparency .all <| isDefEq (← inferType X) (← inferType denoted) do
    throwStratum .invalid m!"a value of {category.name} is compared with a literal of another type"
  mkEq X denoted

/-- Whether a decision decides `true` (realized), after `executable`. -/
def decidesTrue (decision : Expr) : TermElabM Bool := do
  evalBool (← executable (← mkAppM ``BEq.beq #[← mkAppM ``Decision.answer #[decision],
    toExpr (some true)]))

/-- The comparison `l = r`: semantically, the proposition it states is formed (and must be);
through realizations, it is decided. -/
def assertEqual (scope : Scope) (l r : Syntax) : M Outcome := do
  let state ← registryState
  let semantic := (← read) == .semantic
  let right ← eval scope r
  let ambient := match right with
    | .element _ X => some X
    | _ => none
  let left ← eval scope l none ambient
  -- Elements are compared as morphisms `1 → X`; a numeral side is an element of `X`.
  let (left, right) ← match left, right with
    | .element _ X, _ => pure (left, ← toElement right X)
    | _, .element _ X => pure (← toElement left X, right)
    | _, _ => pure (left, right)
  let wrong := Outcome.wrong s!"{shown l} is not {shown r}"
  match left, right with
  | .element f (.object _ category _), .element g _ | .morphism f _ _ category, .morphism g _ _ _ =>
      if semantic then discard <| mkEq f g; return .holds
      let decision ← elabEqualityQuery (← quoteExpr f) (← quoteExpr g) category.id.raw
      return if ← decidesTrue decision then .holds else wrong
  | .element .., _ => throwStratum .invalid m!"an element is compared with an element"
  | .morphism .., _ => throwStratum .invalid m!"a morphism is compared with a morphism"
  | .object X category _, _ =>
      if semantic then discard <| literalProp state X category right; return .holds
      return if ← observes state X category right then .holds else wrong
  | .answer answer, _ =>
      let expected ← match right with
        | .literal `true => pure (some true)
        | .literal `false => pure (some false)
        | .literal `unknown => pure none
        | _ => throwStratum .invalid m!"a decision is `true`, `false` or `unknown`"
      if semantic then return .holds
      let e ← mkAppM ``BEq.beq #[answer, toExpr expected]
      return if ← evalBool (← executable e) then .holds else wrong
  | _, _ => throwStratum .invalid m!"`{l}` is neither a value nor a decision"

/-- A statement read in the current mode. -/
def statement (scope : Scope) (stx : Syntax) : M Outcome := do
  let semantic := (← read) == .semantic
  match stx with
  | `(cas_stmt| let $_:ident := $t) => discard <| eval scope t; return .holds
  | `(cas_stmt| assert implemented $t) => discard <| eval scope t; return .holds
  | `(cas_stmt| assert $l = $r) => assertEqual scope l r
  | `(cas_stmt| assert $p) =>
      let .answer answer ← eval scope p | throwStratum .invalid m!"`assert P` needs a property"
      if semantic then return .holds
      let e ← mkAppM ``BEq.beq #[answer, toExpr (some true)]
      return if ← evalBool (← executable e) then .holds else .wrong s!"{shown p} is not true"
  | _ => throwStratum .invalid m!"not a statement of the language: {stx}"

/-- Run a statement, within the `let` bindings `scope`: first its semantic reading, whose failure
makes it invalid whatever is realized; then its realized reading, where a missing realization is a
gap. A `let` binds its term either way; its realized failure surfaces where it is used. -/
def run (scope : Scope) (stx : Syntax) : TermElabM (Outcome × Scope) := do
  let scope' := match stx with
    | `(cas_stmt| let $x:ident := $t) => scope.insert x.getId t
    | _ => scope
  try discard <| (statement scope stx).run .semantic
  catch e => throwError "not a valid statement: {e.toMessageData}"
  let classify (e : Exception) : TermElabM Outcome := do
    match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization =>
        return .gap (← e.toMessageData.toString)
    | some .unavailable => return .unavailable (← e.toMessageData.toString)
    | some .malformed => return .malformed (← e.toMessageData.toString)
    | _ => throw e
  let outcome ← try (statement scope stx).run .realized catch e => classify e
  if let `(cas_stmt| let $_:ident := $_) := stx then return (.holds, scope')
  return (outcome, scope')

end CasCatalogue.Language
