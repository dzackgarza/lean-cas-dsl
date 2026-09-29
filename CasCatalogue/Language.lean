/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.ObjectCall
public import CasCatalogue.LimitCall

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
* `S(f, …)` for a registered limit or colimit shape `S` (`pullback`, `pushout`, `equalizer`,
  `coequalizer`, `kernel`, `cokernel`): the apex of the registered (co)limit of the standard
  diagram on `f, …` in their category;
* `X.m()`: the registered method or property `m`, resolved from the category of `X`;
* `|X|`: `X.cardinality()`;
* `X in C`: `X` in the category named `C`;
* numerals and identifiers not bound to anything else are literals.

Statements:
* `let x := X`;
* `assert X = L`: the value of `X` is the literal `L` of its category's literal form, compared by
  the result realizer's registered observation, which carries the proof that the handle denotes
  the observed literal;
* `assert f = g` for morphisms: the category's registered equality decides it;
* `assert P`, `assert P = true | false | unknown`: the decision of a property;
* `assert implemented X`: a realization computes `X`.

Each statement has an outcome: it holds, it is wrong, its computation is a gap (`NoImplementation`
or an ambiguous realization), its backend is unavailable, its answer is malformed, or it is not a
valid statement. `CasCatalogue.TestSuite` runs files of statements.
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
syntax:50 cas_term:51 " in " ident : cas_term

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
  /-- The decision of a property: an `Option Bool`. -/
  | answer (answer : Expr)
  deriving Inhabited

/-- The `let` bindings of a file: each name's term, evaluated where it is used, so that a use of a
binding whose computation is a gap is itself a gap. -/
abbrev Scope := Std.HashMap Name Syntax

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
def standardDiagram (shape : String) (args : Array Value) : TermElabM Term := do
  let quote : Value → TermElabM Term
    | .object handle .. => quoteExpr handle
    | .morphism hom .. => quoteExpr hom
    | _ => throwStratum .invalid m!"the diagram of a {shape} is of objects and morphisms"
  let ts ← args.mapM quote
  match shape, ts with
  | "pullback", #[f, g] => `(CategoryTheory.Limits.cospan $f $g)
  | "pushout", #[f, g] => `(CategoryTheory.Limits.span $f $g)
  | "product", #[x, y] | "coproduct", #[x, y] => `(CategoryTheory.Limits.pair $x $y)
  | "equalizer", #[f, g] | "coequalizer", #[f, g] => `(CategoryTheory.Limits.parallelPair $f $g)
  | "kernel", #[f] | "cokernel", #[f] => `(CategoryTheory.Limits.parallelPair $f 0)
  | _, _ => throwStratum .invalid m!"a {shape} of {args.size} arguments has no standard diagram"

mutual

/-- The value of a term, in the category `category?` of an enclosing `in C`. -/
partial def eval (scope : Scope) (stx : Syntax) (category? : Option NamedCategoryEntry := none) :
    TermElabM Value := do
  let state ← registryState
  match stx with
  | `(cas_term| $n:num) => return .nat n.getNat
  | `(cas_term| ($t)) => eval scope t category?
  | `(cas_term| $t in $c:ident) =>
      eval scope t (some (← categoryNamed state c.getId.toString))
  | `(cas_term| ℵ₀) => return .literal `«ℵ₀»
  | `(cas_term| $x:ident) =>
      if let some t := scope.get? x.getId then return ← eval scope t category?
      let name := x.getId.toString
      if state.objects.any (·.name == name) then object state name #[] category?
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
  | `(cas_term| |$t|) => call scope t "cardinality" category?
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
    (category? : Option NamedCategoryEntry) : TermElabM Value := do
  let entry ← objectNamed state name category?
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the object {name} has an unregistered category"
  let params ← args.mapM fun
    | .nat n => pure (Syntax.mkNumLit (toString n) : Term)
    | _ => throwStratum .invalid m!"the parameters of {name} are numerals"
  let handle ← elabObjectCall entry.id.raw params category.id.raw none
  let numerals := args.filterMap fun | .nat n => some n | _ => none
  return .object handle category (some (entry, numerals))

/-- The method or property `name` of the object `t`. -/
partial def call (scope : Scope) (t : Syntax) (name : String)
    (category? : Option NamedCategoryEntry) : TermElabM Value := do
  let state ← registryState
  let .object handle category _ ← eval scope t category?
    | throwStratum .invalid m!"`{name}` is called on an object"
  let receiver ← quoteExpr handle
  if state.properties.any (·.name == name) && !state.methods.any (·.name == name) then
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
    (category? : Option NamedCategoryEntry) : TermElabM Value := do
  let state ← registryState
  if name == "id" then
    let #[x] := args | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let .object a category _ ← eval scope x category?
      | throwStratum .invalid m!"`id(X)` is the identity of an object `X`"
    let hom ← elabHomCall (← `(CategoryTheory.CategoryStruct.id _)) (← quoteExpr a)
      (← quoteExpr a) category.id.raw
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
      morphism state entry (← args.mapM (eval scope · none))
  | true, true, some limit =>
      let values ← args.mapM (eval scope · category?)
      let category ← match (values[0]? : Option Value) with
        | some (.object _ c _) | some (.morphism _ _ _ c) => pure c
        | _ => throwStratum .invalid m!"a {name} is of objects or morphisms"
      let presentation ← elabLimitCall limit.colimit name (← standardDiagram name values)
        category.id.raw
      let apex ← if limit.colimit then
          mkAppM ``CategoryTheory.Limits.Cocone.pt
            #[← mkAppM ``CategoryTheory.Limits.ColimitCocone.cocone #[presentation]]
        else
          mkAppM ``CategoryTheory.Limits.Cone.pt
            #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]]
      return .object apex category
  | true, true, none => throwStratum .invalid m!"nothing registered is named {name}"
  | _, _, _ => throwStratum .invalid m!"several kinds of registered rows are named {name}"

/-- The registered morphism family `entry` at the numerals `args`, between the named objects it
relates. -/
partial def morphism (state : RegistryState) (entry : MorphismEntry) (args : Array Value) :
    TermElabM Value := do
  let some category := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid m!"the morphism {entry.name} has an unregistered category"
  let params ← numeralTerms entry.name args
  let family ← `($(mkCIdent entry.declaration) $params*)
  let semantic ← instantiateMVars (← elabTermAndSynthesize family none)
  let type ← instantiateMVars (← inferType semantic)
  let some (source, target) := match type.getAppFn.constName?, type.getAppArgs with
      | some ``Quiver.Hom, #[_, _, x, y] => some (x, y)
      | _, _ => none
    | throwStratum .invalid m!"{entry.name} is not a family of morphisms"
  let .object a _ _ ← recognize state source category
    | throwStratum .invalid m!"the source of {entry.name} is not an object"
  let .object b _ _ ← recognize state target category
    | throwStratum .invalid m!"the target of {entry.name} is not an object"
  let hom ← elabHomCall (← quoteExpr semantic) (← quoteExpr a) (← quoteExpr b) category.id.raw
  return .morphism hom a b category

/-- The object `x` of `category` as the registered object it is (reducibly) at numeral
parameters. -/
partial def recognize (state : RegistryState) (x : Expr) (category : NamedCategoryEntry) :
    TermElabM Value := do
  let mut found : Array (ObjectEntry × Array Nat) := #[]
  for entry in state.objects.filter (·.category == category.id) do
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let numerals? ← withoutModifyingState do
      unless ← withReducible (isDefEq (mkAppN declaration args) x) do return none
      let values ← args.mapM fun a => do (Meta.evalNat (← instantiateMVars a)).run
      return values.mapM id
    if let some numerals := numerals? then found := found.push (entry, numerals)
  let #[(entry, numerals)] := found
    | throwStratum .invalid m!"{x} is not a unique registered object of {category.name}"
  object state entry.name (numerals.map .nat) (some category)

/-- The morphism `{x ↦ y, …} : s → t` with that graph, by the registered graph literal of the
category of `s` and `t`, whose elements are the registered element literals of `s` and `t`. -/
partial def graph (scope : Scope) (pairs : Array Syntax) (s t : Syntax)
    (category? : Option NamedCategoryEntry) : TermElabM Value := do
  let state ← registryState
  let .object a category (some (source, sourceParams)) ← eval scope s category?
    | throwStratum .invalid m!"the domain of a graph is a named object"
  let .object b category' (some (target, targetParams)) ← eval scope t (some category)
    | throwStratum .invalid m!"the codomain of a graph is a named object"
  unless category.id == category'.id do
    throwStratum .invalid m!"a graph from {category.name} to {category'.name}"
  let some form := state.graphLiterals.find? (·.category == category.id)
    | throwStratum .invalid m!"{category.name} has no registered graph literals"
  let element (object : ObjectEntry) (params : Array Nat) (x : Syntax) : TermElabM Term := do
    let .nat k ← eval scope x | throwStratum .invalid m!"an element literal is a numeral"
    let some literal := state.elementLiterals.find? (·.object == object.id)
      | throwStratum .invalid m!"{object.name} has no registered element literals"
    let params ← numeralTerms object.name (params.map .nat)
    `(Option.get ($(mkCIdent literal.denotation) $params* $(Syntax.mkNumLit (toString k)))
        (by decide))
  let entries ← pairs.mapM fun pair => do
    -- A pair `x ↦ y`: its arguments 0 and 2.
    `(($(← element source sourceParams pair[0]), $(← element target targetParams pair[2])))
  let X ← `($(mkCIdent source.declaration) $(← numeralTerms source.name (sourceParams.map .nat))*)
  let Y ← `($(mkCIdent target.declaration) $(← numeralTerms target.name (targetParams.map .nat))*)
  let semantic ← `($(mkCIdent form.denotation) (X := $X) (Y := $Y) [$entries,*] (by decide)
    (by decide))
  let hom ← elabHomCall semantic (← quoteExpr a) (← quoteExpr b) category.id.raw
  return .morphism hom a b category

/-- The registered product of `a` and `b`, or their coproduct if `colimit`. -/
partial def product (scope : Scope) (colimit : Bool) (a b : Syntax)
    (category? : Option NamedCategoryEntry) : TermElabM Value := do
  let symbol := if colimit then "⊔" else "×"
  let .object x category _ ← eval scope a category?
    | throwStratum .invalid m!"`{symbol}` is of objects"
  let .object y category' _ ← eval scope b (some category)
    | throwStratum .invalid m!"`{symbol}` is of objects"
  unless category.id == category'.id do
    throwStratum .invalid m!"`{symbol}` of objects of {category.name} and {category'.name}"
  let diagram ← `(CategoryTheory.Limits.pair $(← quoteExpr x) $(← quoteExpr y))
  let shape := if colimit then "coproduct" else "product"
  let presentation ← elabLimitCall colimit shape diagram category.id.raw
  let apex ← if colimit then
      mkAppM ``CategoryTheory.Limits.Cocone.pt
        #[← mkAppM ``CategoryTheory.Limits.ColimitCocone.cocone #[presentation]]
    else
      mkAppM ``CategoryTheory.Limits.Cone.pt
        #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]]
  return .object apex category

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

/-- Run a statement, within the `let` bindings `scope`. -/
def run (scope : Scope) (stx : Syntax) : TermElabM (Outcome × Scope) := do
  let state ← registryState
  let classify (e : Exception) : TermElabM Outcome := do
    match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization =>
        return .gap (← e.toMessageData.toString)
    | some .unavailable => return .unavailable (← e.toMessageData.toString)
    | some .malformed => return .malformed (← e.toMessageData.toString)
    | _ => throw e
  match stx with
  | `(cas_stmt| let $x:ident := $t) =>
      -- An invalid binding fails here; one whose computation is a gap is bound all the same.
      try discard <| eval scope t catch e => discard <| classify e
      return (.holds, scope.insert x.getId t)
  | `(cas_stmt| assert implemented $t) =>
      try discard <| eval scope t; return (.holds, scope)
      catch e => return (← classify e, scope)
  | `(cas_stmt| assert $l = $r) =>
      try
        let right ← eval scope r
        match ← eval scope l with
        | .object handle category _ =>
            if ← observes state handle category right then return (.holds, scope)
            return (.wrong s!"{shown l} is not {shown r}", scope)
        | .morphism f _ _ category =>
            let .morphism g _ _ _ := right
              | throwStratum .invalid m!"a morphism is compared with a morphism"
            let decision ← elabEqualityQuery (← quoteExpr f) (← quoteExpr g) category.id.raw
            let e ← mkAppM ``BEq.beq #[← mkAppM ``Decision.answer #[decision], toExpr (some true)]
            if ← evalBool (← executable e) then return (.holds, scope)
            return (.wrong s!"{shown l} = {shown r} is not decided true", scope)
        | .answer answer =>
            let expected ← match right with
              | .literal `true => pure (some true)
              | .literal `false => pure (some false)
              | .literal `unknown => pure none
              | _ => throwStratum .invalid m!"a decision is `true`, `false` or `unknown`"
            let e ← mkAppM ``BEq.beq #[answer, toExpr expected]
            if ← evalBool (← executable e) then return (.holds, scope)
            return (.wrong s!"{shown l} is not {shown r}", scope)
        | _ => throwStratum .invalid m!"`{l}` is neither a value nor a decision"
      catch e => return (← classify e, scope)
  | `(cas_stmt| assert $p) =>
      try
        let .answer answer ← eval scope p
          | throwStratum .invalid m!"`assert P` needs a property"
        let e ← mkAppM ``BEq.beq #[answer, toExpr (some true)]
        if ← evalBool (← executable e) then return (.holds, scope)
        return (.wrong s!"{shown p} is not true", scope)
      catch e => return (← classify e, scope)
  | _ => throwStratum .invalid m!"not a statement of the language: {stx}"

end CasCatalogue.Language
