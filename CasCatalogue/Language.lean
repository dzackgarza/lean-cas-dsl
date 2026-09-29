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
* `N` or `N(a, …)`: the registered object named `N` (in the category of an enclosing `in C`, or
  the unique one of that name), at the numeral parameters `a, …`;
* `ℤ/n` is `ZMod(n)`, and `(ℤ/n)^k` is `ZModPower(n, k)`;
* `X × Y`: the registered product in the category of `X` and `Y`;
* `X.m()`: the registered method or property `m`, resolved from the category of `X`;
* `|X|`: `X.cardinality()`;
* `X in C`: `X` in the category named `C`;
* numerals and identifiers not bound to anything else are literals.

Statements:
* `let x := X`;
* `assert X = L`: the value of `X` is the literal `L` of its category's literal form, compared by
  the result realizer's registered observation, which carries the proof that the handle denotes
  the observed literal;
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
syntax:50 cas_term:51 " in " ident : cas_term

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
  /-- A realized object: its handle and the registered category it is an object of. -/
  | object (handle : Expr) (category : NamedCategoryEntry)
  /-- The decision of a property: an `Option Bool`. -/
  | answer (answer : Expr)
  deriving Inhabited

/-- The `let` bindings of a file. -/
abbrev Scope := Std.HashMap Name Value

/-- The registered category named `name`. -/
def categoryNamed (state : RegistryState) (name : String) : TermElabM NamedCategoryEntry := do
  let some entry := state.categories.find? (·.name == name)
    | throwStratum .invalid m!"no registered category is named {name}"
  return entry

/-- The registered object named `name`, in `category` when given. -/
def objectNamed (state : RegistryState) (name : String) (category? : Option NamedCategoryEntry) :
    TermElabM ObjectEntry := do
  let candidates := state.objects.filter fun o =>
    o.name == name && category?.all (o.category == ·.id)
  match candidates with
  | #[object] => return object
  | #[] => throwStratum .invalid m!"no registered object is named {name}{match category? with
      | some c => m!" in {c.name}" | none => m!""}"
  | _ => throwStratum .invalid m!"several registered objects are named {name}: state its \
      category (`in C`)"

/-- A term for an elaborated expression. -/
def quoteExpr (e : Expr) : TermElabM Term := exprToSyntax e

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
      if let some v := scope.get? x.getId then return v
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
      | _, _ => object state f.getId.toString (← args.getElems.mapM (eval scope · none)) category?
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
  | `(cas_term| $a × $b) => product scope a b category?
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
  return .object handle category

/-- The method or property `name` of the object `t`. -/
partial def call (scope : Scope) (t : Syntax) (name : String)
    (category? : Option NamedCategoryEntry) : TermElabM Value := do
  let state ← registryState
  let .object handle category ← eval scope t category?
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

/-- The registered product of `a` and `b`. -/
partial def product (scope : Scope) (a b : Syntax) (category? : Option NamedCategoryEntry) :
    TermElabM Value := do
  let .object x category ← eval scope a category?
    | throwStratum .invalid m!"`×` is a product of objects"
  let .object y category' ← eval scope b (some category)
    | throwStratum .invalid m!"`×` is a product of objects"
  unless category.id == category'.id do
    throwStratum .invalid m!"`×` of objects of {category.name} and {category'.name}"
  let diagram ← `(CategoryTheory.Limits.pair $(← quoteExpr x) $(← quoteExpr y))
  let cone ← elabLimitCall false "product" diagram category.id.raw
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt
    #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[cone]]
  return .object apex category

end

/-- A term as written. -/
def shown (stx : Syntax) : String := (stx.reprint.getD (toString stx)).trimAscii.toString

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
  | `(cas_stmt| let $x:ident := $t) => return (.holds, scope.insert x.getId (← eval scope t))
  | `(cas_stmt| assert implemented $t) =>
      try discard <| eval scope t; return (.holds, scope)
      catch e => return (← classify e, scope)
  | `(cas_stmt| assert $l = $r) =>
      try
        let right ← eval scope r
        match ← eval scope l with
        | .object handle category =>
            if ← observes state handle category right then return (.holds, scope)
            return (.wrong s!"{shown l} is not {shown r}", scope)
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
