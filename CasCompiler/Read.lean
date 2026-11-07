module

public import CasCompiler.Surface
import Lean.Elab.App
public meta import CasCompiler.Surface
public meta import Lean.Elab.App

public section

namespace CasCompiler

open Lean Meta Elab Term

syntax (name := sourceExpression) "cas_source% " cas_term : term

private meta def sourceArgument (stx : TSyntax `cas_term) : TermElabM Arg := withRef stx do
  return .stx (← `(term| cas_source% $stx:cas_term))

private meta def sourceApplication (function : Expr) (arguments : Array (TSyntax `cas_term))
    (expected : Option Expr) : TermElabM Expr := do
  elabAppArgs function #[] (← arguments.mapM sourceArgument) expected false false

/-- Native application supplies the dependent expected type of each source argument.
Only original source syntax is embedded; retained expressions never return to syntax. -/
@[term_elab sourceExpression] meta def elabSourceExpression : TermElab := fun stx expected => do
  let source : TSyntax `cas_term := ⟨stx[1]⟩
  let registered := fun (name : Ident) (category : Option String)
      (arguments : Array (TSyntax `cas_term)) => do
    if let some declaration := (← getLCtx).findFromUserName? name.getId then
      if category.isSome then
        throwError
          "category qualification of a retained source value requires structural translation"
      return ← sourceApplication (mkFVar declaration.fvarId) arguments expected
    let (entry, categoryEntry) ← selectObject name.getId.toString category
    let (_, value) ← objectExpressions entry categoryEntry (← arguments.mapM sourceArgument)
    return value
  let value ← withRef source do
    match source with
    | `(cas_term| ($inner:cas_term)) =>
      elabTerm (← `(term| cas_source% $inner:cas_term)) expected
    | `(cas_term| $number:num) =>
      unless expected.isSome do
        throwError "a source numeral requires its independently declared parameter type"
      elabTermEnsuringType (← `(term| $number:num)) expected
    | `(cas_term| $name:ident) =>
      if let some declaration := (← getLCtx).findFromUserName? name.getId then
        pure (mkFVar declaration.fvarId)
      else registered name none #[]
    | `(cas_term| $name:ident($arguments:cas_term,*)) =>
      registered name none arguments.getElems
    | `(cas_term| $name:ident($arguments:cas_term,*) in $category:ident) =>
      registered name (some category.getId.toString) arguments.getElems
    | `(cas_term| $name:ident in $category:ident) =>
      registered name (some category.getId.toString) #[]
    | `(cas_term| ($function:cas_term)($arguments:cas_term,*)) => do
      let function ← elabTerm (← `(term| cas_source% $function:cas_term)) none
      sourceApplication function arguments.getElems expected
    | `(cas_term| $function:cas_term($arguments:cas_term,*)) => do
      let function ← elabTerm (← `(term| cas_source% $function:cas_term)) none
      sourceApplication function arguments.getElems expected
    | _ => throwError "source translation is not implemented for this expression form"
  if let some expected := expected then
    unless ← isDefEq (← inferType value) expected do
      throwError "the source expression does not have its independently declared parameter type"
  return value

/-- Read public source syntax directly in the retained native context.
Reuse: Lean's term elaborator supplies dependent parameter types and local bindings. -/
opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  session.elaborate stx fun context => do
    let expected ← expected.mapM (·.inContext context)
    elabTermEnsuringType (← `(term| cas_source% $stx:cas_term)) expected

end CasCompiler
