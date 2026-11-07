module

public import CasCompiler.ReadExpression
public meta import CasCompiler.ReadExpression

public section

namespace CasCompiler

open Lean Meta Elab Term

syntax (name := sourceExpression) "cas_source% " cas_term : term

/-- Standalone syntax uses the same source reader; retained category selections come from
the SourceSession entry point rather than a carrier-type inference or global replay table. -/
@[term_elab sourceExpression] meta def elabSourceExpression : TermElab := fun stx expected => do
  return (← readExpression (fun _ => pure none) ⟨stx[1]⟩ expected).value

private def sourceCategory (session : SourceSession) (context : OpenContext)
    (id : FVarId) : TermElabM (Option NativeSourceCategory) := do
  let some binding := context.bindings.find? (·.expression.fvarId! == id)
    | return none
  let some category := session.categoryFor binding.id | return none
  return some ⟨category.role, category.expression, ← category.bundle.inContext context⟩

/-- Read public source syntax directly in the retained native context.
Reuse: Lean's term elaborator supplies dependent parameter types and local bindings. -/
opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm := do
  let #[term] ← session.elaborateJudgements stx fun context => do
    let expected ← expected.mapM (·.inContext context)
    return #[← readExpression (sourceCategory session context) stx expected]
    | throwError "source reading returned an invalid number of judgements"
  return term

-- Assertion equality uses native Eq, as in SourceEquality and the public claimEqual
-- contract. Logical conjunction uses native And. Neither operation supplies a proof.
-- Reuse: Lean.Meta.mkEq, Lean.Meta.mkAppM and the single native source reader.
private partial def questionExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (stx : TSyntax `cas_term) : TermElabM Expr := withRef stx do
  match stx with
  | `(cas_term| ($body:cas_term)) => questionExpression categoryOf body
  | `(cas_term| $left:cas_term and $right:cas_term) =>
    mkAppM ``And #[← questionExpression categoryOf left, ← questionExpression categoryOf right]
  | `(cas_term| $left:cas_term = $right:cas_term)
  | `(cas_term| $left:cas_term is $right:cas_term) => do
    let left ← readExpression categoryOf left none
    let right ← readExpression categoryOf right (some (← inferType left.value))
    checkRegisteredDomains (← inferType left.value) (← inferType right.value)
    if let some first := left.category then
      if let some second := right.category then
        unless first.role == second.role && first.expression.syntacticEq second.expression &&
            (← isDefEq first.bundle second.bundle) do
          throwError "source equality has different complete selected categories"
    mkEq left.value right.value
  | _ =>
    let value ← readExpression categoryOf stx (some (mkSort .zero))
    unless ← isProp value.value do throwError "a source question must be a proposition"
    return value.value

/-- Form the proposition asked by public source, in its complete original context.
Source: mathematical-input contract §1 and ContextTelescope; equality and conjunction
retain the actual terms. Formation does not decide the question or add a hypothesis. -/
opaque SourceSession.readQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceTerm :=
  session.elaborate stx fun context => questionExpression (sourceCategory session context) stx

/-- A definition extends the native scope. A question retains that scope without extending it. -/
inductive SourceStatement where
  | definition (session : SourceSession) (value : SourceTerm)
  | question (proposition : SourceTerm)

/-- Read public statements through the checked source session, retaining actual let bindings.
Reuse: SourceSession.read/defineTerm and native expected-type checking. Source annotations
are read in the preceding scope; the new name is inserted only after its value is checked. -/
opaque SourceSession.readStatement (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatement := withRef stx do
  match stx with
  | `(cas_stmt| let $name:ident := $body:cas_term) =>
    let value ← session.read body
    return .definition (← session.defineTerm name.getId value) value
  | `(cas_stmt| let $name:ident : $annotation:cas_term := $body:cas_term) =>
    let type ← session.read annotation
    type.source.withOpen fun _ expression => discard <| getLevel expression
    let value ← session.read body (some type.source)
    return .definition (← session.defineTerm name.getId value) value
  | `(cas_stmt| assert implemented $_:cas_term) =>
    CasCatalogue.throwUnsupportedSource
      "source implementation requests require their prepared computational obligation"
  | `(cas_stmt| assert $body:cas_term) =>
    return .question (← session.readQuestion body)
  | _ =>
    CasCatalogue.throwUnsupportedSource
      "source translation is not implemented for this statement form"

end CasCompiler
