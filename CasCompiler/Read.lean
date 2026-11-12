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
  let carrier ← category.carrier.mapM fun carrier => do
    return (⟨carrier.refs, carrier.target, carrier.identifications,
      ← carrier.actions.mapM (·.inContext context),
      ← carrier.comparisons.mapM (·.inContext context)⟩ : NativeSourceCarrierSelection)
  return some ⟨category.role, category.expression, ← category.bundle.inContext context,
    carrier⟩

private def SourceSession.readAt (session : SourceSession) (reference : Syntax)
    (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm := do
  let #[term] ← session.elaborateJudgements reference fun context => do
    let expected ← expected.mapM (·.inContext context)
    return #[← readSourceTerm (sourceCategory session context) stx expected]
    | throwError "source reading returned an invalid number of judgements"
  return term

/-- Read public source syntax directly in the retained native context.
Reuse: Lean's term elaborator supplies dependent parameter types and local bindings. -/
opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  session.readAt stx stx expected

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
  | `(cas_term| $left:cas_term is $right:cas_term) => sourceEquation categoryOf left right
  | _ =>
    let value ← readExpression categoryOf stx (some (mkSort .zero))
    unless ← isProp value.value do throwError "a source question must be a proposition"
    return value.value

/-- Form the proposition asked by public source, in its complete original context.
Source: mathematical-input contract §1 and ContextTelescope; equality and conjunction
retain the actual terms. Formation does not decide the question or add a hypothesis. -/
opaque SourceSession.readQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceTerm :=
  session.elaborate stx fun context => do
    let categoryOf := sourceCategory session context
    return (← withRingVariables categoryOf stx do
      return ⟨← questionExpression categoryOf stx, none⟩).value

/-- A definition extends the native scope. A question retains that scope without extending it.
An implementation request asks that the installed computations produce the value. A typing
question (`x ∈ Y` or `x in Y` for an object `Y`) is settled by reading `x` in `Y`. -/
inductive SourceStatement where
  | definition (session : SourceSession) (value : SourceTerm)
  | question (proposition : SourceTerm)
  | implemented (value : SourceTerm)
  | settled (value : SourceTerm)

/-- Read an asserted membership or annotation. Membership in a subset is a proposition; in an
object it is the element's reading there, whose success settles the question.
Source: mathematical-input contract §1; the original reader's settled typing judgements. -/
private def typingQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceStatement := do
  let term ← session.elaborate stx fun context =>
    return (← readSourceTerm (sourceCategory session context) stx none).value
  let proposition ← term.source.withOpen fun _ expression => isProp expression
  return if proposition then .question term else .settled term

private partial def patternFunction (pattern body : TSyntax `cas_term) :
    TermElabM (TSyntax `cas_term) :=
  match pattern with
  | `(cas_term| $name:ident) => `(cas_term| $name:ident ↦ $body:cas_term)
  | `(cas_term| ($first:cas_term, $rest:cas_term,*)) =>
    `(cas_term| ($first:cas_term, $rest:cas_term,*) ↦ $body:cas_term)
  | `(cas_term| ($inner:cas_term)) => patternFunction inner body
  | _ => throwErrorAt pattern "a source function parameter must be a name or tuple pattern"

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
  | `(cas_stmt| let $name:ident($parameter:cas_term) := $value:cas_term) =>
    let translated ← match value with
      | `(cas_term| $body:cas_term in $domain:cas_term) => do
        let function ← patternFunction parameter body
        `(cas_term| $function:cas_term in $domain:cas_term)
      | _ => patternFunction parameter value
    -- Public let-function syntax expands once. The native value retains its actual
    -- preceding bindings; its span refers to the original statement, not generated syntax.
    let value ← session.readAt stx translated
    return .definition (← session.defineTerm name.getId value) value
  | `(cas_stmt| assert implemented $body:cas_term) =>
    return .implemented (← session.read body)
  | `(cas_stmt| assert $body:cas_term) =>
    match body with
    | `(cas_term| $_:cas_term ∈ $_:cas_term)
    | `(cas_term| $_:cas_term in $_:cas_term) => typingQuestion session body
    | _ => return .question (← session.readQuestion body)
  | _ =>
    CasCatalogue.throwUnsupportedSource
      "source translation is not implemented for this statement form"

end CasCompiler
