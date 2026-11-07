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

/-- Read public source syntax directly in the retained native context.
Reuse: Lean's term elaborator supplies dependent parameter types and local bindings. -/
opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm := do
  let #[term] ← session.elaborateJudgements stx fun context => do
    let expected ← expected.mapM (·.inContext context)
    let categoryOf := fun id => do
      let some binding := context.bindings.find? (·.expression.fvarId! == id)
        | return none
      let some category := session.categoryFor binding.id | return none
      return some (category.expression, ← category.bundle.inContext context)
    return #[← readExpression categoryOf stx expected]
    | throwError "source reading returned an invalid number of judgements"
  return term

end CasCompiler
