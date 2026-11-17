module

public import CasCompiler.ReadSession
public meta import CasCompiler.ReadExpression
public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

syntax (name := sourceExpression) "cas_source% " cas_term : term

/-- Standalone syntax uses the same source reader; retained category selections come from
the SourceSession entry point rather than a carrier-type inference or global replay table. -/
@[term_elab sourceExpression] meta def elabSourceExpression : TermElab := fun stx expected => do
  return (← readExpression (fun _ => pure none) ⟨stx[1]⟩ expected).value

end CasCompiler
