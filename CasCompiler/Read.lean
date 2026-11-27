module

public import CasCompiler.ReadSession
public meta import CasCompiler.ReadExpression
public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

syntax (name := sourceExpression) "cas_source% " cas_term : term



@[term_elab sourceExpression] meta def elabSourceExpression : TermElab := fun stx expected => do
  SourceReadM.elaborateNative stx do
    return (← readExpression (fun _ => pure none) ⟨stx[1]⟩ expected).value

end CasCompiler
