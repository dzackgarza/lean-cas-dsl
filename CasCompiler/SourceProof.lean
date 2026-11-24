module

public import CasCompiler.Elaborate
public import CasCompiler.Syntax

public section

namespace CasCompiler

open Lean Meta Elab Term

/-- Check an explicitly supplied source proof at an independently prepared proposition.
Reuse: native expected-type elaboration and stable-ID context transport. The source hypothesis
and proof remain formal; this operation accepts no computational response as evidence. -/
opaque SourceSession.proof (session : SourceSession) (stx : TSyntax `cas_term)
    (obligation : ClosedTerm) : TermElabM SourceTerm := withRef stx do
  let `(cas_term| proof($evidence:term)) := stx
    | throwError "source evidence requires an explicit proof term"
  session.elaborate evidence fun context => do
    sourceFormalProof evidence (← obligation.inContext context)

end CasCompiler
