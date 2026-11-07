module

public import CasCompiler.Context
public import CasCompiler.Syntax
public import CasGates.AxiomAuditRules
public import Lean.Elab.Term
public import Lean.Elab.SyntheticMVars

public section

namespace CasCompiler

open Lean Meta Elab Term

structure SourceSpan where
  fileName : String
  start : Option String.Pos.Raw
  stop : Option String.Pos.Raw

private def sourceSpan (stx : Syntax) : CoreM SourceSpan := do
  return ⟨← getFileName, stx.getPos?, stx.getTailPos?⟩

/-- A completed checked source expression, with its full telescope and original source span. -/
structure SourceTerm where
  private mk ::
  source : ClosedTerm
  span : SourceSpan

/-- Persistent source declarations. Later terms reopen their checked native declarations.
Source: mathematical-input contract §1 and data-model contract §2, lean-cas-dsl#66.
No provider, runtime value or stored binding syntax participates in this context. -/
structure SourceSession where
  private mk ::
  private identity : String
  private nextBinding : Nat
  context : ContextTelescope
  spans : Array SourceSpan

opaque SourceSession.empty (identity : String) : MetaM SourceSession := do
  if identity.isEmpty then throwError "a source session requires a stable identity"
  let context ← withLCtx {} #[] <| ContextTelescope.capture #[]
  return ⟨identity, 0, context.telescope, #[]⟩

/-- Apply the release's safety and axiom policy to the newly completed source term and type.
Reuse: Lean.collectAxioms and the existing source-family intake policy in Program.lean.
Earlier declarations were checked when inserted into this private persistent session. -/
private def checkSource (source : ClosedTerm) : MetaM Unit := do
  let constants := source.expression.getUsedConstants ++ source.type.getUsedConstants
  for declaration in constants do
    let info ← getConstInfo declaration
    if info.isUnsafe then throwError "source declaration {declaration} is unsafe"
    for assumption in ← collectAxioms declaration do
      unless CasCatalogue.Tools.AxiomAudit.permitted.contains assumption do
        throwError "source declaration {declaration} depends on {assumption}"

/-- Elaborate in the complete native context and publish only a resolved checked expression.
Reuse: Lean 4.33.0 Term.elabTermEnsuringType, withSynthesize and native context reopening.
Source syntax is consumed here; persistent definitions store their checked values. -/
opaque SourceSession.term (session : SourceSession) (stx : Term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  withRef stx <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let expected ← expected.mapM (·.inContext context)
      let expression ← instantiateMVars (← withSynthesize <| elabTermEnsuringType stx expected)
      let source ← context.close expression
      checkSource source
      return ⟨source, ← sourceSpan stx⟩

/-- A formal proposition is retained as a question; elaboration does not establish it. -/
opaque SourceSession.proposition (session : SourceSession) (stx : Term) :
    TermElabM SourceTerm := withRef stx do
  let term ← session.term stx
  term.source.withOpen fun _ expression => do
    unless ← isProp expression do throwError "a source proposition must have type Prop"
  return term

/-- Check an explicitly supplied source proof at an independently prepared proposition.
Reuse: native expected-type elaboration and stable-ID context transport. The source hypothesis
and proof remain formal; this operation accepts no computational response as evidence. -/
opaque SourceSession.proof (session : SourceSession) (stx : TSyntax `cas_term)
    (obligation : ClosedTerm) : TermElabM SourceTerm := withRef stx do
  obligation.withOpen fun _ proposition => do
    unless ← isProp proposition do
      throwError "a formal proof requires a source proposition"
  let `(cas_term| proof($evidence:term)) := stx
    | throwError "source evidence requires an explicit proof term"
  session.term evidence (some obligation)

/-- Add one native parameter, hypothesis or selected instance with a fresh stable source ID.
Reuse: Lean.elabType and Meta.withLocalDecl, including native local-instance registration. -/
opaque SourceSession.assume (session : SourceSession) (name : Name) (stx : Term)
    (binderInfo : BinderInfo := .default) : TermElabM SourceSession :=
  withRef stx <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let type ← instantiateMVars (← withSynthesize <| elabType stx)
      let source ← context.close type
      checkSource source
      let role ← if binderInfo == .instImplicit then do
          unless (← isClass? type).isSome do
            throwError "a selected-instance source binder must have a class type"
          pure BindingRole.instance
        else if ← isProp type then pure BindingRole.hypothesis
        else pure BindingRole.parameter
      let id : BindingId := ⟨session.identity, session.nextBinding⟩
      withLocalDecl name binderInfo type fun expression => do
        let context ← ContextTelescope.capture (bindings.push { id, role, expression })
        return ⟨session.identity, session.nextBinding + 1, context.telescope,
          session.spans.push (← sourceSpan stx)⟩

/-- Retain an elaborated definition as a native let declaration for all subsequent source use.
Reuse: Term.elabTermEnsuringType and Meta.withLetDecl; no expansion/replay table is stored. -/
opaque SourceSession.define (session : SourceSession) (name : Name) (stx : Term)
    (annotation : Option Term := none) : TermElabM SourceSession :=
  withRef stx <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let expected ← annotation.mapM fun stx => withSynthesize <| elabType stx
      let expression ← instantiateMVars (← withSynthesize <| elabTermEnsuringType stx expected)
      let source ← context.close expression
      checkSource source
      let type ← inferType expression
      let id : BindingId := ⟨session.identity, session.nextBinding⟩
      withLetDecl name type expression fun expression => do
        let context ← ContextTelescope.capture
          (bindings.push { id, role := .definition, expression })
        return ⟨session.identity, session.nextBinding + 1, context.telescope,
          session.spans.push (← sourceSpan stx)⟩

end CasCompiler
