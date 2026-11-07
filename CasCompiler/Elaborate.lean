module

public import CasCompiler.Context
public import CasCompiler.Declaration
public import CasCompiler.Syntax
public import CasRuntime.Identity
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
  private identities : CasRuntime.IdentitySupply
  context : ContextTelescope
  spans : Array SourceSpan

/-- Source declarations share the worker's monotone identity supply across snapshot branches.
Reuse: IdentitySupply.fresh and its native atomic counter; only identities live in the supply. -/
private def SourceSession.freshBinding (session : SourceSession) : BaseIO BindingId := do
  let id ← session.identities.fresh .sourceBinding
  return ⟨id.worker, id.serial⟩

private def defineIn (session : SourceSession) (context : OpenContext) (name : Name)
    (expression : Expr) (span : SourceSpan) : MetaM SourceSession := do
  let type ← inferType expression
  let id ← session.freshBinding
  withLetDecl name type expression fun expression => do
    let context ← ContextTelescope.capture
      (context.bindings.push { id, role := .definition, expression })
    return ⟨session.identities, context.telescope, session.spans.push span⟩

opaque SourceSession.empty (identities : CasRuntime.IdentitySupply) : MetaM SourceSession := do
  let context ← withLCtx {} #[] <| ContextTelescope.capture #[]
  return ⟨identities, context.telescope, #[]⟩

/-- Apply the release's safety and axiom policy to the newly completed source term and type.
Reuse: Lean.collectAxioms and the existing source-family intake policy in Program.lean.
Earlier declarations were checked when inserted into this private persistent session. -/
private def checkSource (source : ClosedTerm) : MetaM Unit := do
  let constants := source.expression.getUsedConstants ++ source.type.getUsedConstants
  for declaration in constants do
    discard <| checkedDeclaration declaration

/-- Form a checked source term directly in the complete native scope.
Reuse: ContextTelescope.withOpen, native synthesis and OpenContext.close. Public frontend
adapters supply native expressions; source terms never pass through a syntax replay table. -/
opaque SourceSession.elaborate (session : SourceSession) (reference : Syntax)
    (build : OpenContext → TermElabM Expr) : TermElabM SourceTerm :=
  withRef reference <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let expression ← instantiateMVars (← withSynthesize <| build context)
      let source ← context.close expression
      checkSource source
      return ⟨source, ← sourceSpan reference⟩

/-- Elaborate in the complete native context and publish only a resolved checked expression.
Reuse: Lean 4.33.0 Term.elabTermEnsuringType, withSynthesize and native context reopening.
Source syntax is consumed here; persistent definitions store their checked values. -/
opaque SourceSession.term (session : SourceSession) (stx : Term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  session.elaborate stx fun context => do
    let expected ← expected.mapM (·.inContext context)
    elabTermEnsuringType stx expected

/-- Intake the whole source declaration before selecting explicit rigid universe arguments.
Reuse: checkedDeclaration and Lean.mkConst; native checking retains the full family type. -/
opaque SourceSession.constant (session : SourceSession) (reference : Syntax) (name : Name)
    (universes : List Level) : TermElabM SourceTerm :=
  session.elaborate reference fun _ => do
    let info ← checkedDeclaration name
    unless universes.length == info.levelParams.length do
      throwError "source universe arguments do not match the whole declaration"
    let universes ← universes.mapM instantiateLevelMVars
    if universes.any (·.hasMVar) then
      throwError "source declaration intake requires resolved universe arguments"
    return mkConst name universes

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
      let id ← session.freshBinding
      withLocalDecl name binderInfo type fun expression => do
        let context ← ContextTelescope.capture (bindings.push { id, role, expression })
        return ⟨session.identities, context.telescope,
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
      defineIn session context name expression (← sourceSpan stx)

/-- Bind an already checked source value by native context transport and a fresh declaration.
Reuse: ClosedTerm.inContext and the same native let capture as ordinary source definitions. -/
opaque SourceSession.defineTerm (session : SourceSession) (name : Name) (term : SourceTerm) :
    MetaM SourceSession :=
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    defineIn session context name (← term.source.inContext context) term.span

/-- Form ordinary native application from retained checked function and argument sources.
Reuse: OpenContext.apply, also used by SourceLayout.applyIn, with complete argument order. -/
opaque SourceSession.apply (session : SourceSession) (reference : Syntax) (function : SourceTerm)
    (arguments : Array SourceTerm) : TermElabM SourceTerm :=
  session.elaborate reference fun context => do
    context.apply function.source (arguments.map (·.source))

end CasCompiler
