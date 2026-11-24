module

public import CasCompiler.Context
public import CasCompiler.Declaration
public import CasCompiler.SourceReference
public import CasCompiler.Syntax
public import CasRuntime.Identity
public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Catalogue.Registry.Entry
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

inductive SourceCategoryRole where
  | object
  | morphism
  deriving BEq

/-- A carrier prefix selected by the independent object registration.
Its remaining edges and comparison declarations survive native aliases and explicit views. -/
structure SourceCarrierSelection where
  refs : Array CasCatalogue.EdgeRef
  target : CasCatalogue.CategoryExpr
  identifications : Array Name
  actions : Array ClosedTerm
  comparisons : Array ClosedTerm

structure NativeSourceCarrierSelection where
  refs : Array CasCatalogue.EdgeRef
  target : CasCatalogue.CategoryExpr
  identifications : Array Name
  actions : Array Expr
  comparisons : Array Expr

/-- The registered limit or colimit that a source construction selected: its row, and its cone or
cocone at the source diagram. A later use (`K.leg(j)`) takes them from here, not from the apex. -/
structure SourceLimitSelection where
  row : String
  declaration : Name
  cone : ClosedTerm
  colimit : Bool
  category : CasCatalogue.CategoryExpr
  bundle : ClosedTerm

structure NativeSourceLimitSelection where
  row : String
  declaration : Name
  cone : Expr
  colimit : Bool
  category : CasCatalogue.CategoryExpr
  bundle : Expr

/-- The selected symbolic category and its complete native bundle in the original context. -/
structure SourceCategoryBinding where
  private mk ::
  expression : CasCatalogue.CategoryExpr
  bundle : ClosedTerm
  role : SourceCategoryRole
  carrier : Option SourceCarrierSelection := none
  limit : Option SourceLimitSelection := none

/-- A native value's selected category, including whether it is an object or an arrow. -/
structure NativeSourceCategory where
  role : SourceCategoryRole
  expression : CasCatalogue.CategoryExpr
  bundle : Expr
  carrier : Option NativeSourceCarrierSelection := none
  limit : Option NativeSourceLimitSelection := none

/-- An elaborated value and any category explicitly selected by the source frontend. -/
structure NativeSourceJudgement where
  value : Expr
  category : Option NativeSourceCategory

/-- A completed checked source expression, with its full telescope and original source span. -/
structure SourceTerm where
  private mk ::
  source : ClosedTerm
  span : SourceSpan
  category : Option SourceCategoryBinding

/-- A variable that a ring written in a source definition names: `x` of `ℚ[x]`, `x_3` (index 3)
of `ℂ[x_0, …, x_9]`, with the ring's carrier. -/
structure SourceRingVariable where
  name : Name
  carrier : ClosedTerm
  index : Option Nat

/-- Persistent source declarations. Later terms reopen their checked native declarations.
Source: mathematical-input contract §1 and data-model contract §2, lean-cas-dsl#66.
No provider, runtime value or stored binding syntax participates in this context. -/
structure SourceSession where
  private mk ::
  private identities : CasRuntime.IdentitySupply
  context : ContextTelescope
  spans : Array SourceSpan
  private categories : Array (Option SourceCategoryBinding)
  /-- The ring variables each definition's source wrote, by entry position. -/
  private rings : Array (Array SourceRingVariable)
  /-- Inert declaration-time type displays; native entries remain the authority. -/
  private descriptions : Array String

/-- An immutable observation of the original complete source scope. Display strings are
formed when declarations enter the session; inspecting this record performs no elaboration. -/
structure SourceContextObservation where
  private mk ::
  context : ContextTelescope
  spans : Array SourceSpan
  categories : Array (Option SourceCategoryBinding)
  descriptions : Array String

/-- Freeze the actual context and its selected category table without opening or evaluating it. -/
def SourceSession.observation (session : SourceSession) : SourceContextObservation :=
  ⟨session.context, session.spans, session.categories, session.descriptions⟩

def SourceContextObservation.categoryFor (observation : SourceContextObservation)
    (id : BindingId) : Option SourceCategoryBinding := do
  let index ← observation.context.entries.findIdx? (·.id == id)
  observation.categories[index]?.bind fun category => category

/-- Explicit assumption inspection uses only frozen declaration displays and stable identities.
Definitions remain in the native context but are not presented as hypothetical assumptions. -/
def SourceContextObservation.assumptionsText (observation : SourceContextObservation) : String :=
  Id.run do
    let mut lines := #[]
    for entry in observation.context.entries, index in [:observation.context.entries.size] do
      if entry.role == .parameter || entry.role == .hypothesis || entry.role == .instance then
        let role := if entry.role == .hypothesis then "hypothesis"
          else if entry.role == .instance then "instance" else "parameter"
        let type := observation.descriptions[index]?.getD ""
        lines := lines.push s!"{role} {entry.userName}: {type} [{entry.id.session}:{entry.id.serial}]"
    return if lines.isEmpty then "No local assumptions." else "\n".intercalate lines.toList

/-- A statement's original source terms and scope, retained even after lexical scope exit.
The optional proof is only explicitly checked native evidence, never a computational response. -/
structure SourceConclusion where
  private mk ::
  terms : Array SourceTerm
  context : SourceContextObservation
  proof : Option SourceTerm := none

/-- Attach the already checked statement to the actual source scope that formed it. -/
opaque SourceSession.conclusion (session : SourceSession) (terms : Array SourceTerm)
    (proof : Option SourceTerm := none) : MetaM SourceConclusion := do
  for term in terms ++ proof.toArray do
    unless term.source.context.exactlyMatches session.context do
      throwError "a retained conclusion changed its complete source scope"
  if let some evidence := proof then
    let #[proposition] := terms
      | throwError "explicit evidence requires one retained proposition"
    session.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let proposition ← proposition.source.inContext context
      unless (← isProp proposition) &&
          (← isDefEq (← inferType (← evidence.source.inContext context)) proposition) do
        throwError "a retained proof has a different original proposition"
  return ⟨terms, session.observation, proof⟩

/-- Public post-scope inspection of a retained conclusion; no current session is consulted. -/
def SourceConclusion.inspectAssumptions (conclusion : SourceConclusion) : String :=
  conclusion.context.assumptionsText

/-- The ring variables written by the source of the declaration `id`. -/
def SourceSession.ringsFor (session : SourceSession) (id : BindingId) :
    Array SourceRingVariable := Id.run do
  let some index := session.context.entries.findIdx? (·.id == id) | return #[]
  return session.rings[index]?.getD #[]

/-- Retain the ring variables that the source of the latest declaration wrote. -/
def SourceSession.recordRings (session : SourceSession) (written : Array SourceRingVariable) :
    SourceSession :=
  { session with rings := session.rings.pop.push written }

def SourceSession.categoryFor (session : SourceSession) (id : BindingId) :
    Option SourceCategoryBinding := do
  let index ← session.context.entries.findIdx? (·.id == id)
  session.categories[index]?.bind fun category => category

private def SourceSession.categoryOf (session : SourceSession) (context : OpenContext)
    (expression : Expr) : Option SourceCategoryBinding := do
  let .fvar binderId := expression | none
  let binding ← context.bindings.find? (·.expression.fvarId! == binderId)
  session.categoryFor binding.id

/-- The identity functor of the supplied complete category, with its actual structure.
Reuse: native Bundled projections and Functor.id, also used by source route interpretation. -/
opaque categoryIdentity (category : Expr) : MetaM Expr := do
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
  let categoryStructure ← mkAppM ``CategoryTheory.Bundled.str #[category]
  mkAppOptM ``CategoryTheory.Functor.id #[some carrier, some categoryStructure]

/-- Inspect the source head through assigned native variables and original definitions.
Uses retain their actual references. Reuse: Lean.Meta.instantiateMVars and native let values. -/
partial def sourceDomain (value : Expr) : MetaM Expr := do
  if let some endpoint := selectedEndpoint? (← instantiateMVars value) then
    return ← sourceDomain endpoint
  let value := (← instantiateMVars value).headBeta.consumeMData
  if value.isAppOfArity ``Function.const 4 then
    return ← sourceDomain value.getAppArgs[2]!
  if let .fvar id := value then
    if let some definition := (← id.getDecl).value? then return ← sourceDomain definition
  return value

/-- Attach only a supplied category bundle, checked at the complete retained source type.
Reuse: native Bundled.α and stable-ID context transport. Category identity is supplied by
source selection, never inferred from a carrier type. Source: #66, comment 6664276482 §1. -/
opaque SourceTerm.inCategory (term : SourceTerm) (expression : CasCatalogue.CategoryExpr)
    (category : SourceTerm) (role : SourceCategoryRole := .object)
    (selection : Option SourceCarrierSelection := none)
    (limit : Option SourceLimitSelection := none) : MetaM SourceTerm := do
  term.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    let categoryValue ← category.source.inContext context
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[categoryValue]
    match role with
    | .object =>
      unless ← isDefEq (← inferType value) carrier do
        throwError "the source value does not inhabit its selected native category"
    | .morphism =>
      -- Native identity-map application checks both endpoints in the supplied category.
      let identity ← categoryIdentity categoryValue
      discard <| withTransparency .all <| mkAppM ``CategoryTheory.Functor.map #[identity, value]
  return { term with category := some ⟨expression, category.source, role, selection, limit⟩ }

/-- Source declarations share the worker's monotone identity supply across snapshot branches.
Reuse: IdentitySupply.fresh and its native atomic counter; only identities live in the supply. -/
private def SourceSession.freshBinding (session : SourceSession) : BaseIO BindingId := do
  let id ← session.identities.fresh .sourceBinding
  return ⟨id.worker, id.serial⟩

private def defineIn (session : SourceSession) (context : OpenContext) (name : Name)
    (expression : Expr) (span : SourceSpan) (category : Option SourceCategoryBinding) :
    MetaM SourceSession := do
  let type ← inferType expression
  let id ← session.freshBinding
  withLetDecl name type expression fun expression => do
    let context ← ContextTelescope.capture
      (context.bindings.push { id, role := .definition, expression })
    return ⟨session.identities, context.telescope, session.spans.push span,
      session.categories.push category, session.rings.push #[],
      session.descriptions.push ""⟩

opaque SourceSession.empty (identities : CasRuntime.IdentitySupply) : MetaM SourceSession := do
  let context ← withLCtx {} #[] <| ContextTelescope.capture #[]
  return ⟨identities, context.telescope, #[], #[], #[], #[]⟩

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
opaque SourceSession.elaborateJudgements (session : SourceSession) (reference : Syntax)
    (build : OpenContext → TermElabM (Array NativeSourceJudgement)) :
    TermElabM (Array SourceTerm) :=
  withRef reference <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let expressions ← withSynthesize <| build context
      let span ← sourceSpan reference
      expressions.mapM fun judgement => do
        let expression ← instantiateMVars judgement.value
        let source ← context.close (← instantiateMVars expression)
        checkSource source
        let term : SourceTerm := ⟨source, span, session.categoryOf context expression⟩
        match judgement.category with
        | none => return term
        | some selected =>
          let category ← context.close (← instantiateMVars selected.bundle)
          checkSource category
          let selection ← selected.carrier.mapM fun carrier => do
            let close := fun action => do
              let action ← context.close (← instantiateMVars action)
              checkSource action
              return action
            let actions ← carrier.actions.mapM close
            let comparisons ← carrier.comparisons.mapM close
            return (⟨carrier.refs, carrier.target, carrier.identifications, actions, comparisons⟩ :
              SourceCarrierSelection)
          let limit ← selected.limit.mapM fun limit => do
            let cone ← context.close (← instantiateMVars limit.cone)
            checkSource cone
            let bundle ← context.close (← instantiateMVars limit.bundle)
            checkSource bundle
            return (⟨limit.row, limit.declaration, cone, limit.colimit, limit.category, bundle⟩ :
              SourceLimitSelection)
          term.inCategory selected.expression ⟨category, span, none⟩ selected.role selection limit

/-- Form ordinary checked native terms through the same complete source boundary. -/
opaque SourceSession.elaborateMany (session : SourceSession) (reference : Syntax)
    (build : OpenContext → TermElabM (Array Expr)) : TermElabM (Array SourceTerm) :=
  session.elaborateJudgements reference fun context => do
    return (← build context).map fun value => ⟨value, none⟩

opaque SourceSession.elaborate (session : SourceSession) (reference : Syntax)
    (build : OpenContext → TermElabM Expr) : TermElabM SourceTerm := do
  let #[source] ← session.elaborateMany reference fun context => do
      return #[← build context]
    | throwError "source formation returned an invalid number of expressions"
  return source

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

/-- Check supplied formal evidence at its independently prepared native proposition.
Both source-session proof intake and constrained-point construction use this same check. -/
def sourceFormalProof (evidence : Term) (proposition : Expr) : TermElabM Expr :=
  withRef evidence do
    unless ← isProp proposition do
      throwError "a formal proof requires a source proposition"
    withSynthesize do
      let proof ← elabTerm evidence (some proposition)
      if ← isDefEq (← inferType proof) proposition then return proof
      -- Preserve native expected-type elaboration and coercions. Only an explicit
      -- native no-coercion result identifies a rejected proof obligation.
      -- Reuse: Lean.Elab.Term.ensureHasType / mkCoe at the pinned Lean version.
      match ← coerceCollectingNames? proof proposition with
      | .some (coerced, expandedCoeDecls) =>
        pushInfoLeaf (.ofCustomInfo {
          stx := ← getRef
          value := Dynamic.mk (CoeExpansionTrace.mk expandedCoeDecls)
        })
        return coerced
      | .none =>
        throwError (MessageData.tagged `CasCompiler.sourceFormalProof.typeMismatch
          (← mkTypeMismatchError none proof (← inferType proof) proposition))
      | .undef =>
        -- Pending native coercions retain the ordinary synthesis/error lifecycle.
        ensureHasType (some proposition) proof

/-- Check an explicitly supplied source proof at an independently prepared proposition.
Reuse: native expected-type elaboration and stable-ID context transport. The source hypothesis
and proof remain formal; this operation accepts no computational response as evidence. -/
opaque SourceSession.proof (session : SourceSession) (stx : TSyntax `cas_term)
    (obligation : ClosedTerm) : TermElabM SourceTerm := withRef stx do
  let `(cas_term| proof($evidence:term)) := stx
    | throwError "source evidence requires an explicit proof term"
  session.elaborate evidence fun context => do
    sourceFormalProof evidence (← obligation.inContext context)

private def assumeIn (session : SourceSession) (context : OpenContext) (name : Name)
    (type : Expr) (span : SourceSpan) (binderInfo : BinderInfo)
    (category : Option SourceCategoryBinding := none) : MetaM SourceSession := do
  discard <| getLevel type
  let role ← if binderInfo == .instImplicit then do
      unless (← isClass? type).isSome do
        throwError "a selected-instance source binder must have a class type"
      pure BindingRole.instance
    else if ← isProp type then pure BindingRole.hypothesis
    else pure BindingRole.parameter
  let description := (← ppExpr type).pretty
  let id ← session.freshBinding
  withLocalDecl name binderInfo type fun expression => do
    let context ← ContextTelescope.capture (context.bindings.push { id, role, expression })
    return ⟨session.identities, context.telescope, session.spans.push span,
      session.categories.push category, session.rings.push #[],
      session.descriptions.push description⟩

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
      assumeIn session context name type (← sourceSpan stx) binderInfo

/-- Bind a retained source type through native context transport and native sort checking.
Reuse: ClosedTerm.inContext, Meta.getLevel and the ordinary native binder capture. -/
opaque SourceSession.assumeTerm (session : SourceSession) (name : Name) (type : SourceTerm)
    (binderInfo : BinderInfo := .default) : MetaM SourceSession :=
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    assumeIn session context name (← type.source.inContext context) type.span binderInfo

/-- Bind an abstract object of the explicitly selected complete native category.
The fresh local has no definition or catalogue value; only the supplied category is retained. -/
opaque SourceSession.assumeObject (session : SourceSession) (name : Name)
    (expression : CasCatalogue.CategoryExpr) (category : SourceTerm) : MetaM SourceSession :=
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let bundle ← category.source.inContext context
    discard <| categoryIdentity bundle
    let type ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    let source ← context.close type
    checkSource source
    assumeIn session context name type category.span .default
      (some ⟨expression, category.source, .object, none, none⟩)

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
        (session.categoryOf context expression)

/-- Bind an already checked source value by native context transport and a fresh declaration.
Reuse: ClosedTerm.inContext and the same native let capture as ordinary source definitions. -/
opaque SourceSession.defineTerm (session : SourceSession) (name : Name) (term : SourceTerm) :
    MetaM SourceSession :=
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    defineIn session context name (← term.source.inContext context) term.span term.category

/-- Form ordinary native application from retained checked function and argument sources.
Reuse: OpenContext.apply, also used by SourceLayout.applyIn, with complete argument order. -/
opaque SourceSession.apply (session : SourceSession) (reference : Syntax) (function : SourceTerm)
    (arguments : Array SourceTerm) : TermElabM SourceTerm :=
  session.elaborate reference fun context => do
    context.apply function.source (arguments.map (·.source))

end CasCompiler
