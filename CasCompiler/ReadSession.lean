module

public import CasCompiler.ReadExpression
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

private def sourceCategory (session : SourceSession) (context : OpenContext)
    (id : FVarId) : TermElabM (Option NativeSourceCategory) := do
  let some binding := context.bindings.find? (·.expression.fvarId! == id)
    | return none
  let some category := session.categoryFor binding.id | return none
  let carrier ← category.carrier.mapM fun carrier => do
    return (⟨carrier.refs, carrier.target, carrier.identifications,
      ← carrier.actions.mapM (·.inContext context),
      ← carrier.comparisons.mapM (·.inContext context)⟩ : NativeSourceCarrierSelection)
  let limit ← category.limit.mapM fun limit => do
    let interface ← limit.interface.mapM (·.inContext context)
    return (⟨limit.row, limit.declaration, ← limit.cone.inContext context, limit.colimit,
      ← limit.presentation.inContext context, ← limit.diagram.inContext context, interface⟩ :
      NativeSourceLimitSelection)
  return some ⟨category.role, category.expression, ← category.bundle.inContext context,
    carrier, limit⟩

/-- The ring variables of the session's definitions that `stx` names, in `context`. -/
private def recordedRings (session : SourceSession) (context : OpenContext) (stx : Syntax) :
    TermElabM (Array (Name × Expr × Option Nat)) := do
  let mut found := #[]
  for binding in context.bindings do
    unless sourceUses (← binding.expression.fvarId!.getUserName) stx do continue
    for ring in session.ringsFor binding.id do
      found := found.push (ring.name, ← ring.carrier.inContext context, ring.index)
  return found

/-- The variables of the rings that the definition `stx` writes, with their carriers, retained by
the session for the statements that use this definition. -/
private def writtenRings (session : SourceSession) (stx : Syntax) :
    TermElabM (Array SourceRingVariable) := do
  let mut found := #[]
  for (name, ring, index) in sourceRingVariables stx do
    if found.any (fun (written : SourceRingVariable) => written.name == name) then continue
    let carrier ← session.elaborate ring fun context => do
      let object ← readExpression (sourceCategory session context) ⟨ring⟩ none
      return (← sourceCarrier object).value
    found := found.push ⟨name, carrier.source, index⟩
  return found

/-- Insert a definition and retain the ring variables its source wrote. -/
private def SourceSession.defineWritten (session : SourceSession) (stx : Syntax) (name : Name)
    (value : SourceTerm) : TermElabM SourceSession := do
  let rings ← writtenRings session stx
  return (← session.defineTerm name value).recordRings rings

private def SourceSession.readAt (session : SourceSession) (reference : Syntax)
    (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm := do
  let #[term] ← session.elaborateJudgements reference fun context => do
    let expected ← expected.mapM (·.inContext context)
    return #[← readSourceTerm (sourceCategory session context)
      (← recordedRings session context stx) stx expected]
    | throwError "source reading returned an invalid number of judgements"
  return term

/-- Read public source syntax directly in the retained native context.
Reuse: Lean's term elaborator supplies dependent parameter types and local bindings. -/
opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  session.readAt stx stx expected

/-- Introduce a native local declaration. A named category selects its complete bundle;
ordinary source domains supply the native type, including retained propositions. -/
private def SourceSession.assumeWritten (session : SourceSession) (reference : Syntax)
    (name : Name) (domain : TSyntax `cas_term) : TermElabM SourceSession := do
  let selected ← session.context.withOpen fun _ => SourceReader.categoryEntry? domain
  let (type, selection) ← match selected with
    | some (entry, arguments) => do
      let bundle ← session.elaborate reference fun context => do
        let categoryOf := sourceCategory session context
        let bundle ← withSynthesize <| withRingVariables categoryOf
          (← recordedRings session context domain) domain do
            return ⟨← readCategory categoryOf domain entry arguments, none⟩
        discard <| levelMVarToParam (← instantiateMVars bundle.value)
        return ← instantiateMVars bundle.value
      let type ← session.elaborate reference fun context => do
        mkAppM ``CategoryTheory.Bundled.α #[← bundle.source.inContext context]
      pure (type, some (entry.expression, bundle))
    | none => do
      let type ← session.elaborate reference fun context => do
        let value ← readSourceTerm (sourceCategory session context)
          (← recordedRings session context domain) domain none
        return (← sourceCarrier value).value
      pure (type, none)
  let rings ← writtenRings session domain
  return (← session.assumeTerm name type .default selection).recordRings rings

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
    return (← withRingVariables categoryOf (← recordedRings session context stx) stx do
      return ⟨← questionExpression categoryOf stx, none⟩).value

/-- A definition extends the native scope. A question retains that scope without extending it.
An implementation request asks that the installed computations produce the value. A typing
question (`x ∈ Y` or `x in Y` for an object `Y`) is settled by reading `x` in `Y`. -/
inductive SourceStatement where
  | assumption (session : SourceSession)
  | definition (session : SourceSession) (value : SourceTerm)
  | question (proposition : SourceTerm)
  | implemented (value : SourceTerm)
  | settled (values : Array SourceTerm)

/-- Read an asserted membership or annotation. Membership in a subset is a proposition; in an
object it is the element's reading there, whose success settles the question.
Source: mathematical-input contract §1; the original reader's settled typing judgements. -/
private def typingQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceStatement := do
  let term ← session.elaborate stx fun context =>
    return (← readSourceTerm (sourceCategory session context)
      (← recordedRings session context stx) stx none).value
  let proposition ← term.source.withOpen fun _ expression => isProp expression
  return if proposition then .question term else .settled #[term]

/-- `X ⊆ Y` for two named sets: the map that a chain of registered inclusions of `X` in `Y`
gives (`sourceCoercion?`: registered inclusions and registered constants; several chains are a
competing reading). With no chain the judgement is not established. `none` when a side is not an
object: `⊆` is then the order of subsets, a proposition. -/
private def inclusionJudgement? (session : SourceSession) (stx left right : TSyntax `cas_term) :
    TermElabM (Option SourceTerm) := do
  try
    return some (← session.elaborate stx fun context => do
      let categoryOf := sourceCategory session context
      let rings ← recordedRings session context stx
      let source ← readSourceTerm categoryOf rings left none
      let target ← readSourceTerm categoryOf rings right none
      unless source.category.any (·.role == .object) && target.category.any (·.role == .object) do
        throwReadRuleMismatch
      unless (← whnfR (← inferType source.value)).isSort &&
          (← whnfR (← inferType target.value)).isSort do
        throwReadRuleMismatch
      withLocalDeclD `x source.value fun element => do
        let some included ← sourceCoercion? element target.value
          | CasCatalogue.throwStratum .invalid
              m!"no chain of registered inclusions gives {left} ⊆ {right}"
        mkLambdaFVars #[element] included)
  catch error =>
    match error with
    | .internal id _ => if id == readRuleMismatch then return none else throw error
    | _ => throw error

/-- The typing judgements of an assertion, when every conjunct is one and each is settled:
`x ∈ Y` or `x in Y` for an object `Y`, and `X ⊆ Y` for named sets. `none` when a conjunct is a
proposition; the assertion is then read as a question. -/
private partial def settledJudgements? (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM (Option (Array SourceTerm)) := do
  match stx with
  | `(cas_term| ($body:cas_term)) => settledJudgements? session body
  | `(cas_term| $left:cas_term and $right:cas_term) =>
    let some first ← settledJudgements? session left | return none
    let some second ← settledJudgements? session right | return none
    return some (first ++ second)
  | `(cas_term| $_:cas_term ∈ $_:cas_term)
  | `(cas_term| $_:cas_term in $_:cas_term) =>
    match ← typingQuestion session stx with
    | .settled values => return some values
    | _ => return none
  | `(cas_term| $left:cas_term ⊆ $right:cas_term) =>
    return (← inclusionJudgement? session stx left right).map fun value => #[value]
  | _ => return none

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
  -- Public let-function syntax expands once. The native value retains its actual preceding
  -- bindings; its span refers to the original statement, not generated syntax.
  let defineFunction := fun (name : TSyntax `ident) (parameter value : TSyntax `cas_term) => do
    let translated ← match value with
      | `(cas_term| $body:cas_term in $domain:cas_term) => do
        let function ← patternFunction parameter body
        `(cas_term| $function:cas_term in $domain:cas_term)
      | _ => patternFunction parameter value
    let value ← session.readAt stx translated
    return SourceStatement.definition (← session.defineWritten translated name.getId value) value
  match stx with
  | `(cas_stmt| let $name:ident := $body:cas_term) =>
    let value ← session.read body
    return .definition (← session.defineWritten body name.getId value) value
  | `(cas_stmt| let $name:ident : $annotation:cas_term := $body:cas_term) =>
    let type ← session.read annotation
    type.source.withOpen fun _ expression => discard <| getLevel expression
    let value ← session.read body (some type.source)
    return .definition (← session.defineWritten annotation name.getId value) value
  | `(cas_stmt| let $name:ident ∈ $domain:cas_term)
  | `(cas_stmt| let $name:ident : $domain:cas_term) =>
    return .assumption (← session.assumeWritten stx name.getId domain)
  | `(cas_stmt| let $name:ident($parameter:cas_term) := $value:cas_term) =>
    defineFunction name parameter value
  | `(cas_stmt| let $name:ident($first:ident, $rest:ident,*) := $value:cas_term) =>
    -- Several parameters are one tuple pattern: `let f(x, y) := e` is `let f := (x, y) ↦ e`.
    let first ← `(cas_term| $first:ident)
    let rest ← rest.getElems.mapM fun parameter => `(cas_term| $parameter:ident)
    defineFunction name (← `(cas_term| ($first:cas_term, $rest:cas_term,*))) value
  | `(cas_stmt| assert implemented $body:cas_term) =>
    return .implemented (← session.read body)
  | `(cas_stmt| assert $body:cas_term) =>
    match body with
    | `(cas_term| $_:cas_term ∈ $_:cas_term)
    | `(cas_term| $_:cas_term in $_:cas_term) => typingQuestion session body
    | `(cas_term| $_:cas_term ⊆ $_:cas_term)
    | `(cas_term| $_:cas_term and $_:cas_term) =>
      match ← settledJudgements? session body with
      | some values => return .settled values
      | none => return .question (← session.readQuestion body)
    | _ => return .question (← session.readQuestion body)
  | _ =>
    CasCatalogue.throwUnsupportedSource
      "source translation is not implemented for this statement form"

end CasCompiler
