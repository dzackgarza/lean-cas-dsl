module

public import CasCompiler.ReadExpression
public import CasCompiler.SourceProof
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
    return (⟨limit.row, limit.declaration, ← limit.cone.inContext context, limit.colimit,
      limit.category, ← limit.bundle.inContext context⟩ :
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
  | definition (session : SourceSession) (value : SourceTerm)
  | question (proposition : SourceTerm)
  | implemented (value : SourceTerm)
  | settled (values : Array SourceTerm)
  | assumption (session : SourceSession)
  | proved (proposition : SourceTerm) (proof : SourceTerm)
  | inspection (scope : SourceContextObservation)
  /-- Every child has already been read in its actual preceding lexical scope. The syntax
  is retained only for original item identity/span reporting, never runtime replay. -/
  | contextBlock (items : Array (TSyntax `cas_item × SourceStatement))

/-- The actual source-preflight result. A failed block retains its completed children,
the original failed child result and every remaining original item in order. `none` means
that item's source was not read; it carries no inferred judgement. The exception is the
reader's original exception, not a replacement interpretation or runtime outcome. -/
inductive SourceStatementRead where
  | complete (statement : SourceStatement)
  | failed (error : Exception)
      (items : Array (TSyntax `cas_item × Option SourceStatementRead))

/-- Original item syntax of a lexical block, shared by statement preparation and source
observation. These exact nodes retain question labels and original file positions. -/
def sourceContextItems? (statement : TSyntax `cas_stmt) : Option (Array (TSyntax `cas_item)) :=
  if statement.raw.isOfKind ``CasCatalogue.Language.casContextBlock then
    some (statement.raw[2].getArgs.map (⟨·⟩))
  else none

/-- The original statement node of one parsed item, without reading or rewriting it. -/
def sourceItemStatement? (item : TSyntax `cas_item) : Option (TSyntax `cas_stmt) :=
  match item with
  | `(cas_item| test $_:ident $_:str : $statement:cas_stmt)
  | `(cas_item| $statement:cas_stmt) => some statement
  | _ => none

/-- Read an asserted membership or annotation. Membership in a subset is a proposition; in an
object it is the element's reading there, whose success settles the question.
Source: mathematical-input contract §1; the original reader's settled typing judgements. -/
private def typingQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceStatement := do
  -- Retain the original selected category, carrier and cone of fresh values too.
  let term ← session.read stx
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

/-- A category spelling is selected before interpreting its arguments. A local binding
shadows a catalogue spelling, so ordinary subset membership keeps its existing meaning. -/
private partial def categoryApplication? (session : SourceSession) (source : TSyntax `cas_term) :
    TermElabM (Option (CasCatalogue.NamedCategoryEntry × Array (TSyntax `cas_term))) := do
  let (name, arguments) ← match source with
    | `(cas_term| ($inner:cas_term)) => return ← categoryApplication? session inner
    | `(cas_term| $name:ident) => pure (name, #[])
    | `(cas_term| $name:ident($arguments:cas_term,*)) => pure (name, arguments.getElems)
    | _ => return none
  if session.context.entries.any (·.userName == name.getId) then return none
  let spelling := name.getId.toString (escape := false)
  let state ← CasCatalogue.semanticState
  unless state.categories.any (·.name == spelling) do return none
  return some (← selectCategory state spelling, arguments)

/-- Seal only unresolved native universe levels after the complete actual application.
Existing context parameters remain rigid; no mathematical universe is defaulted to zero. -/
private def closeDeclarationUniverses (context : OpenContext) (values : Array Expr) :
    MetaM (Array Expr) := do
  let mut used : CollectLevelParams.State := {}
  for binding in context.bindings do
    let declaration ← binding.expression.fvarId!.getDecl
    used := used.collect declaration.type
    if let some value := declaration.value? then used := used.collect value
  for value in values do used := used.collect (← instantiateMVars value)
  for value in values do
    let generalized := (← getMCtx).levelMVarToParam used.params.contains (fun _ => false)
      (← instantiateMVars value) `sourceScopeUniverse
    setMCtx generalized.mctx
    used := used.collect generalized.expr
  let values ← values.mapM instantiateMVars
  if values.any (fun value => value.hasMVar || value.hasLevelMVar) then
    throwError "a source declaration requires its complete native category parameters"
  return values

private def categoryBundle (session : SourceSession) (context : OpenContext)
    (source : TSyntax `cas_term) (entry : CasCatalogue.NamedCategoryEntry)
    (arguments : Array (TSyntax `cas_term)) : TermElabM Expr := do
  discard <| checkedDeclaration entry.declaration
  let reader : ReadContext := ⟨sourceCategory session context, source, none, none, none,
    readProjection, fun categoryOf source expected qualification expectedCategory =>
      readExpressionApplicable categoryOf source expected qualification expectedCategory⟩
  let value ← SourceReader.application reader
    ⟨← mkConstWithFreshMVarLevels entry.declaration, none⟩ arguments none
  discard <| categoryIdentity value
  return value

private def abstractDeclaration (session : SourceSession) (name : Name)
    (domain : TSyntax `cas_term) : TermElabM SourceStatement := do
  if let some (entry, arguments) ← categoryApplication? session domain then
    let category ← session.elaborate domain fun context => do
      let bundle ← categoryBundle session context domain entry arguments
      let #[bundle] ← closeDeclarationUniverses context #[bundle]
        | throwError "the abstract category lost its native bundle"
      return bundle
    return .assumption (← session.assumeObject name entry.expression category)
  let type ← session.elaborate domain fun context => do
    let selected ← readExpression (sourceCategory session context) domain none
    let domain ← sourceCarrier selected
    discard <| getLevel domain.value
    return domain.value
  return .assumption (← session.assumeTerm name type)

/-- Unicode category-qualified definitions use the same selected catalogue judgement as
`in`. A non-category right side remains the original membership expression. -/
private def definedValue (session : SourceSession) (body : TSyntax `cas_term) :
    TermElabM SourceTerm := do
  let `(cas_term| $value:cas_term ∈ $domain:cas_term) := body | return ← session.read body
  let some (entry, arguments) ← categoryApplication? session domain
    | return ← session.read body
  let #[term] ← session.elaborateJudgements body fun context => do
    let bundle ← categoryBundle session context domain entry arguments
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    let selected : NativeSourceCategory := ⟨.object, entry.expression, bundle, none, none⟩
    let actual ← readExpression (sourceCategory session context) value (some carrier)
      (some entry.name) (some selected)
    let some category := actual.category
      | throwError "the defined object lost its explicitly selected category"
    unless category.role == .object && category.expression.syntacticEq entry.expression &&
        (← isDefEq category.bundle bundle) do
      throwError "the defined object has a different complete selected category"
    discard <| closeDeclarationUniverses context #[actual.value, category.bundle]
    return #[actual]
    | throwError "the defined object returned an invalid number of judgements"
  return term

/-- Read public statements through the checked source session, retaining actual let bindings.
Reuse: SourceSession.read/defineTerm and native expected-type checking. Source annotations
are read in the preceding scope; the new name is inserted only after its value is checked. -/
private def readStatementLeaf (session : SourceSession) (stx : TSyntax `cas_stmt) :
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
  | `(cas_stmt| let $name:ident ∈ $domain:cas_term)
  | `(cas_stmt| let $name:ident in $domain:cas_term) =>
    abstractDeclaration session name.getId domain
  | `(cas_stmt| assume $name:ident : $proposition:cas_term) =>
    let proposition ← session.readQuestion proposition
    return .assumption (← session.assumeTerm name.getId proposition)
  | `(cas_stmt| inspect assumptions) => return .inspection session.observation
  | `(cas_stmt| assert $body:cas_term using ($evidence:cas_term)) =>
    let proposition ← session.readQuestion body
    return .proved proposition (← session.proof evidence proposition.source)
  | `(cas_stmt| let $name:ident := $body:cas_term) =>
    let value ← definedValue session body
    return .definition (← session.defineWritten body name.getId value) value
  | `(cas_stmt| let $name:ident : $annotation:cas_term := $body:cas_term) =>
    let type ← session.read annotation
    type.source.withOpen fun _ expression => discard <| getLevel expression
    let value ← session.read body (some type.source)
    return .definition (← session.defineWritten annotation name.getId value) value
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

/-- The same reader retains successful source work when a later child fails. A block
advances only through its completed stored source sessions and stops at its first error;
no suffix is read, no source is replayed, and no child session escapes its lexical block. -/
private partial def readStatementCore (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatementRead := withRef stx do
  if let some children := sourceContextItems? stx then
    let mut current := session
    let mut items : Array (TSyntax `cas_item × SourceStatement) := #[]
    for item in children, index in [:children.size] do
      let result : SourceStatementRead ← try
          let some child := sourceItemStatement? item
            | throwError "a context block changed its original item syntax"
          readStatementCore current child
        catch error => pure (.failed error #[])
      match result with
      | .complete prepared =>
        items := items.push (item, prepared)
        match prepared with
        | .definition next _ | .assumption next => current := next
        | _ => pure ()
      | .failed error _ =>
        let prefix := items.map fun (item, statement) =>
          (item, some (SourceStatementRead.complete statement))
        let suffix : Array (TSyntax `cas_item × Option SourceStatementRead) :=
          (children.drop (index + 1)).map fun item => (item, none)
        return .failed error (prefix ++ #[(item, some result)] ++ suffix)
    return .complete (.contextBlock items)
  try
    return .complete (← readStatementLeaf session stx)
  catch error =>
    return .failed error #[]

/-- Read once and expose the actual completed prefix if source preflight fails. Consumers
may observe these original typed terms, but a failed result cannot enter execution. -/
opaque SourceSession.readStatementObserved (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatementRead := readStatementCore session stx

/-- Read one complete source statement before any computational cell is opened. Context
blocks retain typed children in order, including their original item labels and spans.
The ordinary API still throws the exact original error when any child fails. -/
opaque SourceSession.readStatement (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatement := do
  match ← session.readStatementObserved stx with
  | .complete statement => return statement
  | .failed error _ => throw error

end CasCompiler
