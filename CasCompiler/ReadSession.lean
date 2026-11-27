module

public import CasCompiler.ReadExpression
public import CasCompiler.SourceProof
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

def SourceSession.openCategory (session : SourceSession) (context : OpenContext)
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
      limit.category, ← limit.bundle.inContext context,
      ← limit.presentation.inContext context, ← limit.diagram.inContext context,
      ← limit.interface.mapM (·.inContext context), limit.construction,
      ← limit.ownerFamily.mapM (·.inContext context),
      ← limit.creation.mapM (fun creation => creation.mapM (·.inContext context)),
      ← limit.creationFamily.mapM (·.inContext context), limit.creationInputs⟩ :
        NativeSourceLimitSelection)
  return some ⟨category.role, category.expression, ← category.bundle.inContext context,
    carrier, limit⟩


private def recordedRings (session : SourceSession) (stx : Syntax) :
    SourceReadM (Array (Name × Expr × Option Nat)) := do
  let context := (← get).context
  let mut found := #[]
  for binding in context.bindings do
    unless sourceUses (← binding.expression.fvarId!.getUserName) stx do continue
    for ring in session.ringsFor binding.id do
      found := found.push (ring.name, ← session.readClosed stx ring.carrier ring.selections, ring.index)
  return found



private def writtenRings (session : SourceSession) (stx : Syntax) :
    TermElabM (Array SourceRingVariable) := do
  let mut found := #[]
  for (name, ring, index) in sourceRingVariables stx do
    if found.any (fun (written : SourceRingVariable) => written.name == name) then continue
    let carrier ← session.elaborateScoped ring do
      let context := (← get).context
      let object ← readExpression (session.openCategory context) ⟨ring⟩ none
      return (← sourceCarrier object).value
    found := found.push ⟨name, carrier.source, index, carrier.selections⟩
  return found


private def SourceSession.defineWritten (session : SourceSession) (stx : Syntax) (name : Name)
    (value : SourceTerm) : TermElabM SourceSession := do
  let rings ← writtenRings session stx
  return (← session.defineTerm name value).recordRings rings

private def SourceSession.readAt (session : SourceSession) (reference : Syntax)
    (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none)
    (expectedSelections : SourceSelectionScope ClosedTerm := {}) : TermElabM SourceTerm := do
  let #[term] ← session.elaborateJudgementsScoped reference do
    let expected ← expected.mapM (session.readClosed reference · expectedSelections)
    let rings ← recordedRings session stx
    let context := (← get).context
    return #[← readSourceTerm (session.openCategory context) rings stx expected]
    | throwError "source reading returned an invalid number of judgements"
  return term



opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none)
    (expectedSelections : SourceSelectionScope ClosedTerm := {}) : TermElabM SourceTerm :=
  session.readAt stx stx expected expectedSelections




private partial def questionExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (stx : TSyntax `cas_term) : SourceReadM Expr := SourceReadM.withRef stx do
  match stx with
  | `(cas_term| ($body:cas_term)) => questionExpression categoryOf body
  | `(cas_term| $left:cas_term and $right:cas_term) =>
    mkAppM ``And #[← questionExpression categoryOf left, ← questionExpression categoryOf right]
  | `(cas_term| $left:cas_term = $right:cas_term)
  | `(cas_term| $left:cas_term is $right:cas_term) => sourceEquation categoryOf left right
  | _ =>
    let value ← readExpression categoryOf stx (some (mkSort .zero))
    unless ← isProp value.value do liftM (m := TermElabM) <| throwError "a source question must be a proposition"
    return value.value




opaque SourceSession.readQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceTerm :=
  session.elaborateScoped stx do
    let rings ← recordedRings session stx
    let categoryOf := session.openCategory (← get).context
    return (← withRingVariables categoryOf rings stx do
      return ⟨← questionExpression categoryOf stx, none⟩).value




inductive SourceStatement where
  | definition (session : SourceSession) (value : SourceTerm)
  | question (proposition : SourceTerm)
  | implemented (value : SourceTerm)
  | settled (values : Array SourceTerm)
  | assumption (session : SourceSession)
  | proved (proposition : SourceTerm) (proof : SourceTerm)
  | inspection (scope : SourceContextObservation)


  | contextBlock (items : Array (TSyntax `cas_item × SourceStatement))





inductive SourceStatementRead where
  | complete (statement : SourceStatement)
  | failed (error : Exception)
      (items : Array (TSyntax `cas_item × Option SourceStatementRead))



def sourceContextItems? (statement : TSyntax `cas_stmt) : Option (Array (TSyntax `cas_item)) :=
  if statement.raw.isOfKind ``CasCatalogue.Language.casContextBlock then
    some (statement.raw[2].getArgs.map (⟨·⟩))
  else none


def sourceItemStatement? (item : TSyntax `cas_item) : Option (TSyntax `cas_stmt) :=
  match item with
  | `(cas_item| test $_:ident $_:str : $statement:cas_stmt)
  | `(cas_item| $statement:cas_stmt) => some statement
  | _ => none




private def typingQuestion (session : SourceSession) (stx : TSyntax `cas_term) :
    TermElabM SourceStatement := do

  let term ← session.read stx
  let proposition ← term.source.withOpen fun _ expression => isProp expression
  return if proposition then .question term else .settled #[term]





private def inclusionJudgement? (session : SourceSession) (stx left right : TSyntax `cas_term) :
    TermElabM (Option SourceTerm) := do
  try
    return some (← session.elaborateScoped stx do
      let rings ← recordedRings session stx
      let categoryOf := session.openCategory (← get).context
      let source ← readSourceTerm categoryOf rings left none
      let target ← readSourceTerm categoryOf rings right none
      unless source.category.any (·.role == .object) && target.category.any (·.role == .object) do
        throwReadRuleMismatch
      unless (← whnfR (← inferType source.value)).isSort &&
          (← whnfR (← inferType target.value)).isSort do
        throwReadRuleMismatch
      SourceReadM.withLambda `x source.value .default fun element => do
        let some included ← sourceCoercion? element target.value
          | liftM (m := TermElabM) <| CasCatalogue.throwStratum .invalid
              m!"no chain of registered inclusions gives {left} ⊆ {right}"
        return included)
  catch error =>
    match error with
    | .internal id _ => if id == readRuleMismatch then return none else throw error
    | _ => throw error




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
    (arguments : Array (TSyntax `cas_term)) : SourceReadM Expr := do
  discard <| checkedDeclaration entry.declaration
  let reader : ReadContext := ⟨session.openCategory context, source, none, none, none,
    readProjection, fun categoryOf source expected qualification expectedCategory =>
      readExpressionApplicable categoryOf source expected qualification expectedCategory⟩
  let value ← SourceReader.application reader
    ⟨← mkConstWithFreshMVarLevels entry.declaration, none⟩ arguments none
  discard <| categoryIdentity value
  discard <| SourceReadM.select (← sourceReferenceAt (.category entry) value value)
  return value

private def abstractDeclaration (session : SourceSession) (name : Name)
    (domain : TSyntax `cas_term) : TermElabM SourceStatement := do
  if let some (entry, arguments) ← categoryApplication? session domain then
    let category ← session.elaborateScoped domain do
      let context := (← get).context
      let bundle ← categoryBundle session context domain entry arguments
      let #[bundle] ← closeDeclarationUniverses (← get).context #[bundle]
        | liftM (m := TermElabM) <| throwError "the abstract category lost its native bundle"
      return bundle
    return .assumption (← session.assumeObject name entry.expression category)
  let type ← session.elaborateScoped domain do
    let context := (← get).context
    let selected ← readExpression (session.openCategory context) domain none
    let domain ← sourceCarrier selected
    discard <| getLevel domain.value
    return domain.value
  return .assumption (← session.assumeTerm name type)



private def definedValue (session : SourceSession) (body : TSyntax `cas_term) :
    TermElabM SourceTerm := do

  let mut qualification := body
  while true do
    let `(cas_term| ($inner:cas_term)) := qualification | break
    qualification := inner
  let `(cas_term| $value:cas_term ∈ $domain:cas_term) := qualification
    | return ← session.read body
  let some (entry, arguments) ← categoryApplication? session domain
    | return ← session.read body
  let #[term] ← session.elaborateJudgementsScoped body do
    let context := (← get).context
    let bundle ← categoryBundle session context domain entry arguments
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    let selected : NativeSourceCategory := ⟨.object, entry.expression, bundle, none, none⟩
    let actual ← readExpression (session.openCategory context) value (some carrier)
      (some entry.name) (some selected)
    let some category := actual.category
      | liftM (m := TermElabM) <| throwError "the defined object lost its explicitly selected category"
    unless category.role == .object && category.expression.syntacticEq entry.expression &&
        (← isDefEq category.bundle bundle) do
      liftM (m := TermElabM) <| throwError "the defined object has a different complete selected category"
    discard <| closeDeclarationUniverses (← get).context #[actual.value, category.bundle]
    return #[actual]
    | throwError "the defined object returned an invalid number of judgements"
  return term




private def readStatementLeaf (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatement := withRef stx do


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
    return .proved proposition (← session.proof evidence proposition.source proposition.selections)
  | `(cas_stmt| let $name:ident := $body:cas_term) =>
    let value ← definedValue session body
    return .definition (← session.defineWritten body name.getId value) value
  | `(cas_stmt| let $name:ident : $annotation:cas_term := $body:cas_term) =>
    let type ← session.read annotation
    type.source.withOpen fun _ expression => discard <| getLevel expression
    let value ← session.read body (some type.source) type.selections
    return .definition (← session.defineWritten annotation name.getId value) value
  | `(cas_stmt| let $name:ident($parameter:cas_term) := $value:cas_term) =>
    defineFunction name parameter value
  | `(cas_stmt| let $name:ident($first:ident, $rest:ident,*) := $value:cas_term) =>

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
        let completedItems := items.map fun (item, statement) =>
          (item, some (SourceStatementRead.complete statement))
        let suffix : Array (TSyntax `cas_item × Option SourceStatementRead) :=
          (children.drop (index + 1)).map fun item => (item, none)
        return .failed error (completedItems ++ #[(item, some result)] ++ suffix)
    return .complete (.contextBlock items)
  try
    return .complete (← readStatementLeaf session stx)
  catch error =>
    return .failed error #[]



opaque SourceSession.readStatementObserved (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatementRead := readStatementCore session stx




opaque SourceSession.readStatement (session : SourceSession) (stx : TSyntax `cas_stmt) :
    TermElabM SourceStatement := do
  match ← session.readStatementObserved stx with
  | .complete statement => return statement
  | .failed error _ => throw error

end CasCompiler
