module

public import CasCompiler.Elaborate
public import CasCompiler.SourceReference
public import Lean.Meta.Transform

public section

namespace CasCompiler.SourceTest

open Lean Meta Elab Term

/-- Run assertions inside the original completed term's complete native/typed scope.
The callback returns no local expression, so test inspection cannot escape its telescope. -/
def checkSelected (term : SourceTerm) (assertions : Expr → SourceReadM Unit) :
    TermElabM Unit := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  term.source.ensureDeclarations
  term.source.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let expression ← term.source.inContext context
    let selections ← term.selections.inContext context
    (assertions expression).runK { identities, context, selections } fun _ _ => pure ()

/-- Interpret original sources only for mathematical assertions. Exact original operands
are checked separately in the typed scope; this view supplies no compiler selection. -/
def checkOriginal (expressions : Array Expr) (assertions : Array Expr → MetaM Unit) :
    SourceReadM Unit := do
  let scope ← get
  scope.context.withOriginalSources expressions fun expressions => do
    let letIds := (← getLCtx).foldl (fun ids declaration =>
      if declaration.isLet then ids.push declaration.fvarId else ids) #[]
    assertions (← expressions.mapM fun expression => zetaDeltaFVars expression letIds)

/-- Verify a specified original binder through explicit typed aliases or authored native
lets. Equal native values and originalSource checking correspondences are never consulted. -/
partial def originatesAt (context : OpenContext) (selections : SourceSelectionScope Expr)
    (source expected : Expr) (throughAuthoredLets : Bool := true) : MetaM Bool := do
  if source.equal expected then return true
  let beta := source.headBeta
  if !beta.equal source then
    return ← originatesAt context selections beta expected throughAuthoredLets
  if let .letE _ _ value body _ := source then
    return ← originatesAt context selections (body.instantiate1 value) expected throughAuthoredLets
  if !throughAuthoredLets && source.getAppFn.isFVar then
    let some binding := context.bindings.find? (·.expression.equal source.getAppFn)
      | return false
    if binding.role != .selectedStructure then return false
  if let some selected := selections.findAt? context source.getAppFn then
    unless selected.formalBindings.size == source.getAppNumArgs do return false
    let selected ← selected.specialize source.getAppArgs
    if selected.value.equal source then return false
    return ← originatesAt context selections selected.value expected throughAuthoredLets
  if let .fvar localId := source then
    if let some value := (← localId.getDecl).value? then
      return ← originatesAt context selections value expected throughAuthoredLets
  if let .mdata _ body := source then
    return ← originatesAt context selections body expected throughAuthoredLets
  return false

/-- Inspect only explicitly selected applications reachable along a result's native data
and typed value aliases. A matching original record supplies its own complete application;
its declared reference exposes only its own lexical formal telescope. There is no registry
lookup, expression-head search, or selection from an equal carrier. -/
partial def declaredApplications (context : OpenContext) (selections : SourceSelectionScope Expr)
    (declaration : Name) (source : Expr) : MetaM (Array Expr) := do
  if let some selected := selections.findAt? context source.getAppFn then
    if selected.formalBindings.size == source.getAppNumArgs then
      let selected ← selected.specialize source.getAppArgs
      let owns := selected.reference.bind (·.declaration) == some declaration ||
        (selected.application.any fun application => match application.family with
          | .objectAction family => family.declaration == declaration
          | .point family => family.declaration == declaration
          | _ => false)
      if owns then
        let original ← if selected.reference.bind (·.declaration) == some declaration then
          sourceApplication? declaration selected
        else pure selected.originalApplication
        let some original := original
          | throwError "the selected test application lost its original complete native table"
        return #[original]
      if selected.value.equal source then return #[]
      return ← declaredApplications context selections declaration selected.value
  match source with
  | .fvar localId =>
    match (← localId.getDecl).value? with
    | some value => declaredApplications context selections declaration value
    | none => pure #[]
  | .app function argument =>
    return (← declaredApplications context selections declaration function) ++
      (← declaredApplications context selections declaration argument)
  | .letE _ _ value body _ =>
    declaredApplications context selections declaration (body.instantiate1 value)
  | .proj _ _ parent | .mdata _ parent =>
    declaredApplications context selections declaration parent
  | _ => pure #[]

/-- Visit actual native data through explicit typed value aliases. The assertion callback
can inspect an ordinary native constructor without unfolding any registered declaration. -/
partial def visitNativeData (assertion : Expr → SourceReadM Bool) (source : Expr)
    (throughAuthoredLets : Bool := true) :
    SourceReadM Nat := do
  if ← assertion source then return 1
  let followSelection ← if !throughAuthoredLets && source.getAppFn.isFVar then do
    let scope ← get
    let some binding := scope.context.bindings.find? (·.expression.equal source.getAppFn)
      | pure false
    pure (binding.role == .selectedStructure)
  else pure true
  if followSelection then
    if let some selected ← SourceReadM.selection? source then
      if selected.value.equal source then return 0
      return ← visitNativeData assertion selected.value throughAuthoredLets
  match source with
  | .fvar localId =>
    if !throughAuthoredLets then pure 0
    else match (← localId.getDecl).value? with
      | some value => visitNativeData assertion value throughAuthoredLets
      | none => pure 0
  | .app function argument =>
    let first ← visitNativeData assertion function throughAuthoredLets
    let second ← visitNativeData assertion argument throughAuthoredLets
    return first + second
  | .letE _ _ value body _ =>
    visitNativeData assertion (body.instantiate1 value) throughAuthoredLets
  | .proj _ _ parent | .mdata _ parent =>
    visitNativeData assertion parent throughAuthoredLets
  | .lam name type body binderInfo | .forallE name type body binderInfo => do
    let inType ← visitNativeData assertion type throughAuthoredLets
    let inBody ← SourceReadM.withBinder name type none binderInfo
      (fun _ count => pure count) fun parameter =>
        visitNativeData assertion (body.instantiate1 parameter) throughAuthoredLets
    return inType + inBody
  | _ => pure 0

/-- The added typed source locals cannot stand in for authored assumptions or definitions. -/
def authoredEntries {term : Type} (context : ContextTelescope) (selections : SourceSelectionScope term) :
    MetaM (Array ContextEntry) := do
  let mut authored := #[]
  for entry in context.entries do
    if entry.role == .selectedStructure then
      unless entry.originalSource.isSome && entry.value.isNone && selections.contains entry.id do
        throwError "a selected test local changed its original source-binding contract"
    else
      unless entry.originalSource.isNone do
        throwError "an authored test local acquired a selected-source checking correspondence"
      authored := authored.push entry
  return authored

/-- Name the original authored positions inside the unchanged complete test scope. -/
def authoredBindings : SourceReadM (Array LocalBinding) := do
  let scope ← get
  let entries ← authoredEntries scope.context.telescope scope.selections
  entries.mapM fun entry => do
    let some binding := scope.context.bindings.find? (·.id == entry.id)
      | liftM (m := MetaM) <| throwError "an authored test binding is outside its complete original context"
    return binding

/-- Inspect the native value behind only exact typed selection aliases. This preserves
top-level shape assertions without searching subterms or unfolding authored native lets. -/
partial def selectedValue (source : Expr) : SourceReadM Expr := do
  let some selected ← SourceReadM.selection? source | return source
  if selected.value.equal source then return source
  selectedValue selected.value

end CasCompiler.SourceTest
