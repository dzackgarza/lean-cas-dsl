module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData
public import CasCompiler.SelectionScope
public import CasCatalogue.InterpretationFailure
public import Init.Control.StateCps

public import CasCompiler.Context
public import CasCompiler.LimitInterface
public import CasCompiler.CreationInterface
public import CasCompiler.Declaration
public import CasCompiler.NativeProof
public import CasCompiler.SourceReference
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










structure SourceReadScope where
  identities : CasRuntime.IdentitySupply
  context : OpenContext
  selections : SourceSelectionScope Expr
  formals : Array LocalBinding := #[]


abbrev SourceReadM := StateCpsT SourceReadScope TermElabM


def SourceReadM.withRef (reference : Syntax) (read : SourceReadM α) : SourceReadM α :=
  fun _ scope finish => do
    let previous ← getRef
    Lean.withRef reference <| read.runK scope fun value scope =>
      Lean.withRef previous (finish value scope)



def SourceReadM.tryCatch (read : SourceReadM α) (handler : Exception → SourceReadM α) :
    SourceReadM α := fun _ scope finish => do
  let completed ← liftM (m := IO) <| IO.mkRef false
  try read.runK scope fun value scope => do
    completed.set true
    finish value scope
  catch error =>
    if ← completed.get then throw error
    (handler error).runK scope finish

instance : MonadExceptOf Exception SourceReadM where
  throw error := liftM (m := TermElabM) (throw error)
  tryCatch := SourceReadM.tryCatch



def SourceReadM.inspect (read : SourceReadM Bool) : SourceReadM Bool :=
  fun _ scope finish => do
    let saved ← Term.saveState
    let result ← try read.runK scope fun value _ => pure value
      finally saved.restore (restoreInfo := true)
    finish result scope




def SourceReadM.chooseApplicable (readings : Array (SourceReadM (Except MessageData α)))
    (noneMessage ambiguityMessage : MessageData) (restoreInfo : Bool := false) :
    SourceReadM (Except MessageData α) :=
  fun _ initial finish => do
    let original ← Term.saveState
    let originalContext ← getLCtx
    let originalInstances ← getLocalInstances
    let completed ← liftM (m := IO) <| IO.mkRef false
    let rec rejectOthers (remaining : List (SourceReadM (Except MessageData α))) :
        TermElabM Unit := do
      match remaining with
      | [] => pure ()
      | reading :: rest =>
        original.restore (restoreInfo := restoreInfo)
        withLCtx originalContext originalInstances <|
          reading.runK initial fun result _ => do
            match result with
            | .error _ => rejectOthers rest
            | .ok _ => CasCatalogue.throwSemanticAmbiguity ambiguityMessage
    let rec choose (remaining : List (SourceReadM (Except MessageData α)))
        (mismatch : Option MessageData) : TermElabM _ := do
      original.restore (restoreInfo := restoreInfo)
      withLCtx originalContext originalInstances do
        match remaining with
        | [] =>
          completed.set true
          finish (.error (mismatch.getD noneMessage)) initial
        | reading :: rest =>
          reading.runK initial fun result selectedScope => do
            match result with
            | .error message =>
              choose rest (mismatch <|> some (← addMessageContext message))
            | .ok value =>
              let selected ← Term.saveState
              rejectOthers rest
              selected.restore (restoreInfo := restoreInfo)
              completed.set true
              finish (.ok value) selectedScope
    try choose readings.toList none
    catch error =>
      unless ← completed.get do original.restore (restoreInfo := restoreInfo)
      throw error



def SourceReadM.select (selection : SourceSelection Expr)
    (declaredType : Option Expr := none) : SourceReadM Expr :=
  fun _ scope finish => do
    let selection ← selection.abstract scope.formals
    let parameters ← scope.formals.filterM fun binding => do
      return !(← binding.expression.fvarId!.getDecl).isLet
    let declaredType ← declaredType.mapM fun type =>
      mkForallFVars (scope.formals.map (·.expression)) type (usedOnly := false)
    scope.selections.withBinding scope.identities scope.context selection
      (fun context selections value => do
        let value := mkAppN value (parameters.map (·.expression))
        check value
        finish value { scope with context, selections }) (declaredType := declaredType)



def SourceReadM.selection? (source : Expr) : SourceReadM (Option (SourceSelection Expr)) := do
  let scope ← get
  let some selection := scope.selections.findAt? scope.context source.getAppFn
    | do
      if let .fvar localId := source.getAppFn then
        if scope.context.bindings.any (fun binding =>
            binding.expression.fvarId! == localId && binding.role == .selectedStructure) then
          liftM (m := TermElabM) <| throwError (MessageData.tagged
            `CasCompiler.SourceReadM.missingSelection
            m!"the source lost its retained typed selection")
      return none
  let arguments := source.getAppArgs
  unless arguments.size == selection.formalBindings.size do return none
  return some (← selection.specialize arguments)




opaque SourceReadM.withBinder (name : Name) (type : Expr) (value : Option Expr)
    (binderInfo : BinderInfo) (close : LocalBinding → α → MetaM α)
    (body : Expr → SourceReadM α) : SourceReadM α :=
  fun _ outer finish => do
    let allocated ← outer.identities.fresh .sourceBinding
    let id : BindingId := ⟨allocated.worker, allocated.serial⟩
    let role ← if value.isSome then pure BindingRole.definition
      else if binderInfo == .instImplicit then pure BindingRole.instance
      else if ← isProp type then pure BindingRole.hypothesis else pure BindingRole.parameter
    let enter := fun expression => do
      let binding : LocalBinding := { id, role, expression }
      let context ← ContextTelescope.capture (outer.context.bindings.push binding)
      let selections ← match value with
        | none => pure outer.selections
        | some original =>
          match outer.selections.findAt? outer.context original.getAppFn with
          | none => pure outer.selections
          | some selected =>
            if original.getAppNumArgs != selected.formalBindings.size then pure outer.selections
            else do
              let selected ← selected.specialize original.getAppArgs
              pure (outer.selections.insert id { selected with value := original })
      let inner := { outer with context, selections, formals := outer.formals.push binding }
      (body expression).runK inner fun result scope => do
        unless scope.formals.size == outer.formals.size + 1 &&
            scope.formals.back?.any (·.id == id) do
          throwError "source binding changed its complete original formal telescope"
        let result ← close binding result
        let bindings := scope.context.bindings.filter (·.id != id)
        let declarations ← bindings.toList.mapM fun binding => binding.expression.fvarId!.getDecl
        let instances := (← getLocalInstances).filter (·.fvar != expression)
        withLCtx {} #[] <| withExistingLocalDecls declarations do
          withLCtx (← getLCtx) instances do
            let context ← ContextTelescope.capture bindings
            finish result { scope with
              context := context
              selections := scope.selections.erase id
              formals := outer.formals }
    match value with
    | some value => withLetDecl name type value enter
    | none => withLocalDecl name binderInfo type enter


def SourceReadM.withLambda (name : Name) (type : Expr) (binderInfo : BinderInfo)
    (body : Expr → SourceReadM Expr) : SourceReadM Expr :=
  SourceReadM.withBinder name type none binderInfo
    (fun parameter value => mkLambdaFVars #[parameter.expression] value) body


def SourceReadM.withLet (name : Name) (type value : Expr)
    (body : Expr → SourceReadM Expr) : SourceReadM Expr :=
  SourceReadM.withBinder name type (some value) .default
    (fun parameter value => mkLetFVars #[parameter.expression] value
      (usedLetOnly := false) (generalizeNondepLet := false)) body


structure NativeSourceJudgement where
  value : Expr
  category : Option NativeSourceCategory


structure SourceTerm where
  private mk ::
  source : ClosedTerm
  span : SourceSpan
  category : Option SourceCategoryBinding
  selections : SourceSelectionScope ClosedTerm := {}



structure SourceRingVariable where
  name : Name
  carrier : ClosedTerm
  index : Option Nat
  selections : SourceSelectionScope ClosedTerm := {}




structure SourceSession where
  private mk ::
  private identities : CasRuntime.IdentitySupply
  context : ContextTelescope
  spans : Array SourceSpan
  private categories : Array (Option SourceCategoryBinding)

  private rings : Array (Array SourceRingVariable)

  private descriptions : Array String
  selections : SourceSelectionScope ClosedTerm := {}



structure SourceContextObservation where
  private mk ::
  context : ContextTelescope
  spans : Array SourceSpan
  categories : Array (Option SourceCategoryBinding)
  rings : Array (Array SourceRingVariable)
  descriptions : Array String
  selections : SourceSelectionScope ClosedTerm := {}


def SourceSession.observation (session : SourceSession) : SourceContextObservation :=
  ⟨session.context, session.spans, session.categories, session.rings, session.descriptions,
    session.selections⟩

def SourceContextObservation.categoryFor (observation : SourceContextObservation)
    (id : BindingId) : Option SourceCategoryBinding := do
  let index ← observation.context.entries.findIdx? (·.id == id)
  observation.categories[index]?.bind fun category => category


def SourceContextObservation.ringsFor (observation : SourceContextObservation) (id : BindingId) :
    Array SourceRingVariable := Id.run do
  let some index := observation.context.entries.findIdx? (·.id == id) | return #[]
  return observation.rings[index]?.getD #[]



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



structure SourceConclusion where
  private mk ::
  terms : Array SourceTerm
  context : SourceContextObservation
  proof : Option SourceTerm := none



private def SourceSession.checkTermScope (session : SourceSession) (term : SourceTerm) :
    MetaM Unit := do
  let original := session.context
  let actual := term.source.context
  session.selections.checkRequired original
  term.selections.checkRequired actual
  let mut shared := 0
  for first in original.entries, second in actual.entries do
    if first.id != second.id then break
    unless first.role == second.role &&
        first.userName == second.userName && first.binderInfo == second.binderInfo &&
        first.kind == second.kind && first.nondep == second.nondep &&
        first.type.equal second.type do
      throwError "a retained source changed an original lexical declaration"
    match first.value, second.value with
    | none, none => pure ()
    | some first, some second =>
      unless first.equal second do throwError "a retained source changed an authored definition"
    | _, _ => throwError "a retained source changed an authored declaration kind"
    match first.originalSource, second.originalSource with
    | none, none => pure ()
    | some first, some second =>
      unless first.equal second do throwError "a retained source changed an original source"
    | _, _ => throwError "a retained source lost an original source correspondence"
    shared := shared + 1
  let sharedIds := (actual.entries.take shared).map (·.id)
  let instances := original.instances.filter (sharedIds.contains ·.binding)
  unless instances.size == actual.instances.size do
    throwError "a retained source changed its complete lexical instance selection"
  for first in instances, second in actual.instances do
    unless first.className == second.className && first.binding == second.binding do
      throwError "a retained source changed an original selected instance"
  for entry in actual.entries[shared:] do
    unless !(original.entries.any (·.id == entry.id)) &&
        entry.role == .selectedStructure && entry.value.isNone && entry.originalSource.isSome &&
        term.selections.contains entry.id do
      throwError "a retained source introduced an unselected lexical assumption"



opaque SourceSession.withTerm [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (session : SourceSession) (term : SourceTerm)
    (action : OpenContext → SourceSelectionScope Expr → Expr → m α) : m α :=
  controlAt MetaM fun run => do
    session.checkTermScope term
    session.context.withOpenContext fun context => do
      term.source.context.withInContext context fun context => do
        let selections ← SourceSelectionScope.merge (← session.selections.inContext context)
          (← term.selections.inContext context)
        checkSelectedSourceContext context selections
        for binding in context.bindings[session.context.entries.size:] do
          let some selected := selections[binding.id]?
            | throwError "a retained source lost a selected local"
          let some original := binding.originalSource
            | throwError "a retained source lost a selected local's original value"
          unless original.equal selected.value do
            throwError "a retained source changed a selected local's original value"
        run (action context selections (← term.source.inContext context))



opaque SourceSession.readTerm (session : SourceSession) (term : SourceTerm) :
    SourceReadM Expr := fun _ scope finish => do
  liftM (m := MetaM) <| session.checkTermScope term
  controlAt MetaM fun run =>
    term.source.context.withInContext scope.context fun context => do
      let selections ← SourceSelectionScope.merge scope.selections
        (← term.selections.inContext context)
      checkSelectedSourceContext context selections
      for entry in term.source.context.entries do
        if session.context.entries.any (·.id == entry.id) then continue
        let some binding := context.bindings.find? (·.id == entry.id)
          | throwError "a source operand lost an imported selected local"
        let some selected := selections[entry.id]?
          | throwError "a source operand lost its selected local data"
        let some original := binding.originalSource
          | throwError "a source operand lost its original selected value"
        unless original.equal selected.value do
          throwError "a source operand changed its original selected value"
      run (finish (← term.source.inContext context) { scope with context, selections })



opaque SourceSession.readClosed (session : SourceSession) (reference : Syntax)
    (source : ClosedTerm) (selections : SourceSelectionScope ClosedTerm := {}) :
    SourceReadM Expr := do
  let span ← liftM (m := CoreM) <| sourceSpan reference
  session.readTerm ⟨source, span, none, selections⟩


opaque SourceSession.conclusion (session : SourceSession) (terms : Array SourceTerm)
    (proof : Option SourceTerm := none) : MetaM SourceConclusion := do
  for term in terms ++ proof.toArray do
    session.withTerm term fun _ _ _ => pure ()
  if let some evidence := proof then
    let #[proposition] := terms
      | throwError "explicit evidence requires one retained proposition"
    session.withTerm proposition fun context _ proposition => do
      evidence.source.context.withInContext context fun context => do
        let evidence ← evidence.source.inContext context
        context.withOriginalSources #[proposition, ← inferType evidence] fun original => do
          unless (← isProp original[0]!) && (← isDefEq original[1]! original[0]!) do
            throwError "a retained proof has a different original proposition"
  return ⟨terms, session.observation, proof⟩


def SourceConclusion.inspectAssumptions (conclusion : SourceConclusion) : String :=
  conclusion.context.assumptionsText


def SourceSession.ringsFor (session : SourceSession) (id : BindingId) :
    Array SourceRingVariable := Id.run do
  let some index := session.context.entries.findIdx? (·.id == id) | return #[]
  return session.rings[index]?.getD #[]


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



opaque categoryIdentity (category : Expr) : MetaM Expr := do
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
  let categoryStructure ← mkAppM ``CategoryTheory.Bundled.str #[category]
  mkAppOptM ``CategoryTheory.Functor.id #[some carrier, some categoryStructure]



partial def sourceDomain (value : Expr) : MetaM Expr := do
  let value := (← instantiateMVars value).headBeta.consumeMData
  if let .fvar id := value then
    if let some definition := (← id.getDecl).value? then return ← sourceDomain definition
  return value




opaque SourceTerm.inCategory (term : SourceTerm) (expression : CasCatalogue.CategoryExpr)
    (category : SourceTerm) (role : SourceCategoryRole := .object)
    (selection : Option SourceCarrierSelection := none)
    (limit : Option SourceLimitSelection := none) : MetaM SourceTerm := do


  category.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    checkSelectedSourceContext context (← category.selections.inContext context)
  term.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    checkSelectedSourceContext context (← term.selections.inContext context)
    category.source.context.withInContext context fun context => do
      let selections ← SourceSelectionScope.merge (← term.selections.inContext context)
        (← category.selections.inContext context)
      checkSelectedSourceContext context selections
      let categoryValue ← category.source.inContext context
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[categoryValue]
      match role with
      | .object =>
        unless ← isDefEq (← inferType value) carrier do
          throwError "the source value does not inhabit its selected native category"
      | .morphism =>

        context.withOriginalSources #[categoryValue, value] fun original => do
          let identity ← categoryIdentity original[0]!
          discard <| withTransparency .all <|
            mkAppM ``CategoryTheory.Functor.map #[identity, original[1]!]
      return { term with
        source := ← context.close value
        selections := ← SourceSelectionScope.close selections context
        category := some ⟨expression, category.source, role, selection, limit⟩ }



private def SourceSession.freshBinding (session : SourceSession) : BaseIO BindingId := do
  let id ← session.identities.fresh .sourceBinding
  return ⟨id.worker, id.serial⟩

private def defineIn (session : SourceSession) (context : OpenContext) (name : Name)
    (expression : Expr) (span : SourceSpan) (category : Option SourceCategoryBinding)
    (openSelections : MetaM (SourceSelectionScope Expr)) : MetaM SourceSession := do
  let type ← inferType expression
  let id ← session.freshBinding
  let selections ← openSelections
  let selected := selections.findAt? context expression


  let added := context.bindings.size - session.context.entries.size
  withLetDecl name type expression fun expression => do
    let context ← ContextTelescope.capture
      (context.bindings.push { id, role := .definition, expression })
    let selections := match selected with
      | some selected => selections.insert id selected
      | none => selections
    return ⟨session.identities, context.telescope,
      (session.spans ++ Array.replicate added span).push span,
      (session.categories ++ Array.replicate added none).push category,
      (session.rings ++ Array.replicate added #[]).push #[],
      (session.descriptions ++ Array.replicate added "").push "",
      ← SourceSelectionScope.close selections context⟩

opaque SourceSession.empty (identities : CasRuntime.IdentitySupply) : MetaM SourceSession := do
  let context ← withLCtx {} #[] <| ContextTelescope.capture #[]
  return ⟨identities, context.telescope, #[], #[], #[], #[], {}⟩




private def checkSource (source : ClosedTerm) : MetaM Unit := do
  let constants := source.expression.getUsedConstants ++ source.type.getUsedConstants
  for declaration in constants do
    discard <| checkedDeclaration declaration




opaque SourceSession.elaborateJudgementsScoped (session : SourceSession) (reference : Syntax)
    (build : SourceReadM (Array NativeSourceJudgement)) :
    TermElabM (Array SourceTerm) :=
  withRef reference <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.selections.checkRequired session.context
    session.context.withOpenContext fun context => do
      let selections ← session.selections.inContext context
      let initial : SourceReadScope := { identities := session.identities, context, selections }
      checkSelectedSourceContext context selections
      withSynthesize <| build.runK initial fun expressions scope => do
        unless scope.formals.isEmpty do
          throwError "source construction left an original formal parameter unclosed"
        synthesizeSyntheticMVars (postpone := .no)
        let context := scope.context
        checkSelectedSourceContext context scope.selections
        context.withClosing checkSource fun closeChecked => do
          let selections ← SourceSelectionScope.mapM (fun value => do
            closeChecked (← instantiateMVars value)) scope.selections
          let span ← sourceSpan reference
          expressions.mapM fun judgement => do
            let expression ← instantiateMVars judgement.value
            let source ← closeChecked (← instantiateMVars expression)
            let term : SourceTerm := ⟨source, span, session.categoryOf context expression, selections⟩
            match judgement.category with
            | none => return term
            | some selected =>
              let category ← closeChecked (← instantiateMVars selected.bundle)
              let selection ← selected.carrier.mapM fun carrier => do
                let close := fun action => do
                  closeChecked (← instantiateMVars action)
                let actions ← carrier.actions.mapM close
                let comparisons ← carrier.comparisons.mapM close
                return (⟨carrier.refs, carrier.target, carrier.identifications, actions, comparisons⟩ :
                  SourceCarrierSelection)
              let limit ← selected.limit.mapM fun limit => do
                let close : Expr → TermElabM ClosedTerm := fun value => do
                  closeChecked (← instantiateMVars value)
                let cone ← close limit.cone
                let bundle ← close limit.bundle
                let presentation ← close limit.presentation
                let diagram ← close limit.diagram
                let interface ← limit.interface.mapM close
                return (⟨limit.row, limit.declaration, cone, limit.colimit, limit.category, bundle,
                  presentation, diagram, interface, limit.construction,
                  ← limit.ownerFamily.mapM close,
                  ← limit.creation.mapM (fun creation => creation.mapM close),
                  ← limit.creationFamily.mapM close, limit.creationInputs⟩ : SourceLimitSelection)
              term.inCategory selected.expression ⟨category, span, none, selections⟩ selected.role selection limit





opaque SourceReadM.elaborateNative (reference : Syntax) (build : SourceReadM Expr) :
    TermElabM Expr :=
  Lean.withRef reference <| withoutErrToSorry <| withoutAutoBoundImplicit do
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let ambientContext ← getLCtx
    let ambientInstances ← getLocalInstances
    let declarations := ambientContext.foldl (fun result declaration =>
      result.push declaration) #[]
    let mut bindings : Array LocalBinding := #[]
    let mut arguments : Array Expr := #[]
    for declaration in declarations do
      let allocated ← liftM (m := BaseIO) <| identities.fresh .sourceBinding
      let role ← if declaration.isLet then pure BindingRole.definition
        else if declaration.binderInfo == .instImplicit then pure BindingRole.instance
        else if ← isProp declaration.type then pure BindingRole.hypothesis
        else pure BindingRole.parameter
      let expression := mkFVar declaration.fvarId
      bindings := bindings.push {
        id := ⟨allocated.worker, allocated.serial⟩, role, expression }
      unless declaration.isLet do arguments := arguments.push expression
    let context ← ContextTelescope.capture bindings
    withSynthesize <| build.runK { identities, context, selections := {} }
        fun expression scope => do
      unless scope.formals.isEmpty do
        throwError "source quotation left an original formal parameter unclosed"
      synthesizeSyntheticMVars (postpone := .no)
      checkSelectedSourceContext scope.context scope.selections
      discard <| SourceSelectionScope.mapM (fun value => do
        let source ← scope.context.close (← instantiateMVars value)
        checkSource source
        return source) scope.selections
      let expression ← instantiateMVars expression
      checkSource (← scope.context.close expression)
      let function ← scope.context.withOriginalSources #[expression] fun expressions => do
        let locals := (← getLCtx).foldl (fun result declaration =>
          result.push (mkFVar declaration.fvarId)) #[]
        unless locals.size == scope.context.bindings.size do
          throwError "source quotation changed its complete native telescope"
        let function ← mkLambdaFVars locals expressions[0]!
          (usedOnly := false) (usedLetOnly := false)
        checkWithKernel function
        return function
      let expression := mkAppN function arguments
      if (expression.find? (fun
          | .fvar id => !declarations.any (·.fvarId == id)
          | _ => false)).isSome then
        throwError "source quotation contains an escaping selected local"
      withLCtx ambientContext ambientInstances do
        checkWithKernel expression
        return expression


opaque SourceSession.elaborateScoped (session : SourceSession) (reference : Syntax)
    (build : SourceReadM Expr) : TermElabM SourceTerm := do
  let #[term] ← session.elaborateJudgementsScoped reference do
      return #[⟨← build, none⟩]
    | throwError "source formation returned an invalid number of expressions"
  return term


opaque SourceSession.elaborateJudgements (session : SourceSession) (reference : Syntax)
    (build : OpenContext → TermElabM (Array NativeSourceJudgement)) :
    TermElabM (Array SourceTerm) :=
  session.elaborateJudgementsScoped reference do
    let scope ← get
    liftM (build scope.context)


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




opaque SourceSession.term (session : SourceSession) (stx : Term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  session.elaborate stx fun context => do
    let expected ← expected.mapM (·.inContext context)
    elabTermEnsuringType stx expected



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


opaque SourceSession.proposition (session : SourceSession) (stx : Term) :
    TermElabM SourceTerm := withRef stx do
  let term ← session.term stx
  term.source.withOpen fun _ expression => do
    unless ← isProp expression do throwError "a source proposition must have type Prop"
  return term



def sourceFormalProof (evidence : Term) (proposition : Expr) : TermElabM Expr :=
  withRef evidence do
    unless ← isProp proposition do
      throwError "a formal proof requires a source proposition"
    completeNativeProof proposition <| withSynthesize do
      let proof ← elabTerm evidence (some proposition)
      if ← isDefEq (← inferType proof) proposition then return proof



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

        ensureHasType (some proposition) proof


private def SourceSession.retainContext (session : SourceSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (span : SourceSpan) : MetaM SourceSession := do
  let added := context.bindings.size - session.context.entries.size
  return { session with
    context := context.telescope
    spans := session.spans ++ Array.replicate added span
    categories := session.categories ++ Array.replicate added none
    rings := session.rings ++ Array.replicate added #[]
    descriptions := session.descriptions ++ Array.replicate added ""
    selections := ← SourceSelectionScope.close selections context }

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
      session.descriptions.push description, session.selections⟩



opaque SourceSession.assume (session : SourceSession) (name : Name) (stx : Term)
    (binderInfo : BinderInfo := .default) : TermElabM SourceSession :=
  withRef stx <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpenContext fun context => do
      let type ← instantiateMVars (← withSynthesize <| elabType stx)
      let source ← context.close type
      checkSource source
      assumeIn session context name type (← sourceSpan stx) binderInfo



opaque SourceSession.assumeTerm (session : SourceSession) (name : Name) (type : SourceTerm)
    (binderInfo : BinderInfo := .default) : MetaM SourceSession :=
  session.withTerm type fun context selections value => do
    let session ← session.retainContext context selections type.span
    assumeIn session context name value type.span binderInfo



opaque SourceSession.assumeObject (session : SourceSession) (name : Name)
    (expression : CasCatalogue.CategoryExpr) (category : SourceTerm) : MetaM SourceSession :=
  session.withTerm category fun context selections bundle => do
    let session ← session.retainContext context selections category.span
    discard <| categoryIdentity bundle
    let type ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    let source ← context.close type
    checkSource source
    assumeIn session context name type category.span .default
      (some ⟨expression, category.source, .object, none, none⟩)



opaque SourceSession.define (session : SourceSession) (name : Name) (stx : Term)
    (annotation : Option Term := none) : TermElabM SourceSession :=
  withRef stx <| withoutErrToSorry <| withoutAutoBoundImplicit do
    session.context.withOpenContext fun context => do
      let expected ← annotation.mapM fun stx => withSynthesize <| elabType stx
      let expression ← instantiateMVars (← withSynthesize <| elabTermEnsuringType stx expected)
      let source ← context.close expression
      checkSource source
      defineIn session context name expression (← sourceSpan stx)
        (session.categoryOf context expression) (session.selections.inContext context)



opaque SourceSession.defineTerm (session : SourceSession) (name : Name) (term : SourceTerm) :
    MetaM SourceSession :=
  session.withTerm term fun context selections value => do
    defineIn session context name value term.span term.category (pure selections)



opaque SourceSession.apply (session : SourceSession) (reference : Syntax) (function : SourceTerm)
    (arguments : Array SourceTerm) : TermElabM SourceTerm :=
  session.elaborateScoped reference do
    discard <| session.readTerm function
    for argument in arguments do discard <| session.readTerm argument
    let context := (← get).context
    context.apply function.source (arguments.map (·.source))

private def SourceCategoryBinding.ensureDeclarations (category : SourceCategoryBinding) :
    MetaM Unit := do
  category.bundle.ensureDeclarations
  if let some carrier := category.carrier then
    for action in carrier.actions ++ carrier.comparisons do action.ensureDeclarations
  if let some limit := category.limit then
    for term in #[limit.cone, limit.bundle, limit.presentation, limit.diagram,
        limit.interface.presentation, limit.interface.diagram] ++
        limit.interface.standardization.toArray ++ limit.interface.dataConstructor.toArray ++
        limit.ownerFamily.toArray ++ limit.creation.toArray.flatMap (·.terms) ++
        limit.creationFamily.toArray do
      term.ensureDeclarations


opaque SourceTerm.ensureDeclarations (term : SourceTerm) : MetaM Unit := do
  term.source.ensureDeclarations
  discard <| SourceSelectionScope.mapM (fun source => do
    source.ensureDeclarations
    pure source) term.selections
  if let some category := term.category then category.ensureDeclarations


opaque SourceContextObservation.ensureDeclarations (context : SourceContextObservation) :
    MetaM Unit := do
  context.context.ensureDeclarations
  discard <| SourceSelectionScope.mapM (fun source => do
    source.ensureDeclarations
    pure source) context.selections
  for category in context.categories do
    if let some category := category then category.ensureDeclarations
  for rings in context.rings do
    for ring in rings do
      ring.carrier.ensureDeclarations
      discard <| SourceSelectionScope.mapM (fun source => do
        source.ensureDeclarations
        pure source) ring.selections

def SourceSession.ensureDeclarations (session : SourceSession) : MetaM Unit := do
  session.observation.ensureDeclarations
  for ringVariables in session.rings do
    for ringVariable in ringVariables do
      ringVariable.carrier.ensureDeclarations
      discard <| SourceSelectionScope.mapM (fun source => do
        source.ensureDeclarations
        pure source) ringVariable.selections



def SourceConclusion.ensureDeclarations (conclusion : SourceConclusion) : MetaM Unit := do
  conclusion.context.ensureDeclarations
  for term in conclusion.terms ++ conclusion.proof.toArray do term.ensureDeclarations

end CasCompiler
