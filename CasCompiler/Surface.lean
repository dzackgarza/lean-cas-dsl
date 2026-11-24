module

public import CasCompiler.Elaborate
public import CasCompiler.Layout
public import CasCompiler.SelectedMorphism
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Semantics.Foundation.Catalogue
public import CasCatalogue.InterpretationFailure
public import CasContract.Failure
public import Lean.Meta.Structure
import Lean.Elab.App

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The function of the actual set map, using its fixed native category structure.
Reuse: Mathlib.CategoryTheory.Category.Types.Basic, TypeCat.Hom.hom and Fun.toFun. -/
def sourceSetFunction (value : Expr) : MetaM Expr := do
  let function ← mkAppM ``TypeCat.Hom.hom #[value]
  mkAppM ``TypeCat.Fun.toFun #[function]

/-- Expose the native constructor fields of undetermined structure parameters.
Reuse: the selected receiver rule and Lean's checked structure constructors. The complete
source type must determine these fields; this operation does not synthesize instances. -/
def expandSourceStructures (parameters : Array Expr) : MetaM Bool := do
  for parameter in parameters do
    let parameter ← instantiateMVars parameter
    unless parameter.isMVar do continue
    let type ← whnfR (← inferType parameter)
    let some name := type.getAppFn.constName? | continue
    unless isStructure (← getEnv) name do continue
    let .inductInfo info ← getConstInfo name | continue
    let [constructor] := info.ctors | continue
    discard <| checkedDeclaration constructor
    let constructor ← mkConstWithFreshMVarLevels constructor
    let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
    unless ← isDefEq result type do return false
    unless ← isDefEq parameter (mkAppN constructor fields) do return false
  return true

/-- Locate the exact registered source domains through original native definitions. -/
def registeredDomain (value : Expr) : MetaM (Expr × Array ObjectEntry) := do
  let state ← semanticState
  let domain ← sourceDomain value
  let reference ← sourceObjectReference? value
  let owners := state.objects.filter fun entry => match reference with
    | some (id, declaration) => entry.id == id && entry.declaration == declaration
    | none => domain.getAppFn.constName? == some entry.declaration
  if reference.isSome && owners.isEmpty then
    throwError "the source domain reference is unavailable in the source inventory"
  return (domain, owners)

/-- Follow a let only when its own source selects an earlier input or native field.
Independently computed lets retain their different fvar identities, even when their
definitions are convertible. This is the same alias rule as runtime dependency admission. -/
private partial def sourceArgumentReference (inputs : Array Expr) (source : Expr)
    (path : Array Name := #[]) : MetaM (Option (Nat × Array Name)) := do
  let some (index, selected) ← sourceInputProjection? source inputs path | return none
  let some input := inputs[index]?
    | throwError "a source argument selected an unavailable original input"
  if let some definition := (← getFVarLocalDecl input).value? then
    if definition.hasFVar then
      if let some original ← sourceArgumentReference inputs definition selected then
        return some original
  return some (index, selected)

private def alignSourceArgumentsCore? (declaration : Name) (parameters : Array Expr)
    (declared original : Expr) : MetaM (Option (Array (Option Expr))) := do
  let declared := declared.headBeta.consumeMData
  let original := original.headBeta.consumeMData
  unless declared.getAppFn.isConstOf declaration &&
      original.getAppFn.isConstOf declaration do return none
  let arity ← forallTelescopeReducing (← inferType original.getAppFn)
    fun arguments _ => pure arguments.size
  unless declared.getAppNumArgs == arity && original.getAppNumArgs == arity do return none
  unless ← isDefEq declared.getAppFn original.getAppFn do return none
  let inputs ← ((← getLCtx).foldl (fun inputs entry => inputs.push (mkFVar entry.fvarId)) #[])
    |>.filterM fun input => return !(← isProof input)
  let mut retained : Array (Option Expr) := Array.replicate parameters.size none
  for parameter in declared.getAppArgs, supplied in original.getAppArgs do
    if let some index := parameters.findIdx? (· == parameter.consumeMData) then
      if let some previous := retained[index]! then
        unless ← isProof parameter do
          let some first ← sourceArgumentReference inputs previous | return none
          let some second ← sourceArgumentReference inputs supplied | return none
          unless first == second do return none
      else
        retained := retained.set! index (some supplied)
    unless ← isDefEq parameter supplied do return none
  return some retained

/-- Specialize one already selected native target declaration by its complete argument
positions before carrier conversion. Admission and refinement binders need not be in the
target's order. Direct formal parameters retain the original supplied expressions; a repeated
computational formal requires one exact source input/path, not convertible values. Failed
matches leave the caller's metavariables unchanged. -/
opaque alignSourceArguments? (declaration : Name) (parameters : Array Expr)
    (declared original : Expr) : MetaM (Option (Array (Option Expr))) := do
  let accepts ← withoutModifyingState do
    return (← alignSourceArgumentsCore? declaration parameters declared original).isSome
  unless accepts do return none
  alignSourceArgumentsCore? declaration parameters declared original

/-- The complete named or unary-constructed native category family.
Reuse: Resolve's categoryFamily/unaryCategoryFamily and the source constructor interface.
The caller supplies universe variables; no source object is introduced here. -/
partial def nativeCategoryFamily (state : SemanticState) (source : CategoryExpr)
    (instantiateUniverse : Name → MetaM Level) : MetaM Expr := do
  match state.categories.filter (·.expression.syntacticEq source) with
  | #[entry] =>
    let info ← checkedDeclaration entry.declaration
    return mkConst entry.declaration (← info.levelParams.mapM instantiateUniverse)
  | #[] =>
    let .construct id #[.category argument] := source
      | throwUnsupportedSource "comparison requires its complete source category family"
    let some constructor := state.constructor? id
      | throwError "the source category constructor is absent"
    unless constructor.signature == #[.category] do
      throwUnsupportedSource "comparison requires its declared constructor parameters"
    discard <| checkedDeclaration constructor.semantics
    let family ← nativeCategoryFamily state argument instantiateUniverse
    forallTelescopeReducing (← inferType family) fun parameters _ => do
      let category := mkAppN family parameters
      let result ← applyConstructorInterface constructor.semantics #[category] #[category]
      mkLambdaFVars parameters result
  | _ => throwSemanticAmbiguity "comparison requires one complete source category family"

/-- Match the independently declared literal selectors at their complete authored values.
Reuse: Foundation.Objects and Algebra.NamedRings object notation selectors. -/
def sourceLiteralDomains (domain : Expr) : TermElabM (Array ObjectEntry) := do
  let defaults ← (← semanticState).objects.filterM fun entry => do
    unless entry.notations.contains "literal.integral.domain" ||
        entry.notations.contains "literal.fractional.domain" do return false
    let info ← checkedDeclaration entry.declaration
    let some body := info.value? | return false
    let head := body.headBeta.consumeMData.getAppFn.constName?
    unless head.isSome && head == domain.consumeMData.getAppFn.constName? do return false
    withoutModifyingState <| isDefEq body domain
  if defaults.size > 1 then
    throwSemanticAmbiguity "the source has several declared literal-domain selectors"
  return defaults

/-- Compare registered source identities before native carrier conversion.
Where both endpoints name registered objects, their exact row and actual declaration
parameters must agree. Native carrier equality cannot supply a cross-domain comparison.
Reuse: ObjectEntry, sourceObjectReference? and the original native definition bindings. -/
opaque registeredDomainsApplicable (left right : Expr) : MetaM (Except MessageData Unit) := do
  let (left, leftOwners) ← registeredDomain left
  let (right, rightOwners) ← registeredDomain right
  if leftOwners.isEmpty || rightOwners.isEmpty then return .ok ()
  unless leftOwners.any fun first => rightOwners.any (·.id == first.id) do
    return .error m!"the source values have different registered domains \
      ({left}: {leftOwners.map (·.id.raw)}, {right}: {rightOwners.map (·.id.raw)})"
  let leftParameters := left.getAppArgs
  let rightParameters := right.getAppArgs
  unless leftParameters.size == rightParameters.size do
    return .error m!"the source domains have different complete declaration parameters"
  for left in leftParameters, right in rightParameters do
    unless ← isDefEq left right do
      return .error m!"the source domains have different complete declaration parameters \
        ({left} : {← inferType left}, {right} : {← inferType right})"
  return .ok ()

/-- Require the original registered domains to agree. Only the explicit comparison result
above is a candidate mismatch; errors while recovering either original domain propagate. -/
opaque checkRegisteredDomains (left right : Expr) : MetaM Unit := do
  match ← registeredDomainsApplicable left right with
  | .ok () => pure ()
  | .error message => throwError message

/-- Canonical native indices at the complete finite arity supplied by the source type.
Reuse: Lean.Meta.LitValues.litToCtor's Fin construction and native Boolean proof. -/
def sourceFiniteIndices (arity : Expr) (count : Nat) : MetaM (Array Expr) := do
  unless ← isDefEq arity (mkNatLit count) do
    throwError "the source tuple pattern has a different declared component arity"
  (Array.range count).mapM fun index => do
    let literal := mkNatLit index
    let bound := mkApp4 (mkConst ``LT.lt [.zero]) (mkConst ``Nat) (mkConst ``instLTNat)
      literal (mkNatLit count)
    let proof := mkApp3 (mkConst ``of_decide_eq_true) bound
      (mkApp2 (mkConst ``Nat.decLt) literal (mkNatLit count)) eagerReflBoolTrue
    mkAppOptM ``Fin.mk #[some (mkNatLit count), some literal, some proof]

/-- Apply the coordinates declared by the exact source object of a bound value.
Reuse: ObjectComponents and Registry.Semantic.applyObjectParameters, which checks the
complete dependent parameters before application. An unregistered native type returns none;
a registered object never obtains coordinates from a coincident native representation. -/
opaque sourceComponentValues (value : Expr) (count : Nat) : TermElabM (Option (Array Expr)) := do
  let domain ← inferType value
  let (source, entries) ← registeredDomain domain
  if entries.isEmpty then return none
  let #[entry] := entries
    | throwSemanticAmbiguity "the source pattern requires one selected component declaration"
  let some components := entry.components
    | throwUnsupportedSource "source pattern binding is not implemented for this registered object"
  discard <| checkedDeclaration components.arity
  discard <| checkedDeclaration components.projection
  let parameters := source.getAppArgs
  let arity ← applyObjectParameters s!"object {entry.id.raw}" components.arity parameters
  let mut values := #[]
  for index in ← sourceFiniteIndices arity count do
    let projection ← applyObjectParameters s!"object {entry.id.raw}"
      components.projection (parameters.push index)
    let type ← whnfR (← inferType projection)
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the declared source component is not a morphism"
    let source := type.getAppArgs[2]!
    checkRegisteredDomains domain source
    unless ← isDefEq domain source do
      throwError "the declared source component has a different complete domain"
    let component ← elabAppArgs projection #[] #[Arg.expr value] none false false
    values := values.push (sourceReference ``ObjectComponents entry.id.raw
      components.projection component)
  return some values

/-- Exact registered source selection and its applied native category and value. -/
structure SourceObject where
  private mk ::
  entry : ObjectEntry
  categoryEntry : NamedCategoryEntry
  category : SourceTerm
  value : SourceTerm

opaque selectCategory (state : SemanticState) (name : String) : TermElabM NamedCategoryEntry := do
  match state.categories.filter (·.name == name) with
  | #[entry] => pure entry
  | #[] => throwError "unregistered source category: {name}"
  | _ => throwSemanticAmbiguity m!"source category {name} has several registrations"

-- ObjectEntry permits distinct explicit names for refinements of the same base.
-- validateObject checks the base reference before it enters SemanticState. A shared
-- base name still requires a selected category; a distinct name selects its own row.
private def unqualifiedObjectName (state : SemanticState) (entry : ObjectEntry) : Bool :=
  entry.refines.all fun refinement => state.objects.any fun base =>
    base.id == refinement.base && base.name != entry.name

/-- The source uses a name that no registration and no binding declares: invalid source, tagged
with the name. -/
private def throwUnknownSourceName {α : Type} (name : String) : TermElabM α :=
  throwStratum .invalid
    (MessageData.tagged (unknownSourceNameTag name) m!"unregistered source object: {name}")

-- A directly qualified row retains its existing meaning. When no such row exists,
-- an explicit classifier qualification first names an object of that classifier's
-- own host; the checked property action is applied by ReadDispatch to that result.
-- This is a source-name lookup, not a trial after a failed mathematical interpretation.
private def sourceNameCategory (state : SemanticState) (name : String)
    (qualification : Option String) : TermElabM (Option NamedCategoryEntry) := do
  let some required ← qualification.mapM (selectCategory state) | return none
  let .classifierTotal id := required.expression | return some required
  if state.objects.any (fun row => row.name == name && row.category == required.id) ||
      state.morphisms.any (fun row => row.name == name && row.category == required.id) ||
      state.constructions.any (fun row =>
        row.name == name && row.target.syntacticEq required.expression) then
    return some required
  let some classifier := state.classifier? id
    | throwError "the explicitly selected classifier is absent"
  let #[host] := state.categories.filter (·.expression.syntacticEq classifier.host)
    | throwError "the explicit classifier requires one complete registered host category"
  return some host

/-- Select a named source row in an explicit category or independently declared parameter type.
Reuse: native category declaration telescopes, Lean isDefEq and withoutModifyingState.
Each candidate check has isolated metavariables; lexical bindings bypass this selection. -/
opaque selectObjectApplicable (name : String) (category : Option String)
    (expected : Option Expr := none) :
    TermElabM (Except MessageData (ObjectEntry × NamedCategoryEntry)) := do
    let state ← semanticState
    let qualified ← sourceNameCategory state name category
    let expected ← expected.mapM fun type => do whnf (← instantiateMVars type)
    let parameterType := if qualified.isNone then
        expected.filter (! ·.getAppFn.isMVar)
      else none
    let entries := state.objects.filter fun entry =>
      entry.name == name && match qualified with
        | some category => entry.category == category.id
        | none => parameterType.isSome || unqualifiedObjectName state entry
    -- Absence of an independently registered source name is an error. Only the native
    -- parameter-type comparison below can make a known name inapplicable to this reader.
    if entries.isEmpty then throwUnknownSourceName name
    let entries ← entries.filterM fun entry => do
      let #[categoryEntry] := state.categories.filter (·.id == entry.category)
        | throwError "the source object requires one registered category"
      if let some expected := parameterType then withoutModifyingState do
        discard <| checkedDeclaration categoryEntry.declaration
        let family ← mkConstWithFreshMVarLevels categoryEntry.declaration
        let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
        let carrier ← mkAppM ``CategoryTheory.Bundled.α #[mkAppN family parameters]
        isDefEq carrier expected
      else return true
    let entry ← match entries with
      | #[entry] => pure entry
      | #[] =>
        if let some expected := parameterType then
          return .error m!"the source object {name} does not have its independently declared parameter type {expected}"
        else throwUnknownSourceName name
      | _ => throwSemanticAmbiguity m!"source object {name} requires a category qualification"
    let #[categoryEntry] := state.categories.filter (·.id == entry.category)
      | throwError "the source object requires one registered category"
    return .ok (entry, categoryEntry)

/-- Required lookup retains the source error when no compatible native object is available. -/
opaque selectObject (name : String) (category : Option String) (expected : Option Expr := none) :
    TermElabM (ObjectEntry × NamedCategoryEntry) := do
  match ← selectObjectApplicable name category expected with
  | .ok selected => pure selected
  | .error message => throwError message

inductive SourceNamedEntry where
  | registered (entry : ObjectEntry ⊕ MorphismEntry) (category : NamedCategoryEntry)
  | construction (entry : ConstructionEntry)

/-- Select the exact named source kind without a priority between kinds. When a registered
morphism and a registered object share the name, every one of them is a candidate; the reader
keeps those that accept the actual arguments (`span({u₁, u₂})`), and the name is ambiguous
only if several do. -/
opaque selectNamedApplicable (name : String) (category : Option String) (expected : Option Expr) :
    TermElabM (Except MessageData (Array SourceNamedEntry)) := do
  let state ← semanticState
  let qualified ← sourceNameCategory state name category
  let morphisms := state.morphisms.filter fun entry =>
    entry.name == name && qualified.all (·.id == entry.category)
  let objects := state.objects.filter fun entry =>
    entry.name == name && qualified.all (·.id == entry.category) &&
      (qualified.isSome || unqualifiedObjectName state entry)
  let constructions := state.constructions.filter fun entry =>
    entry.name == name && qualified.all (entry.target.syntacticEq ·.expression)
  unless constructions.isEmpty do
    unless objects.isEmpty && morphisms.isEmpty do
      throwSemanticAmbiguity m!"source name {name} has distinct registered kinds"
    let #[entry] := constructions
      | throwSemanticAmbiguity m!"source construction {name} has several registrations"
    return .ok #[.construction entry]
  if morphisms.isEmpty then
    match ← selectObjectApplicable name category expected with
    | .ok (entry, category) => return .ok #[.registered (.inl entry) category]
    | .error message => return .error message
  let category := fun (id : CategoryId) => do
    let #[categoryEntry] := state.categories.filter (·.id == id)
      | throwError "the source name requires one registered category"
    return categoryEntry
  unless objects.isEmpty do
    let kinds ← morphisms.mapM fun entry => do
      return SourceNamedEntry.registered (.inr entry) (← category entry.category)
    return .ok (kinds ++ (← objects.mapM fun entry => do
      return SourceNamedEntry.registered (.inl entry) (← category entry.category)))
  let #[entry] := morphisms
    | throwSemanticAmbiguity m!"source name {name} requires a category qualification"
  return .ok #[.registered (.inr entry) (← category entry.category)]

/-- Required named selection preserves all registered kinds and genuine ambiguity. -/
opaque selectNamed (name : String) (category : Option String) (expected : Option Expr) :
    TermElabM (Array SourceNamedEntry) := do
  match ← selectNamedApplicable name category expected with
  | .ok selected => pure selected
  | .error message => throwError message

/-- Form the actual registered value and check its declared object or morphism role.
Reuse: the source's declaration/category pair, native application and the identity functor. -/
opaque registeredExpressionsApplicable (entry : ObjectEntry ⊕ MorphismEntry)
    (categoryEntry : NamedCategoryEntry)
    (application : Expr → Option Expr → TermElabM (Except MessageData Expr)) :
    TermElabM (Except MessageData (Expr × Expr)) := do
  let (declaration, role, kind, id) := match entry with
    | .inl entry => (entry.declaration, SourceCategoryRole.object, ``ObjectEntry, entry.id.raw)
    | .inr entry => (entry.declaration, SourceCategoryRole.morphism, ``MorphismEntry, entry.id.raw)
  discard <| checkedDeclaration declaration
  discard <| checkedDeclaration categoryEntry.declaration
  let family ← mkConstWithFreshMVarLevels categoryEntry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let category := mkAppN family parameters
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
  let function ← mkConstWithFreshMVarLevels declaration
  let value ← application function (if role == .object then some carrier else none)
  let value ← match value with
    | .ok value => pure value
    | .error message => return .error message
  unless value.consumeMData.getAppFn.constName? == some declaration do
    throwError "registered source formation did not retain its actual declaration"
  match role with
  | .object =>
    unless ← isDefEq (← inferType value) carrier do
      throwError "the source object does not inhabit its registered category"
  | .morphism =>
    let identity ← categoryIdentity category
    let function ← mkAppM ``CategoryTheory.Functor.map #[identity]
    discard <| elabAppArgs function #[] #[Arg.expr value] none false false
  let value := sourceReference kind id declaration value
  return .ok (category, ← if role == .morphism then selectMorphism value else pure value)

/-- Form a required registered source value, retaining ordinary failure diagnostics. -/
opaque registeredExpressions (entry : ObjectEntry ⊕ MorphismEntry)
    (categoryEntry : NamedCategoryEntry)
    (application : Expr → Option Expr → TermElabM Expr) : TermElabM (Expr × Expr) := do
  let formed ← registeredExpressionsApplicable entry categoryEntry fun function expected => do
    return .ok (← application function expected)
  match formed with
  | .ok value => pure value
  | .error message => throwError message

/-- Retain the registered category of a set or set map formed by public function syntax.
Reuse: the actual Sets declaration, Bundled projections and Functor.map. The supplied
native value constrains the complete category bundle, including its universe. -/
opaque sourceSetJudgement (role : SourceCategoryRole) (value : Expr) :
    TermElabM NativeSourceJudgement := do
  let #[entry] := (← semanticState).categories.filter (·.id == CategoryId.sets)
    | throwError "source function syntax requires one registered category of sets"
  discard <| checkedDeclaration entry.declaration
  let family ← mkConstWithFreshMVarLevels entry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let bundle := mkAppN family parameters
  match role with
  | .object =>
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    unless ← isDefEq (← inferType value) carrier do
      throwError "the source function domain is outside its registered category of sets"
  | .morphism =>
    let function ← mkAppM ``CategoryTheory.Functor.map #[← categoryIdentity bundle]
    discard <| elabAppArgs function #[] #[Arg.expr value] none false false
  return ⟨value, some ⟨role, entry.expression, bundle, none, none⟩⟩

/-- A direct registered view before closing its complete native expressions. -/
structure NativeSourceView where
  private mk ::
  reference : FunctorId ⊕ ClassifierId
  declaration : Name
  target : CategoryExpr
  functor : Expr
  targetBundle : Expr

inductive SourceActionEntry where
  | registered (entry : FunctorEntry ⊕ ClassifierEntry)
  | construction (entry : ConstructionEntry)

/-- Select an actual direct source action by its exact published identity. -/
opaque selectView (id : String) : TermElabM SourceActionEntry := do
  let state ← semanticState
  match state.functors.filter (·.id.raw == id), state.classifiers.filter (·.id.raw == id),
      state.constructions.filter (·.name == id) with
  | #[entry], #[], #[] => return .registered (.inl entry)
  | #[], #[entry], #[] => return .registered (.inr entry)
  | #[], #[], #[entry] => return .construction entry
  | #[], #[], #[] => throwError "unregistered source view: {id}"
  | _, _, _ => throwSemanticAmbiguity m!"source view {id} has several declared actions"

/-- Apply the selected declaration and retain its complete native functor boundary.
An existing receiver category stays fixed. Otherwise the explicitly selected action supplies
its source context, which native object application must check. Explicit functor use admits
each registered role. Reuse: SourceSession.namedFunctor, classifierForgetInstance and
functorCategoryBundles; source: #66, comment 6664276482 §4. -/
opaque viewExpressions (entry : FunctorEntry ⊕ ClassifierEntry)
    (source : Option (CategoryExpr × Expr))
    (application : Expr → TermElabM Expr) : TermElabM NativeSourceView := do
  let (symbolic, target, declaration, reference) := match entry with
    | .inl entry => (entry.source, entry.target, entry.declaration, Sum.inl entry.id)
    | .inr entry => (.classifierTotal entry.id, entry.host, entry.declaration, Sum.inr entry.id)
  if let some (selected, _) := source then
    unless symbolic.syntacticEq selected do
      throwError "the selected source action has a different complete symbolic source category"
  discard <| checkedDeclaration declaration
  let value ← application (← mkConstWithFreshMVarLevels declaration)
  let functor ← match entry with
    | .inl _ =>
      if (← whnf (← inferType value)).isAppOf ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[value]
      else pure value
    | .inr _ => do
      let type ← whnf (← inferType value)
      let classifier ← if type.isAppOf ``LeanCategories.PropertyClassifier then
          mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[value]
        else if type.isAppOf ``LeanCategories.StructureClassifier then
          mkAppM ``LeanCategories.StructureClassifier.toClassifier #[value]
        else if type.isAppOf ``LeanCategories.Classifier then pure value
        else throwError "the selected classifier requires its complete declaration arguments"
      mkAppM ``CategoryTheory.Cat.Hom.toFunctor
        #[← mkAppM ``LeanCategories.Classifier.forget #[classifier]]
  let (domain, targetBundle) ← functorCategoryBundles functor
  if let some (_, selected) := source then
    unless ← isDefEq domain selected do
      throwError "the selected source action has a different complete native source category"
  return ⟨reference, declaration, target, functor, targetBundle⟩

/-- Apply the actual native functor to its actual object and check its complete target type.
Reuse: Functor.toPrefunctor/Prefunctor.obj, shared with the retained source functor API. -/
opaque functorObject (functor object target : Expr) : MetaM Expr := do
  let (domain, _) ← functorCategoryBundles functor
  let inputType ← mkAppM ``CategoryTheory.Bundled.α #[domain]
  unless ← withTransparency .all <| isDefEq (← inferType object) inputType do
    throwError "the source object does not inhabit the selected functor's native domain"
  let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
  let value ← mkAppM ``Prefunctor.obj #[prefunctor, object]
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[target]
  unless ← isDefEq (← inferType value) carrier do
    throwError "the source image does not belong to its complete native target category"
  return value

partial def checkEdgeDeclarations (state : SemanticState) : EdgeRef → MetaM Unit
  | .functor id => do
    let some entry := state.functor? id | throwError "the source functor declaration is absent"
    discard <| checkedDeclaration entry.declaration
  | .classifierForget id => do
    let some entry := state.classifier? id
      | throwError "the source classifier declaration is absent"
    discard <| checkedDeclaration entry.declaration
  | .constructMap id inner => do
    let some entry := state.constructor? id
      | throwError "the source constructor declaration is absent"
    let some action := entry.functorialAction
      | throwError "the source constructor has no declared functorial action"
    discard <| checkedDeclaration entry.semantics
    discard <| checkedDeclaration action
    checkEdgeDeclarations state inner

structure NativeRouteFunctor where
  functor : Expr
  target : Expr
  actions : Array Expr

/-- Interpret a source route while retaining every complete edge application.
Reuse: Registry.Semantic.routeFunctor's composition, edgeFunctor and functorCategoryBundles. -/
def nativeRouteFunctor (state : SemanticState) (route : Route) (category : Expr) :
    MetaM NativeRouteFunctor := do
  let mut current := category
  let mut actions := #[]
  for ref in route.refs do
    checkEdgeDeclarations state ref
    let action ← state.edgeFunctor ref
    unless ← expandSourceStructures ((← getMVars action).map mkMVar) do
      throwError "the selected functor's native parameter structures are inconsistent"
    let (domain, target) ← functorCategoryBundles action
    unless ← isDefEq domain current do
      throwError "the selected functor edge {repr ref} has a different complete source category: expected {current}, declared {domain}"
    actions := actions.push (← instantiateMVars action)
    current ← instantiateMVars target
  let functor ← match actions[0]? with
    | none => categoryIdentity category
    | some first => (actions.drop 1).foldlM mkFunctorComp first
  return ⟨functor, current, actions⟩

/-- Retain the route, actual edge parameters and comparison of an object refinement.
Reuse: ObjectRefinement and applyObjectParameters at the original object arguments. -/
opaque objectCarrierSelection (entry : ObjectEntry) (category value : Expr) :
    TermElabM (Option NativeSourceCarrierSelection) := do
  let some refinement := entry.refines | return none
  let state ← semanticState
  let some base := state.objects.find? (·.id == refinement.base)
    | throwError "the selected object refinement has no registered base"
  let #[targetCategory] := state.categories.filter (·.id == base.category)
    | throwError "the selected object refinement requires one registered base category"
  discard <| checkedDeclaration refinement.identification
  let #[sourceCategory] := state.categories.filter (·.id == entry.category)
    | throwError "the selected object refinement requires one registered source category"
  let some steps := state.routeEdges? sourceCategory.expression targetCategory.expression
      refinement.route
    | throwError "the selected object refinement has different source boundaries"
  let selected ← nativeRouteFunctor state
    { source := sourceCategory.expression, target := targetCategory.expression, steps } category
  let comparison ← applyObjectParameters s!"object {entry.id.raw}" refinement.identification
    (← sourceDomain value).getAppArgs
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the selected carrier comparison is not an isomorphism"
  let image ← functorObject selected.functor value selected.target
  unless ← isDefEq type.getAppArgs[2]! image do
    throwError "the selected carrier action has different complete comparison parameters"
  return some ⟨refinement.route, targetCategory.expression, #[refinement.identification],
    ← selected.actions.mapM instantiateMVars, #[← instantiateMVars comparison]⟩

/-- Select a registered source family, then let native application elaborate its arguments.
Reuse: semanticState and the independently owned declaration telescopes; Lean.elabAppArgs
accepts retained expressions and synthesizes native implicits and selected instances. -/
opaque SourceSession.namedObject (session : SourceSession) (reference : Syntax) (name : String)
    (category : Option String) (arguments : Array SourceTerm) : TermElabM SourceObject :=
  withRef reference do
    let (entry, categoryEntry) ← selectObject name category
    let #[category, value] ← session.elaborateJudgements reference fun context => do
        let arguments ← arguments.mapM fun argument => do
          return Arg.expr (← argument.source.inContext context)
        let (category, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
          elabAppArgs function #[] arguments expected false false
        let selection ← objectCarrierSelection entry category value
        return #[⟨category, none⟩,
          ⟨value, some ⟨.object, categoryEntry.expression, category, selection, none⟩⟩]
      | throwError "registered source formation returned an invalid number of expressions"
    return ⟨entry, categoryEntry, category, value⟩

end CasCompiler
