module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.Elaborate
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.Layout
public import CasCompiler.SelectedMorphism
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Semantics.Foundation.Catalogue
public import CasCatalogue.InterpretationFailure
public import CasCatalogue.Admission
public import CasContract.Failure
public import Lean.Meta.Structure
import Lean.Elab.App

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- The function of the actual set map, through its two native record fields.
Reuse: Mathlib.CategoryTheory.Types.Basic, TypeCat.Hom.hom' and Fun.toFun.
The public hom abbreviation selects the same field through ConcreteCategory;
the direct projection retains that map without an extra dictionary application. -/
def sourceSetFunction (value : Expr) : MetaM Expr := do
  let function ← mkAppM ``TypeCat.Hom.hom' #[value]
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

/-- Recognize a complete native declaration in a mathematical template. Typed source
selections use registeredSourceDomain below, at their exact retained binding. -/
def registeredDomain (value : Expr) : MetaM (Expr × Array ObjectEntry) := do
  let state ← semanticState
  let domain ← sourceDomain value
  return (domain, state.objects.filter fun entry =>
    domain.getAppFn.constName? == some entry.declaration)

/-- Read the selected object only through its explicit source record and original application.
Unselected native templates retain the original whole-declaration check. -/
partial def registeredSourceDomain (value : Expr) : SourceReadM (Expr × Array ObjectEntry) := do
  let some selected ← SourceReadM.selection? value | return ← registeredDomain value
  match selected.reference with
  | some (.named (.registered (.inl entry) _)) =>
    let some application ← sourceApplication? entry.declaration selected
      | liftM (m := TermElabM) <| throwError "the selected source object lost its original application"
    return (application, #[entry])
  | _ =>
    if let some origin := selected.typeOrigin then
      return ← registeredSourceDomain origin.object
    if let some endpoint := selected.endpoint then
      return ← registeredSourceDomain endpoint.value
    return (value, #[])

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

/-- Source domain agreement retains exact selected rows before mathematical parameter checking.
Original-source substitution checks those parameters only; it cannot choose a selected row. -/
opaque registeredSourceDomainsApplicable (left right : Expr) :
    SourceReadM (Except MessageData Unit) := do
  let (left, leftOwners) ← registeredSourceDomain left
  let (right, rightOwners) ← registeredSourceDomain right
  if leftOwners.isEmpty || rightOwners.isEmpty then return .ok ()
  unless leftOwners.any fun first => rightOwners.any (·.id == first.id) do
    return .error m!"the source values have different registered domains \
      ({left}: {leftOwners.map (·.id.raw)}, {right}: {rightOwners.map (·.id.raw)})"
  let leftParameters := left.getAppArgs
  let rightParameters := right.getAppArgs
  unless leftParameters.size == rightParameters.size do
    return .error m!"the source domains have different complete declaration parameters"
  let scope ← get
  let agrees ← scope.context.withOriginalSources (leftParameters ++ rightParameters)
    fun parameters => do
      let mut agrees := true
      for index in [:leftParameters.size] do
        unless ← isDefEq parameters[index]! parameters[leftParameters.size + index]! do
          agrees := false
      pure agrees
  unless agrees do
    return .error m!"the source domains have different complete declaration parameters"
  return .ok ()

/-- Require complete typed source domains at the current source scope. -/
opaque checkRegisteredSourceDomains (left right : Expr) : SourceReadM Unit := do
  match ← registeredSourceDomainsApplicable left right with
  | .ok () => pure ()
  | .error message => liftM (m := TermElabM) <| throwError message

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
opaque sourceComponentValues (value : Expr) (count : Nat) : SourceReadM (Option (Array Expr)) := do
  let domain ← inferType value
  let (source, entries) ← registeredSourceDomain domain
  if entries.isEmpty then return none
  let #[entry] := entries
    | liftM (m := TermElabM) <| throwSemanticAmbiguity "the source pattern requires one selected component declaration"
  let some components := entry.components
    | liftM (m := TermElabM) <| throwUnsupportedSource "source pattern binding is not implemented for this registered object"
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
      liftM (m := TermElabM) <| throwError "the declared source component is not a morphism"
    let source := type.getAppArgs[2]!
    checkRegisteredSourceDomains domain source
    unless ← isDefEq domain source do
      liftM (m := TermElabM) <| throwError "the declared source component has a different complete domain"
    let component ← elabAppArgs projection #[] #[Arg.expr value] none false false
    values := values.push (← SourceReadM.select (← sourceReferenceAt (.components entry)
      projection component))
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
opaque registeredExpressionsApplicableScoped (entry : ObjectEntry ⊕ MorphismEntry)
    (categoryEntry : NamedCategoryEntry)
    (select : SourceSelection Expr → Option Expr → StateCpsT σ TermElabM Expr)
    (application : Expr → Option Expr → StateCpsT σ TermElabM (Except MessageData Expr)) :
    StateCpsT σ TermElabM (Except MessageData (Expr × Expr)) := do
  let (declaration, role) := match entry with
    | .inl entry => (entry.declaration, SourceCategoryRole.object)
    | .inr entry => (entry.declaration, SourceCategoryRole.morphism)
  discard <| checkedDeclaration declaration
  discard <| checkedDeclaration categoryEntry.declaration
  let previous ← liftM (m := MetaM) getMCtx
  let family ← mkConstWithFreshMVarLevels categoryEntry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let nativeCategory := mkAppN family parameters
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[nativeCategory]
  let function ← mkConstWithFreshMVarLevels declaration
  let current ← liftM (m := MetaM) getMCtx
  let owned := current.decls.foldl (fun result identity _ =>
    if previous.decls.contains identity then result else result.push identity) #[]
  let value ← application function (if role == .object then some carrier else none)
  let value ← match value with
    | .ok value => pure value
    | .error message => return .error message
  extendSourceApplicationScope owned
  unless value.consumeMData.getAppFn.constName? == some declaration do
    liftM (m := TermElabM) <|
      throwError "registered source formation did not retain its actual declaration"
  match role with
  | .object =>
    unless ← isDefEq (← inferType value) carrier do
      liftM (m := TermElabM) <|
        throwError "the source object does not inhabit its registered category"
  | .morphism =>
    let identity ← categoryIdentity nativeCategory
    let function ← mkAppM ``CategoryTheory.Functor.map #[identity]
    discard <| elabAppArgs function #[] #[Arg.expr value] none false false
  discard <| select (← sourceReferenceAt (.category categoryEntry)
    nativeCategory nativeCategory) none
  let category := nativeCategory
  let categoryData : NativeSourceCategory :=
    ⟨role, categoryEntry.expression, category, none, none⟩
  let selected ← sourceReferenceAt (.named (.registered entry categoryEntry)) value value
  let selected := { selected with category := some categoryData }
  let value ← if role == .morphism then
      selectMorphism selected select (some category)
    else
      select selected (some (← mkAppM ``CategoryTheory.Bundled.α #[category]))
  return .ok (category, value)

/-- Named source syntax uses the same producer with its current typed source scope. -/
opaque registeredExpressionsApplicable (entry : ObjectEntry ⊕ MorphismEntry)
    (categoryEntry : NamedCategoryEntry)
    (application : Expr → Option Expr → SourceReadM (Except MessageData Expr)) :
    SourceReadM (Except MessageData (Expr × Expr)) :=
  registeredExpressionsApplicableScoped entry categoryEntry
    (fun selected expected => SourceReadM.select selected expected) application

/-- Form a required registered source value, retaining ordinary failure diagnostics. -/
opaque registeredExpressions (entry : ObjectEntry ⊕ MorphismEntry)
    (categoryEntry : NamedCategoryEntry)
    (application : Expr → Option Expr → SourceReadM Expr) : SourceReadM (Expr × Expr) := do
  let formed ← registeredExpressionsApplicable entry categoryEntry fun function expected => do
    return .ok (← application function expected)
  match formed with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

/-- Retain the registered category of a set or set map formed by public function syntax.
Reuse: the actual Sets declaration, Bundled projections and Functor.map. The supplied
native value constrains the complete category bundle, including its universe. -/
opaque sourceSetJudgement (role : SourceCategoryRole) (value : Expr) :
    SourceReadM NativeSourceJudgement := do
  let #[entry] := (← semanticState).categories.filter (·.id == CategoryId.sets)
    | liftM (m := TermElabM) <| throwError "source function syntax requires one registered category of sets"
  discard <| checkedDeclaration entry.declaration
  let family ← mkConstWithFreshMVarLevels entry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let nativeBundle := mkAppN family parameters
  let bundle := nativeBundle
  match role with
  | .object =>
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    unless ← isDefEq (← inferType value) carrier do
      liftM (m := TermElabM) <| throwError "the source function domain is outside its registered category of sets"
  | .morphism =>
    let function ← mkAppM ``CategoryTheory.Functor.map #[← categoryIdentity bundle]
    discard <| elabAppArgs function #[] #[Arg.expr value] none false false
  discard <| SourceReadM.select (← sourceReferenceAt (.category entry) nativeBundle nativeBundle)
  let category : NativeSourceCategory := ⟨role, entry.expression, nativeBundle, none, none⟩
  let selected := (← SourceReadM.selection? value).getD { value }
  let value ← SourceReadM.select { selected with value, category := some category }
  return ⟨value, some category⟩

/-- A direct registered view before closing its complete native expressions. -/
structure NativeSourceView where
  private mk ::
  reference : FunctorId ⊕ ClassifierId
  declaration : Name
  target : CategoryExpr
  functor : Expr
  targetBundle : Expr
  application : Expr

/-- Expose the native functor field of this actual declared value. The source reference is
already on its declaration application, before a field projection can hide that head. -/
def sourceFunctorValue (value : Expr) : MetaM Expr := do
  if (← whnf (← inferType value)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[value]
  else pure value

/-- Instantiate an explicitly selected functor family with its exact source reference.
Reuse: registeredFunctorInstance's native telescope and sourceFunctorValue; the existing
adapter returns only the projected functor and has no reference hook at formation. -/
def sourceFunctorInstance (entry : FunctorEntry) : MetaM Expr := do
  discard <| checkedDeclaration entry.declaration
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  sourceFunctorValue (mkAppN constant arguments)

/-- Expose the forgetful field of this actual selected classifier application.
Reuse: classifierForgetInstance's native projections; its argument already retains the
complete registered declaration and parameters before any projection is formed. -/
def sourceClassifierForgetValue (value : Expr) : MetaM Expr := do
  let type ← whnf (← inferType value)
  let classifier ← if type.isAppOf ``LeanCategories.PropertyClassifier then
      mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[value]
    else if type.isAppOf ``LeanCategories.StructureClassifier then
      mkAppM ``LeanCategories.StructureClassifier.toClassifier #[value]
    else if type.isAppOf ``LeanCategories.Classifier then pure value
    else throwError "the selected classifier requires its complete declaration arguments"
  mkAppM ``CategoryTheory.Cat.Hom.toFunctor
    #[← mkAppM ``LeanCategories.Classifier.forget #[classifier]]

/-- Prepare the actual declared edge and a continuation that retains those same original
applications after the complete native path has solved their parameters. This continuation
does not repeat declaration selection or recover an application from a projected value. -/
private def sourceEdgeFormation [Monad m] [MonadLiftT MetaM m]
    (state : SemanticState) (select : SourceSelection Expr → Option Expr → m Expr)
    (edge : EdgeRef) (next : Expr → m Expr → m α) : m α :=
  match edge with
  | .functor id => do
    let (entry, application, native) ← liftM (m := MetaM) do
      let some entry := state.functor? id
        | throwError "unregistered functor {id.raw}"
      discard <| checkedDeclaration entry.declaration
      let constant ← mkConstWithFreshMVarLevels entry.declaration
      let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
      let application := mkAppN constant arguments
      return (entry, application, ← sourceFunctorValue application)
    let retain : m Expr := do
      let application ← liftM (m := MetaM) <| instantiateMVars application
      let selected ← liftM (m := MetaM) <| sourceReferenceAt (.functor entry)
        application application
      let value ← select selected none
      liftM (m := MetaM) <| sourceFunctorValue value
    next native retain
  | .classifierForget id => do
    let (entry, application, native) ← liftM (m := MetaM) do
      let some entry := state.classifier? id
        | throwError "unregistered classifier {id.raw}"
      discard <| checkedDeclaration entry.declaration
      let constant ← mkConstWithFreshMVarLevels entry.declaration
      let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
      let application := mkAppN constant arguments
      return (entry, application, ← sourceClassifierForgetValue application)
    let retain : m Expr := do
      let application ← liftM (m := MetaM) <| instantiateMVars application
      let selected ← liftM (m := MetaM) <| sourceReferenceAt (.classifier entry)
        application application
      let value ← select selected none
      liftM (m := MetaM) <| sourceClassifierForgetValue value
    next native retain
  | .constructMap id inner => do
    let (constructor, action) ← liftM (m := MetaM) do
      let some constructor := state.constructor? id
        | throwError "unregistered constructor {id.raw}"
      let some action := constructor.functorialAction
        | throwError "constructor {id.raw} has no registered action on functors"
      return (constructor, action)
    sourceEdgeFormation state select inner fun functor retainInner => do
      let (source, target, native) ← liftM (m := MetaM) do
        let (source, target) ← functorCategoryBundles functor
        let native ← applyConstructorInterface action #[source, target] #[functor]
        return (source, target, native)
      let retain : m Expr := do
        let functor ← retainInner
        let categories ← liftM (m := MetaM) <| #[source, target].mapM instantiateMVars
        let value ← liftM (m := MetaM) <| applyConstructorInterface action categories #[functor]
        let selected ← liftM (m := MetaM) <| sourceReferenceAt
          (.constructorInterface constructor .functorialAction) value value
        select selected none
      next native retain

/-- The pure native edge keeps the same declared mathematical family for rigid checks. -/
def sourceEdgeFunctor (state : SemanticState) (edge : EdgeRef) : MetaM Expr :=
  sourceEdgeFormation (m := MetaM) state
    (fun selected _ => pure selected.value) edge (fun native _ => pure native)
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

/-- Apply the actual native functor's object projection to its actual object.
`Functor.toPrefunctor` is a record conversion with an additional dependent map field.
The original object action does not request that conversion or its category arguments:
Mathlib's `Functor.toPrefunctor.obj` is definitionally `Functor.obj`. -/
opaque functorObject (functor object target : Expr) (source : Option Expr := none) : MetaM Expr := do
  let (declaredDomain, declaredTarget) ← functorCategoryBundles functor
  let domain := source.getD declaredDomain
  unless ← isDefEq domain declaredDomain <&&> isDefEq target declaredTarget do
    throwError "the source object action changed its complete functor categories"
  let inputType ← mkAppM ``CategoryTheory.Bundled.α #[domain]
  unless ← withTransparency .all <| isDefEq (← inferType object) inputType do
    throwError "the source object does not inhabit the selected functor's native domain"
  let value ← mkAppM ``CategoryTheory.Functor.obj #[functor, object]
  -- At a known source bundle, retain its actual carrier and dictionary at the
  -- native object's projection slots; inferred types are only conversion checks.
  let value ← if source.isSome then do
    let arguments := value.getAppArgs
    unless arguments.size == 6 do
      throwError "the source object action lost its native category parameters"
    let sourceInstance ← mkAppM ``CategoryTheory.Bundled.str #[domain]
    let targetType ← mkAppM ``CategoryTheory.Bundled.α #[target]
    let targetInstance ← mkAppM ``CategoryTheory.Bundled.str #[target]
    let retained := mkAppN value.getAppFn
      #[inputType, sourceInstance, targetType, targetInstance, functor, object]
    check retained
    unless ← isDefEq retained value do
      throwError "the source object action changed its native object projection"
    pure retained
  else pure value
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


/-- Form this exact declared edge path with an explicit source-selection continuation.
Every original declaration is prepared once, the complete native category constraints are
checked, and only then are its full selected rows bound before native projections. -/
def nativeEdgePathFunctorWith [Monad m] [MonadLiftT MetaM m]
    (state : SemanticState) (references : Array EdgeRef) (category : Expr)
    (select : SourceSelection Expr → Option Expr → m Expr) : m NativeRouteFunctor := do
  -- Pending scoped effects stay in this continuation, outside native MetaM results.
  -- Every path constraint is still solved before any original selection is bound.
  let rec prepare : List EdgeRef → Expr → Array (m Expr) → Array Expr → m NativeRouteFunctor
    | [], current, pending, boundaries => do
      let (current, boundaries) ← liftM (m := MetaM) do
        return (← instantiateMVars current, ← boundaries.mapM instantiateMVars)
      let actions ← pending.mapM id
      let functor ← liftM (m := MetaM) do
        match actions[0]? with
        | none => categoryIdentity category
        | some first => do
          let mut composite := first
          for index in [1:actions.size] do
            let next := actions[index]!
            let inferred ← mkFunctorComp composite next
            let mut arguments := #[]
            for bundle in #[category, boundaries[index]!, boundaries[index + 1]!] do
              arguments := arguments.push (← mkAppM ``CategoryTheory.Bundled.α #[bundle])
              arguments := arguments.push (← mkAppM ``CategoryTheory.Bundled.str #[bundle])
            let retained := mkAppN inferred.getAppFn (arguments ++ #[composite, next])
            check retained
            unless ← isDefEq retained inferred do
              throwError "the source path changed its complete native composition"
            composite := retained
          pure composite
      return ⟨functor, current, actions⟩
    | ref :: remaining, current, pending, boundaries => do
      liftM (m := MetaM) <| checkEdgeDeclarations state ref
      sourceEdgeFormation state select ref fun action retain => do
        let target ← liftM (m := MetaM) do
          unless ← expandSourceStructures ((← getMVars action).map mkMVar) do
            throwError "the selected functor's native parameter structures are inconsistent"
          let (domain, target) ← functorCategoryBundles action
          unless ← isDefEq domain current do
            throwError "the selected functor edge {repr ref} has a different complete source category: expected {current}, declared {domain}"
          instantiateMVars target
        prepare remaining target (pending.push retain) (boundaries.push target)
  prepare references.toList category #[] #[category]

/-- Pure native families use the same complete path formation without introducing binders. -/
def nativeEdgePathFunctor (state : SemanticState) (references : Array EdgeRef) (category : Expr) :
    MetaM NativeRouteFunctor :=
  nativeEdgePathFunctorWith state references category (fun selected _ => pure selected.value)
/-- A selected structural route uses the same complete native edge formation. -/
def nativeRouteFunctor (state : SemanticState) (route : Route) (category : Expr) :
    MetaM NativeRouteFunctor :=
  nativeEdgePathFunctor state route.refs category

/-- Retain the route, actual edge parameters and comparison of an object refinement.
Reuse: ObjectRefinement and applyObjectParameters at the original object arguments. -/
opaque objectCarrierSelection (entry : ObjectEntry) (category value : Expr) :
    SourceReadM (Option NativeSourceCarrierSelection) := do
  let some refinement := entry.refines | return none
  let state ← semanticState
  let some base := state.objects.find? (·.id == refinement.base)
    | liftM (m := TermElabM) <| throwError "the selected object refinement has no registered base"
  let #[targetCategory] := state.categories.filter (·.id == base.category)
    | liftM (m := TermElabM) <| throwError "the selected object refinement requires one registered base category"
  discard <| checkedDeclaration refinement.identification
  let #[sourceCategory] := state.categories.filter (·.id == entry.category)
    | liftM (m := TermElabM) <| throwError "the selected object refinement requires one registered source category"
  let some steps := state.routeEdges? sourceCategory.expression targetCategory.expression
      refinement.route
    | liftM (m := TermElabM) <| throwError "the selected object refinement has different source boundaries"
  let selected ← nativeRouteFunctor state
    { source := sourceCategory.expression, target := targetCategory.expression, steps } category
  let some original ← SourceReadM.selection? value
    | liftM (m := TermElabM) <| throwError "the selected refinement lost its original object binding"
  let some application ← sourceApplication? entry.declaration original
    | liftM (m := TermElabM) <| throwError "the selected refinement lost its original object parameters"
  let comparison ← applyObjectParameters s!"object {entry.id.raw}" refinement.identification
    application.getAppArgs
  let comparison ← SourceReadM.select (← sourceReferenceAt (.refinement entry refinement)
    comparison comparison)
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    liftM (m := TermElabM) <| throwError "the selected carrier comparison is not an isomorphism"
  let image ← functorObject selected.functor value selected.target
  let scope ← get
  let agrees ← liftM (m := MetaM) <|
    scope.context.withOriginalSources
        #[original.value, application, type.getAppArgs[2]!, image] fun sources =>
      isDefEq sources[0]! sources[1]! <&&> isDefEq sources[2]! sources[3]!
  unless agrees do
    liftM (m := TermElabM) <| throwError "the selected carrier action has different complete comparison parameters"
  let actions ← liftM (m := MetaM) <| selected.actions.mapM instantiateMVars
  let comparison ← liftM (m := MetaM) <| instantiateMVars comparison
  return some ⟨refinement.route, targetCategory.expression, #[refinement.identification],
    actions, #[comparison]⟩

/-- Select a registered source family, then let native application elaborate its arguments.
Reuse: semanticState and the independently owned declaration telescopes; Lean.elabAppArgs
accepts retained expressions and synthesizes native implicits and selected instances. -/
opaque SourceSession.namedObject (session : SourceSession) (reference : Syntax) (name : String)
    (category : Option String) (arguments : Array SourceTerm) : TermElabM SourceObject :=
  withRef reference do
    let (entry, categoryEntry) ← selectObject name category
    let #[category, value] ← session.elaborateJudgementsScoped reference do
        let arguments ← arguments.mapM fun argument => do
          return Arg.expr (← session.readTerm argument)
        let (category, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
          elabAppArgs function #[] arguments expected false false
        let selection ← objectCarrierSelection entry category value
        return #[⟨category, none⟩,
          ⟨value, some ⟨.object, categoryEntry.expression, category, selection, none⟩⟩]
      | throwError "registered source formation returned an invalid number of expressions"
    return ⟨entry, categoryEntry, category, value⟩

private partial def sourceActionSelection (state : SemanticState) :
    EdgeRef → MetaM (Name × Array SelectedSourceReference)
  | .functor id => do
    let some entry := state.functor? id | throwError "the original point functor is absent"
    return (entry.declaration, #[.functor entry])
  | .classifierForget id => do
    let some entry := state.classifier? id | throwError "the original point classifier is absent"
    return (entry.declaration, #[.classifierForget entry])
  | .constructMap id inner => do
    let some entry := state.constructor? id | throwError "the original point constructor is absent"
    let (declaration, references) ← sourceActionSelection state inner
    return (declaration, #[.constructorInterface entry .functorialAction] ++ references)

def sourceActionDeclaration (state : SemanticState) (edge : EdgeRef) : MetaM Name :=
  return (← sourceActionSelection state edge).1

/-- Complete original rows of the explicitly selected edge, in its native nesting order. -/
def sourceActionReferences (state : SemanticState) (edge : EdgeRef) :
    MetaM (Array SelectedSourceReference) :=
  return (← sourceActionSelection state edge).2

partial def categoricalActionValue (state : SemanticState) (edge : EdgeRef)
    (application : Expr) : MetaM (Expr × CategoryExpr) := do
  match edge with
  | .functor id =>
    let some entry := state.functor? id | throwError "the original point functor is absent"
    return (← sourceFunctorValue application, entry.target)
  | .classifierForget id =>
    let some entry := state.classifier? id | throwError "the original point classifier is absent"
    return (← sourceClassifierForgetValue application, entry.host)
  | .constructMap id inner =>
    let some entry := state.constructor? id | throwError "the original point constructor is absent"
    unless entry.signature == #[.category] do
      throwError "the derived point action requires the original unary category constructor"
    let some declaration := entry.functorialAction
      | throwError "the original point constructor has no functor action"
    let (inner, target) ← categoricalActionValue state inner application
    let (sourceBundle, targetBundle) ← functorCategoryBundles inner
    let result ← applyConstructorInterface declaration #[sourceBundle, targetBundle] #[inner]
    return (result, .construct id #[.category target])

def sourceDeclarationParameters (declaration : Name) : MetaM (Array Nat) := do
  let info ← getConstInfo declaration
  forallTelescopeReducing info.type fun parameters _ => do
    let mut indices := #[]
    for parameter in parameters, index in [:parameters.size] do
      if (← getFVarLocalDecl parameter).binderInfo.isExplicit && !(← isProof parameter) then
        indices := indices.push index
    return indices

def SourceActionFamily.operation (family : SourceActionFamily) : String :=
  match family.edge with
  | .functor id => id.raw
  | edge => "action:" ++ (CasCatalogue.edgeImageDescriptor edge).compress

opaque SourceActionFamily.explicitParameters (family : SourceActionFamily) :
    MetaM (Array Nat) := sourceDeclarationParameters family.declaration

opaque SourceActionFamily.forEdge (edge : EdgeRef) : MetaM SourceActionFamily :=
    withLCtx {} #[] do
  let state ← semanticState
  let (declaration, references) ← sourceActionSelection state edge
  let info ← checkedDeclaration declaration
  let head := Lean.mkConst declaration (info.levelParams.map Level.param)
  forallTelescopeReducing info.type fun parameters _ => do
    let (functor, category) ← categoricalActionValue state edge (mkAppN head parameters)
    let (source, target) ← functorCategoryBundles functor
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[source]
    let family ← withLocalDeclD `receiver carrier fun receiver => do
      let result ← functorObject functor receiver target (some source)
      mkLambdaFVars (parameters.push receiver) result
        (usedOnly := false) (usedLetOnly := false)
    let family ← instantiateMVars family
    if family.hasMVar || family.hasLevelMVar then
      throwError "the native object action has undetermined complete source parameters"
    check family
    return ⟨edge, declaration, info.levelParams, parameters.size, category,
      family, ← inferType family, references⟩

def SourceActionFamily.instantiate (family : SourceActionFamily) :
    MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

/-- Retain the explicit selected edge and the original receiver of its native object action. -/
def SourceActionFamily.selected (family : SourceActionFamily) (levels : List Level)
    (parameters : Array Expr) (receiver : Expr) : MetaM (SourceSelection Expr) := do
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    throwError "the native object action changed its original complete declaration inputs"
  let expression := mkAppN
    (family.family.instantiateLevelParams family.universeParams levels) (parameters.push receiver)
  check expression
  return {
    value := expression
    originalApplication := some (mkAppN (mkConst family.declaration levels) parameters)
    application := some {
      family := .objectAction family, universes := levels, parameters, arguments := #[receiver] } }

def SourceActionFamily.realized (family : SourceActionFamily) (levels : List Level)
    (parameters : Array Expr) (receiver replacement : Expr) : MetaM Expr := do
  unless family.edge matches .functor _ do
    throwError "a derived edge has no independently selected computation derivation"
  unless levels.length == family.universeParams.length && parameters.size == family.parameterCount do
    throwError "the object derivation lost its complete original declaration inputs"
  let expected := mkAppN (mkConst family.declaration levels) parameters
  checkRegisteredDomains (← inferType replacement) (← inferType expected)
  unless ← isDefEq (← inferType replacement) (← inferType expected) do
    throwError "the object derivation changed its original complete native family"
  let functor ← sourceFunctorValue replacement
  let (source, target) ← functorCategoryBundles functor
  functorObject functor receiver target (some source)

/-- Apply the selected declaration and retain its complete native functor boundary.
An existing receiver category stays fixed. Otherwise the explicitly selected action supplies
its source context, which native object application must check. Explicit functor use admits
each registered role. Reuse: SourceSession.namedFunctor, classifierForgetInstance and
functorCategoryBundles; source: #66, comment 6664276482 §4. -/
opaque viewExpressionsScoped (entry : FunctorEntry ⊕ ClassifierEntry)
    (source : Option (CategoryExpr × Expr))
    (select : SourceSelection Expr → Option Expr → StateCpsT σ TermElabM Expr)
    (application : Expr → StateCpsT σ TermElabM Expr)
    (checkSource : Expr → Expr → StateCpsT σ TermElabM Bool :=
      fun domain selected => liftM (m := MetaM) <| isDefEq domain selected) :
    StateCpsT σ TermElabM NativeSourceView := do
  let (symbolic, target, declaration, reference) := match entry with
    | .inl entry => (entry.source, entry.target, entry.declaration, Sum.inl entry.id)
    | .inr entry => (.classifierTotal entry.id, entry.host, entry.declaration, Sum.inr entry.id)
  if let some (selected, _) := source then
    unless symbolic.syntacticEq selected do
      liftM (m := TermElabM) <|
        throwError (MessageData.tagged `CasCompiler.SourceReader.actionSymbolicSource
          m!"the selected source action has a different complete symbolic source category")
  discard <| checkedDeclaration declaration
  let original ← application (← mkConstWithFreshMVarLevels declaration)
  -- The actual receiver fixes the declared family's parameters before its complete
  -- selected application is captured. In particular, a nullary polymorphic view
  -- obtains its universe from this full category check, without a default.
  let nativeFunctor ← match entry with
    | .inl _ => sourceFunctorValue original
    | .inr _ => sourceClassifierForgetValue original
  let (domain, _) ← functorCategoryBundles nativeFunctor
  if let some (_, selected) := source then
    unless ← checkSource domain selected do
      liftM (m := TermElabM) <|
        throwError (MessageData.tagged `CasCompiler.SourceReader.actionNativeSource
          m!"the selected source action has a different complete native source category; \
            declared={domain}; selected={selected}")
  -- A computation address belongs to this declaration application, before its native
  -- object/map action is formed. It does not scope over declarations in the receiver.
  let selected ← sourceReferenceAt (match entry with
    | .inl entry => .functor entry
    | .inr entry => .classifier entry) original original
  let value ← select selected none
  let functor ← match entry with
    | .inl _ => sourceFunctorValue value
    | .inr _ => sourceClassifierForgetValue value
  let (_, targetBundle) ← functorCategoryBundles functor
  return ⟨reference, declaration, target, functor, targetBundle, original⟩

/-- Ordinary source actions retain the same complete selected native view. -/
opaque viewExpressions (entry : FunctorEntry ⊕ ClassifierEntry)
    (source : Option (CategoryExpr × Expr))
    (application : Expr → SourceReadM Expr) : SourceReadM NativeSourceView := do
  viewExpressionsScoped entry source
    (fun selected expected => SourceReadM.select selected expected) application
    (checkSource := fun domain selected => do
      if ← isDefEq domain selected then return true
      let scope ← get
      -- The whole declared category is checked in the recorded source interpretation.
      -- The actual action and all of its authored parameter bindings stay unchanged.
      withoutModifyingState <| scope.context.withOriginalSources #[domain, selected]
        fun original => isDefEq original[0]! original[1]!)


end CasCompiler
