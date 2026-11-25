module

public import CasCatalogue.Admission
public import CasContract.Port
public import CasCompiler.SourceCell
public import CasCompiler.SourceCartesian
public import CasCompiler.PointPath
public import CasCompiler.PointFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue CasCatalogue.Backend

/-- Original owners of the released categorical point dialect. This is a source selection,
not a registry of additional mathematics or a provider-dependent interpretation. -/
inductive CategoricalPointOwner
  | named (owner : PointFamilyOwner)
  | component (entry : CellEntry) (constructors : Array ConstructorId) (inverse : Bool)
  | cartesian (entry : FunctorEntry)
  | binder (entry : BinderEntry)
  | action (edge : EdgeRef)

def CategoricalPointOwner.operation : CategoricalPointOwner → String
  | .named owner => owner.operation
  | .component entry constructors _ => ConstructedCellComponent.address {
      constructors := constructors.map (·.raw)
      component := { cell := entry.id.raw, parameters := #[], receiver := .null, inverse := false } }
  | .cartesian entry => entry.id.raw ++ "#cartesian"
  | .binder entry => entry.id.raw
  | .action (.functor id) => id.raw ++ "#map"
  | .action edge => "action:" ++ (edgeImageDescriptor edge).compress ++ "#map"

def CategoricalPointOwner.input (owner : CategoricalPointOwner) : String :=
  match owner with
  | .action (.functor id) => id.raw ++ "#input"
  | .action edge => "action:" ++ (edgeImageDescriptor edge).compress ++ "#input"
  | _ => owner.operation

/-- A whole native postcomposition family, under its original rigid parameters. The final
two arguments are an arbitrary object of the actual category and a map from that object to
the selected arrow's source. Constructed categories keep their own complete native bundle. -/
structure CategoricalPointFamily where
  private mk ::
  owner : CategoricalPointOwner
  declaration : Name
  universeParams : List Name
  declarationParameterCount : Nat
  parameterCount : Nat
  category : CategoryExpr
  categoryFamily : Expr
  arrowFamily : Expr
  family : Expr
  familyType : Expr
  whole : Bool := false
  invocation : Bool := true

def CategoricalPointFamily.operation (family : CategoricalPointFamily) : String :=
  family.owner.operation

private def categoryStructure (bundle : Expr) : MetaM (Expr × Expr) := do
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[bundle]
  return (carrier, ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some instanceValue])

/-- Native categorical identity at the caller's actual object. It supplies the whole-arrow
case of the same generalized application; no scalar or terminal convention is substituted. -/
def categoricalPointIdentity (bundle object : Expr) : MetaM Expr := do
  let (carrier, structureValue) ← categoryStructure bundle
  mkAppOptM ``CategoryTheory.CategoryStruct.id #[some carrier, some structureValue, some object]

/-- Read the original native Hom endpoints; no search or declaration identity is inferred. -/
def categoricalPointEndpoints (arrow : Expr) : MetaM (Expr × Expr) := do
  let original ← inferType arrow
  let type ← if original.isAppOfArity ``Quiver.Hom 4 then pure original else whnfR original
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the selected point action requires its complete native Hom interface"
  return (← declaredEndpoint type.getAppArgs[2]!, ← declaredEndpoint type.getAppArgs[3]!)

private def finish (owner : CategoricalPointOwner) (declaration : Name)
    (universes : List Name) (declaredCount : Nat) (parameters : Array Expr)
    (category : CategoryExpr) (bundle arrow : Expr) : MetaM CategoricalPointFamily := do
  let close := fun value => mkLambdaFVars parameters value
    (usedOnly := false) (usedLetOnly := false)
  let (source, target) ← categoricalPointEndpoints arrow
  let (carrier, structureValue) ← categoryStructure bundle
  let family ← withLocalDeclD `pointDomain carrier fun domain => do
    let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
      #[some carrier, some structureValue, some domain, some source, some target]
    let .forallE _ pointType _ _ ← whnfR (← inferType composition)
      | throwError "categorical composition lost its original first map"
    withLocalDeclD `point pointType fun point => do
      let result := mkAppN composition #[point, arrow]
      check result
      mkLambdaFVars (parameters ++ #[domain, point]) result
        (usedOnly := false) (usedLetOnly := false)
  let family ← instantiateMVars family
  let arrowFamily ← instantiateMVars (← close arrow)
  let categoryFamily ← instantiateMVars (← close bundle)
  if family.hasMVar || family.hasLevelMVar || arrowFamily.hasMVar ||
      categoryFamily.hasMVar || categoryFamily.hasLevelMVar then
    throwError "the categorical point family has undetermined native parameters"
  return ⟨owner, declaration, universes, declaredCount, parameters.size, category,
    categoryFamily, arrowFamily, family, ← inferType family, false, true⟩

private partial def actionDeclaration (state : SemanticState) : EdgeRef → MetaM Name
  | .functor id => do
    let some entry := state.functor? id | throwError "the original point functor is absent"
    return entry.declaration
  | .classifierForget id => do
    let some entry := state.classifier? id | throwError "the original point classifier is absent"
    return entry.declaration
  | .constructMap _ inner => actionDeclaration state inner

partial def categoricalActionValue (state : SemanticState) (edge : EdgeRef)
    (application : Expr) : MetaM (Expr × CategoryExpr) := do
  match edge with
  | .functor id =>
    let some entry := state.functor? id | throwError "the original point functor is absent"
    return (← sourceFunctorValue
      (sourceReference ``EdgeRef.functor id.raw entry.declaration application), entry.target)
  | .classifierForget id =>
    let some entry := state.classifier? id | throwError "the original point classifier is absent"
    return (← sourceClassifierForgetValue
      (sourceReference ``ClassifierEntry id.raw entry.declaration application), entry.host)
  | .constructMap id inner =>
    let some entry := state.constructor? id | throwError "the original point constructor is absent"
    unless entry.signature == #[.category] do
      throwError "the derived point action requires the original unary category constructor"
    let some declaration := entry.functorialAction
      | throwError "the original point constructor has no functor action"
    let (inner, target) ← categoricalActionValue state inner application
    let (sourceBundle, targetBundle) ← functorCategoryBundles inner
    let result ← applyConstructorInterface declaration #[sourceBundle, targetBundle] #[inner]
    return (sourceReference ``ConstructorEntry.functorialAction id.raw declaration result,
      .construct id #[.category target])

private def fixedPointCategory (state : SemanticState) (id : CategoryId) (arrow : Expr) :
    MetaM (CategoryExpr × Expr) := do
  let #[category] := state.categories.filter (·.id == id)
    | throwError "the point family lost its original named category"
  let bundleFamily ← nativeCategoryFamily state category.expression fun _ => mkFreshLevelMVar
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType bundleFamily)
  let bundle := mkAppN bundleFamily arguments
  let identity ← categoryIdentity bundle
  let map ← mkAppM ``CategoryTheory.Functor.map #[identity]
  let (inputs, binders, _) ← forallMetaTelescope (← inferType map)
  let some index := binders.findIdx? (·.isExplicit)
    | throwError "the point category identity lost its native arrow slot"
  unless ← isDefEq (← inferType inputs[index]!) (← inferType arrow) do
    throwError "the point arrow has another complete selected category"
  return (category.expression, ← instantiateMVars bundle)

/-- Read the accepted native family before any specialization or runtime availability.
All cases construct ordinary native categorical applications from their original source. -/
opaque CategoricalPointFamily.forOwner (owner : CategoricalPointOwner) :
    MetaM CategoricalPointFamily := withLCtx {} #[] do
  let state ← semanticState
  let declaration ← match owner with
    | .named (.morphism entry) => pure entry.declaration
    | .named (.application entry) => do
      let some declaration := entry.application
        | throwError "the original object has no published application"
      pure declaration
    | .component entry _ _ => pure entry.declaration
    | .cartesian entry => pure entry.declaration
    | .binder entry => pure entry.operation
    | .action edge => actionDeclaration state edge
  let info ← checkedDeclaration declaration
  let head := mkConst declaration (info.levelParams.map Level.param)
  forallTelescopeReducing info.type fun parameters _ => do
    let application := mkAppN head parameters
    match owner with
    | .named selected => do
      let (kind, id) ← match selected with
        | .morphism entry => do
          let #[original] := state.morphisms.filter (·.id == entry.id)
            | throwError "the point family lost its original morphism row"
          unless original.declaration == declaration && original.category == entry.category do
            throwError "the point family changed its original morphism owner"
          pure (``MorphismEntry, entry.id.raw)
        | .application entry => do
          let #[original] := state.objects.filter (·.id == entry.id)
            | throwError "the point family lost its original application row"
          unless original.declaration == entry.declaration &&
              original.category == entry.category && original.application == some declaration do
            throwError "the point family changed its original application owner"
          pure (``ObjectEntry.application, entry.id.raw)
      let (category, bundle) ← fixedPointCategory state selected.category application
      finish owner declaration info.levelParams parameters.size parameters category bundle
        (sourceReference kind id declaration application)
    | .component entry constructors inverse =>
      let mut cell ← nativeSourceCell entry application inverse
      for constructor in constructors.reverse do cell ← cell.construct constructor
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[cell.sourceBundle]
      withLocalDeclD `receiver carrier fun receiver => do
        let arrow ← cell.component ⟨receiver, none⟩
        finish owner declaration info.levelParams parameters.size (parameters.push receiver)
          cell.target cell.targetBundle arrow.value
    | .cartesian entry =>
      let .familyReindex family := entry.expression.registrationKind
        | throwError "the cartesian point family is not a reindexing"
      let (source, _) ← functorCategoryBundles (← sourceFunctorValue application)
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[source]
      withLocalDeclD `receiver carrier fun receiver => do
        let arrow ← sourceCartesian entry application receiver
        let some original ← sourceCartesian? arrow
          | throwError "the cartesian point family lost its complete native source"
        finish owner declaration info.levelParams parameters.size (parameters.push receiver)
          (.familyTotal family) original.totalBundle arrow
    | .binder entry =>
      let #[original] := state.binders.filter (·.id == entry.id)
        | throwError "the binder point family requires its exact accepted row"
      unless original.operation == entry.operation && original.category == entry.category do
        throwError "the binder point family changed its accepted declaration or category"
      let (category, bundle) ← fixedPointCategory state entry.category application
      finish owner declaration info.levelParams parameters.size parameters category bundle
        (sourceReference ``BinderEntry entry.id.raw declaration application)
    | .action edge =>
      let (functor, category) ← categoricalActionValue state edge application
      let (sourceBundle, targetBundle) ← functorCategoryBundles functor
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[sourceBundle]
      withLocalDeclD `sourceObject carrier fun source =>
        withLocalDeclD `targetObject carrier fun target => do
          let map ← mkAppOptM ``CategoryTheory.Functor.map
            #[none, none, none, none, some functor, some source, some target]
          let .forallE _ arrowType _ _ ← whnfR (← inferType map)
            | throwError "the functor point action lost its complete native arrow"
          withLocalDeclD `sourceArrow arrowType fun arrow => do
            let mapped := mkApp map arrow
            finish owner declaration info.levelParams parameters.size
              (parameters ++ #[source, target, arrow]) category targetBundle mapped

def CategoricalPointFamily.instantiate (family : CategoricalPointFamily) :
    MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

/-- Preserve the actual native arrow in the whole-map case. The original domain and
identity-point slots remain explicit request inputs; no category law replaces the result
by a propositionally equal composite. -/
opaque CategoricalPointFamily.asWhole (family : CategoricalPointFamily) :
    MetaM CategoricalPointFamily := withLCtx {} #[] do
  if family.whole then return family
  let expression ← forallTelescopeReducing family.familyType fun inputs _ => do
    unless inputs.size == family.parameterCount + 2 do
      throwError "the whole point family lost its complete original input telescope"
    let arrow := mkAppN family.arrowFamily (inputs.extract 0 family.parameterCount)
    mkLambdaFVars inputs arrow (usedOnly := false) (usedLetOnly := false)
  check expression
  return { family with family := expression, familyType := ← inferType expression, whole := true }

/-- Formation of a native arrow retains its callable family, as formation of a named
morphism does. A later actual point or explicit whole-map request supplies the demand. -/
opaque CategoricalPointFamily.asReference (family : CategoricalPointFamily) :
    MetaM CategoricalPointFamily := do
  let familyType ← inferType family.arrowFamily
  return { family with
    family := family.arrowFamily
    familyType
    whole := true
    invocation := false }

/-- The exact selected arrow and complete category at the caller's original parameter slots. -/
def CategoricalPointFamily.arrowAt (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) : MetaM (Expr × Expr) := do
  unless levels.length == family.universeParams.length && parameters.size == family.parameterCount do
    throwError "the categorical point changed its original complete parameter telescope"
  let arrow := mkAppN (family.arrowFamily.instantiateLevelParams family.universeParams levels) parameters
  let category := mkAppN (family.categoryFamily.instantiateLevelParams family.universeParams levels) parameters
  return (arrow.headBeta, category.headBeta)

/-- A scalar continuation exists only when the accepted whole category has a native carrier
action on this exact arrow field. Full categorical maps do not require such a carrier. -/
def CategoricalPointFamily.carrierFamily? (family : CategoricalPointFamily) :
    MetaM (Option NativePointFamily) := do
  let routes ← SourceRoutes.forOwner family.category (.atom CategoryId.sets)
  let some candidates ← routes.finiteRoutes | return none
  if candidates.isEmpty then return none
  try
    return some (← NativePointFamily.prepare family.family family.universeParams
      fun parameters _ => do
        let bundle := (mkAppN family.categoryFamily
          (parameters.extract 0 family.parameterCount)).headBeta
        return ⟨.morphism, family.category, bundle, none, none⟩)
  catch error =>
    if CasCatalogue.Exception.isUnsupportedSource error ||
        CasCatalogue.Exception.isSemanticAmbiguity error then return none
    throw error

/-- The original complete native carrier action, when the caller has already checked its
whole-family path. It never manufactures a named category for a constructed bundle. -/
def CategoricalPointFamily.function (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow : Expr) : MetaM Expr := do
  let (_, bundle) ← family.arrowAt levels parameters
  sourceFunction ⟨arrow, some ⟨.morphism, family.category, bundle, none, none⟩⟩

/-- Invocation-local original descriptors retained at the typed generalized map. Their
runtime marks can refer to the original supplied values; they never choose a source family. -/
structure CategoricalPointRequest where
  arrow : Expr
  domain : Expr
  source : Expr
  target : Expr
  point : Expr

/-- Project a checked replacement of the original declared family through the same native
arrow producer. The runtime supplies its selected checked derivation; this function preserves
that term and every prerequisite marker, and validates only its already fixed source type. -/
def CategoricalPointFamily.realizedArrow (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (replacement : Expr) : MetaM Expr := do
  let (expected, _) ← family.arrowAt levels parameters
  let declaration := mkAppN (mkConst family.declaration levels)
    (parameters.extract 0 family.declarationParameterCount)
  checkRegisteredDomains (← inferType replacement) (← inferType declaration)
  unless ← isDefEq (← inferType replacement) (← inferType declaration) do
    throwError "the selected derivation changed its original complete declaration family"
  let value ← match family.owner with
    | .named _ => pure replacement
    | .action (.functor _) => do
      let functor ← sourceFunctorValue replacement
      mkAppOptM ``CategoryTheory.Functor.map #[none, none, none, none, some functor,
        some parameters[family.declarationParameterCount]!,
        some parameters[family.declarationParameterCount + 1]!,
        some parameters[family.declarationParameterCount + 2]!]
    | _ => throwError "the selected point owner has no checked computation derivation"
  checkRegisteredDomains (← inferType value) (← inferType expected)
  unless ← isDefEq (← inferType value) (← inferType expected) do
    throwError "the selected derivation changed its original native arrow interface"
  return value

/-- The ordinary native postcomposition at the fixed complete category. Whole requests
preserve their original arrow; generalized requests retain the supplied domain and point. -/
def CategoricalPointFamily.resultAt (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow domain point : Expr) : MetaM Expr := do
  let (expected, bundle) ← family.arrowAt levels parameters
  checkRegisteredDomains (← inferType arrow) (← inferType expected)
  unless ← isDefEq (← inferType arrow) (← inferType expected) do
    throwError "the point result changed its complete selected native arrow type"
  if family.whole then return arrow
  let (source, target) ← categoricalPointEndpoints arrow
  let (carrier, structureValue) ← categoryStructure bundle
  mkAppOptM ``CategoryTheory.CategoryStruct.comp #[some carrier, some structureValue,
    some domain, some source, some target, some point, some arrow]

def CategoricalPointFamily.withRequest (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow domain source target point : Expr) : MetaM Expr := do
  let (expectedArrow, _) ← family.arrowAt levels parameters
  let (expectedSource, expectedTarget) ← categoricalPointEndpoints expectedArrow
  let (expectedDomain, pointTarget) ← categoricalPointEndpoints point
  checkRegisteredDomains domain expectedDomain
  checkRegisteredDomains source expectedSource
  checkRegisteredDomains target expectedTarget
  checkRegisteredDomains pointTarget expectedSource
  unless ← isDefEq arrow expectedArrow <&&> isDefEq domain expectedDomain <&&>
      isDefEq source expectedSource <&&> isDefEq target expectedTarget <&&>
      isDefEq pointTarget expectedSource do
    throwError "the generalized point changed its complete original native inputs"
  let mut body := point
  for input in #[arrow, domain, source, target] do
    body ← mkAppM ``Function.const #[← inferType input, body, input]
  return .mdata (KVMap.empty.setString `CasCompiler.source.categoricalPointRequest
    family.operation) body

/-- The scalar carrier case retains the original reader-authored generalized point and the
same complete categorical arrow. Its domain is that point's domain, independently of the
category object that is the original arrow's source. -/
def CategoricalPointFamily.withScalarRequest (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow domain source target point : Expr) : MetaM Expr := do
  let (expectedArrow, _) ← family.arrowAt levels parameters
  let (expectedSource, expectedTarget) ← categoricalPointEndpoints expectedArrow
  let some original ← sourcePointOrigin? point
    | throwError "a scalar categorical request requires its original generalized point"
  let function ← family.function levels parameters expectedArrow
  let .forallE _ expected _ _ ← whnfR (← inferType function)
    | throwError "the categorical arrow has no original scalar carrier interface"
  checkRegisteredDomains (← inferType point) expected
  checkRegisteredDomains domain original.domain
  checkRegisteredDomains source expectedSource
  checkRegisteredDomains target expectedTarget
  unless ← isDefEq (← inferType point) expected <&&> isDefEq arrow expectedArrow <&&>
      isDefEq domain original.domain <&&> isDefEq source expectedSource <&&>
      isDefEq target expectedTarget do
    throwError "the scalar categorical request changed its original complete native inputs"
  let mut body := point
  for input in #[arrow, domain, source, target] do
    body ← mkAppM ``Function.const #[← inferType input, body, input]
  return .mdata (KVMap.empty.setString `CasCompiler.source.categoricalPointRequest
    family.operation) body

partial def CategoricalPointFamily.request? (family : CategoricalPointFamily) (point : Expr) :
    MetaM (Option CategoricalPointRequest) := do
  let .mdata data body := point | return none
  let address := data.getString `CasCompiler.source.categoricalPointRequest
  if address.isEmpty then return ← family.request? body
  unless address == family.operation do
    throwError "the retained generalized point changed its selected operation"
  let mut current := body
  let mut fields := #[]
  for _ in [:4] do
    unless current.isAppOfArity ``Function.const 4 do
      throwError "the retained generalized point lost an original input"
    fields := fields.push current.getAppArgs[3]!
    current := current.getAppArgs[2]!
  let #[target, source, domain, arrow] := fields
    | throwError "the retained generalized point changed its native input layout"
  return some ⟨arrow, domain, source, target, current⟩

private def pointDeclarationParameters (declaration : Name) : MetaM (Array Nat) := do
  let info ← getConstInfo declaration
  forallTelescopeReducing info.type fun parameters _ => do
    let mut indices := #[]
    for parameter in parameters, index in [:parameters.size] do
      if (← getFVarLocalDecl parameter).binderInfo.isExplicit && !(← isProof parameter) then
        indices := indices.push index
    return indices

/-- Original explicit nonproof declaration slots in the released parameter array. -/
opaque CategoricalPointFamily.explicitParameters (family : CategoricalPointFamily) :
    MetaM (Array Nat) := pointDeclarationParameters family.declaration

/-- Keep the original native declaration application beside a fully formed generalized
application. The marker selects its accepted owner before any source reduction. -/
def CategoricalPointFamily.mark (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (domain point : Expr) (whole : Bool := false) : MetaM Expr := do
  let family ← if whole then family.asWhole else pure family
  let (arrow, bundle) ← family.arrowAt levels parameters
  if family.whole then
    let (source, _) ← categoricalPointEndpoints arrow
    checkRegisteredDomains domain source
    unless ← isDefEq domain source <&&>
        isDefEq point (← categoricalPointIdentity bundle source) do
      throwError "the whole native arrow requires its original source and identity point"
  let arguments := if family.invocation then parameters ++ #[domain, point] else parameters
  let expression := mkAppN
    (family.family.instantiateLevelParams family.universeParams levels) arguments
  check expression
  let application := mkAppN (mkConst family.declaration levels)
    (parameters.extract 0 family.declarationParameterCount)
  let body ← mkAppM ``Function.const #[← inferType application, expression, application]
  let inverse := match family.owner with | .component _ _ inverse => inverse | _ => false
  let owner := match family.owner with
    | .named .. => ``CategoricalPointOwner.named
    | .component .. => ``CategoricalPointOwner.component
    | .cartesian .. => ``CategoricalPointOwner.cartesian
    | .binder .. => ``CategoricalPointOwner.binder
    | .action .. => ``CategoricalPointOwner.action
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``CategoricalPointFamily
    |>.setString `CasCompiler.source.id family.operation
    |>.setName `CasCompiler.source.declaration family.declaration
    |>.setName `CasCompiler.source.application family.declaration
    |>.setName `CasCompiler.source.point.owner owner
    |>.setBool `CasCompiler.source.point.inverse inverse
    |>.setBool `CasCompiler.source.point.whole family.whole
    |>.setBool `CasCompiler.source.point.reference (!family.invocation)) body

/-- Read only the retained complete application slots. Native conversion validates the
already selected whole family; it cannot select another owner or replace any argument. -/
def CategoricalPointFamily.application (family : CategoricalPointFamily) (body : Expr) :
    MetaM (List Level × Array Expr) := do
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the source generalized point lost its original application witness"
  let original := body.getAppArgs[3]!
  let .const declaration levels := original.getAppFn
    | throwError "the source generalized point lost its original declaration"
  unless declaration == family.declaration &&
      original.getAppNumArgs == family.declarationParameterCount do
    throwError "the source generalized point changed its original declaration telescope"
  let applied := body.getAppArgs[2]!
  let arguments := applied.getAppArgs
  unless arguments.size == family.parameterCount + (if family.invocation then 2 else 0) &&
      arguments.extract 0 family.declarationParameterCount == original.getAppArgs do
    throwError "the source generalized point replaced its actual original arguments"
  unless ← isDefEq applied.getAppFn
      (family.family.instantiateLevelParams family.universeParams levels) do
    throwError "the source generalized point changed its complete native family"
  if family.whole && family.invocation then
    let parameters := arguments.extract 0 family.parameterCount
    let (arrow, bundle) ← family.arrowAt levels parameters
    let (source, _) ← categoricalPointEndpoints arrow
    unless ← isDefEq arguments[family.parameterCount]! source <&&>
        isDefEq arguments[family.parameterCount + 1]!
          (← categoricalPointIdentity bundle source) do
      throwError "the whole native source replaced its original identity-point request"
  return (levels, arguments)

/-- The object action of one explicitly selected complete native edge. Its body is the
same functorObject application used by ordinary source views; the retained edge only fixes
the public operation that a provider may implement. -/
structure SourceActionFamily where
  private mk ::
  edge : EdgeRef
  declaration : Name
  universeParams : List Name
  parameterCount : Nat
  category : CategoryExpr
  family : Expr
  familyType : Expr

def SourceActionFamily.operation (family : SourceActionFamily) : String :=
  match family.edge with
  | .functor id => id.raw
  | edge => "action:" ++ (edgeImageDescriptor edge).compress

opaque SourceActionFamily.explicitParameters (family : SourceActionFamily) :
    MetaM (Array Nat) := pointDeclarationParameters family.declaration

opaque SourceActionFamily.forEdge (edge : EdgeRef) : MetaM SourceActionFamily :=
    withLCtx {} #[] do
  let state ← semanticState
  let declaration ← actionDeclaration state edge
  let info ← checkedDeclaration declaration
  let head := mkConst declaration (info.levelParams.map Level.param)
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
      family, ← inferType family⟩

def SourceActionFamily.instantiate (family : SourceActionFamily) :
    MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

def SourceActionFamily.mark (family : SourceActionFamily) (levels : List Level)
    (parameters : Array Expr) (receiver : Expr) : MetaM Expr := do
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    throwError "the native object action changed its original complete declaration inputs"
  let expression := mkAppN
    (family.family.instantiateLevelParams family.universeParams levels) (parameters.push receiver)
  check expression
  let application := mkAppN (mkConst family.declaration levels) parameters
  let body ← mkAppM ``Function.const #[← inferType application, expression, application]
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``SourceActionFamily
    |>.setString `CasCompiler.source.id family.operation
    |>.setName `CasCompiler.source.declaration family.declaration
    |>.setName `CasCompiler.source.application family.declaration) body

def SourceActionFamily.application (family : SourceActionFamily) (body : Expr) :
    MetaM (List Level × Array Expr) := do
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the native object action lost its original declaration witness"
  let original := body.getAppArgs[3]!
  let .const declaration levels := original.getAppFn
    | throwError "the native object action lost its selected declaration"
  let applied := body.getAppArgs[2]!
  let arguments := applied.getAppArgs
  unless declaration == family.declaration && original.getAppNumArgs == family.parameterCount &&
      arguments.size == family.parameterCount + 1 &&
      arguments.extract 0 family.parameterCount == original.getAppArgs do
    throwError "the native object action replaced an original declaration argument or receiver"
  unless ← isDefEq applied.getAppFn
      (family.family.instantiateLevelParams family.universeParams levels) do
    throwError "the object request changed its selected complete native action"
  return (levels, arguments)

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

end CasCompiler
