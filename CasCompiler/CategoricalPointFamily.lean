module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCatalogue.Admission
public import CasContract.Port
public import CasCompiler.SourceCell
public import CasCompiler.SourceCartesian
public import CasCompiler.PointPath
public import CasCompiler.PointFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue CasCatalogue.Backend


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


def CategoricalPointFamily.operation (family : CategoricalPointFamily) : String :=
  family.owner.operation

private def categoryStructure (bundle : Expr) : MetaM (Expr × Expr) := do
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[bundle]
  return (carrier, ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some instanceValue])



def categoricalPointIdentity (bundle object : Expr) : MetaM Expr := do
  let (carrier, structureValue) ← categoryStructure bundle
  mkAppOptM ``CategoryTheory.CategoryStruct.id #[some carrier, some structureValue, some object]


def categoricalPointEndpoints (arrow : Expr) : MetaM (Expr × Expr) := do
  let original ← inferType arrow
  let type ← if original.isAppOfArity ``Quiver.Hom 4 then pure original else whnfR original
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the selected point action requires its complete native Hom interface"
  return (← declaredEndpoint type.getAppArgs[2]!, ← declaredEndpoint type.getAppArgs[3]!)

private def finish (owner : CategoricalPointOwner) (declaration : Name)
    (universes : List Name) (declaredCount : Nat) (parameters : Array Expr)
    (category : CategoryExpr) (bundle arrow : Expr)
    (references : Array SelectedSourceReference)
    (component : Option NativeSourceCellComponent := none)
    (cartesian : Option NativeSourceCartesian := none) : MetaM CategoricalPointFamily := do
  let close := fun value => do
    let value ← instantiateMVars (← mkLambdaFVars parameters value
      (usedOnly := false) (usedLetOnly := false))
    if value.hasFVar || value.hasMVar || value.hasLevelMVar then
      throwError "the categorical point template lost its complete original parameter scope"
    check value
    return value
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
    categoryFamily, arrowFamily, family, ← inferType family, false, true, references,
    ← component.mapM (·.mapM close), ← cartesian.mapM (·.mapM close)⟩

private def fixedPointCategory (state : SemanticState) (id : CategoryId) (arrow : Expr) :
    MetaM (NamedCategoryEntry × Expr) := do
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
  return (category, ← instantiateMVars bundle)



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
    | .action edge => sourceActionDeclaration state edge
  let info ← checkedDeclaration declaration
  let head := mkConst declaration (info.levelParams.map Level.param)
  forallTelescopeReducing info.type fun parameters _ => do
    let application := mkAppN head parameters
    match owner with
    | .named selected => do
      match selected with
        | .morphism entry => do
          let #[original] := state.morphisms.filter (·.id == entry.id)
            | throwError "the point family lost its original morphism row"
          unless reprStr original == reprStr entry do
            throwError "the point family changed its original morphism owner"
        | .application entry => do
          let #[original] := state.objects.filter (·.id == entry.id)
            | throwError "the point family lost its original application row"
          unless reprStr original == reprStr entry do
            throwError "the point family changed its original application owner"
      let (category, bundle) ← fixedPointCategory state selected.category application
      let reference := match selected with
        | .morphism entry => SelectedSourceReference.named (.registered (.inr entry) category)
        | .application entry => SelectedSourceReference.named (.registered (.inl entry) category)
      finish owner declaration info.levelParams parameters.size parameters category.expression bundle
        application #[reference]
    | .component entry constructors inverse =>
      let mut cell ← nativeSourceCell entry application inverse
      for constructor in constructors.reverse do cell ← cell.construct constructor
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[cell.sourceBundle]
      withLocalDeclD `receiver carrier fun receiver => do
        let arrow ← cell.component ⟨receiver, none⟩
        let some original := arrow.cell
          | throwError "the component point family lost its complete native source"
        finish owner declaration info.levelParams parameters.size (parameters.push receiver)
          cell.target cell.targetBundle arrow.value cell.references (some original)
    | .cartesian entry =>
      let .familyReindex family := entry.expression.registrationKind
        | throwError "the cartesian point family is not a reindexing"
      let (source, _) ← functorCategoryBundles (← sourceFunctorValue application)
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[source]
      withLocalDeclD `receiver carrier fun receiver => do
        let arrow ← sourceCartesian entry application receiver
        let some original := arrow.cartesian
          | throwError "the cartesian point family lost its complete native source"
        finish owner declaration info.levelParams parameters.size (parameters.push receiver)
          (.familyTotal family) original.totalBundle arrow.value #[.functor entry]
            none (some original)
    | .binder entry =>
      let #[original] := state.binders.filter (·.id == entry.id)
        | throwError "the binder point family requires its exact accepted row"
      unless reprStr original == reprStr entry do
        throwError "the binder point family changed its accepted declaration or category"
      let (category, bundle) ← fixedPointCategory state entry.category application
      finish owner declaration info.levelParams parameters.size parameters category.expression bundle
        application #[.binder entry, .category category]
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
                (← sourceActionReferences state edge)

def CategoricalPointFamily.instantiate (family : CategoricalPointFamily) :
    MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)




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



opaque CategoricalPointFamily.asReference (family : CategoricalPointFamily) :
    MetaM CategoricalPointFamily := do
  let familyType ← inferType family.arrowFamily
  return { family with
    family := family.arrowFamily
    familyType
    whole := true
    invocation := false }


def CategoricalPointFamily.arrowAt (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) : MetaM (Expr × Expr) := do
  unless levels.length == family.universeParams.length && parameters.size == family.parameterCount do
    throwError "the categorical point changed its original complete parameter telescope"
  let arrow := mkAppN (family.arrowFamily.instantiateLevelParams family.universeParams levels) parameters
  let category := mkAppN (family.categoryFamily.instantiateLevelParams family.universeParams levels) parameters
  return (arrow.headBeta, category.headBeta)



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



def CategoricalPointFamily.function (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow : Expr) : MetaM Expr := do
  let (_, bundle) ← family.arrowAt levels parameters
  sourceFunction ⟨arrow, some ⟨.morphism, family.category, bundle, none, none⟩⟩





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
    (parameters : Array Expr) (arrow domain source target point : Expr)
    (context : Option OpenContext := none) : MetaM (SourceSelection Expr) := do
  let (expectedArrow, _) ← family.arrowAt levels parameters
  let (expectedSource, expectedTarget) ← categoricalPointEndpoints expectedArrow
  let (expectedDomain, pointTarget) ← categoricalPointEndpoints point
  let inputs := #[arrow, domain, source, target, pointTarget,
    expectedArrow, expectedDomain, expectedSource, expectedTarget]
  let check : Array Expr → MetaM Unit := fun inputs => do
    checkRegisteredDomains inputs[1]! inputs[6]!
    checkRegisteredDomains inputs[2]! inputs[7]!
    checkRegisteredDomains inputs[3]! inputs[8]!
    checkRegisteredDomains inputs[4]! inputs[7]!
    unless ← isDefEq inputs[0]! inputs[5]! <&&> isDefEq inputs[1]! inputs[6]! <&&>
        isDefEq inputs[2]! inputs[7]! <&&> isDefEq inputs[3]! inputs[8]! <&&>
        isDefEq inputs[4]! inputs[7]! do
      throwError "the generalized point changed its complete original native inputs"
  match context with
  | some context => context.withOriginalSources inputs check
  | none => check inputs
  return { value := point, pointRequest := some (.categorical family
    ⟨arrow, domain, source, target, point⟩) }


def CategoricalPointFamily.checkScalarRequest (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow domain source target point originalDomain : Expr)
    (context : Option OpenContext := none) : MetaM Unit := do
  let (expectedArrow, _) ← family.arrowAt levels parameters
  let (expectedSource, expectedTarget) ← categoricalPointEndpoints expectedArrow
  let function ← family.function levels parameters expectedArrow
  let .forallE _ expected _ _ ← whnfR (← inferType function)
    | throwError "the categorical arrow has no original scalar carrier interface"
  let inputs := #[← inferType point, arrow, domain, source, target,
    expected, expectedArrow, originalDomain, expectedSource, expectedTarget]
  let check : Array Expr → MetaM Unit := fun inputs => do
    checkRegisteredDomains inputs[0]! inputs[5]!
    checkRegisteredDomains inputs[2]! inputs[7]!
    checkRegisteredDomains inputs[3]! inputs[8]!
    checkRegisteredDomains inputs[4]! inputs[9]!
    unless ← isDefEq inputs[0]! inputs[5]! <&&> isDefEq inputs[1]! inputs[6]! <&&>
        isDefEq inputs[2]! inputs[7]! <&&> isDefEq inputs[3]! inputs[8]! <&&>
        isDefEq inputs[4]! inputs[9]! do
      throwError "the scalar categorical request changed its original complete native inputs"
  match context with
  | some context => context.withOriginalSources inputs check
  | none => check inputs


def CategoricalPointFamily.withScalarRequest (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (arrow domain source target : Expr) (point : SourceSelection Expr)
    (context : Option OpenContext := none) : MetaM (SourceSelection Expr) := do
  let some original := point.pointOrigin
    | throwError "a scalar categorical request requires its original generalized point"
  family.checkScalarRequest levels parameters arrow domain source target point.value original.domain context
  return { point with pointRequest := some (.categorical family
    ⟨arrow, domain, source, target, point.value⟩) }


opaque CategoricalPointFamily.explicitParameters (family : CategoricalPointFamily) :
    MetaM (Array Nat) := sourceDeclarationParameters family.declaration



def CategoricalPointFamily.selected (family : CategoricalPointFamily) (levels : List Level)
    (parameters : Array Expr) (domain : Expr) (point : SourceSelection Expr)
    (whole : Bool := false) (context : Option OpenContext := none) :
    MetaM (SourceSelection Expr) := do
  let originalFamily := family
  let family ← if whole then family.asWhole else pure family
  let (arrow, bundle) ← family.arrowAt levels parameters
  if family.whole then
    let (source, _) ← categoricalPointEndpoints arrow
    let inputs := #[domain, source, point.value, ← categoricalPointIdentity bundle source]
    let check : Array Expr → MetaM Unit := fun inputs => do
      checkRegisteredDomains inputs[0]! inputs[1]!
      unless ← isDefEq inputs[0]! inputs[1]! <&&> isDefEq inputs[2]! inputs[3]! do
        throwError "the whole native arrow requires its original source and identity point"
    match context with
    | some context => context.withOriginalSources inputs check
    | none => check inputs
  let arguments := if family.invocation then #[domain, point.value] else #[]
  let expression := mkAppN
    (family.family.instantiateLevelParams family.universeParams levels) (parameters ++ arguments)
  check expression
  let original := mkAppN (mkConst family.declaration levels)
    (parameters.extract 0 family.declarationParameterCount)
  let pointRequest ← match point.pointRequest with
    | none => pure none
    | some (.categorical selected request) => do
      unless (SelectedApplicationFamily.point originalFamily).exactlyMatches (.point selected) do
        throwError "the point request changed its original selected family"
      pure (some (.categorical family request))
    | some (.named ..) =>
      throwError "a categorical point application requires its original categorical input record"
  return {
    value := expression
    originalApplication := some original
    application := some { family := .point family, universes := levels, parameters, arguments }
    category := some ⟨.morphism, family.category, bundle, none, none⟩
    pointRequest }



def CategoricalPointFamily.arrowSelection (family : CategoricalPointFamily)
    (levels : List Level) (parameters : Array Expr) : MetaM (SourceSelection Expr) := do
  let (arrow, bundle) ← family.arrowAt levels parameters
  let instantiate := fun template => do
    let value := (mkAppN
      (template.instantiateLevelParams family.universeParams levels) parameters).headBeta
    check value
    return value
  let component ← family.componentTemplate.mapM (·.mapM instantiate)
  let cartesian ← family.cartesianTemplate.mapM (·.mapM instantiate)
  let (source, target) ← categoricalPointEndpoints arrow
  let identity ← categoricalPointIdentity bundle source
  let selected ← if (← family.carrierFamily?).isSome then family.asReference else family.asWhole
  let point ← selected.withRequest levels parameters arrow source source target identity
  let result ← selected.selected levels parameters source point
  return { result with value := arrow, cell := component, cartesian }



def NativeSourceCell.selectedComponent (cell : NativeSourceCell)
    (receiver : NativeSourceJudgement) : MetaM (SourceSelection Expr) := do
  let original ← cell.component receiver
  let some originalComponent := original.cell
    | throwError "the selected component lost its complete original cell"
  let application := cell.application.consumeMData
  let .const declaration levels := application.getAppFn
    | throwError "the selected cell lost its original declared application"
  let family ← CategoricalPointFamily.forOwner
    (.component cell.entry cell.constructors cell.inverse)
  unless declaration == family.declaration &&
      application.getAppNumArgs == family.declarationParameterCount do
    throwError "the selected cell changed its complete original declaration telescope"
  let parameters := application.getAppArgs.push receiver.value
  let prepared ← family.arrowSelection levels parameters
  let some expectedComponent := prepared.cell
    | throwError "the component family lost its original checked native template"
  let originalData : SourceSelection Expr := { value := original.value, cell := some originalComponent }
  let expectedData : SourceSelection Expr := { value := prepared.value, cell := some expectedComponent }
  unless originalData.exactlyMatches (fun _ _ => true) expectedData do
    throwError "the selected component changed an original cell, route, or constructor row"
  let terms := fun (component : NativeSourceCellComponent Expr) =>
    ((component.mapM fun term => do
      modify (·.push term)
      pure ()) : StateM (Array Expr) (NativeSourceCellComponent Unit)).run #[] |>.2
  let originalTerms := terms originalComponent
  let expectedTerms := terms expectedComponent
  unless originalTerms.size == expectedTerms.size do
    throwError "the selected component changed its complete native field table"
  for originalTerm in originalTerms, expectedTerm in expectedTerms do
    unless ← isDefEq originalTerm expectedTerm do
      throwError "the selected component changed an original native cell field"
  let some application := prepared.application
    | throwError "the selected component lost its original point application"
  let .point selected := application.family
    | throwError "the selected component changed its original point owner"
  let (source, target) ← categoricalPointEndpoints original.value
  let identity ← categoricalPointIdentity cell.targetBundle source
  let point ← selected.withRequest levels parameters original.value source source target identity
  let arguments := if selected.invocation then #[source, identity] else #[]
  return { original with
    application := some { application with arguments }
    pointRequest := point.pointRequest }

end CasCompiler
