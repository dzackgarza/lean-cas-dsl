module

public import CasCompiler.Context
public import CasCompiler.LimitInterface
public import CasCompiler.CreationInterface
public import LeanCategories.Catalogue.Registry.Computation
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Lift
public import LeanCategories.Catalogue.Constructors
public import CasContract.Port

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue CasCatalogue.Backend

inductive SourceNamedEntry where
  | registered (entry : ObjectEntry ⊕ MorphismEntry) (category : NamedCategoryEntry)
  | construction (entry : ConstructionEntry)


inductive SelectedConstructorInterface
  | functorialAction
  | comparisonAction
  | identityComparison
  | compositionComparison
  deriving BEq, Repr


inductive SelectedSourceReference
  | named (entry : SourceNamedEntry)
  | category (entry : NamedCategoryEntry)
  | operation (entry : OperationEntry)
  | method (entry : MethodEntry) (functor : FunctorEntry)
  | functor (entry : FunctorEntry)
  | classifier (entry : ClassifierEntry)
  | constructor (entry : ConstructorEntry)
  | cell (entry : CellEntry)
  | binder (entry : BinderEntry)
  | lift (entry : LiftEntry)
  | presentation (entry : PresentationComparisonEntry)
  | literal (entry : LiteralEntry)
  | numeral (entry : NumeralEntry)
  | subset (entry : SubsetLiteralEntry)
  | graph (entry : GraphLiteralEntry)
  | generator (entry : ObjectEntry)
  | components (entry : ObjectEntry)
  | limit (entry : LimitEntry)
  | constructorInterface (entry : ConstructorEntry) (field : SelectedConstructorInterface)
  | refinement (entry : ObjectEntry) (refinement : ObjectRefinement)
  | classifierForget (entry : ClassifierEntry)



structure NativePowerObject (term : Type := Expr) where
  row : PowerObjectEntry
  object : ObjectEntry
  category : NamedCategoryEntry
  base : term

inductive SourceCategoryRole where
  | object
  | morphism
  deriving BEq



structure SourceCarrierSelection where
  refs : Array CasCatalogue.EdgeRef
  target : CasCatalogue.CategoryExpr
  identifications : Array Name
  actions : Array ClosedTerm
  comparisons : Array ClosedTerm

structure NativeSourceCarrierSelection (term : Type := Expr) where
  refs : Array CasCatalogue.EdgeRef
  target : CasCatalogue.CategoryExpr
  identifications : Array Name
  actions : Array term
  comparisons : Array term



structure SourceLimitSelection where
  row : String
  declaration : Name
  cone : ClosedTerm
  colimit : Bool
  category : CasCatalogue.CategoryExpr
  bundle : ClosedTerm
  presentation : ClosedTerm
  diagram : ClosedTerm
  interface : LimitInterface ClosedTerm

  construction : Name


  ownerFamily : Option ClosedTerm := none

  creation : Option (LimitCreationInterface ClosedTerm) := none

  creationFamily : Option ClosedTerm := none

  creationInputs : Array Nat := #[]

structure NativeSourceLimitSelection (term : Type := Expr) where
  row : String
  declaration : Name
  cone : term
  colimit : Bool
  category : CasCatalogue.CategoryExpr
  bundle : term
  presentation : term
  diagram : term
  interface : LimitInterface term
  construction : Name
  ownerFamily : Option term := none
  creation : Option (LimitCreationInterface term) := none
  creationFamily : Option term := none
  creationInputs : Array Nat := #[]


structure SourceCategoryBinding where
  private mk ::
  expression : CasCatalogue.CategoryExpr
  bundle : ClosedTerm
  role : SourceCategoryRole
  carrier : Option SourceCarrierSelection := none
  limit : Option SourceLimitSelection := none


structure NativeSourceCategory (term : Type := Expr) where
  role : SourceCategoryRole
  expression : CasCatalogue.CategoryExpr
  bundle : term
  carrier : Option (NativeSourceCarrierSelection term) := none
  limit : Option (NativeSourceLimitSelection term) := none


structure NativeSourceElementOwner (term : Type := Expr) where
  category : NativeSourceCategory term
  value : term
  evidence : term


structure NativeSourceTypeOrigin (term : Type := Expr) where
  category : NativeSourceCategory term
  object : term
  type : term



structure NativeSourcePointOrigin (term : Type := Expr) where
  private mk ::
  point : term
  domain : term
  target : term

structure NativeRouteFunctor (term : Type := Expr) where
  functor : term
  target : term
  actions : Array term




structure NativeSourceCell (term : Type := Expr) where
  entry : CellEntry
  application : term
  inverse : Bool
  constructors : Array ConstructorId := #[]
  source : CategoryExpr
  sourceBundle : term
  target : CategoryExpr
  targetBundle : term
  left : NativeRouteFunctor term
  right : NativeRouteFunctor term
  transformation : term
  isomorphism : Option term
  references : Array SelectedSourceReference := #[]



structure NativeSourceCellComponent (term : Type := Expr) where
  private mk ::
  cell : NativeSourceCell term
  receiver : term
  value : term



structure NativeSourceCartesian (term : Type := Expr) where
  entry : FunctorEntry
  application : term
  realization : term
  baseMap : term
  receiver : term
  totalBundle : term
  arrow : term


inductive LiftPort


  | computation

  | factor
  deriving BEq, Repr




structure LiftFamily where
  private mk ::
  lift : LiftId
  port : LiftPort
  family : Expr
  familyType : Expr
  universeParams : List Name
  entry : LiftEntry




structure PresentationFamily where
  private mk ::
  entry : PresentationComparisonEntry
  source : ObjectEntry
  target : ObjectEntry
  category : NamedCategoryEntry
  family : Expr
  familyType : Expr
  universeParams : List Name
  forwardPath : Array Name
  inversePath : Array Name




structure SourceActionFamily where
  private mk ::
  edge : EdgeRef
  declaration : Name
  universeParams : List Name
  parameterCount : Nat
  category : CategoryExpr
  family : Expr
  familyType : Expr
  references : Array SelectedSourceReference




structure RoutedMethodReturn where
  route : Route
  rows : Array LiftEntry
  actions : Array Expr
  actionFamilies : Array SourceActionFamily
  agreement : Option Expr
  evidences : Array Expr
  category : CategoryExpr
  categoryFamily : Expr
  resultFamily : Expr




structure RoutedMethodFamily where
  private mk ::
  entry : MethodEntry
  route : Route
  functor : FunctorEntry
  categoryFamily : Expr
  functorFamily : Expr
  family : Expr
  actions : Array Expr
  actionFamilies : Array SourceActionFamily

  receiverViews : Array (Option ConstructorEntry)
  universeParams : List Name
  parameterCount : Nat
  returns : Option RoutedMethodReturn := none



structure PropertyFamily where
  private mk ::
  entry : PropertyEntry
  classifier : ClassifierEntry
  route : Route
  categoryFamily : Expr
  family : Expr
  actions : Array Expr
  actionFamilies : Array SourceActionFamily

  receiverViews : Array (Option ConstructorEntry)
  universeParams : List Name
  parameterCount : Nat



inductive PointFamilyOwner
  | morphism (entry : MorphismEntry)
  | application (entry : ObjectEntry)



structure PointFamily where
  private mk ::
  owner : PointFamilyOwner
  declaration : Name
  category : NamedCategoryEntry
  family : Expr
  familyType : Expr
  universeParams : List Name
  path : Array Name



structure NativePointRequest (term : Type := Expr) where
  private mk ::
  arrow : term
  domain : term
  source : term
  target : term
  point : term



inductive CategoricalPointOwner
  | named (owner : PointFamilyOwner)
  | component (entry : CellEntry) (constructors : Array ConstructorId) (inverse : Bool)
  | cartesian (entry : FunctorEntry)
  | binder (entry : BinderEntry)
  | action (edge : EdgeRef)




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
  references : Array SelectedSourceReference := #[]
  componentTemplate : Option (NativeSourceCellComponent Expr) := none
  cartesianTemplate : Option (NativeSourceCartesian Expr) := none



structure CategoricalPointRequest (term : Type := Expr) where
  arrow : term
  domain : term
  source : term
  target : term
  point : term



structure LimitFamily where
  private mk ::
  entry : LimitEntry
  category : NamedCategoryEntry
  universeParams : List Name
  parameterCount : Nat
  presentationFamily : Expr
  diagramFamily : Expr
  family : Expr
  familyType : Expr




structure LimitUniversalFamily where
  private mk ::
  presentation : LimitFamily
  projection : Name
  family : Expr
  familyType : Expr




structure CreationFamily where
  private mk ::
  entry : LiftEntry
  universeParams : List Name
  parameterCount : Nat
  evidenceFamily : Expr
  evidenceType : Expr
  family : Expr
  familyType : Expr




structure NativeLimitSelection (term : Type := Expr) where
  private mk ::
  source : NativeSourceLimitSelection term
  receiver : term



structure SelectedLimitOwner (term : Type) where
  selection : NativeLimitSelection term
  formalBindings : Array BindingId



structure NativeLimitLegSelection (term : Type := Expr) where
  private mk ::
  construction : NativeLimitSelection term
  index : term
  value : term


structure SourceProgram where
  private mk ::
  source : CheckedComputationDerivation
  targetReference : SelectedSourceReference
  prerequisiteReferences : Array SelectedSourceReference


structure SourceFamily where
  private mk ::
  source : CheckedComputationPrerequisite
  universeParams : List Name
  selectedReference : SelectedSourceReference
  pointFamily : Option PointFamily


inductive SelectedApplicationFamily
  | registered (family : SourceFamily)
  | target (program : SourceProgram)
  | prerequisite (program : SourceProgram) (index : Fin program.source.prerequisites.size)
  | lift (family : LiftFamily)
  | presentation (family : PresentationFamily)
  | routedMethod (family : RoutedMethodFamily)
  | property (family : PropertyFamily)
  | application (family : PointFamily)
  | point (family : CategoricalPointFamily)
  | objectAction (family : SourceActionFamily)
  | limit (family : LimitFamily)
  | limitUniversal (family : LimitUniversalFamily)
  | creation (family : CreationFamily) (target : LimitFamily)


structure SelectedSourceApplication (term : Type) where
  family : SelectedApplicationFamily
  universes : List Level
  parameters : Array term
  arguments : Array term := #[]
  owner : Option term := none
  ownerSelection : Option (SelectedLimitOwner term) := none


structure SelectedSourceAdmission (term : Type) where
  entry : ObjectEntry
  family : term
  arguments : Array term
  element : Nat


inductive SelectedSourcePointRequest (term : Type)
  | named (family : PointFamily) (request : NativePointRequest term)
  | categorical (family : CategoricalPointFamily) (request : CategoricalPointRequest term)


structure SelectedSourceField (term : Type) where
  selection : Name
  projection : Name
  owner : term
  deferredCone : Bool := false

inductive SelectedEndpointSide
  | source
  | target
  deriving BEq


structure SelectedSourceEndpoint (term : Type) where
  arrow : term
  side : SelectedEndpointSide
  value : term



structure SourceSelection (term : Type) where
  value : term
  formalBindings : Array BindingId := #[]
  carrierRoutes : Array (Array EdgeRef) := #[]
  preferredRoute : Option (Array EdgeRef) := none
  operationRefinements : Array (CategoryExpr × Array (Array EdgeRef)) := #[]

  alternatives : Array (SelectedSourceReference × Array EdgeRef) := #[]
  reference : Option SelectedSourceReference := none

  observation : Option SelectedSourceReference := none
  originalApplication : Option term := none
  application : Option (SelectedSourceApplication term) := none

  creationOwner : Option (CreationFamily × LimitFamily) := none
  admission : Option (SelectedSourceAdmission term) := none
  presentationEndpoints : Option (term × term) := none
  routedInputs : Option (Array (Array term)) := none
  legOrdinal : Option Nat := none

  recordSelection : Option Name := none

  recordOwner : Option term := none
  category : Option (NativeSourceCategory term) := none
  typeOrigin : Option (NativeSourceTypeOrigin term) := none
  elementOwner : Option (NativeSourceElementOwner term) := none
  pointOrigin : Option (NativeSourcePointOrigin term) := none
  pointRequest : Option (SelectedSourcePointRequest term) := none
  isoOrigin : Option term := none
  field : Option (SelectedSourceField term) := none
  endpoint : Option (SelectedSourceEndpoint term) := none

  limitFamily : Option LimitFamily := none
  limit : Option (NativeLimitSelection term) := none
  leg : Option (NativeLimitLegSelection term) := none
  cellFamily : Option (NativeSourceCell term) := none
  cell : Option (NativeSourceCellComponent term) := none
  cartesian : Option (NativeSourceCartesian term) := none
  powerObject : Option (NativePowerObject term) := none


abbrev SourceSelectionScope (term : Type) :=
  Std.HashMap BindingId (SourceSelection term)


def NativePowerObject.mapM [Monad m] (f : α → m β)
    (value : NativePowerObject α) : m (NativePowerObject β) := do
  return ⟨value.row, value.object, value.category, ← f value.base⟩

def NativeSourceCarrierSelection.mapM [Monad m] (f : α → m β)
    (value : NativeSourceCarrierSelection α) : m (NativeSourceCarrierSelection β) := do
  return ⟨value.refs, value.target, value.identifications,
    ← value.actions.mapM f, ← value.comparisons.mapM f⟩

def NativeSourceLimitSelection.mapM [Monad m] (f : α → m β)
    (value : NativeSourceLimitSelection α) : m (NativeSourceLimitSelection β) := do
  return ⟨value.row, value.declaration, ← f value.cone, value.colimit, value.category,
    ← f value.bundle, ← f value.presentation, ← f value.diagram, ← value.interface.mapM f,
    value.construction, ← value.ownerFamily.mapM f,
    ← value.creation.mapM (fun creation => creation.mapM f),
    ← value.creationFamily.mapM f, value.creationInputs⟩

def NativeSourceCategory.mapM [Monad m] (f : α → m β)
    (value : NativeSourceCategory α) : m (NativeSourceCategory β) := do
  return ⟨value.role, value.expression, ← f value.bundle,
    ← value.carrier.mapM (fun carrier => carrier.mapM f),
    ← value.limit.mapM (fun limit => limit.mapM f)⟩

def NativeSourceElementOwner.mapM [Monad m] (f : α → m β)
    (value : NativeSourceElementOwner α) : m (NativeSourceElementOwner β) := do
  return ⟨← value.category.mapM f, ← f value.value, ← f value.evidence⟩

def NativeSourceTypeOrigin.mapM [Monad m] (f : α → m β)
    (value : NativeSourceTypeOrigin α) : m (NativeSourceTypeOrigin β) := do
  return ⟨← value.category.mapM f, ← f value.object, ← f value.type⟩

opaque NativeSourcePointOrigin.mapM [Monad m] (f : α → m β)
    (value : NativeSourcePointOrigin α) : m (NativeSourcePointOrigin β) := do
  return ⟨← f value.point, ← f value.domain, ← f value.target⟩

def NativeRouteFunctor.mapM [Monad m] (f : α → m β)
    (value : NativeRouteFunctor α) : m (NativeRouteFunctor β) := do
  return ⟨← f value.functor, ← f value.target, ← value.actions.mapM f⟩

def NativeSourceCell.mapM [Monad m] (f : α → m β)
    (value : NativeSourceCell α) : m (NativeSourceCell β) := do
  return {
    entry := value.entry, application := ← f value.application, inverse := value.inverse
    constructors := value.constructors, source := value.source
    sourceBundle := ← f value.sourceBundle, target := value.target
    targetBundle := ← f value.targetBundle, left := ← value.left.mapM f
    right := ← value.right.mapM f, transformation := ← f value.transformation
    isomorphism := ← value.isomorphism.mapM f, references := value.references }

opaque NativeSourceCellComponent.mapM [Monad m] (f : α → m β)
    (value : NativeSourceCellComponent α) : m (NativeSourceCellComponent β) := do
  return ⟨← value.cell.mapM f, ← f value.receiver, ← f value.value⟩

def NativeSourceCartesian.mapM [Monad m] (f : α → m β)
    (value : NativeSourceCartesian α) : m (NativeSourceCartesian β) := do
  return ⟨value.entry, ← f value.application, ← f value.realization, ← f value.baseMap,
    ← f value.receiver, ← f value.totalBundle, ← f value.arrow⟩

opaque NativePointRequest.mapM [Monad m] (f : α → m β)
    (value : NativePointRequest α) : m (NativePointRequest β) := do
  return ⟨← f value.arrow, ← f value.domain, ← f value.source, ← f value.target, ← f value.point⟩

def CategoricalPointRequest.mapM [Monad m] (f : α → m β)
    (value : CategoricalPointRequest α) : m (CategoricalPointRequest β) := do
  return ⟨← f value.arrow, ← f value.domain, ← f value.source, ← f value.target, ← f value.point⟩

opaque NativeLimitSelection.mapM [Monad m] (f : α → m β)
    (value : NativeLimitSelection α) : m (NativeLimitSelection β) := do
  return ⟨← value.source.mapM f, ← f value.receiver⟩

def SelectedLimitOwner.mapM [Monad m] (f : α → m β)
    (owner : SelectedLimitOwner α) : m (SelectedLimitOwner β) := do
  return ⟨← owner.selection.mapM f, owner.formalBindings⟩


def SelectedLimitOwner.specialize (owner : SelectedLimitOwner Expr)
    (arguments : Array Expr) : MetaM NativeLimitSelection := do
  unless owner.formalBindings.size == arguments.size do
    throwError "the selected owner lost its complete original formal argument table"
  owner.selection.mapM fun value => do
    let applied := mkAppN value arguments
    check applied
    return applied.headBeta

opaque NativeLimitLegSelection.mapM [Monad m] (f : α → m β)
    (value : NativeLimitLegSelection α) : m (NativeLimitLegSelection β) := do
  return ⟨← value.construction.mapM f, ← f value.index, ← f value.value⟩

def SelectedSourceApplication.mapM [Monad m] (f : α → m β)
    (value : SelectedSourceApplication α) : m (SelectedSourceApplication β) := do
  return ⟨value.family, value.universes, ← value.parameters.mapM f,
    ← value.arguments.mapM f, ← value.owner.mapM f,
    ← value.ownerSelection.mapM (fun owner => owner.mapM f)⟩

def SelectedSourceAdmission.mapM [Monad m] (f : α → m β)
    (value : SelectedSourceAdmission α) : m (SelectedSourceAdmission β) := do
  return ⟨value.entry, ← f value.family, ← value.arguments.mapM f, value.element⟩

def SelectedSourcePointRequest.mapM [Monad m] (f : α → m β)
    (value : SelectedSourcePointRequest α) : m (SelectedSourcePointRequest β) := do
  match value with
  | .named family request => return .named family (← request.mapM f)
  | .categorical family request => return .categorical family (← request.mapM f)

def SelectedSourceField.mapM [Monad m] (f : α → m β)
    (value : SelectedSourceField α) : m (SelectedSourceField β) := do
  return ⟨value.selection, value.projection, ← f value.owner, value.deferredCone⟩

def SelectedSourceEndpoint.mapM [Monad m] (f : α → m β)
    (value : SelectedSourceEndpoint α) : m (SelectedSourceEndpoint β) := do
  return ⟨← f value.arrow, value.side, ← f value.value⟩


@[noinline, nospecialize] def SourceSelection.mapM [Monad m] (f : α → m β)
    (value : SourceSelection α) : m (SourceSelection β) := do
  return {
    value := ← f value.value, formalBindings := value.formalBindings
    carrierRoutes := value.carrierRoutes, preferredRoute := value.preferredRoute
    operationRefinements := value.operationRefinements
    alternatives := value.alternatives
    reference := value.reference
    observation := value.observation
    originalApplication := ← value.originalApplication.mapM f
    application := ← value.application.mapM (fun item => item.mapM f)
    creationOwner := value.creationOwner
    admission := ← value.admission.mapM (fun item => item.mapM f)
    presentationEndpoints := ← value.presentationEndpoints.mapM fun (left, right) => do
      return (← f left, ← f right)
    routedInputs := ← value.routedInputs.mapM fun inputs => inputs.mapM (·.mapM f)
    legOrdinal := value.legOrdinal
    recordSelection := value.recordSelection
    recordOwner := ← value.recordOwner.mapM f
    category := ← value.category.mapM (fun item => item.mapM f)
    typeOrigin := ← value.typeOrigin.mapM (fun item => item.mapM f)
    elementOwner := ← value.elementOwner.mapM (fun item => item.mapM f)
    pointOrigin := ← value.pointOrigin.mapM (fun item => item.mapM f)
    pointRequest := ← value.pointRequest.mapM (fun item => item.mapM f)
    isoOrigin := ← value.isoOrigin.mapM f
    field := ← value.field.mapM (fun item => item.mapM f)
    endpoint := ← value.endpoint.mapM (fun item => item.mapM f)
    limitFamily := value.limitFamily
    limit := ← value.limit.mapM (fun item => item.mapM f)
    leg := ← value.leg.mapM (fun item => item.mapM f)
    cellFamily := ← value.cellFamily.mapM (fun item => item.mapM f)
    cell := ← value.cell.mapM (fun item => item.mapM f)
    cartesian := ← value.cartesian.mapM (fun item => item.mapM f)
    powerObject := ← value.powerObject.mapM (fun item => item.mapM f) }

@[noinline, nospecialize] def SourceSelectionScope.mapM [Monad m] (f : α → m β)
    (scope : SourceSelectionScope α) : m (SourceSelectionScope β) := do
  scope.toList.foldlM (fun result (binding, selection) => do
    return result.insert binding (← selection.mapM f)) {}

end CasCompiler
