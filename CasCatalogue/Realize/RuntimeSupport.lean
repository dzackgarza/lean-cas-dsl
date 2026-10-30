/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language
public import CasCatalogue.Admission
public import CasCatalogue.Codec
public import CasCatalogue.StructuredResult
public import CasCatalogue.ConstructionData
public import CasCatalogue.FunctorActionData
public import CasCatalogue.DeclaredApplication
public import CasCatalogue.RoutedResultPlan
public import CasCatalogue.LiftedSubobjectData
public import CasCatalogue.LiftStageExecution
public import CasCatalogue.CellAction
public import CasCatalogue.ElementData
public import CasCatalogue.QuestionIdentity
public import CasCatalogue.ComputationalData
public import CasCatalogue.DataOwnership
public import CasCatalogue.ObjectPresentation
public import CasCatalogue.OperationAgreement
public import CasCatalogue.SimpleServiceRequest
public import CasCatalogue.StructuredServiceRequest
public import CasCatalogue.UniversalServiceRequest
public import CasCatalogue.ComputationDerivation
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import CasContract.Port

@[expose] public section

/-!
# Shared support for realized computation

This module retains the realized values, their exact owned data and producer
occurrences, the harness and port boundary, preparation and validation helpers,
and the recorded-node evaluator with its existing explicit callbacks. The
recursive execution owner and public question API remain in `CasCatalogue.Realize`.

The declarations are extracted without changing their names or bodies. Importing
this module preserves the full original semantic registry import closure.
-/

open Lean Meta Elab Term

namespace CasCatalogue

namespace Realize

open Language

export Decide (decideBudget kernelAccepts kernelDecides decideProp)

/-- A value the realized reading passes to or from a port: a closed value of a registered form (a
literal of a literal form, a morphism by its graph, a registered named object at its parameters,
a diagram), as the term the semantic reading elaborated and as its wire encoding. -/
inductive ComputationData where
  | inline (data : Json)
  | opaque (backend : String) (session : Nat) (token : String)
  | owned (backend : String) (session : Nat) (data : Json)
  | scoped (data : DataOwnership.Data)
  /-- Kernel-built data awaiting execution, with every actual dependency's
  supplier retained. Computational dependencies do not make the recipe a reply. -/
  | recipe (data : DataOwnership.Data)

inductive ComputationScope where
  | portable
  | owned (backend : String) (session : Nat)
  /-- Relative to the complete `Wire.json`, including its retained input diagram. -/
  | scoped (ownership : DataOwnership.Table)

/-- The returned packet and its exact suppliers travel together through nested
service completion. `backend` retains the raw observation interface's supplier
summary for diagnostics; it never assigns ownership to completed data. -/
structure ComputationalReply where
  data : DataOwnership.Data
  backend : String

inductive WirePayload where
  | ordinary (value : Expr) (json : Json)
  | computed (value : Expr) (data : ComputationData)
  | construction (result : StructuredResult.Result) (scope : ComputationScope)

/-- Complete actual lift fields retained with the selected formal computation. Subsequent
projections and factors reuse this execution, including its enclosing wire's live owner. -/
structure LiftStageHandles where
  action : Nat
  source : Nat
  sourceImage : Nat
  base : Nat
  baseObject : Nat
  comparisonImage : Nat
  outputs : Array Nat
  /-- Descriptor and evidence-parameter occurrences at their public request paths. -/
  staticInputPaths : Array (DataOwnership.Path × Nat) := #[]
  deriving BEq

def LiftStageHandles.all (stage : LiftStageHandles) : Array Nat :=
  #[stage.action, stage.source, stage.sourceImage, stage.base, stage.baseObject, stage.comparisonImage] ++
    stage.outputs ++ stage.staticInputPaths.map Prod.snd

structure LiftExecution where
  selections : Array SelectedLift.Plan
  actions : Array Json
  parameters : Array (Array Json)
  sources : Array Json
  bases : Array Json
  outputs : Array (Array Json)
  /-- Actual object images `U(X)` and `U(O)` for each complete selected stage.
  Both arrays are absent only on the explicit legacy recipe interface. -/
  sourceImages : Array Json := #[]
  comparisonImages : Array Json := #[]
  /-- Exact complete Wire occurrences live in the owning harness, avoiding a
  recursive Wire copy or a lookup by mathematical value or packet equality. -/
  stageHandles : Array LiftStageHandles := #[]
  /-- Each table is relative to its corresponding retained field. Parameter
  tables cover the whole parameter array; output tables cover each output. -/
  actionOwnership : Array DataOwnership.Table := #[]
  parameterOwnership : Array DataOwnership.Table := #[]
  sourceOwnership : Array DataOwnership.Table := #[]
  baseOwnership : Array DataOwnership.Table := #[]
  outputOwnership : Array (Array DataOwnership.Table) := #[]
  sourceImageOwnership : Array DataOwnership.Table := #[]
  comparisonImageOwnership : Array DataOwnership.Table := #[]

/-- The complete endpoint interface of data representing one closed point.
Point data and whole callable data can have identical JSON; the producer fixes
their role independently of bytes and of whether computation has completed. -/
structure PointDataInterface where
  domain : Expr
  target : Expr
  domainData : DataOwnership.Data
  targetData : DataOwnership.Data
  deriving BEq

/-- The accepted owner of one complete action. Dependent constructions are
registered operations in their own right, not fabricated structural edges. -/
inductive ActionOwner where
  | edge (edge : EdgeRef)
  | construction (id : ConstructionId) (parameters : Array Expr)
  deriving BEq

/-- Observation belongs to the typed slot selected by its producer. A retained
literal or element descriptor does not become an action merely because of its bytes. -/
inductive ActionDataRole where
  | parameter
  | object
  | map
  | retained
  deriving BEq

/-- The complete output interface of an assembly or captured computation is
independent of its inputs' roles. General values, including transformations and
dependent families, do not acquire the constructor's category dictionary. -/
inductive IntrinsicResultInterface where
  | object (context : CategoryContext)
  | map (context : CategoryContext)
  | value (expectedType : Expr)

def IntrinsicResultInterface.context? : IntrinsicResultInterface → Option CategoryContext
  | .object context | .map context => some context
  | .value _ => none

def IntrinsicResultInterface.role : IntrinsicResultInterface → ActionDataRole
  | .object _ => .object
  | .map _ => .map
  | .value _ => .parameter

inductive CallableEndpointOrigin where
  | retained
  | reference
  deriving BEq, Inhabited

mutual

/-- An accepted change from the fixed semantic endpoint to the representation
used by its actual computational data. Both map descriptors retain their complete
declaration parameters; the comparison itself comes only from the catalogue. -/
structure EndpointPresentation where
  comparison : Expr
  forward : Json
  backward : Json
  forwardOwnership : DataOwnership.Table := #[]
  backwardOwnership : DataOwnership.Table := #[]
  /-- Exact typed comparison occurrences, fixed by the representation producer. -/
  maps : Option (Wire × Wire) := none
  /-- A named representation is refreshed from its original typed constructor
  inputs before observation, without evaluating its semantic image action. -/
  namedRefinement : Option NamedRefinementOrigin := none

/-- A complete kernel-owned source snapshot for a proof-only refinement. -/
structure WireSnapshot where
  form : Form
  payload : WirePayload
  presentationIsos : Array Expr
  objectIso : Option Expr
  callableObserved : Bool := false
  objectObserved : Bool := false
  liftExecution : Option LiftExecution := none
  endpointPresentation : Option EndpointPresentation := none
  categoryContext : Option CategoryContext := none
  constructionInputs : Option (Expr × ComputationalData.InterfaceObjects) := none
  constructionInputOwnership : Array DataOwnership.Table := #[]
  /-- Exact runtime operand occurrences retained for nested computational service
  requests. These indices carry no mathematical interpretation or dispatch policy. -/
  serviceHandles : Array Nat := #[]
  /-- `some` selects exact request-path references, including an explicitly empty scope. -/
  serviceInputPaths : Option (Array (DataOwnership.Path × Nat)) := none
  pointDataInterface : Option PointDataInterface := none
  productComponents : Array Wire := #[]
  actionRecipe : Option ActionRecipe := none
  intrinsicAssembly : Option IntrinsicAssembly := none
  capturedInvocation : Option CapturedInvocation := none
  callableEndpoints : Option CallableEndpoints := none
  pointOrigin : Option PointOrigin := none
  morphismFramed : Bool := false
  morphismFraming : Option MorphismFraming := none

structure Wire where
  form : Form
  payload : WirePayload
  /-- Accepted identifications used to change the wire presentation, in route order. -/
  presentationIsos : Array Expr := #[]
  /-- Full selected-object comparison from the fixed semantic receiver to actual returned data. -/
  objectIso : Option Expr := none
  endpointPresentation : Option EndpointPresentation := none
  /-- This callable already consumes its endpoints' retained presentation maps. -/
  morphismFramed : Bool := false
  /-- Exact producer inputs of ordinary endpoint framing. This is not inferred
  from the resulting compose syntax or from the framed-status Boolean. -/
  morphismFraming : Option MorphismFraming := none
  /-- The kernel already received this whole callable's computational result.
  A returned expression can resemble its original recipe without becoming a new request. -/
  callableObserved : Bool := false
  /-- This object's selected action has already produced actual target data.
  A returned expression is never replayed merely because it resembles a recipe. -/
  objectObserved : Bool := false
  /-- Full source snapshots, restored only by their checked classifier forgetful prefixes. -/
  proofSources : List WireSnapshot := []
  liftExecution : Option LiftExecution := none
  categoryContext : Option CategoryContext := none
  /-- Original formal receiver and its complete pre-dispatch constructor input
  interfaces. Returned fields never populate this table or choose its receiver. -/
  constructionInputs : Option (Expr × ComputationalData.InterfaceObjects) := none
  constructionInputOwnership : Array DataOwnership.Table := #[]
  serviceHandles : Array Nat := #[]
  /-- Selected request positions refer to existing complete operand occurrences.
  An exact empty scope never enables recovery from equal packets. -/
  serviceInputPaths : Option (Array (DataOwnership.Path × Nat)) := none
  pointDataInterface : Option PointDataInterface := none
  /-- Ordered complete component selections of a structurally declared product.
  These are retained context, independently fixed before data lookup; service
  handles remain separate occurrence plumbing. A later action may retain this
  provenance without preserving products. Current-factor use checks the full
  category and exact product value again. -/
  productComponents : Array Wire := #[]
  actionRecipe : Option ActionRecipe := none
  intrinsicAssembly : Option IntrinsicAssembly := none
  capturedInvocation : Option CapturedInvocation := none
  callableEndpoints : Option CallableEndpoints := none
  pointOrigin : Option PointOrigin := none

/-- The original input and complete endpoints at one checked framing step.
Retaining it licenses a scoped replay check; it never substitutes an unobserved
formal value for the original computational packet. -/
structure MorphismFraming where
  input : Wire
  source : Wire
  target : Wire
  context : Option CategoryContext
  /-- Exact source inverse and target forward used by this frame. Their
  execution does not replace either original endpoint occurrence. -/
  comparisons : Option (Option Wire × Option Wire) := none

/-- Only a producer builds this assembly tree. Literal data retain their exact
suppliers; typed leaves retain complete occurrences without expression lookup. -/
inductive ActionDataTemplate where
  | literal (data : DataOwnership.Data)
  | wire (role : ActionDataRole) (input : Wire)
  | ctor (tag : String) (children : Array ActionDataTemplate)
  | array (children : Array ActionDataTemplate)
  | object (fields : Array (String × ActionDataTemplate))
  | project (path : DataOwnership.Path) (child : ActionDataTemplate)
  /-- Fixed descriptor context retains all typed slots without demanding them. -/
  | retained (child : ActionDataTemplate)
  /-- Declaration slots keep their logical typed values. Rendering and demand
  remain transparent; only positioned validation chooses the declared view. -/
  | logical (child : ActionDataTemplate)
  /-- The existing point-data interface selects this representation conversion.
  Its original typed point, rather than returned bytes, determines the role. -/
  | pointCallable (context : CategoryContext) (source target : Expr) (point : Wire)
  /-- A transparent inventory view changes only the complete endpoint frames.
  Its original whole map remains the producer when a pending child is observed. -/
  | inventoryMap (context : CategoryContext) (source target original : Wire)

/-- Exact endpoint occurrences of this complete callable packet. The anchor is
checked before use; historical endpoints cannot describe a projection or a new
transported value merely because the enclosing record copied their metadata. -/
structure CallableEndpoints where
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  source : Wire
  target : Wire

/-- A producer-declared map field and its two independently selected objects.
This relation is checked again when a child supplies a new actual callable. -/
structure IntrinsicMapFields where
  context : CategoryContext
  source : Wire
  target : Wire
  callable : Wire

/-- Intrinsic data assembly retains typed children, not expression-cache keys.
Only its producer selects the constructor and field roles. A current anchor is
required before observation; rendering introduces no mathematical operation. -/
structure IntrinsicAssembly where
  result : IntrinsicResultInterface
  formal : Expr
  fragment : DataOwnership.Data
  template : ActionDataTemplate
  maps : Array IntrinsicMapFields := #[]
  equalObjects : Array (Wire × Wire) := #[]
  endpointRoles : ActionDataRole × ActionDataRole := (.object, .object)

/-- Original point construction, selected by the producer before any owner
reassembly. Product paths address its chosen public encoding, never a value
found by searching another packet. -/
inductive PointRecipe where
  | element (owner : Wire) (dependencies : Array Wire)
  | product (presentation : Expr) (domain : Expr) (first second : Wire)
      (firstPath secondPath : DataOwnership.Path)
  | alias (original : Wire)

/-- Exact point inputs and endpoints. A copied historical anchor cannot describe
a newly projected or transported point. Framing retains its original input. -/
structure PointOrigin where
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  source : Wire
  target : Wire
  recipe : PointRecipe

/-- One original explicit declaration slot. Proof slots can have no data;
ordinary data parameters retain every actual supplier and typed dependency. -/
structure OperationParameterOccurrence where
  formal : Expr
  expectedType : Expr
  templates : Array ActionDataTemplate
  data : Array DataOwnership.Data
  dependencies : Array Wire

/-- A complete prepared invocation, whose mathematical choice is already fixed. -/
structure OperationObservation where
  original : Wire
  operation : OperationId
  trace : Trace
  parameters : Array Expr
  parameterOccurrences : Array OperationParameterOccurrence
  owner : Wire
  argument : Wire
  argumentDomain : Wire
  argumentData : DataOwnership.Data
  argumentTemplate : ActionDataTemplate
  argumentDependencies : Array Wire
  domainWire : Wire
  sourceWire : Wire
  targetWire : Wire
  targetOrigin : CallableEndpointOrigin
  input : Wire
  domain : Expr
  target : Expr
  targetData : Json
  materialized : Bool

/-- One independently selected declaration parameter. A proof slot has no
data fields; ordinary values retain their exact typed producer templates. -/
structure SelectedCallableParameter where
  formal : Expr
  expectedType : Expr
  templates : Array ActionDataTemplate

/-- One pending registered invocation, independent of surface notation. Its
producer fixes the whole declaration, parameter positions, endpoint occurrences
and optional existing operation-owner request before any observation. -/
structure SelectedCallableInvocation where
  address : String
  application : Expr
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  declarationParameters : Array SelectedCallableParameter
  descriptor : ActionDataTemplate
  parameters : Array ActionDataTemplate
  source : Wire
  target : Wire
  sourceOrigin : CallableEndpointOrigin
  targetOrigin : CallableEndpointOrigin
  argument : Wire
  inverse : Option Bool := none
  operationRequest : Option OperationObservation := none

/-- One explicit input occurrence of a captured request. Its index is private
runtime plumbing; the formal value and type were fixed before any demand. -/
structure InvocationOperand where
  formal : Expr
  expectedType : Expr
  role : ActionDataRole
  wire : Wire

/-- The exact original/image input slots of a universal diagram argument. -/
structure UniversalInputOccurrence where
  operand : Nat
  endpoints : Option (Nat × Nat) := none
  unchangedGraph : Option DataOwnership.Data := none

/-- A selected universal construction retains its complete result schema and
all accepted creation comparisons. No computational packet is present yet. -/
structure SelectedStructuredInvocation where
  address : String
  application : Expr
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  inputForm : Form
  resultForm : Form
  row : LimitEntry
  standard : Name
  sourceContext : CategoryContext
  targetContext : CategoryContext
  sourceDiagram : Expr
  targetDiagram : Expr
  encodingPresentation : Expr
  formalPresentation : Expr
  formalLowerPresentation : Expr
  lowerComparison : Option Expr
  creation : Option LiftEntry
  plan : StructuredResult.DataPlan
  operands : Array InvocationOperand
  sourceInputs : Array UniversalInputOccurrence
  imageInputs : Array UniversalInputOccurrence

/-- A projection retains the exact parent occurrence and independently selected
constructor port. It can be formed while the parent has no returned packet. -/
structure SelectedStructuredProjection where
  formal : Expr
  fragment : DataOwnership.Data
  /-- The constructor/input category belongs to the selected projection plan.
  It is not an output category for a transformation, family, or scalar field. -/
  context : CategoryContext
  result : IntrinsicResultInterface
  parent : Wire
  construction : StructuredProjection.ConstructionPlan
  plan : Option StructuredResult.DataPlan := none
  port : Option StructuredResult.DataPort
  inputOccurrences : Array (Nat × Option Bool) := #[]
  endpoint : Option Bool := none
  leg : Option Expr := none
  legData : Option DataOwnership.Data := none
  endpoints : Option (Wire × Wire) := none

/-- One independently selected object-field action and its complete original
parameter template. Reuse never reconstructs this declaration from a cache. -/
structure RecordProjectionAlignment where
  plan : RoutedResultPlan.ProjectionAlignmentStep
  parameters : Array SelectedCallableParameter
  before : Array ActionDataTemplate
  left : Array ActionDataTemplate
  right : Array ActionDataTemplate
  after : Array ActionDataTemplate

structure RecordProjectionAction where
  plan : RoutedResultPlan.ProjectionActionPlan
  descriptors : Array ActionDataTemplate
  alignment : Array RecordProjectionAlignment := #[]

/-- A public record projection retains its exact parent and declaration path.
The result is an alias of that field occurrence, not a newly computed object. -/
structure SelectedRecordProjection where
  formal : Expr
  fragment : DataOwnership.Data
  result : IntrinsicResultInterface
  parent : Wire
  path : ComputationalData.RecordFieldPath
  endpoints : Option (Wire × Wire) := none

/-- A service supplies exact parameter occurrences at ordinal declaration slots.
This is private runtime plumbing; public data carry no kernel handle. -/
structure RoutedParameterInput where
  actionIndex : Nat
  dataIndex : Nat
  wire : Wire

/-- One parameter position of one selected route action. The original typed
template is captured once and reused in both its descriptor and result roles. -/
structure RoutedParameterOccurrence where
  slot : RoutedResultPlan.Parameter
  template : ActionDataTemplate
  interface : RoutedResultPlan.ParameterInterface

/-- An admitted source-composite and a fully transported input are distinct
computational boundaries for the same independently selected mathematics. -/
structure SelectedRoutedBoundary where
  receiver : Wire
  context : CategoryContext
  prefixActions : Array (EdgeRef × Expr)
  descriptors : Array ActionDataTemplate
  images : Array Wire := #[]
  parameters : Array RoutedParameterOccurrence
  /-- Boundary-local action zero has this original route ordinal. The complete
  original route and its parameter occurrences remain on the invocation. -/
  routeOffset : Nat := 0
  /-- Only this boundary executes the complete original forward route. A named
  presentation with an empty residual route is a different producer. -/
  materializeRoute : Bool := false

/-- The exact ordinary method application and both inert input choices. Result
schemas are compiled purely after choosing a boundary, before executing inputs. -/
structure SelectedRoutedInvocation where
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  form : Form
  method : MethodEntry
  functor : FunctorEntry
  application : Expr
  expected : Expr
  acceptedInput : Expr
  original : Wire
  canonical : SelectedRoutedBoundary
  transported : SelectedRoutedBoundary
  presented : Option SelectedRoutedBoundary := none
  descriptor : ActionDataTemplate
  resolution : Resolution
  comparisonTerms : Array Expr

/-- A prescribed method retains its pending base and every selected lift input.
The existing ordered executor consumes these same positions on observation. -/
structure SelectedPrescribedInvocation where
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  method : MethodId
  original : Wire
  base : Wire
  sources : Array Wire
  images : Array Wire
  plan : LiftedSubobjectData.Plan
  parameters : Array (Array ActionDataTemplate)
  actions : Array ActionDataTemplate

/-- A direct selected lift keeps its original operands before any computation.
The first two slots are the source and the complete base inclusion; subsequent
slots are the ordered typed leaves of the action and selection parameters. -/
structure SelectedDirectLiftInvocation where
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  plan : SelectedLift.Plan
  operands : Array InvocationOperand
  descriptor : ActionDataTemplate
  parameters : Array ActionDataTemplate

/-- A public lift field is a positioned projection of its original producer.
The parent is retained even when its formal apex is definitionally equal to a
different construction's apex. -/
structure SelectedLiftFieldInvocation where
  formal : Expr
  fragment : DataOwnership.Data
  result : IntrinsicResultInterface
  parent : Wire
  plans : Array SelectedLift.Plan
  index : Nat

/-- A factor retains its selected construction, base map and source cone.
Only the independently checked plans and proof determine its formal result. -/
structure SelectedLiftFactorInvocation where
  formal : Expr
  fragment : DataOwnership.Data
  context : CategoryContext
  plans : Array SelectedLift.Plan
  proof : Expr
  operands : Array InvocationOperand

/-- Result protocols share occurrence identity and completion reuse. Protocol
kind does not assert that any computational data has been received. -/
inductive CapturedInvocationInterface where
  | intrinsic (selected : IntrinsicAssembly)
  | callable (selected : SelectedCallableInvocation)
  | structured (selected : SelectedStructuredInvocation)
  | projection (selected : SelectedStructuredProjection)
  | recordProjection (selected : SelectedRecordProjection)
  | routed (selected : SelectedRoutedInvocation)
  | prescribed (selected : SelectedPrescribedInvocation)
  | directLift (selected : SelectedDirectLiftInvocation)
  | liftField (selected : SelectedLiftFieldInvocation)
  | liftFactor (selected : SelectedLiftFactorInvocation)

structure CapturedInvocation where
  occurrence : Nat
  interface : CapturedInvocationInterface

/-- One pending accepted action step. Chained original Wires retain categorical
order. The output anchor distinguishes a current recipe from historical context. -/
structure ActionRecipe where
  morphism : Bool
  owner : ActionOwner
  application : Expr
  original : Wire
  descriptor : ActionDataTemplate
  source : CategoryContext
  target : CategoryContext
  formal : Expr
  fragment : DataOwnership.Data
  endpoints : Option (Wire × Wire) := none
  /-- Independently selected image occurrences reused by mapped comparisons. -/
  imageEndpoints : Option (Wire × Wire) := none

/-- The accepted named-refinement row owns this representation producer. Its
anchor and original parameter positions survive actual and private observation;
neither a matching expression nor a matching packet can choose another source. -/
structure NamedRefinementOrigin where
  formal : Expr
  fragment : DataOwnership.Data
  comparison : Expr
  entry : ObjectId
  target : ObjectId
  parameters : Array Expr
  templates : Array ActionDataTemplate
  source : Wire
  route : Array EdgeRef
  applications : Array Expr
  descriptors : Array ActionDataTemplate
  identification : Expr

end

private initialize nextInvocationOccurrence : IO.Ref Nat ← IO.mkRef 0

def SelectedRoutedInvocation.boundaries (selected : SelectedRoutedInvocation) :
    Array SelectedRoutedBoundary :=
  #[selected.transported, selected.canonical] ++ selected.presented.toArray

/-- An accepted named presentation consumed this original route prefix. Its
last image is the exact receiver transmitted to the chosen invocation; earlier
positions retain their own typed producers for subsequent consumers. This is
not a claim that every prefix action has already executed. -/
structure RoutedPrefixInput where
  receiver : Wire
  actions : Array (EdgeRef × Expr)
  descriptors : Array ActionDataTemplate
  images : Array Wire

/-- Original input positions remain available to result completion. For a
dispatched request these are its exact materialized Wires; a purely retained
result keeps its original lazy inputs. A transported request also retains the
ordered action occurrences whose final image was sent as its receiver. -/
structure RoutedInputData where
  receiver : Wire
  parameters : Array (RoutedResultPlan.Input × Wire)
  dependencies : Array Wire
  routeSources : Array Wire := #[]
  routeImages : Array Wire := #[]
  routeOffset : Nat := 0
  «prefix» : Option RoutedPrefixInput := none

def RoutedInputData.read (inputs : RoutedInputData) (input : RoutedResultPlan.Input) :
    TermElabM Wire := do
  match input with
  | .receiver => return inputs.receiver
  | .parameter .. =>
    let candidates := inputs.parameters.filter (·.1 == input)
    let #[(_, selected)] := candidates
      | throwError "the routed result lost a unique original parameter position"
    return selected

/-- Completion belongs to one result occurrence, indexed by its original
action and public field positions. Equal terms and packets are not cache keys. -/
structure IntermediateResultState where
  values : Array (Nat × Nat × Wire) := #[]
  active : Array (Nat × Nat) := #[]

/-- The selected routed schema and its complete positioned field occurrences.
Children precede their records; the output entry is the exact pre-commit result. -/
structure RetainedResultFields where
  plan : RoutedResultPlan.Plan
  values : Array Wire
  inputs : Option RoutedInputData := none
  intermediates : Option (IO.Ref IntermediateResultState) := none

/-- One immutable input and complete selected interface, created together by
the invocation owner. Reading either field cannot replace it under this
preparation's identity; a new preparation receives a fresh occurrence. -/
structure PreparedInvocation where
  private mk ::
  input : Wire
  captured : CapturedInvocation

/-- Identity of an owner-created preparation, not equality of mathematical
values or packets. The private constructor and allocator bind the complete
input and interface to this occurrence for its lifetime. -/
def PreparedInvocation.same (first second : PreparedInvocation) : Bool :=
  first.captured.occurrence == second.captured.occurrence

/-- A harness-owned immutable preparation and its optional completed result.
Equal formal terms or bytes never select a different occurrence. -/
structure InvocationExecution where
  prepared : PreparedInvocation
  result : Option Wire := none
  recordFields : Option RetainedResultFields := none

def InvocationExecution.input (record : InvocationExecution) : Wire :=
  record.prepared.input

def InvocationExecution.captured (record : InvocationExecution) : CapturedInvocation :=
  record.prepared.captured

/-- A suspended caller in the existing invocation owner. Results fill only
the next fixed operand position; there is no expression-keyed result recovery.
This is the entry/return discipline of PolyFun's HandlerMachine (b13c0744),
adapted to the existing selected requests, without its program store or fuel. -/
structure InvocationFrame where
  position : Nat
  record : InvocationExecution
  operands : Array InvocationOperand
  returned : Array Wire := #[]

def EndpointPresentation.forwardFragment (presentation : EndpointPresentation) : DataOwnership.Data :=
  { json := presentation.forward, ownership := presentation.forwardOwnership }

def EndpointPresentation.backwardFragment (presentation : EndpointPresentation) : DataOwnership.Data :=
  { json := presentation.backward, ownership := presentation.backwardOwnership }

/-- Runtime provenance of one executed complete action. Source data and owners
remain here even when the actual returned target packet is self-contained.
This receipt is not sent to an unrelated target consumer or used as evidence. -/
structure ActionExecution where
  operation : String
  action : Expr
  input : Wire
  parameters : Array Json
  parameterOwnership : DataOwnership.Table := #[]
  parameterInputs : Array Wire
  imageEndpoints : Array Wire := #[]
  result : Wire

/-- Exact runtime call provenance. A returned portable packet does not discard
the original request, its selected formal expression, or its owning session. -/
structure ReplyExecution where
  operation : String
  input : Wire
  backend : String
  session : Nat
  original : Json
  completed : Option (Json × String) := none
  completedOwnership : DataOwnership.Table := #[]

structure ServiceNodeExecution where
  operation : String
  input : String
  request : Wire
  dependencies : Array Wire
  result : Wire

/-- One deferred program keeps every actual child Wire even when its final
assembled packet is portable. No child replaces the enclosing formal question. -/
structure ServiceExecution where
  operation : String
  input : Wire
  backend : String
  original : Json
  nodes : Array ServiceNodeExecution := #[]
  result : Json := Json.null
  owner : Option (String × Nat) := none
  ownership : DataOwnership.Table := #[]
  completed : Bool := false

/-- A proved family expansion retains its exact original request and actual
primitive results. This is execution provenance, never evidence about a leaf. -/
structure DerivationExecution where
  derivation : ComputationDerivationId
  target : ComputationRef
  application : Expr
  original : Expr
  identity : Expr
  input : Wire
  prerequisites : Array ComputationDerivation.Call
  steps : Array Wire := #[]
  result : Option Wire := none

def Wire.value (wire : Wire) : Expr := match wire.payload with
  | .ordinary value _ | .computed value _ => value
  | .construction result _ => result.apex

def Wire.json (wire : Wire) : Json := match wire.payload with
  | .ordinary _ json => json
  | .computed _ (.inline data) => data
  | .computed _ (.opaque _ _ token) => Backend.ComputationalValue.encode (.opaque token)
  | .computed _ (.owned _ _ data) => data
  | .computed _ (.scoped data) | .computed _ (.recipe data) => data.json
  | .construction result _ => Json.mkObj [("ctor", "constructionApex"),
      ("args", Json.arr #[toJson wire.form.id, result.diagramJson, result.json])]

def Wire.formId (w : Wire) : String := w.form.id

/-- Exact opaque positions in the public packet. Legacy one-supplier payloads
are expanded structurally; scoped packets preserve independent occurrences. -/
def Wire.ownership (wire : Wire) : DataOwnership.Table := match wire.payload with
  | .computed _ (.opaque backend session _) | .computed _ (.owned backend session _) |
      .construction _ (.owned backend session) =>
    DataOwnership.capture wire.json (backend, session)
  | .computed _ (.scoped data) | .computed _ (.recipe data) => data.ownership
  | .construction _ (.scoped ownership) => ownership
  | _ => #[]

def Wire.fragment (wire : Wire) : DataOwnership.Data :=
  { json := wire.json, ownership := wire.ownership }

/-- Actual received data and checked projections are distinct from descriptors
assembled around computed dependencies. The distinction is set by the producer,
never inferred from a returned constructor or token. -/
def Wire.actualData (wire : Wire) : Bool := match wire.payload with
  | .ordinary .. | .computed _ (.recipe _) => false
  | .computed .. | .construction .. => true

/-- Completion is a producer's computational result, not a declared point role
or a copied historical framing origin. Pending intrinsic views retain their
exact children until their own observation boundary. -/
def Wire.completedData (wire : Wire) : Bool :=
  wire.actualData || wire.objectObserved || wire.callableObserved

/-- A convenience summary only. Dispatch, reuse and projection use every exact
ownership binding; a multi-supplier packet has no single owning session. -/
def Wire.owner? (wire : Wire) : Option (String × Nat) :=
  match DataOwnership.owners wire.ownership with
  | #[owner] => some owner
  | _ => none

def checkedFragment (result : Except String α) : TermElabM α :=
  match result with
  | .ok value => pure value
  | .error message => throwStratum .unavailable m!"the computational data lost its exact suppliers: {message}"

/-- Assemble a computational payload only from positioned fragments. -/
def scopedPayload (formal : Expr) (data : DataOwnership.Data)
    (computed : Bool := true) : TermElabM WirePayload := do
  discard <| checkedFragment data.validate
  if data.ownership.isEmpty then
    return if computed then .computed formal (.inline data.json) else .ordinary formal data.json
  return .computed formal (if computed then .scoped data else .recipe data)

/-- A complete public recipe can depend on actual owned data without claiming
that its own operation has executed. -/
def recipePayload (formal : Expr) (data : DataOwnership.Data)
    (computed : Bool := true) : TermElabM WirePayload := do
  discard <| checkedFragment data.validate
  return if computed || !data.ownership.isEmpty then .computed formal (.recipe data)
    else .ordinary formal data.json

def scopedNode (tag : String) (arguments : Array DataOwnership.Data) :
    TermElabM DataOwnership.Data :=
  checkedFragment (DataOwnership.Data.ctor tag arguments)

/-- Positions are supplied by the builder that inserted each fragment. Equality
checks only that predetermined position; no equal-JSON search chooses a supplier. -/
def placedData (json : Json) (parts : Array (DataOwnership.Path × DataOwnership.Data)) :
    TermElabM DataOwnership.Data := do
  let mut ownership := #[]
  for (position, part) in parts do
    discard <| checkedFragment part.validate
    unless DataOwnership.get? json position == some part.json do
      throwError "the positioned computational fragment changed its declared occurrence"
    ownership := ownership ++ DataOwnership.prefix position part.ownership
  let result : DataOwnership.Data := { json, ownership }
  discard <| checkedFragment result.validate
  return result

/-- A construction's table is relative to its entire public apex envelope.
Its input diagram and returned packet can retain different live suppliers. -/
def constructionPayload (form : Form) (result : StructuredResult.Result)
    (diagram packet : DataOwnership.Data) : TermElabM WirePayload := do
  unless diagram.json == result.diagramJson && packet.json == result.json do
    throwError "the complete construction changed its positioned input or result packet"
  let whole ← scopedNode "constructionApex" #[{ json := toJson form.id }, diagram, packet]
  return .construction result (.scoped whole.ownership)

/-- Constructor input scopes are aligned when the diagram is assembled. They
are never recovered by matching a returned JSON value to an earlier operand. -/
def constructionInputFragments (wire : Wire) :
    TermElabM (Array (DataOwnership.Data × Expr)) := do
  let inputs := wire.constructionInputs.map Prod.snd |>.getD #[]
  unless wire.constructionInputOwnership.isEmpty ||
      wire.constructionInputOwnership.size == inputs.size do
    throwStratum .unavailable "the retained construction input scopes lost their exact alignment"
  inputs.mapIdxM fun index (json, formal) => do
    let ownership := match wire.constructionInputOwnership[index]? with
      | some ownership => ownership
      | none => match wire.payload with
        -- The legacy constructor explicitly assigns its entire packet to one
        -- known supplier. Production construction uses aligned scoped fields.
        | .construction _ (.owned backend session) => DataOwnership.capture json (backend, session)
        | _ => #[]
    let data : DataOwnership.Data := { json, ownership }
    discard <| checkedFragment data.validate
    return (data, formal)

def selectedConstructionInput (inputs : Array (DataOwnership.Data × Expr)) (value : Expr) :
    Except String (Option DataOwnership.Data) := do
  let mut actual : Array DataOwnership.Data := #[]
  for (data, formal) in inputs do
    if formal == value && !actual.contains data then actual := actual.push data
  match actual with
  | #[] => return none
  | #[data] => return some data
  | _ => throw "the defining map has distinct actual occurrences of one formal input"

/-- The released invocation encoder still owns the wire grammar. These exact
placements carry runtime suppliers through its seven fixed fields. -/
def pointInvocationData (operation : String) (parameters : Array DataOwnership.Data)
    (arrow domain source target argument : DataOwnership.Data) : TermElabM DataOwnership.Data :=
  placedData (Backend.PointInvocation.encode {
    operation, parameters := parameters.map (·.json), arrow := arrow.json
    domain := domain.json, source := source.json, target := target.json, argument := argument.json })
    #[(#[.field "args", .index 1], DataOwnership.Data.array parameters),
      (#[.field "args", .index 2], arrow), (#[.field "args", .index 3], domain),
      (#[.field "args", .index 4], source), (#[.field "args", .index 5], target),
      (#[.field "args", .index 6], argument)]

def presentationInvocationData (parameters : Array DataOwnership.Data) (inverse : Bool)
    (source target argument : DataOwnership.Data) : TermElabM DataOwnership.Data :=
  placedData (Backend.PresentationInvocation.encode {
    parameters := parameters.map (·.json), inverse, source := source.json
    target := target.json, argument := argument.json })
    #[(#[.field "args", .index 0], DataOwnership.Data.array parameters),
      (#[.field "args", .index 2], source), (#[.field "args", .index 3], target),
      (#[.field "args", .index 4], argument)]

def dataPayload (formal : Expr) (data : Json) (owner : Option (String × Nat)) : WirePayload :=
  match owner with
  | none => .ordinary formal data
  | some (backend, session) => .computed formal (.owned backend session data)

/-- A backend reply remains computational data even when it has no opaque owner.
Portability does not turn a computed result back into its formal construction. -/
def computedPayload (formal : Expr) (data : Json) (owner : Option (String × Nat)) :
    WirePayload :=
  .computed formal (match owner with
    | none => .inline data
    | some (backend, session) => .owned backend session data)

/-- Forward exact selected occurrences without turning computational data into
formal input. Each pair is an original path and its new output path. Unchanged
forwarding uses the identity placement; wrappers and projections specify theirs. -/
def forwardPayload (source : Wire) (formal : Expr) (json : Json)
    (placements : Array (DataOwnership.Path × DataOwnership.Path) := #[(#[], #[])]) :
    WirePayload :=
  let ownership := placements.foldl (fun table (selected, position) =>
    table ++ DataOwnership.prefix position (DataOwnership.project selected source.ownership)) #[]
  match source.payload with
  | .ordinary .. => .ordinary formal json
  | .computed _ (.recipe _) => .computed formal (.recipe { json, ownership })
  | _ => .computed formal (if ownership.isEmpty then .inline json else .scoped { json, ownership })

/-- Combine already completed data without losing portable computations or
session ownership. This existing helper remains available for intrinsic data
assembly. Producers of pending operations use `combinedRecipePayload`. -/
def combinedPayload (formal : Expr) (data : DataOwnership.Data) (dependencies : Array Wire) :
    TermElabM WirePayload := do
  let computed := dependencies.any fun dependency =>
    match dependency.payload with
      | .ordinary .. => false
      | _ => true
  if dependencies.any (fun dependency => match dependency.payload with
      | .computed _ (.recipe _) => !dependency.completedData
      | _ => false) then
    return ← recipePayload formal data computed
  scopedPayload formal data computed

/-- Assembling an operation around actual dependencies preserves its pending
origin independently of the dependency packets' portability. -/
def combinedRecipePayload (formal : Expr) (data : DataOwnership.Data)
    (dependencies : Array Wire) : TermElabM WirePayload := do
  let computed := dependencies.any fun dependency =>
    match dependency.payload with
      | .ordinary .. => false
      | _ => true
  recipePayload formal data computed

def sameOperationPresentationPayload (left right : WirePayload) : Bool :=
  match left, right with
  | .ordinary first data, .ordinary second actual => first == second && data == actual
  | .computed first data, .computed second actual => first == second &&
    (match data, actual with
      | .inline first, .inline second => first == second
      | .opaque first session token, .opaque second actualSession actualToken =>
          first == second && session == actualSession && token == actualToken
      | .owned first session data, .owned second actualSession actual =>
          first == second && session == actualSession && data == actual
      | .scoped first, .scoped second | .recipe first, .recipe second => first == second
      | _, _ => false)
  | .construction first scope, .construction second actualScope =>
      first.colimit == second.colimit && first.presentation == second.presentation &&
      first.diagram == second.diagram && first.cone == second.cone && first.apex == second.apex &&
      first.diagramJson == second.diagramJson &&
      (match first.packet, second.packet with
        | .direct first, .direct second => first == second
        | .created first source data, .created second actualSource actual =>
            first == second && source == actualSource && data == actual
        | _, _ => false) &&
      (match scope, actualScope with
        | .portable, .portable => true
        | .owned first session, .owned second actualSession =>
            first == second && session == actualSession
        | .scoped first, .scoped second => first == second
        | _, _ => false)
  | _, _ => false

/-- Registry addresses identify their already admitted rows; the form constructor
and every contextual wrapper must agree as well as that address and category. -/
partial def sameOperationPresentationForm (left right : Form) : Bool :=
  left.id == right.id && left.category == right.category &&
    (match left, right with
      | .contextual first original, .contextual second actual =>
          first.syntacticEq second && sameOperationPresentationForm original actual
      | .proofRefinement first classifier original, .proofRefinement second actualClassifier actual =>
          first.id == second.id && classifier == actualClassifier &&
            sameOperationPresentationForm original actual
      | .element first, .element second => sameOperationPresentationForm first second
      | .liftInput .., .liftInput .. | .constructionInput .., .constructionInput .. |
          .constructionImage .., .constructionImage .. | .functorInput .., .functorInput .. |
          .edgeActionInput .., .edgeActionInput .. | .cellComponent .., .cellComponent .. |
          .cartesian .., .cartesian .. | .literal .., .literal .. | .graph .., .graph .. |
          .subset .., .subset .. | .object .., .object .. | .namedMorphism .., .namedMorphism .. |
          .application .., .application .. | .binder .., .binder .. |
          .canonicalMorphism .., .canonicalMorphism .. | .generator .., .generator .. |
          .limitApex .., .limitApex .. | .createdApex .., .createdApex .. |
          .functorImage .., .functorImage .. | .edgeImage .., .edgeImage .. |
          .arrow .., .arrow .. | .subobject .., .subobject .. | .presentation .., .presentation .. |
          .diagrams .., .diagrams .. => true
      | _, _ => false)

def sameRetainedLiftPlan (left right : SelectedLift.Plan) : Bool :=
  left.entry.id == right.entry.id && left.entry.edge == right.entry.edge &&
    left.entry.evidence == right.entry.evidence && left.entry.computation == right.entry.computation &&
    left.entry.kind == right.entry.kind && left.parameters == right.parameters &&
    left.evidence == right.evidence && left.computation == right.computation &&
    left.action == right.action && left.source == right.source &&
    left.inclusion == right.inclusion && left.monic == right.monic && left.ports == right.ports

def sameRetainedLiftExecution (left right : Option LiftExecution) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      left.selections.size == right.selections.size &&
      (left.selections.zip right.selections).all (fun (first, second) => sameRetainedLiftPlan first second) &&
      left.actions == right.actions && left.parameters == right.parameters &&
      left.sources == right.sources && left.bases == right.bases && left.outputs == right.outputs &&
      left.sourceImages == right.sourceImages && left.comparisonImages == right.comparisonImages &&
      left.stageHandles == right.stageHandles &&
      left.actionOwnership == right.actionOwnership && left.parameterOwnership == right.parameterOwnership &&
      left.sourceOwnership == right.sourceOwnership && left.baseOwnership == right.baseOwnership &&
      left.outputOwnership == right.outputOwnership &&
      left.sourceImageOwnership == right.sourceImageOwnership &&
      left.comparisonImageOwnership == right.comparisonImageOwnership
  | _, _ => false

/-- Exact stored snapshot fields, without inventing execution provenance that
the proof-only snapshot did not contain. -/
def retainedSnapshotWire (snapshot : WireSnapshot) : Wire := {
  form := snapshot.form, payload := snapshot.payload
  presentationIsos := snapshot.presentationIsos, objectIso := snapshot.objectIso
  callableObserved := snapshot.callableObserved, objectObserved := snapshot.objectObserved
  liftExecution := snapshot.liftExecution, endpointPresentation := snapshot.endpointPresentation
  categoryContext := snapshot.categoryContext, constructionInputs := snapshot.constructionInputs
  constructionInputOwnership := snapshot.constructionInputOwnership
  serviceHandles := snapshot.serviceHandles, serviceInputPaths := snapshot.serviceInputPaths
  pointDataInterface := snapshot.pointDataInterface
  productComponents := snapshot.productComponents, actionRecipe := snapshot.actionRecipe
  intrinsicAssembly := snapshot.intrinsicAssembly, capturedInvocation := snapshot.capturedInvocation,
  callableEndpoints := snapshot.callableEndpoints
  pointOrigin := snapshot.pointOrigin
  morphismFramed := snapshot.morphismFramed, morphismFraming := snapshot.morphismFraming }

def CapturedInvocationInterface.formal : CapturedInvocationInterface → Expr
  | .intrinsic selected => selected.formal
  | .callable selected => selected.formal
  | .structured selected => selected.formal
  | .projection selected => selected.formal
  | .recordProjection selected => selected.formal
  | .routed selected => selected.formal
  | .prescribed selected => selected.formal
  | .directLift selected => selected.formal
  | .liftField selected => selected.formal
  | .liftFactor selected => selected.formal

def CapturedInvocationInterface.fragment : CapturedInvocationInterface → DataOwnership.Data
  | .intrinsic selected => selected.fragment
  | .callable selected => selected.fragment
  | .structured selected => selected.fragment
  | .projection selected => selected.fragment
  | .recordProjection selected => selected.fragment
  | .routed selected => selected.fragment
  | .prescribed selected => selected.fragment
  | .directLift selected => selected.fragment
  | .liftField selected => selected.fragment
  | .liftFactor selected => selected.fragment

def CapturedInvocationInterface.result : CapturedInvocationInterface → IntrinsicResultInterface
  | .intrinsic selected => selected.result
  | .callable selected => .map selected.context
  | .structured selected => .object selected.context
  | .projection selected => selected.result
  | .recordProjection selected => selected.result
  | .routed selected => .object selected.context
  | .prescribed selected => .object selected.context
  | .directLift selected => .object selected.context
  | .liftField selected => selected.result
  | .liftFactor selected => .map selected.context

def CapturedInvocationInterface.context? (selected : CapturedInvocationInterface) :
    Option CategoryContext := selected.result.context?

def CapturedInvocationInterface.reanchor (selected : CapturedInvocationInterface)
    (formal : Expr) : CapturedInvocationInterface :=
  match selected with
  | .intrinsic selected => .intrinsic { selected with formal }
  | .callable selected => .callable { selected with formal }
  | .structured selected => .structured { selected with formal }
  | .projection selected => .projection { selected with formal }
  | .recordProjection selected => .recordProjection { selected with formal }
  | .routed selected => .routed { selected with formal }
  | .prescribed selected => .prescribed { selected with formal }
  | .directLift selected => .directLift { selected with formal }
  | .liftField selected => .liftField { selected with formal }
  | .liftFactor selected => .liftFactor { selected with formal }

/-- A field alias keeps the original computational occurrence. New replies and
newly projected constructor data retain the owning computation's receipt. -/
def CapturedInvocationInterface.retainsResultOccurrence : CapturedInvocationInterface → Bool
  | .intrinsic _ | .recordProjection _ => true
  | .projection selected => !selected.inputOccurrences.isEmpty
  | .callable _ | .structured _ | .routed _ | .prescribed _ |
      .directLift _ | .liftField _ | .liftFactor _ => false

/-- Exactly the constructions transferred to the demand/resume driver. -/
def CapturedInvocationInterface.staged : CapturedInvocationInterface → Bool
  | .directLift _ | .liftField _ | .liftFactor _ => true
  | _ => false

mutual

/-- Computational occurrence identity never compares carriers or mathematical
values for equality. Distinct actual packets and live owners remain distinct. -/
partial def sameActionOperand (left right : Wire) : Bool :=
  left.value == right.value && left.json == right.json && left.ownership == right.ownership &&
    left.serviceInputPaths == right.serviceInputPaths &&
    left.pointDataInterface == right.pointDataInterface &&
    left.objectIso == right.objectIso &&
    left.endpointPresentation.map (·.comparison) == right.endpointPresentation.map (·.comparison) &&
    left.endpointPresentation.map (·.forward) == right.endpointPresentation.map (·.forward) &&
    left.endpointPresentation.map (·.backward) == right.endpointPresentation.map (·.backward) &&
    left.endpointPresentation.map (·.forwardOwnership) ==
      right.endpointPresentation.map (·.forwardOwnership) &&
    left.endpointPresentation.map (·.backwardOwnership) ==
      right.endpointPresentation.map (·.backwardOwnership) &&
    sameEndpointComparisonMaps (left.endpointPresentation.bind (·.maps))
      (right.endpointPresentation.bind (·.maps)) &&
    sameNamedRefinementOrigin (left.endpointPresentation.bind (·.namedRefinement))
      (right.endpointPresentation.bind (·.namedRefinement)) &&
    sameProductComponents left.productComponents right.productComponents &&
    sameMorphismFraming left.morphismFraming right.morphismFraming &&
    sameActionRecipe left.actionRecipe right.actionRecipe &&
    sameIntrinsicAssembly left.intrinsicAssembly right.intrinsicAssembly &&
    left.capturedInvocation.map (·.occurrence) == right.capturedInvocation.map (·.occurrence) &&
    sameCallableEndpoints left.callableEndpoints right.callableEndpoints &&
    samePointOrigin left.pointOrigin right.pointOrigin

partial def samePointOrigin (left right : Option PointOrigin) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      left.formal == right.formal && left.fragment == right.fragment &&
      left.context.bundle == right.context.bundle &&
      left.context.expression.syntacticEq right.context.expression &&
      sameCompleteWireContext left.source right.source &&
      sameCompleteWireContext left.target right.target &&
      (match left.recipe, right.recipe with
        | .element owner inputs, .element actualOwner actualInputs =>
            sameCompleteWireContext owner actualOwner &&
              sameProductComponents inputs actualInputs
        | .product presentation domain first second firstPath secondPath,
            .product actualPresentation actualDomain actualFirst actualSecond
              actualFirstPath actualSecondPath =>
            presentation == actualPresentation && domain == actualDomain &&
              firstPath == actualFirstPath && secondPath == actualSecondPath &&
              sameCompleteWireContext first actualFirst &&
              sameCompleteWireContext second actualSecond
        | .alias original, .alias actual => sameCompleteWireContext original actual
        | _, _ => false)
  | _, _ => false

partial def sameEndpointComparisonMaps (left right : Option (Wire × Wire)) : Bool :=
  match left, right with
  | none, none => true
  | some (a, b), some (c, d) =>
      sameCompleteWireContext a c && sameCompleteWireContext b d
  | _, _ => false

partial def sameNamedRefinementOrigin
    (left right : Option NamedRefinementOrigin) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      left.formal == right.formal && left.fragment == right.fragment &&
      left.comparison == right.comparison && left.entry == right.entry &&
      left.target == right.target && left.parameters == right.parameters &&
      left.route == right.route && left.applications == right.applications &&
      left.identification == right.identification &&
      sameCompleteWireContext left.source right.source &&
      left.templates.size == right.templates.size &&
      (left.templates.zip right.templates).all (fun (a, b) => sameActionTemplate a b) &&
      left.descriptors.size == right.descriptors.size &&
      (left.descriptors.zip right.descriptors).all (fun (a, b) => sameActionTemplate a b)
  | _, _ => false

partial def sameMorphismFraming (left right : Option MorphismFraming) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
    sameCompleteWireContext left.input right.input &&
      sameCompleteWireContext left.source right.source &&
      sameCompleteWireContext left.target right.target &&
      (match left.comparisons, right.comparisons with
        | none, none => true
        | some (a, b), some (c, d) =>
            sameProductComponents a.toArray c.toArray && sameProductComponents b.toArray d.toArray
        | _, _ => false) &&
      left.context.map (·.bundle) == right.context.map (·.bundle) &&
      (match left.context, right.context with
        | none, none => true
        | some left, some right => left.expression.syntacticEq right.expression
        | _, _ => false)
  | _, _ => false

partial def sameActionTemplate (left right : ActionDataTemplate) : Bool :=
  match left, right with
  | .literal left, .literal right => left == right
  | .wire leftRole left, .wire rightRole right =>
      leftRole == rightRole && sameCompleteWireContext left right
  | .ctor leftTag left, .ctor rightTag right =>
      leftTag == rightTag && left.size == right.size &&
        (left.zip right).all (fun (a, b) => sameActionTemplate a b)
  | .array left, .array right => left.size == right.size &&
      (left.zip right).all (fun (a, b) => sameActionTemplate a b)
  | .object left, .object right => left.size == right.size &&
      (left.zip right).all (fun ((firstKey, first), (secondKey, second)) =>
        firstKey == secondKey && sameActionTemplate first second)
  | .project firstPath first, .project secondPath second =>
      firstPath == secondPath && sameActionTemplate first second
  | .retained left, .retained right | .logical left, .logical right =>
      sameActionTemplate left right
  | .pointCallable a s t x, .pointCallable b u v y =>
      a.expression.syntacticEq b.expression && a.bundle == b.bundle &&
        s == u && t == v && sameCompleteWireContext x y
  | .inventoryMap a s t x, .inventoryMap b u v y =>
      a.expression.syntacticEq b.expression && a.bundle == b.bundle &&
        sameCompleteWireContext s u && sameCompleteWireContext t v &&
          sameCompleteWireContext x y
  | _, _ => false

partial def sameActionRecipe (left right : Option ActionRecipe) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      left.morphism == right.morphism && left.owner == right.owner &&
      left.application == right.application && left.formal == right.formal &&
      left.fragment == right.fragment &&
      left.source.expression.syntacticEq right.source.expression &&
      left.source.bundle == right.source.bundle &&
      left.target.expression.syntacticEq right.target.expression &&
      left.target.bundle == right.target.bundle &&
      sameCompleteWireContext left.original right.original &&
      sameActionTemplate left.descriptor right.descriptor &&
      sameEndpointComparisonMaps left.imageEndpoints right.imageEndpoints &&
      (match left.endpoints, right.endpoints with
        | none, none => true
        | some (a, b), some (c, d) =>
            sameCompleteWireContext a c && sameCompleteWireContext b d
        | _, _ => false)
  | _, _ => false

partial def sameCallableEndpoints (left right : Option CallableEndpoints) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      left.formal == right.formal && left.fragment == right.fragment &&
      left.context.expression.syntacticEq right.context.expression &&
      left.context.bundle == right.context.bundle &&
      sameCompleteWireContext left.source right.source &&
      sameCompleteWireContext left.target right.target
  | _, _ => false

partial def sameIntrinsicAssembly (left right : Option IntrinsicAssembly) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      (match left.result, right.result with
        | .object a, .object b | .map a, .map b =>
            a.expression.syntacticEq b.expression && a.bundle == b.bundle
        | .value a, .value b => a == b
        | _, _ => false) && left.formal == right.formal &&
      left.fragment == right.fragment &&
      left.endpointRoles == right.endpointRoles &&
      sameActionTemplate left.template right.template &&
      left.maps.size == right.maps.size &&
      (left.maps.zip right.maps).all (fun (a, b) =>
        a.context.expression.syntacticEq b.context.expression &&
        a.context.bundle == b.context.bundle &&
        sameCompleteWireContext a.source b.source &&
        sameCompleteWireContext a.target b.target &&
        sameCompleteWireContext a.callable b.callable) &&
      left.equalObjects.size == right.equalObjects.size &&
      (left.equalObjects.zip right.equalObjects).all (fun ((a, b), (c, d)) =>
        sameCompleteWireContext a c && sameCompleteWireContext b d)
  | _, _ => false

partial def sameSelectedCallableParameter (left right : SelectedCallableParameter) : Bool :=
  left.formal == right.formal && left.expectedType == right.expectedType &&
    left.templates.size == right.templates.size &&
    (left.templates.zip right.templates).all (fun (a, b) => sameActionTemplate a b)

partial def samePreparedOperation (left right : OperationObservation) : Bool :=
  left.operation == right.operation && left.parameters == right.parameters &&
    left.parameterOccurrences.size == right.parameterOccurrences.size &&
    (left.parameterOccurrences.zip right.parameterOccurrences).all (fun (a, b) =>
      a.formal == b.formal && a.expectedType == b.expectedType &&
        a.templates.size == b.templates.size &&
        (a.templates.zip b.templates).all (fun (left, right) => sameActionTemplate left right) &&
        a.data == b.data && sameProductComponents a.dependencies b.dependencies) &&
    sameCompleteWireContext left.original right.original &&
    sameCompleteWireContext left.owner right.owner &&
    sameCompleteWireContext left.argument right.argument &&
    sameCompleteWireContext left.argumentDomain right.argumentDomain &&
    left.argumentData == right.argumentData &&
    sameActionTemplate left.argumentTemplate right.argumentTemplate &&
    sameProductComponents left.argumentDependencies right.argumentDependencies &&
    sameCompleteWireContext left.domainWire right.domainWire &&
    sameCompleteWireContext left.sourceWire right.sourceWire &&
    sameCompleteWireContext left.targetWire right.targetWire &&
    left.targetOrigin == right.targetOrigin &&
    sameCompleteWireContext left.input right.input &&
    left.domain == right.domain && left.target == right.target &&
    left.targetData == right.targetData && left.materialized == right.materialized

partial def sameSelectedCallableInvocation
    (left right : Option SelectedCallableInvocation) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      left.address == right.address && left.application == right.application &&
      left.formal == right.formal && left.fragment == right.fragment &&
      left.context.expression.syntacticEq right.context.expression &&
      left.context.bundle == right.context.bundle &&
      left.declarationParameters.size == right.declarationParameters.size &&
      (left.declarationParameters.zip right.declarationParameters).all
        (fun (a, b) => sameSelectedCallableParameter a b) &&
      sameActionTemplate left.descriptor right.descriptor &&
      left.parameters.size == right.parameters.size &&
      (left.parameters.zip right.parameters).all (fun (a, b) => sameActionTemplate a b) &&
      sameCompleteWireContext left.source right.source &&
      sameCompleteWireContext left.target right.target &&
      left.sourceOrigin == right.sourceOrigin && left.targetOrigin == right.targetOrigin &&
      sameCompleteWireContext left.argument right.argument && left.inverse == right.inverse &&
      (match left.operationRequest, right.operationRequest with
      | none, none => true
      | some a, some b => samePreparedOperation a b
      | _, _ => false)
  | _, _ => false

/-- Product identity keeps every ordered child selection recursively. The
service graph may allocate different exact handles for the same selection. -/
partial def sameProductComponents (left right : Array Wire) : Bool :=
  left.size == right.size && (left.zip right).all fun (first, second) =>
    sameCompleteWireContext first second

/-- Global selection identity is reflexive on every complete retained payload.
Operation-use restrictions are checked separately; unpositioned dependency
handles do not choose a mathematical context. Exact request-path bindings remain
part of the retained occurrence. -/
partial def sameCompleteWireContext (left right : Wire) : Bool :=
  sameActionOperand left right && sameOperationPresentationPayload left.payload right.payload &&
    sameOperationPresentationForm left.form right.form &&
    left.morphismFramed == right.morphismFramed &&
    left.callableObserved == right.callableObserved && left.objectObserved == right.objectObserved &&
    left.presentationIsos == right.presentationIsos &&
    left.categoryContext.map (·.bundle) == right.categoryContext.map (·.bundle) &&
    (match left.categoryContext, right.categoryContext with
      | none, none => true
      | some left, some right => left.expression.syntacticEq right.expression
      | _, _ => false) &&
    left.constructionInputs == right.constructionInputs &&
    left.constructionInputOwnership == right.constructionInputOwnership &&
    sameRetainedLiftExecution left.liftExecution right.liftExecution &&
    left.proofSources.length == right.proofSources.length &&
    (left.proofSources.zip right.proofSources).all (fun (first, second) =>
      sameCompleteWireContext (retainedSnapshotWire first) (retainedSnapshotWire second))

end

def sameOperationPointPresentation (left right : Wire) : Bool :=
  sameCompleteWireContext left right && left.serviceHandles == right.serviceHandles

def sameActionOperands (left right : Array Wire) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) => sameActionOperand a b

/-- A selected framing context may supply an absent context, but may not replace
an existing complete category dictionary. Accepted expression aliases can share
the same full bundle; matching only their carriers or Hom types is insufficient.
The comparison cannot determine missing parameters of either context. -/
def framingContext (selected retained : Option CategoryContext) :
    TermElabM (Option CategoryContext) := do
  if let (some selected, some retained) := (selected, retained) then
    let selectedBundle ← instantiateMVars selected.bundle
    let retainedBundle ← instantiateMVars retained.bundle
    if selectedBundle.hasMVar || selectedBundle.hasLevelMVar ||
        retainedBundle.hasMVar || retainedBundle.hasLevelMVar then
      throwStratum .invalid "the callable framing requires complete retained category contexts"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq selectedBundle retainedBundle) do
      throwStratum .invalid "the callable framing changed its complete retained category context"
  return selected.orElse fun _ => retained

/-- An initial declared object slot supplies its complete category dictionary.
The original data, supplier and producer remain unchanged; an already retained
conflicting dictionary is rejected instead of being inferred from its carrier. -/
def captureDeclaredObjectInput (wire : Wire) (context : CategoryContext) : TermElabM Wire := do
  discard <| framingContext (some context) wire.categoryContext
  CategoryContext.checkObject context wire.value
  return { wire with categoryContext := some context }

/-- Construct the identity using the already selected full category dictionary.
Its object or Hom carrier never selects a new typeclass instance. -/
def identityAtContext (context : CategoryContext) (object : Expr) : TermElabM Expr := do
  CategoryContext.checkObject context object
  let carrier ← CategoryContext.carrier context
  let dictionary ← CategoryContext.dictionary context
  let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some dictionary]
  let formal ← instantiateMVars (← mkAppOptM ``CategoryTheory.CategoryStruct.id
    #[some carrier, some categoryStructure, some object])
  CategoryContext.checkMorphism context formal object object
  return formal

/-- A copied endpoint receipt is current only at its original exact packet and
full category. Formal equality alone cannot revive historical endpoint data. -/
def retainedCallableEndpoints? (wire : Wire) (context : CategoryContext) :
    TermElabM (Option (Wire × Wire)) := do
  let some selected := wire.callableEndpoints | return none
  unless wire.value == selected.formal && wire.fragment == selected.fragment do return none
  unless context.expression.syntacticEq selected.context.expression do return none
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq context.bundle selected.context.bundle) do return none
  discard <| framingContext (some context) wire.categoryContext
  discard <| framingContext (some context) selected.source.categoryContext
  discard <| framingContext (some context) selected.target.categoryContext
  CategoryContext.checkMorphism context wire.value selected.source.value selected.target.value
  return some (selected.source, selected.target)

/-- Attach complete endpoint occurrences already fixed by this producer. No
formal lookup, action execution, or representation choice occurs here. -/
def retainCallableEndpoints (wire source target : Wire) (context : CategoryContext) :
    TermElabM Wire := do
  discard <| framingContext (some context) wire.categoryContext
  discard <| framingContext (some context) source.categoryContext
  discard <| framingContext (some context) target.categoryContext
  CategoryContext.checkMorphism context wire.value source.value target.value
  discard <| checkedFragment wire.fragment.validate
  return { wire with categoryContext := some context, callableEndpoints := some {
    formal := wire.value, fragment := wire.fragment, context, source, target } }

/-- Transport an entire actual callable through independently accepted endpoint
presentations. No graph is enumerated, no data are recovered from its formal term,
and even a comparison with definitionally equal endpoints is retained. -/
def presentMorphism (input source target : Wire)
    (context : Option CategoryContext := none)
    (comparisons : Option (Option Wire × Option Wire) := none) : TermElabM Wire := do
  let context ← framingContext context input.categoryContext
  if let some context := context then
    discard <| framingContext (some context) source.categoryContext
    discard <| framingContext (some context) target.categoryContext
    CategoryContext.checkMorphism context input.value source.value target.value
  if input.morphismFramed then return { input with categoryContext := context }
  if context.isNone then
    let type ← whnfR (← inferType input.value)
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the whole computational arrow lost its complete hom signature"
    let arguments := type.getAppArgs
    unless ← withTransparency .all <|
        isDefEq arguments[2]! source.value <&&> isDefEq arguments[3]! target.value do
      throwError "the whole computational arrow changed its selected complete endpoints"
  let mut actual := input.value
  let mut actualSource := source.value
  let mut data := input.fragment
  let sourceMap := comparisons.bind (·.1)
  let targetMap := comparisons.bind (·.2)
  if (sourceMap.isSome && source.endpointPresentation.isNone) ||
      (targetMap.isSome && target.endpointPresentation.isNone) then
    throwError "computational framing supplied an unselected endpoint comparison"
  if let some presentation := source.endpointPresentation then
    let type ← whnfR (← inferType presentation.comparison)
    unless type.isAppOf ``CategoryTheory.Iso &&
        (← withTransparency .all <| isDefEq type.getAppArgs[type.getAppArgs.size - 2]!
          source.value) do
      throwError "the domain comparison starts at a different complete object"
    let inverse ← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison]
    actualSource := type.getAppArgs.back!
    actual ← match context with
      | some context => ServiceRequest.compose context actualSource source.value target.value inverse actual
      | none => mkAppM ``CategoryTheory.CategoryStruct.comp #[inverse, actual]
    let comparisonData ← match sourceMap with
      | none => pure presentation.backwardFragment
      | some comparisonMap =>
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType comparisonMap.value) (← inferType inverse) <&&>
              isDefEq comparisonMap.value inverse) do
          throwError "the observed source comparison changed its complete selected direction"
        pure comparisonMap.fragment
    data ← scopedNode "compose" #[comparisonData, data]
  if let some presentation := target.endpointPresentation then
    let type ← whnfR (← inferType presentation.comparison)
    unless type.isAppOf ``CategoryTheory.Iso &&
        (← withTransparency .all <| isDefEq type.getAppArgs[type.getAppArgs.size - 2]!
          target.value) do
      throwError "the codomain comparison starts at a different complete object"
    let forward ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]
    actual ← match context with
      | some context =>
        ServiceRequest.compose context actualSource target.value type.getAppArgs.back!
          actual forward
      | none => mkAppM ``CategoryTheory.CategoryStruct.comp #[actual, forward]
    let comparisonData ← match targetMap with
      | none => pure presentation.forwardFragment
      | some comparisonMap =>
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType comparisonMap.value) (← inferType forward) <&&>
              isDefEq comparisonMap.value forward) do
          throwError "the observed target comparison changed its complete selected direction"
        pure comparisonMap.fragment
    data ← scopedNode "compose" #[data, comparisonData]
  discard <| StructuredResult.checkReconstruction actual
  -- A data-preserving frame over a completed callable is itself complete.
  -- New comparison maps keep their explicit current framing recipe: their
  -- mathematical comparison alone is not computational completion provenance.
  let completed := (input.actualData || input.callableObserved) &&
    (source.endpointPresentation.isNone || sourceMap.any (·.completedData)) &&
    (target.endpointPresentation.isNone || targetMap.any (·.completedData))
  let payload ←
    if completed then
      scopedPayload input.value data
    else
      combinedRecipePayload input.value data
        (#[input, source, target] ++ sourceMap.toArray ++ targetMap.toArray)
  let result := { input with
    morphismFramed := true
    morphismFraming := some { input, source, target, context, comparisons }
    -- The exact input keeps its own pending producer. This framing layer is
    -- the current owner even when an identity frame preserves the same bytes.
    intrinsicAssembly := none, capturedInvocation := none, actionRecipe := none
    objectObserved := false, callableObserved := completed
    categoryContext := context
    payload := payload }
  match context with
  | some context => retainCallableEndpoints result source target context
  | none => pure result

def mapEndpointPresentation (action : Expr) (descriptor : Json)
    (presentation : Option EndpointPresentation) (ownership : DataOwnership.Table := #[]) :
    TermElabM (Option EndpointPresentation) := do
  let some presentation := presentation | return none
  let descriptor : DataOwnership.Data := { json := descriptor, ownership }
  let forward ← scopedNode "map" #[descriptor, presentation.forwardFragment]
  let backward ← scopedNode "map" #[descriptor, presentation.backwardFragment]
  return some {
    comparison := (← mkAppM ``CategoryTheory.Functor.mapIso
      #[← Semantic.asFunctor action, presentation.comparison])
    forward := forward.json, backward := backward.json
    forwardOwnership := forward.ownership, backwardOwnership := backward.ownership }

/-- Retain the exact occurrence scopes of the inventory accepted by the public
endpoint codec. Wrapper and product paths follow that codec; only a registered
primitive codec introduces portable keys. Equal JSON never chooses an owner. -/
partial def endpointInventoryFragment (data : DataOwnership.Data) :
    TermElabM DataOwnership.Data := do
  discard <| checkedFragment data.validate
  let .ok (some keys) ← ComputationalData.endpointKeys data.json
    | throwStratum .noImplementation
        "a closed point needs its actual singleton-domain inventory when used as a whole callable"
  let .ok (tag, _) := ComputationalData.envelope data.json
    | throwError "the validated endpoint inventory lost its complete descriptor"
  let inventory ← if tag == "finiteData" then
      checkedFragment (data.project #[.field "args", .index 1])
    else if tag == "valueData" then
      endpointInventoryFragment (← checkedFragment (data.project #[.field "args", .index 0]))
    else if tag == "objectPresentation" || tag == "functorAction" then
      endpointInventoryFragment (← checkedFragment (data.project #[.field "args", .index 1]))
    else if tag == "objectProduct" then do
      let left ← endpointInventoryFragment
        (← checkedFragment (data.project #[.field "args", .index 0]))
      let right ← endpointInventoryFragment
        (← checkedFragment (data.project #[.field "args", .index 1]))
      let .ok leftKeys := left.json.getArr?
        | throwError "the validated left inventory is not an array"
      let .ok rightKeys := right.json.getArr?
        | throwError "the validated right inventory is not an array"
      let mut pairs := #[]
      for i in [:leftKeys.size] do
        let first ← checkedFragment (left.project #[.index i])
        for j in [:rightKeys.size] do
          let second ← checkedFragment (right.project #[.index j])
          pairs := pairs.push (DataOwnership.Data.array #[first, second])
      pure (DataOwnership.Data.array pairs)
    else if tag == "extent" then do
      let mut actual ← checkedFragment (data.project #[.field "args", .index 2])
      while (actual.json.getObjValAs? String "ctor").toOption == some "valueData" do
        actual ← checkedFragment (actual.project #[.field "args", .index 0])
      pure actual
    else checkedFragment (DataOwnership.Data.portable (Json.arr keys))
  unless inventory.json == Json.arr keys do
    throwError "the scoped endpoint inventory differs from the validated public inventory"
  return inventory

/-- Embed actual point data as a callable only when a consumer needs a map.
The singleton key comes from the supplied domain's existing inventory; no
formal point, carrier enumeration, or mathematical answer is evaluated here. -/
def pointCallableFragment (wire : Wire) (source target : Expr)
    (selected : PointDataInterface) : TermElabM DataOwnership.Data := do
  unless ← withoutModifyingState <| withTransparency .all <|
      isDefEq (← inferType selected.domain) (← inferType source) <&&>
        isDefEq selected.domain source <&&>
        isDefEq (← inferType selected.target) (← inferType target) <&&>
        isDefEq selected.target target do
    throwError "the retained point data changed its complete selected endpoints"
  let inventory ← endpointInventoryFragment selected.domainData
  let .arr #[_] := inventory.json
    | throwStratum .noImplementation
        "the actual domain inventory does not supply one closed-point input"
  let key ← checkedFragment (inventory.project #[.index 0])
  let graph := DataOwnership.Data.array
    #[DataOwnership.Data.array #[key, wire.fragment]]
  let callable ← scopedNode "finiteGraph" #[inventory, graph]
  scopedNode "typedMap" #[selected.domainData, selected.targetData, callable]

/-- Recover the endpoints through the complete independently selected Hom interface.
The original `Quiver.Hom` syntax retains priority. A bundled Hom representation may
use another head; its complete selected category still fixes both object arguments.
Unresolved objects are rejected instead of selecting an object from its carrier. -/
def contextualMorphismEndpoints (context : CategoryContext) (value : Expr) :
    TermElabM (Expr × Expr) := do
  let type ← instantiateMVars (← inferType value)
  if let some (source, target) := Language.homEnds? type.consumeMData then
    CategoryContext.checkMorphism context value source target
    return (source, target)
  let target ← mkFreshExprMVar (← CategoryContext.carrier context)
  let source ← CategoryContext.morphismDomain context value target
  let target ← instantiateMVars target
  if target.hasMVar || target.hasLevelMVar then
    throwError "the selected Hom interface does not retain its complete target object"
  CategoryContext.checkMorphism context value source target
  return (source, target)

/-- Only an exact existing descriptor may acquire its supplied finite inventory.
The descriptor's original occurrence and suppliers remain fixed; an inventory
already present in that occurrence cannot be replaced or discarded. -/
def checkInventoryEndpointData (original actual : DataOwnership.Data) : TermElabM Unit := do
  if actual == original then return
  if (original.json.getObjValAs? String "ctor").toOption == some "finiteData" then
    throwStratum .malformed "the inventory view changes an already retained inventory"
  let .ok ("finiteData", #[_, _]) := ComputationalData.envelope actual.json
    | throwStratum .malformed "the inventory view changes an actual endpoint or its supplier"
  let descriptor ← checkedFragment (actual.project #[.field "args", .index 0])
  unless descriptor == original do
    throwStratum .malformed "the inventory view changes its retained descriptor or supplier"

/-- Reframe only transparent callable envelopes, at their producer-selected
positions. The remaining whole callable body is a projection of the exact typed
original. A newly observed child can have another transparent wrapper depth. -/
partial def inventoryMapBodyTemplate (original oldSource oldTarget source target : Wire)
    (data : DataOwnership.Data) (path : DataOwnership.Path := #[])
    (framed : Bool := false) : TermElabM ActionDataTemplate := do
  match ComputationalData.envelope data.json with
  | .ok ("valueData", #[_]) =>
      let childPath := #[DataOwnership.Step.field "args", .index 0]
      let child ← checkedFragment (data.project childPath)
      return .ctor "valueData" #[← inventoryMapBodyTemplate original oldSource oldTarget
        source target child (path ++ childPath) framed]
  | .ok ("typedMap", #[_, _, _]) =>
      let actualSource ← checkedFragment (data.project #[.field "args", .index 0])
      let actualTarget ← checkedFragment (data.project #[.field "args", .index 1])
      unless (actualSource == oldSource.fragment || actualSource == source.fragment) &&
          (actualTarget == oldTarget.fragment || actualTarget == target.fragment) do
        throwStratum .malformed "the inventory frame changed a nested endpoint occurrence or supplier"
      let childPath := #[DataOwnership.Step.field "args", .index 2]
      let child ← checkedFragment (data.project childPath)
      return .ctor "typedMap" #[.wire .retained source, .wire .retained target,
        ← inventoryMapBodyTemplate original oldSource oldTarget source target
          child (path ++ childPath) true]
  | _ =>
      let body := ActionDataTemplate.project path (.retained (.wire .map original))
      return if framed then body else
        .ctor "typedMap" #[.wire .retained source, .wire .retained target, body]

/-- Expand the current inventory view without observing data. Its typed map
receipt supplies both original endpoint occurrences; no formal cache or equality
search chooses them. The selected new endpoints change only finite framing. -/
def inventoryMapFrameTemplate (context : CategoryContext) (source target original : Wire) :
    TermElabM ActionDataTemplate := do
  let some (oldSource, oldTarget) ← retainedCallableEndpoints? original context
    | throwError "the inventory view lost its original complete callable endpoints"
  CategoryContext.checkMorphism context original.value source.value target.value
  for (expected, actual) in #[(oldSource, source), (oldTarget, target)] do
    discard <| framingContext (some context) actual.categoryContext
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq expected.value actual.value) do
      throwError "the inventory frame changed a fixed formal endpoint"
    checkInventoryEndpointData expected.fragment actual.fragment
  inventoryMapBodyTemplate original oldSource oldTarget source target original.fragment

/-- Render only producer-declared slots. The observation callback cannot change
any slot's independently fixed formal value or complete category dictionary. -/
partial def renderActionDataWith
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (template : ActionDataTemplate) : TermElabM (DataOwnership.Data × Array Wire) := do
  match template with
  | .literal data =>
      discard <| checkedFragment data.validate
      return (data, #[])
  | .wire role original =>
      let actual ← observe role original
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual.value) (← inferType original.value) <&&>
            isDefEq actual.value original.value) do
        throwError "observing an action parameter changed its complete formal selection"
      discard <| framingContext original.categoryContext actual.categoryContext
      return (actual.fragment, #[actual])
  | .ctor tag children =>
      let rendered ← children.mapM (renderActionDataWith observe)
      return (← scopedNode tag (rendered.map Prod.fst),
        rendered.foldl (fun result child => result ++ child.2) #[])
  | .array children =>
      let rendered ← children.mapM (renderActionDataWith observe)
      return (DataOwnership.Data.array (rendered.map Prod.fst),
        rendered.foldl (fun result child => result ++ child.2) #[])
  | .object fields =>
      let rendered ← fields.mapM fun (key, child) => do
        let (data, dependencies) ← renderActionDataWith observe child
        pure (key, data, dependencies)
      let data ← checkedFragment (DataOwnership.Data.object
        (rendered.toList.map fun (key, data, _) => (key, data)))
      return (data, rendered.foldl (fun result child => result ++ child.2.2) #[])
  | .project path child =>
      let (data, dependencies) ← renderActionDataWith observe child
      return (← checkedFragment (data.project path), dependencies)
  | .retained child => renderActionDataWith (fun _ wire => pure wire) child
  | .logical child => renderActionDataWith observe child
  | .pointCallable context source target original =>
      let point ← observe .map original
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType point.value) (← inferType original.value) <&&>
            isDefEq point.value original.value) do
        throwError "the point conversion changed its complete original callable"
      discard <| framingContext (some context) point.categoryContext
      CategoryContext.checkMorphism context point.value source target
      let some selected := point.pointDataInterface
        | throwError "the point conversion lost its independently selected data interface"
      return (← pointCallableFragment point source target selected, #[point])
  | .inventoryMap context source target original =>
      let actual ← observe .map original
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual.value) (← inferType original.value) <&&>
            isDefEq actual.value original.value) do
        throwError "the inventory view changed its original complete callable"
      discard <| framingContext (some context) actual.categoryContext
      let template ← inventoryMapFrameTemplate context source target actual
      renderActionDataWith (fun _ wire => pure wire) template

def renderCapturedActionData (template : ActionDataTemplate) :
    TermElabM (DataOwnership.Data × Array Wire) :=
  renderActionDataWith (fun _ wire => pure wire) template

partial def actionTemplateInputs (template : ActionDataTemplate) : Array Wire :=
  match template with
  | .literal _ => #[]
  | .wire _ input => #[input]
  | .pointCallable _ _ _ input => #[input]
  | .inventoryMap _ source target original => #[original, source, target]
  | .retained child | .logical child | .project _ child => actionTemplateInputs child
  | .object fields => fields.flatMap (fun (_, child) => actionTemplateInputs child)
  | .ctor _ children | .array children => children.flatMap actionTemplateInputs

/-- The producer's explicit typed children, including retained framing context.
This traversal reads no expression cache and allocates no service handles. A
captured invocation's private ID already selects its canonical input table. -/
def retainedWireInputs (wire : Wire) : Array Wire :=
  wire.productComponents ++ wire.proofSources.toArray.map retainedSnapshotWire ++
    (wire.morphismFraming.toArray.flatMap fun frame =>
      #[frame.input, frame.source, frame.target] ++
        frame.comparisons.toArray.flatMap (fun (a, b) => a.toArray ++ b.toArray)) ++
    (wire.actionRecipe.toArray.flatMap fun recipe =>
      #[recipe.original] ++ actionTemplateInputs recipe.descriptor ++
        recipe.endpoints.toArray.flatMap (fun (a, b) => #[a, b]) ++
        recipe.imageEndpoints.toArray.flatMap (fun (a, b) => #[a, b])) ++
    (wire.intrinsicAssembly.toArray.flatMap fun assembly =>
      actionTemplateInputs assembly.template ++
        assembly.maps.flatMap (fun fields => #[fields.source, fields.target, fields.callable]) ++
        assembly.equalObjects.flatMap (fun (a, b) => #[a, b])) ++
    (wire.callableEndpoints.toArray.flatMap fun endpoints => #[endpoints.source, endpoints.target]) ++
    (wire.pointOrigin.toArray.flatMap fun origin =>
      #[origin.source, origin.target] ++ (match origin.recipe with
        | .element owner inputs => #[owner] ++ inputs
        | .product _ _ first second _ _ => #[first, second]
        | .alias original => #[original])) ++
    (wire.endpointPresentation.toArray.flatMap fun presentation =>
      presentation.maps.toArray.flatMap (fun (a, b) => #[a, b]) ++
        presentation.namedRefinement.toArray.flatMap (fun origin =>
          #[origin.source] ++ (origin.templates ++ origin.descriptors).flatMap actionTemplateInputs))

/-- Complete selection equality deliberately ignores unpositioned service
indices. Reusing one actual production additionally preserves every original
typed child's exact handle graph; equal public packets cannot merge requests. -/
partial def sameRetainedServiceHandles (left right : Wire) : Bool :=
  left.serviceHandles == right.serviceHandles && Id.run do
    let first := retainedWireInputs left
    let second := retainedWireInputs right
    return first.size == second.size &&
      (first.zip second).all (fun (a, b) => sameRetainedServiceHandles a b)

def sameIntrinsicObservationInput (left right : Wire) : Bool :=
  sameCompleteWireContext left right && sameRetainedServiceHandles left right

/-- Logical validation annotations do not change an intrinsic assembly's
execution role. Retained wrappers remain distinct because they suppress demand. -/
partial def actionTemplateExecution : ActionDataTemplate → ActionDataTemplate
  | .logical child => actionTemplateExecution child
  | selected => selected

/-- Substitute only a producer's declared typed leaves. The original tree's
constructor positions and literal scoped data remain unchanged. -/
partial def mapActionTemplateWires
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (template : ActionDataTemplate) : TermElabM ActionDataTemplate := do
  match template with
  | .literal data => return .literal data
  | .wire role wire => return .wire role (← observe role wire)
  | .ctor tag children =>
      return .ctor tag (← children.mapM (mapActionTemplateWires observe))
  | .array children => return .array (← children.mapM (mapActionTemplateWires observe))
  | .object fields => return .object (← fields.mapM fun (key, child) => do
      pure (key, ← mapActionTemplateWires observe child))
  | .project path child => return .project path (← mapActionTemplateWires observe child)
  | .retained child => return .retained child
  | .logical child => return .logical (← mapActionTemplateWires observe child)
  | .pointCallable context source target point =>
      return .pointCallable context source target (← observe .map point)
  | .inventoryMap context source target original =>
      return .inventoryMap context source target (← observe .map original)

def checkIntrinsicResultInterface (wire : Wire) (result : IntrinsicResultInterface) :
    TermElabM Unit := do
  match result with
  | .object context =>
      discard <| framingContext (some context) wire.categoryContext
      CategoryContext.checkObject context wire.value
  | .map context =>
      discard <| framingContext (some context) wire.categoryContext
      discard <| contextualMorphismEndpoints context wire.value
  | .value expectedType =>
      let expectedType ← instantiateMVars expectedType
      if expectedType.hasMVar || expectedType.hasLevelMVar || (← isProp expectedType) then
        throwError "an intrinsic value requires its complete computational result type"
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType wire.value) expectedType) do
        throwError "the intrinsic value changed its complete expected type"

/-- A data port is interpreted only in the constructor's independently
selected category. Matching its complete carrier or Hom validates that role;
no category or dictionary is looked up from the port's carrier. Every other
declared computational type remains a value, including whole transformations
and dependent families. The decision precedes every computational reply. -/
def constructionResultInterface (context : CategoryContext) (formal expectedType : Expr) :
    TermElabM IntrinsicResultInterface := do
  let expectedType ← instantiateMVars expectedType
  if expectedType.hasMVar || expectedType.hasLevelMVar || (← isProp expectedType) then
    throwError "the constructor result requires its complete computational field type"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType formal) expectedType) do
    throwError "the constructor field changed its independently declared result type"
  let carrier ← CategoryContext.carrier context
  if ← withoutModifyingState (withTransparency .all <| isDefEq expectedType carrier) then
    return .object context
  if let some (source, target) := Language.homEnds? expectedType then
    let declaredMap ← withoutModifyingState <| withTransparency .all do
      unless (← isDefEq (← inferType source) carrier) &&
          (← isDefEq (← inferType target) carrier) do return false
      isDefEq expectedType (← CategoryContext.hom context source target)
    if declaredMap then return .map context
  return .value expectedType

/-- Captured outputs retain a current interface, rather than borrowing their
producer's category. A value result cannot carry an object/map completion flag
or a current callable frame merely because its bytes resemble one. -/
def checkCapturedResultInterface (wire : Wire) (result : IntrinsicResultInterface) :
    TermElabM Unit := do
  checkIntrinsicResultInterface wire result
  match result with
  | .object fixed | .map fixed =>
      let some context := wire.categoryContext
        | throwError "the captured categorical result lost its complete result context"
      unless context.expression.syntacticEq fixed.expression do
        throwError "the captured result changed its selected category expression"
  | .value _ =>
      unless wire.categoryContext.isNone && !wire.objectObserved && !wire.callableObserved &&
          !wire.morphismFramed && wire.callableEndpoints.isNone && wire.pointDataInterface.isNone do
        throwError "the captured value inherited an unrelated categorical output role"

/-- The producer fixes a complete output interface before any child is
observed. Scalar results keep their expected type, without an object/map cast. -/
def retainIntrinsicResultAssembly (wire : Wire) (result : IntrinsicResultInterface)
    (template : ActionDataTemplate) (maps : Array IntrinsicMapFields := #[])
    (equalObjects : Array (Wire × Wire) := #[])
    (endpointRoles : ActionDataRole × ActionDataRole := (.object, .object)) : TermElabM Wire := do
  checkIntrinsicResultInterface wire result
  for role in #[endpointRoles.1, endpointRoles.2] do
    unless role == .object || role == .retained do
      throwError "an intrinsic endpoint requires its declared object or retained descriptor role"
  let (fragment, _) ← renderCapturedActionData template
  unless fragment == wire.fragment do
    throwError "the intrinsic producer changed its ordered child data or suppliers"
  for fields in maps do
    CategoryContext.checkMorphism fields.context fields.callable.value
      fields.source.value fields.target.value
  if !wire.actualData && !wire.objectObserved && !wire.callableObserved then
    if let some captured := wire.capturedInvocation then
      if wire.value == captured.interface.formal && wire.fragment == captured.interface.fragment then
        unless (actionTemplateInputs template).any (fun input =>
            input.capturedInvocation.any (·.occurrence == captured.occurrence)) do
          throwError "the intrinsic producer did not retain its original invocation as a typed child"
  let capturedInvocation := if wire.actualData || wire.objectObserved || wire.callableObserved then
    wire.capturedInvocation else none
  return { wire with capturedInvocation, intrinsicAssembly := some {
    result, formal := wire.value, fragment, template, maps, equalObjects, endpointRoles } }

/-- Attach the already selected interface to a fresh checked projection.
The value case keeps a current typed literal assembly after completion so later
parameter capture cannot reinterpret a Hom-shaped value in another category. -/
def retainCompletedResultInterface (wire : Wire) (result : IntrinsicResultInterface) :
    TermElabM Wire := do
  unless wire.actualData do
    throwError "a completed result interface requires actual checked projection data"
  if let .value _ := result then
    checkCapturedResultInterface wire result
  let wire := { wire with
    categoryContext := result.context?,
    objectObserved := result.role == .object,
    callableObserved := result.role == .map }
  checkCapturedResultInterface wire result
  match result with
  | .value _ => retainIntrinsicResultAssembly wire result (.literal wire.fragment)
  | _ => pure wire

/-- Attach only the intrinsic constructor which this checked producer formed.
The complete output role and context are fixed before any child is observed. -/
def retainIntrinsicAssembly (wire : Wire) (role : ActionDataRole)
    (context : CategoryContext) (template : ActionDataTemplate)
    (maps : Array IntrinsicMapFields := #[])
    (equalObjects : Array (Wire × Wire) := #[])
    (endpointRoles : ActionDataRole × ActionDataRole := (.object, .object)) : TermElabM Wire := do
  let result ← match role with
    | .object => pure (IntrinsicResultInterface.object context)
    | .map => pure (IntrinsicResultInterface.map context)
    | _ => throwError "an intrinsic assembly requires its declared object or map role"
  retainIntrinsicResultAssembly wire result template maps equalObjects endpointRoles

/-- Current-role lookup ignores historical assembly context after a projection
or transport. Such context never licenses rebuilding a different current value. -/
def currentIntrinsicAssembly? (wire : Wire) :
    TermElabM (Option IntrinsicAssembly) := do
  let some selected := wire.intrinsicAssembly | return none
  unless wire.value == selected.formal &&
      wire.fragment == selected.fragment do return none
  match selected.result with
  | .object fixed | .map fixed =>
      if let some context := wire.categoryContext then
        unless context.expression.syntacticEq fixed.expression do return none
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq context.bundle fixed.bundle) do return none
  | .value expectedType =>
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType wire.value) expectedType) do return none
  return some selected

/-- Compatibility lookup for the existing object/map observation boundaries. -/
def retainedIntrinsicAssembly? (wire : Wire) (role : ActionDataRole) :
    TermElabM (Option IntrinsicAssembly) := do
  let some selected ← currentIntrinsicAssembly? wire | return none
  match role, selected.result with
  | .object, .object _ | .map, .map _ => return some selected
  | _, _ => return none

def retainedIntrinsicValueAssembly? (wire : Wire) : TermElabM (Option IntrinsicAssembly) := do
  let some selected ← currentIntrinsicAssembly? wire | return none
  if let .value _ := selected.result then return some selected
  return none

/-- Historical producer metadata cannot describe a new current value. -/
def retainedCapturedInvocation? (wire : Wire) : TermElabM (Option CapturedInvocation) := do
  -- A received packet can equal its old request bytes. Completion, not the
  -- packet's spelling, keeps its retained provenance from becoming a request.
  if wire.completedData then return none
  let some captured := wire.capturedInvocation | return none
  let selected := captured.interface
  unless wire.value == selected.formal && wire.fragment == selected.fragment do return none
  match selected.result with
  | .object fixed | .map fixed =>
      let some context := wire.categoryContext | return none
      unless context.expression.syntacticEq fixed.expression do return none
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq context.bundle fixed.bundle) do return none
  | .value expectedType =>
      unless wire.categoryContext.isNone && !wire.objectObserved && !wire.callableObserved &&
          !wire.morphismFramed && wire.callableEndpoints.isNone && wire.pointDataInterface.isNone do
        return none
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType wire.value) expectedType) do return none
  return some captured

/-- Current declared value roles survive both pending capture and completed
intrinsic value assembly. Historical producer metadata never chooses a role. -/
def retainedValueResultInterface? (wire : Wire) : TermElabM (Option IntrinsicResultInterface) := do
  if let some assembly ← retainedIntrinsicValueAssembly? wire then
    return some assembly.result
  if let some captured ← retainedCapturedInvocation? wire then
    if let .value expectedType := captured.interface.result then
      return some (.value expectedType)
  return none

/-- Read only the exact original point occurrence. A framing replay is checked
against its complete historical input before exposing that input's provenance. -/
partial def retainedPointOrigin? (wire : Wire) : TermElabM (Option PointOrigin) := do
  if wire.completedData || wire.callableObserved then return none
  if let some origin := wire.pointOrigin then
    if wire.value == origin.formal && wire.fragment == origin.fragment then
      discard <| framingContext (some origin.context) wire.categoryContext
      CategoryContext.checkMorphism origin.context wire.value origin.source.value origin.target.value
      match origin.recipe with
      | .alias original =>
          unless original.fragment == wire.fragment do
            throwStratum .unavailable "the retained point alias changed its exact data occurrence"
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq (← inferType original.value) (← inferType wire.value) <&&>
                isDefEq original.value wire.value) do
            throwError "the retained point alias changed its complete mathematical value"
          return ← retainedPointOrigin? original
      | _ => return some origin
  if let some framing := wire.morphismFraming then
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context framing.comparisons
    unless sameCompleteWireContext replayed wire do
      throwStratum .unavailable "the point lost its exact original framing occurrence"
    return ← retainedPointOrigin? framing.input
  return none

def retainPointOrigin (wire : Wire) (context : CategoryContext) (source target : Wire)
    (recipe : PointRecipe) : TermElabM Wire := do
  CategoryContext.checkMorphism context wire.value source.value target.value
  let wire ← retainCallableEndpoints wire source target context
  return { wire with pointOrigin := some {
    formal := wire.value, fragment := wire.fragment, context, source, target, recipe } }

/-- A checked transparent alias forwards current typed provenance explicitly.
Historical anchors stay historical; a different mathematical value or type is
never licensed by copying endpoint or intrinsic-assembly metadata. -/
def forwardCapturedInvocation (source : Wire) (formal : Expr) : Option CapturedInvocation := do
  let captured ← source.capturedInvocation
  unless source.actualData || source.objectObserved || source.callableObserved ||
      (source.value == captured.interface.formal && source.fragment == captured.interface.fragment) do none
  return { captured with interface := captured.interface.reanchor formal }

/-- Only the current complete named producer can be forwarded or refreshed.
A copied historical comparison does not authorize a different value or packet,
even when the mathematical expressions happen to be definitionally equal. -/
def currentNamedRefinementOrigin? (wire : Wire) : TermElabM (Option NamedRefinementOrigin) := do
  let some presentation := wire.endpointPresentation | return none
  let some origin := presentation.namedRefinement | return none
  unless origin.formal == wire.value && origin.fragment == wire.fragment &&
      origin.comparison == presentation.comparison do
    throwStratum .unavailable "historical named representation data cannot refresh another occurrence"
  return some origin

def forwardRetainedValue (source : Wire) (formal : Expr) : TermElabM Wire := do
  if source.value == formal then return source
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType source.value) (← inferType formal) <&&>
        isDefEq source.value formal) do
    throwError "the retained data alias changed its complete mathematical value"
  let mut result := { source with
    capturedInvocation := forwardCapturedInvocation source formal, payload := forwardPayload source formal source.json }
  if let some origin ← currentNamedRefinementOrigin? source then
    let some presentation := source.endpointPresentation | unreachable!
    result := { result with endpointPresentation := some { presentation with
      namedRefinement := some { origin with formal } } }
  if let some framing := source.morphismFraming then
    -- The old frame belongs to its exact original input. Keep that whole
    -- occurrence as a typed child rather than rewriting its historical anchor
    -- or weakening the replay check to equality of mathematical values.
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context framing.comparisons
    unless sameCompleteWireContext replayed source do
      throwStratum .unavailable "the retained alias lost its complete framing producer"
    let context ← framingContext source.categoryContext framing.context
    let context ← match context with
      | some context => pure context
      | none =>
        let some category := (← registryState).categories.find? (·.id == source.form.category)
          | throwError "the retained callable alias lost its registered category"
        CategoryContext.ofNamed category framing.source.value
    CategoryContext.checkMorphism context formal framing.source.value framing.target.value
    result := { result with
      morphismFraming := none, actionRecipe := none,
      intrinsicAssembly := none, callableEndpoints := none, categoryContext := some context }
    result ← retainIntrinsicAssembly result .map context (.wire .map source)
    result ← retainCallableEndpoints result framing.source framing.target context
    if (← retainedPointOrigin? source).isSome then
      result ← retainPointOrigin result context framing.source framing.target (.alias source)
    return result
  if let some assembly := source.intrinsicAssembly then
    if (← currentIntrinsicAssembly? source).isSome then
      result := { result with intrinsicAssembly := some { assembly with formal } }
  if let some origin := source.pointOrigin then
    if source.value == origin.formal && source.fragment == origin.fragment then
      result := { result with pointOrigin := some { origin with formal } }
  if let some endpoints := source.callableEndpoints then
    if (← retainedCallableEndpoints? source endpoints.context).isSome then
      result := { result with callableEndpoints := some { endpoints with formal } }
  return result

/-- Capture complete callable data without observing it. A closed point is
converted before whole-map framing. Arrow fields can preserve their existing
framed bytes; public callable slots additionally expose the typedMap envelope.
The exact child and both endpoint occurrences remain available in either case. -/
def captureCompleteCallableWith
    (readEndpoints : Wire → CategoryContext → TermElabM (Wire × Wire))
    (input : Wire) (context : CategoryContext)
    (endpoints : Option (Wire × Wire) := none) (publicFrame : Bool := true) :
    TermElabM Wire := do
  let selected ← readEndpoints input context
  let (source, target) ← match endpoints with
    | some endpoints =>
      unless sameCompleteWireContext endpoints.1 selected.1 &&
          sameCompleteWireContext endpoints.2 selected.2 do
        throwStratum .unavailable
          "an explicit callable frame cannot replace its retained endpoint occurrences"
      pure selected
    | none => pure selected
  CategoryContext.checkMorphism context input.value source.value target.value
  -- A value already declared at a complete Hom is consumed through its own
  -- value producer before it acquires this caller's map view. The transparent
  -- value envelope keeps that distinct typed child at a public data position;
  -- in particular, an element extraction retains its entire original point,
  -- including any admission and singleton comparisons. A scalar whose type
  -- merely reduces to some Hom is not a declared callable input.
  let input ← match ← retainedValueResultInterface? input with
    | some (.value expectedType) => do
      let some declared ← ComputationalData.declaredCallableType? expectedType | pure input
      let expected ← context.hom source.value target.value
      unless declared.isAppOfArity ``Quiver.Hom 4 && expected.isAppOfArity ``Quiver.Hom 4 do
        throwError "the declared callable value lost its complete Hom interface"
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq declared.getAppArgs[0]! expected.getAppArgs[0]! <&&>
          isDefEq declared.getAppArgs[1]! expected.getAppArgs[1]! <&&>
          isDefEq declared expected) do
        throwStratum .unavailable "the callable value changed its complete selected category or endpoints"
      let template := ActionDataTemplate.ctor "valueData" #[.wire .parameter input]
      let (data, dependencies) ← renderCapturedActionData template
      let value : Wire := {
        form := input.form,
        payload := (← combinedRecipePayload input.value data dependencies),
        categoryContext := some context, serviceHandles := input.serviceHandles }
      let value ← retainIntrinsicAssembly value .map context template
      retainCallableEndpoints value source target context
    | _ => pure input
  if let some selected := input.pointDataInterface then
    unless source.fragment == selected.domainData && target.fragment == selected.targetData do
      throwStratum .unavailable "the point conversion changed its exact retained endpoint packets"
    let data ← pointCallableFragment input source.value target.value selected
    let completed := input.actualData || input.callableObserved
    let result := { input with
      payload := (← if completed then scopedPayload input.value data else recipePayload input.value data)
      pointDataInterface := none, morphismFramed := true, morphismFraming := none
      objectObserved := false, callableObserved := completed
      actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none }
    let result ← if completed then pure result else
      retainIntrinsicAssembly result .map context
        (.pointCallable context source.value target.value input)
    return ← retainCallableEndpoints result source target context
  let presented ← presentMorphism input source target (some context)
  let presented ← retainCallableEndpoints presented source target context
  if !publicFrame then return presented
  let some data := ComputationalData.recordPayload? presented.fragment
    | throwStratum .malformed "the complete callable lost its transparent data envelope"
  if (Backend.TypedMap.decode data.json).isOk then
    let actualSource ← checkedFragment (data.project #[.field "args", .index 0])
    let actualTarget ← checkedFragment (data.project #[.field "args", .index 1])
    unless actualSource == source.fragment && actualTarget == target.fragment do
      throwStratum .malformed "the complete callable changed its retained endpoint occurrences"
    return presented
  let template : ActionDataTemplate := .ctor "typedMap"
    #[.wire .object source, .wire .object target, .wire .map presented]
  let (data, dependencies) ← renderCapturedActionData template
  let result := { presented with
    payload := (← combinedRecipePayload input.value data dependencies)
    morphismFraming := none, actionRecipe := none, intrinsicAssembly := none
    callableEndpoints := none, pointDataInterface := none }
  let result ← retainIntrinsicAssembly result .map context template
    #[{ context, source, target, callable := presented }]
  retainCallableEndpoints result source target context

/-- Give a complete callable a transparent inventory frame at already selected
endpoints. The ordinary framing owner converts any point or pending presentation
first. Later observation refreshes this view from that exact whole child. -/
def captureInventoryMapEndpoints (context : CategoryContext) (original source target : Wire) :
    TermElabM Wire := do
  let read := fun (wire : Wire) (selected : CategoryContext) => do
    let some endpoints ← retainedCallableEndpoints? wire selected
      | throwError "the inventory frame lost its original typed callable receipt"
    return endpoints
  let original ← captureCompleteCallableWith read original context
  let template := ActionDataTemplate.inventoryMap context source target original
  let (data, dependencies) ← renderCapturedActionData template
  let result : Wire := {
    form := original.form,
    payload := (← if original.completedData then scopedPayload original.value data
      else recipePayload original.value data),
    categoryContext := some context, morphismFramed := true,
    callableObserved := original.callableObserved,
    serviceHandles := dependencies.flatMap (·.serviceHandles) }
  let result ← retainIntrinsicAssembly result .map context template
    (endpointRoles := (.retained, .retained))
  retainCallableEndpoints result source target context

/-- Expose only producer-declared typed occurrences at their actual rendered
positions. Retention suppresses observation, not the existence of an input slot.
A projection keeps bindings below its selected path; it never relabels a whole
parent occurrence as a smaller packet. -/
partial def actionTemplateInputPaths (template : ActionDataTemplate) :
    TermElabM (Array (DataOwnership.Path × Wire)) := do
  let prefixPaths (path : DataOwnership.Path) (inputs : Array (DataOwnership.Path × Wire)) :=
    inputs.map fun (child, wire) => (path ++ child, wire)
  let inputs ← match template with
    | .literal _ => pure #[]
    | .wire _ input => pure #[(#[], input)]
    | .ctor _ children => do
        let children ← children.mapIdxM fun index child => do
          return prefixPaths #[.field "args", .index index] (← actionTemplateInputPaths child)
        pure (children.foldl (· ++ ·) #[])
    | .array children => do
        let children ← children.mapIdxM fun index child => do
          return prefixPaths #[.index index] (← actionTemplateInputPaths child)
        pure (children.foldl (· ++ ·) #[])
    | .object fields => do
        let fields ← fields.mapM fun (key, child) => do
          return prefixPaths #[.field key] (← actionTemplateInputPaths child)
        pure (fields.foldl (· ++ ·) #[])
    | .project path child => do
        let inputs ← actionTemplateInputPaths child
        pure (inputs.filterMap fun (selected, wire) =>
          (DataOwnership.stripPrefix? path selected).map (·, wire))
    | .retained child | .logical child => actionTemplateInputPaths child
    | .pointCallable context source target point => do
        let read := fun (wire : Wire) (selected : CategoryContext) => do
          let some endpoints ← retainedCallableEndpoints? wire selected
            | throwError "the point input paths lost their original complete endpoints"
          return endpoints
        let callable ← captureCompleteCallableWith read point context
        CategoryContext.checkMorphism context callable.value source target
        let (domain, codomain) ← read callable context
        pure #[(#[], callable), (#[.field "args", .index 0], domain),
          (#[.field "args", .index 1], codomain)]
    | .inventoryMap context source target original => do
        let expanded ← inventoryMapFrameTemplate context source target original
        let inputs ← actionTemplateInputPaths expanded
        let (data, _) ← renderCapturedActionData template
        -- The original whole map remains a binding only when this exact frame
        -- leaves its full packet and suppliers unchanged.
        if data == original.fragment then pure (#[(#[], original)] ++ inputs)
        else pure inputs
  let (data, _) ← renderCapturedActionData template
  for (path, wire) in inputs do
    unless (← checkedFragment (data.project path)) == wire.fragment do
      throwError "a declared service input path changed its complete operand packet or suppliers"
  return inputs

structure BackendSession where
  identity : Nat
  connection : Backend.Conn

initialize nextBackendSession : IO.Ref Nat ← IO.mkRef 0

/-- Transport only the retained full selected-object comparison through the actual functor. -/
def mapObjectComparison (F actual : Expr) (comparison : Option Expr) : TermElabM (Option Expr) := do
  match comparison with
  | none => return none
  | some iso =>
      let type ← withTransparency .all <| whnf (← inferType iso)
      unless type.isAppOf ``CategoryTheory.Iso && type.getAppArgs.size >= 2 do
        throwError "the retained object comparison is not a full isomorphism"
      unless ← withTransparency .all <| isDefEq type.getAppArgs.back! actual do
        throwError "the retained object comparison targets a different full receiver"
      return some (← StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.Functor.mapIso #[← Semantic.asFunctor F, iso]))

def composeObjectComparisons (first second : Option Expr) : TermElabM (Option Expr) := do
  match first, second with
  | none, other | other, none => return other
  | some first, some second =>
      return some (← StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.Iso.trans #[first, second]))

/-- Preserve complete inherited object context when the returned data uses its actual image. -/
def preserveResultComparison (inherited returned : Option Expr) (expected actual : Expr)
    (form : Form) (fixed answer : Json) : TermElabM (Option Expr × Json) := do
  if returned.isSome then
    let comparison ← composeObjectComparisons inherited returned
    return (comparison, Json.mkObj [("ctor", "objectPresentation"),
      ("args", Json.arr #[fixed, answer])])
  if inherited.isNone then return (none, answer)
  if ← withTransparency .all <| isDefEq expected actual then
    return (inherited, fixed)
  match form with
  | .literal _ | .element _ | .generator _ => return (none, answer)
  | _ =>
      throwStratum .noImplementation "the returned structured object requires a checked comparison to preserve its inherited context"

/-- Align the actual stored Arrow map using the retained full Arrow-object isomorphism. -/
def alignedArrowHom (arrow : Expr) (comparison : Option Expr) : TermElabM Expr := do
  let actual ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
  match comparison with
  | none => return actual
  | some iso =>
      let type ← withTransparency .all <| whnf (← inferType iso)
      unless type.isAppOf ``CategoryTheory.Iso do
        throwError "the stored Arrow comparison is not a complete isomorphism"
      let args := type.getAppArgs
      unless args.size >= 2 do throwError "the stored Arrow comparison has no complete endpoints"
      unless ← withTransparency .all <| isDefEq args.back! arrow do
        throwError "the stored Arrow comparison targets a different actual Arrow object"
      let left ← mkAppM ``CategoryTheory.Arrow.Hom.left
        #[← mkAppM ``CategoryTheory.Iso.hom #[iso]]
      let right ← mkAppM ``CategoryTheory.Arrow.Hom.right
        #[← mkAppM ``CategoryTheory.Iso.inv #[iso]]
      return ← StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.CategoryStruct.comp #[
          ← mkAppM ``CategoryTheory.CategoryStruct.comp #[left, actual], right])

/-- Closed arithmetic elements use the registered singleton domain of their formal reading. -/
def closedElementDomain (_state : RegistryState) : TermElabM Expr := do
  ServiceRequest.closedElementDomain

/-- The independently fixed result interface of a point invocation. Closed points use
the registry's selected global point; generalized maps retain their complete map type. -/
def pointResultValue (_state : RegistryState) (point : Expr) : TermElabM Expr := do
  ServiceRequest.pointResultValue point

/-- Retain the actual endpoint packets only for the independently selected
closed-point result interface. This does not inspect an answer to infer its role. -/
def pointDataInterfaceAt (domain target : Expr)
    (domainData targetData : DataOwnership.Data) : TermElabM (Option PointDataInterface) := do
  unless ← withoutModifyingState <| withTransparency .all <|
      isDefEq domain (← ServiceRequest.closedElementDomain) do return none
  return some { domain, target, domainData, targetData }

/-- A complete point invocation already positions both result endpoints. Keep
their exact occurrence scopes after the point reply has passed its validator. -/
def pointInvocationInterface (formal : Expr) (request : DataOwnership.Data) :
    TermElabM (Option PointDataInterface) := do
  let some (domain, target) := Language.homEnds? (← inferType formal)
    | throwError "a completed point invocation lost its complete result signature"
  let .ok _ := Backend.PointInvocation.decode request.json
    | throwError "a completed point invocation lost its complete request framing"
  pointDataInterfaceAt domain target
    (← checkedFragment (request.project #[.field "args", .index 3]))
    (← checkedFragment (request.project #[.field "args", .index 5]))

/-- The checked universal properties identify the requested and returned apex completely. -/
def universalPointIso (row : LimitEntry) (accepted rebuilt : Expr) : TermElabM Expr := do
  let projection := if row.colimit then ``CategoryTheory.Limits.ColimitCocone.isColimit
    else ``CategoryTheory.Limits.LimitCone.isLimit
  let first ← mkAppM projection #[accepted]
  let second ← mkAppM projection #[rebuilt]
  StructuredResult.checkReconstruction (← mkAppM (if row.colimit then
    ``CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso else
    ``CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso) #[first, second])

/-- Change only the apex endpoint through its checked universal comparison. -/
def alignUniversalLeg (row : LimitEntry) (iso leg : Expr) : TermElabM Expr := do
  let arrow ← mkAppM (if row.colimit then ``CategoryTheory.Iso.inv
    else ``CategoryTheory.Iso.hom) #[iso]
  let (first, second) := if row.colimit then (leg, arrow) else (arrow, leg)
  elabTermAndSynthesize
    (← `(CategoryTheory.CategoryStruct.comp $(← exprToSyntax first)
      $(← exprToSyntax second))) none

/-- The admitted registrations of a run, their backend programs, and the live connections. -/
structure Harness where
  admitted : Array Admitted := #[]
  /-- The registrations not admitted, each with its reason. -/
  rejected : Array String := #[]
  backends : Array BackendProgram := #[]
  /-- The directory the programs run in: the manifest's. -/
  root : System.FilePath := "."
  /-- Exercise registered computation without the optional proof-discharge shortcut. -/
  computationOnly : Bool := false
  /-- Trusted observations of requests actually dispatched by this kernel harness. -/
  dispatches : Option (IO.Ref (Array Json)) := none
  connections : IO.Ref (Std.HashMap String (Except Backend.PortError BackendSession))
  /-- Actual computed results keyed by their exact closed formal terms; no dispatch is fabricated on reuse. -/
  results : IO.Ref (Std.HashMap Expr Wire)
  /-- Retained images are keyed by the selected action and actual input data,
  including owners and, for maps, both already computed image endpoints. -/
  actions : IO.Ref (Array ActionExecution)
  replies : IO.Ref (Array ReplyExecution)
  services : IO.Ref (Array ServiceExecution)
  derivations : IO.Ref (Array DerivationExecution)
  /-- A dispatched failure cannot be mistaken for a missing structural leaf and
  retried through a different proved plan, including an `unsupported` reply. -/
  portFailures : IO.Ref Nat
  serviceOperands : IO.Ref (Array Wire)
  invocations : IO.Ref (Array InvocationExecution)
  invocationStack : Array Nat := #[]
  /-- Installed by the ordinary computation boundary and available to direct
  harness consumers through the same public installer. -/
  deferred : Option (String → Wire → ComputationalReply → TermElabM ComputationalReply) := none
  /-- Used only after exact ordinary admission finds no implementation. Its
  input is the same complete request; no computational reply can install it. -/
  derivation : Option (String → Wire → Bool → TermElabM ComputationalReply) := none
  /-- Exact parameters currently recovering their source/action data. A scoped harness copy
  carries this across both callbacks without changing the shared result cache. -/
  parameterRecovery : Array Expr := #[]
  /-- A computational boundary demands registered object actions in complete
  parameters; metadata-only preparation retains the same formal recipes. -/
  demandObjectActions : Bool := false

/-- A harness with no leaf installed. -/
def Harness.empty : IO Harness := return {
  connections := ← IO.mkRef {}, results := ← IO.mkRef {}, actions := ← IO.mkRef #[]
  replies := ← IO.mkRef #[], services := ← IO.mkRef #[], derivations := ← IO.mkRef #[]
  portFailures := ← IO.mkRef 0
  serviceOperands := ← IO.mkRef #[], invocations := ← IO.mkRef #[] }

/-- The harness of the manifest `manifest`, at the directory `root`. -/
def Harness.ofManifest (root : System.FilePath) (manifest : Manifest) : CoreM Harness := do
  let admission := (← registryState).admit manifest
  return { admitted := admission.admitted, rejected := admission.rejected
           backends := manifest.backends, root, connections := ← IO.mkRef {},
           results := ← IO.mkRef {}, actions := ← IO.mkRef #[],
           replies := ← IO.mkRef #[], services := ← IO.mkRef #[], derivations := ← IO.mkRef #[]
           portFailures := ← IO.mkRef 0
           serviceOperands := ← IO.mkRef #[], invocations := ← IO.mkRef #[] }

/-- The common owner fixes one complete input and selected interface before
allocating its private identity. Preparation chooses no implementation and
creates neither an actual packet nor a completion receipt. -/
private def captureInvocationCore (h : Harness) (wire : Wire)
    (interface : CapturedInvocationInterface) : TermElabM PreparedInvocation := do
  unless wire.value == interface.formal && wire.fragment == interface.fragment do
    throwError "the captured invocation changed its original selected anchor"
  checkCapturedResultInterface wire interface.result
  unless wire.capturedInvocation.isNone do
    throwError "a fresh invocation must retain its previous producer as an explicit operand"
  let occurrence ← nextInvocationOccurrence.modifyGet fun next => (next, next + 1)
  let captured : CapturedInvocation := { occurrence, interface }
  let prepared := PreparedInvocation.mk wire captured
  h.invocations.modify (·.push { prepared })
  return prepared

/-- A separately supplied intrinsic interface must retain the Wire's complete
current assembly and every original child handle before receiving identity. -/
def captureInvocation (h : Harness) (wire : Wire)
    (interface : CapturedInvocationInterface) : TermElabM PreparedInvocation := private_decl% (do
  if let .intrinsic assembly := interface then
    let some current ← currentIntrinsicAssembly? wire
      | throwStratum .unavailable "the captured invocation lost its current complete assembly"
    unless sameIntrinsicAssembly (some current) (some assembly) &&
        sameIntrinsicObservationInput wire { wire with intrinsicAssembly := some assembly } do
      throwStratum .unavailable "the captured invocation changed its selected assembly"
  captureInvocationCore h wire interface)

/-- This private entry derives the intrinsic interface from its sole input.
There is no separately supplied assembly to authenticate against that input. -/
private def captureCurrentIntrinsicInvocation (h : Harness) (wire : Wire) :
    TermElabM PreparedInvocation := do
  let some assembly ← currentIntrinsicAssembly? wire
    | throwStratum .unavailable "the intrinsic observation lost its current complete assembly"
  captureInvocationCore h wire (.intrinsic assembly)

/-- Expose the existing wire reference to the same owner-created preparation.
The canonical input and interface remain together in the invocation table. -/
def retainCapturedInvocation (h : Harness) (wire : Wire)
    (interface : CapturedInvocationInterface) : TermElabM Wire := do
  let prepared ← captureInvocation h wire interface
  return { wire with capturedInvocation := some prepared.captured }

/-- An interpreted intrinsic producer joins the existing invocation owner.
Only its checked administrative anchor can recover a preparation, and its
complete original input graph must still agree. Unanchored synthetic assemblies
and already captured producers keep their own existing observation path. -/
def currentIntrinsicInvocationReference? (h : Harness) (trace : Trace) (wire : Wire) :
    TermElabM (Option PreparedInvocation) := private_decl% (do
  if wire.capturedInvocation.isSome then return none
  let some _ := Trace.producerAnchor? wire.value | return none
  let some node ← trace.node? wire.value
    | throwStratum .unavailable "the intrinsic observation lost its original typed producer"
  Trace.checkProducerRecord wire.value node
  let some _ ← currentIntrinsicAssembly? wire
    | throwStratum .unavailable "the intrinsic observation lost its current complete assembly"
  let records := (← h.invocations.get).filter fun record =>
    (match record.captured.interface with | .intrinsic _ => true | _ => false) &&
      record.input.value == wire.value && sameIntrinsicObservationInput record.input wire
  match records with
  | #[] => return some (← captureCurrentIntrinsicInvocation h wire)
  | #[record] => return some record.prepared
  | _ => throwStratum .unavailable "the intrinsic producer has several canonical preparations")

/-- A separately supplied assembly must still match every original field and
retained child handle before the current producer can enter the owner. Ordinary
observation supplies only its Wire and reads that Wire's own current assembly. -/
def intrinsicInvocationReference? (h : Harness) (trace : Trace) (wire : Wire)
    (assembly : IntrinsicAssembly) : TermElabM (Option Wire) := do
  if wire.capturedInvocation.isSome then return none
  let some _ := Trace.producerAnchor? wire.value | return none
  let some node ← trace.node? wire.value
    | throwStratum .unavailable "the intrinsic observation lost its original typed producer"
  Trace.checkProducerRecord wire.value node
  let some current ← currentIntrinsicAssembly? wire
    | throwStratum .unavailable "the intrinsic observation lost its current complete assembly"
  unless sameIntrinsicAssembly (some current) (some assembly) &&
      sameIntrinsicObservationInput wire { wire with intrinsicAssembly := some assembly } do
    throwStratum .unavailable "the intrinsic observation changed its selected assembly"
  let some prepared ← currentIntrinsicInvocationReference? h trace wire | return none
  return some { prepared.input with capturedInvocation := some prepared.captured }

/-- A migrated use is identified by its original typed producer node. This
predicate does not infer an executable producer from a reduced formal value. -/
def stagedLiftNode (trace : Trace) (formal : Expr) : TermElabM Bool := do
  match ← trace.node? formal with
  | some (.selectedLift ..) | some (.liftFactor ..) => return true
  | some (.liftProjection _ field) => return field != "composed"
  | _ => return false

/-- Reuse a preparation only through the checked producer reference returned
by interpretation. The legacy expression/result table is not consulted. Raw
mathematical terms are not occurrence keys and acquire no recovery behavior. -/
def preparedLiftReference? (h : Harness) (trace : Trace) (formal : Expr) :
    TermElabM (Option Wire) := do
  let some _ := Trace.producerAnchor? formal | return none
  let some node ← trace.node? formal
    | throwError "the selected execution reference lost its original typed producer"
  Trace.checkProducerRecord formal node
  let candidates := (← h.invocations.get).filter fun record =>
    record.captured.interface.staged && record.input.value == formal
  match candidates with
  | #[] => return none
  | #[record] =>
      return some { record.input with capturedInvocation := some record.captured }
  | _ => throwError "the selected producer has more than one canonical preparation"

/-- Installed primitive families seed a finite support calculation. An admitted
family is only a possible leaf here: exact form, ownership and ambiguity remain
the ordinary dispatcher's responsibility at each complete request. -/
def derivationSupport (h : Harness) (entries : Array ComputationDerivationEntry)
    (blocked : Array ComputationRef := #[]) : CoreM (Array ComputationRef) := do
  let state ← registryState
  let direct := h.admitted.filterMap fun registration =>
    (state.operation? registration.registration.operation).bind ComputationDerivation.reference?
  return ComputationDerivation.grounded entries direct.contains blocked

/-- Whether an ordinary observation has any finitely supported proved plan.
This does not admit a request or select a mathematical operation. -/
def hasGroundedDerivation (h : Harness) (operation : String) : CoreM Bool := do
  if h.derivation.isNone then return false
  let state ← registryState
  let some reference := (state.operation? operation).bind ComputationDerivation.reference?
    | return false
  let entries ← computationDerivations
  let support ← derivationSupport h entries #[reference]
  return entries.any fun entry => entry.target == reference &&
    entry.prerequisites.all support.contains

/-- Preserve occurrences without an expression-keyed lookup or an equality-based
presentation choice. A request stores the returned indices as runtime metadata. -/
def retainServiceOperands (h : Harness) (wires : Array Wire) : IO (Array Nat) :=
  h.serviceOperands.modifyGet fun prior =>
    ((List.range wires.size).toArray.map (prior.size + ·), prior ++ wires)

/-- Bind exact public request positions to existing complete operands. The
builder supplies every path before any lookup; equal packets never select an
occurrence or merge two positions. -/
def retainServiceInputPaths (h : Harness) (data : DataOwnership.Data)
    (inputs : Array (DataOwnership.Path × Wire)) :
    TermElabM (Array (DataOwnership.Path × Nat)) := do
  discard <| checkedFragment data.validate
  let mut selected : Array DataOwnership.Path := #[]
  for (path, wire) in inputs do
    if selected.contains path then
      throwError "one service input path has several selected operand occurrences"
    selected := selected.push path
    unless (← checkedFragment (data.project path)) == wire.fragment do
      throwError "a service input path changed its complete operand packet or suppliers"
  let handles ← retainServiceOperands h (inputs.map Prod.snd)
  return (inputs.map Prod.fst).zip handles

/-- A request builder refreshes only its own declared positions after observing
their operands. Paths beneath those positions belong to the new exact frame. -/
def replaceServiceInputPaths (h : Harness) (data : DataOwnership.Data)
    (previous : Array (DataOwnership.Path × Nat))
    (current : Array (DataOwnership.Path × Wire)) :
    TermElabM (Array (DataOwnership.Path × Nat)) := do
  let remaining := previous.filter fun (path, _) =>
    !current.any (fun (prefixPath, _) => (DataOwnership.stripPrefix? prefixPath path).isSome)
  return remaining ++ (← retainServiceInputPaths h data current)

/-- Where the installed leaves' manifest is, when no path is given: the environment variable
`CAS_LEAVES`, naming the leaves package's directory (a checkout of `lean-cas-dsl-leaves`) or its
`leaves.json` itself; else `.lake/packages/cas_leaves`, where a checkout of the leaves conventionally
lives. The leaves are not a Lake dependency: they ship no Lean, and the kernel imports nothing from
them (`specs/leaf-registration.md`). -/
def leavesManifest : IO System.FilePath := do
  match ← IO.getEnv "CAS_LEAVES" with
  | some leaves =>
      let leaves : System.FilePath := leaves
      return if leaves.extension == some "json" then leaves else leaves / manifestFile
  | none => return (".lake" / "packages" / "cas_leaves" : System.FilePath) / manifestFile

/-- The harness of the manifest at `path`, or of the installed leaves' manifest
(`leavesManifest`). No manifest is no leaf. A manifest that does not read is reported and admits
nothing. -/
def Harness.load (path? : Option System.FilePath := none) : CoreM Harness := do
  let path ← match path? with
    | some path => pure path
    | none => leavesManifest
  unless ← path.pathExists do return ← Harness.empty
  match ← Manifest.read path with
  | .error message =>
      logWarning m!"the manifest {path} is not read, and admits nothing: {message}"
      Harness.empty
  | .ok manifest => Harness.ofManifest (path.parent.getD ".") manifest

/-- Start the program `backend` in `root` and read its `ready` announcement. Nothing the
announcement says is consulted: which operations are called on it is the registrations'. -/
def start (root : System.FilePath) (backend : BackendProgram) :
    IO (Except Backend.PortError Backend.Conn) := do
  -- The program finds the port's reference implementation `cas_port` on its `PYTHONPATH`.
  let portPython ← try
      IO.FS.realPath ((← Backend.packageDir Backend.contractPackage) / "python")
    catch error => return .error (.unavailable backend.name
      s!"the public protocol helper is unavailable: {error}")
  let path := match ← IO.getEnv "PYTHONPATH" with
    | some p => s!"{portPython}:{p}"
    | none => portPython.toString
  -- Direct harness invocations have the same engine default as `just harness`.
  -- Explicit engine selections always take precedence over the workspace venv.
  let workspacePython := (← IO.currentDir) / ".venv" / "bin" / "python"
  let enginePython := if ← workspacePython.pathExists then some workspacePython.toString else none
  let sagePython := (← IO.getEnv "CAS_SAGE_PYTHON").orElse fun _ => enginePython
  let gapPython := (← IO.getEnv "CAS_GAP_PYTHON").orElse fun _ => enginePython
  let child ← try
      IO.Process.spawn { toStdioConfig := Backend.Stdio, cmd := backend.command
                         args := backend.args, cwd := some root
                         env := #[("PYTHONPATH", some path),
                                  ("CAS_SAGE_PYTHON", sagePython),
                                  ("CAS_GAP_PYTHON", gapPython)] }
    -- not a reading fallback: a program that cannot start is the unavailable stratum
    catch e => return .error (.unavailable backend.name s!"cannot start {backend.command}: {e}")
  match (← Backend.readFrame child.stdout) >>= Backend.readyOf with
  | .ok ready => return .ok { child, ready, nextId := ← IO.mkRef 1 }
  | .error e =>
      Backend.abort child
      return .error (.unavailable backend.name s!"no ready frame ({e.render})")

/-- The connection to the backend `name`, started on first use. -/
def Harness.connection (h : Harness) (name : String) :
    IO (Except Backend.PortError BackendSession) := do
  if let some connection := (← h.connections.get)[name]? then return connection
  let connection ← match h.backends.find? (·.name == name) with
    | some backend => do
        match ← start h.root backend with
        | .error error => pure (.error error)
        | .ok connection =>
            let identity ← nextBackendSession.modifyGet fun n => (n, n + 1)
            pure (.ok { identity, connection })
    | none => pure (.error (.unavailable name "not declared in the manifest"))
  h.connections.modify (·.insert name connection)
  return connection

/-- Stop every started backend. -/
def Harness.stop (h : Harness) : IO Unit := do
  let connections ← h.connections.get
  h.connections.set {}
  h.results.set {}
  h.actions.set #[]
  h.replies.set #[]
  h.services.set #[]
  h.derivations.set #[]
  h.portFailures.set 0
  h.serviceOperands.set #[]
  h.invocations.set #[]
  -- A backend is killed, not asked to exit: nothing it does is waited on or believed, and
  -- closing its input cannot be relied on while other references to the handle are alive.
  for (_, connection) in connections.toList do
    if let .ok c := connection then Backend.abort c.connection.child

/-- Validate every exact supplier before admission or reuse. A missing bridge
between live sessions is a computation gap; an expired supplier is unavailable. -/
def checkDataOwners (h : Harness) (data : DataOwnership.Data) : TermElabM Unit := do
  discard <| checkedFragment data.validate
  for (backend, identity) in DataOwnership.owners data.ownership do
    let some (.ok session) := (← h.connections.get)[backend]?
      | throwStratum .unavailable "the computational value's owning session is unavailable"
    unless session.identity == identity do
      throwStratum .unavailable "the computational value belongs to an expired backend session"

/-- Recover the already registered identity of a complete action descriptor.
The selected formal action independently checks its actual parameters. -/
partial def descriptorEdge? (state : RegistryState) (json : Json) : Option EdgeRef := do
  let tag ← (json.getObjValAs? String "ctor").toOption
  let args ← ((json.getObjVal? "args").bind (·.getArr?)).toOption
  if let some entry := state.functors.find? (·.id.raw == tag) then
    return .functor entry.id
  match tag, args with
  | "classifierForget", #[id, _] =>
      let id ← id.getStr?.toOption
      let entry ← state.classifiers.find? (·.id.raw == id)
      some (.classifierForget entry.id)
  | "constructorMap", #[id, inner] =>
      let id ← id.getStr?.toOption
      let entry ← state.constructors.find? (·.id.raw == id)
      some (.constructMap entry.id (← descriptorEdge? state inner))
  | _, _ => none

/-- The selected operation, input address and backend identify one registration. -/
def sameRegistration (first second : Registration) : Bool :=
  first.operation == second.operation && first.input == second.input &&
    first.backend == second.backend

/-- The complete applicable registration set, before starting a process. Exact
and category-wide forms and all eligible backends retain equal standing. -/
def admittedRegistrations (h : Harness) (operation : String) (input : Wire)
    (completeRequest : Bool := false) : TermElabM (Array Admitted) := do
  let state ← registryState
  let some declared := state.operation? operation
    | throwError "the requested computational operation is no longer registered"
  let mut addresses := state.inputAddresses declared input.form
  if completeRequest then
    match declared with
    | .functor _ | .construction _ false | .edgeAction _ false =>
      let .ok invocation := Backend.ConstructionInvocation.decode operation input.json
        | throwError "a complete object action lost its selected public request framing"
      if let .edgeAction edge false := declared then
        let #[descriptor] := invocation.parameters
          | throwError "a derived object action lost its complete selected action parameter"
        unless descriptorEdge? state descriptor == some edge do
          throwError "a derived object request changed its selected registered edge"
      addresses := state.objectActionInputAddresses declared input.form
    | .method entry =>
      let .ok _ := Backend.ConstructionInvocation.decodeMethod
          operation entry.functor.raw input.json
        | throwError "a complete method lost its selected public invocation framing"
    | .presentation _ =>
      let .ok _ := Backend.PresentationInvocation.decode input.json
        | throwError "a complete comparison request lost its published presentation framing"
      addresses := state.presentationInputAddresses declared input.form
    | _ =>
      let .ok invocation := Backend.PointInvocation.decode input.json
        | throwError "a complete callable request lost its published point-invocation framing"
      unless invocation.operation == operation do
        throwError "a complete callable request changed its declared operation"
      if let .functorMap entry := declared then
        let .ok ("map", #[action, original]) := ComputationalData.envelope invocation.arrow
          | throwError "a functor map request lost its complete selected action and source map"
        let .ok (identifier, parameters) := ComputationalData.envelope action
          | throwError "a functor map request lost its selected declaration parameters"
        unless identifier == entry.id.raw && parameters == invocation.parameters do
          throwError "a functor map request changed its complete selected declaration"
        unless DataOwnership.project
            #[.field "args", .index 2, .field "args", .index 0, .field "args"] input.ownership ==
            DataOwnership.project #[.field "args", .index 1] input.ownership do
          throwStratum .malformed "a functor map request changed a selected parameter supplier"
        let .ok _ := Backend.TypedMap.decode original
          | throwError "a functor map request lost its actual source map endpoint fields"
      if let .edgeAction edge true := declared then
        let .ok ("map", #[descriptor, original]) := ComputationalData.envelope invocation.arrow
          | throwError "a derived map request lost its full selected action and original map"
        unless invocation.parameters == #[descriptor] &&
            descriptorEdge? state descriptor == some edge do
          throwError "a derived map request changed its selected edge or complete action parameters"
        unless DataOwnership.project
            #[.field "args", .index 2, .field "args", .index 0] input.ownership ==
            DataOwnership.project #[.field "args", .index 1, .index 0] input.ownership do
          throwStratum .malformed "a derived map request changed a selected action supplier"
        let .ok _ := Backend.TypedMap.decode original
          | throwError "a derived map request lost its actual source map endpoint fields"
      addresses := state.pointInputAddresses declared input.form
  return h.admitted.filter fun a =>
    a.registration.operation == operation && addresses.contains a.registration.input &&
      (DataOwnership.owners input.ownership).all (fun owner => owner.1 == a.registration.backend)

/-- Send the value `input` to the admitted registration of `operation` on its form, and read the
answer: untrusted JSON, with the backend that gave it. -/
def sendData (h : Harness) (operation : String) (input : Wire)
    (comparisons : Array NaturalTransformationId := #[]) (completeRequest : Bool := false)
    (selected : Option Registration := none) :
    TermElabM ComputationalReply := do
  checkDataOwners h input.fragment
  let registrations ← admittedRegistrations h operation input completeRequest
  if registrations.isEmpty && selected.isNone then
    if let some derive := h.derivation then
      let result ← derive operation input completeRequest
      checkDataOwners h result.data
      return result
  let registration ← match selected with
    | some selected => do
        unless registrations.any (fun row => sameRegistration row.registration selected) do
          throwStratum .noImplementation
            "the selected registration cannot consume the actual data with these suppliers"
        pure selected
    | none => match registrations with
      | #[r] => pure r.registration
      | #[] => throwStratum .noImplementation m!"no admitted registration computes {operation} on \
          the form {input.formId}"
      | _ =>
          let backends := registrations.toList.map (·.registration.backend)
          throwStratum .ambiguousRealization m!"several admitted registrations compute \
            {operation} on the form {input.formId} ({backends}); which one is used is a choice \
            the kernel does not make"
  let connection ← if let some (backend, identity) := input.owner? then do
    let some (.ok session) := (← h.connections.get)[backend]?
      | throwStratum .unavailable "the computational value's owning session is unavailable"
    unless session.identity == identity && backend == registration.backend do
      throwStratum .unavailable "the computational value belongs to a different backend session"
    pure session
  else
    match ← (h.connection registration.backend : IO _) with
    | .ok session => pure session
    | .error e => throwStratum .unavailable m!"{e.render}"
  let observation := [("operation", toJson operation), ("input", toJson input.formId),
    ("registrationInput", toJson registration.input),
    ("backend", toJson registration.backend), ("session", toJson connection.identity),
    ("inputOwner", toJson input.owner?), ("inputOwnership", toJson input.ownership),
    ("request", input.json)] ++
    (if comparisons.isEmpty then [] else [("comparisons", toJson (comparisons.map (·.raw)))])
  let observedIndex : Option Nat ← match h.dispatches with
    | none => pure none
    | some observations =>
      pure (some (← observations.modifyGet fun entries =>
        (entries.size, entries.push (Json.mkObj observation))))
  match ← (Backend.call connection.connection operation input.json : IO _) with
  | .ok answer =>
      if let some observations := h.dispatches then
        if let some index := observedIndex then
          observations.modify fun entries =>
            entries.set! index (Json.mkObj (observation ++ [("response", answer)]))
      let index ← h.replies.modifyGet fun entries => (entries.size, entries.push {
        operation, input, backend := registration.backend
        session := connection.identity, original := answer })
      let reply : ComputationalReply := {
        data := DataOwnership.Data.capture answer (registration.backend, connection.identity)
        backend := registration.backend }
      let completed ← match h.deferred with
        | none => pure reply
        | some complete => complete operation input reply
      checkDataOwners h completed.data
      h.replies.modify fun entries => entries.modify index fun entry =>
        { entry with
          completed := some (completed.data.json, completed.backend)
          completedOwnership := completed.data.ownership }
      if completed.data.json != answer || completed.backend != registration.backend then
        if let some observations := h.dispatches then
          if let some index := observedIndex then
            observations.modify fun entries => entries.set! index
              (Json.mkObj (observation ++ [("response", answer),
                ("completedResponse", completed.data.json),
                ("dataBackend", toJson completed.backend),
                ("completedOwnership", toJson completed.data.ownership)]))
      return completed
  | .error e =>
      h.portFailures.modify (· + 1)
      if let some observations := h.dispatches then
        if let some index := observedIndex then
          observations.modify fun entries =>
            entries.set! index (Json.mkObj (observation ++ [("failure", toJson e.render)]))
      throwStratum e.stratum m!"{e.render}"

/-- The raw observation interface remains available to callers that decode a
portable result immediately. Runtime data adoption uses `sendData` so nested
ownership never has to be reconstructed from these bytes. -/
def send (h : Harness) (operation : String) (input : Wire)
    (comparisons : Array NaturalTransformationId := #[]) (completeRequest : Bool := false) :
    TermElabM (Json × String) := do
  let reply ← sendData h operation input comparisons completeRequest
  return (reply.data.json, reply.backend)

/-- The answer `answer` of `backend` to `operation` is not a value of the operation's result
form. -/
def malformed (backend operation : String) (answer : Json) (message : String) : TermElabM α :=
  throwStratum .malformed m!"the answer of {backend} to {operation} is not a value of its \
    result form: {message} (the answer was {answer.compress})"

/-- Detect opaque references in complete nested computational data. -/
partial def containsOpaqueData (json : Json) : Bool :=
  if (json.getObjValAs? String "ctor").toOption == some "opaqueData" then true
  else match json with
    | .arr data => data.any containsOpaqueData
    | .obj fields => fields.any fun _ value => containsOpaqueData value
    | _ => false

/-- Open the public value envelope together with its exact ownership projection.
No child supplier is reconstructed from a completed packet's backend label. -/
def receiveReplyFragment (h : Harness) (operation : String) (reply : ComputationalReply)
    (structured : Bool := false) : TermElabM DataOwnership.Data := do
  checkDataOwners h reply.data
  match Backend.ComputationalValue.decode reply.data.json with
  | .ok (.opaque _) => return reply.data
  | .ok (.inline _) =>
      checkedFragment (reply.data.project #[.field "args", .index 0])
  | .error message =>
      unless structured do malformed reply.backend operation reply.data.json message
      return reply.data

def receiveReplyData (h : Harness) (operation : String) (reply : ComputationalReply)
    (structured : Bool := false) : TermElabM ComputationData := do
  let data ← receiveReplyFragment h operation reply structured
  return if data.ownership.isEmpty then .inline data.json else .scoped data

/-- Adopt a direct response from its one known process. Nested service execution
uses `receiveReplyData`, retaining the separately carried occurrence table. -/
def receiveComputationalData (h : Harness) (backend operation : String) (json : Json)
    (structured : Bool := false) : TermElabM ComputationData := do
  let data ← if containsOpaqueData json then do
    let some (.ok session) := (← h.connections.get)[backend]?
      | throwStratum .unavailable "the returned value has no live owning session"
    pure (DataOwnership.Data.capture json (backend, session.identity))
  else pure { json : DataOwnership.Data }
  receiveReplyData h operation { data, backend } structured

/-- Completed field packets can share a fixed formal port and portable bytes
while retaining distinct producing requests. Keep that existing request receipt
in the action cache key. Re-retaining the same Wire preserves its handle vector;
a conservative cache miss cannot substitute another production's result.
This comparison is deliberately local to completed action reuse, not cycle detection. -/
private def sameActionCacheOperand (left right : Wire) : Bool :=
  sameActionOperand left right && left.serviceHandles == right.serviceHandles

private def sameActionCacheOperands (left right : Array Wire) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) => sameActionCacheOperand a b

/-- Reuse a completed action only on the same selected functor and actual
operands, including their retained producing requests. Map keys include both
actual image endpoints, as well as the source map. -/
@[no_expose] def retainedActionResult? (h : Harness) (operation : String) (action : Expr)
    (input : Wire) (parameters : Array Json) (dependencies images : Array Wire)
    (parameterOwnership : DataOwnership.Table := #[]) : TermElabM (Option Wire) := do
  let result := ((← h.actions.get).find? fun record =>
    record.operation == operation && record.action == action &&
      sameActionCacheOperand record.input input && record.parameters == parameters &&
      record.parameterOwnership == parameterOwnership &&
      sameActionCacheOperands record.parameterInputs dependencies &&
      sameActionCacheOperands record.imageEndpoints images).map (·.result)
  if let some actual := result then
    checkDataOwners h actual.fragment
  return result

def retainActionResult (h : Harness) (record : ActionExecution) : IO Unit := do
  h.actions.modify (·.push record)
  let formal := record.result.value
  unless formal.hasMVar || formal.hasLevelMVar || formal.hasFVar || formal.hasLooseBVars do
    h.results.modify (·.insert formal record.result)

/-- Call the admitted registration of `operation` on the value `input`, and decode the answer as
a value of `resultType`. -/
def call (h : Harness) (operation : String) (input : Wire) (resultType : Expr)
    (comparisons : Array NaturalTransformationId := #[]) :
    TermElabM (Expr × Json) := do
  let reply ← sendData h operation input comparisons
  let answer := reply.data.json
  let backend := reply.backend
  match ← Codec.decode resultType answer with
  | .ok value => return (value, answer)
  | .error message => malformed backend operation answer message

/-- The value of the registered family `declaration` (the denotation of a literal form, the
standard cone constructor of a shape) at the answer `args`, as a value of `expected`. The
family's arguments are taken in order: one the expected type determines is what it determines;
an instance is synthesized; a proposition is checked by kernel decision and generic structural
proof assembly (`CasCatalogue.Codec.conditionProof`); a condition that cannot be independently
proved rejects the answer. Binder annotations never run their tactics. Every other
argument is the next value of `args`,
decoded by `decodeArg` at its type. The decoded arguments are returned with their forms, when
they are values of a registered form. Too few or too many values reject the answer. -/
def decodeFamily (declaration : Name) (expected : Expr) (args : Array Json)
    (decodeArg : Expr → Json → TermElabM (Except String (Expr × Option Form)))
    (accepted? : Option Expr := none) (completeParameters : Bool := false) :
    TermElabM (Except String (Expr × Array (Expr × Option Form))) := do
  let c ← mkConstWithFreshMVarLevels declaration
  let (mvars, infos, type) ← forallMetaTelescopeReducing (← inferType c)
  unless ← isDefEq type expected do
    return .error s!"{declaration} does not form a value of {expected}"
  if let some accepted := accepted? then
    let canonical ← withoutModifyingState do
      unless ← withTransparency .all <| isDefEq (← inferType accepted) expected do return none
      let mut positions : Array Expr := #[]
      for (arg, info) in mvars.zip infos do
        unless (← instantiateMVars arg).isMVar do continue
        let fieldType ← instantiateMVars (← inferType arg)
        if info.isInstImplicit || (← isProp fieldType) then continue
        if !info.isExplicit && fieldType.hasMVar then continue
        positions := positions.push arg
      unless positions.size == args.size do return none
      unless ← withTransparency .all <| isDefEq (mkAppN c mvars) accepted do return none
      let mut fields := #[]
      for (parameter, data) in positions.zip args do
        let parameter ← instantiateMVars parameter
        if parameter.hasMVar || parameter.hasLevelMVar then return none
        match ← decodeArg (← inferType parameter) data with
        | .error _ => return none
        | .ok (value, form) =>
            unless ← withTransparency .all <| isDefEq value parameter do return none
            fields := fields.push (value, form)
      -- Every supplied apex and defining map agrees with the independently accepted cone.
      -- Its mathematical equations are retained rather than recomputed on infinite carriers.
      return some (accepted, fields)
    if let some result := canonical then return .ok result
  let mut remaining := args.toList
  let mut decoded : Array (Expr × Option Form) := #[]
  let mut postponed : Array Expr := #[]
  for (m, info) in mvars.zip infos do
    let t ← instantiateMVars (← inferType m)
    let fixed := !(← instantiateMVars m).isMVar
    let supplied := completeParameters && info.isExplicit && !(← isProp t)
    if fixed && !supplied then continue
    if completeParameters && !info.isExplicit && !info.isInstImplicit then
      postponed := postponed.push m
      continue
    if !info.isExplicit && t.hasMVar then
      postponed := postponed.push m
      continue
    if info.isInstImplicit then
      match ← Codec.dataInstance t with
      | some inst => discard <| isDefEq m inst
      | none => return .error s!"no instance of {t} is found"
    else if ← isProp t then
      -- Binder annotations such as autoParam carry elaboration instructions, not another
      -- mathematical condition. Decide their reduced proposition without running the tactic.
      let condition ← whnfR t
      if condition.hasMVar then
        return .error s!"a condition of {declaration} is not determined by the answer"
      let mut proof? ← Codec.conditionProof condition
      -- Reflexivity needs no Decidable instance and changes no commuting equation.
      -- The independently constructed proof is checked against the complete condition.
      if proof?.isNone then
        if let some (_, left, right) := condition.eq? then
          if ← isDefEq left right then
            let reflexive ← mkEqRefl left
            if ← Decide.kernelAccepts condition reflexive then proof? := some reflexive
      let some proof := proof?
        | return .error s!"the kernel does not establish a condition of {declaration}"
      unless ← isDefEq m proof do
        return .error s!"the checked proof does not inhabit a condition of {declaration}"
    else
      let j :: rest := remaining
        | return .error s!"the answer has {args.size} values, and {Codec.label declaration} \
            takes more (its next is a {t})"
      remaining := rest
      match ← decodeArg t j with
      | .error message => return .error message
      | .ok (v, form) =>
          unless ← isDefEq m v do return .error s!"{j.compress} is not a {t}"
          decoded := decoded.push (v, form)
  for m in postponed do
    unless (← instantiateMVars m).isMVar do continue
    let type ← instantiateMVars (← inferType m)
    let value? ← if ← isProp type then Codec.conditionProof (← whnfR type)
      else Codec.dataInstance type
    let some value := value?
      | return .error s!"{declaration} has an undetermined implicit parameter of type {type}"
    unless ← isDefEq m value do
      return .error s!"the implicit parameter does not inhabit {type}"
  unless remaining.isEmpty do
    return .error s!"the answer has {args.size} values, and {Codec.label declaration} takes \
      {args.size - remaining.length}"
  return .ok (← instantiateMVars (mkAppN c mvars), decoded)

/-- Public declaration descriptors carry every explicit data parameter, including
parameters already fixed by the expected dependent result type. Those values are
consumed and checked in place; they never shift later arguments or replace the fixed
selected structure. Constructor data ports use `decodeFamily`'s separate inferred-port
convention. No proof or instance is accepted as computational data. -/
def decodeDeclaration (declaration : Name) (expected : Expr) (args : Array Json)
    (decodeArg : Expr → Json → TermElabM (Except String (Expr × Option Form))) :
    TermElabM (Except String (Expr × Array (Expr × Option Form))) :=
  decodeFamily declaration expected args decodeArg none true

/-- The registered literal form of the category `category`: the result form of an operation
landing there. -/
def resultForm (state : RegistryState) (category : CategoryId) (what : MessageData) :
    TermElabM (LiteralEntry × Expr) := do
  let some form := state.literals.find? (·.category == category)
    | let name := (state.categories.find? (·.id == category)).map (·.name) |>.getD category.raw
      throwStratum .noImplementation m!"{what} is an object of {name}, which has no registered \
        literal form: nothing decodes it"
  return (form, ← mkConstWithFreshMVarLevels form.type)

/-- The registered named object `entry` at the parameters `params` (closed terms), elaborated and
recorded in `trace` as the semantic reading records one. -/
def objectAt (trace : Trace) (entry : ObjectEntry) (params : Array Expr) : TermElabM Expr := do
  Semantic.object entry (← params.mapM exprToSyntax) (some trace)

/-- An operation agreement wraps its selected result without replacing that result's
original operation trace. The strict syntactic child prevents recursive alias provenance;
the independent validator checks the complete universal families and every retained source. -/
def checkOperationEquivalence (wrapper representative : Expr) (chosen : Nat)
    (candidates : Array OperationCandidate) (comparisons : Array OperationFamilyComparison) :
    TermElabM Unit := do
  OperationAgreement.validate representative chosen candidates comparisons
  let wrapper ← instantiateMVars wrapper
  let representative ← instantiateMVars representative
  let mut inner := wrapper.consumeMData
  let mut retainedChild := false
  while inner.isAppOfArity ``id 2 do
    inner := inner.appArg!.consumeMData
    if inner == representative.consumeMData then
      retainedChild := true
      break
  unless retainedChild && wrapper != representative do
    throwError "the operation agreement lost its distinct original-result wrapper"
  unless !wrapper.hasMVar && !wrapper.hasLevelMVar && !wrapper.hasFVar &&
      !wrapper.hasLooseBVars && (← isTypeCorrect wrapper) &&
      (← withTransparency .all <| isDefEq (← inferType wrapper) (← inferType representative)) &&
      (← withTransparency .all <| isDefEq wrapper representative) do
    throwError "the operation agreement wrapper changed its complete selected value or type"

/-- Reframe only actual data of the already checked representative. All computational
metadata, including its owner and complete interfaces, stay attached to that same payload. -/
def forwardOperationEquivalent (wrapper representative : Expr) (actual : Wire) :
    TermElabM Wire := do
  unless (← withTransparency .all <|
      isDefEq (← inferType actual.value) (← inferType representative)) &&
      (← withTransparency .all <| isDefEq actual.value representative) do
    throwError "the operation agreement received data for a different complete result"
  forwardRetainedValue actual wrapper

/-- Recover parameters through an exact published object family occurring inside
the requested value. Agreement is checked on fresh typed parameters, so a match
at one actual value or carrier cannot supply an unrelated presentation. Only then
are the original declaration arguments restored; no default or cached data is used. -/
def completeObjectFamilyApplication? (declaration : Name) (value source : Expr) :
    TermElabM (Option Expr) := withoutModifyingState do
  let state ← registryState
  unless FunctorActionData.closedParameter value &&
      FunctorActionData.closedParameter source &&
      state.objects.any (fun row => source.getAppFn.constName? == some row.declaration) &&
      (value.find? (· == source)).isSome do return none
  forallTelescopeReducing (← inferType source.getAppFn) fun parameters _ => do
    unless parameters.size == source.getAppNumArgs do return none
    let family := mkAppN source.getAppFn parameters
    let generalized := value.replace fun term => if term == source then some family else none
    unless ← isTypeCorrect generalized do return none
    let constant ← mkConstWithFreshMVarLevels declaration
    let (fields, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
    let arguments := (fields.zip infos).filterMap fun (field, info) =>
      if info.isExplicit then some field else none
    let supplied ← parameters.filterM fun field => return (← field.fvarId!.getBinderInfo).isExplicit
    unless arguments.size == supplied.size do return none
    for (argument, parameter) in arguments.zip supplied do
      unless ← withTransparency .all <|
          isDefEq (← inferType argument) (← inferType parameter) <&&> isDefEq argument parameter do
        return none
    let application := mkAppN constant fields
    unless ← withTransparency .all <|
        isDefEq (← inferType application) (← inferType generalized) <&&>
          isDefEq application generalized do return none
    let application ← instantiateMVars application
    if application.hasMVar || application.hasLevelMVar then return none
    let concrete := application.replaceFVars parameters source.getAppArgs
    unless FunctorActionData.closedParameter concrete && (← isTypeCorrect concrete) do return none
    unless ← withTransparency .all <|
        isDefEq (← inferType concrete) (← inferType value) <&&> isDefEq concrete value do return none
    unless ← Decide.kernelAccepts (← mkEq concrete value) (← mkEqRefl concrete) do
      throwError "the recovered whole object family failed its original kernel check"
    return some concrete

/-- Accepted presentations of a complete closed object. A literal declaration keeps
its exact ordered arguments. Recovery otherwise checks both the full object type
and its whole value; equal carriers do not identify structure dictionaries. This is
execution metadata and never participates in reading the mathematical question. -/
def completeNamedObjectPresentations (value : Expr) :
    TermElabM (Array (ObjectEntry × Array Expr)) := do
  let value ← instantiateMVars value
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return #[]
  let state ← registryState
  let mut selected := Trace.unanchor value.consumeMData
  while selected.isAppOfArity ``id 2 do
    selected := Trace.unanchor selected.appArg!.consumeMData
  let direct := state.objects.filter fun entry =>
    selected.getAppFn.constName? == some entry.declaration
  let sources ← IO.mkRef (#[] : Array Expr)
  if direct.isEmpty then
    value.forEach fun term => do
      if term != value && FunctorActionData.closedParameter term &&
          state.objects.any (fun row => term.getAppFn.constName? == some row.declaration) then
        sources.modify fun previous => if previous.contains term then previous else previous.push term
  let mut candidates := #[]
  for entry in (if direct.isEmpty then state.objects else direct) do
    let candidate ← withoutModifyingState do
      let application ← if direct.isEmpty then instantiateFresh entry.declaration
        else pure selected
      -- A fixed whole object can determine a selected bundled parameter through
      -- its projections even when ordinary unification cannot assign that bundle.
      -- Expose only fresh structure fields; the repeated full typed comparison
      -- must determine all of them from the original requested object.
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType application) (← inferType value) <&&>
            isDefEq application value) do
        CategoryContext.exposeStructureParameters application
      unless ← withTransparency .all <|
          isDefEq (← inferType application) (← inferType value) <&&>
            isDefEq application value do return none
      let application ← instantiateMVars application
      unless FunctorActionData.closedParameter application &&
          (← isTypeCorrect application) do return none
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      unless application.getAppNumArgs == infos.size do return none
      unless ← Decide.kernelAccepts (← mkEq application value) (← mkEqRefl application) do
        throwError "the complete named-object presentation failed its original kernel check"
      return some ((application.getAppArgs.zip infos).filterMap fun (arg, info) =>
        if info.isExplicit then some arg else none)
    if let some parameters := candidate then candidates := candidates.push (entry, parameters)
    if direct.isEmpty then
      for source in ← sources.get do
        let some application ← completeObjectFamilyApplication? entry.declaration value source
          | continue
        let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
          xs.mapM (·.fvarId!.getBinderInfo)
        unless application.getAppNumArgs == infos.size do continue
        let parameters := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
          if info.isExplicit then some argument else none
        unless candidates.any (fun (previous, arguments) =>
            previous.id == entry.id && arguments == parameters) do
          candidates := candidates.push (entry, parameters)
  return candidates

/-- Retain a uniquely checked complete named presentation on the execution trace.
No equal cached object is searched or substituted for the selected value. -/
def recordCompleteNamedObject (trace : Trace) (value : Expr) : TermElabM Bool := do
  let candidates ← completeNamedObjectPresentations value
  match candidates with
  | #[] => return false
  | #[(entry, parameters)] =>
      Trace.record (some trace) value (.object entry.id parameters)
      return true
  | _ => throwStratum .ambiguousRealization m!"the complete selected object has several accepted \
      data presentations: {candidates.map (·.1.id.raw)}"

/-- A complete accepted declaration at an already fixed value or whole functor.
Literal arguments retain priority; otherwise every structure field must be fixed
by the full typed comparison. No class, dictionary or data argument is defaulted. -/
def completeDeclarationApplication? (declaration : Name) (value : Expr)
    (asFunctor : Bool := false) : TermElabM (Option (Expr × Array Expr)) :=
  DeclaredApplication.complete? declaration value asFunctor

/-- Registered presentations of the entire category bundle, including its Hom,
identity and composition dictionary. A shared carrier is never a match. -/
def completeNamedCategoryPresentations (value : Expr) :
    TermElabM (Array (NamedCategoryEntry × Array Expr)) := do
  let state ← registryState
  let value ← instantiateMVars value
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return #[]
  let categoryType ← mkConstWithFreshMVarLevels ``CategoryTheory.Cat
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType value) categoryType) do return #[]
  let mut selected := Trace.unanchor value.consumeMData
  while selected.isAppOfArity ``id 2 do
    selected := Trace.unanchor selected.appArg!.consumeMData
  let direct := state.categories.filter fun entry =>
    selected.getAppFn.constName? == some entry.declaration
  let mut candidates := #[]
  for entry in (if direct.isEmpty then state.categories else direct) do
    if let some (_, parameters) ← completeDeclarationApplication? entry.declaration value then
      candidates := candidates.push (entry, parameters)
  return candidates

def recordCompleteNamedCategory (trace : Trace) (value : Expr) : TermElabM Bool := do
  let candidates ← completeNamedCategoryPresentations value
  match candidates with
  | #[] => return false
  | #[(entry, parameters)] =>
      Trace.record (some trace) value (.categoryParameter entry.id parameters)
      return true
  | _ => throwStratum .ambiguousRealization m!"the complete category dictionary has several \
      accepted data presentations: {candidates.map (·.1.id.raw)}"

/-- A literal core object retains its own underlying object. Its category comes
only from the selected construction's full source bundle, independently checked
against the accepted core constructor, never from the object's carrier alone. -/
def recordConstructionCoreSource (trace : Trace) (action : DirectConstruction.Action)
    (receiver : Expr) : TermElabM Unit := do
  if (← trace.node? receiver).isSome then return
  let literal := Trace.unanchor receiver.consumeMData
  unless literal.isAppOf ``CategoryTheory.Core.mk do return
  let state ← registryState
  let #[constructor] := state.constructors.filter (·.semantics == `CasCatalogue.Constructors.core)
    | return
  let (source, _) ← functorCategoryBundles action.functor
  let some (_, #[bundle]) ← completeDeclarationApplication? constructor.semantics source
    | return
  let candidates ← completeNamedCategoryPresentations bundle
  let #[(entry, _)] := candidates
    | if candidates.isEmpty then return
      else
        throwStratum .ambiguousRealization
          "the construction's complete core source has several accepted category presentations"
  let context : CategoryContext := { expression := entry.expression, bundle }
  let original := literal.appArg!
  CategoryContext.checkObject context original
  let coreContext ← CategoryContext.construct context constructor.id
  unless ← withTransparency .all <| isDefEq coreContext.bundle source do
    throwError "the literal core receiver changed the selected complete source category"
  CategoryContext.checkObject coreContext receiver
  let expected ← mkAppM ``CategoryTheory.Core.mk #[original]
  unless ← Decide.kernelAccepts (← mkEq expected receiver) (← mkEqRefl expected) do
    throwError "the literal core receiver changed its original underlying object"
  Trace.record (some trace) receiver (.coreObject context original)

/-- Recover a literal object action only from a unique complete registered
construction. Agreement at a single receiver never selects an action. -/
def completeLiteralConstruction? (value : Expr) : TermElabM (Option DirectConstruction.Action) := do
  let value ← instantiateMVars value
  let some (functor, receiver) := FunctorActionData.objectAction? value | return none
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return none
  let state ← registryState
  let mut literal := Trace.unanchor functor.consumeMData
  while literal.isAppOfArity ``id 2 || literal.isAppOf ``CategoryTheory.Cat.Hom.toFunctor do
    literal := Trace.unanchor literal.appArg!.consumeMData
  let direct := state.constructions.filter fun entry =>
    literal.getAppFn.constName? == some entry.declaration
  let mut candidates : Array DirectConstruction.Action := #[]
  for entry in (if direct.isEmpty then state.constructions else direct) do
    let some (_, parameters) ← completeDeclarationApplication? entry.declaration functor true
      | continue
    let action ← DirectConstruction.select entry (← parameters.mapM exprToSyntax) receiver
    let image ← DirectConstruction.obj action receiver
    unless ← withTransparency .all <|
        isDefEq (← inferType image) (← inferType value) <&&> isDefEq image value do
      throwError "the complete construction changed the original selected object action"
    unless ← Decide.kernelAccepts (← mkEq image value) (← mkEqRefl image) do
      throwError "the complete construction failed its original object identification"
    candidates := candidates.push action
  match candidates with
  | #[] => return none
  | #[action] => return some action
  | _ =>
      throwStratum .ambiguousRealization
        "the complete literal action has several accepted construction presentations"

def recordCompleteConstruction (trace : Trace) (value : Expr) : TermElabM Bool := do
  let some action ← completeLiteralConstruction? value | return false
  let some (_, receiver) := FunctorActionData.objectAction? value | unreachable!
  recordConstructionCoreSource trace action receiver
  Trace.record (some trace) value (.construction action.entry.id action.parameters receiver)
  return true

/-- A missing original object may have a complete public universal construction.
Only a closed application of the whole accepted declaration can provide it. The
full apex, selected diagram category and all parameters must be fixed; a carrier
or an equal cached result supplies nothing. All complete alternatives survive. -/
def recordCompleteUniversalObject (trace : Trace) (value : Expr) : TermElabM Bool := do
  let value ← instantiateMVars value
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return false
  let state ← registryState
  let mut candidates : Array (LimitEntry × Expr) := #[]
  for row in state.limits do
    let diagram? ← withoutModifyingState do
      let application ← instantiateFresh row.declaration
      -- Keep the declaration's actual diagram and category parameters while
      -- matching its apex. Fresh instance synthesis cannot select an open shape.
      let cone ← withTransparency .all <|
        mkProjection application (if row.colimit then `cocone else `cone)
      let apex ← withTransparency .all <| mkProjection cone `pt
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType apex) (← inferType value) <&&> isDefEq apex value) do
        CategoryContext.exposeStructureParameters application
      unless ← withTransparency .all <|
          isDefEq (← inferType apex) (← inferType value) <&&> isDefEq apex value do
        return none
      let application ← instantiateMVars application
      let apex ← instantiateMVars apex
      unless FunctorActionData.closedParameter application &&
          FunctorActionData.closedParameter apex && (← isTypeCorrect application) do return none
      let applicationType ← withTransparency .all <| whnf (← inferType application)
      let expectedHead := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
        else ``CategoryTheory.Limits.LimitCone
      unless applicationType.getAppFn.constName? == some expectedHead do
        throwError "the accepted universal object has a different full declaration type"
      let diagram := applicationType.appArg!
      unless FunctorActionData.closedParameter diagram && (← isTypeCorrect diagram) do return none
      let some category := state.categories.find? (·.id == row.category)
        | throwError "the accepted universal object lost its declared category"
      let (_, bundle) ← functorCategoryBundles diagram
      let context ← CategoryContext.presented { expression := category.expression, bundle }
      CategoryContext.checkObject context value
      let accepted ← Semantic.limitPresentation row diagram
      unless ← withTransparency .all <|
          isDefEq (← inferType accepted) (← inferType application) <&&>
            isDefEq accepted application do
        throwError "the universal object changed its complete accepted diagram presentation"
      unless ← Decide.kernelAccepts (← mkEq apex value) (← mkEqRefl apex) do
        throwError "the complete universal object failed its original kernel check"
      return some diagram
    if let some diagram := diagram? then
      let resolution ← match state.resolveLimitDetailed row.category row.shape row.colimit with
        | .ok resolution => pure resolution
        | .error error => Semantic.limitResolutionFailure error
      unless resolution.limit == row.id && resolution.lift.isNone do continue
      unless candidates.any (fun (previous, original) => previous.id == row.id && original == diagram) do
        candidates := candidates.push (row, diagram)
  match candidates with
  | #[] => return false
  | #[(row, diagram)] =>
      Trace.record (some trace) value (.limit row.id diagram none)
      return true
  | _ =>
      throwStratum .ambiguousRealization
        "the complete selected object has several accepted universal presentations"

/-- Recover a recorded construction only from the same literal receiver and the
same complete functor. The original occurrence remains the data source, including
any returned packet and owner; equality of results at one object is insufficient. -/
def retainedConstructionResult? (trace : Trace) (value : Expr) :
    TermElabM (Option Expr) := do
  let value ← instantiateMVars value
  let some (action, receiver) := FunctorActionData.objectAction? value | return none
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return none
  let state ← registryState
  let mut candidates : Array Expr := #[]
  for (recorded, node) in (← trace.get).toArray do
    let .construction id parameters original := node | continue
    unless original == receiver && recorded != value do continue
    let same ← withoutModifyingState do
      unless FunctorActionData.closedParameter recorded && (← isTypeCorrect recorded) do
        return false
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the retained construction is no longer registered"
      let selected ← DirectConstruction.select entry (← parameters.mapM exprToSyntax) original
      unless ← withTransparency .all <|
          isDefEq (← inferType selected.functor) (← inferType action) <&&>
            isDefEq selected.functor action do return false
      let image ← DirectConstruction.obj selected original
      unless ← withTransparency .all <|
          isDefEq (← inferType image) (← inferType recorded) <&&> isDefEq image recorded do
        throwError "the retained construction changed its complete original result"
      unless ← withTransparency .all <|
          isDefEq (← inferType image) (← inferType value) <&&> isDefEq image value do
        throwError "the selected construction changed its complete object action"
      unless ← Decide.kernelAccepts (← mkEq image value) (← mkEqRefl image) do
        throwError "the selected construction failed its original object identification"
      return true
    if same && !candidates.contains recorded then candidates := candidates.push recorded
  match candidates with
  | #[] => return none
  | #[original] => return some original
  | _ =>
      throwStratum .ambiguousRealization
        "the complete construction retains several distinct original data occurrences"

mutual

/-- Closed parameter data retaining accepted named-object provenance when present. -/
partial def parameterData (trace : Trace) (value : Expr) (recovering : Array Expr := #[]) : TermElabM Json := do
  let state ← registryState
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
    throwStratum .noImplementation m!"the exact functor parameter is not closed"
  if let some (.operationEquivalence representative chosen candidates comparisons) ←
      trace.node? value then
    checkOperationEquivalence value representative chosen candidates comparisons
    return ← parameterData trace representative recovering
  let selected := value.consumeMData
  if let some category := state.categories.find?
      (fun row => selected.getAppFn.constName? == some row.declaration) then
    let data : Backend.CategoryParameter := {
      category := category.id.raw
      parameters := (← declarationData trace category.declaration selected recovering) }
    return data.encode
  if let some constructor := state.constructors.find?
      (fun row => selected.getAppFn.constName? == some row.semantics) then
    let parameters ← declarationData trace constructor.semantics selected recovering
    unless parameters.size == constructor.signature.size do
      throwError "the constructed category lost its complete ordered declared arguments"
    return Json.mkObj [("ctor", "constructedCategory"),
      ("args", Json.arr #[toJson constructor.id.raw, Json.arr parameters])]
  let selectedFunctor := if selected.isAppOf ``CategoryTheory.Cat.Hom.toFunctor then
    selected.appArg! else selected
  if let some functor := state.functors.find?
      (fun row => selectedFunctor.getAppFn.constName? == some row.declaration) then
    let data : Backend.FunctorParameter := {
      functor := functor.id.raw
      parameters := (← declarationData trace functor.declaration selectedFunctor recovering) }
    return data.encode
  if let some (.object id params) ← (trace.node? value : IO _) then
    return Json.mkObj [("ctor", id.raw), ("args", Json.arr (← params.mapM (fun parameter => parameterData trace parameter recovering)))]
  -- A numeral point of a selected structure: its element descriptor.
  if let some (.elementNumeral n _ selected) ← (trace.node? value : IO _) then
    return Json.mkObj [("ctor", "element"), ("args", Json.arr #[← parameterData trace selected recovering,
      Json.mkObj [("ctor", "numeral"), ("args", Json.arr #[toJson n])]])]
  if let some (.functor id params receiver) ← (trace.node? value : IO _) then
    if receiver == value then
      throwStratum .noImplementation "the accepted parameter action has cyclic source provenance"
    let some entry := state.functor? id
      | throwError "the retained parameter action is not registered"
    let (image, _) ← Semantic.applyRegisteredFunctor entry receiver
      (← params.mapM exprToSyntax) none
    unless ← withTransparency .all <| isDefEq image value do
      throwError "the retained parameter action changes the complete selected value"
    let condition ← mkEq image value
    unless ← Decide.kernelAccepts condition (← mkEqRefl image) do
      throwError "the complete parameter action identification failed its original kernel check"
    return Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
      Json.mkObj [("ctor", id.raw), ("args", Json.arr (← params.mapM (fun parameter => parameterData trace parameter recovering)))],
      ← parameterData trace receiver recovering])]
  if let some (.retainedRoute _ _ route applications receiver) ← (trace.node? value : IO _) then
    unless route.size == applications.size do
      throwError "the parameter route lost its exact ordered edge applications"
    let mut image := receiver
    let mut json ← parameterData trace receiver recovering
    for (step, application) in route.zip applications do
      if application.hasMVar || application.hasLevelMVar || application.hasFVar ||
          application.hasLooseBVars then
        throwError "the parameter route has an unresolved selected edge application"
      image ← Semantic.objOf application image
      json := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
        ← edgeDescriptor trace step application recovering, json])]
    let condition ← mkEq image value
    unless ← withTransparency .all <| isDefEq image value do
      throwError "the retained parameter route changed its complete selected image"
    unless ← Decide.kernelAccepts condition (← mkEqRefl image) do
      throwError "the retained parameter route failed its original image identification"
    return json
  if let some (.parameterEquivalence expectedType representative sources) ←
      (trace.node? value : IO _) then
    unless ← isDefEq representative value do
      throwError "the parameter identity class has a different requested representative"
    let some chosen := sources[0]?
      | throwError "the parameter identity class has no accepted source"
    for source in sources do
      let some entry := state.objects.find? (·.id == source.source)
        | throwError "the parameter identity class has an unregistered source"
      unless entry.category == source.sourceCategory do
        throwError "the parameter identity class has a different declared source category"
      let object ← objectAt trace entry source.params
      unless ← isDefEq object source.object do
        throwError "the parameter identity class lost its exact declared source arguments"
      unless source.route.size == source.applications.size do
        throwError "the parameter identity class lost its complete ordered edge applications"
      let mut image := object
      for (step, application) in source.route.zip source.applications do
        if application.hasMVar || application.hasLevelMVar || application.hasFVar ||
            application.hasLooseBVars then
          throwError "the parameter identity class has an unresolved selected edge application"
        discard <| edgeDescriptor trace step application recovering
        image ← Semantic.objOf application image
      unless (← isDefEq image source.image) && (← isDefEq (← inferType image) expectedType) do
        throwError "the parameter identity class has an incompatible full structured image"
      unless ← Decide.kernelAccepts (← mkEq source.image representative) source.identity do
        throwError "the parameter identity class has no checked full-object identification"
    -- A distinct retained child has its own construction and must keep it. Older
    -- identity-class records can be keyed by their representative itself; only
    -- those self-records require direct encoding of the checked named source.
    if representative != value then return ← parameterData trace representative recovering
    -- The chosen source is already a checked registered application. Encoding it directly
    -- avoids following the representative back into its own identity-class trace node.
    let mut json := Json.mkObj [("ctor", chosen.source.raw),
      ("args", Json.arr (← chosen.params.mapM (fun parameter => parameterData trace parameter recovering)))]
    for (step, application) in chosen.route.zip chosen.applications do
      json := Json.mkObj [("ctor", "functorAction"),
        ("args", Json.arr #[← edgeDescriptor trace step application recovering, json])]
    return json
  if let .ok json ← Codec.encode value then return json
  -- Preserve the complete literal action in either public projection form.
  -- A composite is encoded in its declared order, never by an inner declaration.
  if let some (action, source) := FunctorActionData.objectAction? value then
    if action.isAppOf ``CategoryTheory.Functor.comp then
      let arguments := action.getAppArgs
      let intermediate ← Semantic.objOf arguments[arguments.size - 2]! source
      let nested ← Semantic.objOf arguments.back! intermediate
      unless ← withTransparency .all <| isDefEq nested value do
        throwError "the parameter composition changed its original complete object action"
      return ← parameterData trace nested recovering
    if let some selected ← FunctorActionData.registeredAction? state action then
      return Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
        ← edgeDescriptor trace selected.edge selected.declarationApplication recovering,
        ← parameterData trace source recovering])]
  if let some (data, _) ← FunctorActionData.encodeRetainedParameterAction? (Dependency := Unit)
      trace value
      (fun source => return (← parameterData trace source (recovering.push value), #[]))
      (fun edge action => return (← edgeDescriptor trace edge action (recovering.push value), #[]))
      recovering then
    return data
  let categories ← completeNamedCategoryPresentations value
  if let #[(entry, parameters)] := categories then
    let data : Backend.CategoryParameter := {
      category := entry.id.raw
      parameters := (← parameters.mapM (fun parameter => parameterData trace parameter recovering)) }
    return data.encode
  unless categories.isEmpty do
    throwStratum .ambiguousRealization "the complete parameter category has several accepted presentations"
  let candidates ← completeNamedObjectPresentations value
  let #[(entry, params)] := candidates
    | throwStratum .noImplementation m!"the exact functor parameter has no unique accepted data \
        presentation: {candidates.size} registered objects ({candidates.map (·.1.id.raw)}) \
        present {value}"
  return Json.mkObj [("ctor", entry.id.raw), ("args", Json.arr (← params.mapM (fun parameter => parameterData trace parameter recovering)))]

/-- The exact explicitly applied arguments of an accepted declaration inside its actual term. -/
partial def declarationData (trace : Trace) (declaration : Name) (actual : Expr)
    (recovering : Array Expr := #[]) : TermElabM (Array Json) := do
  let actual ← instantiateMVars actual
  let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let some application := actual.find? fun term =>
      term.getAppFn.constName? == some declaration && term.getAppNumArgs == infos.size
    | throwError "the exact registered functor declaration application was lost"
  let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  (← DirectConstruction.dataArguments params).mapM (fun parameter => parameterData trace parameter recovering)

/-- Public edge data from the actual instantiated functor, preserving declaration arguments. -/
partial def edgeDescriptor (trace : Trace) (edge : EdgeRef) (actual : Expr)
    (recovering : Array Expr := #[]) : TermElabM Json := do
  let state ← registryState
  match edge with
  | .functor id =>
      let some entry := state.functor? id | unreachable!
      return Json.mkObj [("ctor", id.raw), ("args", Json.arr (← declarationData trace entry.declaration actual recovering))]
  | .classifierForget id =>
      let some entry := state.classifiers.find? (·.id == id) | unreachable!
      return Json.mkObj [("ctor", "classifierForget"), ("args", Json.arr #[toJson id.raw,
        Json.arr (← declarationData trace entry.declaration actual recovering)])]
  | .constructMap constructor inner =>
      return Json.mkObj [("ctor", "constructorMap"),
        ("args", Json.arr #[toJson constructor.raw, ← edgeDescriptor trace inner actual recovering])]

end

/-- Complete object action data at the actual typed source, retaining every edge parameter. -/
def actionObjectFragment (trace : Trace) (input : Wire) (route : Array EdgeRef) :
    TermElabM DataOwnership.Data := do
  let state ← registryState
  let mut object := input.value
  let mut data := input.fragment
  for edge in route do
    let U ← Semantic.edgeFunctor state edge
    object ← Semantic.objOf U object
    let descriptor ← edgeDescriptor trace edge U
    data ← scopedNode "functorAction" #[{ json := descriptor }, data]
  return data

/-- Send the value `w`, the receiver of an operation, along the structural route `route` the
semantic reading resolved (CC-TRANSPORT): the value of `M(U(x))` is computed on `U(x)`, and
`U(x)` is what the catalogue's rows say it is. A named object refining another along a route that
begins `route` is that other object at the same parameters (`RegistryState.transport`); it is
elaborated and recorded like any named object. A value no row sends further is sent as it is.
Nothing but the catalogue's rows moves a value. -/
-- A target schema is selected only when its accepted metadata determines it uniquely.
def imageCategory? (state : RegistryState) (target : CategoryExpr) : Option NamedCategoryEntry := do
  let exact := state.categories.filter (·.expression.syntacticEq target)
  if let #[category] := exact then return category
  unless exact.isEmpty do none
  let .familyApp family _ := target | none
  let #[category] := state.categories.filter (fun category => match category.expression with
    | .familyApp other _ => family == other
    | _ => false) | none
  some category

def imageForm (state : RegistryState) (edge : EdgeRef) (category : NamedCategoryEntry) : Form :=
  match category.expression with
  | .construct constructor #[.category _] =>
      if (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.subobjects) then .subobject category
      else if (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) then .arrow category
      else .edgeImage edge category
  | _ => match edge with
      | .functor id => match state.functors.find? (·.id == id) with
          | some entry => .functorImage entry category.id
          | none => .edgeImage edge category
      | _ => .edgeImage edge category

/-- A local derived context reuses its original complete data address. It claims no
category identity when the catalogue has no separately named schema. -/
def contextualForm (state : RegistryState) (context : CategoryContext)
    (origin : Form) (morphism : Bool := false) : Form :=
  match CategoryContext.named? state context.expression with
  | some category => if morphism then .canonicalMorphism category else .diagrams category
  | none => .contextual context.expression origin

/-- Read complete returned fields of a fixed full subcategory of arrows, including the
final output of a prescribed reverse lift route. Both public arrow data and its legacy
subobject spelling retain the source, target, and map; no field supplies a property proof. -/
def fragmentAt? (data : DataOwnership.Data) (path : DataOwnership.Path) :
    Option DataOwnership.Data := do
  let json ← DataOwnership.get? data.json path
  return {
    json
    ownership := DataOwnership.project path data.ownership }

def fragmentArguments? (data : DataOwnership.Data) : Option (Array DataOwnership.Data) := do
  let args ← ((data.json.getObjVal? "args").bind (·.getArr?)).toOption
  return args.mapIdx fun index json => {
    json, ownership := DataOwnership.project #[.field "args", .index index] data.ownership }

partial def subobjectFragments? (data : DataOwnership.Data) : Option (Array DataOwnership.Data) := do
  let tag ← (data.json.getObjValAs? String "ctor").toOption
  let args ← fragmentArguments? data
  if tag == "arrow" || tag == "subobject" then
    unless args.size == 3 do none
    return args
  if tag == "objectPresentation" then
    let #[_, answer] := args | none
    return ← subobjectFragments? answer
  if tag == "liftedSubobject" then
    let #[_, _, _, steps] := args | none
    let first ← fragmentAt? steps #[.index 0]
    let fields ← (LiftedSubobjectData.fields "liftStep" 5 first.json).toOption
    let outputs ← fields[4]!.getArr?.toOption
    discard <| (LiftedSubobjectData.nextBase fields[2]! outputs).toOption
    let inclusion ← fragmentAt? first #[.field "args", .index 4, .index 1]
    return ← fragmentArguments? inclusion
  none

/-- Exposed record data must satisfy the record codec at the independently
fixed original fields. A complete public object descriptor is not implicitly
its single stored field merely because the formal structure has one data slot. -/
def exposedRecordData? (receiver : Expr) (data : DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Option DataOwnership.Data) := do
  let some payload := ComputationalData.recordPayload? data | return none
  let checked ← withoutModifyingState <|
    ComputationalData.validateRecordPortWith receiver (← inferType receiver) payload.json objects
      (fun formal type json objects => ComputationalData.validatePort formal type json objects)
  let some (.ok ()) := checked | return none
  return some payload

/-- A projection producer records whether it selected existing fields or
constructed a pending action. An actual field can have any valid public shape. -/
inductive ProjectedObjectFragment where
  | structural (data : DataOwnership.Data)
  | deferredAction (data : DataOwnership.Data)

def ProjectedObjectFragment.data : ProjectedObjectFragment → DataOwnership.Data
  | .structural data | .deferredAction data => data

def ProjectedObjectFragment.isStructural : ProjectedObjectFragment → Bool
  | .structural _ => true
  | .deferredAction _ => false

/-- Compute a structural projection from the complete returned fields. The role of the
registered action is determined on a fresh symbolic receiver, so equal actual objects
cannot make unrelated functors look like projections. Opaque fields and their ownership
remain data. Other accepted actions retain their full functor descriptor. -/
def projectObjectFragmentWithOrigin (trace : Trace) (_source : CategoryExpr) (edge : EdgeRef)
    (action receiver : Expr) (data : DataOwnership.Data)
    (descriptor? : Option DataOwnership.Data := none) (checkOwnership : Bool := true)
    (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Option ProjectedObjectFragment) := do
  if checkOwnership then discard <| checkedFragment data.validate
  let payload := (ComputationalData.recordPayload? data).getD data
  -- Existing explicit codecs own their envelopes before structural single-field
  -- elision. The exact fresh receiver still determines every projected role.
  let role ← withLocalDeclD `receiver (← inferType receiver) fun symbolic => do
    let image ← Semantic.objOf action symbolic
    let selected ← ComputationalData.recordProjection
      ``CategoryTheory.ObjectProperty.FullSubcategory.obj symbolic
    let arrow := selected.getD symbolic
    let some left ← ComputationalData.recordProjection ``CategoryTheory.Arrow.left arrow
      | return none
    let some right ← ComputationalData.recordProjection ``CategoryTheory.Arrow.right arrow
      | return none
    let candidates := #[arrow, left, right]
    for index in [:candidates.size] do
      if ← withoutModifyingState (withTransparency .all <| isDefEq image candidates[index]!) then
        return some (index, selected.isSome)
    return none
  if let some (role, subobjects) := role then
    let fields := if subobjects then subobjectFragments? payload else do
      let tag ← (payload.json.getObjValAs? String "ctor").toOption
      unless tag == "arrow" do none
      let args ← fragmentArguments? payload
      unless args.size == 3 do none
      pure args
    if let some fields := fields then
      if role == 0 then
        let fields := DataOwnership.Data.array fields
        return some (.structural {
          json := Json.mkObj [("ctor", "arrow"), ("args", fields.json)]
          ownership := DataOwnership.prefix #[.field "args"] fields.ownership })
      return fields[role - 1]?.map .structural
  if (payload.json.getObjValAs? String "ctor").toOption == some "coreObject" then
    let core ← withLocalDeclD `receiver (← inferType receiver) fun symbolic => do
      let some original ← ComputationalData.recordProjection ``CategoryTheory.Core.of symbolic
        | return false
      withoutModifyingState <| withTransparency .all <|
        isDefEq (← Semantic.objOf action symbolic) original
    if core then
      if let some #[original] := fragmentArguments? payload then return some (.structural original)
  if let some exposed ← exposedRecordData? receiver data objects then
    let structural ← withLocalDeclD `receiver (← inferType receiver) fun symbolic => do
      let image ← Semantic.objOf action symbolic
      let some plan ← ComputationalData.recordProjectionPlan? symbolic image | return none
      let some projected ← plan.apply? receiver exposed objects | return none
      let fixed ← Semantic.objOf action receiver
      if (← ComputationalData.validatePort fixed (← inferType fixed) projected.json objects).isOk then
        return some projected
      return none
    if let some projected := structural then return some (.structural projected)
  if role.isNone then return none
  let descriptor ← match descriptor? with
    | some descriptor => pure descriptor
    | none => pure { json := ← edgeDescriptor trace edge action }
  let fields := DataOwnership.Data.array #[descriptor, data]
  return some (.deferredAction {
    json := Json.mkObj [("ctor", "functorAction"), ("args", fields.json)]
    ownership := DataOwnership.prefix #[.field "args"] fields.ownership })

/-- The original data-only projection interface delegates to the same checked
producer. Runtime assemblers also retain its explicit origin. -/
def projectObjectFragment (trace : Trace) (source : CategoryExpr) (edge : EdgeRef)
    (action receiver : Expr) (data : DataOwnership.Data)
    (descriptor? : Option DataOwnership.Data := none) (checkOwnership : Bool := true) :
    TermElabM (Option DataOwnership.Data) := do
  return (← projectObjectFragmentWithOrigin trace source edge action receiver data
    descriptor? checkOwnership).map (·.data)

/-- Raw descriptor observations retain the existing metadata interface. Actual
runtime data use `projectObjectFragment` with their complete supplier table. -/
def projectObjectAction (trace : Trace) (source : CategoryExpr) (edge : EdgeRef)
    (action receiver : Expr) (data : Json) (descriptor? : Option Json := none) :
    TermElabM (Option Json) := do
  return (← projectObjectFragmentWithOrigin trace source edge action receiver { json := data }
    (descriptor?.map fun json => { json }) false).map (·.data.json)

/-- Check the complete fixed object context, allowing only a retained full object isomorphism. -/
def checkProofRefinementSource (wire : Wire) (source : Expr) : TermElabM Unit := do
  unless ← withTransparency .all <| isDefEq (← inferType wire.value) (← inferType source) do
    throwError "the proof refinement source changed its complete object type"
  if ← withTransparency .all <| isDefEq wire.value source then return
  let some comparison := wire.objectIso
    | throwStratum .noImplementation "the proof refinement source requires its full object comparison"
  let expected ← withTransparency .all <| mkAppHere ``CategoryTheory.Iso #[source, wire.value]
  unless ← withTransparency .all <| isDefEq (← inferType comparison) expected do
    throwError "the proof refinement source comparison has different complete endpoints"
  discard <| StructuredResult.checkReconstruction comparison

/-- Restore exactly the original computational source after the witnessed forgetful action.
No registration lookup or computational answer participates in this normalization. -/
def proofRefinementBase (trace : Trace) (wire : Wire) (action : Expr) : TermElabM Wire := do
  let .proofRefinement target classifier baseForm := wire.form
    | throwError "the requested wire is not a proof-only refinement"
  let some (.proofRefinement recorded sourceCategory targetCategory source retained identity) ←
      trace.node? wire.value
    | throwError "the proof refinement lost its complete formal provenance"
  unless recorded == classifier && targetCategory == target.id do
    throwError "the proof refinement changed its registered classifier context"
  let state ← registryState
  let some owner := state.classifier? classifier
    | throwError "the proof refinement classifier is no longer registered"
  let some host := state.category? owner.host
    | throwError "the proof refinement host schema is no longer registered"
  unless sourceCategory == host.id do
    throwError "the proof refinement has a different complete host context"
  let complete ← ProofRefinement.construct state classifier target source
  let action ← Semantic.asFunctor action
  unless (← withTransparency .all <| isDefEq complete.value wire.value) &&
      (← withTransparency .all <| isDefEq complete.action retained) &&
      (← withTransparency .all <| isDefEq action retained) do
    throwError "the proof refinement changed its complete total object or forgetful action"
  let image ← Semantic.objOf retained wire.value
  unless !identity.hasMVar && !identity.hasLevelMVar && !identity.hasSorry &&
      (← Decide.kernelAccepts (← mkEq image source) identity) do
    throwError "the proof refinement lost its full forgetful-image identification"
  let snapshot :: remaining := wire.proofSources
    | throwError "the proof refinement lost its complete computational source snapshot"
  unless snapshot.form.id == baseForm.id && snapshot.form.category == sourceCategory do
    throwError "the proof refinement snapshot has a different registered input form"
  let original : Wire := {
    form := snapshot.form, payload := snapshot.payload,
    presentationIsos := snapshot.presentationIsos, objectIso := snapshot.objectIso,
    callableObserved := snapshot.callableObserved,
    objectObserved := snapshot.objectObserved,
    liftExecution := snapshot.liftExecution,
    categoryContext := snapshot.categoryContext,
    endpointPresentation := snapshot.endpointPresentation,
    constructionInputs := snapshot.constructionInputs,
    constructionInputOwnership := snapshot.constructionInputOwnership,
    serviceHandles := snapshot.serviceHandles,
    serviceInputPaths := snapshot.serviceInputPaths,
    pointDataInterface := snapshot.pointDataInterface,
    productComponents := snapshot.productComponents, actionRecipe := snapshot.actionRecipe,
    intrinsicAssembly := snapshot.intrinsicAssembly, capturedInvocation := snapshot.capturedInvocation,
    callableEndpoints := snapshot.callableEndpoints,
    pointOrigin := snapshot.pointOrigin,
    morphismFramed := snapshot.morphismFramed,
    morphismFraming := snapshot.morphismFraming,
    proofSources := remaining }
  checkProofRefinementSource original source
  return original

/-- Both projections use the same whole registered action check. -/
def checkExecutableEdgeAction (state : RegistryState) (edge : EdgeRef) (action : Expr) :
    TermElabM Unit := do
  unless FunctorActionData.closedParameter action do
    throwError "the executable edge requires its complete selected action: {reprStr edge}; \
      expression metavariables: {action.hasMVar}; universe metavariables: {action.hasLevelMVar}; \
      free variables: {action.hasFVar}; loose bound variables: {action.hasLooseBVars}"
  unless ← isTypeCorrect action do
    throwError "the executable edge requires its type-correct complete selected action: {reprStr edge}"
  match edge with
  | .functor _ | .classifierForget _ =>
    let some selected ← FunctorActionData.registeredAction? state action
      | throwError "the executable action lost its complete registered declaration"
    unless selected.edge == edge do
      throwError "the executable action differs from its complete selected declaration"
  | .constructMap .. =>
    let expected ← Semantic.asFunctor (← Semantic.edgeFunctor state edge)
    unless ← withTransparency .all <|
        isDefEq (← inferType expected) (← inferType action) <&&> isDefEq expected action do
      throwError "the executable constructor action changed its full accepted declaration"


/-- Runtime action encoders retain actual parameter data and its computational dependencies.
Metadata-only callers use the declaration encoder without inventing runtime ownership. -/
abbrev ActionEncoder := EdgeRef → Expr → TermElabM (Json × Array Wire)

abbrev ScopedActionEncoder := EdgeRef → Expr → TermElabM (DataOwnership.Data × Array Wire)

abbrev CapturedActionEncoder := EdgeRef → Expr → TermElabM ActionDataTemplate

abbrev ActionEndpointReader :=
  Wire → Option CategoryContext → Expr → Bool → TermElabM Wire

/-- Recheck an owner's whole declaration without recovering any runtime data.
The complete source dictionary comes from the original selected occurrence. -/
def actionOwnerContexts (owner : ActionOwner) (application : Expr) (original : Wire)
    (morphism : Bool) : TermElabM (CategoryContext × CategoryContext) := do
  let state ← registryState
  let application ← instantiateMVars (← Semantic.asFunctor application)
  let (sourceBundle, targetBundle) ← functorCategoryBundles application
  let (sourceExpression, targetExpression) ← match owner with
    | .edge edge => do
        checkExecutableEdgeAction state edge application
        let some source := state.selectedEdgeSource? edge
          | throwError "the captured action lost its complete source category"
        let some target := state.selectedEdgeTarget? edge
          | throwError "the captured action lost its complete target category"
        pure (source, target)
    | .construction id parameters => do
        let some entry := state.constructions.find? (·.id == id)
          | throwError "the captured construction is no longer registered"
        let expression ← match original.categoryContext with
          | some context => pure context.expression
          | none =>
              let some expression := state.formExpression? original.form
                | throwError "the captured construction lost its complete source category"
              pure expression
        let source : CategoryContext := { expression, bundle := sourceBundle }
        discard <| framingContext (some source) original.categoryContext
        let receiver ← if morphism then
          pure (← contextualMorphismEndpoints source original.value).1
        else pure original.value
        let selected ← DirectConstruction.select entry (← parameters.mapM exprToSyntax) receiver
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType selected.functor) (← inferType application) <&&>
              isDefEq selected.functor application) do
          throwError "the captured construction changed its complete declared application"
        discard <| framingContext (some selected.target)
          (some { expression := entry.target, bundle := targetBundle })
        pure (expression, entry.target)
  let source : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
  let target : CategoryContext := { expression := targetExpression, bundle := targetBundle }
  discard <| framingContext (some source) original.categoryContext
  if morphism then discard <| contextualMorphismEndpoints source original.value
  else CategoryContext.checkObject source original.value
  return (source, target)

/-- Attach an exact current producer plan. This formal check selects no port and
performs no computational action; metadata preparation remains inert. -/
def retainRegisteredActionInput (owner : ActionOwner) (morphism : Bool) (application : Expr)
    (original output : Wire) (descriptor : ActionDataTemplate)
    (endpoints : Option (Wire × Wire) := none)
    (imageEndpoints : Option (Wire × Wire) := none) : TermElabM Wire := do
  let application ← instantiateMVars (← Semantic.asFunctor application)
  let (source, target) ← actionOwnerContexts owner application original morphism
  discard <| framingContext (some target) output.categoryContext
  let expected ← if morphism then Semantic.mapOf application original.value
    else Semantic.objOf application original.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType expected) (← inferType output.value) <&&>
        isDefEq expected output.value) do
    throwError "the captured action changed its independently selected complete result"
  let (data, _) ← renderCapturedActionData descriptor
  if let .error message ← ComputationalData.validateAction application data.json then
    throwError "the captured action has an incompatible complete descriptor: {message}"
  discard <| checkedFragment output.fragment.validate
  if let some (left, right) := imageEndpoints then
    unless morphism do throwError "an object action cannot retain whole-map image endpoints"
    let (sourceValue, targetValue) ← contextualMorphismEndpoints source original.value
    for (endpoint, value) in #[(left, sourceValue), (right, targetValue)] do
      discard <| framingContext (some target) endpoint.categoryContext
      let expected ← Semantic.objOf application value
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType endpoint.value) (← inferType expected) <&&>
            isDefEq endpoint.value expected) do
        throwError "a retained action image changed its independently fixed complete object"
  let output := { output with capturedInvocation := none, actionRecipe := some {
    morphism, owner, application, original, descriptor, source, target,
    formal := output.value, fragment := output.fragment, endpoints, imageEndpoints } }
  match imageEndpoints with
  | some (source, image) => retainCallableEndpoints output source image target
  | none => pure output

def retainActionInput (morphism : Bool) (edge : EdgeRef) (application : Expr)
    (original output : Wire) (descriptor : ActionDataTemplate)
    (endpoints : Option (Wire × Wire) := none) : TermElabM Wire :=
  retainRegisteredActionInput (.edge edge) morphism application original output descriptor endpoints

/-- Read an already selected complete comparison in the fixed category. This
checks both directions and their dictionaries before any product construction. -/
def operationComparisonEnds (context : CategoryContext) (comparison : Expr) :
    TermElabM (Expr × Expr) := do
  let comparison ← instantiateMVars comparison
  if comparison.hasMVar || comparison.hasLevelMVar then
    throwError "the operation comparison has unresolved complete parameters"
  discard <| StructuredResult.checkReconstruction comparison
  let type ← whnfR (← inferType comparison)
  unless type.isAppOf ``CategoryTheory.Iso && type.getAppArgs.size >= 2 do
    throwError "the operation endpoint comparison is not a complete isomorphism"
  let fields := type.getAppArgs
  let source := fields[fields.size - 2]!
  let target := fields.back!
  CategoryContext.checkObject context source
  CategoryContext.checkObject context target
  CategoryContext.checkMorphism context (← mkAppM ``CategoryTheory.Iso.hom #[comparison]) source target
  CategoryContext.checkMorphism context (← mkAppM ``CategoryTheory.Iso.inv #[comparison]) target source
  return (source, target)

/-- Retain the two complete comparison occurrences at their producer. The
accepted Iso fixes their directions; its proof does not mark either map actual. -/
def retainEndpointPresentationMaps (wire : Wire) (context : CategoryContext)
    (comparison : Expr) (forward backward : Wire) : TermElabM Wire := do
  let (semantic, actual) ← operationComparisonEnds context comparison
  discard <| framingContext (some context) wire.categoryContext
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType wire.value) (← inferType semantic) <&&>
        isDefEq wire.value semantic) do
    throwError "the endpoint presentation changed its complete semantic object"
  let forward ← forwardRetainedValue forward (← mkAppM ``CategoryTheory.Iso.hom #[comparison])
  let backward ← forwardRetainedValue backward (← mkAppM ``CategoryTheory.Iso.inv #[comparison])
  CategoryContext.checkMorphism context forward.value semantic actual
  CategoryContext.checkMorphism context backward.value actual semantic
  let some (source, target) ← retainedCallableEndpoints? forward context
    | throwError "the forward comparison lost its complete endpoint occurrences"
  let some (reverseSource, reverseTarget) ← retainedCallableEndpoints? backward context
    | throwError "the backward comparison lost its complete endpoint occurrences"
  unless sameCompleteWireContext source (← forwardRetainedValue reverseTarget source.value) &&
      sameCompleteWireContext target (← forwardRetainedValue reverseSource target.value) do
    throwError "the comparison directions have different complete endpoint occurrences"
  unless wire.fragment == target.fragment do
    throwStratum .unavailable "the endpoint presentation changed its original actual packet or supplier"
  return { wire with endpointPresentation := some {
    comparison, forward := forward.json, backward := backward.json,
    forwardOwnership := forward.ownership, backwardOwnership := backward.ownership,
    maps := some (forward, backward) } }

/-- Packet-only callers still supply a complete fixed comparison role. Recover
only its public endpoint fields, never an expression-keyed object or action.
The resulting literal descriptors remain pending and retain every supplier. -/
def endpointPresentationMaps (wire : Wire) (context : CategoryContext)
    (presentation : EndpointPresentation) : TermElabM (Wire × Wire) := do
  if let some (forward, backward) := presentation.maps then
    let (semantic, actual) ← operationComparisonEnds context presentation.comparison
    for (comparisonMap, source, target, selector) in #[
        (forward, semantic, actual, ``CategoryTheory.Iso.hom),
        (backward, actual, semantic, ``CategoryTheory.Iso.inv)] do
      discard <| framingContext (some context) comparisonMap.categoryContext
      CategoryContext.checkMorphism context comparisonMap.value source target
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq comparisonMap.value (← mkAppM selector #[presentation.comparison])) do
        throwError "the retained comparison changed its selected complete direction"
      unless (← retainedCallableEndpoints? comparisonMap context).isSome do
        throwError "the retained comparison lost its original full endpoint occurrences"
    unless forward.fragment == presentation.forwardFragment &&
        backward.fragment == presentation.backwardFragment do
      throwStratum .unavailable "the endpoint comparison changed its retained positioned map data"
    return (forward, backward)
  let (semantic, actual) ← operationComparisonEnds context presentation.comparison
  let forwardValue ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]
  let backwardValue ← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison]
  let readEndpoint := fun (formal : Expr) (data : DataOwnership.Data) (source : Bool) => do
    let selected ← checkedFragment (← ComputationalData.interfaceEndpointDataWithOrigin #[]
      formal data source false)
    if selected.origin == .action then
      throwStratum .noImplementation
        "the comparison action has no retained typed endpoint continuation"
    pure selected.data
  let sourceData ← readEndpoint forwardValue presentation.forwardFragment true
  let targetData ← readEndpoint forwardValue presentation.forwardFragment false
  let reverseSource ← readEndpoint backwardValue presentation.backwardFragment true
  let reverseTarget ← readEndpoint backwardValue presentation.backwardFragment false
  unless sourceData == reverseTarget && targetData == reverseSource && targetData == wire.fragment do
    throwStratum .noImplementation
      "the packet-only comparison lacks its complete original endpoint interface"
  let state ← registryState
  let source : Wire := {
    form := contextualForm state context wire.form
    payload := (← scopedPayload semantic sourceData false), categoryContext := some context }
  let target : Wire := {
    form := contextualForm state context wire.form
    payload := (← scopedPayload actual targetData false), categoryContext := some context }
  let prepare := fun (formal : Expr) (data : DataOwnership.Data) (source target : Wire) => do
    let comparisonMap : Wire := {
      form := contextualForm state context wire.form true
      payload := (← scopedPayload formal data false), categoryContext := some context,
      morphismFramed := true }
    let comparisonMap ← retainIntrinsicAssembly comparisonMap .map context (.literal data) #[] #[]
      (.retained, .retained)
    retainCallableEndpoints comparisonMap source target context
  let forward ← prepare forwardValue presentation.forwardFragment source target
  let backward ← prepare backwardValue presentation.backwardFragment target source
  discard <| retainEndpointPresentationMaps wire context presentation.comparison forward backward
  return (forward, backward)

/-- Ordinary categorical composition of two already selected comparison
occurrences. The middle endpoint is retained in both positions and checked;
neither a trace replay nor a packet search supplies a constituent. -/
def composeEndpointMaps (context : CategoryContext) (first second : Wire) : TermElabM Wire := do
  let some (source, middle) ← retainedCallableEndpoints? first context
    | throwError "the first comparison constituent lost its complete endpoints"
  let some (otherMiddle, target) ← retainedCallableEndpoints? second context
    | throwError "the second comparison constituent lost its complete endpoints"
  let otherMiddle ← forwardRetainedValue otherMiddle middle.value
  unless sameCompleteWireContext middle otherMiddle do
    throwStratum .noImplementation "comparison composition needs its exact shared endpoint occurrence"
  let formal ← StructuredResult.checkReconstruction
    (← ServiceRequest.compose context source.value middle.value target.value first.value second.value)
  let template : ActionDataTemplate := .ctor "compose" #[.wire .map first, .wire .map second]
  let (data, inputs) ← renderCapturedActionData template
  let wire : Wire := {
    form := contextualForm (← registryState) context first.form true
    payload := (← combinedRecipePayload formal data inputs)
    categoryContext := some context, morphismFramed := true }
  let wire ← retainIntrinsicAssembly wire .map context template
    #[{ context, source, target := middle, callable := first },
      { context, source := otherMiddle, target, callable := second }]
    #[(middle, otherMiddle)]
  retainCallableEndpoints wire source target context

/-- A mapped representation keeps its original image occurrence. In particular,
the actual-side endpoint is a continuation of this very object action, not a
second execution that happens to have an isomorphic formal result. -/
def retainMappedEndpointPresentation (owner : ActionOwner) (action : Expr)
    (original output : Wire) (descriptor : ActionDataTemplate)
    (actualImage? : Option Wire := none) : TermElabM Wire := do
  let some presentation := original.endpointPresentation | return output
  let (source, target) ← actionOwnerContexts owner action original false
  let (forward, backward) ← endpointPresentationMaps original source presentation
  let some (semanticEndpoint, actualEndpoint) ← retainedCallableEndpoints? forward source
    | throwError "the mapped comparison lost its original complete endpoints"
  let (data, dependencies) ← renderCapturedActionData descriptor
  let comparison ← mkAppM ``CategoryTheory.Functor.mapIso
    #[← Semantic.asFunctor action, presentation.comparison]
  let (semantic, actual) ← operationComparisonEnds target comparison
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType output.value) (← inferType semantic) <&&>
        isDefEq output.value semantic) do
    throwError "the mapped comparison changed its selected object action"
  let state ← registryState
  let semanticImage : Wire := {
    form := contextualForm state target semanticEndpoint.form
    payload := (← combinedRecipePayload semantic
      (← scopedNode "functorAction" #[data, semanticEndpoint.fragment])
      (#[semanticEndpoint] ++ dependencies))
    categoryContext := some target }
  let semanticImage ← retainRegisteredActionInput owner false action
    semanticEndpoint semanticImage descriptor
  -- The original producer chose this actual representation through the full
  -- accepted comparison. Keep its entire object computation as the typed child;
  -- this view neither computes a comparison nor claims the data are complete.
  let actualImage ← match actualImage? with
    | some originalImage => do
      discard <| framingContext (some target) originalImage.categoryContext
      CategoryContext.checkObject target originalImage.value
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType originalImage.value) (← inferType actual) <&&>
            isDefEq originalImage.value actual) do
        throwStratum .noImplementation
          "the retained field needs its independently selected comparison to the mapped actual image"
      unless originalImage.fragment == output.fragment do
        throwStratum .unavailable "the mapped comparison changed its selected actual field data or suppliers"
      pure originalImage
    | none => do
      let origin := { output with endpointPresentation := none }
      let actualImage : Wire := {
        form := contextualForm state target actualEndpoint.form
        payload := (← combinedRecipePayload actual output.fragment #[origin])
        categoryContext := some target }
      retainIntrinsicAssembly actualImage .object target (.wire .object origin)
  let capture := fun (comparisonMap left right : Wire) => do
    let formal ← Semantic.mapOf action comparisonMap.value
    let output : Wire := {
      form := contextualForm state target comparisonMap.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map" #[data, comparisonMap.fragment])
        (#[comparisonMap, left, right] ++ dependencies))
      categoryContext := some target, morphismFramed := true }
    let some endpoints ← retainedCallableEndpoints? comparisonMap source
      | throwError "the mapped comparison lost an original direction's full endpoints"
    retainRegisteredActionInput owner true action comparisonMap output descriptor (some endpoints)
      (some (left, right))
  let forward ← capture forward semanticImage actualImage
  let backward ← capture backward actualImage semanticImage
  retainEndpointPresentationMaps output target comparison forward backward

/-- Capture the common object projection of a complete registered action.
The producer fixes the exact source occurrence, parameter slots and full target
context. A checked structural projection may supply its existing public packet;
otherwise the usual functorAction envelope remains pending until observation.
This function neither selects a registration nor calls an executor. -/
def captureRegisteredObjectAction (owner : ActionOwner) (action : Expr)
    (original : Wire) (formal : Expr) (form : Form) (context : CategoryContext)
    (descriptor : ActionDataTemplate)
    (projection : Option DataOwnership.Data := none) : TermElabM Wire := do
  let (data, dependencies) ← renderCapturedActionData descriptor
  let fragment ← match projection with
    | some projection =>
      discard <| checkedFragment projection.validate
      pure projection
    | none => scopedNode "functorAction" #[data, original.fragment]
  let output : Wire := {
    form
    payload := (← combinedRecipePayload formal fragment (#[original] ++ dependencies))
    categoryContext := some context
    objectIso := (← mapObjectComparison action original.value original.objectIso)
    endpointPresentation := (← mapEndpointPresentation action data.json
      original.endpointPresentation data.ownership) }
  let output ← retainRegisteredActionInput owner false action original output descriptor
  retainMappedEndpointPresentation owner action original output descriptor

/-- Current-role checks precede observation or intrinsic endpoint projection.
Historical plans cannot select a different value, context or positioned packet. -/
def checkActionRecipe (wire : Wire) (recipe : ActionRecipe) : TermElabM Unit := do
  unless wire.fragment == recipe.fragment do
    throwStratum .unavailable "the pending action changed its positioned producer packet or suppliers"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType wire.value) (← inferType recipe.formal) <&&>
        isDefEq wire.value recipe.formal) do
    throwStratum .unavailable "historical action provenance cannot select a different current value"
  let (source, target) ← actionOwnerContexts recipe.owner recipe.application
    recipe.original recipe.morphism
  unless source.expression.syntacticEq recipe.source.expression &&
      target.expression.syntacticEq recipe.target.expression do
    throwError "the retained action changed its independently selected category expressions"
  discard <| framingContext (some source) (some recipe.source)
  discard <| framingContext (some target) (some recipe.target)
  discard <| framingContext (some recipe.target) wire.categoryContext
  let expected ← if recipe.morphism then Semantic.mapOf recipe.application recipe.original.value
    else Semantic.objOf recipe.application recipe.original.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType expected) (← inferType recipe.formal) <&&>
        isDefEq expected recipe.formal) do
    throwError "the retained action changed its complete original selection"
  if let some (left, right) := recipe.imageEndpoints then
    unless recipe.morphism do throwError "an object action retained an unrelated map image"
    let (sourceValue, targetValue) ← contextualMorphismEndpoints source recipe.original.value
    for (endpoint, value) in #[(left, sourceValue), (right, targetValue)] do
      discard <| framingContext (some target) endpoint.categoryContext
      let expected ← Semantic.objOf recipe.application value
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType endpoint.value) (← inferType expected) <&&>
            isDefEq endpoint.value expected) do
        throwError "the retained action image changed its complete selected object"

/-- A pending map already retains the exact endpoint occurrences and selected
action. Its endpoint is the corresponding object action, without executing the
map or reconstructing its source from a formal cache or equal packet bytes. -/
def retainedActionEndpoint? (original : Wire) (context : Option CategoryContext)
    (formal : Expr) (source : Bool) : TermElabM (Option Wire) := do
  if original.completedData then return none
  let some recipe := original.actionRecipe | return none
  unless recipe.morphism do return none
  checkActionRecipe original recipe
  discard <| framingContext context (some recipe.target)
  if let some images := recipe.imageEndpoints then
    return some (← forwardRetainedValue (if source then images.1 else images.2) formal)
  let some endpoints := recipe.endpoints
    | throwError "the pending map action lost its complete original endpoint occurrences"
  let endpoint := if source then endpoints.1 else endpoints.2
  let (left, right) ← contextualMorphismEndpoints recipe.source recipe.original.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType endpoint.value) (← inferType (if source then left else right)) <&&>
        isDefEq endpoint.value (if source then left else right)) do
    throwError "the retained map endpoint changed its original complete source"
  discard <| framingContext (some recipe.source) endpoint.categoryContext
  let value ← Semantic.objOf recipe.application endpoint.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType value) (← inferType formal) <&&> isDefEq value formal) do
    throwError "the pending map endpoint changed its complete selected image"
  let state ← registryState
  let form ← match recipe.owner with
    | .edge edge => pure <| match imageCategory? state recipe.target.expression with
        | some category => imageForm state edge category
        | none => contextualForm state recipe.target endpoint.form
    | .construction id _ =>
        let some form := state.constructionForm? id.raw
          | throwError "the pending construction endpoint lost its complete result form"
        pure form
  let (descriptor, dependencies) ← renderCapturedActionData recipe.descriptor
  let data ← scopedNode "functorAction" #[descriptor, endpoint.fragment]
  let output : Wire := {
    form, payload := (← combinedRecipePayload formal data (#[endpoint] ++ dependencies))
    categoryContext := some recipe.target
    objectIso := (← mapObjectComparison recipe.application endpoint.value endpoint.objectIso)
    endpointPresentation := (← mapEndpointPresentation recipe.application descriptor.json
      endpoint.endpointPresentation descriptor.ownership) }
  let output ← retainRegisteredActionInput recipe.owner false recipe.application
    endpoint output recipe.descriptor
  return some (← retainMappedEndpointPresentation recipe.owner recipe.application
    endpoint output recipe.descriptor)

/-- A mapped callable owns its two image occurrences from capture onward.
Endpoint views and the map executor read these same typed inputs, including
their original parameters and presentations; neither recreates an image from
an equal formal expression when another consumer asks for it. -/
def retainActionImageEndpoints (wire : Wire) : TermElabM Wire := do
  let some recipe := wire.actionRecipe
    | throwError "the mapped callable has no retained action producer"
  unless recipe.morphism do
    throwError "an object action cannot own mapped callable endpoints"
  checkActionRecipe wire recipe
  let (source, target) ← contextualMorphismEndpoints recipe.target wire.value
  let some source ← retainedActionEndpoint? wire (some recipe.target) source true
    | throwError "the mapped callable lost its selected source image"
  let some target ← retainedActionEndpoint? wire (some recipe.target) target false
    | throwError "the mapped callable lost its selected target image"
  let result := { wire with actionRecipe := some { recipe with imageEndpoints := some (source, target) } }
  retainCallableEndpoints result source target recipe.target

def encodeAction (trace : Trace) (encoder? : Option ScopedActionEncoder)
    (step : EdgeRef) (action : Expr) : TermElabM (DataOwnership.Data × Array Wire) := do
  match encoder? with
  | some encoder => encoder step action
  | none => return ({ json := ← edgeDescriptor trace step action }, #[])

/-- Retain every residual object action, including its complete instantiated edge data. -/
def transportImage (trace : Trace) (w : Wire) (route : Array EdgeRef)
    (applications : Option (Array Expr) := none)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none) : TermElabM Wire := do
  if let some retained := applications then
    unless retained.size == route.size do
      throwError "the retained route has incompatible ordered full applications"
  if route.isEmpty then return w
  let state ← registryState
  let some sourceExpression := state.formExpression? w.form
    | throwError "the reconstructed source image has no accepted category"
  let mut expression := sourceExpression
  let mut result := w
  for index in [:route.size] do
    let step := route[index]!
    let some edge := (state.edgesFrom expression).find? (·.ref == step)
      | throwError "the reconstructed image route disagrees with its retained category"
    let target := imageCategory? state edge.target
    let U ← match applications with
      | some retained => pure retained[index]!
      | none => Semantic.edgeFunctor state step
    if let .proofRefinement _ classifier _ := result.form then
      if step == .classifierForget classifier then
        result ← proofRefinementBase trace result U
        expression := edge.target
        continue
    let value ← Semantic.objOf U result.value
    let (sourceBundle, targetBundle) ← functorCategoryBundles (← Semantic.asFunctor U)
    if let some context := result.categoryContext then
      unless context.expression.syntacticEq expression &&
          (← withTransparency .all <| isDefEq sourceBundle context.bundle) do
        throwError "the route changed the retained complete source category"
    let U ← instantiateMVars U
    if U.hasMVar || U.hasLevelMVar || U.hasFVar || U.hasLooseBVars then
      throwError "the retained structural edge application is not closed"
    let captured ← capture?.mapM (fun capture => capture step U)
    let (descriptor, dependencies) ← match captured with
      | some template => renderCapturedActionData template
      | none => encodeAction trace encoder? step U
    let original := result
    let projection ← projectObjectFragmentWithOrigin trace expression step U result.value result.fragment
      (some descriptor)
    let json ← match projection with
      | some projected => pure projected.data
      | none => scopedNode "functorAction" #[descriptor, result.fragment]
    let completed := result.completedData && projection.any (·.isStructural)
    let objectIso ← mapObjectComparison U result.value result.objectIso
    let endpointPresentation ← mapEndpointPresentation U descriptor.json
      result.endpointPresentation descriptor.ownership
    result := { result with
      form := match target with
        | some target => imageForm state step target
        | none => .contextual edge.target result.form
      categoryContext := some {
        expression := edge.target, bundle := (← instantiateMVars targetBundle) }
      objectIso := objectIso
      endpointPresentation := endpointPresentation
      objectObserved := completed
      callableObserved := false
      actionRecipe := none
      proofSources := []
      payload := (← if completed then scopedPayload value json
        else combinedRecipePayload value json (#[result] ++ dependencies)) }
    if let some descriptor := captured then
      if !completed then
        result ← retainActionInput false step U original result descriptor
      result ← retainMappedEndpointPresentation (.edge step) U original result descriptor
    expression := edge.target
  return result

/-- A named constructor keeps the declaration's ordered parameter occurrences.
The fallback is only its exact public literal encoding; a different producer's
packet or an expression-equal parameter cannot supply a replacement occurrence. -/
def namedObjectParameterTemplates (wire : Wire) (entry : ObjectEntry)
    (parameters : Array Expr) : TermElabM (Array ActionDataTemplate) := do
  let fixed ← DirectConstruction.dataArguments parameters
  if let some assembly ← currentIntrinsicAssembly? wire then
    if let .ctor tag fields := actionTemplateExecution assembly.template then
      if tag == entry.id.raw then
        unless fields.size == fixed.size do
          throwError "the named constructor changed its ordered declaration parameter count"
        return fields
  let .ok (tag, fields) := ComputationalData.envelope wire.json
    | throwStratum .noImplementation "the named constructor has no retained public parameter interface"
  unless tag == entry.id.raw && fields.size == fixed.size do
    throwStratum .noImplementation "the named constructor has a different complete parameter interface"
  fixed.mapIdxM fun index _ => do
    return .literal (← checkedFragment (wire.fragment.project #[.field "args", .index index]))

/-- The accepted refinement supplies a representation of the interpreted image,
not a replacement mathematical object. Its two public callable directions keep
the exact image and named-base occurrences and remain pending until consumed. -/
def retainNamedRefinementPresentation (trace : Trace) (entry target : ObjectEntry)
    (parameters : Array Expr) (templates : Array ActionDataTemplate)
    (identification : Expr) (image : Wire) : TermElabM Wire := do
  let some refinement := entry.refines
    | throwError "the named representation has no accepted refinement declaration"
  unless refinement.base == target.id do
    throwError "the named representation changed its accepted base row"
  let accepted ← ObjectPresentation.applyParameters refinement.identification parameters
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType identification) (← inferType accepted) <&&>
        isDefEq identification accepted) do
    throwError "the named representation changed its accepted comparison application"
  let context ← match image.categoryContext with
    | some context => pure context
    | none =>
      let some category := (← registryState).categories.find? (·.id == target.category)
        | throwError "the named refinement lost its complete target category"
      CategoryContext.ofNamed category image.value
  let actualValue ← objectAt trace target parameters
  CategoryContext.checkObject context image.value
  CategoryContext.checkObject context actualValue
  let retained ← image.endpointPresentation.mapM (endpointPresentationMaps image context)
  let initial ← match retained with
    | none => pure image
    | some (forward, _) => do
      let some (_, actual) ← retainedCallableEndpoints? forward context
        | throwError "the named refinement lost its preceding actual image occurrence"
      pure actual
  let expected ← mkAppM ``CategoryTheory.Iso #[initial.value, actualValue]
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType identification) expected) do
    throwError "the accepted named refinement changed its complete image or base object"
  let identification ← instantiateMVars identification
  if identification.hasMVar || identification.hasLevelMVar || identification.hasFVar ||
      identification.hasLooseBVars then
    throwError "the accepted named refinement has unresolved complete parameters"
  let template := ActionDataTemplate.ctor target.id.raw templates
  let (data, parameterInputs) ← renderCapturedActionData template
  let actual : Wire := {
    form := .object target, payload := (← combinedRecipePayload actualValue data parameterInputs),
    categoryContext := some context, serviceHandles := image.serviceHandles }
  let actual ← retainIntrinsicAssembly actual .object context template
  let field := fun (selector : String) (formal : Expr) (source target : Wire) => do
    let template := ActionDataTemplate.ctor "objectField"
      #[.literal { json := toJson entry.id.raw }, .literal { json := toJson selector },
        .array templates]
    let (data, inputs) ← renderCapturedActionData template
    let wire : Wire := {
      form := contextualForm (← registryState) context source.form true,
      payload := (← combinedRecipePayload formal data inputs),
      categoryContext := some context, morphismFramed := true,
      serviceHandles := source.serviceHandles ++ target.serviceHandles }
    let wire ← retainIntrinsicAssembly wire .map context template #[] #[]
      (.retained, .retained)
    retainCallableEndpoints wire source target context
  let mut comparison := identification
  let mut forward ← field "refinement" (← mkAppM ``CategoryTheory.Iso.hom #[identification])
    initial actual
  let mut backward ← field "inverseRefinement" (← mkAppM ``CategoryTheory.Iso.inv #[identification])
    actual initial
  if let some (previousForward, previousBackward) := retained then
    let some previous := image.endpointPresentation | unreachable!
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[previous.comparison, identification]
    forward ← composeEndpointMaps context previousForward forward
    backward ← composeEndpointMaps context backward previousBackward
  let result : Wire := {
    form := .object target, payload := forwardPayload actual image.value actual.json,
    categoryContext := some context, serviceHandles := image.serviceHandles ++ actual.serviceHandles,
    presentationIsos := image.presentationIsos.push identification }
  let result ← retainIntrinsicAssembly result .object context (.wire .object actual)
  retainEndpointPresentationMaps result context comparison forward backward

def retainNamedRefinementOrigin (wire source : Wire) (entry target : ObjectEntry)
    (parameters : Array Expr) (templates : Array ActionDataTemplate)
    (route : Array EdgeRef) (applications : Array Expr)
    (descriptors : Array ActionDataTemplate) (identification : Expr) : TermElabM Wire := do
  let some presentation := wire.endpointPresentation
    | throwError "the named representation lost its complete comparison occurrences"
  unless !route.isEmpty && route.size == applications.size && route.size == descriptors.size do
    throwError "the named representation lost its original complete action positions"
  let origin : NamedRefinementOrigin := {
    formal := wire.value, fragment := wire.fragment, comparison := presentation.comparison,
    entry := entry.id, target := target.id, parameters, templates, source,
    route, applications, descriptors, identification }
  return { wire with endpointPresentation := some { presentation with namedRefinement := some origin } }

partial def transport (trace : Trace) (w : Wire) (route : Array EdgeRef)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none)
    (applications : Option (Array Expr) := none) : TermElabM Wire := do
  if let some retained := applications then
    unless retained.size == route.size do
      throwError "the retained presentation route lost its complete ordered applications"
  if route.isEmpty then return w
  if w.form.namedCategory?.isNone then return ← transportImage trace w route applications encoder? capture?
  if w.actualData || w.objectObserved || w.capturedInvocation.isSome || w.actionRecipe.isSome then
    return ← transportImage trace w route applications encoder? capture?
  if w.objectIso.isSome then return ← transportImage trace w route applications encoder? capture?
  let state ← registryState
  if let .arrow _ := w.form then
    return ← transportImage trace w route applications encoder? capture?
  let .object entry := w.form | transportImage trace w route applications encoder? capture?
  let represented ← match w.endpointPresentation with
    | none => pure w
    | some presentation => do
      let context ← match w.categoryContext with
        | some context => pure context
        | none =>
          let some category := state.categories.find? (·.id == entry.category)
            | throwError "the represented named source lost its complete category"
          CategoryContext.ofNamed category w.value
      let (forward, _) ← endpointPresentationMaps w context presentation
      let some (_, actual) ← retainedCallableEndpoints? forward context
        | throwError "the named source lost its selected actual endpoint"
      pure actual
  let some (.object id params) ← (trace.node? represented.value : IO _)
    | return ← transportImage trace w route applications encoder? capture?
  unless id == entry.id do
    return ← transportImage trace w route applications encoder? capture?
  let .ok (tag, _) := ComputationalData.envelope represented.json
    | return ← transportImage trace w route applications encoder? capture?
  unless tag == entry.id.raw do
    return ← transportImage trace w route applications encoder? capture?
  let templates ← namedObjectParameterTemplates represented entry params
  let selected ← match applications with
    | some selected => pure selected
    | none => route.mapM fun edge => do pure (← Semantic.edgeFunctor state edge)
  let mut current := entry
  let mut remaining := route
  let mut result := w
  for _ in [:state.objects.size + 1] do
    let some refinement := current.refines | break
    unless !refinement.route.isEmpty &&
        remaining.extract 0 refinement.route.size == refinement.route do break
    let some target := state.objects.find? (·.id == refinement.base)
      | throwError "the accepted refinement has no target object"
    let offset := route.size - remaining.size
    let applications := selected.extract offset (offset + refinement.route.size)
    let descriptors ← IO.mkRef (#[] : Array ActionDataTemplate)
    let capture : CapturedActionEncoder := fun edge application => do
      let descriptor ← match capture? with
        | some capture => capture edge application
        | none => pure (.literal (← encodeAction trace encoder? edge application).1)
      descriptors.modify (·.push descriptor)
      return descriptor
    let image ← transportImage trace result refinement.route
      (some applications) none (some capture)
    let identification ← ObjectPresentation.applyParameters refinement.identification params
    let presented ← retainNamedRefinementPresentation trace current target params templates identification image
    result ← retainNamedRefinementOrigin presented result current target params templates
      refinement.route applications (← descriptors.get) identification
    current := target
    remaining := remaining.extract refinement.route.size remaining.size
  transportImage trace result remaining
    (some (selected.extract (route.size - remaining.size) route.size))
    encoder? capture?

/-- Actual and private observation refresh the same retained named producer.
Only original constructor parameter occurrences are observed. The semantic
image and comparison maps are captured again at those exact inputs, not run. -/
def materializeNamedRefinementWith
    (observe : ActionDataRole → Wire → TermElabM Wire) (trace : Trace)
    (wire : Wire) (origin : NamedRefinementOrigin) : TermElabM Wire := do
  let some presentation := wire.endpointPresentation
    | throwStratum .unavailable "the named representation lost its anchored comparison"
  let current ← currentNamedRefinementOrigin? wire
  unless sameNamedRefinementOrigin current (some origin) do
    throwStratum .unavailable "historical named representation data cannot refresh another occurrence"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType origin.formal) (← inferType wire.value) <&&>
        isDefEq origin.formal wire.value) do
    throwStratum .unavailable "the named representation changed its complete semantic value"
  let state ← registryState
  let some entry := state.objects.find? (·.id == origin.entry)
    | throwError "the named representation lost its accepted source row"
  let some target := state.objects.find? (·.id == origin.target)
    | throwError "the named representation lost its accepted base row"
  let some refinement := entry.refines
    | throwError "the named representation lost its accepted refinement"
  unless refinement.base == target.id && refinement.route == origin.route &&
      origin.route.size == origin.applications.size && origin.route.size == origin.descriptors.size do
    throwError "the named representation changed its original complete route"
  let source ← observe .object origin.source
  let source ← forwardRetainedValue source origin.source.value
  let templates ← origin.templates.mapM (mapActionTemplateWires observe)
  if sameCompleteWireContext source origin.source &&
      templates.size == origin.templates.size &&
      (templates.zip origin.templates).all (fun (a, b) => sameActionTemplate a b) then
    return wire
  let (arguments, _) ← renderCapturedActionData (.array templates)
  let represented ← match source.endpointPresentation with
    | none => pure source
    | some selected => do
      let some context := source.categoryContext
        | throwError "the named representation source lost its complete category"
      let (forward, _) ← endpointPresentationMaps source context selected
      let some (_, target) ← retainedCallableEndpoints? forward context
        | throwError "the named representation source lost its selected actual endpoint"
      pure target
  let actualArguments ← checkedFragment (represented.fragment.project #[.field "args"])
  unless actualArguments == arguments do
    throwStratum .unavailable "the named representation changed an original positioned parameter supplier"
  let next ← IO.mkRef 0
  let capture : CapturedActionEncoder := fun edge application => do
    let index ← next.get
    let some expectedEdge := origin.route[index]?
      | throwError "the named representation added a route action"
    let some expected := origin.applications[index]?
      | throwError "the named representation omitted a complete action application"
    unless edge == expectedEdge && (← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType application) (← inferType expected) <&&>
          isDefEq application expected)) do
      throwError "the named representation changed an exact retained action position"
    let some descriptor := origin.descriptors[index]?
      | throwError "the named representation omitted a positioned action descriptor"
    next.set (index + 1)
    return descriptor
  let image ← transportImage trace source origin.route (some origin.applications) none (some capture)
  unless (← next.get) == origin.route.size do
    throwError "the named representation omitted a retained semantic image action"
  let result ← retainNamedRefinementPresentation trace entry target origin.parameters templates
    origin.identification image
  let result ← retainNamedRefinementOrigin result source entry target origin.parameters templates
    origin.route origin.applications origin.descriptors origin.identification
  forwardRetainedValue result wire.value

/-- Consume exact checked proof-refinement and named-presentation prefixes while
retaining the complete residual route. A later category-wide operation can then
apply every residual action without undoing the registered presentation. -/
partial def canonicalOperationInput (trace : Trace) (wire : Wire) (route : Array EdgeRef)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none)
    (applications : Option (Array Expr) := none) :
    TermElabM (Wire × Array EdgeRef) := do
  let state ← registryState
  match wire.form with
  | .contextual .. =>
      if applications.isSome then return (wire, route)
      return (← transportImage trace wire route applications encoder? capture?, #[])
  | .proofRefinement _ classifier _ =>
      if route[0]? == some (.classifierForget classifier) then
        let action ← match applications with
          | some selected => pure selected[0]!
          | none => Semantic.edgeFunctor state (.classifierForget classifier)
        let original ← proofRefinementBase trace wire action
        return ← canonicalOperationInput trace original (route.extract 1 route.size) encoder? capture?
          (applications.map (fun selected => selected.extract 1 selected.size))
      return (wire, route)
  | .object entry =>
      if applications.isSome && (wire.actualData || wire.objectObserved || wire.objectIso.isSome ||
          wire.capturedInvocation.isSome || wire.actionRecipe.isSome) then return (wire, route)
      let (_, remaining) := state.transport entry route
      let count := route.size - remaining.size
      return (← transport trace wire (route.extract 0 count) encoder? capture?
        (applications.map (fun selected => selected.extract 0 count)), remaining)
  | _ => return (wire, route)

/-- The compatible source-composite request retains every residual action in its
accepted registration, rather than requiring its input packet to execute it. -/
def canonicalOperationReceiver (trace : Trace) (wire : Wire) (route : Array EdgeRef)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none) :
    TermElabM Wire := do
  return (← canonicalOperationInput trace wire route encoder? capture?).1

/-- Keep the full mathematical receiver separate from its canonical computational input. -/
def operationReceiver (trace : Trace) (wire : Wire) (route : Array EdgeRef)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none) :
    TermElabM (Wire × Expr) := do
  let state ← registryState
  let image ← if route.isEmpty then pure wire.value else
    Semantic.objOf (← Semantic.routeFunctor state route) wire.value
  return (← canonicalOperationReceiver trace wire route encoder? capture?, image)

/-- Decode `j` as a registered named object at its parameters, `{"ctor": <object id>, "args":
[<numerals, or objects>]}`, elaborated and recorded in `trace`. -/
partial def decodeObject (trace : Trace) (j : Json) :
    TermElabM (Except String (ObjectEntry × Expr)) := do
  let state ← registryState
  let .ok id := j.getObjValAs? String "ctor" | return .error s!"{j.compress} is not a named object"
  let some entry := state.objects.find? (·.id.raw == id)
    | return .error s!"{id} is not a registered object"
  let .ok args := (j.getObjVal? "args").bind (·.getArr?)
    | return .error s!"{j.compress} has no `args` array"
  let family ← instantiateFresh entry.declaration
  let expected ← inferType family
  let decoded ← decodeDeclaration entry.declaration expected args fun type arg => do
    if (arg.getObjValAs? String "ctor").toOption.any
        (fun id => state.objects.any (·.id.raw == id)) then
      match ← decodeObject trace arg with
      | .error message => return .error message
      | .ok (parameter, value) =>
          unless ← isDefEq (← inferType value) type do
            return .error s!"{parameter.id.raw} is not a parameter of type {type}"
          return .ok (value, some (.object parameter))
    return (← Codec.decode type arg).map (·, none)
  match decoded with
  | .error message => return .error s!"a parameter of {id} is not decoded: {message}"
  | .ok (value, _) =>
      let value ← instantiateMVars value
      if value.hasMVar || value.hasLevelMVar then
        return .error s!"{id} does not determine a closed named object"
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let params := (value.getAppArgs.zip infos).filterMap fun (arg, info) =>
        if info.isExplicit then some arg else none
      let value ← Trace.recordProduced (some trace) value (.object entry.id params)
      return .ok (entry, value)

/-- Recover ordered application arguments beneath elaborator type hints. -/
def actualApplicationArguments (application : Expr) : Array Expr := Id.run do
  let mut application := Trace.unanchor application.consumeMData
  while application.isAppOfArity ``id 2 do
    application := Trace.unanchor application.appArg!.consumeMData
  return application.getAppArgs

mutual

/-- Decode `j` as a value of `type` in the category `category` (CC-DECODE): a morphism `a ⟶ b`
of the category by its graph, in its registered graph-literal form; a registered named object of
the category at its parameters; a literal of the category's registered literal form, denoted;
or, for any other type, a value of the structural codec. -/
partial def decodeValue (trace : Trace) (category : NamedCategoryEntry) (type : Expr) (j : Json) :
    TermElabM (Except String (Expr × Option Form)) := do
  let state ← registryState
  let type ← instantiateMVars type
  if let some result ← FunctorActionData.decode type j
      (decodeFunctorData trace category) (decodeSelectedSource trace) then
    let edgeJson? := (j.getObjVal? "args").toOption >>= (·.getArr?.toOption) >>= (·[0]?)
    let form? := edgeJson?.bind fun json =>
      (descriptorEdge? state json).map (fun edge => imageForm state edge category)
    return result.map (·, form?)
  let tag := (j.getObjValAs? String "ctor").toOption
  let mut diagramConstructors : Array Name := #[]
  for row in state.limits do
    if let some constructor ← Semantic.diagramConstructor row then
      if tag == some (Codec.label constructor) && !diagramConstructors.contains constructor then
        diagramConstructors := diagramConstructors.push constructor
  unless diagramConstructors.isEmpty do
    let .ok args := (j.getObjVal? "args").bind (·.getArr?)
      | return .error "a registered diagram has no ordered defining fields"
    let mut answers : Array Expr := #[]
    for constructor in diagramConstructors do
      let decoded ← withoutModifyingState <|
        decodeDeclaration constructor type args (decodeValue trace category)
      if let .ok (diagram, _) := decoded then answers := answers.push diagram
    match answers.toList with
    | [diagram] => return .ok (diagram, none)
    | [] => return .error "the diagram data has incompatible complete selected parameters"
    | _ => return .error "the diagram data has several distinct registered interpretations"
  if let some result ← ConstructionData.decode type j fun expected data => do
      return (← decodeValue trace category expected data).map (·.1) then
    let form? := do
      guard ((j.getObjValAs? String "ctor").toOption == some "limitApex")
      let args ← (j.getObjVal? "args").toOption >>= (·.getArr?.toOption)
      let id ← args[0]? >>= (·.getStr?.toOption)
      let row ← state.limits.find? (·.id.raw == id)
      return Form.limitApex row
    return result.map (·, form?)
  if tag == some "element" && (Language.homEnds? type).isNone then
    match ← decodeElementData trace category j with
    | .error message => return .error message
    | .ok value =>
      unless ← withTransparency .all <| isDefEq (← inferType value) type do
        return .error "the selected element has a different complete parameter type"
      return .ok (value, none)
  if let some address := tag then
    if let some (declaration, _) := state.callable? address then
      let .ok args := (j.getObjVal? "args").bind (·.getArr?)
        | return .error "a registered callable has no ordered complete parameters"
      match ← decodeDeclaration declaration type args (decodeValue trace category) with
      | .error message => return .error message
      | .ok (value, _) =>
        if let some entry := state.morphisms.find? (·.id.raw == address) then
          let value ← Semantic.namedMorphismProduced entry value (some trace)
          return .ok (value, some (.namedMorphism entry))
        return .ok (value, some (.canonicalMorphism category))
    if let some entry := state.inclusions.find? (·.id.raw == address) then
      let .ok args := (j.getObjVal? "args").bind (·.getArr?)
        | return .error "a registered inclusion has no ordered complete parameters"
      return (← decodeDeclaration entry.declaration type args (decodeValue trace category)).map
        (fun (value, _) => (value, some (.canonicalMorphism category)))
  if (j.getObjValAs? String "ctor").toOption.any (fun tag =>
      #["map", "compose", "presentation", "arrow", "arrowHom", "constructionLeg", "pointView",
        "operationPoint", "objectField", "powerObjectMap", "mediator", "element", "typedMap"].contains tag) then
    match ← decodeArrowData trace category j with
    | .error message => return .error message
    | .ok arrow =>
        unless ← isDefEq (← inferType arrow) type do
          return .error "the arrow descriptor has incompatible declared endpoints"
        return .ok (arrow, some (.canonicalMorphism category))
  if (j.getObjValAs? String "ctor").toOption == some "objectPresentation" then
    let .ok (value, target, _) ← decodePresentedObject trace category j
      | return .error "the complete fixed object presentation does not decode"
    unless target.syntacticEq category.expression do
      return .error "the presented object has a different exact selected category"
    unless ← withTransparency .all <| isDefEq (← inferType value) type do
      return .error "the presented object has different independently fixed type parameters"
    return .ok (value, some (.subobject category))
  if (j.getObjValAs? String "ctor").toOption == some "subobject" then
    let .construct constructor #[.category base] := category.expression
      | return .error "a subobject response requires a registered subobject category"
    unless (state.constructors.find? (·.id == constructor)).any
        (·.semantics == `CasCatalogue.Constructors.subobjects) do
      return .error "the response category is not the registered subobject constructor"
    let some ambient := state.categories.find? (·.expression.syntacticEq base)
      | return .error "the subobject ambient category has no registered name"
    let .ok args := (j.getObjVal? "args").bind (·.getArr?)
      | return .error "a subobject requires source, ambient object, and inclusion"
    unless args.size == 3 do return .error "a subobject requires all three defining fields"
    let source ← decodeObjectData trace ambient args[0]!
    let target ← decodeObjectData trace ambient args[1]!
    let (.ok source, .ok target) := (source, target)
      | return .error "a subobject endpoint has no registered data presentation"
    let homType ← mkAppM ``Quiver.Hom #[source, target]
    let .ok (inclusion, _) ← decodeValue trace ambient homType args[2]!
      | return .error "the subobject inclusion does not decode at its declared endpoints"
    let monoType ← mkAppM ``CategoryTheory.Mono #[inclusion]
    let mono? : Except String Expr ← if let some monicInstance := (← trySynthInstance monoType).toOption then pure (.ok monicInstance) else do
      let monoCriterion ← mkConstWithFreshMVarLevels ``CategoryTheory.ConcreteCategory.mono_of_injective
      let (params, infos, result) ← forallMetaTelescopeReducing (← inferType monoCriterion)
      unless ← withTransparency .all <| isDefEq result monoType do
        return .error "no independently available monicity criterion applies to this inclusion"
      -- Instance outparameters determine the exact accepted concrete hom/carrier families.
      -- Ordinary implicit data parameters are never submitted as typeclass goals.
      for _ in [:params.size] do
        for (param, info) in params.zip infos do
          unless info.isInstImplicit && (← instantiateMVars param).isMVar do continue
          let t ← instantiateMVars (← inferType param)
          if let some evidence := (← trySynthInstance t).toOption then
            discard <| isDefEq param evidence
      for param in params do
        unless (← instantiateMVars param).isMVar do continue
        let t ← instantiateMVars (← inferType param)
        unless ← isProp t do
          return .error "the monicity criterion has unresolved exact concrete data parameters"
        let some proof ← Codec.conditionProof t
          | return .error "the kernel does not establish monicity of the decoded inclusion"
        discard <| isDefEq param proof
      pure (.ok (← instantiateMVars (mkAppN monoCriterion params)))
    let .ok mono := mono? | return mono?.map (·, none)
    let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[inclusion]
    let constructor ← mkConstWithFreshMVarLevels ``CategoryTheory.ObjectProperty.FullSubcategory.mk
    let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
    unless ← withTransparency .all <| isDefEq result type do
      return .error "the decoded subobject has a different exact registered property category"
    unless fields.size >= 2 do throwError "the subobject constructor has changed"
    unless ← withTransparency .all <| isDefEq fields[fields.size - 2]! arrow do
      return .error "the subobject constructor rejects its complete defining arrow"
    unless ← withTransparency .all <| isDefEq fields.back! mono do
      return .error "the subobject constructor rejects its independently checked monicity"
    let value ← instantiateMVars (mkAppN constructor fields)
    unless ← isDefEq (← inferType value) type do
      return .error "the decoded subobject has the wrong category"
    let value ← StructuredResult.checkReconstruction value
    return .ok (value, some (.subobject category))
  if let .ok id := j.getObjValAs? String "ctor" then
    if let some entry := state.morphisms.find? (·.id.raw == id) then
      let .ok args := (j.getObjVal? "args").bind (·.getArr?)
        | return .error "a registered morphism has no ordered arguments"
      match ← decodeDeclaration entry.declaration type args (decodeValue trace category) with
      | .error message => return .error message
      | .ok (value, fields) =>
          let value ← Semantic.namedMorphismProduced entry value (some trace)
          return .ok (value, some (.namedMorphism entry))
  if (← whnfR type).isAppOf ``Quiver.Hom then
    let some form := state.graphLiterals.find? (·.category == category.id)
      | do
        -- A finite bundled homomorphism is structural data: its function field
        -- is decoded at the exact endpoints, and every law is proved independently.
        -- This does not register a graph primitive or erase its defining laws.
        match ← Codec.decode type j with
        | .error message =>
            return .error s!"the structural morphism of {category.name} is invalid: {message}"
        | .ok hom =>
            let hom ← StructuredResult.checkReconstruction hom
            return .ok (hom, some (.canonicalMorphism category))
    return ← match ← decodeFamily form.denotation type #[j] fun t j' => do
        return (← Codec.decode t j').map (·, none) with
      | .ok (hom, fields) => do
          let hom ← if let some (graph, _) := fields[0]? then
            Trace.recordProduced (some trace) hom (.literal form.id graph)
            else pure hom
          pure (.ok (hom, some (.graph form)))
      | .error message => pure (.error s!"{j.compress} is not the graph of a morphism \
          {type}: {message}")
  if (j.getObjValAs? String "ctor").toOption.any fun id => state.objects.any (·.id.raw == id) then
    match ← decodeObject trace j with
    | .error message => return .error message
    | .ok (entry, value) =>
        unless ← isDefEq (← inferType value) type do
          return .error s!"{entry.id.raw} is not an object of the expected type {type}"
        return .ok (value, some (.object entry))
  if let some form := state.literals.find? (·.category == category.id) then
    if let .ok literal ← Codec.decode (← mkConstWithFreshMVarLevels form.type) j then
      let value ← mkAppM form.denotation #[literal]
      unless ← isDefEq (← inferType value) type do
        return .error s!"{j.compress} is a literal of {form.id.raw}, not a {type}"
      let value ← Trace.recordProduced (some trace) value (.literal form.id literal)
      return .ok (value, some (.literal form))
  return (← Codec.decode type j).map (·, none)

/-- Recover an object's type from its own accepted descriptor, never from a target carrier. -/
partial def decodeObjectData (trace : Trace) (category : NamedCategoryEntry) (json : Json) :
    TermElabM (Except String Expr) := do
  let state ← registryState
  if (json.getObjValAs? String "ctor").toOption == some "morphismEndpoint" then
    let .ok endpoint := Backend.MorphismEndpoint.decode json
      | return .error "the endpoint projection has incomplete callable data"
    let .ok callable ← decodeArrowData trace category endpoint.callable
      | return .error "the declared endpoint's callable does not decode"
    let some (source, target) := Language.homEnds? (← inferType callable)
      | return .error "the declared endpoint does not belong to a categorical map"
    return .ok (if endpoint.source then source else target)
  let inCategory := fun id =>
    id == category.id || (state.categories.find? (·.id == id)).any fun entry =>
      entry.expression.syntacticEq category.expression ||
      match entry.expression, category.expression with
      | .familyApp left _, .familyApp right _ => left == right
      | _, _ => false
  if (json.getObjValAs? String "ctor").toOption == some "objectPresentation" then
    let .ok (value, selected, _) ← decodePresentedObject trace category json
      | return .error "the complete object presentation does not decode"
    unless selected.syntacticEq category.expression do
      return .error "the object presentation belongs to a different exact category"
    return .ok value
  if let some decoded ← FunctorActionData.decodeInferred json
      (decodeFunctorData trace category) (decodeSelectedSource trace) then
    match decoded with
    | .error message => return .error message
    | .ok (value, selected) =>
        unless selected.syntacticEq category.expression ||
            (match selected, category.expression with
            | .familyApp a _, .familyApp b _ => a == b
            | _, _ => false) do
          return .error "the accepted action object belongs to a different selected category"
        return .ok value
  if (json.getObjValAs? String "ctor").toOption == some "limitApex" then
    let .ok args := (json.getObjVal? "args").bind (·.getArr?)
      | return .error "a canonical apex has no defining fields"
    let some id := args[0]?.bind (·.getStr?.toOption)
      | return .error "a canonical apex has no registered limit id"
    let some row := state.limits.find? (·.id.raw == id)
      | return .error "a canonical apex names an unregistered limit"
    unless inCategory row.category do return .error "the canonical apex belongs to a different selected category"
    let family ← instantiateFresh row.declaration
    let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
      else ``CategoryTheory.Limits.LimitCone.cone) #[family]
    let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
      else ``CategoryTheory.Limits.Cone.pt) #[cone]
    return (← decodeValue trace category (← inferType apex) json).map (·.1)
  match ← decodeObject trace json with
  | .error message => return .error message
  | .ok (entry, value) =>
      unless inCategory entry.category do return .error "the object descriptor belongs to a different selected category"
      return .ok value

/-- Decode the complete selected source at the actual registered functor domain. -/
partial def decodeSelectedSource (trace : Trace) (source : CategoryExpr) (expected : Expr)
    (json : Json) : TermElabM (Except String Expr) := do
  let state ← registryState
  let category ← Semantic.namedCategoryFor state source
  if (json.getObjValAs? String "ctor").toOption == some "objectPresentation" then
    let .ok (value, target, _) ← decodePresentedObject trace category json
      | return .error "the actual source object presentation does not decode"
    unless target.syntacticEq source do return .error "the presented source uses a different selected category"
    unless ← withTransparency .all <| isDefEq (← inferType value) expected do
      return .error "the presented source has different complete action type parameters"
    return .ok value
  let decoded ← match source with
    | .construct constructor #[.category base] =>
        if (state.constructors.find? (·.id == constructor)).any
            (·.semantics == `CasCatalogue.Constructors.arrow) then do
          let tag := (json.getObjValAs? String "ctor").toOption
          if tag.any (fun id => state.objects.any (·.id.raw == id)) ||
              tag == some "functorAction" then
            decodeObjectData trace category json
          else
            let baseCategory ← Semantic.namedCategoryFor state base
            match ← decodeArrowData trace baseCategory json with
            | .error message => pure (.error message)
            | .ok hom => pure (.ok (← mkAppM ``CategoryTheory.Arrow.mk #[hom]))
        else decodeObjectData trace category json
    | _ => decodeObjectData trace category json
  match decoded with
  | .error message => return .error message
  | .ok value =>
      unless ← isDefEq (← inferType value) expected do
        return .error "the selected source is outside the actual registered functor domain"
      return .ok (← StructuredResult.checkReconstruction value)

/-- Decode accepted functor data, including classifier and constructor edges. -/
partial def decodeFunctorData (trace : Trace) (category : NamedCategoryEntry) (json : Json) :
    TermElabM (Except String (Expr × CategoryExpr × CategoryExpr)) := do
  let state ← registryState
  let .ok tag := json.getObjValAs? String "ctor" | return .error "a functor has no constructor"
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | return .error "a functor has no ordered declaration arguments"
  if let some entry := state.functors.find? (·.id.raw == tag) then
    let source ← Semantic.namedCategoryFor state entry.source
    return (← decodeDeclaration entry.declaration
      (← inferType (← instantiateFresh entry.declaration)) args (decodeValue trace source)).map
      (fun (F, _) => (F, entry.source, entry.target))
  match tag, args with
  | "classifierForget", #[idJson, paramsJson] =>
      let .ok id := idJson.getStr? | return .error "a classifier edge has no registered id"
      let some entry := state.classifiers.find? (·.id.raw == id)
        | return .error "the classifier edge is not registered"
      let .ok params := paramsJson.getArr? | return .error "classifier declaration arguments are not ordered data"
      let .ok (classifier, _) ← decodeDeclaration entry.declaration
          (← inferType (← instantiateFresh entry.declaration)) params (decodeValue trace category)
        | return .error "the classifier does not decode at its exact accepted signature"
      let mut classifier := classifier
      let type ← whnfR (← inferType classifier)
      if type.isAppOf ``LeanCategories.PropertyClassifier then
        classifier ← mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[classifier]
      else if type.isAppOf ``LeanCategories.StructureClassifier then
        classifier ← mkAppM ``LeanCategories.StructureClassifier.toClassifier #[classifier]
      let F ← mkAppM ``CategoryTheory.Cat.Hom.toFunctor
        #[← mkAppM ``LeanCategories.Classifier.forget #[classifier]]
      return .ok (F, .refine entry.host entry.id, entry.host)
  | "constructorMap", #[idJson, innerJson] =>
      let .ok id := idJson.getStr? | return .error "a constructor edge has no registered id"
      let some constructor := state.constructors.find? (·.id.raw == id)
        | return .error "the functorial constructor is not registered"
      let some action := constructor.functorialAction
        | return .error "the registered constructor has no accepted action on functors"
      let .ok (inner, source, target) ← decodeFunctorData trace category innerJson
        | return .error "the inner constructor functor does not decode"
      let F ← mkAppM action #[← Semantic.asFunctor inner]
      return .ok (F, .construct constructor.id #[.category source],
        .construct constructor.id #[.category target])
  | _, _ => return .error "unknown functor descriptor or wrong declaration argument arity"

/-- Synthesize declaration instances and independently check a closed arrow term. -/
partial def completeArrow (declaration : Expr) (params : Array Expr) :
    TermElabM (Except String Expr) := do
  let infos ← forallTelescopeReducing (← inferType declaration) fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  for (param, info) in params.zip infos do
    unless info.isInstImplicit && (← instantiateMVars param).isMVar do continue
    let some instanceValue ← Codec.dataInstance (← instantiateMVars (← inferType param))
      | return .error "the declared arrow has an unresolved category instance"
    discard <| isDefEq param instanceValue
  let value ← instantiateMVars (mkAppN declaration params)
  if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
    return .error "the arrow descriptor has unresolved declaration parameters"
  return .ok (← StructuredResult.checkReconstruction value)

/-- Infer an arrow only from complete endpoints or independently registered declarations. -/
partial def decodeElementData (trace : Trace) (category : NamedCategoryEntry) (json : Json) :
    TermElabM (Except String Expr) := do
  let state ← registryState
  let .ok #[selectedJson, _] := (json.getObjVal? "args").bind (·.getArr?)
    | return .error "the element requires its complete selected object and point data"
  let selected ← if let some result ← FunctorActionData.decodeInferred selectedJson
      (decodeFunctorData trace category) (decodeSelectedSource trace) then
    match result with
    | .error message => return .error message
    | .ok (value, expression) =>
      pure (value, ← Semantic.namedCategoryFor state expression)
    else do
      let .ok (entry, selected) ← decodeObject trace selectedJson
        | return .error "the element has no complete selected object descriptor"
      let some selectedCategory := state.categories.find? (·.id == entry.category)
        | return .error "the element's selected category is not registered"
      pure (selected, selectedCategory)
  let (selected, selectedCategory) := selected
  let selectedValue ← (Language.recognize state selected selectedCategory).run {}
  let carrier ← (Language.carrierObject selectedValue).run {}
  let target ← (Language.semanticObject carrier).run {}
  let decoders : ElementData.Decoders := {
    application := fun declaration expected params => do
      return (← decodeDeclaration declaration expected params (decodeValue trace selectedCategory)).map Prod.fst
    point := fun domain target data => do
      let decoded ← decodeArrowData trace category data
      match decoded with
      | .error message => return .error message
      | .ok point =>
        unless ← withTransparency .all <| isDefEq (← inferType point)
            (← mkAppM ``Quiver.Hom #[domain, target]) do
          return .error "the element point has incompatible complete endpoints"
        return .ok point }
  let some decoded ← ElementData.decode selectedValue selectedJson target json decoders
    | return .error "the selected element descriptor is incomplete"
  return decoded

/-- Infer an arrow only from complete endpoints or independently registered declarations. -/
partial def decodeArrowData (trace : Trace) (category : NamedCategoryEntry) (json : Json) :
    TermElabM (Except String Expr) := do
  let state ← registryState
  let .ok tag := json.getObjValAs? String "ctor"
    | return .error "an untyped arrow graph requires complete source and target fields"
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | return .error "an arrow descriptor has no defining fields"
  if let some (declaration, _) := state.callable? tag then
    let expected ← inferType (← instantiateFresh declaration)
    return (← decodeDeclaration declaration expected args (decodeValue trace category)).map Prod.fst
  if let some entry := state.inclusions.find? (·.id.raw == tag) then
    let expected ← inferType (← instantiateFresh entry.declaration)
    return (← decodeDeclaration entry.declaration expected args (decodeValue trace category)).map Prod.fst
  match tag, args with
  | "objectField", #[idJson, fieldJson, paramsJson] =>
      let .ok id := idJson.getStr? | return .error "the object field has no registered owner"
      let some entry := state.objects.find? (·.id.raw == id)
        | return .error "the object field owner is not registered"
      let .ok field := fieldJson.getStr? | return .error "the object field has no public field name"
      let some declaration := ObjectPresentation.fieldDeclaration entry field
        | return .error "the object has no such public field"
      let .ok params := paramsJson.getArr? | return .error "the object field parameters are not ordered data"
      let expected ← inferType (← instantiateFresh declaration)
      let .ok (application, _) ← decodeDeclaration declaration expected params (decodeValue trace category)
        | return .error "the object field parameters do not decode at their declared types"
      return .ok (← ObjectPresentation.fieldValue field application)
  | "powerObjectMap", #[idJson, fieldJson, paramsJson] =>
      let .ok id := idJson.getStr? | return .error "the power-object map has no registered owner"
      let some entry := state.powerObjects.find? (·.id.raw == id)
        | return .error "the power-object map owner is not registered"
      let .ok field := fieldJson.getStr? | return .error "the power-object map has no public field name"
      let declaration := match field with
        | "member" => some entry.member
        | "terminal" => some entry.terminal
        | "transpose" => some entry.transpose
        | "image" => some entry.image
        | "truth" => some entry.truth
        | _ => none
      let some declaration := declaration | return .error "the power object has no such public field"
      let .ok params := paramsJson.getArr? | return .error "the power-object parameters are not ordered data"
      let expected ← inferType (← instantiateFresh declaration)
      return (← decodeDeclaration declaration expected params (decodeValue trace category)).map Prod.fst
  | "mediator", #[firstJson, secondJson] =>
      let .ok first ← decodeArrowData trace category firstJson
        | return .error "the first mediator leg does not decode at its declared endpoints"
      let .ok second ← decodeArrowData trace category secondJson
        | return .error "the second mediator leg does not decode at its declared endpoints"
      let some (domain, left) := Language.homEnds? (← inferType first)
        | return .error "the first mediator leg is not a categorical map"
      let some (otherDomain, right) := Language.homEnds? (← inferType second)
        | return .error "the second mediator leg is not a categorical map"
      unless ← withTransparency .all <| isDefEq domain otherDomain do
        return .error "the mediator legs have different generalized-point domains"
      let diagramSyntax ← (Language.standardDiagram "product"
        #[.object left category none none none, .object right category none none none]).run {}
      let diagram ← elabTermAndSynthesize diagramSyntax none
      let presentation ← Semantic.limit false "product" diagram category.id.raw (some trace)
      let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[first, second]
      let universal ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[presentation]
      return .ok (← StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.Limits.IsLimit.lift #[universal, fan]))
  | "element", #[_, _] =>
      let .ok point ← decodeElementData trace category json
        | return .error "the element point does not decode at its selected structure"
      let domain ← closedElementDomain state
      let function ← withLocalDeclD `point domain fun argument => mkLambdaFVars #[argument] point
      return .ok (← StructuredResult.checkReconstruction (← mkAppM ``TypeCat.ofHom #[function]))
  | "arrowHom", #[objectJson] =>
      let decoded ← if (objectJson.getObjValAs? String "ctor").toOption.any
          (#["functorAction", "objectPresentation"].contains ·) then
        decodePresentedObject trace category objectJson
      else if (objectJson.getObjValAs? String "ctor").toOption == some "arrow" then do
        let .ok hom ← decodeArrowData trace category objectJson
          | return .error "the complete arrow object's defining map does not decode"
        let #[constructor] := state.constructors.filter
            (·.semantics == `CasCatalogue.Constructors.arrow)
          | return .error "the canonical arrow construction is not uniquely registered"
        pure (.ok (← mkAppM ``CategoryTheory.Arrow.mk #[hom],
          .construct constructor.id #[.category category.expression], none))
      else do
        match ← decodeObject trace objectJson with
        | .error message => pure (.error message)
        | .ok (entry, value) =>
          let some objectCategory := state.categories.find? (·.id == entry.category)
            | return .error "the stored arrow object has no registered category"
          pure (.ok (value, objectCategory.expression, none))
      let .ok (object, objectCategory, objectIso) := decoded
        | return .error "the stored arrow object does not decode at an accepted signature"
      let .construct constructor #[.category base] := objectCategory
        | return .error "the stored object does not belong to an arrow construction"
      unless (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        return .error "the stored object uses a different registered construction"
      let compatible := base.syntacticEq category.expression ||
        match base, category.expression with
        | .familyApp left _, .familyApp right _ => left == right
        | _, _ => false
      unless compatible do return .error "the stored arrow belongs to a different category"
      return .ok (← alignedArrowHom object objectIso)
  | "arrow", #[sourceJson, targetJson, mapJson]
  | "typedMap", #[sourceJson, targetJson, mapJson] =>
      let .ok source ← decodeObjectData trace category sourceJson
        | return .error "the arrow source does not have an accepted object descriptor"
      let .ok target ← decodeObjectData trace category targetJson
        | return .error "the arrow target does not have an accepted object descriptor"
      let expected ← mkAppM ``Quiver.Hom #[source, target]
      return (← decodeValue trace category expected mapJson).map (·.1)
  | "zero", #[sourceJson, targetJson] | "identity", #[sourceJson, targetJson] =>
      let .ok source ← decodeObjectData trace category sourceJson
        | return .error "the arrow source does not decode"
      let .ok target ← decodeObjectData trace category targetJson
        | return .error "the arrow target does not decode"
      let expected ← mkAppM ``Quiver.Hom #[source, target]
      let some decoded ← ConstructionData.decode expected json (fun t j => do
        return (← decodeValue trace category t j).map (·.1))
        | return .error "the arrow constructor is not recognized"
      return decoded
  | "compose", #[firstJson, secondJson] =>
      let .ok first ← decodeArrowData trace category firstJson
        | return .error "the first composite arrow does not decode"
      let .ok second ← decodeArrowData trace category secondJson
        | return .error "the second composite arrow does not decode"
      let comp ← mkConstWithFreshMVarLevels ``CategoryTheory.CategoryStruct.comp
      let (params, _, result) ← forallMetaTelescopeReducing (← inferType comp)
      unless params.size >= 2 do throwError "the categorical composition declaration has changed"
      unless ← isDefEq params[params.size - 2]! first do
        return .error "the first composite arrow is outside the selected category"
      unless ← isDefEq params[params.size - 1]! second do
        return .error "the composite arrows have incompatible shared endpoints"
      return ← completeArrow comp params
  | "presentation", #[idJson, paramsJson, inverseJson] =>
      let .ok id := idJson.getStr? | return .error "a presentation has no registered id"
      let some entry := state.presentations.find? (·.id.raw == id)
        | return .error "the presentation id is not registered"
      let .ok params := paramsJson.getArr? | return .error "presentation arguments are not ordered data"
      let .ok inverse := inverseJson.getBool? | return .error "presentation orientation is not Boolean"
      let expected ← inferType (← instantiateFresh entry.declaration)
      let .ok (iso, _) ← decodeDeclaration entry.declaration expected params (decodeValue trace category)
        | return .error "the presentation does not decode at its exact declaration signature"
      return .ok (← Semantic.presentationArrow entry iso inverse (some trace))
  | "operationPoint", #[idJson, paramsJson, comparisonJson, domainJson, selectedJson] =>
      unless category.id == CategoryId.sets do
        return .error "a terminal point must have its exact set-carrier category"
      let .ok id := idJson.getStr? | return .error "the terminal operation has no id"
      let some entry := state.operations.find? (·.id.raw == id)
        | return .error "the terminal operation is not registered"
      let .ok params := paramsJson.getArr? | return .error "the terminal operation parameters are not ordered"
      let expected ← inferType (← instantiateFresh entry.declaration)
      let .ok (operation, _) ← decodeDeclaration entry.declaration expected params (decodeValue trace category)
        | return .error "the terminal operation does not decode at its full declaration"
      let operation ← StructuredResult.checkReconstruction operation
      let operationType ← inferType operation
      unless ((comparisonJson.getObjVal? "ctor").bind (·.getStr?)).toOption == some "presentation" do
        return .error "the terminal comparison must retain its registered presentation descriptor"
      let .ok comparison ← decodeArrowData trace category comparisonJson
        | return .error "the terminal comparison does not decode"
      let comparisonType ← whnfR (← inferType comparison)
      let comparisonArgs := comparisonType.getAppArgs
      unless comparisonArgs.size >= 2 &&
          (← withTransparency .all <| isDefEq comparisonArgs[comparisonArgs.size - 2]!
            (← closedElementDomain state)) do
        return .error "the terminal comparison changed its registered singleton source"
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, operation]
      let globalPoint ← Language.globalPoint.run {}
      let point ← elabTermAndSynthesize
        (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax composite)
          $(← exprToSyntax globalPoint))) none
      let selectedData : Except String (Expr × NamedCategoryEntry × Language.Value) ← if (selectedJson.getObjValAs? String "ctor").toOption ==
          some "functorAction" then
        let some result ← FunctorActionData.decodeInferred selectedJson
            (decodeFunctorData trace category) (decodeSelectedSource trace)
          | return .error "the selected terminal action is incomplete"
        match result with
        | .error message => pure (.error message)
        | .ok (selected, expression) =>
          let selectedCategory ← Semantic.namedCategoryFor state expression
          pure (.ok (selected, selectedCategory,
            Language.Value.object selected selectedCategory none none none))
      else do
        match ← decodeObject trace selectedJson with
        | .error message => pure (.error message)
        | .ok (entry, selected) =>
          let some selectedCategory := state.categories.find? (·.id == entry.category) | unreachable!
          let selectedValue ← (Language.recognize state selected selectedCategory).run {}
          pure (.ok (selected, selectedCategory, selectedValue))
      let .ok (selected, _, selectedValue) := selectedData
        | return .error "the terminal target has no complete accepted structured descriptor"
      let operationHom ← whnfR operationType
      let operationEnds := operationHom.getAppArgs
      let some operationTarget := operationEnds.back?
        | return .error "the terminal operation has no declared target endpoint"
      let mut selectedParameter := false
      for parameter in operation.getAppArgs do
        if (operationTarget.find? (· == parameter)).isSome &&
            (← withoutModifyingState (withTransparency .all <| isDefEq parameter selected)) then
          selectedParameter := true
      unless selectedParameter do
        return .error "the terminal operation has a different complete declared target structure"
      let carrier ← (Language.carrierObject selectedValue).run {}
      unless ← withTransparency .all <| isDefEq (← inferType point)
          (← (Language.semanticObject carrier).run {}) do
        return .error "the terminal point changed its selected target carrier"
      let .ok domain ← decodeObjectData trace category domainJson
        | return .error "the original generalized point domain does not decode"
      let function ← withLocalDeclD `point domain fun argument => mkLambdaFVars #[argument] point
      return .ok (← StructuredResult.checkReconstruction (← mkAppM ``TypeCat.ofHom #[function]))
  | "pointView", #[targetJson, sourceAnswer, domainJson] =>
      unless category.id == CategoryId.sets do
        return .error "a forward carrier point is a sets morphism"
      let .ok "element" := sourceAnswer.getObjValAs? String "ctor"
        | return .error "a forward point requires complete selected arithmetic data"
      let .ok #[sourceJson, _] := (sourceAnswer.getObjVal? "args").bind (·.getArr?)
        | return .error "a forward point has no complete selected source"
      let .ok (sourceEntry, source) ← decodeObject trace sourceJson
        | return .error "the original point structure does not decode"
      let some sourceCategory := state.categories.find? (·.id == sourceEntry.category) | unreachable!
      let sourceValue ← (Language.recognize state source sourceCategory).run {}
      let baseSource : Json → Option Json := fun json => Id.run do
        let mut current := json
        for _ in [:64] do
          if (current.getObjValAs? String "ctor").toOption != some "functorAction" then
            return some current
          let .ok #[_, parent] := (current.getObjVal? "args").bind (·.getArr?)
            | return none
          current := parent
        return none
      unless (targetJson.getObjValAs? String "ctor").toOption == some "functorAction" &&
          baseSource targetJson == some sourceJson do
        return .error "the forward action does not retain this exact selected point source"
      let some targetData ← FunctorActionData.decodeInferred targetJson
          (decodeFunctorData trace category) (decodeSelectedSource trace)
        | return .error "the complete forward selected object action is incomplete"
      let (target, targetExpression) ← match targetData with
        | .ok result => pure result
        | .error message => return .error s!"the complete forward selected object action does not decode: {message}"
      let targetCategory ← Semantic.namedCategoryFor state targetExpression
      let mut action := targetJson
      let mut route : Array EdgeRef := #[]
      let mut applications : Array (EdgeRef × Array Expr) := #[]
      let mut functors : Array Expr := #[]
      for _ in [:64] do
        if (action.getObjValAs? String "ctor").toOption != some "functorAction" then break
        let .ok #[edgeJson, parent] := (action.getObjVal? "args").bind (·.getArr?)
          | return .error "the forward action has incomplete source provenance"
        let some edge := descriptorEdge? state edgeJson
          | return .error "the forward object action is not a registered structural edge"
        let .ok (functor, _, _) ← decodeFunctorData trace category edgeJson
          | return .error "the retained point view action does not instantiate"
        let functor ← Semantic.asFunctor functor
        route := #[edge] ++ route
        applications := #[(edge, actualApplicationArguments functor)] ++ applications
        functors := #[functor] ++ functors
        action := parent
      let mut currentCategory := sourceCategory.expression
      let mut image := source
      for (step, functor) in route.zip functors do
        let some edge := (state.edgesFrom currentCategory).find? (·.ref == step)
          | return .error "the forward point action is not a declared structural route"
        image ← Semantic.objOf functor image
        currentCategory := edge.target
      unless ← withTransparency .all <| isDefEq image target do
        return .error "the forward point route does not yield its full selected target"
      let targetValue : Language.Value := .object target targetCategory none none
        (some (#[sourceValue], sourceValue, route, #[], applications))
      let sourceCarrier ← (Language.carrierObject sourceValue).run {}
      let targetCarrier ← (Language.carrierObject targetValue).run {}
      let .object sourceType _ _ _ _ := sourceCarrier
        | return .error "the original point has no accepted carrier view"
      let .object targetType _ _ _ _ := targetCarrier
        | return .error "the selected point has no accepted carrier view"
      unless ← withTransparency .all <| isDefEq sourceType targetType do
        return .error "the declared structural object action changes the point carrier"
      let decoders : ElementData.Decoders := {
        application := fun declaration expected args => do
          return (← decodeDeclaration declaration expected args (decodeValue trace sourceCategory)).map Prod.fst
        point := fun domain target data => do
          let decoded ← decodeArrowData trace category data
          match decoded with
          | .error message => return .error message
          | .ok point =>
            let expected ← mkAppM ``Quiver.Hom #[domain, target]
            unless ← withTransparency .all <| isDefEq (← inferType point) expected do
              return .error "the retained point has different declared endpoints"
            return .ok point }
      let some (.ok point) ← ElementData.decode sourceValue sourceJson sourceType sourceAnswer decoders
        | return .error "the original selected arithmetic point does not reconstruct"
      let .ok domain ← decodeObjectData trace category domainJson
        | return .error "the exact generalized point domain does not decode"
      let function ← withLocalDeclD `point domain fun argument => do
        let point ← mkExpectedTypeHint point targetType
        mkLambdaFVars #[argument] point
      let value ← mkAppM ``TypeCat.ofHom #[function]
      return .ok (← StructuredResult.checkReconstruction value)
  | "constructionLeg", _ =>
      return .error "a computational defining leg requires its retained formal construction context"
  | "limitLeg", _ =>
      let some id := args[0]?.bind (·.getStr?.toOption)
        | return .error "a canonical defining map has no registered limit id"
      let some row := state.limits.find? (·.id.raw == id)
        | return .error "a canonical defining map names an unregistered limit"
      let family ← instantiateFresh row.declaration
      let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[family]
      let leg ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.ι
        else ``CategoryTheory.Limits.Cone.π) #[cone]
      let app ← mkAppM ``CategoryTheory.NatTrans.app #[leg]
      let (_, _, expected) ← forallMetaTelescopeReducing (← inferType app)
      let some decoded ← ConstructionData.decode expected json (fun t j => do
        return (← decodeValue trace category t j).map (·.1))
        | return .error "the canonical defining map is not recognized"
      return decoded
  | "map", #[functorJson, sourceJson] =>
      let .ok (F, sourceExpression, _) ← decodeFunctorData trace category functorJson
        | return .error "the mapped functor descriptor does not decode"
      let sourceCategory ← Semantic.namedCategoryFor state sourceExpression
      let .ok sourceMap ← decodeArrowData trace sourceCategory sourceJson
        | return .error "the mapped source arrow does not decode from its exact descriptor"
      let mapDeclaration ← mkConstWithFreshMVarLevels ``CategoryTheory.Functor.map
      let (params, _, _) ← forallMetaTelescopeReducing (← inferType mapDeclaration)
      unless params.size >= 4 do throwError "the functor map declaration has changed"
      -- Its final explicit argument is the source arrow; unification checks category and ends.
      let infos ← forallTelescopeReducing (← inferType mapDeclaration) fun xs _ => xs.mapM (·.fvarId!.getBinderInfo)
      let explicit := (params.zip infos).filterMap fun (arg, info) => if info.isExplicit then some arg else none
      unless explicit.size == 2 do throwError "the functor map explicit signature has changed"
      unless (← isDefEq explicit[0]! F) && (← isDefEq explicit[1]! sourceMap) do
        return .error "the mapped arrow is outside the declared functor source"
      return ← completeArrow mapDeclaration params
  | _, _ => return .error "unknown arrow descriptor or incorrect defining-field arity"

/-- Reconstruct complete presented object data together with its full selected-object comparison. -/
partial def decodePresentedObject (trace : Trace) (context : NamedCategoryEntry) (json : Json) :
    TermElabM (Except String (Expr × CategoryExpr × Option Expr)) := do
  let state ← registryState
  let .ok tag := json.getObjValAs? String "ctor" | return .error "a presented object has no constructor"
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | return .error "a presented object has no complete defining data"
  if tag == "objectPresentation" then
    let #[fixedJson, returnedJson] := args
      | return .error "an object presentation requires the fixed action and complete returned subobject"
    unless (fixedJson.getObjValAs? String "ctor").toOption == some "functorAction" do
      return .error "the fixed presentation receiver is not a registered functor action"
    unless (returnedJson.getObjValAs? String "ctor").toOption == some "subobject" do
      return .error "the returned presentation is not complete subobject data"
    let .ok (expected, target, prior) ← decodePresentedObject trace context fixedJson
      | return .error "the fixed complete construction does not decode"
    let category ← Semantic.namedCategoryFor state target
    let .ok (returned, _) ← decodeValue trace category (← inferType expected) returnedJson
      | return .error "the presented subobject does not decode at the fixed complete category"
    let comparison ← fixedConstructionComparison category expected returned returnedJson
    return .ok (returned, target, ← composeObjectComparisons prior comparison)
  unless tag == "functorAction" do return .error "the presented object is not an accepted complete action"
  let #[edgeJson, sourceJson] := args | return .error "the object action requires its full functor and source"
  let some (.ok (actual, target)) ← FunctorActionData.decodeInferred json
      (decodeFunctorData trace context) (decodeSelectedSource trace)
    | return .error "the complete presented functor action does not decode"
  let .ok (F, sourceCategory, _) ← decodeFunctorData trace context edgeJson
    | return .error "the presented action does not instantiate its registered functor"
  let sourceTag := (sourceJson.getObjValAs? String "ctor").toOption
  if sourceTag == some "objectPresentation" || sourceTag == some "functorAction" then
    let .ok (source, selectedCategory, comparison) ← decodePresentedObject trace context sourceJson
      | return .error "the complete source presentation does not decode"
    unless selectedCategory.syntacticEq sourceCategory do
      return .error "the source presentation belongs to a different exact action category"
    unless ← withTransparency .all <| isDefEq (← Semantic.objOf F source) actual do
      return .error "the presented action changed its actual complete source image"
    return .ok (actual, target, ← mapObjectComparison F source comparison)
  return .ok (actual, target, none)

/-- Bind canonical structured replies to the exact requested construction, including the
ambient object and defining inclusion. Mere membership in its result category is insufficient.
Scalar data remains subject to the independent assertion comparison. -/
partial def fixedConstructionComparison (category : NamedCategoryEntry) (expected value : Expr)
    (answer : Json) : TermElabM (Option Expr) := do
  let state ← registryState
  let canonical := (answer.getObjValAs? String "ctor").toOption == some "functorAction"
  let subobject := match category.expression with
    | .construct constructor #[.category _] =>
        (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.subobjects)
    | _ => false
  unless canonical || subobject do return none
  if let some presentation := (answer.getObjVal? "presentation").toOption then
    unless subobject do
      throwStratum .malformed "a subobject presentation requires the fixed subobject result category"
    let .construct _ #[.category base] := category.expression | unreachable!
    let ambientCategory ← Semantic.namedCategoryFor state base
    let expectedArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[expected]
    let returnedArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[value]
    let expectedApex ← mkAppM ``CategoryTheory.Arrow.left #[expectedArrow]
    let returnedApex ← mkAppM ``CategoryTheory.Arrow.left #[returnedArrow]
    let expectedAmbient ← mkAppM ``CategoryTheory.Arrow.right #[expectedArrow]
    let returnedAmbient ← mkAppM ``CategoryTheory.Arrow.right #[returnedArrow]
    unless ← withTransparency .all <| isDefEq expectedAmbient returnedAmbient do
      throwStratum .malformed "the subobject presentation changes the fixed ambient object"
    let expectedInclusion ← mkAppM ``CategoryTheory.Arrow.hom #[expectedArrow]
    let returnedInclusion ← mkAppM ``CategoryTheory.Arrow.hom #[returnedArrow]
    let .ok homJson := presentation.getObjVal? "hom"
      | throwStratum .malformed "the subobject presentation has no forward apex map"
    let .ok invJson := presentation.getObjVal? "inv"
      | throwStratum .malformed "the subobject presentation has no inverse apex map"
    let trace ← (Trace.new : IO _)
    let .ok (hom, _) ← decodeValue trace ambientCategory
        (← mkAppM ``Quiver.Hom #[expectedApex, returnedApex]) homJson
      | throwStratum .malformed "the subobject forward map has incompatible complete endpoints"
    let .ok (inv, _) ← decodeValue trace ambientCategory
        (← mkAppM ``Quiver.Hom #[returnedApex, expectedApex]) invJson
      | throwStratum .malformed "the subobject inverse map has incompatible complete endpoints"
    let conditions := #[
      (← mkEq (← mkAppM ``CategoryTheory.CategoryStruct.comp #[hom, inv])
        (← mkAppM ``CategoryTheory.CategoryStruct.id #[expectedApex])),
      (← mkEq (← mkAppM ``CategoryTheory.CategoryStruct.comp #[inv, hom])
        (← mkAppM ``CategoryTheory.CategoryStruct.id #[returnedApex])),
      (← mkEq (← mkAppM ``CategoryTheory.CategoryStruct.comp #[hom, returnedInclusion]) expectedInclusion),
      (← mkEq (← mkAppM ``CategoryTheory.CategoryStruct.comp #[inv, expectedInclusion]) returnedInclusion)]
    let mut proofs : Array Expr := #[]
    for condition in conditions do
      let some proof ← Codec.conditionProof condition
        | throwStratum .malformed "the subobject presentation does not establish both inverse equations and fixed-ambient inclusion squares"
      unless ← Decide.kernelAccepts condition proof do
        throwError "the checked subobject comparison proof does not inhabit its original condition"
      proofs := proofs.push proof
    let apexIsoType ← mkAppM ``CategoryTheory.Iso #[expectedApex, returnedApex]
    let apexIso ← withTransparency .all <| mkAppOptM ``CategoryTheory.Iso.mk
      #[none, none, some expectedApex, some returnedApex, some hom, some inv,
        some proofs[0]!, some proofs[1]!]
    unless ← withTransparency .all <| isDefEq (← inferType apexIso) apexIsoType do
      throwError "the assembled apex comparison has different full endpoints"
    let .ok comparison ← StructuredResult.subobjectComparison expected value apexIso proofs[2]!
      | throwError "the checked apex comparison did not induce its full fixed-ambient subobject comparison"
    return some comparison
  if ← isDefEq value expected then return none
  if canonical then
    throwStratum .malformed m!"the canonical action reply describes a different requested construction"
  throwStratum .noImplementation m!"the returned subobject needs a checked apex comparison preserving its inclusion into the fixed requested ambient object"


end

/-- Validate complete structured reply data even when its full comparison is not consumed. -/
def checkFixedConstruction (category : NamedCategoryEntry) (expected value : Expr)
    (answer : Json) : TermElabM Unit := do
  discard <| fixedConstructionComparison category expected value answer

/-- Replay context is fixed by the semantic operation, independently of reply data. -/
structure LiftReplayContext where
  fixedSource : Expr
  prescribed : Array LiftId
  fixedBase : Expr
  plan : Option LiftedSubobjectData.Plan := none

mutual

/-- Check a prescribed computational packet against its independently fixed operation.
The returned expression is the formal plan, not a reconstruction of backend data; in
particular, no comparison or monomorphism law is obtained from the packet. This
formal-reference path has no runtime request history: parameter checks concern
framing and fixed interfaces only, and establish no equality to unseen requests.
Runtime execution supplies its actual request parameters directly to `decodeIn`. -/
partial def decodeLiftedAt (_trace : Trace) (category : NamedCategoryEntry) (expected : Expr)
    (context : LiftReplayContext) (json : Json) :
    TermElabM (Except String (Expr × Option Expr)) := do
  let some checked ← LiftedSubobjectData.decode expected category context.fixedSource
      context.prescribed context.fixedBase json
      (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
      (fun _ formal data objects => do
        ComputationalData.validatePort formal (← inferType formal) data objects)
      none context.plan
    | return .error "the prescribed result requires a complete liftedSubobject packet"
  match checked with
  | .error message => return .error message
  | .ok packet => return .ok (packet.formalResult, none)

/-- Decode object data with the independently retained semantic child, rather than its type alone. -/
partial def decodeObjectAt (trace : Trace) (category : NamedCategoryEntry)
    (fixed : Expr) (json : Json) : TermElabM (Except String (Expr × Option Expr)) := do
  let state ← registryState
  let tag := (json.getObjValAs? String "ctor").toOption
  if tag == some "liftedSubobject" then
    let some (.methodWithLifts id route lifts receiver _ interpreted) ← trace.node? fixed
      | return .error "the lifted child has no independently retained prescribed operation"
    let .ok plan ← LiftedSubobjectData.planIn (← inferType fixed)
        interpreted.resultContext.expression receiver lifts interpreted.baseResult (some interpreted)
      | return .error "the lifted child lost its complete retained method plan"
    return ← decodeLiftedAt trace category (← inferType fixed)
      { fixedSource := receiver, prescribed := lifts,
        fixedBase := interpreted.baseResult, plan := some plan } json
  if tag == some "objectPresentation" then
    let .ok #[action, returned] := (json.getObjVal? "args").bind (·.getArr?)
      | return .error "the child presentation lacks its complete fixed action and result"
    let .ok (image, prior) ← decodeObjectAt trace category fixed action
      | return .error "the child presentation changed its independently retained action"
    let .ok (value, _) ← decodeValue trace category (← inferType fixed) returned
      | return .error "the child presentation result does not decode at its full fixed type"
    let comparison ← fixedConstructionComparison category image value returned
    return .ok (value, ← composeObjectComparisons prior comparison)
  if tag == some "functorAction" then
    if let some (.retainedRoute sourceId targetId route applications receiver) ← trace.node? fixed then
      unless route.size == applications.size && targetId == category.id do
        return .error "the retained structural child has different complete route endpoints"
      let some sourceEntry := state.categories.find? (·.id == sourceId)
        | return .error "the retained structural source category is not registered"
      let mut categories := #[sourceEntry]
      let mut current := sourceEntry.expression
      let mut expected := receiver
      for (step, application) in route.zip applications do
        let some edge := (state.edgesFrom current).find? (·.ref == step)
          | return .error "the retained structural child changed its exact registered route"
        let some target := imageCategory? state edge.target
          | return .error "the retained structural target has no unique accepted category"
        if application.hasMVar || application.hasLevelMVar || application.hasFVar ||
            application.hasLooseBVars then
          return .error "the retained structural application is not closed"
        expected ← Semantic.objOf application expected
        categories := categories.push target
        current := edge.target
      unless ← withTransparency .all <| isDefEq expected fixed do
        return .error "the retained structural child changed its original full semantic image"
      let rec walk (count : Nat) (data : Json) :
          TermElabM (Except String (Expr × Option Expr)) := do
        match count with
        | 0 => decodeObjectAt trace sourceEntry receiver data
        | index + 1 =>
          unless (data.getObjValAs? String "ctor").toOption == some "functorAction" do
            return .error "the retained structural child lacks its complete ordered action"
          let .ok #[edgeJson, sourceJson] := (data.getObjVal? "args").bind (·.getArr?)
            | return .error "the retained structural child action has incomplete data"
          unless descriptorEdge? state edgeJson == some route[index]! do
            return .error "the structural child descriptor changed its registered edge"
          let .ok (F, source, target) ← decodeFunctorData trace categories[index + 1]! edgeJson
            | return .error "the retained structural edge does not decode"
          unless source.syntacticEq categories[index]!.expression &&
              target.syntacticEq categories[index + 1]!.expression &&
              (← withTransparency .all <| isDefEq (← Semantic.asFunctor F)
                (← Semantic.asFunctor applications[index]!)) do
            return .error "the structural child changed a complete retained edge application"
          let .ok (actualSource, comparison) ← walk index sourceJson
            | return .error "the structural child changed its independently retained source"
          let value ← Semantic.objOf F actualSource
          return .ok (value, ← mapObjectComparison F actualSource comparison)
      return ← walk route.size json
  if tag == some "subobjectApex" || tag == some "subobjectInclusion" then
    let some (.functor id params receiver) ← trace.node? fixed
      | return .error "the projection child has no independently retained source action"
    let some entry := state.functor? id
      | return .error "the projection child action is not registered"
    let sourceCategory ← Semantic.namedCategoryFor state entry.source
    let .ok #[source] := (json.getObjVal? "args").bind (·.getArr?)
      | return .error "the projection child has no complete retained receiver"
    let receiverDecoder := fun data => do
      let result ← decodeObjectAt trace sourceCategory receiver data
      return result.map fun (value, _) => (value, sourceCategory.expression)
    let some (.ok (projected, resultCategory)) ← FunctorActionData.decodeInferred json
        (decodeFunctorData trace category) (decodeSelectedSource trace) (some receiverDecoder)
      | return .error "the projection failed its independent complete receiver check"
    unless resultCategory.syntacticEq category.expression do
      return .error "the projection changed its independently selected result category"
    let action := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
      Json.mkObj [("ctor", id.raw), ("args", Json.arr (← params.mapM (parameterData trace)))], source])]
    let .ok (value, comparison) ← decodeObjectAt trace category fixed action
      | return .error "the projection does not match its independently retained action"
    unless ← withTransparency .all <| isDefEq value projected do
      return .error "the projection changed the actual stored defining data"
    return .ok (value, comparison)
  if tag == some "functorAction" then
    let some (.functor id params receiver) ← trace.node? fixed
      | return .error "the action child has no independently retained full source operation"
    let some entry := state.functor? id
      | return .error "the child action is not registered"
    let .ok #[edge, source] := (json.getObjVal? "args").bind (·.getArr?)
      | return .error "the child action lacks its exact edge and full source"
    unless (edge.getObjValAs? String "ctor").toOption == some id.raw do
      return .error "the child action changed its independently registered declaration"
    let .ok (actualF, sourceCategory, targetCategory) ← decodeFunctorData trace category edge
      | return .error "the child edge does not decode as an accepted action"
    let declaration ← mkConstWithFreshMVarLevels entry.declaration
    let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
    let explicit := (arguments.zip infos).filterMap fun (arg, info) =>
      if info.isExplicit then some arg else none
    unless explicit.size == params.size do
      return .error "the retained child action has incompatible ordered declaration arguments"
    for (argument, parameter) in explicit.zip params do
      unless ← withTransparency .all <| isDefEq argument parameter do
        return .error "the child action changed a complete retained declaration parameter"
    let acceptedF := mkAppN declaration arguments
    unless targetCategory.syntacticEq category.expression &&
        (← withTransparency .all <| isDefEq actualF acceptedF) do
      return .error "the child descriptor changed its independently retained full action"
    let sourceEntry ← Semantic.namedCategoryFor state sourceCategory
    let .ok (actualSource, comparison) ← decodeObjectAt trace sourceEntry receiver source
      | return .error "the action source lacks its independently fixed child context"
    let value ← Semantic.objOf actualF actualSource
    let expected ← Semantic.objOf acceptedF receiver
    unless ← withTransparency .all <| isDefEq expected fixed do
      return .error "the retained child operation has different complete semantic endpoints"
    return .ok (value, ← mapObjectComparison actualF actualSource comparison)
  let .ok (value, _) ← decodeValue trace category (← inferType fixed) json
    | return .error "the object child does not decode at its independently fixed full type"
  let comparison ← fixedConstructionComparison category fixed value json
  if comparison.isNone then
    unless ← withTransparency .all <| isDefEq value fixed do
      return .error "the object child changes its independently fixed full value"
  return .ok (value, comparison)

end

/-- Validate aligned retained scopes. Only the explicit legacy single-supplier
adapter may fill a wholly unannotated record; partial annotations are rejected. -/
def scopedLiftExecution (execution : LiftExecution)
    (legacyOwner : Option DataOwnership.Owner := none) : TermElabM LiftExecution := do
  let absent := execution.actionOwnership.isEmpty && execution.parameterOwnership.isEmpty &&
    execution.sourceOwnership.isEmpty && execution.baseOwnership.isEmpty && execution.outputOwnership.isEmpty &&
    execution.sourceImageOwnership.isEmpty && execution.comparisonImageOwnership.isEmpty
  let scope := fun json => match legacyOwner with
    | some owner => DataOwnership.capture json owner
    | none => #[]
  let execution := if absent then { execution with
      actionOwnership := execution.actions.map scope
      parameterOwnership := execution.parameters.map (fun data => scope (Json.arr data))
      sourceOwnership := execution.sources.map scope
      baseOwnership := execution.bases.map scope
      outputOwnership := execution.outputs.map (fun fields => fields.map scope)
      sourceImageOwnership := execution.sourceImages.map scope
      comparisonImageOwnership := execution.comparisonImages.map scope }
    else execution
  let count := execution.selections.size
  unless count > 0 && execution.actions.size == count && execution.parameters.size == count &&
      execution.sources.size == count && execution.bases.size == count && execution.outputs.size == count &&
      execution.actionOwnership.size == count && execution.parameterOwnership.size == count &&
      execution.sourceOwnership.size == count && execution.baseOwnership.size == count &&
      execution.outputOwnership.size == count && execution.outputs.all (·.size == 4) &&
      execution.outputOwnership.all (·.size == 4) do
    throwError "the selected lift cache omits a required component output or exact scope"
  let legacyImages := execution.sourceImages.isEmpty && execution.comparisonImages.isEmpty &&
    execution.sourceImageOwnership.isEmpty && execution.comparisonImageOwnership.isEmpty
  unless legacyImages || (execution.sourceImages.size == count && execution.comparisonImages.size == count &&
      execution.sourceImageOwnership.size == count && execution.comparisonImageOwnership.size == count) do
    throwError "the selected lift cache omits an actual image or its exact scope"
  unless (legacyImages && execution.stageHandles.isEmpty) ||
      (execution.stageHandles.size == count && execution.stageHandles.all (·.outputs.size == 4)) do
    throwError "the selected lift cache omits an exact typed stage occurrence"
  for index in [:count] do
    for (json, ownership) in #[
        (execution.actions[index]!, execution.actionOwnership[index]!),
        (Json.arr execution.parameters[index]!, execution.parameterOwnership[index]!),
        (execution.sources[index]!, execution.sourceOwnership[index]!),
        (execution.bases[index]!, execution.baseOwnership[index]!)] do
      discard <| checkedFragment (DataOwnership.checkCoverage json ownership)
    for (json, ownership) in execution.outputs[index]!.zip execution.outputOwnership[index]! do
      discard <| checkedFragment (DataOwnership.checkCoverage json ownership)
    if !legacyImages then
      for (json, ownership) in #[
          (execution.sourceImages[index]!, execution.sourceImageOwnership[index]!),
          (execution.comparisonImages[index]!, execution.comparisonImageOwnership[index]!)] do
        discard <| checkedFragment (DataOwnership.checkCoverage json ownership)
  return execution

def liftFragments (data : Array Json) (ownership : Array DataOwnership.Table) :
    TermElabM (Array DataOwnership.Data) := do
  unless data.size == ownership.size do
    throwError "the retained lift data lost its aligned occurrence scopes"
  (data.zip ownership).mapM fun (json, ownership) => do
    let result : DataOwnership.Data := { json, ownership }
    discard <| checkedFragment result.validate
    return result

def LiftExecution.actionFragment (execution : LiftExecution) (index : Nat) :
    TermElabM DataOwnership.Data := do
  let some data := (← liftFragments execution.actions execution.actionOwnership)[index]?
    | throwError "the retained lift omitted a selected action"
  return data

def LiftExecution.sourceFragment (execution : LiftExecution) (index : Nat) :
    TermElabM DataOwnership.Data := do
  let some data := (← liftFragments execution.sources execution.sourceOwnership)[index]?
    | throwError "the retained lift omitted its original source"
  return data

def LiftExecution.baseFragment (execution : LiftExecution) (index : Nat) :
    TermElabM DataOwnership.Data := do
  let some data := (← liftFragments execution.bases execution.baseOwnership)[index]?
    | throwError "the retained lift omitted its complete base"
  return data

def LiftExecution.parameterFragment (execution : LiftExecution) (index : Nat) :
    TermElabM DataOwnership.Data := do
  let some data := (← liftFragments (execution.parameters.map Json.arr) execution.parameterOwnership)[index]?
    | throwError "the retained lift omitted its selected parameter array"
  return data

def LiftExecution.outputFragments (execution : LiftExecution) (index : Nat) :
    TermElabM (Array DataOwnership.Data) := do
  let some fields := execution.outputs[index]?
    | throwError "the retained lift omitted a component's outputs"
  let some ownership := execution.outputOwnership[index]?
    | throwError "the retained lift omitted its output occurrence scopes"
  liftFragments fields ownership

def LiftExecution.sourceImageFragment? (execution : LiftExecution) (index : Nat) :
    TermElabM (Option DataOwnership.Data) := do
  if execution.sourceImages.isEmpty && execution.sourceImageOwnership.isEmpty then return none
  let some data := (← liftFragments execution.sourceImages execution.sourceImageOwnership)[index]?
    | throwError "the retained lift omitted its actual source image"
  return some data

def LiftExecution.comparisonImageFragment? (execution : LiftExecution) (index : Nat) :
    TermElabM (Option DataOwnership.Data) := do
  if execution.comparisonImages.isEmpty && execution.comparisonImageOwnership.isEmpty then return none
  let some data := (← liftFragments execution.comparisonImages execution.comparisonImageOwnership)[index]?
    | throwError "the retained lift omitted its actual comparison image"
  return some data

/-- Existing lift request/step framing, with every input positioned explicitly. -/
def liftStageData (tag id : String) (parameters : DataOwnership.Data)
    (action source base : DataOwnership.Data) (outputs : Array DataOwnership.Data)
    (sourceImage? : Option DataOwnership.Data := none)
    (comparisonImage? : Option DataOwnership.Data := none) :
    TermElabM DataOwnership.Data :=
  LiftStageExecution.packet tag id parameters action source base outputs sourceImage? comparisonImage?

/-- Re-encode exactly the three typed-map fields, discarding only envelope
fields that the existing public encoder also discards. -/
def retagLiftMap (tag : String) (data : DataOwnership.Data) : TermElabM DataOwnership.Data := do
  let .ok _ := Backend.TypedMap.decode data.json
    | throwError "the lift's complete map omitted its actual ordered fields"
  let args ← checkedFragment (data.project #[.field "args"])
  checkedFragment (DataOwnership.Data.object [("ctor", { json := toJson tag }), ("args", args)])

/-- Attach actual data only to a role already fixed by the complete lift plan. -/
def liftOperand (formal : Expr) (context : CategoryContext) (origin : Form)
    (data : DataOwnership.Data) (morphism : Bool := false) (observed : Bool := false) :
    TermElabM Wire := do
  if morphism then
    discard <| contextualMorphismEndpoints context formal
  else CategoryContext.checkObject context formal
  return {
    form := contextualForm (← registryState) context origin morphism
    payload := (← scopedPayload formal data observed), categoryContext := some context
    objectObserved := observed && !morphism, callableObserved := observed && morphism }

/-- Endpoint positions are fixed before dispatch. A permitted inventory
enrichment keeps its original descriptor and supplier; matching token bytes
from another session cannot replace that exact endpoint occurrence. -/
partial def liftEndpointOperand (expected : Wire) (context : CategoryContext)
    (data : DataOwnership.Data) : TermElabM Wire := do
  if data == expected.fragment then return expected
  checkInventoryEndpointData expected.fragment data
  let expected ← captureDeclaredObjectInput expected context
  let inventory ← checkedFragment (data.project #[.field "args", .index 1])
  let value ← liftOperand expected.value context expected.form data false true
  let value := { value with
    objectIso := expected.objectIso, presentationIsos := expected.presentationIsos,
    serviceHandles := expected.serviceHandles }
  let value ← retainIntrinsicAssembly value .object context
    (.ctor "finiteData" #[.retained (.wire .object expected), .literal inventory])
  let some presentation := expected.endpointPresentation | return value
  -- The new view owns its own comparison endpoints. Anchored named/result
  -- producers remain on the complete original child, never on the new packet.
  discard <| currentNamedRefinementOrigin? expected
  let (forward, backward) ← endpointPresentationMaps expected context presentation
  let some (semantic, actual) ← retainedCallableEndpoints? forward context
    | throwError "the inventory view lost the forward comparison's complete endpoints"
  let some (reverseActual, reverseSemantic) ← retainedCallableEndpoints? backward context
    | throwError "the inventory view lost the backward comparison's complete endpoints"
  unless sameCompleteWireContext semantic (← forwardRetainedValue reverseSemantic semantic.value) &&
      sameCompleteWireContext actual (← forwardRetainedValue reverseActual actual.value) &&
      actual.fragment == expected.fragment do
    throwStratum .unavailable "the inventory view changed an original comparison endpoint occurrence"
  let actual ← liftEndpointOperand actual context data
  let forward ← captureInventoryMapEndpoints context forward semantic actual
  let backward ← captureInventoryMapEndpoints context backward actual semantic
  retainEndpointPresentationMaps value context presentation.comparison forward backward

/-- The producer's complete endpoint receipt is shared by actual and private
stage values. Reading it performs no dispatch and makes no new endpoint choice. -/
def liftStageEndpoints (wire : Wire) (context : CategoryContext) :
    TermElabM (Wire × Wire) := do
  let some endpoints ← retainedCallableEndpoints? wire context
    | throwError "the selected lift field omitted its complete endpoint occurrences"
  return endpoints

/-- Actual and prospective stage folds share typed ports. Only this producer
dispatches a field, validates its returned prefix and attaches actual endpoints. -/
def liftServiceInputPositions (path : DataOwnership.Path) (wire : Wire) :
    TermElabM (Array (DataOwnership.Path × Wire)) := do
  let mut positions := #[(path, wire)]
  if let .ok _ := Backend.TypedMap.decode wire.json then
    if let some context := wire.categoryContext then
      if let some (source, target) ← retainedCallableEndpoints? wire context then
        for (index, endpoint) in #[(0, source), (1, target)] do
          let localPath := #[.field "args", .index index]
          unless (← checkedFragment (wire.fragment.project localPath)) == endpoint.fragment do
            throwError "a positioned map input changed its retained endpoint occurrence"
          positions := positions.push (path ++ localPath, endpoint)
  return positions

def observeLiftStageFieldWithInputs (h : Harness) (input : LiftStageExecution.Input Wire)
    (requestValue : Expr) (form : Form) (dependencies : Array Wire)
    (staticInputPaths : Option (Array (DataOwnership.Path × Nat)))
    (field : LiftStageExecution.Field Wire) : TermElabM Wire := do
  if field.index == 0 then
    if let some image := input.sourceImage? then
      let sourceImage ← if input.originalArrow then
          checkedFragment (image.fragment.project #[.field "args", .index 0])
        else pure image.fragment
      if let .error message ← LiftedSubobjectData.validateSourceImageBase
          input.selection sourceImage.json input.base.json then
        throwStratum .malformed m!"the selected lift changed its actual image ambient: {message}"
  let dependencies := dependencies ++ #[input.original, input.source, input.base, input.baseObject] ++
    input.sourceImage?.toArray ++ input.sourceImageObject?.toArray ++
    field.preceding ++ field.comparisonImage?.toArray
  let serviceInputPaths ← staticInputPaths.mapM fun static => do
    let mut positions :=
      (← liftServiceInputPositions #[.field "args", .index 2] input.original) ++
      (← liftServiceInputPositions #[.field "args", .index 3] input.base)
    for (output, index) in field.preceding.zipIdx do
      positions := positions ++
        (← liftServiceInputPositions #[.field "args", .index 4, .index index] output)
    if let some image := input.sourceImage? then
      positions := positions ++ (← liftServiceInputPositions #[.field "sourceImage"] image)
      if let some comparison := field.comparisonImage? then
        positions := positions ++
          (← liftServiceInputPositions #[.field "comparisonImage"] comparison)
    return static ++ (← retainServiceInputPaths h field.request positions)
  let request : Wire := {
    form, payload := (← recipePayload requestValue field.request),
    serviceInputPaths,
    serviceHandles := (← retainServiceOperands h dependencies) ++ dependencies.flatMap (·.serviceHandles) }
  let operation := input.selection.entry.fieldAddress field.field
  let reply ← sendData h operation request
  let outputs := (field.preceding.map (·.json)).push reply.data.json
  let comparison := LiftedSubobjectData.ComparisonImageRole.ofMetadata
    input.sourceImage?.isSome (if input.sourceImage?.isSome then field.comparisonImage?.map (·.json) else none)
  if let .error message ← LiftedSubobjectData.validateSelectionPrefixWith input.selection
      input.action.json input.source.json input.base.json outputs comparison then
    malformed reply.backend operation reply.data.json message
  let output ← liftOperand field.formal field.context form reply.data (field.index != 0) true
  let output := { output with
    serviceHandles := request.serviceHandles
    morphismFramed := field.index != 0 }
  match field.endpoints with
  | none => return output
  | some (source, target) =>
      let sourceData ← checkedFragment (reply.data.project #[.field "args", .index 0])
      let targetData ← checkedFragment (reply.data.project #[.field "args", .index 1])
      let endpoint := fun (role : LiftStageExecution.EndpointRole Wire) (data : DataOwnership.Data) => do
        match role with
        | .retained expected => liftEndpointOperand expected field.context data
        | .produced formal =>
            let endpoint ← liftOperand formal field.context form data false true
            return { endpoint with serviceHandles := request.serviceHandles }
      let source ← endpoint source sourceData
      let target ← endpoint target targetData
      retainCallableEndpoints output source target field.context

def observeLiftStageField (h : Harness) (input : LiftStageExecution.Input Wire)
    (requestValue : Expr) (form : Form) (dependencies : Array Wire)
    (field : LiftStageExecution.Field Wire) : TermElabM Wire :=
  observeLiftStageFieldWithInputs h input requestValue form dependencies none field

/-- Exact source/base roles for a prescribed stage are supplied by its formal
component, including both full constructed category dictionaries. -/
def prescribedLiftViews (component : LiftedSubobjectData.Component) (source base : Wire)
    (sourceData baseData : DataOwnership.Data) : TermElabM (Wire × Wire) := do
  let state ← registryState
  let .constructMap arrow _ := component.selection.entry.edge
    | throwError "the retained prescribed source lost its accepted Arrow constructor"
  let #[subobjects] := state.constructors.filter
      (·.semantics == `CasCatalogue.Constructors.subobjects)
    | throwError "the retained prescribed base has no unique accepted subobject constructor"
  let sourceContext ← CategoryContext.construct (← SelectedLift.context component.selection) arrow
  let baseContext ← CategoryContext.construct (← SelectedLift.context component.selection true) subobjects.id
  return (← liftOperand component.receiver sourceContext source.form sourceData,
    ← liftOperand component.base baseContext base.form baseData)

/-- The selected inclusion and its already checked monicity supply the complete
formal base. No computational field supplies the predicate or its witness. -/
def selectedLiftBaseOperand (plan : SelectedLift.Plan) (origin : Form)
    (data : DataOwnership.Data) : TermElabM Wire := do
  let #[subobjects] := (← registryState).constructors.filter
      (·.semantics == `CasCatalogue.Constructors.subobjects)
    | throwError "the selected base has no unique accepted subobject constructor"
  let context ← CategoryContext.construct (← SelectedLift.context plan true) subobjects.id
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[plan.inclusion]
  let constructor ← mkConstWithFreshMVarLevels ``CategoryTheory.ObjectProperty.FullSubcategory.mk
  let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless fields.size >= 2 && (← withTransparency .all <|
      isDefEq result (← CategoryContext.carrier context) <&&>
      isDefEq fields[fields.size - 2]! arrow <&&> isDefEq fields.back! plan.monic) do
    throwError "the selected base lost its complete inclusion or independently checked monicity"
  let formal ← instantiateMVars (mkAppN constructor fields)
  liftOperand formal context origin data

def retainLiftOperands (h : Harness) (wires : Array Wire) : IO (Array Nat) := do
  return wires.flatMap (·.serviceHandles) ++ (← retainServiceOperands h wires)

/-- Retain the selected functor descriptor as a value with its original ordered
parameter producers. A full functor value has no object category or object-action
completion claim; its intrinsic template owns every positioned data dependency. -/
def retainedLiftActionValue (selection : SelectedLift.Plan) (origin : Form)
    (template : ActionDataTemplate) : TermElabM Wire := do
  let state ← registryState
  let inner ← SelectedLift.innerEdge state selection.entry
  checkExecutableEdgeAction state inner selection.action
  let (data, dependencies) ← renderCapturedActionData template
  let result : Wire := {
    form := origin, payload := (← combinedPayload selection.action data dependencies),
    serviceHandles := dependencies.flatMap (·.serviceHandles) }
  let result ← retainIntrinsicResultAssembly result (.value (← inferType selection.action)) template
  checkCapturedResultInterface result (.value (← inferType selection.action))
  return result

/-- Preserve every complete producer occurrence used by later fields and
factors. The returned indices are retained in the containing result's scope. -/
def retainLiftStageHandles (h : Harness) (input : LiftStageExecution.Input Wire)
    (result : LiftStageExecution.Result Wire) (action : Wire) : TermElabM LiftStageHandles := do
  let some sourceImage := input.sourceImageObject?
    | throwError "an actual lift stage omitted its exact source image object"
  unless result.outputs.size == 4 do
    throwError "an actual lift stage omitted a public output occurrence"
  unless action.fragment == input.action do
    throwError "the retained lift action changed its positioned parameter data or suppliers"
  let action ← forwardRetainedValue action input.selection.action
  checkCapturedResultInterface action (.value (← inferType input.selection.action))
  let handles ← retainServiceOperands h
    (#[action, input.source, sourceImage, input.base, input.baseObject, result.comparisonImage] ++ result.outputs)
  return {
    action := handles[0]!, source := handles[1]!, sourceImage := handles[2]!, base := handles[3]!,
    baseObject := handles[4]!, comparisonImage := handles[5]!, outputs := handles.extract 6 10 }

/-- Preserve the scoped legacy recipe entry point, using the shared typed field
fold in reverse route order. Production with retained actual action images uses
`executePrescribedRetainedWith`. The selected plan and every descriptor owner
remain fixed before dispatch; no reply supplies a semantic term or lift law. -/
def executePrescribedLiftData (h : Harness) (trace : Trace) (plan : LiftedSubobjectData.Plan)
    (source base : Wire) (parameters : Array (Array DataOwnership.Data × Array Wire))
    (encoder? : Option ScopedActionEncoder := none) : TermElabM DataOwnership.Data := do
  unless parameters.size == plan.components.size do
    throwError "the prescribed lift lost its complete selected evidence parameters"
  let .ok _ := LiftedSubobjectData.subobjectFields base.json
    | throwStratum .malformed "the lift base omitted its complete apex, ambient and inclusion"
  let state ← registryState
  let mut sources : Array DataOwnership.Data := #[]
  let mut actions : Array DataOwnership.Data := #[]
  let mut actionDependencies : Array (Array Wire) := #[]
  let mut currentSource := source.fragment
  for component in plan.components do
    let some row := state.lifts.find? (·.id == component.lift)
      | throwError "the fixed lift plan lost its registered row"
    let .constructMap _ inner := row.edge
      | throwError "the fixed lift plan lost its selected inner action"
    let (action, dependencies) ← encodeAction trace encoder? inner component.action
    sources := sources.push currentSource
    actions := actions.push action
    actionDependencies := actionDependencies.push dependencies
    let .ok next := LiftedSubobjectData.mapArrowData action.json currentSource.json
      | throwStratum .malformed "the prescribed lift source omitted complete Arrow fields"
    let left ← checkedFragment (currentSource.project #[.field "args", .index 0])
    let right ← checkedFragment (currentSource.project #[.field "args", .index 1])
    let arrow ← checkedFragment (currentSource.project #[.field "args", .index 2])
    currentSource ← scopedNode "arrow" #[
      ← scopedNode "functorAction" #[action, left],
      ← scopedNode "functorAction" #[action, right],
      ← scopedNode "map" #[action, arrow]]
    unless currentSource.json == next do
      throwError "the scoped source transport changed its public Arrow encoding"
  let mut currentBase := base.fragment
  let mut steps := Array.replicate plan.components.size ({ json := Json.null } : DataOwnership.Data)
  for index in (List.range plan.components.size).reverse do
    let some component := plan.components[index]?
      | throwError "the fixed route lost a required computation component"
    let some row := state.lifts.find? (·.id == component.lift)
      | throwError "the fixed lift plan lost its public computation row"
    let some form := state.liftInputForm? row.inputAddress
      | throwError "the public lift request has no unique registered source context"
    let parameterData := DataOwnership.Data.array parameters[index]!.1
    let (sourceView, baseView) ← prescribedLiftViews component source base sources[index]! currentBase
    let sourceView := if index == 0 then source else sourceView
    let baseView := if index + 1 == plan.components.size then base else baseView
    let some (baseObjectFormal, _) := Language.homEnds? (← inferType component.selection.inclusion)
      | throwError "the selected lift lost its complete base inclusion type"
    let sourceObject ← liftOperand component.selection.source
      (← SelectedLift.context component.selection) form
      (← checkedFragment (sources[index]!.project #[.field "args", .index 0]))
    let baseObject ← liftOperand baseObjectFormal (← SelectedLift.context component.selection true) form
      (← checkedFragment (currentBase.project #[.field "args", .index 0]))
    let stage : LiftStageExecution.Input Wire := {
      selection := component.selection, originalArrow := true,
      action := actions[index]!, parameters := parameterData,
      original := sourceView, source := sourceObject, base := baseView, baseObject }
    let dependencies := #[source, base, sourceView, baseView] ++ parameters[index]!.2 ++
      (actionDependencies.extract 0 (index + 1)).flatMap id
    let result ← LiftStageExecution.fold Wire.fragment stage
      (fun object => do
        let formal ← Semantic.objOf component.action object.value
        let context ← SelectedLift.context component.selection true
        let data ← scopedNode "functorAction" #[actions[index]!, object.fragment]
        return some {
          form := contextualForm state context form,
          payload := (← combinedRecipePayload formal data (#[object] ++ dependencies)),
          categoryContext := some context })
      (observeLiftStageField h stage component.receiver form dependencies)
      liftStageEndpoints
    steps := steps.set! index result.step
    let .ok next := LiftedSubobjectData.nextBase sources[index]!.json (result.outputs.map (·.json))
      | throwError "the completed lift omitted its actual next object or inclusion"
    let some inclusion := result.outputs[1]?
      | throwError "the completed lift omitted its actual inclusion output"
    currentBase ← retagLiftMap "subobject" inclusion.fragment
    unless currentBase.json == next do
      throwError "the scoped next base changed its complete original defining map"
  scopedNode "liftedSubobject" #[base.fragment, source.fragment,
    { json := toJson (plan.components.map (·.lift.raw)) }, DataOwnership.Data.array steps]

/-- Validate computational object fields without proving construction laws. In particular,
subobject data carries its inclusion at the declared endpoints but is not promoted to a Lean
`Mono` instance or identified with the formal construction. -/
partial def validateComputationalObject (_trace : Trace) (_category : NamedCategoryEntry)
    (fixed : Expr) (json : Json) : TermElabM (Except String Unit) := do
  ComputationalData.validatePort fixed (← inferType fixed) json

/-- The registered constructor selects the computational apex by its original
binder role. Returned bytes and coincident formal fields do not choose a port. -/
def constructionApexFragment (plan : StructuredResult.DataPlan)
    (answer : DataOwnership.Data) (external : Nat → Option DataOwnership.Data) :
    TermElabM (Option DataOwnership.Data) := do
  let some binder := plan.apexBinder | return none
  let some binding := plan.binders[binder]? | return none
  match binding.port with
  | none => pure (external binder)
  | some index =>
    let .ok (tag, fields) := ComputationalData.envelope answer.json | return none
    unless tag == (if plan.colimit then "cocone" else "cone") &&
        fields.size == plan.ports.size do return none
    let some port := plan.ports[index]? | return none
    unless port.index == index && port.constructorBinder == binder do return none
    return some (← checkedFragment (answer.project #[.field "args", .index index]))

/-- A completed construction supplies its authoritative presentation. A legacy
computed descriptor must retain the whole formal projection syntactically;
equality with an arbitrary object or historical capture is not an origin. -/
def retainedApexPresentation? (input : Wire) (row : LimitEntry) : TermElabM (Option Expr) := do
  let presentation ← match input.payload with
    | .construction result _ => pure result.presentation
    | _ =>
      let apex ← withTransparency .all <| whnfHeadPred input.value fun value =>
        pure (!(value.isAppOf ``CategoryTheory.Limits.Cone.pt ||
          value.isAppOf ``CategoryTheory.Limits.Cocone.pt))
      let point := if row.colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt
      unless apex.isAppOf point do return none
      let cone := apex.getAppArgs.back!
      let projection := if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone
      unless cone.isAppOf projection do return none
      pure cone.getAppArgs.back!
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType apex) (← inferType input.value) <&&>
        isDefEq apex input.value) do return none
  return some presentation

/-- Project a direct construction through its independently selected schema.
Private inspection supplies its already authenticated canonical selection
explicitly. Actual data use the complete Result or the public formal interface;
copied historical capture never chooses a presentation. This is a receiver
field view: the caller retains the original complete parent occurrence.

A created source object is deliberately not projected here. Its lower field
has a target-category type, and a formal creation comparison does not by itself
supply an executable comparison action or authorize relabeling those bytes. -/
def computationalApexImage? (_trace : Trace) (input : Wire)
    (outerObjects : ComputationalData.InterfaceObjects := #[])
    (selection : Option SelectedStructuredInvocation := none) : TermElabM (Option Wire) := do
  let state ← registryState
  let row ← match selection with
    | some selected =>
      if selected.creation.isSome then return none
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType selected.formal) (← inferType input.value) <&&>
            isDefEq selected.formal input.value) do return none
      discard <| framingContext (some selected.context) input.categoryContext
      pure selected.row
    | none =>
      unless input.actualData || input.objectObserved do return none
      match input.form with
      | .limitApex row => pure row
      | _ => return none
  let some row := state.limits.find? (·.id == row.id) | return none
  let .ok ("constructionApex", #[identifier, _, _]) := ComputationalData.envelope input.json
    | return none
  unless identifier == toJson row.id.raw do return none
  if let .construction result _ := input.payload then
    if let .created .. := result.packet then return none
  let diagramData ← checkedFragment (input.fragment.project #[.field "args", .index 1])
  let answer ← checkedFragment (input.fragment.project #[.field "args", .index 2])
  if let .ok ("createdCone", _) := ComputationalData.envelope answer.json then return none
  if let some (receiver, _) := input.constructionInputs then
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType receiver) (← inferType input.value) <&&>
          isDefEq receiver input.value) do return none
  let retained := input.constructionInputs.map Prod.snd |>.getD #[]
  let objects := retained ++ outerObjects.filter (fun (data, _) =>
    !retained.any (·.1 == data))
  let (diagram, presentation, plan) ← match selection with
    | some selected =>
      pure (selected.targetDiagram, selected.encodingPresentation, selected.plan)
    | none =>
      let some presentation ← retainedApexPresentation? input row | return none
      let diagram := (← whnfR (← inferType presentation)).getAppArgs.back!
      let .ok plan ← StructuredResult.dataPlan row diagram presentation | return none
      pure (diagram, presentation, plan)
  let .ok (_, inputs) ← ComputationalData.interfaceDiagram objects row (← inferType diagram)
      diagramData.json (some diagram) | return none
  let context : ComputationalData.ConstructionInterface := {
    row, diagram, presentation, dataDiagram := diagram, dataPresentation := presentation,
    inputs, dataInputs := inputs, answer := some answer.json }
  if let .error _ ← ComputationalData.validateConstructionData objects context then return none
  let readRole := fun (role : StructuredResult.InputRole) => do
    let (position, source) := match role with
      | .argument position => (position, none)
      | .source position => (position, some true)
      | .target position => (position, some false)
    let some (_, formal) := inputs[position]? | return none
    let data ← checkedFragment (diagramData.project #[.field "args", .index position])
    match source with
    | none => pure (some data)
    | some source =>
      match ← ComputationalData.interfaceEndpointData objects formal data source false with
      | .ok endpoint => pure (some endpoint)
      | .error _ => pure none
  let mut bindings : Array (Nat × DataOwnership.Data) := #[]
  for binding in plan.binders do
    if binding.port.isSome then continue
    let some role := binding.inputRoles[0]? | continue
    let some first ← readRole role | continue
    let mut agrees := true
    for role in binding.inputRoles do
      unless (← readRole role) == some first do agrees := false
    if agrees then bindings := bindings.push (binding.index, first)
  let external := fun binder => (bindings.find? (·.1 == binder)).map (·.2)
  let some apex ← constructionApexFragment plan answer external | return none
  let some category := state.categories.find? (·.id == row.category) | return none
  let selectedContext := selection.map (·.context)
  let context ← framingContext selectedContext input.categoryContext
  let context ← match context with
    | some context => pure context
    | none => CategoryContext.ofNamed category input.value
  unless context.expression.syntacticEq category.expression do return none
  CategoryContext.checkObject context input.value
  if let .error _ ← ComputationalData.validatePort input.value (← inferType input.value)
      apex.json objects then return none
  let mut descriptor := apex.json
  if let .ok ("finiteData", #[actual, _]) := ComputationalData.envelope descriptor then
    descriptor := actual
  let named := state.objects.find? fun entry =>
    (descriptor.getObjValAs? String "ctor").toOption == some entry.id.raw
  if let some entry := named then
    unless entry.category == row.category do return none
  let form := named.map Form.object |>.getD (.diagrams category)
  let completed := input.actualData || input.objectObserved
  let payload ← if completed then scopedPayload input.value apex else recipePayload input.value apex
  -- No whole-parent capture, action, intrinsic tree, or endpoint presentation
  -- is copied onto a different field packet. Its exact full parent remains in
  -- the caller's canonical operand graph and is never replaced in that graph.
  return some {
    form, payload, categoryContext := some context, objectObserved := completed,
    constructionInputs := input.constructionInputs,
    constructionInputOwnership := input.constructionInputOwnership,
    serviceHandles := input.serviceHandles }

/-- Ordinary and prospective consumers request the same direct apex view.
Complete creation interfaces and unsupported schema projections remain intact. -/
def computationalApexReceiver (trace : Trace) (input : Wire)
    (objects : ComputationalData.InterfaceObjects := #[])
    (selection : Option SelectedStructuredInvocation := none) : TermElabM Wire := do
  return (← computationalApexImage? trace input objects selection).getD input

/-- The no-dispatch record projections of an accepted edge. Actual execution
and prospective ownership inspection use the same checked schema. A creation
comparison alone does not supply an executable action on its lower packet. -/
def intrinsicObjectEdgeData? (trace : Trace) (edge : EdgeRef) (action : Expr)
    (original : Wire) (_imageValue : Expr) (descriptor : DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Option DataOwnership.Data) := do
  let state ← registryState
  let some source := state.selectedEdgeSource? edge
    | throwError "the intrinsic object action lost its registered source"
  if let some (.structural projected) ← projectObjectFragmentWithOrigin trace source edge action
      original.value original.fragment (some descriptor) true objects then
    return some projected
  return none

/-- The power object, ambient set and subset of `e` when `e` is the extent of a subset, the
set `po.extent X A` that `Language.asObject` forms. -/
def extentOf? (state : RegistryState) (e : Expr) :
    TermElabM (Option (PowerObjectEntry × Expr × Expr)) := do
  let e := Trace.unanchor e.consumeMData
  let some po ← Language.selectedPowerObject? state (e.isAppOf ·.extent)
      m!"the selected extent declaration {e.getAppFn}"
    | return none
  let #[X, A] := e.getAppArgs | return none
  return some (po, X, A)

/-- Remove only the reader's administrative expected-type wrappers. The original
categorical composition and its complete selected argument remain unchanged. -/
def operationApplicationBody (value : Expr) : Expr := Id.run do
  return ComputationDerivation.applicationBody value

/-- Retain the original generalized argument of a staged operation, including
terminal comparisons. Only categorical composition and administrative wrappers
are inspected; no mathematical function body or computed result is unfolded. -/
partial def operationApplicationSpine (value : Expr) : Array Expr × Expr :=
  ComputationDerivation.applicationSpine value

structure CallableEndpointData where
  wire : Wire
  origin : CallableEndpointOrigin

/-- The public endpoint-reference constructor is an intrinsic projection of
this exact complete callable occurrence. Its producer records the role, so a
later owner substitution never discovers it by inspecting returned bytes. -/
def callableEndpointReference (wire : Wire) (value : Expr) (source : Bool)
    (context : Option CategoryContext := none) : TermElabM Wire := do
  let context ← framingContext context wire.categoryContext
  if let some context := context then CategoryContext.checkObject context value
  let state ← registryState
  let form ← match context with
    | some context => pure (contextualForm state context wire.form)
    | none =>
      let some category := state.categories.find? (·.id == wire.form.category)
        | throwError "the callable endpoint lost its complete registered category"
      pure (.diagrams category)
  let data := Backend.MorphismEndpoint.encode { callable := wire.json, source }
  return {
    form
    payload := forwardPayload wire value data #[(#[], #[.field "args", .index 0])]
    categoryContext := context }

/-- Read only a producer-owned endpoint interface. A retained frame and an
actual point have explicit original fields; no expression lookup or action is
needed to recover them. Current metadata takes priority over historical plans. -/
def retainedCallableEndpoint? (wire : Wire) (formal : Expr) (source : Bool)
    (context : Option CategoryContext := none) : TermElabM (Option Wire) := do
  let context ← framingContext context wire.categoryContext
  let check := fun (endpoint : Wire) => do
    discard <| framingContext context endpoint.categoryContext
    forwardRetainedValue endpoint formal
  if let some context := context then
    if let some endpoints ← retainedCallableEndpoints? wire context then
      return some (← check (if source then endpoints.1 else endpoints.2))
  if let some framing := wire.morphismFraming then
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context framing.comparisons
    unless sameCompleteWireContext replayed wire do
      throwStratum .unavailable "the callable endpoint lost its exact framing producer"
    return some (← check (if source then framing.source else framing.target))
  if let some selected := wire.pointDataInterface then
    let endpoint := if source then selected.domain else selected.target
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType endpoint) (← inferType formal) <&&> isDefEq endpoint formal) do
      throwError "the retained point changed its independently selected endpoint"
    let state ← registryState
    let form ← match context with
      | some context => pure (contextualForm state context wire.form)
      | none =>
        let some category := state.categories.find? (·.id == wire.form.category)
          | throwError "the point endpoint lost its complete registered category"
        pure (.diagrams category)
    let data := if source then selected.domainData else selected.targetData
    -- A point interface fixes an endpoint role even while its computation is
    -- pending. Only independently completed point data makes this projection
    -- actual; producer-owned complete endpoint Wires above retain priority.
    let completed := wire.actualData || wire.callableObserved
    return some {
      form, payload := (← scopedPayload formal data completed), categoryContext := context,
      objectObserved := completed }
  return none

/-- The declaration, applied to a fresh owner at the original complete type,
determines whether its endpoints are exposed fields of that owner's record.
Actual equal carriers cannot choose a projection. Other representations keep
the ordinary complete callable endpoint interface. -/
def operationRecordEndpointData (entry : OperationEntry) (application : Expr)
    (receiver : Wire) (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Option DataOwnership.Data × Option DataOwnership.Data) := do
  let application := operationApplicationBody application
  let arguments := application.getAppArgs
  let index := arguments.size - 1 - entry.numerals
  let some original := arguments[index]? | return (none, none)
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType original) (← inferType receiver.value) <&&>
        isDefEq original receiver.value) do
    throwError "the operation endpoint changed its complete declared record owner"
  discard <| checkedFragment receiver.fragment.validate
  let some exposed ← exposedRecordData? original receiver.fragment objects | return (none, none)
  withLocalDeclD `recordOwner (← inferType original) fun symbolic => do
    let selected := mkAppN application.getAppFn (arguments.set! index symbolic)
    unless ← isTypeCorrect selected do return (none, none)
    let some (source, target) := Language.homEnds? (← inferType selected)
      | return (none, none)
    return (← ComputationalData.recordEndpointData? symbolic source exposed objects (some original),
      ← ComputationalData.recordEndpointData? symbolic target exposed objects (some original))

/-- Endpoint roles are identified on the declaration's fresh complete owner.
The paths contain field declarations, not instantiated carriers or reply data. -/
inductive OperationEndpointRole where
  | field (path : ComputationalData.RecordFieldPath)
  | product (left right : OperationEndpointRole)

partial def operationEndpointRole? (owner endpoint : Expr) :
    TermElabM (Option OperationEndpointRole) := do
  if let some path ← ComputationalData.recordFieldPath? owner endpoint then
    return some (.field path)
  let endpoint ← withTransparency .all <| whnf endpoint
  unless endpoint.isAppOfArity ``Prod 2 do return none
  let fields := endpoint.getAppArgs
  let some left ← operationEndpointRole? owner fields[0]! | return none
  let some right ← operationEndpointRole? owner fields[1]! | return none
  return some (.product left right)

/-- The pending operation may retain an input presentation for an output field
only through this exact declaration-relative role. Unsupported signatures keep
their existing representation path; no equality of actual fields selects a role. -/
def operationPointRoles? (entry : OperationEntry) (application : Expr) (receiver : Wire) :
    TermElabM (Option (OperationEndpointRole × ComputationalData.RecordFieldPath)) := do
  let application := operationApplicationBody application
  let arguments := application.getAppArgs
  let index := arguments.size - 1 - entry.numerals
  let some original := arguments[index]? | return none
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType original) (← inferType receiver.value) <&&>
        isDefEq original receiver.value) do
    throwError "the point presentation changed its complete operation owner"
  withLocalDeclD `recordOwner (← inferType original) fun symbolic => do
    let selected := mkAppN application.getAppFn (arguments.set! index symbolic)
    unless ← isTypeCorrect selected do return none
    let some (source, target) := Language.homEnds? (← inferType selected) | return none
    let some source ← operationEndpointRole? symbolic source | return none
    let some target ← ComputationalData.recordFieldPath? symbolic target | return none
    return some (source, target)

def sameOperationFieldPath (left right : ComputationalData.RecordFieldPath) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) =>
    a.structureName == b.structureName && a.field == b.field &&
      a.index == b.index && a.count == b.count && a.codec == b.codec

/-- The positions in a public record are declaration positions. Equal closed
fields never merge their role, supplier, or presentation metadata. -/
structure PublicRecordField where
  step : ComputationalData.RecordFieldStep
  formal : Expr
  result : IntrinsicResultInterface

def instantiateRecordInterface (result : IntrinsicResultInterface)
    (symbolic actual : Expr) : IntrinsicResultInterface :=
  match result with
  | .object context => .object {
      context with bundle := context.bundle.replaceFVars #[symbolic] #[actual] }
  | .map context => .map {
      context with bundle := context.bundle.replaceFVars #[symbolic] #[actual] }
  | .value expected => .value (expected.replaceFVars #[symbolic] #[actual])

/-- Recover a constructor's complete original category from its accepted
application, rather than choosing a category instance from a field carrier. -/
def recordCoreContext (context : CategoryContext) : TermElabM CategoryContext := do
  let .construct constructor #[.category expression] := context.expression
    | throwStratum .noImplementation "the Core field lacks its complete constructor context"
  let some row := (← registryState).constructor? constructor
    | throwError "the Core record names an absent accepted constructor"
  unless row.semantics == `CasCatalogue.Constructors.core do
    throwStratum .noImplementation "the selected record is not the accepted Core interface"
  let some (_, #[bundle]) ← DeclaredApplication.complete? row.semantics context.bundle
    | throwStratum .noImplementation "the Core field lost its complete original category parameter"
  return { expression, bundle }

private partial def publicScalarRecordSchema : ComputationalData.PointSchema → Bool
  | .literal _ shape | .constrainedData shape => publicScalarRecordSchema shape
  | .recordFields .. => true
  | _ => false

/-- Select record children on a fresh output variable. A scalar Hom remains a
value, and an ordinary opaque object does not expose Lean implementation fields. -/
@[no_expose] def publicRecordFields (formal : Expr) (result : IntrinsicResultInterface) :
    TermElabM (ComputationalData.RecordFieldCodec × Array PublicRecordField) := do
  withLocalDeclD `recordShape (← inferType formal) fun symbolic => do
    let codec ← ComputationalData.recordFieldCodec symbolic
    let fields : Array (Expr × IntrinsicResultInterface) ← match result with
      | .object context => do
        CategoryContext.checkObject context symbolic
        if let some arrow ← StructuredProjection.arrow? symbolic context then
          if arrow.subobject then
            pure #[(arrow.arrow, .object arrow.arrowContext)]
          else pure #[(arrow.source, .object arrow.base), (arrow.target, .object arrow.base),
            (arrow.hom, .map arrow.base)]
        else if codec == .core then
          let some underlying ← ComputationalData.recordProjection ``CategoryTheory.Core.of symbolic
            | throwError "the accepted Core record omitted its public object field"
          pure #[(underlying, .object (← recordCoreContext context))]
        else throwStratum .noImplementation "the selected object has no public record-field interface"
      | .map _ =>
        throwStratum .noImplementation "a complete callable has no independently represented record fields"
      | .value expected => do
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType formal) expected) do
          throwError "the selected scalar record changed its complete result type"
        let some schema ← ComputationalData.pointSchema expected
          | throwStratum .noImplementation "the scalar record has no declared public codec"
        unless publicScalarRecordSchema schema do
          throwStratum .noImplementation "the selected scalar codec has no public record-field positions"
        let type ← withTransparency .all <| whnf (← inferType symbolic)
        let some name := type.getAppFn.constName?
          | throwError "the selected scalar record lost its structure declaration"
        let some info := getStructureInfo? (← getEnv) name
          | throwError "the selected scalar codec lost its declared record fields"
        let mut fields := #[]
        for name in info.fieldNames do
          let field ← withTransparency .all <| mkProjection symbolic name
          unless ← isProp (← inferType field) do
            fields := fields.push (field, .value (← inferType field))
        pure fields
    let mut selected := #[]
    for (field, interface) in fields do
      let some #[step] ← ComputationalData.recordFieldPath? symbolic field
        | throwError "a public record field lost its direct declaration position"
      unless step.codec == codec do
        throwError "the public record changed its independently selected codec"
      selected := selected.push {
        step, formal := field.replaceFVars #[symbolic] #[formal],
        result := instantiateRecordInterface interface symbolic formal }
    return (codec, selected)

/-- The original typed Wire, not its bytes, fixes the top public result role. -/
def retainedRecordInterface (wire : Wire) : TermElabM IntrinsicResultInterface := do
  if let some assembly ← currentIntrinsicAssembly? wire then return assembly.result
  if let some captured ← retainedCapturedInvocation? wire then return captured.interface.result
  if let some context := wire.categoryContext then
    if let some (source, target) ← retainedCallableEndpoints? wire context then
      CategoryContext.checkMorphism context wire.value source.value target.value
      return .map context
    CategoryContext.checkObject context wire.value
    return .object context
  return .value (← inferType wire.value)

structure PublicRecordSelection where
  formal : Expr
  result : IntrinsicResultInterface
  endpoints : Option (ComputationalData.RecordFieldPath × ComputationalData.RecordFieldPath) := none

/-- Validate each selected path against the public declaration, keeping map
endpoint positions even when their instantiated formal values coincide. -/
def selectPublicRecordField (original : Wire) (path : ComputationalData.RecordFieldPath) :
    TermElabM PublicRecordSelection := do
  let mut formal := original.value
  let mut result ← retainedRecordInterface original
  let mut prefixPath := #[]
  let mut endpoints := none
  for step in path do
    let (codec, fields) ← publicRecordFields formal result
    let some field := fields.find? fun field =>
        sameOperationFieldPath #[field.step] #[step]
      | throwStratum .invalid "the selected field is outside the original public record schema"
    endpoints := none
    if let .map _ := field.result then
      unless codec == .arrow do
        throwError "the selected map field has no declared record endpoint positions"
      let some source := fields[0]?
        | throwError "the public Arrow omitted its source field position"
      let some target := fields[1]?
        | throwError "the public Arrow omitted its target field position"
      endpoints := some (prefixPath.push source.step, prefixPath.push target.step)
    formal := field.formal
    result := field.result
    prefixPath := prefixPath.push step
  return { formal, result, endpoints }

/-- An exact input occurrence and declared field path are the only lookup keys.
Both execution and private admission supply this same field-reader interface. -/
structure RetainedRecordReader where
  readField : Wire → ComputationalData.RecordFieldPath → TermElabM Wire

/-- Preserve the exact public envelope, optional fields, and their suppliers.
Only the codec's independently declared argument slots receive typed children. -/
partial def retainedRecordPacketTemplate (codec : ComputationalData.RecordFieldCodec)
    (packet : DataOwnership.Data) (children : Array ActionDataTemplate) :
    TermElabM ActionDataTemplate := do
  if let .ok ("valueData", #[_]) := ComputationalData.envelope packet.json then
    let inner ← checkedFragment (packet.project #[.field "args", .index 0])
    let inner ← retainedRecordPacketTemplate codec inner children
    let .obj fields := packet.json
      | throwError "the transparent record envelope lost its object fields"
    let mut result := #[]
    for (key, _) in fields.toList do
      let selected ← if key == "args" then pure (ActionDataTemplate.array #[inner])
        else pure (.literal (← checkedFragment (packet.project #[.field key])))
      result := result.push (key, selected)
    return .object result
  if codec == .ordered then
    if let #[child] := children then return child
    let .arr fields := packet.json
      | throwStratum .malformed "the ordered record omitted its complete field array"
    unless fields.size == children.size do
      throwStratum .malformed "the ordered record changed its declared field count"
    return .array children
  let .obj fields := packet.json
    | throwStratum .malformed "the public record omitted its declared envelope"
  let .ok (tag, values) := ComputationalData.envelope packet.json
    | throwStratum .malformed "the public record has no complete constructor envelope"
  let arguments ← match codec with
    | .core =>
      unless tag == "coreObject" && children.size == 1 && values.size == 1 do
        throwStratum .malformed "the Core record changed its declared object field"
      pure (ActionDataTemplate.array children)
    | .arrow =>
      unless tag == "arrow" && children.size == 3 && values.size == 3 do
        throwStratum .malformed "the Arrow record changed its complete field layout"
      pure (ActionDataTemplate.array children)
    | .arrowRefinement =>
      unless (tag == "arrow" || tag == "subobject") && children.size == 1 && values.size == 3 do
        throwStratum .malformed "the Arrow refinement changed its complete underlying fields"
      let some child := children[0]?
        | throwError "the Arrow refinement omitted its typed child"
      pure (.project #[.field "args"] child)
    | .ordered => throwError "an ordered record acquired an unrelated constructor envelope"
  let mut result := #[]
  for (key, _) in fields.toList do
    let selected ← if key == "args" then pure arguments
      else pure (.literal (← checkedFragment (packet.project #[.field key])))
    result := result.push (key, selected)
  return .object result

/-- Assemble the existing public codec from complete typed fields. This operation
does not frame a map again; its retained receipt must already own these endpoints. -/
def assembleRetainedRecordWith (codec : ComputationalData.RecordFieldCodec)
    (fields : Array Wire) (formal : Expr) (result : IntrinsicResultInterface)
    (form : Form) (packet : Option DataOwnership.Data := none) : TermElabM Wire := do
  let (selectedCodec, selected) ← publicRecordFields formal result
  unless codec == selectedCodec && fields.size == selected.size do
    throwError "the retained record assembly changed its declared codec or field count"
  let mut actual := #[]
  for (field, selected) in fields.zip selected do
    let field ← forwardRetainedValue field selected.formal
    checkCapturedResultInterface field selected.result
    actual := actual.push field
  let mut maps : Array IntrinsicMapFields := #[]
  if codec == .arrow && result.role == .object then
    let #[source, target, callable] := actual
      | throwError "the retained Arrow assembly lost one of its complete fields"
    let some hom := selected[2]?
      | throwError "the retained Arrow omitted its declared hom position"
    let .map context := hom.result
      | throwError "the retained Arrow hom lost its declared complete map role"
    let some (actualSource, actualTarget) ← retainedCallableEndpoints? callable context
      | throwStratum .noImplementation "the retained Arrow hom omitted its complete endpoint occurrences"
    let actualSource ← forwardRetainedValue actualSource source.value
    let actualTarget ← forwardRetainedValue actualTarget target.value
    unless sameCompleteWireContext source actualSource &&
        sameCompleteWireContext target actualTarget do
      throwStratum .malformed "the retained Arrow hom changed a complete endpoint occurrence or presentation"
    maps := #[{ context, source, target, callable }]
  let children := (actual.zip selected).map fun (field, selected) =>
    ActionDataTemplate.wire selected.result.role field
  let canonical : ActionDataTemplate ← match codec with
    | .ordered =>
      if let #[field] := actual then pure (.wire .parameter field)
      else pure (.array (actual.map (.wire .parameter)))
    | .core => pure (.ctor "coreObject" children)
    | .arrow => pure (.ctor "arrow" children)
    | .arrowRefinement =>
      let #[field] := children
        | throwError "the Arrow refinement lost its exact underlying record"
      pure field
  let (data, template) ← match packet with
    | none =>
      let some data := codec.assemble? (actual.map (·.fragment))
        | throwError "the retained record fields disagree with their selected public codec"
      pure (data, canonical)
    | some packet =>
      for (field, selected) in actual.zip selected do
        let projection := ComputationalData.RecordProjectionPlan.input #[selected.step]
        let some original ← projection.projectData? formal packet
          | throwStratum .malformed "the returned record omitted a declared field position"
        unless original == field.fragment do
          throwStratum .malformed "the returned record changed a retained field or its supplier"
      pure (packet, ← retainedRecordPacketTemplate codec packet children)
  let (rendered, _) ← renderCapturedActionData template
  unless rendered == data do
    throwError "the typed record assembly changed its positioned data or suppliers"
  let wire : Wire := {
    form, payload := (← combinedPayload formal data actual), categoryContext := result.context?,
    serviceHandles := actual.flatMap (·.serviceHandles) }
  retainIntrinsicResultAssembly wire result template maps

/-- A prescribed run keeps every selected stage's typed inputs and four outputs.
The shared fold may contain private future values; only the actual observer
turns its scoped packet into a completed result and a `LiftExecution`. -/
structure PrescribedLiftData where
  result : Wire
  packet : DataOwnership.Data
  stages : Array (LiftStageExecution.Input Wire × LiftStageExecution.Result Wire)
  dependencies : Array Wire

/-- Read the ordinary complete Arrow fields through their producer positions.
The full-subcategory wrapper contributes its one declared underlying Arrow field. -/
def liftArrowFieldsWith (reader : RetainedRecordReader) (original : Wire) :
    TermElabM (Array Wire) := do
  let some context := original.categoryContext
    | throwError "the selected lift operand lost its complete record context"
  let (codec, fields) ← publicRecordFields original.value (.object context)
  let arrow ← if codec == .arrowRefinement then do
      let #[field] := fields
        | throwError "the selected lift base lost its complete underlying Arrow"
      reader.readField original #[field.step]
    else pure original
  let some context := arrow.categoryContext
    | throwError "the selected lift Arrow lost its complete category context"
  let (codec, fields) ← publicRecordFields arrow.value (.object context)
  unless codec == .arrow && fields.size == 3 do
    throwError "the selected lift requires its three declared Arrow fields"
  fields.mapM fun field => reader.readField arrow #[field.step]

/-- A typed inclusion supplies the next complete subobject. Its actual endpoint
occurrences, including permitted inventory enrichment, determine the data fields;
the independently fixed result supplies all formal meaning and its predicate. -/
def assembleLiftSubobject (formal : Expr) (context : CategoryContext) (origin : Form)
    (inclusion : Wire) : TermElabM Wire := do
  let some selected ← StructuredProjection.arrow? formal context
    | throwError "the selected lift result lost its complete Arrow interface"
  unless selected.subobject do
    throwError "the selected lift result changed its accepted subobject constructor"
  let some (source, target) ← retainedCallableEndpoints? inclusion selected.base
    | throwError "the selected lift inclusion lost its actual endpoint occurrences"
  let body ← checkedFragment (inclusion.fragment.project #[.field "args", .index 2])
  let callable : Wire := {
    form := inclusion.form, payload := (← combinedPayload selected.hom body #[inclusion]),
    categoryContext := some selected.base, callableObserved := inclusion.callableObserved,
    morphismFramed := inclusion.morphismFramed,
    serviceHandles := inclusion.serviceHandles }
  let callable ← retainCallableEndpoints callable source target selected.base
  let state ← registryState
  let arrow ← assembleRetainedRecordWith .arrow #[source, target, callable]
    selected.arrow (.object selected.arrowContext)
    (contextualForm state selected.arrowContext origin)
  let packet ← retagLiftMap "subobject" inclusion.fragment
  assembleRetainedRecordWith .arrowRefinement #[arrow] formal (.object context)
    (contextualForm state context origin) (some packet)

/-- Complete retained source/image occurrences are supplied by the chosen
method boundary or its exposed producer fields. This fold never independently
executes captured route recipes to guess a fused implementation's intermediates. -/
def executePrescribedRetainedWith (reader : RetainedRecordReader)
    (plan : LiftedSubobjectData.Plan) (original base : Wire)
    (sources images : Array Wire)
    (parameters : Array (Array DataOwnership.Data × Array Wire))
    (actions : Array (DataOwnership.Data × Array Wire))
    (image : Nat → Wire → TermElabM (Option Wire))
    (returned : Nat → LiftStageExecution.Input Wire → Array Wire →
      LiftStageExecution.Field Wire → TermElabM Wire) : TermElabM PrescribedLiftData := do
  let count := plan.components.size
  unless count > 0 && sources.size == count && images.size == count && parameters.size == count &&
      actions.size == count do
    throwError "the prescribed lift lost a retained stage input position"
  let mut currentBase := base
  let mut reverseStages := #[]
  let mut dependencies := #[original, base] ++ sources ++ images ++
    parameters.flatMap (·.2) ++ actions.flatMap (·.2)
  for index in (List.range count).reverse do
    let some component := plan.components[index]?
      | throwError "the prescribed lift lost a selected stage"
    let some source := sources[index]?
      | throwError "the prescribed lift lost its actual source occurrence"
    let some sourceImage := images[index]?
      | throwError "the prescribed lift lost its actual source image occurrence"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq source.value component.receiver <&&>
          isDefEq (← inferType source.value) (← inferType component.receiver) <&&>
          isDefEq sourceImage.value component.transportedSource <&&>
          isDefEq (← inferType sourceImage.value) (← inferType component.transportedSource) <&&>
          isDefEq currentBase.value component.base) do
      throwError "the prescribed stage changed a complete retained formal interface"
    let #[sourceObject, _, _] ← liftArrowFieldsWith reader source
      | throwError "the prescribed source lost its complete original Arrow fields"
    let #[baseObject, _, _] ← liftArrowFieldsWith reader currentBase
      | throwError "the prescribed base lost its complete original subobject fields"
    let #[sourceImageObject, _, _] ← liftArrowFieldsWith reader sourceImage
      | throwError "the prescribed image lost its complete transported Arrow fields"
    let stage : LiftStageExecution.Input Wire := {
      selection := component.selection, originalArrow := true,
      action := actions[index]!.1, parameters := DataOwnership.Data.array parameters[index]!.1,
      original := source, source := sourceObject, base := currentBase, baseObject,
      sourceImage? := some sourceImage, sourceImageObject? := some sourceImageObject }
    let result ← LiftStageExecution.fold Wire.fragment stage (image index)
      (returned index stage dependencies) liftStageEndpoints
    reverseStages := reverseStages.push (stage, result)
    dependencies := dependencies ++ result.outputs ++ #[result.comparisonImage]
    let some inclusion := result.outputs[1]?
      | throwError "the completed stage lost its selected inclusion"
    let formal ← if index == 0 then pure plan.formalResult else do
      let some next := plan.components[index - 1]?
        | throwError "the reverse route lost its next independently fixed base"
      pure next.base
    let #[subobjects] := (← registryState).constructors.filter
        (·.semantics == `CasCatalogue.Constructors.subobjects)
      | throwError "the selected lift lost its unique accepted subobject constructor"
    let context ← CategoryContext.construct (← SelectedLift.context component.selection) subobjects.id
    currentBase ← assembleLiftSubobject formal context original.form inclusion
    dependencies := dependencies.push currentBase
  let stages := reverseStages.reverse
  let packet ← scopedNode "liftedSubobject" #[base.fragment, original.fragment,
    { json := toJson (plan.components.map (·.lift.raw)) },
    DataOwnership.Data.array (stages.map (·.2.step))]
  return { result := currentBase, packet, stages, dependencies }

/-- Project original input occurrences or assemble another public record from
them. This fold never drops the field Wires to a data-only intermediate table. -/
partial def projectRetainedRecordWith (reader : RetainedRecordReader) (original : Wire)
    (projection : ComputationalData.RecordProjectionPlan) (formal : Expr)
    (result : IntrinsicResultInterface) (form : Form) : TermElabM Wire := do
  match projection with
  | .input path =>
    let selected ← reader.readField original path
    let selected ← forwardRetainedValue selected formal
    checkCapturedResultInterface selected result
    return selected
  | .record codec projections =>
    let (selectedCodec, fields) ← publicRecordFields formal result
    unless codec == selectedCodec && projections.size == fields.size do
      throwError "the retained projection changed its complete output-record schema"
    let state ← registryState
    let mut actual := #[]
    for (projection, field) in projections.zip fields do
      let fieldForm := match field.result with
        | .object context => contextualForm state context form
        | .map context => contextualForm state context form true
        | .value _ => form
      actual := actual.push (← projectRetainedRecordWith reader original projection
        field.formal field.result fieldForm)
    assembleRetainedRecordWith codec actual formal result form

/-- Extract candidate reply slots by the already selected schema shape. Each
returned leaf still needs its ordinary typed validator; retained slots must be
compared to their original occurrences before this table can become a result. -/
def projectRoutedResultShape (plan : RoutedResultPlan.Plan) (reply : DataOwnership.Data) :
    TermElabM (Array DataOwnership.Data) := do
  let mut fields := #[]
  for slot in plan.slots do
    let projection := ComputationalData.RecordProjectionPlan.input slot.replyPath
    let some field ← projection.projectData? plan.formal reply
      | throwStratum .malformed "the routed reply omitted a declared public result-field position"
    fields := fields.push field
  return fields

def recordPathPrefix (prefixPath path : ComputationalData.RecordFieldPath) : Bool :=
  decide (prefixPath.size ≤ path.size) &&
    sameOperationFieldPath prefixPath (path.extract 0 prefixPath.size)

/-- The symbolic slot fixes its complete public result role. -/
def routedSlotInterface (slot : RoutedResultPlan.Slot) : IntrinsicResultInterface :=
  match slot.role with
  | .object context => .object context
  | .map context .. => .map context
  | .value => .value slot.expectedType

def routedSlotForm (state : RegistryState) (fallback : Form)
    (slot : RoutedResultPlan.Slot) : Form :=
  match slot.role with
  | .object context => contextualForm state context fallback
  | .map context .. => contextualForm state context fallback true
  | .value => fallback

/-- A result table is indexed by declaration paths. An exact match returns the
whole stored field; the longest prefix delegates only its remaining subpath to
that exact field, which also supports whole-record retained input slots. -/
def routedSlotPosition? (slots : Array RoutedResultPlan.Slot)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM (Option (Nat × ComputationalData.RecordFieldPath)) := do
  let mut selected : Option (Nat × Nat) := none
  for index in [:slots.size] do
    let some slot := slots[index]?
      | throwError "the retained result schema lost a declared slot"
    if recordPathPrefix slot.replyPath path then
      if let some (_, length) := selected then
        if length == slot.replyPath.size then
          throwError "the result schema repeats one declared public field path"
        if length > slot.replyPath.size then continue
      selected := some (index, slot.replyPath.size)
  let some (index, length) := selected | return none
  return some (index, path.extract length path.size)

def routedResultPosition? (plan : RoutedResultPlan.Plan)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM (Option (Nat × ComputationalData.RecordFieldPath)) :=
  routedSlotPosition? plan.slots path

def RetainedResultFields.project? (fields : RetainedResultFields)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM (Option (Wire × ComputationalData.RecordFieldPath)) := do
  unless fields.values.size == fields.plan.slots.size do
    throwError "the retained result table changed its selected slot count"
  let some (index, remaining) ← routedResultPosition? fields.plan path | return none
  let some field := fields.values[index]?
    | throwError "the retained result table omitted its selected field occurrence"
  let some slot := fields.plan.slots[index]?
    | throwError "the retained result field lost its independently fixed slot"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType field.value) slot.expectedType <&&>
        isDefEq field.value slot.formal) do
    throwError "the retained result field changed its original complete formal selection"
  return some (field, remaining)

/-- Both named and explicitly contextual identities use the same complete
intrinsic producer. The formal identity is checked at the already selected
category; its repeated endpoint is one retained computational occurrence. -/
def captureIntrinsicIdentity (formal : Expr) (form : Form)
    (context : CategoryContext) (endpoint : Wire) : TermElabM Wire := do
  CategoryContext.checkMorphism context formal endpoint.value endpoint.value
  let expected ← identityAtContext context endpoint.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq formal expected) do
    throwError "the intrinsic identity changed its independently fixed formal map"
  let template : ActionDataTemplate := .ctor "identity"
    #[.wire .object endpoint, .wire .object endpoint]
  let (data, dependencies) ← renderCapturedActionData template
  let result : Wire := {
    form, payload := (← combinedRecipePayload formal data dependencies)
    categoryContext := some context }
  let result ← retainIntrinsicAssembly result .map context template
  retainCallableEndpoints result endpoint endpoint context

/-- Independently check one canonical callable body, including a preattachment
Wire held by the shared occurrence table. The descriptor must retain every exact
positioned supplier before any observation or registration dispatch. -/
def checkSelectedCallableInvocation (wire : Wire) (selected : SelectedCallableInvocation) :
    TermElabM Unit := do
  unless wire.value == selected.formal && wire.fragment == selected.fragment do
    throwError "the selected invocation changed its original whole occurrence"
  discard <| framingContext (some selected.context) wire.categoryContext
  CategoryContext.checkMorphism selected.context wire.value selected.source.value selected.target.value
  let (descriptor, _) ← renderCapturedActionData selected.descriptor
  unless descriptor == wire.fragment do
    throwError "the selected invocation lost its original descriptor positions or suppliers"
  for parameter in selected.declarationParameters do
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType parameter.formal) parameter.expectedType) do
      throwError "the selected invocation changed a complete declaration parameter type"
  return ()

/-- Allocate through the shared immutable occurrence owner only after the
complete callable specialization has passed its own formal and input checks. -/
def retainSelectedCallableInvocation (h : Harness) (wire : Wire)
    (selected : SelectedCallableInvocation) : TermElabM Wire := do
  checkSelectedCallableInvocation wire selected
  -- Every consumer of this pending callable reads its producer's exact
  -- endpoint occurrences, including before the invocation is observed.
  let wire ← retainCallableEndpoints wire selected.source selected.target selected.context
  retainCapturedInvocation h wire (.callable selected)

def selectedCallableIdentity (context : CategoryContext) (source : Wire) : TermElabM Wire := do
  let formal ← identityAtContext context source.value
  captureIntrinsicIdentity formal (contextualForm (← registryState) context source.form true)
    context source

/-- Form the public field while its parent is still pending. The exact path
and endpoint positions come from a fresh receiver, not its actual equal fields. -/
partial def capturePublicRecordProjectionAt (h : Harness) (parent : Wire)
    (path : ComputationalData.RecordFieldPath) : TermElabM Wire := do
  if path.isEmpty then return parent
  let selected ← selectPublicRecordField parent path
  let state ← registryState
  let form := match selected.result with
    | .object context => contextualForm state context parent.form
    | .map context => contextualForm state context parent.form true
    | .value _ => parent.form
  let endpoints ← match selected.endpoints with
    | none => pure none
    | some (source, target) =>
      pure (some (← capturePublicRecordProjectionAt h parent source,
        ← capturePublicRecordProjectionAt h parent target))
  let wire : Wire := {
    form, payload := (← combinedRecipePayload selected.formal parent.fragment #[parent]),
    categoryContext := selected.result.context?,
    serviceHandles := (← retainServiceOperands h #[parent]) }
  let wire ← match selected.result, endpoints with
    | .map context, some (source, target) => retainCallableEndpoints wire source target context
    | .map _, none => throwError "the public map field lost its declared endpoint paths"
    | _, none => pure wire
    | _, some _ => throwError "a non-map public field acquired an unrelated callable interface"
  retainCapturedInvocation h wire (.recordProjection {
    formal := wire.value, fragment := wire.fragment, result := selected.result,
    parent, path, endpoints })

/-- An intermediate exposed by a fused reply is read from that exact returned
position. A separately observed action has no authority over its packet. Hidden
whole intermediates are never reconstructed from an equal closed expression. -/
partial def readProducedProjectionWith (reader : RetainedRecordReader)
    (fields : RetainedResultFields) (actionIndex : Nat)
    (projection : ComputationalData.RecordProjectionPlan) (formal : Expr)
    (result : IntrinsicResultInterface) (form : Form)
    (missing : Nat → ComputationalData.RecordProjectionPlan → Expr →
      IntrinsicResultInterface → Form → TermElabM Wire := fun _ _ _ _ _ =>
      throwStratum .noImplementation
        "the complete reply omits the required intermediate data occurrence") : TermElabM Wire := do
  match projection with
  | .input path =>
    let paths := fields.plan.producedPaths actionIndex path
    if paths.isEmpty then
      return ← missing actionIndex projection formal result form
    let selected ← match paths with
      | #[path] => pure path
      | #[] =>
        throwStratum .noImplementation
          "the complete reply omits the required intermediate data occurrence"
      | _ =>
        throwStratum .ambiguousRealization
          "the complete reply exposes several distinct occurrences of a required intermediate"
    let some (original, remaining) ← fields.project? selected
      | throwError "the produced field lost its declared complete output position"
    let field ← if remaining.isEmpty then pure original else reader.readField original remaining
    let field ← forwardRetainedValue field formal
    checkCapturedResultInterface field result
    return field
  | .record codec projections =>
    let (expectedCodec, children) ← publicRecordFields formal result
    unless codec == expectedCodec && projections.size == children.size do
      throwError "the produced parameter changed its public record schema"
    let state ← registryState
    let children ← (projections.zip children).mapM fun (projection, child) => do
      let childForm := match child.result with
        | .object context => contextualForm state context form
        | .map context => contextualForm state context form true
        | .value _ => form
      readProducedProjectionWith reader fields actionIndex projection
        child.formal child.result childForm missing
    assembleRetainedRecordWith codec children formal result form

/-- Materialize a declared projection parameter by its positional producer tree.
An intermediate is the captured output of one preceding action, never a lookup
by its mathematical value. Records preserve every original child occurrence. -/
partial def materializeProjectionSourceWith (reader : RetainedRecordReader)
    (readInput : RoutedResultPlan.Input → TermElabM Wire)
    (readIntermediate : Nat → ComputationalData.RecordProjectionPlan → Expr →
      IntrinsicResultInterface → Form → TermElabM Wire)
    (source : RoutedResultPlan.ProjectionParameterSource) (formal : Expr)
    (result : IntrinsicResultInterface) (form : Form) : TermElabM Wire := do
  match source with
  | .retained input projection =>
    projectRetainedRecordWith reader (← readInput input) projection formal result form
  | .intermediate index projection =>
    readIntermediate index projection formal result form
  | .record codec sources =>
    let (expectedCodec, fields) ← publicRecordFields formal result
    unless codec == expectedCodec && sources.size == fields.size do
      throwError "the composed projection parameter changed its public field schema"
    let state ← registryState
    let children ← (sources.zip fields).mapM fun (source, field) => do
      let form := match field.result with
        | .object context => contextualForm state context form
        | .map context => contextualForm state context form true
        | .value _ => form
      materializeProjectionSourceWith reader readInput readIntermediate source
        field.formal field.result form
    assembleRetainedRecordWith codec children formal result form
  | .literal data =>
    let .value expected := result
      | throwError "a fixed scalar parameter acquired an unrelated categorical role"
    let .ok decoded ← Codec.decode expected data
      | throwError "the fixed projection parameter lost its portable literal codec"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType decoded) expected <&&> isDefEq decoded formal) do
      throwError "the fixed projection literal changed its selected formal value"
    let packet ← checkedFragment (DataOwnership.Data.portable data)
    let wire : Wire := { form, payload := (← scopedPayload formal packet) }
    retainCompletedResultInterface wire result

/-- Use the existing public action descriptor at its fixed declaration slots.
Constructor wrappers are the same accepted wrappers used by capturedEdgeData. -/
def routedActionDescriptor (edge : EdgeRef)
    (parameters : Array ActionDataTemplate) : ActionDataTemplate :=
  match edge with
  | .functor id => .ctor id.raw parameters
  | .classifierForget id =>
      .ctor "classifierForget" #[.literal { json := toJson id.raw }, .array parameters]
  | .constructMap constructor inner =>
      .ctor "constructorMap" #[.literal { json := toJson constructor.raw },
        routedActionDescriptor inner parameters]

/-- Materialize one retained declaration telescope. Explicit proof parameters
remain formal slots with no computational data; every other slot keeps its
original positioned supplier and full public role. -/
def materializeProjectionParametersWith (reader : RetainedRecordReader)
    (readInput : RoutedResultPlan.Input → TermElabM Wire)
    (readIntermediate : Nat → ComputationalData.RecordProjectionPlan → Expr →
      IntrinsicResultInterface → Form → TermElabM Wire)
    (declared : Expr) (parameters : Array RoutedResultPlan.ProjectionParameter) :
    TermElabM (Array SelectedCallableParameter) := do
  let state ← registryState
  let (_, infos, _) ← forallMetaTelescopeReducing (← inferType declared.getAppFn)
  let arguments := declared.getAppArgs
  unless infos.size == arguments.size do
    throwError "the field declaration changed its complete parameter telescope"
  let mut dataIndex := 0
  let mut result := #[]
  for position in [:arguments.size] do
    let some expected := arguments[position]?
      | throwError "the field declaration omitted a complete argument"
    let some info := infos[position]?
      | throwError "the field declaration omitted a binder role"
    unless info.isExplicit do continue
    let expectedType ← instantiateMVars (← inferType expected)
    if ← isProp expectedType then
      result := result.push { formal := expected, expectedType, templates := #[] }
      continue
    let some parameter := parameters[dataIndex]?
      | throwError "the field declaration omitted an original computational parameter slot"
    unless parameter.dataIndex == dataIndex && parameter.declarationIndex == position do
      throwError "the field declaration changed its original computational parameter order"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq expectedType parameter.expectedType <&&> isDefEq expected parameter.formal) do
      throwError "the field declaration changed a parameter's complete formal interface"
    let (interface, fallback) ← match parameter.role with
      | .value => pure (IntrinsicResultInterface.value parameter.expectedType, none)
      | .objectAt context => pure (.object context, none)
      | .mapAt context source target => do
        CategoryContext.checkMorphism context parameter.formal source target
        pure (.map context, none)
      | .object input path => do
        let original ← readInput input
        let selected ← selectPublicRecordField original path
        let .object context := selected.result
          | throwError "the field action's object parameter changed its original public role"
        pure (.object context, some original.form)
      | .map input path => do
        let original ← readInput input
        let selected ← selectPublicRecordField original path
        let .map context := selected.result
          | throwError "the field action's callable parameter changed its original public role"
        pure (.map context, some original.form)
    let original ← readInput .receiver
    let form := match interface with
      | .object context => contextualForm state context (fallback.getD original.form)
      | .map context => contextualForm state context (fallback.getD original.form) true
      | .value _ => original.form
    let field ← materializeProjectionSourceWith reader readInput readIntermediate
      parameter.source parameter.formal interface form
    checkCapturedResultInterface field interface
    result := result.push {
      formal := parameter.formal, expectedType := parameter.expectedType,
      templates := #[.wire interface.role field] }
    dataIndex := dataIndex + 1
  unless dataIndex == parameters.size do
    throwError "the field declaration acquired extra computational parameter positions"
  return result

/-- Materialize a symbolically selected projection and every retained alignment
segment. Comparisons select the whole canonical functor; their component data
remain local to the original cell and action positions. -/
def materializeRecordProjectionActionWith (reader : RetainedRecordReader)
    (readInput : RoutedResultPlan.Input → TermElabM Wire)
    (plan : RoutedResultPlan.ProjectionActionPlan)
    (readIntermediate : Nat → ComputationalData.RecordProjectionPlan → Expr →
      IntrinsicResultInterface → Form → TermElabM Wire := fun _ _ _ _ _ =>
      throwError "a standalone projection has no captured intermediate action") :
    TermElabM RecordProjectionAction := do
  unless plan.route.refs == plan.steps.map (·.edge) do
    throwError "the projection route changed its original ordered action positions"
  unless plan.steps.isEmpty do
    let composite ← Semantic.compositeOfApplications (plan.steps.map (·.application))
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType composite) (← inferType plan.application) <&&>
          isDefEq composite plan.application) do
      throwError "the field route changed its complete selected composite"
  let segment := fun (steps : Array RoutedResultPlan.ProjectionActionStep) => do
    steps.mapM fun step => do
      let declared ← step.checkedDeclaration
      let parameters ← materializeProjectionParametersWith reader readInput readIntermediate
        declared step.parameters
      pure (routedActionDescriptor step.edge (parameters.flatMap (·.templates)))
  let descriptors ← segment plan.steps
  let mut alignment := #[]
  let mut comparison : Option Expr := none
  for selected in plan.alignment do
    let declared ← selected.checkedDeclaration
    let parameters ← materializeProjectionParametersWith reader readInput readIntermediate
      declared selected.parameters
    let current ← if selected.inverse then
      mkAppM ``CategoryTheory.Iso.symm #[selected.data.comparison]
      else pure selected.data.comparison
    comparison ← match comparison with
      | none => pure (some current)
      | some previous => some <$> mkAppM ``CategoryTheory.Iso.trans #[previous, current]
    alignment := alignment.push {
      plan := selected, parameters,
      before := (← segment selected.before), left := (← segment selected.left),
      right := (← segment selected.right), after := (← segment selected.after) }
  match comparison, plan.alignmentComparison with
  | none, none =>
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType plan.application) (← inferType plan.projection) <&&>
          isDefEq plan.application plan.projection) do
      throwError "the field route omitted its complete accepted alignment"
  | some actual, some fixed =>
    Semantic.checkRouteComparison fixed plan.application plan.projection
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType actual) (← inferType fixed) <&&> isDefEq actual fixed) do
      throwError "the field alignment changed its original ordered comparison occurrences"
  | _, _ => throwError "the field route lost an accepted comparison occurrence"
  return { plan, descriptors, alignment }

/-- A standalone projection has only its original parent as a retained input
root. Missing nonportable category-parameter data remains an explicit missing
interface; it is never replaced by an equal closed cache entry. -/
def standaloneRecordProjectionActionWith (reader : RetainedRecordReader)
    (parent : Wire) (step : ComputationalData.RecordFieldStep) :
    TermElabM (Option RecordProjectionAction) := do
  if parent.objectIso.isNone && parent.endpointPresentation.isNone then return none
  let selected ← selectPublicRecordField parent #[step]
  let .object target := selected.result | return none
  let some source := parent.categoryContext
    | throwError "the presented record lost its complete selected source category"
  let plan ← match ← RoutedResultPlan.selectProjectionAction parent.value source target step with
    | .ok plan => pure plan
    | .error failure => failure.raise
  return some (← materializeRecordProjectionActionWith reader (fun input => match input with
    | .receiver => pure parent
    | .parameter .. => throwError "a standalone field action acquired an unrelated parameter root") plan)

/-- Retain the entire selected endpoint, including comparison and category data.
Bindings are local to one operation application and one declared field path. -/
structure OperationPointPresentation where
  path : ComputationalData.RecordFieldPath
  endpoint : Wire

/-- A point's actual invocation interface is prepared together. The original
formal point and its generalized domain remain fixed; normalized endpoint
metadata cannot be installed after retaining an argument framed at other data. -/
structure PreparedOperationPoints where
  domain : Wire
  source : Wire
  target : Option Wire
  argument : DataOwnership.Data
  argumentTemplate : ActionDataTemplate
  dependencies : Array Wire

structure PreparedOperationArgument where
  data : DataOwnership.Data
  template : ActionDataTemplate
  actual : Expr
  dependencies : Array Wire

/-- Construction packets and proof/lift snapshots have additional provenance.
This local presentation binding does not compare or merge those execution states. -/
partial def operationPresentationRefinement (form : Form) : Bool :=
  match form with
  | .proofRefinement .. => true
  | .contextual _ original | .element original => operationPresentationRefinement original
  | _ => false

partial def checkOperationPointPresentation (endpoint : Wire) : TermElabM Unit := do
  if !endpoint.proofSources.isEmpty || endpoint.liftExecution.isSome ||
      operationPresentationRefinement endpoint.form ||
      (endpoint.payload matches .construction ..) then
    throwStratum .noImplementation
      "the operation endpoint requires its complete retained lift or refinement presentation"
  for component in endpoint.productComponents do
    checkOperationPointPresentation component


def bindOperationPointPresentation (bindings : Array OperationPointPresentation)
    (path : ComputationalData.RecordFieldPath) (endpoint : Wire) :
    TermElabM (Array OperationPointPresentation) := do
  checkOperationPointPresentation endpoint
  let matching := bindings.filter fun binding => sameOperationFieldPath binding.path path
  for previous in matching do
    unless sameOperationPointPresentation previous.endpoint endpoint do
      throwStratum .ambiguousRealization
        "one declared operation field has distinct complete point presentations"
  return bindings.push { path, endpoint }

/-- The declared role tree checks the product context produced from the
original endpoints. A missing context is not filled from equal outer bytes,
and a component's complete selection cannot be replaced by traversal order. -/
partial def checkOperationProductContext (context : CategoryContext)
    (role : OperationEndpointRole) (wire : Wire)
    (bindings : Array OperationPointPresentation) (position : Nat := 0) :
    TermElabM Nat := do
  checkOperationPointPresentation wire
  CategoryContext.checkObject context wire.value
  discard <| framingContext (some context) wire.categoryContext
  match role with
  | .field path =>
    let some selected := bindings[position]?
      | throwError "the operation product lost an ordered selected component"
    unless sameOperationFieldPath path selected.path &&
        sameProductComponents #[wire] #[selected.endpoint] do
      throwStratum .ambiguousRealization
        "the operation product has distinct complete contexts at one declared component"
    return position + 1
  | .product left right =>
    let #[first, second] := wire.productComponents
      | throwStratum .noImplementation
          "the operation product lacks its independently retained ordered component context"
    let product ← withTransparency .all <| whnf wire.value
    unless product.isAppOfArity ``Prod 2 do
      throwError "the retained product context is not the current complete product"
    let fields := product.getAppArgs
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq first.value fields[0]! <&&> isDefEq second.value fields[1]!) do
      throwError "the retained product context changed an independently fixed component"
    unless wire.fragment == (← scopedNode "objectProduct" #[first.fragment, second.fragment]) do
      throwStratum .unavailable "the product context changed its ordered data or suppliers"
    let position ← checkOperationProductContext context left first bindings position
    checkOperationProductContext context right second bindings position

/-- Follow only producer-recorded child selections and exact operand handles.
Preserve duplicates and order; equal data or formal expressions select nothing.
A cycle or missing handle is invalid metadata, not a presentation fallback. -/
partial def operationPresentationOperandClosure (retained : Array Wire)
    (wire : Wire) (active : Array Nat := #[]) : TermElabM (Array Wire) := do
  let mut result := #[wire]
  if let some framing := wire.morphismFraming then
    let comparisons := framing.comparisons.toArray.flatMap fun (source, target) =>
      source.toArray ++ target.toArray
    for component in #[framing.input, framing.source, framing.target] ++ comparisons do
      result := result ++ (← operationPresentationOperandClosure retained component active)
  if let some maps := wire.endpointPresentation.bind (·.maps) then
    for component in #[maps.1, maps.2] do
      result := result ++ (← operationPresentationOperandClosure retained component active)
  for component in wire.productComponents do
    result := result ++ (← operationPresentationOperandClosure retained component active)
  if let some recipe := wire.actionRecipe then
    for component in #[recipe.original] ++ actionTemplateInputs recipe.descriptor ++
        (recipe.endpoints.toArray.flatMap fun (source, target) => #[source, target]) ++
        (recipe.imageEndpoints.toArray.flatMap fun (source, target) => #[source, target]) do
      result := result ++ (← operationPresentationOperandClosure retained component active)
  if let some assembly := wire.intrinsicAssembly then
    let inputs := actionTemplateInputs assembly.template ++
      assembly.maps.flatMap (fun fields => #[fields.source, fields.target, fields.callable]) ++
      assembly.equalObjects.flatMap (fun (left, right) => #[left, right])
    for component in inputs do
      result := result ++ (← operationPresentationOperandClosure retained component active)
  if let some endpoints := wire.callableEndpoints then
    for component in #[endpoints.source, endpoints.target] do
      result := result ++ (← operationPresentationOperandClosure retained component active)
  for handle in wire.serviceHandles do
    if active.contains handle then
      throwError "the operation presentation has cyclic operand occurrences"
    let some operand := retained[handle]?
      | throwError "the operation presentation lost an exact operand occurrence"
    result := result ++ (← operationPresentationOperandClosure retained operand (active.push handle))
  return result

/-- The service decoder reads one handle layer. Retain each supplied whole Wire
in its original position, followed by its exact transitive occurrence context. -/
def retainOperationPresentationOperands (h : Harness) (wires : Array Wire) :
    TermElabM (Array Nat) := do
  let retained ← h.serviceOperands.get
  let mut inherited := #[]
  for wire in wires do
    let complete ← operationPresentationOperandClosure retained wire
    inherited := inherited ++ complete.extract 1 complete.size
  retainServiceOperands h (wires ++ inherited)

/-- Select the already accepted product interface once for both endpoint diagrams.
A created or differently represented product needs its supplied comparison. -/
def operationProductRow : TermElabM LimitEntry := do
  let state ← registryState
  let resolution ← match state.resolveLimitDetailed CategoryId.sets "product" false with
    | .ok selected => pure selected
    | .error (.ambiguous category shape colimit candidates) =>
        Semantic.limitResolutionFailure (.ambiguous category shape colimit candidates)
    | .error error => throwStratum .noImplementation m!"{error.message}"
  if resolution.lift.isSome then
    throwStratum .noImplementation
      "the selected product projection requires its complete creation comparison"
  let some row := state.limits.find? (·.id == resolution.limit)
    | throwError "the selected product projection interface disappeared"
  unless row.category == CategoryId.sets && !row.colimit do
    throwError "the published product projection has a different complete category"
  return row

/-- Instantiate the supplied cone at the complete ordered factors. Its apex,
diagram and category are checked before either comparisons or encodings use it. -/
def operationProductCone (context : CategoryContext) (row : LimitEntry)
    (first second : Expr) : TermElabM (Expr × Expr) := do
  CategoryContext.checkObject context first
  CategoryContext.checkObject context second
  let diagram ← mkAppOptM ``CategoryTheory.Limits.pair #[
    some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
    some first, some second]
  let some constructor ← Semantic.diagramConstructor row
    | throwError "the published product has no complete diagram declaration"
  unless diagram.getAppFn.constName? == some constructor do
    throwError "the product action changed its registered diagram declaration"
  let presentation ← StructuredResult.checkReconstruction
    (← Semantic.limitPresentation row diagram)
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let expected ← mkAppM ``Prod #[first, second]
  CategoryContext.checkObject context apex
  unless ← withoutModifyingState (withTransparency .all <| isDefEq apex expected) do
    throwStratum .noImplementation "the declared projection requires its actual product-apex comparison"
  return (diagram, presentation)

/-- The component comparisons induce the unique comparison of the selected
product cones through their supplied universal properties. -/
def operationProductIso (context : CategoryContext) (first second : Expr) :
    TermElabM Expr := do
  let (firstSource, firstTarget) ← operationComparisonEnds context first
  let (secondSource, secondTarget) ← operationComparisonEnds context second
  let row ← operationProductRow
  let (sourceDiagram, sourcePresentation) ← operationProductCone context row firstSource secondSource
  let (targetDiagram, targetPresentation) ← operationProductCone context row firstTarget secondTarget
  let diagramComparison ← mkAppOptM ``CategoryTheory.Limits.mapPairIso #[
    some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
    some sourceDiagram, some targetDiagram, some first, some second]
  let sourceLimit ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[sourcePresentation]
  let targetLimit ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[targetPresentation]
  let comparison ← StructuredResult.checkReconstruction
    (← mkAppM ``CategoryTheory.Limits.IsLimit.conePointsIsoOfNatIso
      #[sourceLimit, targetLimit, diagramComparison])
  let (source, target) ← operationComparisonEnds context comparison
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq source (← mkAppM ``Prod #[firstSource, secondSource]) <&&>
        isDefEq target (← mkAppM ``Prod #[firstTarget, secondTarget])) do
    throwError "the product comparison changed its independently fixed complete endpoints"
  return ← instantiateMVars comparison

/-- Recover only the formal composite already used by `presentMorphism`.
The original point remains the selected value; this is its actual data interface,
not a new invocation or a replacement of its generalized domain. -/
def operationFramedPoint (context : CategoryContext) (point source target : Wire) :
    TermElabM (Expr × Expr × Expr) := do
  CategoryContext.checkMorphism context point.value source.value target.value
  let mut actual := point.value
  let mut actualSource := source.value
  let mut actualTarget := target.value
  if let some presentation := source.endpointPresentation then
    let (original, selected) ← operationComparisonEnds context presentation.comparison
    unless ← withoutModifyingState (withTransparency .all <| isDefEq original source.value) do
      throwError "the original point's domain comparison changed its complete selected source"
    actualSource := selected
    actual ← ServiceRequest.compose context actualSource source.value target.value
      (← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison]) actual
  if let some presentation := target.endpointPresentation then
    let (original, selected) ← operationComparisonEnds context presentation.comparison
    unless ← withoutModifyingState (withTransparency .all <| isDefEq original target.value) do
      throwError "the original point's target comparison changed its complete selected source"
    actualTarget := selected
    actual ← ServiceRequest.compose context actualSource target.value actualTarget
      actual (← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison])
  discard <| StructuredResult.checkReconstruction actual
  CategoryContext.checkMorphism context actual actualSource actualTarget
  return (actual, actualSource, actualTarget)


/-- Declared parameter values keep their logical interface. A computational
composition reads its actual full map interface. The producer selects the view;
the validator never chooses it by testing which equal packet happens to fit. -/
inductive ValidationMapView where
  | logical
  | actual
  deriving BEq

/-- A selected computational interface is local to this exact occurrence.
Replacing its root view is permitted only by the producer's current typed
result; descendants remain at their declared positions and keep their owners. -/
def bindValidationScope (scope : ComputationalData.InterfaceScope) (formal : Expr)
    (role : ComputationalData.InterfaceRole) (representation : Option Expr := none) :
    TermElabM ComputationalData.InterfaceScope := do
  discard <| checkedFragment (scope.validate scope.data.json)
  let expectedType ← match role with
    | .object context =>
        CategoryContext.checkObject context formal
        CategoryContext.carrier context
    | .map context =>
        let (source, target) ← contextualMorphismEndpoints context formal
        CategoryContext.hom context source target
    | .value => inferType formal
  let representation ← representation.mapM fun actual => do
    let .map context := role
      | throwError "a value or object cannot acquire a callable presentation view"
    let (source, target) ← contextualMorphismEndpoints context actual
    return (actual, ← CategoryContext.hom context source target)
  if let some previous := scope.bindings.find? (·.path.isEmpty) then
    let oldType := previous.representation.map Prod.snd |>.getD previous.expectedType
    let newType := representation.map Prod.snd |>.getD expectedType
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq oldType newType) do
      throwStratum .unavailable
        "a current producer cannot replace a different complete data-result interface"
  let scope := { scope with bindings := scope.bindings.filter (! ·.path.isEmpty) }
  let scope ← checkedFragment (scope.bind formal expectedType role representation)
  discard <| checkedFragment (← ComputationalData.interfaceScopeBinding (some scope) scope.data.json)
  return scope

/-- The accepted comparison fixes the actual-side object. Its complete retained
endpoint occurrence supplies the data and all metadata; equal packets are never
used to obtain or substitute an endpoint. No comparison is executed here. -/
def endpointValidationView (wire : Wire) (context : CategoryContext)
    (actualSide : Bool := true) : TermElabM Wire := do
  CategoryContext.checkObject context wire.value
  discard <| framingContext (some context) wire.categoryContext
  let some presentation := wire.endpointPresentation | return wire
  let (forward, _) ← endpointPresentationMaps wire context presentation
  let some (semantic, actual) ← retainedCallableEndpoints? forward context
    | throwError "the comparison view lost its complete selected endpoint occurrence"
  unless actual.fragment == wire.fragment do
    throwStratum .unavailable "the actual endpoint view changed its original packet or suppliers"
  return if actualSide then actual else semantic

def validationScopeCtor (tag : String) (children : Array ComputationalData.InterfaceScope) :
    TermElabM ComputationalData.InterfaceScope := do
  let data ← scopedNode tag (children.map (·.data))
  checkedFragment (ComputationalData.InterfaceScope.assemble data
    (children.mapIdx fun index child => (#[.field "args", .index index], child)))

/-- A pending action's endpoint is its retained typed continuation. This
projection uses the original occurrence and selected application, never a cache
or a descriptor whose bytes happen to resemble an object action. -/
def validationMapEndpoints (wire : Wire) (context : CategoryContext) :
    TermElabM (Option (Wire × Wire)) := do
  if let some endpoints ← retainedCallableEndpoints? wire context then return some endpoints
  if !wire.completedData then
    if let some recipe := wire.actionRecipe then
      if recipe.morphism then
        checkActionRecipe wire recipe
        let (source, target) ← contextualMorphismEndpoints context wire.value
        let some source ← retainedActionEndpoint? wire (some context) source true
          | throwError "the pending map scope lost its retained source continuation"
        let some target ← retainedActionEndpoint? wire (some context) target false
          | throwError "the pending map scope lost its retained target continuation"
        return some (source, target)
  return none

/-- The complete producer/receipt, not a framed-status Boolean, authorizes a
computational Hom at the actual endpoints. Formal comparisons determine only
its type; this helper neither applies their maps nor claims completion. -/
def validationMapFormal (wire : Wire) (context : CategoryContext)
    (producer : Bool) : TermElabM Expr := do
  discard <| framingContext (some context) wire.categoryContext
  if !wire.morphismFramed then return wire.value
  let some (source, target) ← validationMapEndpoints wire context
    | throwStratum .unavailable "the consumed map scope lost its complete endpoint occurrences"
  unless producer || wire.completedData do
    if source.endpointPresentation.isSome || target.endpointPresentation.isSome then
      throwStratum .unavailable
        "a pending complete map has no retained producer for its consumed endpoint comparisons"
    return wire.value
  let (formal, _, _) ← operationFramedPoint context wire source target
  return formal

mutual

/-- Inspect only typed producer slots. This reader is inert: it never observes
an action, resolves a mathematical expression, or consults a result cache. -/
partial def templateValidationScope (template : ActionDataTemplate)
    (operands : Option (IO.Ref (Array Wire)) := none) (mapView : ValidationMapView := .actual) :
    TermElabM ComputationalData.InterfaceScope := do
  match template with
  | .literal data =>
      discard <| checkedFragment data.validate
      return { data }
  | .wire role original => wireValidationScope role original (operands := operands) (mapView := mapView)
  | .retained child => templateValidationScope child operands mapView
  | .logical child => templateValidationScope child operands .logical
  | .ctor tag children =>
      validationScopeCtor tag (← children.mapM fun child => templateValidationScope child operands mapView)
  | .array children =>
      let children ← children.mapM fun child => templateValidationScope child operands mapView
      let data := DataOwnership.Data.array (children.map (·.data))
      checkedFragment (ComputationalData.InterfaceScope.assemble data
        (children.mapIdx fun index child => (#[.index index], child)))
  | .object fields =>
      let children ← fields.mapM fun (key, child) => do
        return (key, ← templateValidationScope child operands mapView)
      let data ← checkedFragment (DataOwnership.Data.object
        (children.toList.map fun (key, scope) => (key, scope.data)))
      checkedFragment (ComputationalData.InterfaceScope.assemble data
        (children.map fun (key, scope) => (#[.field key], scope)))
  | .project path child =>
      let original ← templateValidationScope child operands mapView
      discard <| checkedFragment (original.validate original.data.json)
      let data ← checkedFragment (original.data.project path)
      let some selected := ComputationalData.InterfaceScope.at? (some original) path
        | throwStratum .unavailable "the retained template lost its declared data projection"
      unless selected.data == data do
        throwStratum .unavailable "the retained template changed its projected data or suppliers"
      discard <| checkedFragment (selected.validate data.json)
      return selected
  | .pointCallable context source target point =>
      let some selected := point.pointDataInterface
        | throwError "the positioned point conversion lost its declared data interface"
      let some (domain, codomain) ← retainedCallableEndpoints? point context
        | throwStratum .unavailable "the point conversion lost its exact complete endpoint occurrences"
      if let some operands := operands then operands.modify (· ++ #[domain, codomain])
      unless selected.domainData == domain.fragment && selected.targetData == codomain.fragment do
        throwStratum .unavailable "the point conversion changed its retained endpoint suppliers"
      CategoryContext.checkMorphism context point.value domain.value codomain.value
      let data ← pointCallableFragment point source target selected
      let output ← wireValidationScope .retained point (operands := operands) (mapView := .logical)
      let domain ← endpointValidationView domain context
      let codomain ← endpointValidationView codomain context
      let scope ← checkedFragment (ComputationalData.InterfaceScope.assemble data #[
        (#[.field "args", .index 0], ← wireValidationScope .object domain (operands := operands)),
        (#[.field "args", .index 1], ← wireValidationScope .object codomain (operands := operands)),
        (#[.field "args", .index 2, .field "args", .index 1, .index 0, .index 1], output)])
      let formal ← validationMapFormal { point with morphismFramed := true } context true
      let scope ← bindValidationScope scope formal (.map context)
      if mapView == .logical then bindValidationScope scope point.value (.map context) (some formal)
      else pure scope
  | .inventoryMap context source target original =>
      let template ← inventoryMapFrameTemplate context source target original
      -- Only the declared endpoint leaves receive actual presentation views.
      -- The retained whole-map body keeps its own positioned validation scope.
      let template ← mapActionTemplateWires (fun role endpoint => do
        if role == .retained then endpointValidationView endpoint context
        else pure endpoint) template
      templateValidationScope template operands mapView

/-- A current framing layer contributes its exact input and chosen comparison
occurrences. Replay checks the complete packet and metadata before a local
actual-Hom view is assembled from those ordered constituent scopes. -/
partial def framingValidationScope (wire : Wire) (context : CategoryContext)
    (framing : MorphismFraming) (operands : Option (IO.Ref (Array Wire)) := none)
    (inputScope : Option ComputationalData.InterfaceScope := none) :
    TermElabM ComputationalData.InterfaceScope := do
  discard <| framingContext (some context) framing.context
  let replayed ← presentMorphism framing.input framing.source framing.target
    framing.context framing.comparisons
  unless sameCompleteWireContext replayed wire do
    throwStratum .unavailable "the comparison scope lost its exact current framing producer"
  if let some operands := operands then
    operands.modify (· ++ #[framing.source, framing.target])
  let mut scope ← match inputScope with
    | none => wireValidationScope .map framing.input (some context) operands
    | some supplied => do
      unless supplied.data == framing.input.fragment do
        throwStratum .unavailable "the declared comparison input changed its exact packet or suppliers"
      let .ok (some selected) ← ComputationalData.interfaceScopeBinding
          (some supplied) framing.input.json
        | throwStratum .unavailable "the declared comparison input lost its complete selected interface"
      let (source, target) ← contextualMorphismEndpoints context framing.input.value
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq selected.expectedType (← CategoryContext.hom context source target) <&&>
            isDefEq selected.formal framing.input.value) do
        throwStratum .unavailable "the declared comparison input changed its original full Hom"
      pure supplied
  let mut actual := framing.input.value
  let mut source := framing.source.value
  if let some presentation := framing.source.endpointPresentation then
    let (_, selected) ← endpointPresentationMaps framing.source context presentation
    let selected := (framing.comparisons.bind (·.1)).getD selected
    let expected ← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison]
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType selected.value) (← inferType expected) <&&>
          isDefEq selected.value expected) do
      throwError "the local source view changed its independently selected comparison"
    let some (actualSource, semanticSource) ← retainedCallableEndpoints? selected context
      | throwError "the source comparison lost its complete endpoint occurrences"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq semanticSource.value source) do
      throwError "the source comparison changed the original typed domain"
    scope ← validationScopeCtor "compose" #[← wireValidationScope .map selected (operands := operands), scope]
    actual ← ServiceRequest.compose context actualSource.value source framing.target.value selected.value actual
    source := actualSource.value
    scope ← bindValidationScope scope actual (.map context)
  if let some presentation := framing.target.endpointPresentation then
    let (selected, _) ← endpointPresentationMaps framing.target context presentation
    let selected := (framing.comparisons.bind (·.2)).getD selected
    let expected ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType selected.value) (← inferType expected) <&&>
          isDefEq selected.value expected) do
      throwError "the local target view changed its independently selected comparison"
    let some (semanticTarget, actualTarget) ← retainedCallableEndpoints? selected context
      | throwError "the target comparison lost its complete endpoint occurrences"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq semanticTarget.value framing.target.value) do
      throwError "the target comparison changed the original typed codomain"
    scope ← validationScopeCtor "compose" #[scope, ← wireValidationScope .map selected (operands := operands)]
    actual ← ServiceRequest.compose context source framing.target.value actualTarget.value actual selected.value
    scope ← bindValidationScope scope actual (.map context)
  unless scope.data == wire.fragment do
    throwStratum .unavailable "the selected comparison scope changed its positioned data or suppliers"
  bindValidationScope scope actual (.map context)

/-- Whole replies keep their complete invocation endpoints. TypedMap's known
fields may expose those exact occurrences, but returned body bytes never select
a new producer or typed dependency. Other public packets retain only their full
already selected map interface and undergo the normal recursive validator. -/
partial def endpointValidationScope (scope : ComputationalData.InterfaceScope)
    (wire : Wire) (context : CategoryContext) (operands : Option (IO.Ref (Array Wire)) := none) :
    TermElabM ComputationalData.InterfaceScope := do
  let some (source, target) ← validationMapEndpoints wire context | return scope
  if let some operands := operands then operands.modify (· ++ #[source, target])
  let source ← endpointValidationView source context wire.morphismFramed
  let target ← endpointValidationView target context wire.morphismFramed
  let some body := ComputationalData.InterfaceScope.valuePayload? (some scope) | return scope
  let .ok typed := Backend.TypedMap.decode body.data.json | return scope
  unless typed.source == source.json && typed.target == target.json do
    throwStratum .unavailable "the map scope changed its complete original computational endpoints"
  let sourceData ← checkedFragment (body.data.project #[.field "args", .index 0])
  let targetData ← checkedFragment (body.data.project #[.field "args", .index 1])
  unless sourceData == source.fragment && targetData == target.fragment do
    throwStratum .unavailable "the map scope changed a retained endpoint supplier"
  let mut fieldPath : DataOwnership.Path := #[]
  let mut current := scope.data
  while (current.json.getObjValAs? String "ctor").toOption == some "valueData" do
    current ← checkedFragment (current.project #[.field "args", .index 0])
    fieldPath := fieldPath ++ #[.field "args", .index 0]
  let mut bindings := scope.bindings
  for (index, endpoint) in #[(0, source), (1, target)] do
    let path := fieldPath ++ #[.field "args", .index index]
    let child ← wireValidationScope .object endpoint (operands := operands)
    if let some existing := ComputationalData.InterfaceScope.at? (some scope) path then
      let .ok previous ← ComputationalData.interfaceScopeBinding (some existing) endpoint.json
        | throwStratum .unavailable "the callable field lost its positioned typed producer"
      if let some previous := previous then
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq previous.expectedType (← inferType endpoint.value) <&&>
              isDefEq previous.formal endpoint.value) do
          throwStratum .unavailable "the endpoint receipt conflicts with its declared typed field"
        match previous.role with
        | .object previous | .map previous =>
          discard <| framingContext (some context) (some previous)
        | .value => pure ()
    -- This explicit endpoint receipt is current authority for this field.
    -- Deeper children stay at their own typed positions; no packet is searched.
    bindings := bindings.filter fun binding => (DataOwnership.stripPrefix? path binding.path).isNone
    bindings := bindings ++ child.bindings.map (fun binding => { binding with path := path ++ binding.path })
  let scope := { scope with bindings }
  discard <| checkedFragment (scope.validate scope.data.json)
  return scope

partial def wireValidationScope (role : ActionDataRole) (wire : Wire)
    (context? : Option CategoryContext := none) (operands : Option (IO.Ref (Array Wire)) := none)
    (mapView : ValidationMapView := .actual) :
    TermElabM ComputationalData.InterfaceScope := do
  discard <| checkedFragment wire.fragment.validate
  if let some operands := operands then operands.modify (·.push wire)
  let context ← framingContext context? wire.categoryContext
  let mapView := if role == .parameter then ValidationMapView.logical else mapView
  if role != .object && wire.pointDataInterface.isNone &&
      (← retainedValueResultInterface? wire).isNone then
    if let some framing := wire.morphismFraming then
      let some context := context
        | throwError "the positioned framing lost its complete selected category"
      let scope ← framingValidationScope wire context framing operands
      if mapView == .logical then
        let some selected := scope.bindings.find? (·.path.isEmpty)
          | throwError "the positioned frame lost its actual full Hom"
        return ← bindValidationScope scope wire.value (.map context) (some selected.formal)
      return scope
  let assembly ← currentIntrinsicAssembly? wire
  let mut scope ← match assembly with
    | some selected =>
      let templateView := match selected.result with
        | .map _ => if wire.pointDataInterface.isSome then .logical else .actual
        | .object _ | .value _ => ValidationMapView.logical
      let scope ← templateValidationScope selected.template operands templateView
      unless scope.data == wire.fragment do
        throwStratum .unavailable "the current result lost its exact typed producer slots"
      pure scope
    | none =>
      if !wire.completedData then
        if let some captured ← retainedCapturedInvocation? wire then
          if let .callable selected := captured.interface then
            let scope ← templateValidationScope selected.descriptor operands .logical
            unless scope.data == wire.fragment do
              throwStratum .unavailable "the selected callable lost its declared parameter positions"
            pure scope
          else pure { data := wire.fragment }
        else if let some recipe := wire.actionRecipe then
          checkActionRecipe wire recipe
          if recipe.morphism then
            let some (source, target) := recipe.endpoints
              | throwError "the positioned map action lost its exact original endpoints"
            let input ← if recipe.original.pointDataInterface.isSome then
                pure (ActionDataTemplate.pointCallable recipe.source source.value target.value recipe.original)
              else do
                let framed ← presentMorphism recipe.original source target (some recipe.source)
                pure (.wire .map framed)
            if let some operands := operands then operands.modify (· ++ #[source, target])
            let descriptorScope ← templateValidationScope recipe.descriptor operands .logical
            let inputScope ← templateValidationScope input operands .actual
            let scope ← validationScopeCtor "map" #[descriptorScope, inputScope]
            unless scope.data == wire.fragment do
              throwStratum .unavailable "the positioned map action changed its exact captured input assembly"
            pure scope
          else pure { data := wire.fragment }
        else pure { data := wire.fragment }
      else pure { data := wire.fragment }
  -- A point's bytes are its value data, possibly themselves a whole callable.
  -- Only pointCallable's declared conversion gives them the outer point Hom.
  if wire.pointDataInterface.isSome then return scope
  let selectedRole : ComputationalData.InterfaceRole ← match role with
    | .object =>
      let some context := context
        | throwStratum .unavailable "the positioned object lost its complete selected category"
      pure (ComputationalData.InterfaceRole.object context)
    | .map =>
      match context with
      | some context => pure (.map context)
      | none =>
        throwStratum .unavailable
          "the positioned whole map lost its complete selected category"
    | .parameter | .retained =>
      match assembly.map (fun (selected : IntrinsicAssembly) => selected.result) with
      | some (.object context) => pure (.object context)
      | some (.map context) => pure (.map context)
      | some (.value _) => pure .value
      | none =>
        match context with
        | none => pure .value
        | some context =>
          match ← constructionResultInterface context wire.value (← inferType wire.value) with
          | .object context => pure (.object context)
          | .map context => pure (.map context)
          | .value _ => pure .value
  match selectedRole with
  | .map context =>
    let producer := assembly.isSome || (!wire.completedData &&
      (wire.actionRecipe.isSome || wire.capturedInvocation.isSome))
    let formal ← validationMapFormal wire context producer
    scope ← endpointValidationScope scope wire context operands
    let boundScope ← bindValidationScope scope formal (.map context)
    if mapView == .logical then bindValidationScope boundScope wire.value (.map context) (some formal)
    else pure boundScope
  | _ => bindValidationScope scope wire.value selectedRole

end

/-- Build a private view from one complete current map occurrence. The caller
fixes the computational Hom independently; it may differ from the logical Hom
only through this occurrence's retained accepted endpoint comparisons. -/
def callableValidationScope (wire : Wire) (context : CategoryContext) (formal : Expr)
    (operands : Option (IO.Ref (Array Wire)) := none) :
    TermElabM ComputationalData.InterfaceScope := do
  let scope ← wireValidationScope .map wire (some context) operands
  let .ok (some selected) ← ComputationalData.interfaceScopeBinding (some scope) wire.json
    | throwStratum .unavailable "the whole map lost its current positioned result interface"
  let (source, target) ← contextualMorphismEndpoints context formal
  let expected ← CategoryContext.hom context source target
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq selected.expectedType expected <&&> isDefEq selected.formal formal) do
    throwStratum .unavailable "the comparison scope changed the complete computational Hom"
  return scope

/-- A short-lived producer template can frame a private future or a prepared
argument without relabeling the persistent logical Wire. Every literal and
typed child must reproduce the exact supplied packet, including suppliers. -/
def callableTemplateValidationScope (context : CategoryContext) (formal : Expr)
    (data : DataOwnership.Data) (template : ActionDataTemplate)
    (operands : Option (IO.Ref (Array Wire)) := none)
    (mapView : ValidationMapView := .actual) :
    TermElabM ComputationalData.InterfaceScope := do
  let scope ← templateValidationScope template operands mapView
  unless scope.data == data do
    throwStratum .unavailable "the local callable template changed a declared field or supplier"
  bindValidationScope scope formal (.map context)

/-- A field's producer determines whether it already owns a validated
computational interface. Newly returned bytes remain neutral until validation. -/
inductive RecordFieldOrigin where
  | retained
  | returned

/-- Complete a selected segment at its original typed input. A supplied final
image is an existing occurrence at that independently fixed interface, not a
receipt claiming that this segment was separately executed. -/
def captureProjectionObjectSegment (steps : Array RoutedResultPlan.ProjectionActionStep)
    (descriptors : Array ActionDataTemplate) (original : Wire)
    (finalImage? : Option Wire := none) : TermElabM Wire := do
  unless steps.size == descriptors.size do
    throwError "the projection segment lost an ordered action descriptor"
  if steps.isEmpty then
    if let some image := finalImage? then
      let image ← forwardRetainedValue image original.value
      unless sameCompleteWireContext original image do
        throwStratum .noImplementation "an empty action segment needs its exact original occurrence"
    return original
  let state ← registryState
  let mut current := original
  for (step, index) in steps.zipIdx do
    let some descriptor := descriptors[index]?
      | throwError "the projection segment lost an original parameter template"
    discard <| step.checkedDeclaration
    let (source, target) ← actionOwnerContexts (.edge step.edge) step.application current false
    discard <| framingContext (some step.sourceContext) (some source)
    discard <| framingContext (some step.targetContext) (some target)
    let formal ← Semantic.objOf step.application current.value
    if index + 1 == steps.size then
      if let some image := finalImage? then
        discard <| framingContext (some target) image.categoryContext
        CategoryContext.checkObject target image.value
        return ← forwardRetainedValue image formal
    let form := match CategoryContext.named? state target.expression with
      | some category => imageForm state step.edge category
      | none => contextualForm state target current.form
    current ← captureRegisteredObjectAction (.edge step.edge) step.application
      current formal form target descriptor
  return current

/-- The common map-action capture retains independently chosen image endpoints.
Its ordinary executor computes the map at those occurrences, without claiming
that a separately observed object action produced either supplied packet. -/
def captureRegisteredMapAction (owner : ActionOwner) (action : Expr)
    (descriptor : ActionDataTemplate) (original sourceImage targetImage : Wire) :
    TermElabM Wire := do
  let (source, target) ← actionOwnerContexts owner action original true
  let some endpoints ← retainedCallableEndpoints? original source
    | throwError "the captured map action lost its complete original endpoints"
  let formal ← Semantic.mapOf action original.value
  let template : ActionDataTemplate := .ctor "map" #[descriptor, .wire .map original]
  let (data, dependencies) ← renderCapturedActionData template
  let output : Wire := {
    form := contextualForm (← registryState) target original.form true,
    payload := (← combinedRecipePayload formal data
      (dependencies ++ #[sourceImage, targetImage])),
    categoryContext := some target, morphismFramed := true }
  let output ← retainRegisteredActionInput owner true action original output descriptor
    (some endpoints) (some (sourceImage, targetImage))
  retainActionImageEndpoints output

/-- Projection steps use the same map-action capture as every other consumer.
Recheck the complete original declaration before supplying its retained images. -/
def captureProjectionMapStep (step : RoutedResultPlan.ProjectionActionStep)
    (descriptor : ActionDataTemplate) (original sourceImage targetImage : Wire) :
    TermElabM Wire := do
  discard <| step.checkedDeclaration
  captureRegisteredMapAction (.edge step.edge) step.application descriptor
    original sourceImage targetImage

/-- A completion action consumes the public role selected on the original
fresh stage. Its closed formal type alone never reclassifies scalar data. -/
def intermediateActionInputInterface (inputs : RoutedInputData)
    (selected : RoutedResultPlan.FieldCompletionAction) :
    TermElabM IntrinsicResultInterface := do
  match selected.inputRole with
  | .value => return .value selected.inputType
  | .objectAt context =>
    CategoryContext.checkObject context selected.input
    return .object context
  | .mapAt context source target =>
    CategoryContext.checkMorphism context selected.input source target
    return .map context
  | .object input path =>
    let field ← selectPublicRecordField (← inputs.read input) path
    let .object context := field.result
      | throwError "the intermediate object action changed its original public input role"
    return .object context
  | .map input path =>
    let field ← selectPublicRecordField (← inputs.read input) path
    let .map context := field.result
      | throwError "the intermediate map action changed its original public callable role"
    return .map context

mutual

/-- Exposed final-reply occurrences are authoritative. Only an absent field
uses its stage's independently compiled completion, with the exact request
inputs and a cache local to this one returned occurrence. -/
partial def readCompletedProducedProjectionWith (reader : RetainedRecordReader)
    (fields : RetainedResultFields) (actionIndex : Nat)
    (projection : ComputationalData.RecordProjectionPlan) (formal : Expr)
    (result : IntrinsicResultInterface) (form : Form) : TermElabM Wire := do
  readProducedProjectionWith reader fields actionIndex projection formal result form
    (fun actionIndex projection formal result form => do
      let .input path := projection
        | throwError "a missing intermediate field lost its selected public path"
      let stage ← fields.plan.stage actionIndex
      let some (index, remaining) ← routedSlotPosition? stage.slots path
        | throwStratum .noImplementation
            "the required intermediate has no declared public result-field position"
      let original ← completeIntermediateSlotWith reader fields actionIndex index
      let field ← if remaining.isEmpty then pure original else reader.readField original remaining
      let field ← forwardRetainedValue field formal
      checkCapturedResultInterface field result
      return field)

/-- Capture a missing stage field through registered actions and public record
assembly. Capture is inert; the ordinary actual/private observer executes the
result only when a consumer demands that complete field. -/
partial def completeIntermediateSlotWith (reader : RetainedRecordReader)
    (fields : RetainedResultFields) (actionIndex index : Nat) : TermElabM Wire := do
  unless actionIndex < fields.plan.prefixActions.size do
    throwError "an intermediate completion cannot depend on its own method result"
  let stage ← fields.plan.stage actionIndex
  let some slot := stage.slots[index]?
    | throwError "the intermediate completion lost an original field position"
  let some inputs := fields.inputs
    | throwStratum .unavailable "the result lost its exact materialized request input receipt"
  let result := routedSlotInterface slot
  let form := routedSlotForm (← registryState) inputs.receiver.form slot
  -- Never replace a supplied field by another invocation of its producer.
  if !(fields.plan.producedPaths actionIndex slot.replyPath).isEmpty then
    return ← readProducedProjectionWith reader fields actionIndex (.input slot.replyPath)
      slot.formal result form
  let some cache := fields.intermediates
    | throwStratum .unavailable "the intermediate completion lost its owning result scope"
  if let some (_, _, completed) := (← cache.get).values.find? fun (action, position, _) =>
      action == actionIndex && position == index then
    let completed ← forwardRetainedValue completed slot.formal
    checkCapturedResultInterface completed result
    return completed
  let key := (actionIndex, index)
  if (← cache.get).active.contains key then
    throwStratum .noImplementation
      "the declared intermediate completion requires a cyclic data occurrence"
  let some completion := stage.completions[index]?
    | throwError "the intermediate schema omitted its positioned completion instruction"
  cache.modify fun state => { state with active := state.active.push key }
  try
    let readIntermediate := readCompletedProducedProjectionWith reader fields
    let completed ← match completion with
      | .retained source =>
        materializeProjectionSourceWith reader inputs.read readIntermediate
          source slot.formal result form
      | .record codec indices => do
        let children ← indices.mapM (completeIntermediateSlotWith reader fields actionIndex)
        assembleRetainedRecordWith codec children slot.formal result form
      | .action selected => do
        let originalInterface ← intermediateActionInputInterface inputs selected
        let state ← registryState
        let originalForm := match originalInterface with
          | .object context => contextualForm state context inputs.receiver.form
          | .map context => contextualForm state context inputs.receiver.form true
          | .value _ => inputs.receiver.form
        let original ← materializeProjectionSourceWith reader inputs.read readIntermediate
          selected.source selected.input originalInterface originalForm
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType original.value) selected.inputType <&&>
              isDefEq original.value selected.input) do
          throwError "the intermediate action changed its original complete input"
        let descriptors ← selected.steps.mapM fun step => do
          let parameters ← materializeProjectionParametersWith reader inputs.read readIntermediate
            (← step.checkedDeclaration) step.parameters
          pure (routedActionDescriptor step.edge (parameters.flatMap (·.templates)))
        match selected.kind with
        | .object => captureProjectionObjectSegment selected.steps descriptors original
        | .map sourceIndex targetIndex => do
          let sourceImage ← completeIntermediateSlotWith reader fields actionIndex sourceIndex
          let targetImage ← completeIntermediateSlotWith reader fields actionIndex targetIndex
          let some first := selected.steps[0]?
            | throwError "the missing map lost its selected complete action"
          let some (originalSource, originalTarget) ←
              retainedCallableEndpoints? original first.sourceContext
            | throwError "the missing map lost its original complete endpoint occurrences"
          let mut current := original
          let mut source := originalSource
          let mut target := originalTarget
          for (step, position) in selected.steps.zipIdx do
            let some descriptor := descriptors[position]?
              | throwError "the intermediate map lost an original action parameter position"
            let final := position + 1 == selected.steps.size
            let sourceImage ← if final then pure sourceImage
              else captureProjectionObjectSegment #[step] #[descriptor] source
            let targetImage ← if final then pure targetImage
              else captureProjectionObjectSegment #[step] #[descriptor] target
            current ← captureProjectionMapStep step descriptor current sourceImage targetImage
            source := sourceImage
            target := targetImage
          pure current
      | .unavailable failure => failure.raise
    let completed ← forwardRetainedValue completed slot.formal
    checkCapturedResultInterface completed result
    if let .map context sourceIndex targetIndex := slot.role then
      let source ← completeIntermediateSlotWith reader fields actionIndex sourceIndex
      let target ← completeIntermediateSlotWith reader fields actionIndex targetIndex
      let some (actualSource, actualTarget) ← retainedCallableEndpoints? completed context
        | throwError "the completed intermediate map omitted its full endpoint occurrences"
      let actualSource ← forwardRetainedValue actualSource source.value
      let actualTarget ← forwardRetainedValue actualTarget target.value
      unless sameCompleteWireContext source actualSource &&
          sameCompleteWireContext target actualTarget do
        throwStratum .noImplementation
          "the intermediate map requires its exact selected image endpoint occurrences"
    cache.modify fun state => { state with
      values := state.values.push (actionIndex, index, completed) }
    return completed
  finally
    cache.modify fun state => { state with active := state.active.filter (· != key) }

end

/-- Execute both directions of one accepted alignment at the same retained
prefix and image occurrences. Constructor comparison actions use their existing
public component port, then the declared suffix map actions whisker its result. -/
def captureProjectionAlignmentStep (h : Harness) (selected : RecordProjectionAlignment)
    (original sourceImage targetImage : Wire) : TermElabM (Wire × Wire) := do
  let plan := selected.plan
  discard <| plan.checkedDeclaration
  let state ← registryState
  let some cell := state.cells.find? (·.id == plan.witness.cell)
    | throwError "the captured projection alignment lost its registered comparison"
  let preceding ← captureProjectionObjectSegment plan.before selected.before original
  let (declaredSource, declaredTarget) := if plan.inverse then
    (targetImage, sourceImage) else (sourceImage, targetImage)
  let left ← captureProjectionObjectSegment plan.left selected.left preceding
    (if plan.after.isEmpty then some declaredSource else none)
  let right ← captureProjectionObjectSegment plan.right selected.right preceding
    (if plan.after.isEmpty then some declaredTarget else none)
  let some context := left.categoryContext
    | throwError "the alignment component lost its complete target category"
  discard <| framingContext (some context) right.categoryContext
  let component ← mkAppM ``CategoryTheory.Iso.app #[plan.data.componentComparison, preceding.value]
  let (formalSource, formalTarget) ← operationComparisonEnds context component
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq formalSource left.value <&&> isDefEq formalTarget right.value) do
    throwError "the alignment component changed its complete selected images"
  let some form := state.componentForm? (cell.componentAddress plan.witness.constructors)
    | throwError "the alignment component lost its published complete input form"
  let capture := fun (inverse : Bool) (source target : Wire) => do
    let transformation ← mkAppM
      (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom)
      #[plan.data.componentComparison]
    let formal ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, preceding.value]
    CategoryContext.checkMorphism context formal source.value target.value
    let parameters : Array ActionDataTemplate := #[
      .array (selected.parameters.flatMap (·.templates)), .wire .object preceding,
      .literal { json := toJson inverse }]
    let base : ActionDataTemplate := .ctor "cellComponent"
      (#[.literal { json := toJson cell.id.raw }] ++ parameters)
    let descriptor := if plan.witness.constructors.isEmpty then base else
      ActionDataTemplate.ctor "constructedCellComponent" #[
        .literal { json := toJson (plan.witness.constructors.map (·.raw)) }, base]
    let (data, dependencies) ← renderCapturedActionData descriptor
    let wire : Wire := {
      form, payload := (← combinedRecipePayload formal data
        (dependencies ++ #[source, target])), categoryContext := some context }
    retainSelectedCallableInvocation h wire {
      address := cell.componentAddress plan.witness.constructors,
      application := transformation, formal, fragment := data, context,
      declarationParameters := selected.parameters, descriptor, parameters,
      source, target, sourceOrigin := .retained, targetOrigin := .retained,
      argument := (← selectedCallableIdentity context source) }
  let mut forward ← capture false left right
  let mut backward ← capture true right left
  let mut left := left
  let mut right := right
  unless plan.after.size == selected.after.size do
    throwError "the alignment suffix lost an original action descriptor"
  for (step, index) in plan.after.zipIdx do
    let some descriptor := selected.after[index]?
      | throwError "the alignment suffix lost its parameter positions"
    let nextLeft ← captureProjectionObjectSegment #[step] #[descriptor] left
      (if index + 1 == plan.after.size then some declaredSource else none)
    let nextRight ← captureProjectionObjectSegment #[step] #[descriptor] right
      (if index + 1 == plan.after.size then some declaredTarget else none)
    forward ← captureProjectionMapStep step descriptor forward nextLeft nextRight
    backward ← captureProjectionMapStep step descriptor backward nextRight nextLeft
    left := nextLeft
    right := nextRight
  let (selectedForward, selectedBackward) :=
    if plan.inverse then (backward, forward) else (forward, backward)
  let comparison ← if plan.inverse then mkAppM ``CategoryTheory.Iso.symm #[plan.data.comparison]
    else pure plan.data.comparison
  let component ← mkAppM ``CategoryTheory.Iso.app #[comparison, original.value]
  let completedForward ← forwardRetainedValue selectedForward
    (← mkAppM ``CategoryTheory.Iso.hom #[component])
  let completedBackward ← forwardRetainedValue selectedBackward
    (← mkAppM ``CategoryTheory.Iso.inv #[component])
  return (completedForward, completedBackward)

/-- Every cell in a composite alignment shares its exact adjacent image
occurrence. Distinct accepted routes keep their own action descriptors even
when their closed applications happen to be definitionally equal. -/
def captureProjectionAlignmentAt (h : Harness) (action : RecordProjectionAction)
    (original sourceImage targetImage : Wire) : TermElabM (Wire × Wire) := do
  unless action.alignment.size == action.plan.alignment.size && !action.alignment.isEmpty do
    throwError "the projection alignment omitted its selected comparison path"
  let mut current := sourceImage
  let mut forward : Option Wire := none
  let mut backward : Option Wire := none
  for (selected, index) in action.alignment.zipIdx do
    let target ← if index + 1 == action.alignment.size then pure targetImage else do
      let plan := selected.plan
      let steps := plan.before ++ (if plan.inverse then plan.left else plan.right) ++ plan.after
      let descriptors := selected.before ++
        (if plan.inverse then selected.left else selected.right) ++ selected.after
      captureProjectionObjectSegment steps descriptors original
    let (nextForward, nextBackward) ← captureProjectionAlignmentStep h selected original current target
    let some context := nextForward.categoryContext
      | throwError "the projection alignment lost its complete component category"
    forward ← match forward with
      | none => pure (some nextForward)
      | some previous => some <$> composeEndpointMaps context previous nextForward
    backward ← match backward with
      | none => pure (some nextBackward)
      | some previous => some <$> composeEndpointMaps context nextBackward previous
    current := target
  let (some completedForward, some completedBackward, some comparison) :=
      (forward, backward, action.plan.alignmentComparison)
    | throwError "the projection alignment lost its complete composite"
  let component ← mkAppM ``CategoryTheory.Iso.app #[comparison, original.value]
  return (← forwardRetainedValue completedForward (← mkAppM ``CategoryTheory.Iso.hom #[component]),
    ← forwardRetainedValue completedBackward (← mkAppM ``CategoryTheory.Iso.inv #[component]))

/-- A checked equality of formal maps permits reuse of their computational
occurrence. The proof comes from the accepted mathematical interface; it never
certifies any returned data. The original whole callable remains a typed child. -/
def captureProvedMapAlias (context : CategoryContext) (original : Wire)
    (formal proof : Expr) : TermElabM Wire := do
  let condition ← mkEq original.value formal
  unless ← Decide.kernelAccepts condition proof do
    throwError "the map alias lost its accepted equality at the complete selected endpoints"
  let some (source, target) ← retainedCallableEndpoints? original context
    | throwError "the proved map alias lost its original full endpoints"
  CategoryContext.checkMorphism context formal source.value target.value
  let template : ActionDataTemplate := .project #[] (.wire .map original)
  let output : Wire := {
    form := original.form, payload := (← combinedRecipePayload formal original.fragment #[original]),
    categoryContext := some context, morphismFramed := true }
  let output ← retainIntrinsicAssembly output .map context template
    #[{ context, source, target, callable := original }]
  retainCallableEndpoints output source target context

/-- Map a retained parent presentation through the canonical public projection.
The registered route and its accepted alignment execute all component maps; the
existing naturality theorem identifies their composite with the canonical map. -/
def retainAlignedProjectionPresentation (h : Harness) (action : RecordProjectionAction)
    (parent field : Wire) : TermElabM Wire := do
  let plan := action.plan
  let context := plan.targetContext
  let objectIso ← mapObjectComparison plan.projection parent.value parent.objectIso
  let some presentation := parent.endpointPresentation
    | return { field with objectIso }
  let (parentForward, parentBackward) ← endpointPresentationMaps parent plan.sourceContext presentation
  let some (semanticParent, actualParent) ← retainedCallableEndpoints? parentForward plan.sourceContext
    | throwError "the canonical projection lost the parent's complete comparison endpoints"
  let semanticField ← capturePublicRecordProjectionAt h semanticParent #[plan.step]
  let actualFormal ← Semantic.objOf plan.projection actualParent.value
  CategoryContext.checkObject context actualFormal
  let actualTemplate : ActionDataTemplate := .project #[] (.wire .retained field)
  let actualField : Wire := {
    form := field.form, payload := (← combinedRecipePayload actualFormal field.fragment #[field]),
    categoryContext := some context, objectObserved := field.objectObserved,
    serviceHandles := field.serviceHandles }
  let actualField ← retainIntrinsicAssembly actualField .object context actualTemplate
    #[] #[] (.retained, .retained)
  let mut semanticImage := semanticParent
  let mut actualImage := actualParent
  let mut mappedForward := parentForward
  let mut mappedBackward := parentBackward
  unless plan.steps.size == action.descriptors.size do
    throwError "the canonical projection lost its complete registered route"
  for (step, descriptor) in plan.steps.zip action.descriptors do
    let nextSemantic ← captureProjectionObjectSegment #[step] #[descriptor] semanticImage
    let nextActual ← captureProjectionObjectSegment #[step] #[descriptor] actualImage
    mappedForward ← captureProjectionMapStep step descriptor mappedForward nextSemantic nextActual
    mappedBackward ← captureProjectionMapStep step descriptor mappedBackward nextActual nextSemantic
    semanticImage := nextSemantic
    actualImage := nextActual
  let (semanticForward, semanticBackward) ←
    captureProjectionAlignmentAt h action semanticParent semanticImage semanticField
  let (actualForward, actualBackward) ←
    captureProjectionAlignmentAt h action actualParent actualImage actualField
  let forward ← composeEndpointMaps context semanticBackward
    (← composeEndpointMaps context mappedForward actualForward)
  let backward ← composeEndpointMaps context actualBackward
    (← composeEndpointMaps context mappedBackward semanticForward)
  let some forwardProof ← plan.mapAlignment parentForward.value
    | throwError "the nonidentity projection omitted its accepted naturality proof"
  let some backwardProof ← plan.mapAlignment parentBackward.value
    | throwError "the inverse projection omitted its accepted naturality proof"
  let forward ← captureProvedMapAlias context forward
    (← Semantic.mapOf plan.projection parentForward.value) forwardProof
  let backward ← captureProvedMapAlias context backward
    (← Semantic.mapOf plan.projection parentBackward.value) backwardProof
  let comparison ← mkAppM ``CategoryTheory.Functor.mapIso
    #[← Semantic.asFunctor plan.projection, presentation.comparison]
  let output : Wire := {
    form := field.form, payload := field.payload, categoryContext := some context,
    objectIso, objectObserved := field.objectObserved, serviceHandles := field.serviceHandles }
  let output ← retainIntrinsicAssembly output .object context actualTemplate
    #[] #[] (.retained, .retained)
  retainEndpointPresentationMaps output context comparison forward backward

/-- Propagate an existing complete object comparison through its accepted field
action. The actual child is retained as the exact image continuation; the mapped
comparison directions remain ordinary pending map actions. -/
def applyRecordFieldComparison (h : Harness) (selected : Option RecordProjectionAction)
    (parent : Wire) (step : ComputationalData.RecordFieldStep) (field : Wire)
    (endpoints : Option (Wire × Wire) := none)
    (origin : RecordFieldOrigin := .retained) : TermElabM Wire := do
  if parent.objectIso.isNone && parent.endpointPresentation.isNone then return field
  let selection ← selectPublicRecordField parent #[step]
  let field ← forwardRetainedValue field selection.formal
  checkCapturedResultInterface field selection.result
  let some source := parent.categoryContext
    | throwError "the presented record lost its complete selected category"
  match selection.result with
  | .object target =>
    let some action := selected
      | throwError "the field comparison lost its independently captured projection action"
    let plan := action.plan
    unless plan.steps.size == action.descriptors.size &&
        (!plan.steps.isEmpty || !plan.alignment.isEmpty) && plan.route.refs == plan.steps.map (·.edge) &&
        sameOperationFieldPath #[plan.step] #[step] do
      throwError "the field comparison lost its complete ordered projection route"
    discard <| framingContext (some source) (some plan.sourceContext)
    discard <| framingContext (some target) (some plan.targetContext)
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq plan.parent parent.value <&&> isDefEq plan.field field.value) do
      throwError "the field comparison changed its complete canonical public field"
    if !plan.alignment.isEmpty then
      return ← retainAlignedProjectionPresentation h action parent field
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq plan.application plan.projection) do
      throwError "the field comparison omitted its accepted projection alignment"
    let state ← registryState
    let mut current := parent
    for (selected, index) in plan.steps.zipIdx do
      let some descriptor := action.descriptors[index]?
        | throwError "the field route lost an original parameter template"
      discard <| selected.checkedDeclaration
      let (actualSource, actualTarget) ← actionOwnerContexts
        (.edge selected.edge) selected.application current false
      discard <| framingContext (some selected.sourceContext) (some actualSource)
      discard <| framingContext (some selected.targetContext) (some actualTarget)
      let formal ← Semantic.objOf selected.application current.value
      if index + 1 == plan.steps.size then
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType formal) (← inferType field.value) <&&>
              isDefEq formal field.value) do
          throwError "the complete projection route changed its selected field"
        let output : Wire := {
          form := field.form, payload := field.payload,
          objectIso := (← mapObjectComparison selected.application current.value current.objectIso),
          categoryContext := some target, objectObserved := field.objectObserved,
          serviceHandles := field.serviceHandles }
        -- This field is the exact final actual image. Intermediate action
        -- occurrences remain attached to their own original inputs and maps.
        let template := match origin with
          | .returned => ActionDataTemplate.literal field.fragment
          | .retained => .project #[] (.wire .object field)
        let output ← retainIntrinsicResultAssembly output (.object target) template
        let actualImage ← match origin with
          | .returned => pure none
          | .retained => some <$> endpointValidationView field target true
        return ← retainMappedEndpointPresentation (.edge selected.edge)
          selected.application current output descriptor actualImage
      let form := match CategoryContext.named? state selected.targetContext.expression with
        | some category => imageForm state selected.edge category
        | none => contextualForm state selected.targetContext current.form
      current ← captureRegisteredObjectAction (.edge selected.edge) selected.application
        current formal form selected.targetContext descriptor
    throwError "the complete projection route omitted its final field action"
  | .map context =>
    let some arrow ← StructuredProjection.arrow? parent.value source
      | throwStratum .noImplementation "the presented map field lacks its accepted complete Arrow interface"
    let comparison ← parent.objectIso.mapM arrow.arrowComparison
    let aligned ← alignedArrowHom arrow.arrow comparison
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType aligned) (← inferType field.value)) do
      throwError "the accepted Arrow comparison changed the selected defining-map interface"
    let selectedEndpoints ← match endpoints with
      | some endpoints => pure (some endpoints)
      | none => retainedCallableEndpoints? field context
    let some (domain, codomain) := selectedEndpoints
      | throwStratum .noImplementation "the presented defining map lost its exact updated endpoint fields"
    CategoryContext.checkMorphism context field.value domain.value codomain.value
    -- This local representation view preserves the original complete map as a
    -- typed child. The accepted whole-Arrow comparison fixes its actual field
    -- endpoints; reply validation will check them before the table is committed.
    let output : Wire := {
      form := field.form, payload := field.payload, categoryContext := some context,
      morphismFramed := true, callableObserved := field.callableObserved,
      serviceHandles := field.serviceHandles }
    let output ← retainCallableEndpoints output domain codomain context
    let template ← match origin with
      | .returned =>
        -- The enclosing reply/schema selects this new map. Its old local
        -- candidate was not a validated input at the precomparison Hom.
        pure (ActionDataTemplate.literal field.fragment)
      | .retained => do
        let some (oldSource, oldTarget) ← retainedCallableEndpoints? field context
          | throwError "the retained defining map lost its original full endpoint receipt"
        for (oldEndpoint, newEndpoint) in #[(oldSource, domain), (oldTarget, codomain)] do
          let oldActual ← endpointValidationView oldEndpoint context field.morphismFramed
          let newActual ← endpointValidationView newEndpoint context true
          let oldActual ← forwardRetainedValue oldActual newActual.value
          unless sameCompleteWireContext oldActual newActual do
            throwStratum .noImplementation
              "the retained defining map requires the exact actual endpoint occurrences selected by its comparison"
        pure (.project #[] (.wire .map field))
    retainIntrinsicResultAssembly output (.map context) template
  | .value _ =>
    throwStratum .noImplementation
      "the selected scalar field has no independently declared comparison action"

mutual

/-- Follow the same positional completion instructions before a descriptor
can read any final-reply supplier. Missing fields contribute their retained
inputs, parameter sources and explicit image endpoint dependencies. -/
partial def producedProjectionDependenciesWith (plan : RoutedResultPlan.Plan)
    (active : Array (Nat × Nat)) (actionIndex : Nat) :
    ComputationalData.RecordProjectionPlan → TermElabM (Array Nat)
  | .input path => do
    match plan.producedPaths actionIndex path with
    | #[selected] =>
      let some (index, _) ← routedResultPosition? plan selected
        | throwError "the intermediate parameter lost its declared output position"
      return #[index]
    | #[] =>
      let stage ← plan.stage actionIndex
      let some (index, _) ← routedSlotPosition? stage.slots path
        | throwStratum .noImplementation
            "the required intermediate parameter has no public result-field position"
      intermediateSlotDependenciesWith plan active actionIndex index
    | _ =>
      throwStratum .ambiguousRealization
        "the complete reply exposes distinct occurrences of one required intermediate parameter"
  | .record _ fields => do
    return (← fields.mapM
      (producedProjectionDependenciesWith plan active actionIndex)).flatMap id

partial def intermediateSlotDependenciesWith (plan : RoutedResultPlan.Plan)
    (active : Array (Nat × Nat)) (actionIndex index : Nat) : TermElabM (Array Nat) := do
  unless actionIndex < plan.prefixActions.size do
    throwError "an intermediate descriptor cannot depend on its own method result"
  let stage ← plan.stage actionIndex
  let some slot := stage.slots[index]?
    | throwError "the intermediate dependency lost a selected field position"
  if !(plan.producedPaths actionIndex slot.replyPath).isEmpty then
    return ← producedProjectionDependenciesWith plan active actionIndex (.input slot.replyPath)
  let key := (actionIndex, index)
  if active.contains key then
    throwStratum .noImplementation
      "the selected intermediate descriptor has cyclic field dependencies"
  let active := active.push key
  let some completion := stage.completions[index]?
    | throwError "the intermediate dependency lost its declared completion instruction"
  match completion with
  | .retained source => projectionSourceDependenciesWith plan active source
  | .record _ indices => do
    return (← indices.mapM
      (intermediateSlotDependenciesWith plan active actionIndex)).flatMap id
  | .action selected => do
    let mut dependencies ← projectionSourceDependenciesWith plan active selected.source
    for step in selected.steps do
      for parameter in step.parameters do
        dependencies := dependencies ++
          (← projectionSourceDependenciesWith plan active parameter.source)
    if let .map source target := selected.kind then
      dependencies := dependencies ++
        (← intermediateSlotDependenciesWith plan active actionIndex source) ++
        (← intermediateSlotDependenciesWith plan active actionIndex target)
    return dependencies
  | .unavailable failure => failure.raise

partial def projectionSourceDependenciesWith (plan : RoutedResultPlan.Plan)
    (active : Array (Nat × Nat)) :
    RoutedResultPlan.ProjectionParameterSource → TermElabM (Array Nat)
  | .intermediate actionIndex projection =>
    producedProjectionDependenciesWith plan active actionIndex projection
  | .record _ fields => do
    return (← fields.mapM (projectionSourceDependenciesWith plan active)).flatMap id
  | .retained .. | .literal _ => pure #[]

end

def producedProjectionDependencies (plan : RoutedResultPlan.Plan) (actionIndex : Nat) :
    ComputationalData.RecordProjectionPlan → TermElabM (Array Nat) :=
  producedProjectionDependenciesWith plan #[] actionIndex

def projectionSourceDependencies (plan : RoutedResultPlan.Plan) :
    RoutedResultPlan.ProjectionParameterSource → TermElabM (Array Nat) :=
  projectionSourceDependenciesWith plan #[]

/-- Presentation readiness and complete record readiness are different.
A parent supplies its accepted comparison before its children are completed;
a descriptor consuming the parent needs its completed typed children as well. -/
structure RecordFieldCompletion where
  values : Array Wire
  presented : Array Bool
  completed : Array Bool
  presenting : Array Nat := #[]
  completing : Array Nat := #[]

mutual

partial def prepareRecordResultFieldWith (h : Harness)
    (readAction : RetainedResultFields → Nat → Nat → TermElabM (Option RecordProjectionAction))
    (fields : RetainedResultFields) (completion : IO.Ref RecordFieldCompletion)
    (index : Nat) : TermElabM Unit := do
  if ((← completion.get).presented[index]?).getD false then return
  if (← completion.get).presenting.contains index then
    throwStratum .noImplementation
      "the selected field comparisons require a cyclic intermediate parameter occurrence"
  let some slot := fields.plan.slots[index]?
    | throwError "the result comparison lost a declared field position"
  completion.modify fun state => { state with presenting := state.presenting.push index }
  try
    unless slot.replyPath.isEmpty do
      let parentPath := slot.replyPath.extract 0 (slot.replyPath.size - 1)
      let parents := fields.plan.slots.mapIdx (fun position slot => (position, slot)) |>.filter
        (fun (_, candidate) => sameOperationFieldPath candidate.replyPath parentPath)
      let #[(parentIndex, _)] := parents
        | throwStratum .noImplementation
            "the result comparison requires its complete intermediate public record position"
      prepareRecordResultFieldWith h readAction fields completion parentIndex
      let some parent := (← completion.get).values[parentIndex]?
        | throwError "the result comparison lost its exact parent occurrence"
      unless parent.objectIso.isNone && parent.endpointPresentation.isNone do
        -- Descriptor dependencies are selected by the pure positional schema,
        -- before a reader can consume any of their computational packets.
        if let .object _ := slot.role then
          let action ← fields.plan.projectionAction parentIndex index
          for parameter in action.parameters do
            for dependency in (← projectionSourceDependencies fields.plan parameter.source) do
              completeRecordResultFieldWith h readAction fields completion dependency
        if let .map _ sourceIndex targetIndex := slot.role then
          completeRecordResultFieldWith h readAction fields completion sourceIndex
          completeRecordResultFieldWith h readAction fields completion targetIndex
        let current := { fields with values := (← completion.get).values }
        let some parent := current.values[parentIndex]?
          | throwError "the result comparison lost its completed parent presentation"
        let some field := current.values[index]?
          | throwError "the result comparison lost its exact field occurrence"
        let some step := slot.replyPath.back?
          | throwError "the nonempty public field lost its final declaration step"
        let endpoints ← match slot.role with
          | .map context sourceIndex targetIndex => do
            let some source := current.values[sourceIndex]?
              | throwError "the presented map lost its completed source field"
            let some target := current.values[targetIndex]?
              | throwError "the presented map lost its completed target field"
            CategoryContext.checkMorphism context field.value source.value target.value
            pure (some (source, target))
          | _ => pure none
        let action ← match slot.role with
          | .object _ => readAction current parentIndex index
          | _ => pure none
        let origin := match slot.node with
          | .retained .. => RecordFieldOrigin.retained
          | .returned | .record .. => RecordFieldOrigin.returned
        let updated ← applyRecordFieldComparison h action parent step field endpoints origin
        completion.modify fun state => { state with values := state.values.set! index updated }
    completion.modify fun state => { state with presented := state.presented.set! index true }
  finally
    completion.modify fun state => { state with
      presenting := state.presenting.filter (· != index) }

partial def completeRecordResultFieldWith (h : Harness)
    (readAction : RetainedResultFields → Nat → Nat → TermElabM (Option RecordProjectionAction))
    (fields : RetainedResultFields) (completion : IO.Ref RecordFieldCompletion)
    (index : Nat) : TermElabM Unit := do
  if ((← completion.get).completed[index]?).getD false then return
  if (← completion.get).completing.contains index then
    throwStratum .noImplementation
      "the selected result descriptors require a cyclic complete record occurrence"
  let some slot := fields.plan.slots[index]?
    | throwError "the result completion lost a declared field position"
  completion.modify fun state => { state with completing := state.completing.push index }
  try
    prepareRecordResultFieldWith h readAction fields completion index
    if let .record codec children := slot.node then
      for child in children do
        completeRecordResultFieldWith h readAction fields completion child
      let current := (← completion.get).values
      let mut actual := #[]
      for child in children do
        let some child := current[child]?
          | throwError "the result record lost a completed child occurrence"
        actual := actual.push child
      let some previous := current[index]?
        | throwError "the result record lost its current whole occurrence"
      let result : IntrinsicResultInterface := match slot.role with
        | .object context => .object context
        | .map context .. => .map context
        | .value => .value slot.expectedType
      let rebuilt ← assembleRetainedRecordWith codec actual slot.formal result previous.form
        (some previous.fragment)
      unless previous.fragment == rebuilt.fragment do
        throwError "completing a result record changed its positioned data or suppliers"
      if previous.capturedInvocation.isSome then
        throwError "an uncommitted result record already owns a captured computation"
      let updated := { previous with
        intrinsicAssembly := rebuilt.intrinsicAssembly
        serviceHandles := previous.serviceHandles ++ rebuilt.serviceHandles }
      completion.modify fun state => { state with values := state.values.set! index updated }
    completion.modify fun state => { state with completed := state.completed.set! index true }
  finally
    completion.modify fun state => { state with
      completing := state.completing.filter (· != index) }

end

/-- Complete accepted field comparisons over already checked actual data or
private prospective fields. Readers receive the current table after every
required parameter, parent and map endpoint has been completed. Dependencies
retain their ordinal positions, and active cycles never use a stale snapshot. -/
def retainRecordResultComparisonsWith (h : Harness)
    (readAction : RetainedResultFields → Nat → Nat → TermElabM (Option RecordProjectionAction))
    (fields : RetainedResultFields) : TermElabM RetainedResultFields := do
  unless fields.values.size == fields.plan.slots.size do
    throwError "the presented result omitted a declared positioned field"
  let completion ← IO.mkRef {
    values := fields.values,
    presented := Array.replicate fields.plan.slots.size false,
    completed := Array.replicate fields.plan.slots.size false : RecordFieldCompletion }
  for index in [:fields.plan.slots.size] do
    completeRecordResultFieldWith h readAction fields completion index
  return { fields with values := (← completion.get).values }

/-- A producer can expose a symbolically retained field before its unrelated
returned fields execute. The callback must use the original typed input roles. -/
abbrev PendingRecordFieldReader := Wire → ComputationalData.RecordFieldPath → TermElabM (Option Wire)

/-- The live or private table must authenticate the whole parent before making
its canonical fields available. All observation remains in the supplied reader. -/
structure RetainedRecordAccess where
  fields : Wire → TermElabM (Option RetainedResultFields)
  pendingField? : PendingRecordFieldReader := fun _ _ => pure none
  observe : IntrinsicResultInterface → Wire → TermElabM Wire
  presentField : RecordFieldOrigin → Wire → ComputationalData.RecordFieldStep → Wire → TermElabM Wire

/-- Read only an intrinsic producer's declared codec positions. This does not
look for matching bytes, infer an action, or reinterpret a leaf reply as a recipe. -/
partial def recordTemplateField? (template : ActionDataTemplate)
    (step : ComputationalData.RecordFieldStep) : Option ActionDataTemplate := do
  match actionTemplateExecution template with
  | .retained child => return .retained (← recordTemplateField? child step)
  | .object fields =>
    let #[(_, arguments)] := fields.filter (fun (key, _) => key == "args") | none
    let #[(_, tag)] := fields.filter (fun (key, _) => key == "ctor") | none
    if let .literal data := actionTemplateExecution tag then
      if data.json == toJson "valueData" then
        let .array #[child] := actionTemplateExecution arguments | none
        return ← recordTemplateField? child step
    if step.codec == .arrowRefinement && step.count == 1 && step.index == 0 then
      match actionTemplateExecution arguments with
      | .project path child =>
        unless path == #[.field "args"] do none
        return child
      | .array children =>
        unless children.size == 3 do none
        return .object (fields.map fun (key, child) =>
          (key, if key == "ctor" then .literal { json := toJson "arrow" } else child))
      | _ => none
    else
      let .array children := actionTemplateExecution arguments | none
      unless (step.codec == .core || step.codec == .arrow) &&
          children.size == step.count do none
      return ← children[step.index]?
  | .ctor "arrow" fields | .ctor "subobject" fields =>
    if step.codec == .arrow && step.count == 3 && fields.size == 3 then
      return ← fields[step.index]?
    if step.codec == .arrowRefinement && step.count == 1 && step.index == 0 && fields.size == 3 then
      return .ctor "arrow" fields
    none
  | .ctor "coreObject" fields =>
    unless step.codec == .core && step.count == 1 && step.index == 0 && fields.size == 1 do none
    return ← fields[0]?
  | .array fields =>
    unless step.codec == .ordered && step.count == fields.size && step.count != 1 do none
    return ← fields[step.index]?
  | _ =>
    unless (step.codec == .ordered || step.codec == .arrowRefinement) &&
        step.count == 1 && step.index == 0 do none
    return template

/-- Reassemble a selected intrinsic subtree from its full original Wire leaves.
Literal scalar data use their explicitly selected value interface. A missing
categorical child is left to the complete public-packet projection boundary. -/
partial def retainedRecordTemplate? (parent : Wire) (template : ActionDataTemplate)
    (formal : Expr) (result : IntrinsicResultInterface) (form : Form) :
    TermElabM (Option Wire) := do
  match actionTemplateExecution template with
  | .wire _ child =>
    let child ← forwardRetainedValue child formal
    checkCapturedResultInterface child result
    return some child
  | .retained child =>
    let some wire ← retainedRecordTemplate? parent child formal result form | return none
    let wire := { wire with
      actionRecipe := none, intrinsicAssembly := none, capturedInvocation := none,
      morphismFraming := none }
    return some (← retainIntrinsicResultAssembly wire result (.retained child))
  | .literal data =>
    let .value _ := result | return none
    let wire : Wire := {
      form, payload := (← scopedPayload formal data parent.completedData),
      serviceHandles := parent.serviceHandles }
    return some (← retainIntrinsicResultAssembly wire result (.literal data))
  | _ =>
    let (codec, fields) ← publicRecordFields formal result
    let state ← registryState
    let mut actual := #[]
    for field in fields do
      let some child := recordTemplateField? template field.step | return none
      let fieldForm := match field.result with
        | .object context => contextualForm state context form
        | .map context => contextualForm state context form true
        | .value _ => form
      let some child ← retainedRecordTemplate? parent child field.formal field.result fieldForm
        | return none
      actual := actual.push child
    let (packet, _) ← renderCapturedActionData template
    return some (← assembleRetainedRecordWith codec actual formal result form (some packet))

/-- A canonical table must describe precisely its completed or private parent.
Only the common invocation receipt is attached after the field fold commits. -/
def checkRetainedResultParent (parent : Wire) (fields : RetainedResultFields) : TermElabM Unit := do
  unless fields.values.size == fields.plan.slots.size do
    throwError "the canonical result table omitted a declared field position"
  let some output := fields.values[fields.plan.output]?
    | throwError "the canonical result table lost its complete output occurrence"
  let output ← forwardRetainedValue output parent.value
  unless sameCompleteWireContext output { parent with capturedInvocation := output.capturedInvocation } do
    throwStratum .unavailable "the result-field table describes a different complete parent occurrence"

/-- Earlier positions of a consumed named prefix remain separate producers.
The final prefix image is the exact presented receiver supplied to this method
invocation, not another execution of an action with the same formal image. -/
def materializeRoutedPrefixWith
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (routePrefix : RoutedPrefixInput) (receiver : Wire) :
    TermElabM (Array Wire × Array Wire) := do
  unless !routePrefix.actions.isEmpty && routePrefix.actions.size == routePrefix.descriptors.size &&
      routePrefix.actions.size == routePrefix.images.size do
    throwError "the named method prefix lost its original ordered producer positions"
  let mut current ← observe .object routePrefix.receiver
  let mut sources := #[]
  let mut images := #[]
  for ((edge, application), index) in routePrefix.actions.zipIdx do
    let some captured := routePrefix.images[index]?
      | throwError "the named method prefix lost a complete image interface"
    let formal ← Semantic.objOf application current.value
    let (_, context) ← actionOwnerContexts (.edge edge) application current false
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType formal) (← inferType captured.value) <&&>
          isDefEq formal captured.value) do
      throwError "the named method prefix changed an original complete stage"
    let actual ← if index + 1 == routePrefix.actions.size then
        forwardRetainedValue receiver formal
      else do
        let some descriptor := routePrefix.descriptors[index]?
          | throwError "the named method prefix lost an original action parameter position"
        let descriptor ← mapActionTemplateWires observe descriptor
        let pending ← captureRegisteredObjectAction (.edge edge) application current
          formal captured.form context descriptor
        observe .object pending
    let actual ← forwardRetainedValue actual formal
    checkCapturedResultInterface actual (.object context)
    sources := sources.push current
    images := images.push actual
    current := actual
  return (sources, images)

/-- A prescribed lift consumes the chosen base invocation's own forward-route
occurrences. Transported requests retain what they sent; fused replies preserve
their exposed fields and complete only the missing public stage slots. -/
def prescribedRouteInputsWith (reader : RetainedRecordReader)
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (selected : SelectedPrescribedInvocation) (base : Wire)
    (fields : RetainedResultFields) : TermElabM (Array Wire × Array Wire) := do
  checkRetainedResultParent base fields
  unless fields.plan.method == selected.method do
    throwError "the prescribed lift changed its selected base method"
  let some inputs := fields.inputs
    | throwStratum .unavailable "the prescribed base lost its exact materialized request receipt"
  let mut sources := inputs.routeSources
  let mut images := inputs.routeImages
  if let some routePrefix := inputs.«prefix» then
    unless sources.isEmpty && images.isEmpty && routePrefix.actions.size == inputs.routeOffset do
      throwError "the named method prefix changed its original route offset or acquired another receipt"
    let completed ← materializeRoutedPrefixWith observe routePrefix inputs.receiver
    sources := completed.1
    images := completed.2
  unless sources.size == inputs.routeOffset && images.size == inputs.routeOffset do
    throwError "the selected method boundary lost its original consumed-prefix positions"
  if !fields.plan.prefixActions.isEmpty then
    let some cache := fields.intermediates
      | throwStratum .unavailable "the prescribed base lost its intermediate completion scope"
    let mut current ← observe .object inputs.receiver
    for actionIndex in [:fields.plan.prefixActions.size] do
      let stage ← fields.plan.stage actionIndex
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType current.value) (← inferType stage.receiver) <&&>
            isDefEq current.value stage.receiver) do
        throwError "the prescribed stage changed its original complete source position"
      discard <| framingContext (some stage.sourceContext) current.categoryContext
      let captured ← completeIntermediateSlotWith reader fields actionIndex stage.output
      let actual ← observe .object captured
      let actual ← forwardRetainedValue actual stage.formal
      checkCapturedResultInterface actual (.object stage.resultContext)
      -- Update only this stage's positioned completion receipt. Public fields
      -- supplied by the final reply remain authoritative at every later read.
      let mut completed := #[]
      for (slot, index) in stage.slots.zipIdx do
        let field ← if slot.replyPath.isEmpty then pure actual
          else reader.readField actual slot.replyPath
        let field ← forwardRetainedValue field slot.formal
        checkCapturedResultInterface field (routedSlotInterface slot)
        completed := completed.push (actionIndex, index, field)
      cache.modify fun state => { state with
        values := state.values.filter (fun (action, _, _) => action != actionIndex) ++ completed }
      sources := sources.push current
      images := images.push actual
      current := actual
  unless sources.size == images.size do
    throwError "the prescribed route receipt lost a complete source or image position"
  let mut selectedSources := #[]
  let mut selectedImages := #[]
  for component in selected.plan.components do
    let some source := sources[component.routeIndex]?
      | throwStratum .unavailable "the base invocation omitted its prescribed route source receipt"
    let some image := images[component.routeIndex]?
      | throwStratum .unavailable "the base invocation omitted its prescribed route image receipt"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType source.value) (← inferType component.receiver) <&&>
          isDefEq source.value component.receiver <&&>
          isDefEq (← inferType image.value) (← inferType component.transportedSource) <&&>
            isDefEq image.value component.transportedSource) do
      throwError "the prescribed route receipt changed a complete independently selected interface"
    selectedSources := selectedSources.push source
    selectedImages := selectedImages.push image
  return (selectedSources, selectedImages)

/-- Read a field without first demanding unrelated intrinsic siblings. A
computed parent is consulted only when its own result is needed to expose the
field; its immutable table then supplies the exact canonical field Wire. -/
partial def readRetainedRecordFieldWith (access : RetainedRecordAccess) (original : Wire)
    (path : ComputationalData.RecordFieldPath) : TermElabM Wire := do
  if path.isEmpty then return original
  let selection ← selectPublicRecordField original path
  if let some assembly ← currentIntrinsicAssembly? original then
    if let .ctor "finiteData" #[.retained (.wire .object child), _] :=
        actionTemplateExecution assembly.template then
      let descriptor ← checkedFragment (original.fragment.project #[.field "args", .index 0])
      unless descriptor == child.fragment &&
          (← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType child.value) (← inferType original.value) <&&>
              isDefEq child.value original.value)) do
        throwStratum .unavailable "the inventory record view changed its original typed descriptor"
      checkCapturedResultInterface child assembly.result
      let field ← readRetainedRecordFieldWith access child path
      let field ← forwardRetainedValue field selection.formal
      checkCapturedResultInterface field selection.result
      return field
  if let some fields ← access.fields original then
    checkRetainedResultParent original fields
    let some (field, remaining) ← fields.project? path
      | throwError "the retained result schema omitted the selected field path"
    let field ← readRetainedRecordFieldWith access field remaining
    let field ← access.observe selection.result field
    let field ← forwardRetainedValue field selection.formal
    checkCapturedResultInterface field selection.result
    return field
  if let some field ← access.pendingField? original path then
    let field ← access.observe selection.result field
    let field ← forwardRetainedValue field selection.formal
    checkCapturedResultInterface field selection.result
    return field
  let some step := path[0]?
    | throwError "the public record selection lost its first field"
  let headSelection ← selectPublicRecordField original #[step]
  let state ← registryState
  let form := match headSelection.result with
    | .object context => contextualForm state context original.form
    | .map context => contextualForm state context original.form true
    | .value _ => original.form
  let mut retained : Option Wire := none
  if let some assembly ← currentIntrinsicAssembly? original then
    let (data, _) ← renderCapturedActionData assembly.template
    unless data == original.fragment do
      throwStratum .unavailable "the record projection changed its original intrinsic field data"
    let selectedTemplate := match actionTemplateExecution assembly.template with
      | .project path child => if path.isEmpty then actionTemplateExecution child else assembly.template
      | selected => selected
    if let .wire _ child := selectedTemplate then
      let isAlias ← withoutModifyingState <| withTransparency .all <|
        isDefEq (← inferType child.value) (← inferType original.value) <&&>
          isDefEq child.value original.value
      if isAlias then
        retained := some (← readRetainedRecordFieldWith access child #[step])
    if retained.isNone then
      if let some selected := recordTemplateField? assembly.template step then
        retained ← retainedRecordTemplate? original selected headSelection.formal headSelection.result form
  if retained.isNone && !original.completedData then
    let actual ← access.observe (← retainedRecordInterface original) original
    if sameCompleteWireContext original actual then
      throwStratum .noImplementation
        "the pending public record omitted its original typed field producer"
    return ← readRetainedRecordFieldWith access actual path
  let selected ← match retained with
    | some field => do
      let field ← access.observe headSelection.result field
      let field ← forwardRetainedValue field headSelection.formal
      checkCapturedResultInterface field headSelection.result
      access.presentField .retained original step field
    | none => do
      let projection := ComputationalData.RecordProjectionPlan.input #[step]
      let some data ← projection.projectData? original.value original.fragment
        | throwStratum .noImplementation "the complete result omits its selected public record field"
      -- This local candidate is never installed as a retained interface before
      -- the ordinary public validator accepts its independently selected role.
      let wire : Wire := {
        form, payload := (← scopedPayload headSelection.formal data),
        categoryContext := headSelection.result.context?,
        serviceHandles := original.serviceHandles }
      let wire ← match headSelection.result with
        | .map context => do
          let some (sourcePath, targetPath) := headSelection.endpoints
            | throwError "the selected record map lost its declared endpoint positions"
          let source ← readRetainedRecordFieldWith access original sourcePath
          let target ← readRetainedRecordFieldWith access original targetPath
          -- A returned field can be a raw graph or opaque callable. Its
          -- complete endpoint receipt does not rewrite the original packet.
          retainCallableEndpoints { wire with morphismFramed := true } source target context
        | _ => pure wire
      let wire ← access.presentField .returned original step wire
      let validation ← match headSelection.result with
        | .map context => do
          let some (source, target) ← retainedCallableEndpoints? wire context
            | throwError "the projected callable lost its complete original endpoint fields"
          let formal ← validationMapFormal wire context true
          let source ← endpointValidationView source context true
          let target ← endpointValidationView target context true
          -- Only already validated endpoint fields can supply positioned
          -- bindings. The new body and root have no trusted result binding.
          let some (sourcePath, targetPath) := headSelection.endpoints
            | throwError "the returned record map lost its fixed endpoint role positions"
          let targetIndex := if sameOperationFieldPath sourcePath targetPath then 0 else 1
          ComputationalData.validateEndpointSlots formal
            { index := 0, formal := source.value, data := source.fragment }
            { index := targetIndex, formal := target.value, data := target.fragment }
            wire.fragment (scope := some { data := wire.fragment })
        | .object context => do
          let actual ← endpointValidationView wire context true
          unless actual.fragment == wire.fragment do
            throwError "the selected object comparison changed the projected data or suppliers"
          ComputationalData.validatePort actual.value (← inferType actual.value) wire.json
            (scope := some { data := wire.fragment })
        | .value expected =>
          ComputationalData.validatePort headSelection.formal expected wire.json
            (scope := some { data := wire.fragment })
      if let .error message := validation then
        throwStratum .malformed m!"the public record field changed its complete declared interface: {message}"
      retainCompletedResultInterface wire headSelection.result
  let selected ← forwardRetainedValue selected headSelection.formal
  checkCapturedResultInterface selected headSelection.result
  let selected ← readRetainedRecordFieldWith access selected (path.extract 1 path.size)
  let selected ← forwardRetainedValue selected selection.formal
  checkCapturedResultInterface selected selection.result
  return selected

/-- An endpoint's actual validation view comes only from its retained comparison.
Other selected parameters keep their original full values. Repeated descriptor
keys must have the same complete source context before they can share a view. -/
def operationPresentationObjects (inputs : Array Wire)
    (views : Array (Wire × Expr) := #[]) (localInputs : Array Wire := #[]) :
    TermElabM ComputationalData.InterfaceObjects := do
  -- All explicitly retained comparisons are scoped before inspecting sibling
  -- components. Their typed operands do not become global aliases merely
  -- because an unrelated component was normalized first. Packet-only legacy
  -- metadata supplies no original typed operands to exclude here.
  let comparisonInputs ← IO.mkRef localInputs
  for input in inputs ++ views.map Prod.fst do
    if let some presentation := input.endpointPresentation then
      if let some (forward, _) := presentation.maps then
        let some context := input.categoryContext <|> forward.categoryContext
          | throwStratum .unavailable "the retained comparison lost its complete selected category"
        let (forward, backward) ← endpointPresentationMaps input context presentation
        for comparisonWire in #[forward, backward] do
          discard <| wireValidationScope .map comparisonWire (some context) (some comparisonInputs)
  let localInputs ← comparisonInputs.get
  -- Comparison dependencies occupy declared local slots. They are not global
  -- aliases merely because a service handle retains them. Selection here is
  -- exact complete occurrence identity, including every supplier and producer.
  let localInput := fun input => localInputs.any (sameCompleteWireContext input)
  let inputs := inputs.filter (! localInput ·)
  let views := views.filter fun (input, _) => !localInput input
  let mut retained : Array (Wire × Expr) := #[]
  for input in inputs ++ views.map Prod.fst do
    discard <| checkedFragment input.fragment.validate
    let matching := views.filter fun (source, _) => source.json == input.json
    let mut selected : Option Expr := none
    for (source, value) in matching do
      unless sameCompleteWireContext source input do
        throwStratum .ambiguousRealization
          "a comparison descriptor repeats distinct complete selected input contexts"
      if let some previous := selected then
        unless previous == value do
          throwStratum .ambiguousRealization
            "one complete comparison input has distinct actual endpoint views"
      selected := some value
    let actual := selected.getD input.value
    for (previous, value) in retained do
      if previous.json == input.json then
        unless sameCompleteWireContext previous input && value == actual do
          throwStratum .ambiguousRealization
            "a comparison descriptor repeats distinct complete typed parameter occurrences"
    retained := retained.push (input, actual)
  return retained.map fun (input, value) => (input.json, value)

/-- A new endpoint reference is tied to the complete selected comparison that
produced it. It cannot replace a different existing interface with equal bytes. -/
def operationInterfaceBinding (objects : ComputationalData.InterfaceObjects)
    (data : DataOwnership.Data) (value : Expr) : TermElabM ComputationalData.InterfaceObjects := do
  discard <| checkedFragment data.validate
  for (previous, selected) in objects do
    if previous == data.json && selected != value then
      throwStratum .ambiguousRealization
        "a comparison endpoint reference repeats a distinct complete selected interface"
  return objects.push (data.json, value)

/-- Private future bindings supplement an exact positioned interface. A declared
binding stays authoritative, and an incompatible complete type or value fails
before the ordinary validator reads any supplied computational data. -/
def mergeCallableInterfaceObjects (objects outerObjects : ComputationalData.InterfaceObjects) :
    TermElabM ComputationalData.InterfaceObjects := do
  let mut result := objects
  for (data, formal) in outerObjects do
    let matching := result.filter (·.1 == data)
    for (_, selected) in matching do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType selected) (← inferType formal) <&&>
            isDefEq selected formal) do
        throwStratum .ambiguousRealization
          "a private callable slot conflicts with its complete declared interface"
    if matching.isEmpty then result := result.push (data, formal)
  return result

/-- Original callable recipes and actual graph packets use their respective
existing validators. In particular, a formal finite carrier supplies no keys. -/
def validateOperationPresentationMap (formal : Expr) (source target data : DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects)
    (scope : Option ComputationalData.InterfaceScope := none) : TermElabM Unit := do
  if let some scope := scope then
    unless scope.data == data do
      throwStratum .unavailable "the local comparison scope changed the complete packet or suppliers"
    discard <| checkedFragment (scope.validate data.json)
  let .ok unwrapped := ComputationalData.valuePayload data.json
    | throwError "the operation comparison has an incomplete callable envelope"
  let callable := match Backend.TypedMap.decode unwrapped with
    | .ok typed => typed.callable
    | .error _ => unwrapped
  let .ok callable := ComputationalData.valuePayload callable
    | throwError "the operation comparison has an incomplete callable payload"
  let graph := if let .ok ("finiteGraph", #[_, values]) := ComputationalData.envelope callable
    then values else callable
  let checked ← withoutModifyingState <| if graph.getArr?.isOk then
    ComputationalData.validateEndpointPort formal source.json target.json data.json objects scope
  else do
    ComputationalData.validateCallableAt objects (← inferType formal) data.json scope
  if let .error message := checked then
    throwStratum .malformed m!"the operation comparison has incompatible complete framing: {message}"

structure OperationProductLegs where
  presentation : Expr
  first : Expr
  second : Expr
  firstData : DataOwnership.Data
  secondData : DataOwnership.Data
  firstTemplate : ActionDataTemplate
  secondTemplate : ActionDataTemplate

/-- The existing registered product cone supplies both projections and their
exact diagram indices. Forward and backward uses call this on different fixed
endpoint pairs, never reuse one side's descriptor for the other. -/
def operationProductLegs (context : CategoryContext) (first second : Expr)
    (firstData secondData : DataOwnership.Data)
    (components : Option (Wire × Wire) := none) : TermElabM OperationProductLegs := do
  let row ← operationProductRow
  let (diagram, presentation) ← operationProductCone context row first second
  let some constructor := diagram.getAppFn.constName?
    | throwError "the selected product diagram lost its registered declaration"
  let diagramData ← scopedNode (Codec.label constructor) #[firstData, secondData]
  let diagramTemplate : ActionDataTemplate ← match components with
    | none => pure (.literal diagramData)
    | some (left, right) => do
      for (wire, value, data) in #[(left, first, firstData), (right, second, secondData)] do
        discard <| framingContext (some context) wire.categoryContext
        unless wire.fragment == data && (← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType wire.value) (← inferType value) <&&>
              isDefEq wire.value value)) do
          throwError "the product leg changed its complete selected factor occurrence"
      pure (.ctor (Codec.label constructor) #[.wire .object left, .wire .object right])
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let expected ← mkAppM ``Prod #[first, second]
  let maps ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  let mut values := #[]
  let mut data := #[]
  let mut templates : Array ActionDataTemplate := #[]
  for name in #[``CategoryTheory.Limits.WalkingPair.left, ``CategoryTheory.Limits.WalkingPair.right] do
    let index ← mkAppM ``CategoryTheory.Discrete.mk #[mkConst name]
    let value ← mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
    let target := if values.isEmpty then first else second
    CategoryContext.checkMorphism context value expected target
    let .ok encoded ← Codec.encode index
      | throwError "the registered product index has no complete public codec"
    values := values.push value
    data := data.push (← scopedNode "limitLeg"
      #[{ json := toJson row.id.raw }, diagramData, { json := encoded }])
    templates := templates.push (.ctor "limitLeg" #[
      .literal { json := toJson row.id.raw }, diagramTemplate, .literal { json := encoded }])
  let #[firstTemplate, secondTemplate] := templates
    | throwError "the registered product lost its two ordered leg templates"
  return {
    presentation
    first := values[0]!
    second := values[1]!
    firstData := data[0]!
    secondData := data[1]!
    firstTemplate, secondTemplate }

structure OperationComponentPresentation where
  comparison : Expr
  actual : Expr
  semanticData : DataOwnership.Data
  forward : DataOwnership.Data
  backward : DataOwnership.Data
  forwardValue : Expr
  backwardValue : Expr
  semanticEndpoint : Wire
  actualEndpoint : Wire
  forwardWire : Wire
  backwardWire : Wire
  inputs : Array Wire
  objects : ComputationalData.InterfaceObjects

/-- Preserve the original selected component and its actual packet. The
semantic-side descriptor is projected only from its complete retained forward
comparison, with formal-name recovery disabled. -/
def operationComponentPresentation (context : CategoryContext) (wire : Wire)
    (inputs : Array Wire) (views : Array (Wire × Expr))
    (outerObjects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM OperationComponentPresentation := do
  CategoryContext.checkObject context wire.value
  discard <| framingContext (some context) wire.categoryContext
  let some presentation := wire.endpointPresentation | do
    let comparison ← mkAppOptM ``CategoryTheory.Iso.refl
      #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
        some wire.value]
    let value ← identityAtContext context wire.value
    let data ← scopedNode "identity" #[wire.fragment, wire.fragment]
    let identity : Wire := {
      form := contextualForm (← registryState) context wire.form true
      payload := (← combinedRecipePayload value data #[wire])
      categoryContext := some context, morphismFramed := true }
    let identity ← retainIntrinsicAssembly identity .map context
      (.ctor "identity" #[.wire .object wire, .wire .object wire])
    let identity ← retainCallableEndpoints identity wire wire context
    let localInputs ← IO.mkRef #[wire]
    let scope ← callableValidationScope identity context value (some localInputs)
    let objects ← operationPresentationObjects inputs (views.push (wire, wire.value)) (← localInputs.get)
    let objects ← mergeCallableInterfaceObjects objects outerObjects
    validateOperationPresentationMap value wire.fragment wire.fragment data objects (some scope)
    return {
      comparison
      actual := wire.value
      semanticData := wire.fragment
      forward := data
      backward := data
      forwardValue := value
      backwardValue := value
      semanticEndpoint := wire
      actualEndpoint := wire
      forwardWire := identity
      backwardWire := identity
      inputs
      objects }
  let (source, actual) ← operationComparisonEnds context presentation.comparison
  unless ← withoutModifyingState (withTransparency .all <| isDefEq source wire.value) do
    throwError "the component presentation starts at a different complete selected object"
  let forwardValue ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]
  let backwardValue ← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison]
  let (forwardWire, backwardWire) ← endpointPresentationMaps wire context presentation
  let some (semanticEndpoint, actualEndpoint) ← retainedCallableEndpoints? forwardWire context
    | throwError "the component comparison lost its complete retained endpoint occurrences"
  unless actualEndpoint.fragment == wire.fragment do
    throwStratum .unavailable "the component comparison changed its original actual packet or suppliers"
  let semanticData := semanticEndpoint.fragment
  let localInputs ← IO.mkRef #[wire]
  let forwardScope ← callableValidationScope forwardWire context forwardValue (some localInputs)
  let backwardScope ← callableValidationScope backwardWire context backwardValue (some localInputs)
  let objects ← operationPresentationObjects inputs (views.push (wire, actual)) (← localInputs.get)
  let objects ← mergeCallableInterfaceObjects objects outerObjects
  validateOperationPresentationMap forwardValue semanticData wire.fragment presentation.forwardFragment objects
    (some forwardScope)
  validateOperationPresentationMap backwardValue wire.fragment semanticData presentation.backwardFragment objects
    (some backwardScope)
  return {
    comparison := presentation.comparison
    actual
    semanticData
    forward := presentation.forwardFragment
    backward := presentation.backwardFragment
    forwardValue
    backwardValue
    semanticEndpoint
    actualEndpoint
    forwardWire
    backwardWire
    inputs
    objects }

/-- Build current comparisons only for the exact producer-recorded product.
The recursive child selections remain unchanged; derived current maps are kept
separately from them and from historical named-refinement comparisons. -/
def operationProductPresentation (h : Harness) (context : CategoryContext)
    (wire : Wire) (children : Array Wire) (views : Array (Wire × Expr))
    (parameters : Array Wire := #[]) (parameterHandles : Array Nat := #[])
    (outerObjects : ComputationalData.InterfaceObjects := #[]) : TermElabM Wire := do
  if wire.productComponents.isEmpty then return wire
  let #[originalFirst, originalSecond] := wire.productComponents
    | throwError "the product presentation changed its complete ordered component inventory"
  let product ← withTransparency .all <| whnf wire.value
  -- A transported tree can be provenance without still being a current product.
  unless product.isAppOfArity ``Prod 2 && wire.form.category == CategoryId.sets do return wire
  unless wire.fragment == (← scopedNode "objectProduct"
      #[originalFirst.fragment, originalSecond.fragment]) do return wire
  let fields := product.getAppArgs
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq originalFirst.value fields[0]! <&&> isDefEq originalSecond.value fields[1]!) do
    throwError "the current product presentation changed its independently fixed factors"
  CategoryContext.checkObject context wire.value
  discard <| framingContext (some context) wire.categoryContext
  let #[first, second] := children
    | throwError "the normalized product lost its original ordered component occurrences"
  for (original, current) in #[(originalFirst, first), (originalSecond, second)] do
    unless sameCompleteWireContext original { current with
        objectIso := original.objectIso, endpointPresentation := original.endpointPresentation } do
      throwError "product normalization changed the original complete component selection"
  if first.objectIso.isSome || second.objectIso.isSome ||
      first.endpointPresentation.isSome || second.endpointPresentation.isSome then
    checkOperationPointPresentation wire
  let mut objectIso := wire.objectIso
  if first.objectIso.isSome || second.objectIso.isSome then
    let firstIso ← match first.objectIso with
      | some iso => pure iso
      | none => mkAppM ``CategoryTheory.Iso.refl #[first.value]
    let secondIso ← match second.objectIso with
      | some iso => pure iso
      | none => mkAppM ``CategoryTheory.Iso.refl #[second.value]
    for (iso, selected) in #[(firstIso, first.value), (secondIso, second.value)] do
      let (_, target) ← operationComparisonEnds context iso
      unless ← withoutModifyingState (withTransparency .all <| isDefEq target selected) do
        throwError "a product object comparison targets a different complete selected component"
    let comparison ← operationProductIso context firstIso secondIso
    if let some retained := objectIso then
      unless retained == comparison do
        throwStratum .ambiguousRealization "the whole product has a conflicting complete object comparison"
    objectIso := some comparison
  unless first.endpointPresentation.isSome || second.endpointPresentation.isSome do
    return { wire with objectIso }
  let retained ← h.serviceOperands.get
  let mut inputs := parameters
  for child in #[first, second] do
    for handle in child.serviceHandles do
      let some input := retained[handle]?
        | throwError "the product comparison lost an exact declared parameter occurrence"
      inputs := inputs.push input
  let firstAction ← operationComponentPresentation context first inputs views outerObjects
  let secondAction ← operationComponentPresentation context second inputs views outerObjects
  let comparison ← operationProductIso context firstAction.comparison secondAction.comparison
  let (semantic, actual) ← operationComparisonEnds context comparison
  unless ← withoutModifyingState (withTransparency .all <| isDefEq semantic wire.value) do
    throwError "the product action starts at a different complete original product"
  let sourceData ← scopedNode "objectProduct" #[firstAction.semanticData, secondAction.semanticData]
  let state ← registryState
  let productEndpoint := fun (value : Expr) (data : DataOwnership.Data) (left right : Wire) => do
    let template : ActionDataTemplate := .ctor "objectProduct" #[.wire .object left, .wire .object right]
    let (retained, dependencies) ← renderCapturedActionData template
    unless retained == data do
      throwError "the product comparison changed its exact retained factor packets"
    let endpoint : Wire := {
      form := contextualForm state context wire.form
      payload := (← combinedRecipePayload value data dependencies)
      categoryContext := some context, productComponents := #[left, right] }
    retainIntrinsicAssembly endpoint .object context template
  let semanticEndpoint ← productEndpoint semantic sourceData
    firstAction.semanticEndpoint secondAction.semanticEndpoint
  let actualEndpoint ← productEndpoint actual wire.fragment
    firstAction.actualEndpoint secondAction.actualEndpoint
  let sourceLegs ← operationProductLegs context first.value second.value
    firstAction.semanticData secondAction.semanticData
    (some (firstAction.semanticEndpoint, secondAction.semanticEndpoint))
  let targetLegs ← operationProductLegs context firstAction.actual secondAction.actual
    first.fragment second.fragment (some (firstAction.actualEndpoint, secondAction.actualEndpoint))
  let forwardParts ← #[ (sourceLegs.firstData, firstAction.forward),
      (sourceLegs.secondData, secondAction.forward) ].mapM fun (leg, action) => scopedNode "compose" #[leg, action]
  let backwardParts ← #[ (targetLegs.firstData, firstAction.backward),
      (targetLegs.secondData, secondAction.backward) ].mapM fun (leg, action) => scopedNode "compose" #[leg, action]
  let forward ← scopedNode "typedMap" #[sourceData, wire.fragment,
    ← scopedNode "mediator" forwardParts]
  let backward ← scopedNode "typedMap" #[wire.fragment, sourceData,
    ← scopedNode "mediator" backwardParts]
  let forwardValue ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
  let backwardValue ← mkAppM ``CategoryTheory.Iso.inv #[comparison]
  -- Check that the encoded mediators are precisely the induced product maps.
  -- The explicit universal comparison also handles cones whose lift is opaque
  -- to definitional reduction; no alternate comparison or limit is selected.
  let sourcePresentationType ← whnfR (← inferType sourceLegs.presentation)
  let targetPresentationType ← whnfR (← inferType targetLegs.presentation)
  unless sourcePresentationType.isAppOf ``CategoryTheory.Limits.LimitCone &&
      targetPresentationType.isAppOf ``CategoryTheory.Limits.LimitCone do
    throwError "the product maps lost their complete selected universal presentations"
  let diagramComparison ← mkAppOptM ``CategoryTheory.Limits.mapPairIso #[
    some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
    some sourcePresentationType.appArg!, some targetPresentationType.appArg!,
    some firstAction.comparison, some secondAction.comparison]
  let sourceLimit ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[sourceLegs.presentation]
  let targetLimit ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[targetLegs.presentation]
  for (target, legs, firstMap, secondMap, expected, inverse) in
      #[(targetLegs.presentation, sourceLegs, firstAction.forwardValue, secondAction.forwardValue,
          forwardValue, false),
        (sourceLegs.presentation, targetLegs, firstAction.backwardValue, secondAction.backwardValue,
          backwardValue, true)] do
    let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk
      #[← mkAppM ``CategoryTheory.CategoryStruct.comp #[legs.first, firstMap],
        ← mkAppM ``CategoryTheory.CategoryStruct.comp #[legs.second, secondMap]]
    let limiting ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[target]
    let action ← mkAppM ``CategoryTheory.Limits.IsLimit.lift #[limiting, fan]
    discard <| StructuredResult.checkReconstruction action
    unless ← withoutModifyingState (withTransparency .all <| isDefEq action expected) do
      let mut equations := #[]
      for name in #[``CategoryTheory.Limits.WalkingPair.left, ``CategoryTheory.Limits.WalkingPair.right] do
        let index ← mkAppM ``CategoryTheory.Discrete.mk #[mkConst name]
        let supplied ← mkAppM (if inverse then
          ``CategoryTheory.Limits.IsLimit.conePointsIsoOfNatIso_inv_comp else
          ``CategoryTheory.Limits.IsLimit.conePointsIsoOfNatIso_hom_comp)
          #[sourceLimit, targetLimit, diagramComparison, index]
        let encoded ← mkAppM ``CategoryTheory.Limits.IsLimit.fac #[limiting, fan, index]
        equations := equations.push (← mkAppM ``Eq.trans
          #[encoded, ← mkAppM ``Eq.symm #[supplied]])
      let agreement ← StructuredResult.checkReconstruction
        (← mkAppM ``CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext
          #[limiting, equations[0]!, equations[1]!])
      unless ← Decide.kernelAccepts (← mkEq action expected) agreement do
        throwError "the public product action changed its complete declared comparison"
  let legWire := fun (value : Expr) (data : DataOwnership.Data) (template : ActionDataTemplate)
      (source target : Wire) => do
    let (_, dependencies) ← renderCapturedActionData template
    let comparisonMap : Wire := {
      form := contextualForm state context wire.form true
      payload := (← combinedRecipePayload value data dependencies)
      categoryContext := some context, morphismFramed := true }
    let comparisonMap ← retainIntrinsicAssembly comparisonMap .map context template
    retainCallableEndpoints comparisonMap source target context
  let sourceFirst ← legWire sourceLegs.first sourceLegs.firstData sourceLegs.firstTemplate
    semanticEndpoint firstAction.semanticEndpoint
  let sourceSecond ← legWire sourceLegs.second sourceLegs.secondData sourceLegs.secondTemplate
    semanticEndpoint secondAction.semanticEndpoint
  let targetFirst ← legWire targetLegs.first targetLegs.firstData targetLegs.firstTemplate
    actualEndpoint firstAction.actualEndpoint
  let targetSecond ← legWire targetLegs.second targetLegs.secondData targetLegs.secondTemplate
    actualEndpoint secondAction.actualEndpoint
  let forwardFirst ← composeEndpointMaps context sourceFirst firstAction.forwardWire
  let forwardSecond ← composeEndpointMaps context sourceSecond secondAction.forwardWire
  let backwardFirst ← composeEndpointMaps context targetFirst firstAction.backwardWire
  let backwardSecond ← composeEndpointMaps context targetSecond secondAction.backwardWire
  let mediator := fun (value : Expr) (data : DataOwnership.Data) (source target : Wire)
      (first second firstTarget secondTarget : Wire) => do
    let template : ActionDataTemplate := .ctor "typedMap" #[
      .wire .object source, .wire .object target,
      .ctor "mediator" #[.wire .map first, .wire .map second]]
    let (_, dependencies) ← renderCapturedActionData template
    let comparisonMap : Wire := {
      form := contextualForm state context wire.form true
      payload := (← combinedRecipePayload value data dependencies)
      categoryContext := some context, morphismFramed := true,
      serviceHandles := wire.serviceHandles ++ parameterHandles }
    let comparisonMap ← retainIntrinsicAssembly comparisonMap .map context template
      #[{ context, source, target := firstTarget, callable := first },
        { context, source, target := secondTarget, callable := second }]
    retainCallableEndpoints comparisonMap source target context
  let forwardWire ← mediator forwardValue forward semanticEndpoint actualEndpoint
    forwardFirst forwardSecond firstAction.actualEndpoint secondAction.actualEndpoint
  let backwardWire ← mediator backwardValue backward actualEndpoint semanticEndpoint
    backwardFirst backwardSecond firstAction.semanticEndpoint secondAction.semanticEndpoint
  let localInputs ← IO.mkRef #[wire, first, second]
  let forwardScope ← callableValidationScope forwardWire context forwardValue (some localInputs)
  let backwardScope ← callableValidationScope backwardWire context backwardValue (some localInputs)
  let objects ← operationPresentationObjects inputs
    (views ++ #[(first, firstAction.actual), (second, secondAction.actual)]) (← localInputs.get)
  let objects ← mergeCallableInterfaceObjects objects outerObjects
  validateOperationPresentationMap forwardValue sourceData wire.fragment forward objects
    (some forwardScope)
  validateOperationPresentationMap backwardValue wire.fragment sourceData backward objects
    (some backwardScope)
  let result ← retainEndpointPresentationMaps { wire with objectIso } context comparison
    forwardWire backwardWire
  let some presentation := result.endpointPresentation | unreachable!
  if let some original := wire.endpointPresentation then
    unless original.comparison == presentation.comparison &&
        original.forwardFragment == presentation.forwardFragment &&
        original.backwardFragment == presentation.backwardFragment do
      throwStratum .ambiguousRealization "the whole product has a conflicting complete endpoint action"
    if original.maps.isSome && !sameEndpointComparisonMaps original.maps presentation.maps then
      throwStratum .ambiguousRealization
        "the whole product has different complete comparison-map occurrences"
  let maps := #[firstAction.forwardWire, firstAction.backwardWire,
    secondAction.forwardWire, secondAction.backwardWire, forwardWire, backwardWire]
  let handles ← retainServiceOperands h maps
  return { result with
    serviceHandles := wire.serviceHandles ++ handles }

/-- One request-local graph rewrite. The memo is indexed only by exact old
operand handles; original entries are never overwritten or selected by data. -/
structure OperationProductNormalization where
  harness : Harness
  context : CategoryContext
  original : Array Wire
  memo : IO.Ref (Std.HashMap Nat Nat)
  parameters : Array Wire := #[]
  parameterHandles : Array Nat := #[]
  outerObjects : ComputationalData.InterfaceObjects := #[]

mutual

partial def normalizedOperationHandle (scope : OperationProductNormalization)
    (handle : Nat) (active : Array Nat) : TermElabM Nat := do
  if active.contains handle then
    throwError "the operation product has cyclic exact dependency occurrences"
  if let some normalized := (← scope.memo.get)[handle]? then return normalized
  let some original := scope.original[handle]?
    | throwError "the operation product lost an original exact dependency occurrence"
  let (normalized, _) ← normalizedOperationWire scope original (active.push handle)
  let #[fresh] ← retainServiceOperands scope.harness #[normalized]
    | throwError "the normalized product dependency lost its exact occurrence"
  scope.memo.modify (·.insert handle fresh |>.insert fresh fresh)
  return fresh

partial def normalizedOperationWire (scope : OperationProductNormalization)
    (wire : Wire) (active : Array Nat := #[]) : TermElabM (Wire × Array (Wire × Expr)) := do
  let dependencies ← wire.serviceHandles.mapM fun handle =>
    normalizedOperationHandle scope handle active
  let children ← wire.productComponents.mapM fun child => normalizedOperationWire scope child active
  let views := children.foldl (fun views child => views ++ child.2) #[]
  let children := children.map Prod.fst
  let childHandles ← retainServiceOperands scope.harness children
  for handle in childHandles do scope.memo.modify (·.insert handle handle)
  -- The original child tree remains selection provenance. Lookup receives the
  -- normalized child occurrences through fresh handles, never both versions.
  let original := { wire with
    serviceHandles := dependencies ++ childHandles }
  let normalized ← operationProductPresentation scope.harness scope.context original children views
    scope.parameters scope.parameterHandles scope.outerObjects
  -- New comparison map Wires depend only on the already normalized inputs.
  -- They cannot point back to the aggregate currently under construction.
  for handle in normalized.serviceHandles do
    if handle >= scope.original.size then scope.memo.modify (·.insert handle handle)
  let mut views := views
  if normalized.form.category == CategoryId.sets &&
      (← whnfR (← inferType normalized.value)).isSort then
    if let some presentation := normalized.endpointPresentation then
      let (source, actual) ← operationComparisonEnds scope.context presentation.comparison
      unless ← withoutModifyingState (withTransparency .all <| isDefEq source normalized.value) do
        throwError "the normalized endpoint changed its complete original comparison source"
      views := views.push (normalized, actual)
  return (normalized, views)

end

/-- Expand only the normalized dependency graph. Traversing the original
productComponents again here would expose metadata-poor aliases to lookup. -/
partial def normalizedOperationClosure (retained : Array Wire) (wire : Wire)
    (active : Array Nat := #[]) : TermElabM (Array Nat) := do
  let mut result := #[]
  for handle in wire.serviceHandles do
    if active.contains handle then throwError "the normalized product dependency graph is cyclic"
    let some input := retained[handle]?
      | throwError "the normalized product lost an exact retained input"
    result := result.push handle
    result := result ++ (← normalizedOperationClosure retained input (active.push handle))
  return result

/-- Normalize all copied product occurrences before service lookup, including
nested exact dependencies and source aliases. Duplicate occurrences and their
order remain; no context-free product is enriched from equal descriptor bytes. -/
def normalizeOperationProducts (h : Harness) (context : CategoryContext)
    (wires parameters : Array Wire) (outerObjects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Array Wire × Array Nat) := do
  let original ← h.serviceOperands.get
  -- Validate the original graph before appending any new handle: a dangling
  -- original index cannot accidentally resolve to a newly allocated entry.
  for wire in wires ++ parameters do
    discard <| operationPresentationOperandClosure original wire
  let scope : OperationProductNormalization := {
    harness := h, context, original, outerObjects, memo := (← IO.mkRef {}) }
  let parameters ← parameters.mapM fun wire => return (← normalizedOperationWire scope wire).1
  let parameterHandles ← retainServiceOperands h parameters
  for handle in parameterHandles do scope.memo.modify (·.insert handle handle)
  let scope := { scope with parameters, parameterHandles }
  let normalized ← wires.mapM fun wire => return (← normalizedOperationWire scope wire).1
  let handles ← retainServiceOperands h normalized
  let retained ← h.serviceOperands.get
  let mut inherited := #[]
  for wire in normalized do
    inherited := inherited ++ (← normalizedOperationClosure retained wire)
  return (normalized, handles ++ inherited)

def operationRecipeId? (wire : Wire) : Option String :=
  match ComputationalData.envelope wire.json with
  | .ok ("element", #[_, expression]) =>
      match ComputationalData.envelope expression with
      | .ok ("operationExpression", #[operationId, _, _]) => operationId.getStr?.toOption
      | _ => none
  | .ok ("operationPoint", #[operationId, _, _, _, _]) => operationId.getStr?.toOption
  | _ => none

def operationRecipe (wire : Wire) (id : OperationId) : Bool :=
  operationRecipeId? wire == some id.raw

/-- Read the literal inner action from the constructor's published interface,
after the whole selected action has been checked independently. -/
def constructorActionArgument (state : RegistryState) (constructor : ConstructorId)
    (actual : Expr) : TermElabM Expr := do
  let some name := (state.constructor? constructor).bind (·.functorialAction)
    | throwError "the selected constructor has no complete action on functors"
  let mut application := (← instantiateMVars actual).consumeMData.headBeta
  while application.isAppOfArity ``id 2 do
    application := application.appArg!.consumeMData.headBeta
  unless application.getAppFn.isConstOf name do
    throwError "the selected constructor lost its original complete action application"
  let infos ← forallTelescopeReducing (← inferType application.getAppFn) fun fields _ =>
    fields.mapM (·.fvarId!.getBinderInfo)
  let explicit := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none
  let #[original] := explicit
    | throwError "the selected constructor changed its complete inner functor interface"
  return original

/-- Preserve the selected declaration's own parameter occurrences. A strict
execution demand uses the existing whole-action checker, never traversal order. -/
def actionDeclarationParameters (state : RegistryState) (edge : EdgeRef)
    (actual : Expr) (strict : Bool) : TermElabM (Array Expr) := do
  let declaration ← match edge with
    | .functor id =>
      let some entry := state.functor? id | throwError "the selected action is not registered"
      pure entry.declaration
    | .classifierForget id =>
      let some entry := state.classifiers.find? (·.id == id)
        | throwError "the selected classifier is not registered"
      pure entry.declaration
    | _ => throwError "a constructed action requires its complete inner descriptor"
  let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
    fields.mapM (·.fvarId!.getBinderInfo)
  let actual ← instantiateMVars actual
  let application ← if strict then do
    let some selected ← FunctorActionData.registeredAction? state actual
      | throwError "the executable descriptor lost its whole selected action application"
    unless selected.edge == edge do
      throwError "the executable descriptor selected a different registered edge"
    pure selected.declarationApplication
  else do
    let some application := actual.find? fun term =>
        term.getAppFn.constName? == some declaration && term.getAppNumArgs == infos.size
      | throwError "the complete selected action application was lost"
    pure application
  return (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none

/-- Named functors keep their existing parameter vector; derived addresses carry
the complete already public nested action as their single framing parameter. -/
def edgeActionInvocation (state : RegistryState) (edge : EdgeRef) (descriptor : Json)
    (morphismAction : Bool) : TermElabM (String × Array Json) := do
  match edge with
  | .functor id =>
    let some entry := state.functor? id | throwError "the selected functor is no longer registered"
    let .ok parameters := (descriptor.getObjVal? "args").bind (·.getArr?)
      | throwError "the executable action lost its complete ordered parameters"
    pure ((if morphismAction then entry.mapAddress else id.raw), parameters)
  | _ => pure ((if morphismAction then edgeActionMapAddress edge else edgeActionAddress edge),
      #[descriptor])

def edgeActionDataInvocation (state : RegistryState) (edge : EdgeRef)
    (descriptor : DataOwnership.Data) (morphismAction : Bool) :
    TermElabM (String × Array DataOwnership.Data) := do
  let (operation, parameters) ← edgeActionInvocation state edge descriptor.json morphismAction
  let fragments ← match edge with
    | .functor _ =>
      let some fragments := fragmentArguments? descriptor
        | throwError "the executable action lost its parameter positions"
      pure fragments
    | _ => pure #[descriptor]
  unless fragments.map (·.json) == parameters do
    throwError "the executable action changed its complete parameter framing"
  return (operation, fragments)

/-- Preserve a whole reply at the exact endpoint fragments fixed by its
validated invocation. Equality includes every positioned supplying session. -/
def retainMapEndpointFragments (received : Wire) (source target : DataOwnership.Data) :
    TermElabM Wire := do
  let some actual := ComputationalData.recordPayload? received.fragment
    | throwStratum .malformed "the whole callable has an incomplete transparent data envelope"
  if (Backend.TypedMap.decode actual.json).isOk then
    let left ← checkedFragment (actual.project #[.field "args", .index 0])
    let right ← checkedFragment (actual.project #[.field "args", .index 1])
    unless left == source && right == target do
      throwStratum .malformed
        "the returned whole callable changed an independently supplied endpoint occurrence"
    return { received with
      morphismFramed := true, morphismFraming := none, actionRecipe := none,
      intrinsicAssembly := none, callableEndpoints := none }
  let framed ← scopedNode "typedMap" #[source, target, received.fragment]
  return { received with
    payload := (← scopedPayload received.value framed)
    morphismFramed := true, morphismFraming := none, actionRecipe := none,
    intrinsicAssembly := none, callableEndpoints := none }

/-- The completed invocation fixes its category and exact endpoint occurrences.
The named result form supplies a missing complete context only through the
existing typed category constructor; the whole Hom is checked before retention. -/
def completedCallableContext (received source target : Wire) : TermElabM CategoryContext := do
  let context ← framingContext received.categoryContext source.categoryContext
  let context ← framingContext context target.categoryContext
  let context ← match context with
    | some context => pure context
    | none =>
      let some category := (← registryState).categories.find? (·.id == received.form.category)
        | throwError "the completed invocation omitted its complete declared category"
      CategoryContext.ofNamed category source.value
  CategoryContext.checkMorphism context received.value source.value target.value
  return context

def retainMapImageEndpoints (received source target : Wire) : TermElabM Wire := do
  let context ← completedCallableContext received source target
  let actual ← retainMapEndpointFragments received source.fragment target.fragment
  -- The reply was checked at these actual endpoint packets. Its endpoint
  -- comparisons have already been consumed by this invocation's whole-map role.
  retainCallableEndpoints actual source target context

/-- A closed-point reply keeps its value interface; every generalized reply
keeps the complete endpoints supplied to its whole-map validator. -/
def retainPointOrMapEndpoints (received source target : Wire) : TermElabM Wire := do
  if let some selected := received.pointDataInterface then
    unless selected.domainData == source.fragment && selected.targetData == target.fragment &&
        (← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType selected.domain) (← inferType source.value) <&&>
            isDefEq selected.domain source.value <&&>
            isDefEq (← inferType selected.target) (← inferType target.value) <&&>
              isDefEq selected.target target.value)) do
      throwError "the completed point changed its original endpoint interface"
    let received := { received with
      morphismFramed := false, morphismFraming := none,
      actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none }
    return ← retainCallableEndpoints received source target
      (← completedCallableContext received source target)
  retainMapImageEndpoints received source target

/-- Check the service producer's already selected result interface before any
implementation runs. Endpoint fields supply data, never formal object choices. -/
def checkServiceCallableInterface (prepared : ServiceRequest.Prepared) : TermElabM Unit := do
  if let some (sourceOperand, targetOperand) := prepared.callableEndpointOperands then
    let some (.endpoints domain target domainData targetData) := prepared.callableInterface
      | throwError "the service attached endpoint occurrences to a different result interface"
    for (formal, data, operand) in #[(domain, domainData, sourceOperand),
        (target, targetData, targetOperand)] do
      unless data == operand.fragment &&
          (← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType operand.value) (← inferType formal) <&&>
              isDefEq operand.value formal)) do
        throwError "the service changed an independently selected endpoint occurrence"
  match prepared.callableInterface with
  | none =>
    if prepared.callableResult || prepared.pointResult then
      throwError "the typed service omitted its independently selected result interface"
  | some .framed =>
    unless prepared.callableResult && !prepared.pointResult do
      throwError "the service changed its complete returned-map result role"
  | some (.endpoints domain target domainData targetData) =>
    unless prepared.callableResult || prepared.pointResult do
      throwError "the service attached callable endpoints to a different result role"
    discard <| checkedFragment domainData.validate
    discard <| checkedFragment targetData.validate
    match prepared.resultContext with
    | some context => CategoryContext.checkMorphism context prepared.result domain target
    | none =>
      let some (source, codomain) := Language.homEnds? (← inferType prepared.result)
        | throwError "the service result lost its complete callable signature"
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType source) (← inferType domain) <&&>
            isDefEq source domain <&&>
            isDefEq (← inferType codomain) (← inferType target) <&&>
              isDefEq codomain target) do
        throwError "the service result changed its complete selected endpoints"
    if prepared.pointResult then
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq domain (← ServiceRequest.closedElementDomain)) do
        throwError "the service point result lost its selected global-point domain"

/-- Preserve the result interface chosen by a typed service preparer. Some
universal ports require a complete returned frame and permit validated endpoint
enrichment; other ports retain the exact original invocation endpoint packets. -/
def retainServiceCallableResult (prepared : ServiceRequest.Prepared) (received : Wire)
    (endpoints : Option (Wire × Wire) := none) : TermElabM Wire := do
  unless endpoints.isSome == prepared.callableEndpointOperands.isSome do
    throwError "the completed service lost its original endpoint occurrence handles"
  match prepared.callableInterface with
  | none => return received
  | some .framed =>
    let some actual := ComputationalData.recordPayload? received.fragment
      | throwStratum .malformed "the service reply has an incomplete transparent data envelope"
    unless (Backend.TypedMap.decode actual.json).isOk do
      throwStratum .malformed "the service reply omitted its required complete callable frame"
    return { received with
      morphismFramed := true, morphismFraming := none,
      actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none }
  | some (.endpoints domain target domainData targetData) =>
    if prepared.pointResult then
      let some selected ← pointDataInterfaceAt domain target domainData targetData
        | throwError "the completed service point changed its selected result interface"
      let received := { received with pointDataInterface := some selected }
      if let some (source, target) := endpoints then
        return ← retainPointOrMapEndpoints received source target
      return received
    if let some (source, target) := endpoints then
      return ← retainMapImageEndpoints received source target
    retainMapEndpointFragments received domainData targetData

/-- A retained packet belongs to the complete formal selection that produced it.
No equality or selection information is inferred from its returned data. -/
partial def checkRetainedLiftPlan (expected actual : SelectedLift.Plan) : TermElabM Unit := do
  unless expected.entry.id == actual.entry.id &&
      expected.parameters.size == actual.parameters.size &&
      expected.ports.size == actual.ports.size do
    throwError "the selected lift packet changed its registered declaration or full arity"
  let fixed := #[expected.evidence, expected.computation, expected.action,
    expected.source, expected.inclusion, expected.monic] ++ expected.parameters ++ expected.ports
  let retained := #[actual.evidence, actual.computation, actual.action,
    actual.source, actual.inclusion, actual.monic] ++ actual.parameters ++ actual.ports
  for (left, right) in fixed.zip retained do
    unless ← withTransparency .all <| isDefEq left right do
      throwError "the selected lift packet changed its complete formal invocation"

partial def liftProjectionWith {α : Type} [Inhabited α] (execution : LiftExecution) (index : Nat)
    (output : Nat → Nat → TermElabM α) (action : Nat → TermElabM α)
    (baseApex : TermElabM α) (node : String → Array α → TermElabM α) : TermElabM α := do
  let some first := execution.outputs[0]?
    | throwError "the complete lift cache has no output fields"
  let some _ := first[index]? | throwError "the lift projection is not a public field"
  let initial ← output 0 index
  if index < 2 then return initial
  let mut result := initial
  for step in List.range (execution.outputs.size - 1) do
    let next := step + 1
    let mapped ← node "map" #[← action next, result]
    let nextOutput ← output next index
    result ← node "compose" (if index == 2 then #[mapped, nextOutput]
      else #[nextOutput, mapped])
  let base ← baseApex
  let mut image ← output 0 0
  for position in [:execution.actions.size] do
    image ← node "functorAction" #[← action position, image]
  node "typedMap" (if index == 2 then #[image, base, result] else #[base, image, result])

/-- Metadata inspection retains the old JSON interface without assigning owners
to legacy unannotated fixtures. Runtime consumers use `liftProjectionFragment`. -/
partial def liftProjectionData (execution : LiftExecution) (index : Nat) : TermElabM Json :=
  liftProjectionWith execution index
    (fun stage field => pure (execution.outputs[stage]!)[field]!)
    (fun stage => pure execution.actions[stage]!)
    (do
      let .ok base := LiftedSubobjectData.subobjectFields execution.bases.back!
        | throwError "the retained lift lost its original complete base"
      pure base[0]!)
    (fun tag args => pure (Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]))

partial def liftProjectionFragment (execution : LiftExecution) (index : Nat) :
    TermElabM DataOwnership.Data := do
  let execution ← scopedLiftExecution execution
  liftProjectionWith execution index
    (fun stage field => do
      let some output := (← execution.outputFragments stage)[field]?
        | throwError "the retained lift omitted a public output field"
      pure output)
    execution.actionFragment
    (do
      let base ← execution.baseFragment (execution.bases.size - 1)
      let .ok _ := LiftedSubobjectData.subobjectFields base.json
        | throwError "the retained lift lost its original complete base"
      checkedFragment (base.project #[.field "args", .index 0]))
    scopedNode

/-- Typed stage operands remain in their original runtime slots. JSON and scope
checks authenticate those slots; they never select an equal-valued replacement. -/
structure RetainedLiftStage where
  action : Wire
  source : Wire
  sourceImage : Wire
  base : Wire
  baseObject : Wire
  comparisonImage : Wire
  outputs : Array Wire

def retainedLiftStage (h : Harness) (execution : LiftExecution) (index : Nat) :
    TermElabM RetainedLiftStage := do
  let some selection := execution.selections[index]?
    | throwError "the retained lift stage is outside its selected route"
  let some handles := execution.stageHandles[index]?
    | throwStratum .noImplementation "the legacy lift packet has no complete typed execution occurrences"
  let sourceContext ← SelectedLift.context selection
  let targetContext ← SelectedLift.context selection true
  let operands ← h.serviceOperands.get
  let some action := operands[handles.action]?
    | throwStratum .unavailable "the selected lift action's original runtime scope has expired"
  unless action.fragment == (← execution.actionFragment index) do
    throwStratum .unavailable "the retained lift changed its positioned action data or supplier"
  checkDataOwners h action.fragment
  let action ← forwardRetainedValue action selection.action
  checkCapturedResultInterface action (.value (← inferType selection.action))
  let read := fun (handle : Nat) (formal : Expr) (context : CategoryContext)
      (data : DataOwnership.Data) (morphism : Bool) => do
    let some original := operands[handle]?
      | throwStratum .unavailable "the lift operand's original runtime scope has expired"
    unless original.fragment == data do
      throwStratum .unavailable "the retained lift changed its positioned packet or supplier"
    checkDataOwners h original.fragment
    let original ← forwardRetainedValue original formal
    checkCapturedResultInterface original (if morphism then .map context else .object context)
    return original
  let source ← read handles.source selection.source sourceContext
    (← execution.sourceFragment index) false
  let some sourceImageData ← execution.sourceImageFragment? index
    | throwError "the typed lift stage omitted its selected actual source image"
  let sourceImage ← read handles.sourceImage (← Semantic.objOf selection.action selection.source)
    targetContext sourceImageData false
  let (baseObjectFormal, _) ← contextualMorphismEndpoints targetContext selection.inclusion
  let baseData ← execution.baseFragment index
  let some base := operands[handles.base]?
    | throwStratum .unavailable "the complete lift base's runtime scope has expired"
  unless base.fragment == baseData do
    throwStratum .unavailable "the retained lift changed its original complete base occurrence"
  let expectedBase ← selectedLiftBaseOperand selection base.form baseData
  let base ← forwardRetainedValue base expectedBase.value
  discard <| framingContext expectedBase.categoryContext base.categoryContext
  checkDataOwners h base.fragment
  let baseObjectData ← checkedFragment (baseData.project #[.field "args", .index 0])
  let baseObject ← read handles.baseObject baseObjectFormal targetContext baseObjectData false
  let data ← execution.outputFragments index
  unless data.size == 4 && handles.outputs.size == 4 do
    throwError "the retained lift omitted a complete typed output position"
  let mut outputs := #[]
  for field in [:4] do
    let some handle := handles.outputs[field]?
      | throwError "the retained lift lost an original output handle"
    let some formal := selection.ports[field]?
      | throwError "the retained lift lost an original formal port"
    let some data := data[field]?
      | throwError "the retained lift lost an original output packet"
    outputs := outputs.push (← read handle formal
      (if field < 2 then sourceContext else targetContext) data (field != 0))
  let some object := outputs[0]?
    | throwError "the retained lift lost its actual object output"
  let some comparisonImageData ← execution.comparisonImageFragment? index
    | throwError "the typed lift stage omitted its actual comparison image"
  let comparisonImage ← read handles.comparisonImage (← Semantic.objOf selection.action object.value)
    targetContext comparisonImageData false
  return { action, source, sourceImage, base, baseObject, comparisonImage, outputs }

/-- A complete factor input retains the selected endpoint descriptors even
when a finite inventory enriches them. This checks framing and suppliers only;
it does not prove the requested factor equation or a returned mathematical law. -/
def checkLiftFactorMapEndpoints (context : CategoryContext) (wire source target : Wire) :
    TermElabM Unit := do
  CategoryContext.checkMorphism context wire.value source.value target.value
  let some (actualSource, actualTarget) ← retainedCallableEndpoints? wire context
    | throwError "the factor input lost its complete retained callable endpoints"
  for (expected, actual) in #[(source, actualSource), (target, actualTarget)] do
    discard <| framingContext (some context) actual.categoryContext
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq expected.value actual.value) do
      throwError "the factor input changed a fixed formal endpoint"
    discard <| liftEndpointOperand expected context actual.fragment
  let scope ← wireValidationScope .map wire (some context) (mapView := .logical)
  if let .error message ← LiftedSubobjectData.validateMap wire.value source.json target.json
      wire.json (scope := some scope) then
    throwStratum .malformed m!"the factor input changed its complete declared endpoints: {message}"

/-- Use an already retained inventory at a descriptor-only map target. The
existing `finiteData` rule relates these exact occurrences; it supplies neither
a mathematical comparison nor correctness evidence. An existing inventory is
never replaced or erased, and the original complete map remains a typed child. -/
def enrichLiftMapTarget (h : Harness) (context : CategoryContext)
    (original target : Wire) : TermElabM Wire := do
  let some (source, originalTarget) ← retainedCallableEndpoints? original context
    | throwError "the lift map adaptation lost its original complete endpoints"
  let target ← forwardRetainedValue target originalTarget.value
  discard <| framingContext (some context) target.categoryContext
  checkLiftFactorMapEndpoints context original source originalTarget
  if target.fragment == originalTarget.fragment then return original
  let targetHasInventory := (target.json.getObjValAs? String "ctor").toOption == some "finiteData"
  let originalHasInventory := (originalTarget.json.getObjValAs? String "ctor").toOption == some "finiteData"
  if !targetHasInventory || originalHasInventory then
    -- Preserve an already supplied enrichment when the required role is its
    -- descriptor. Every other difference remains subject to the old validator.
    checkLiftFactorMapEndpoints context original source target
    return original
  discard <| liftEndpointOperand originalTarget context target.fragment
  let result ← captureInventoryMapEndpoints context original source target
  let result := { result with serviceHandles := result.serviceHandles ++
    (← retainLiftOperands h #[original, source, target]) }
  checkLiftFactorMapEndpoints context result source target
  return result

/-- Complete comparisons compose through ordinary registered map actions. The
next stage's returned comparison fixes the exact image of the middle object;
only the missing image of the outer apex remains a pending object action. -/
def captureLiftFields (h : Harness) (execution : LiftExecution) :
    TermElabM (Array Wire) := do
  let first ← retainedLiftStage h execution 0
  let #[object, inclusion, initialForward, initialBackward] := first.outputs
    | throwError "the complete lift lost its four typed output occurrences"
  let mut forward := initialForward
  let mut backward := initialBackward
  for index in [:execution.selections.size - 1] do
    let position := index + 1
    let stage ← retainedLiftStage h execution position
    let some selection := execution.selections[position]?
      | throwError "the composed lift lost its next selected stage"
    let #[_, _, nextForward, nextBackward] := stage.outputs
      | throwError "the next lift omitted its complete comparison maps"
    let sourceContext ← SelectedLift.context selection
    let targetContext ← SelectedLift.context selection true
    let some (domain, middle) ← retainedCallableEndpoints? forward sourceContext
      | throwError "the composed forward comparison lost its complete original endpoints"
    let some (reverseMiddle, reverseDomain) ← retainedCallableEndpoints? backward sourceContext
      | throwError "the composed inverse comparison lost its complete original endpoints"
    for (expected, actual) in #[(domain, reverseDomain), (middle, reverseMiddle)] do
      discard <| framingContext (some sourceContext) actual.categoryContext
      let actual ← forwardRetainedValue actual expected.value
      discard <| liftEndpointOperand expected sourceContext actual.fragment
    let some (middleImage, target) ← retainedCallableEndpoints? nextForward targetContext
      | throwError "the next forward comparison lost its actual complete endpoints"
    let some (reverseTarget, reverseImage) ← retainedCallableEndpoints? nextBackward targetContext
      | throwError "the next inverse comparison lost its actual complete endpoints"
    for (expected, actual) in #[(target, reverseTarget), (middleImage, reverseImage)] do
      discard <| framingContext (some targetContext) actual.categoryContext
      let actual ← forwardRetainedValue actual expected.value
      discard <| liftEndpointOperand expected targetContext actual.fragment
    let inner ← SelectedLift.innerEdge (← registryState) selection.entry
    let descriptor := ActionDataTemplate.wire .parameter stage.action
    let domainImage ← captureRegisteredObjectAction (.edge inner) selection.action domain
      (← Semantic.objOf selection.action domain.value)
      (contextualForm (← registryState) targetContext domain.form) targetContext descriptor
    let mappedForward ← captureRegisteredMapAction (.edge inner) selection.action descriptor
      forward domainImage middleImage
    let mappedBackward ← captureRegisteredMapAction (.edge inner) selection.action descriptor
      backward reverseImage domainImage
    forward ← composeEndpointMaps targetContext mappedForward nextForward
    backward ← composeEndpointMaps targetContext nextBackward mappedBackward
  return #[object, inclusion,
    ← forwardRetainedValue forward (← SelectedLift.port execution.selections 2),
    ← forwardRetainedValue backward (← SelectedLift.port execution.selections 3)]

/-- A checked operand retains the complete original type and observation role.
Its ordinal is supplied by its selected request, never recovered from a packet. -/
def invocationOperand (role : ActionDataRole) (wire : Wire) : TermElabM InvocationOperand := do
  return { formal := wire.value, expectedType := ← inferType wire.value, role, wire }

def checkInvocationOperand (selected : InvocationOperand) (returned : Wire) :
    TermElabM Wire := do
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType returned.value) selected.expectedType <&&>
        isDefEq returned.value selected.formal) do
    throwError "a dependency return changed its selected complete operand type or value"
  let returned ← forwardRetainedValue returned selected.formal
  match selected.role, selected.wire.categoryContext with
  | .object, some context => checkCapturedResultInterface returned (.object context)
  | .map, some context => checkCapturedResultInterface returned (.map context)
  | .parameter, _ =>
      checkCapturedResultInterface returned (← retainedRecordInterface selected.wire)
  | .retained, _ =>
      unless sameCompleteWireContext returned selected.wire do
        throwError "a retained dependency changed its original complete occurrence"
  | _, _ => pure ()
  return returned

/-- Assemble a direct lift only from its ordered validated dependency returns.
The same assembly is used by inert prospective admission and actual execution. -/
structure DirectLiftInputs where
  input : LiftStageExecution.Input Wire
  form : Form
  actionValue : Wire
  dependencies : Array Wire
  staticInputPaths : Array (DataOwnership.Path × Nat)

def directLiftInputs (h : Harness) (selected : SelectedDirectLiftInvocation)
    (returned : Array Wire) : TermElabM DirectLiftInputs := do
  unless selected.operands.size == returned.size do
    throwError "the direct lift lost an ordered dependency return"
  let returned ← (selected.operands.zip returned).mapM fun (operand, value) =>
    checkInvocationOperand operand value
  let some source := returned[0]?
    | throwError "the direct lift omitted its original source occurrence"
  let some inclusion := returned[1]?
    | throwError "the direct lift omitted its original base inclusion occurrence"
  let source ← captureDeclaredObjectInput source selected.context
  let plan := selected.plan
  let targetContext ← SelectedLift.context plan true
  let some (baseSource, baseTarget) ← retainedCallableEndpoints? inclusion targetContext
    | throwError "the direct lift's inclusion lost its complete endpoint occurrences"
  let baseTarget ← forwardRetainedValue baseTarget (← Semantic.objOf plan.action source.value)
  let cursor ← IO.mkRef 2
  let read := fun (role : ActionDataRole) (original : Wire) => do
    let index ← cursor.get
    let some operand := selected.operands[index]?
      | throwError "the direct lift descriptor exceeded its selected operand positions"
    unless operand.role == role && sameCompleteWireContext operand.wire original do
      throwError "the direct lift descriptor changed its original positioned operand"
    let some value := returned[index]?
      | throwError "the direct lift descriptor omitted a dependency return"
    cursor.set (index + 1)
    pure value
  let descriptor ← mapActionTemplateWires read selected.descriptor
  let parameterTemplates ← selected.parameters.mapM (mapActionTemplateWires read)
  unless (← cursor.get) == returned.size do
    throwError "the direct lift retained an unconsumed dependency position"
  let (action, actionWires) ← renderCapturedActionData descriptor
  let renderedParameters ← parameterTemplates.mapM renderCapturedActionData
  let parameters := DataOwnership.Data.array (renderedParameters.map (·.1))
  let actionValue ← retainedLiftActionValue plan source.form descriptor
  let base ← scopedNode "subobject" #[baseSource.fragment, baseTarget.fragment, inclusion.fragment]
  let some form := (← registryState).liftInputForm? plan.entry.inputAddress
    | throwError "the selected lift has no published complete input form"
  let baseOperand ← selectedLiftBaseOperand plan form base
  let baseOperand := { baseOperand with
    payload := (← scopedPayload baseOperand.value base), objectObserved := true,
    serviceHandles := (← retainLiftOperands h #[inclusion, baseSource, baseTarget]) }
  let some baseContext := baseOperand.categoryContext
    | throwError "the selected base lost its complete subobject category"
  let baseOperand ← retainIntrinsicAssembly baseOperand .object baseContext
    (.ctor "subobject" #[.wire .object baseSource, .wire .object baseTarget, .wire .map inclusion])
  let input : LiftStageExecution.Input Wire := {
    selection := plan, originalArrow := false, action, parameters,
    original := source, source, base := baseOperand, baseObject := baseSource,
    sourceImage? := some baseTarget, sourceImageObject? := some baseTarget }
  let descriptorInputs ← actionTemplateInputPaths descriptor
  let parameterInputs ← actionTemplateInputPaths (.array parameterTemplates)
  let positions :=
    descriptorInputs.map (fun (path, wire) => (#[.field "args", .index 1] ++ path, wire)) ++
    parameterInputs.map (fun (path, wire) => (#[.field "parameters"] ++ path, wire)) ++
    #[(#[.field "args", .index 3, .field "args", .index 0], baseSource),
      (#[.field "args", .index 3, .field "args", .index 1], baseTarget),
      (#[.field "args", .index 3, .field "args", .index 2], inclusion)]
  let firstRequest ← LiftStageExecution.packet "monoLiftInput" plan.entry.id.raw
    parameters action source.fragment base #[] (some baseTarget.fragment)
  let staticInputPaths ← retainServiceInputPaths h firstRequest positions
  return {
    input := input
    form := form
    actionValue := actionValue
    staticInputPaths := staticInputPaths
    dependencies := returned ++ #[baseSource, baseTarget, baseOperand, actionValue] ++
      actionWires ++ renderedParameters.flatMap (·.2) }

/-- Retain the completed four-field result without exporting an alternate
expression-keyed completion. Only the invocation owner commits this result. -/
def directLiftResult (h : Harness) (selected : SelectedDirectLiftInvocation)
    (prepared : DirectLiftInputs) (result : LiftStageExecution.Result Wire) : TermElabM Wire := do
  let input := prepared.input
  let some baseTarget := input.sourceImageObject?
    | throwError "the direct lift lost its selected source image occurrence"
  let stageHandles ← retainLiftStageHandles h input result prepared.actionValue
  let stageHandles := { stageHandles with staticInputPaths := prepared.staticInputPaths }
  let .arr parameters := input.parameters.json
    | throwError "the selected lift lost its ordered parameter data"
  let execution : LiftExecution := {
    selections := #[selected.plan], actions := #[input.action.json], parameters := #[parameters],
    sources := #[input.source.json], bases := #[input.base.json], outputs := #[result.outputs.map (·.json)],
    sourceImages := #[baseTarget.json], comparisonImages := #[result.comparisonImage.json],
    stageHandles := #[stageHandles],
    actionOwnership := #[input.action.ownership], parameterOwnership := #[input.parameters.ownership],
    sourceOwnership := #[input.source.ownership], baseOwnership := #[input.base.ownership],
    outputOwnership := #[result.outputs.map (·.ownership)],
    sourceImageOwnership := #[baseTarget.ownership],
    comparisonImageOwnership := #[result.comparisonImage.ownership] }
  let handles := stageHandles.all ++ (← retainLiftOperands h
    (prepared.dependencies ++ result.outputs ++ #[result.comparisonImage]))
  let some object := result.outputs[0]?
    | throwError "the completed selected lift lost its actual object output"
  return {
    form := contextualForm (← registryState) selected.context input.source.form,
    payload := (← scopedPayload selected.formal object.fragment),
    objectObserved := true, liftExecution := some execution,
    categoryContext := some selected.context, serviceHandles := handles }

/-- Cache the entire output interface at exact formal expressions. In particular the
object field retains the complete selected suffix, so taking it does not discard lifts. -/
partial def cacheLiftFields (h : Harness) (execution : LiftExecution)
    (owner : Option (String × Nat)) (serviceHandles : Array Nat := #[]) : TermElabM Unit := do
  let execution ← scopedLiftExecution execution owner
  let state ← registryState
  for start in [:execution.selections.size] do
    let suffix : LiftExecution := {
      selections := execution.selections.extract start execution.selections.size,
      actions := execution.actions.extract start execution.actions.size,
      parameters := execution.parameters.extract start execution.parameters.size,
      sources := execution.sources.extract start execution.sources.size,
      bases := execution.bases.extract start execution.bases.size,
      outputs := execution.outputs.extract start execution.outputs.size
      actionOwnership := execution.actionOwnership.extract start execution.actionOwnership.size
      parameterOwnership := execution.parameterOwnership.extract start execution.parameterOwnership.size
      sourceOwnership := execution.sourceOwnership.extract start execution.sourceOwnership.size
      baseOwnership := execution.baseOwnership.extract start execution.baseOwnership.size
      outputOwnership := execution.outputOwnership.extract start execution.outputOwnership.size
      sourceImages := execution.sourceImages.extract start execution.sourceImages.size
      comparisonImages := execution.comparisonImages.extract start execution.comparisonImages.size
      sourceImageOwnership := execution.sourceImageOwnership.extract start execution.sourceImageOwnership.size
      comparisonImageOwnership := execution.comparisonImageOwnership.extract start execution.comparisonImageOwnership.size
      stageHandles := execution.stageHandles.extract start execution.stageHandles.size }
    if !suffix.stageHandles.isEmpty then
      let fields ← captureLiftFields h suffix
      for (field, index) in fields.zipIdx do
        let formal ← SelectedLift.port suffix.selections index
        let field ← forwardRetainedValue field formal
        let field := { field with
          liftExecution := if index == 0 then some suffix else none,
          serviceHandles := serviceHandles ++ suffix.stageHandles.flatMap (·.all) ++ field.serviceHandles }
        h.results.modify (·.insert formal field)
      continue
    -- Explicit compatibility for historical recipe-only packets. New actual
    -- executions retain their typed handles and use the shared action capture.
    for index in [:4] do
      let formal ← SelectedLift.port suffix.selections index
      let some selection := if index < 2 then suffix.selections[0]?
          else suffix.selections.back?
        | throwError "the complete selected suffix is empty"
      let context ← SelectedLift.context selection (index >= 2)
      let some origin := state.liftInputForm? selection.entry.inputAddress
        | throwError "the cached lift field lost its complete input address"
      let data ← liftProjectionFragment suffix index
      let wire : Wire := {
        form := contextualForm state context origin (index != 0),
        payload := (← if index < 2 then scopedPayload formal data else recipePayload formal data),
        liftExecution := if index == 0 then some suffix else none
        categoryContext := some context, serviceHandles }
      h.results.modify (·.insert formal wire)

/-- Dispatch exactly the already selected request. A failed answer never selects
another equivalent operation, and returned data are never replaced by a formal value. -/
partial def dispatchOperationObservation (h : Harness) (request : OperationObservation)
    (selected : Option Registration := none) :
    TermElabM Wire := do
  if request.materialized then return request.original
  let state ← registryState
  let formal := request.original.value
  let reply ← sendData h request.operation.raw request.input (completeRequest := true)
    (selected := selected)
  let answer := reply.data.json
  let backend := reply.backend
  let checked ← if ← withTransparency .all <|
      isDefEq request.domain (← closedElementDomain state) then
    ComputationalData.validateElementAt request.target request.targetData
      (← pointResultValue state formal) answer
  else
    let .ok invocation := Backend.PointInvocation.decode request.input.json
      | throwError "the prepared operation lost its complete invocation"
    ComputationalData.validateEndpointPort formal invocation.domain request.targetData answer
  if let .error message := checked then malformed backend request.operation.raw answer message
  let data ← receiveReplyData h request.operation.raw reply true
  let result : Wire := { request.original with
    payload := .computed formal data, callableObserved := true
    morphismFraming := none
    pointDataInterface := (← pointInvocationInterface formal request.input.fragment) }
  -- A generalized reply is a whole map. Its actual invocation owns both
  -- endpoint packets, even when the implementation returns only an opaque body.
  retainPointOrMapEndpoints result request.domainWire request.targetWire

/-- Execute the object projection of an already selected complete functor.
This is shared by ordinary registered functors and dependent constructions.
Only the actual returned packet determines output portability; the source and
all of its owners remain in the internal action receipt. -/
def executeObjectActionWith (observe : Wire → TermElabM Wire)
    (h : Harness) (operation : String)
    (action : Expr) (original template : Wire) (parameters : Array Json)
    (dependencies : Array Wire) (parameterOwnership : DataOwnership.Table := #[])
    (requestInputPaths : Option (Array (DataOwnership.Path × Nat)) := none) :
    TermElabM Wire := do
  let action ← instantiateMVars (← Semantic.asFunctor action)
  unless FunctorActionData.closedParameter action && (← isTypeCorrect action) do
    throwError "the executable object action lost its complete selected functor"
  let original ← observe original
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  if let some context := original.categoryContext then
    unless ← withoutModifyingState (withTransparency .all <| isDefEq sourceBundle context.bundle) do
      throwError "the executable object action changed its retained full source category"
  if let some context := template.categoryContext then
    unless ← withoutModifyingState (withTransparency .all <| isDefEq targetBundle context.bundle) do
      throwError "the executable object action changed its retained full target category"
  let expected ← Semantic.objOf action original.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType expected) (← inferType template.value) <&&>
        isDefEq expected template.value) do
    throwError "the executable object action changed its fixed full result"
  if let some actual ← retainedActionResult? h operation action original parameters dependencies #[]
      parameterOwnership then
    return ← forwardRetainedValue actual template.value
  let state ← registryState
  let some declared := state.operation? operation
    | throwError "the executable object action has no accepted operation address"
  let inputForm ← match declared with
    | .functor _ => pure original.form
    | .construction entry false =>
      let some form := state.constructionForm? entry.inputAddress
        | throwError "the construction lost its complete request input"
      pure form
    | .edgeAction edge false =>
      let some form := state.edgeActionInputForm? (edgeActionInputAddress edge)
        | throwError "the derived object action lost its complete request input"
      pure form
    | _ => throwError "the executable object action does not name a functor projection"
  let invocation : Backend.ConstructionInvocation := {
    construction := operation, parameters, receiver := original.json }
  let request : Wire := {
    form := inputForm
    payload := (← combinedRecipePayload original.value
      (← placedData invocation.encode #[
        (#[.field "args"], { json := Json.arr parameters, ownership := parameterOwnership }),
        (#[.field "receiver"], original.fragment)]) (#[original] ++ dependencies))
    serviceHandles := (← retainServiceOperands h (#[original] ++ dependencies)),
    serviceInputPaths := requestInputPaths }
  let request ← match requestInputPaths with
    | none => pure request
    | some paths => do
      let paths ← replaceServiceInputPaths h request.fragment paths
        #[(#[.field "receiver"], original)]
      pure { request with serviceInputPaths := some paths }
  let reply ← sendData h operation request (completeRequest := true)
  let answer := reply.data.json
  let backend := reply.backend
  if let .error message ← ComputationalData.validatePort template.value
      (← inferType template.value) answer then
    malformed backend operation answer message
  let data ← receiveReplyData h operation reply true
  let result := { template with
    payload := WirePayload.computed template.value data
    serviceHandles := request.serviceHandles ++ template.serviceHandles
    objectObserved := true }
  retainActionResult h {
    operation, action, input := original, parameters, parameterOwnership
    parameterInputs := dependencies, result }
  return result

/-- Execute the selected complete map after its two object images. The request
uses the existing whole-domain invocation with an identity at the actual image
source. It retains the original source-category map and all endpoint packets.
Returned data are checked at those exact images, without proving any map law. -/
def executeMapActionWithEndpoints
    (endpoint : Wire → Option CategoryContext → Expr → Bool → TermElabM Wire)
    (frame : Wire → Wire → Wire → Option CategoryContext → TermElabM Wire)
    (h : Harness) (operation : String)
    (action : Expr) (sourceContext targetContext : CategoryContext)
    (original template : Wire) (descriptor : Json) (parameters : Array Json)
    (dependencies : Array Wire) (objectImage : Wire → TermElabM Wire)
    (descriptorOwnership : DataOwnership.Table := #[])
    (parameterOwnership : DataOwnership.Table := #[])
    (imageEndpoints : Option (Wire × Wire) := none)
    (requestInputPaths : Option (Array (DataOwnership.Path × Nat)) := none) : TermElabM Wire := do
  let action ← instantiateMVars (← Semantic.asFunctor action)
  unless FunctorActionData.closedParameter action && (← isTypeCorrect action) do
    throwError "the executable map lost its complete selected functor"
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq sourceBundle sourceContext.bundle <&&> isDefEq targetBundle targetContext.bundle) do
    throwError "the executable map changed its full selected category dictionaries"
  discard <| framingContext (some sourceContext) original.categoryContext
  discard <| framingContext (some targetContext) template.categoryContext
  let (source, target) ← contextualMorphismEndpoints sourceContext original.value
  let expected ← Semantic.mapOf action original.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType expected) (← inferType template.value) <&&>
        isDefEq expected template.value) do
    throwError "the executable map changed its complete selected action or endpoints"
  let sourceWire ← endpoint original (some sourceContext) source true
  let targetWire ← endpoint original (some sourceContext) target false
  let (imageSource, imageTarget) ← match imageEndpoints with
    | some images => pure images
    | none => pure (← objectImage sourceWire, ← objectImage targetWire)
  for (image, endpoint) in #[(imageSource, sourceWire), (imageTarget, targetWire)] do
    discard <| framingContext (some targetContext) image.categoryContext
    let expected ← Semantic.objOf action endpoint.value
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType image.value) (← inferType expected) <&&>
          isDefEq image.value expected) do
      throwError "the complete map action changed a producer-selected image endpoint"
  CategoryContext.checkMorphism targetContext template.value imageSource.value imageTarget.value
  let parametersInputs := dependencies ++ #[sourceWire, targetWire]
  let images := #[imageSource, imageTarget]
  if let some actual ← retainedActionResult? h operation action original
      parameters parametersInputs images parameterOwnership then
    return ← forwardRetainedValue actual template.value
  let presented ← if original.pointDataInterface.isSome then pure original
    else frame original sourceWire targetWire (some sourceContext)
  let sourceMapWire ← captureCompleteCallableWith
    (fun _ _ => pure (sourceWire, targetWire)) presented sourceContext
  let sourceMap := sourceMapWire.fragment
  let arrow ← scopedNode "map" #[{ json := descriptor, ownership := descriptorOwnership }, sourceMap]
  let identityWire ← selectedCallableIdentity targetContext imageSource
  let identity := identityWire.fragment
  let invocation : Backend.PointInvocation := {
    operation, parameters, arrow := arrow.json
    domain := imageSource.json, source := imageSource.json, target := imageTarget.json
    argument := identity.json }
  let state ← registryState
  let some declared := state.operation? operation
    | throwError "the executable map has no accepted projection address"
  let inputForm ← match declared with
    | .functorMap entry =>
      let some form := state.functorInputForm? entry.inputAddress
        | throwError "the executable functor map lost its complete request input"
      pure form
    | .construction entry true =>
      let some form := state.constructionForm? entry.inputAddress
        | throwError "the executable construction map lost its complete request input"
      pure form
    | .edgeAction edge true =>
      let some form := state.edgeActionInputForm? (edgeActionInputAddress edge)
        | throwError "the derived map action lost its complete request input"
      pure form
    | _ => throwError "the executable map does not name a registered functor projection"
  let request : Wire := {
    form := inputForm
    payload := (← combinedRecipePayload template.value (← placedData invocation.encode #[
      (#[.field "args", .index 1], { json := Json.arr parameters, ownership := parameterOwnership }),
      (#[.field "args", .index 2], arrow),
      (#[.field "args", .index 3], imageSource.fragment),
      (#[.field "args", .index 4], imageSource.fragment),
      (#[.field "args", .index 5], imageTarget.fragment),
      (#[.field "args", .index 6], identity)])
      (#[original, presented] ++ parametersInputs ++ images))
    serviceHandles := (← retainServiceOperands h
      (#[original, presented] ++ parametersInputs ++ images)),
    serviceInputPaths := requestInputPaths }
  let request ← match requestInputPaths with
    | none => pure request
    | some paths => do
      let positions :=
        (← liftServiceInputPositions #[.field "args", .index 2, .field "args", .index 1]
          sourceMapWire) ++
        #[(#[.field "args", .index 3], imageSource),
          (#[.field "args", .index 4], imageSource),
          (#[.field "args", .index 5], imageTarget)] ++
        (← liftServiceInputPositions #[.field "args", .index 6] identityWire)
      let paths ← replaceServiceInputPaths h request.fragment paths positions
      pure { request with serviceInputPaths := some paths }
  let reply ← sendData h operation request (completeRequest := true)
  let answer := reply.data.json
  let backend := reply.backend
  if let .error message ← ComputationalData.validateEndpointPort template.value
      imageSource.json imageTarget.json answer then
    malformed backend operation answer message
  let data ← receiveReplyData h operation reply true
  let received := { template with
    payload := WirePayload.computed template.value data
    serviceHandles := request.serviceHandles ++ template.serviceHandles
    callableObserved := true, morphismFramed := false
    morphismFraming := none
    pointDataInterface := none }
  -- A whole opaque callable need not repeat its independently supplied
  -- endpoints. Retain those exact actual packets on this occurrence before
  -- another action can inspect it; the formal result cache is not an endpoint
  -- presentation table. The original returned callable remains unchanged.
  let result ← retainMapImageEndpoints received imageSource imageTarget
  retainActionResult h {
    operation, action, input := original, parameters, parameterOwnership
    parameterInputs := parametersInputs
    imageEndpoints := images, result }
  return result


/-- Materialize only the explicit original/image slots of a selected universal
request. Its formal diagram, constructor ports and comparison cells are fixed. -/
def observeStructuredInvocationWith
    (realizeObjectObservation : Harness → Trace → Wire → TermElabM Wire)
    (realizeArrowObservation : Harness → Trace → Wire → TermElabM Wire)
    (captureCompleteCallable : Harness → Trace → Wire → CategoryContext →
      (endpoints : optParam (Option (Wire × Wire)) none) →
      (publicFrame : optParam Bool true) → TermElabM Wire)
    (h : Harness) (trace : Trace) (selected : SelectedStructuredInvocation) : TermElabM Wire := do
  let state ← registryState
  let row := selected.row
  let id := row.id
  let standard := selected.standard
  let plan := selected.plan
  let sourceContext := selected.sourceContext
  let targetContext := selected.targetContext
  let sourceDiagram := selected.sourceDiagram
  let sent := selected.targetDiagram
  let formalPresentation := selected.formalPresentation
  let formalLowerPresentation := selected.formalLowerPresentation
  let lift? := selected.creation.map (·.id)
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the captured universal construction lost its registered category"
  let read := fun (index : Nat) => do
    let some operand := selected.operands[index]?
      | throwError "the captured invocation lost an explicit operand occurrence"
    unless operand.wire.value == operand.formal && (← withoutModifyingState
        (withTransparency .all <| isDefEq (← inferType operand.wire.value) operand.expectedType)) do
      throwError "the captured invocation changed an independently selected operand type"
    return operand.wire
  let inputs := fun (items : Array UniversalInputOccurrence) => items.mapM fun item => do
    let wire ← read item.operand
    let endpoints ← item.endpoints.mapM fun (source, target) => do
      return (← read source, ← read target)
    return (wire, endpoints, item.unchangedGraph)
  let sourceInputs ← inputs selected.sourceInputs
  let mappedInputs ← inputs selected.imageInputs
  -- Every source occurrence and image plan is now fixed. Observation uses
  -- these retained Wires directly; no later formal cache entry supplies a slot.
  let preparing := { h with demandObjectActions := false }
  let observing := { h with demandObjectActions := true }
  let observeObject := fun (wire : Wire) (context : CategoryContext) => do
    let actual ← computationalApexReceiver trace
      (← realizeObjectObservation observing trace wire)
    let actual ← forwardRetainedValue actual wire.value
    CategoryContext.checkObject context actual.value
    discard <| framingContext (some context) actual.categoryContext
    return actual
  let observeMap := fun (wire : Wire) (context : CategoryContext) => do
    let actual ← realizeArrowObservation observing trace wire
    let actual ← forwardRetainedValue actual wire.value
    discard <| framingContext (some context) actual.categoryContext
    let some endpoints ← retainedCallableEndpoints? actual context
      | throwError "the observed diagram map lost its retained complete endpoint occurrences"
    -- A returned callable owns its new actual endpoint packets. The shared
    -- framing producer checks those exact occurrences before exposing its map.
    captureCompleteCallable preparing trace actual context (some endpoints) true
  let mut inputRoles := #[]
  let mut retainedSourceWires := #[]
  let mut retainedWires := #[]
  for index in [:mappedInputs.size] do
    let some (original, sourceEndpoints, _) := sourceInputs[index]?
      | throwError "the constructed diagram lost its original input occurrence"
    let some (wire, imageEndpoints, unchangedGraph) := mappedInputs[index]?
      | throwError "the constructed diagram lost its prepared image occurrence"
    match sourceEndpoints with
    | none =>
      let actualSource ← observeObject original sourceContext
      let actual ← if lift?.isNone then pure actualSource else
        observeObject wire targetContext
      retainedSourceWires := retainedSourceWires.push actualSource
      retainedWires := retainedWires.push actual
      inputRoles := inputRoles.push (actual.fragment, none, none)
    | some _ =>
      let actualSource ← observeMap original sourceContext
      let actual ← if lift?.isNone then pure actualSource else do
        let intrinsic ← match unchangedGraph, imageEndpoints with
          | some graph, some (source, target) => do
            if !sameCompleteWireContext original actualSource then pure none else do
              let source ← observeObject source targetContext
              let target ← observeObject target targetContext
              -- Only the unchanged complete original and the checked target
              -- graph can bypass a primitive. Actual endpoints still validate
              -- the graph; no failed implementation selects this path.
              if (← ComputationalData.validateEndpointPort wire.value source.json target.json
                  graph.json).isOk then
                CategoryContext.checkMorphism targetContext wire.value source.value target.value
                let data ← scopedNode "typedMap" #[source.fragment, target.fragment, graph]
                let result : Wire := {
                  form := wire.form, payload := (← scopedPayload wire.value data)
                  categoryContext := some targetContext
                  callableObserved := true, morphismFramed := true }
                pure (some (← retainCallableEndpoints result source target targetContext))
              else pure none
          | _, _ => pure none
        match intrinsic with
        | some actual => pure actual
        | none => observeMap wire targetContext
      let some (source, target) ← retainedCallableEndpoints? actual targetContext
        | throwError "the dispatched diagram map lost its actual endpoint fields"
      retainedSourceWires := retainedSourceWires.push actualSource
      retainedWires := retainedWires.push actual
      inputRoles := inputRoles.push (actual.fragment, some source.fragment, some target.fragment)
  let sourceDiagramData ← scopedNode (Codec.label standard) (retainedSourceWires.map (·.fragment))
  let diagramData ← scopedNode (Codec.label standard) (retainedWires.map (·.fragment))
  let input : Wire := {
    form := .diagrams category
    payload := (← combinedRecipePayload sent diagramData (retainedSourceWires ++ retainedWires))
    serviceHandles := (← retainServiceOperands h (retainedSourceWires ++ retainedWires)) }
  let resolveRole := fun role => do
    match role with
    | .argument position => return (← inputRoles[position]?).1
    | .source position => (← inputRoles[position]?).2.1
    | .target position => (← inputRoles[position]?).2.2
  let externalFragment := fun binder => do
    let binding ← plan.binders[binder]?
    let role ← binding.inputRoles[0]?
    let descriptor ← resolveRole role
    if binding.inputRoles.all (fun other => resolveRole other == some descriptor) then
      some descriptor
    else none
  let externalDescriptor := fun binder => (externalFragment binder).map (·.json)
  let formalDiagram := if lift?.isSome then sourceDiagram else sent
  let formalDiagramData := if lift?.isSome then sourceDiagramData else input.fragment
  let formalDiagramJson := formalDiagramData.json
  let handles ← retainServiceOperands h (retainedSourceWires ++ retainedWires)
  let serviceOperands := ((retainedSourceWires ++ retainedWires).zip handles).map fun (wire, handle) =>
    ({ value := wire.value, data := wire.json, handle, form := some wire.form,
       context := wire.categoryContext, ownership := wire.ownership } : ServiceRequest.Operand)
  let base ← UniversalServiceRequest.materializedLimit row sent selected.encodingPresentation
    plan serviceOperands inputRoles
  let prepared : ServiceRequest.Prepared := { base with
    requestValue := sent, result := selected.formal, resultForm := selected.resultForm,
    resultContext := some selected.context, familyApplication := some selected.application,
    complete := fun raw => do
      if lift?.isNone then return ← base.complete raw
      match ← base.complete raw with
      | .error message => return .error message
      | .ok _ => pure ()
      let .ok answer := ComputationalData.valuePayload raw
        | return .error "the universal result has a malformed computational value envelope"
      let packet := match lift? with
        | none => StructuredResult.ComputationPacket.direct answer
        | some lift => .created lift.raw sourceDiagramData.json answer
      return (← StructuredResult.complete row formalDiagram formalDiagramJson packet
        selected.formalPresentation (fun answer =>
          StructuredResult.validatePlannedData plan answer
            (fun port seen json => ComputationalData.validatePlannedPort plan port seen json
              externalDescriptor ComputationalData.endpointKeys))).map some }
  unless prepared.fragment == input.fragment do
    throwError "the materialized universal factory changed its exact request data"
  let reply ← sendData h id.raw input
  let rawAnswer := reply.data.json
  let backend := reply.backend
  let answerData ← receiveReplyFragment h id.raw reply true
  let answer := answerData.json
  let mut createdPresentation? : Option Expr := none
  let packet ← match lift? with
    | none => pure (StructuredResult.ComputationPacket.direct answer)
    | some lift => pure (.created lift.raw sourceDiagramData.json answer)
  let completion ← match ← prepared.complete rawAnswer with
    | .ok completed => pure completed
    | .error message => malformed backend id.raw rawAnswer message
  let some completed := completion
    | throwError "the universal factory omitted its complete result"
  let mut completed := completed
  -- Validate the backend packet before reconstructing formal creation evidence:
  -- a malformed reply is not a missing universal-property implementation.
  if let some liftId := lift? then
    let some creation := selected.creation
      | throwError "the captured creation invocation lost its accepted creation evidence"
    unless creation.id == liftId do throwError "the captured creation changed its selected identity"
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[formalLowerPresentation]
    let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    -- The lower universal cone has been transported along the checked
    -- diagram comparison: it is over sourceDiagram ⋙ U, not over the
    -- standard mapped diagram `sent` used as the computational wire.
    let lowerDiagram ← withTransparency .all <| mkFunctorComp sourceDiagram
      (← Semantic.asFunctor (← Semantic.edgeFunctor state creation.edge))
    let decoded : StructuredResult.Decoded := {
      diagram := lowerDiagram, cone, apex, answer }
    match ← StructuredResult.lift state creation sourceDiagram decoded formalLowerPresentation with
    | .ok lifted =>
      unless ← withTransparency .all <| isDefEq lifted.diagram sourceDiagram do
        throwStratum .noImplementation "the creation lift does not reconstruct the source diagram"
      let some createdPresentation := lifted.presentation
        | throwStratum .noImplementation "the registered creation lift omitted its checked universal presentation"
      createdPresentation? := some createdPresentation
    | .error message =>
      throwStratum .noImplementation m!"the registered creation lift cannot reconstruct its universal cone: {message}"
  if let some createdPresentation := createdPresentation? then
    -- Universal cones over the same diagram need not have definitionally
    -- equal apexes. Compare the entire cones through the canonical checked
    -- isomorphism, not by demanding equality of their presentations.
    let createdEvidence ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[createdPresentation]
    let formalEvidence ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[completed.presentation]
    let comparison ← mkAppM ``CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso
      #[formalEvidence, createdEvidence]
    let comparison ← StructuredResult.checkReconstruction comparison
    let createdCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[createdPresentation]
    let createdApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[createdCone]
    let decoded : StructuredResult.Decoded := {
      diagram := completed.diagram, cone := createdCone,
      apex := createdApex, answer, presentation := some createdPresentation }
    match ← StructuredResult.extendCreated decoded comparison with
    | .error message =>
        throwStratum .noImplementation m!"the creation comparison cannot transport its defining maps: {message}"
    | .ok extended =>
        let some transported := extended.presentation
          | throwStratum .noImplementation "the transported creation lost its universal presentation"
        completed ← match ← StructuredResult.complete row formalDiagram formalDiagramJson
            packet transported (fun answer =>
              StructuredResult.validatePlannedData plan answer
                (fun port seen json => ComputationalData.validatePlannedPort plan port seen json
                  externalDescriptor ComputationalData.endpointKeys)) with
          | .ok result => pure result
          | .error message =>
              throwStratum .noImplementation m!"the transported creation cannot be retained: {message}"
  let packetData ← match lift? with
    | none => pure answerData
    | some lift =>
      scopedNode "createdCone"
        #[{ json := toJson lift.raw }, sourceDiagramData, answerData]
  let constructionInputs :=
    plan.binders.filterMap fun binding => if binding.port.isSome then none else do
      let formal ← binding.formalValue
      let actual ← externalFragment binding.index
      return ((actual.json, formal), actual.ownership)
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType completed.apex) (← inferType selected.formal) <&&>
        isDefEq completed.apex selected.formal) do
    throwError "the completed universal construction changed its selected full apex"
  return {
    form := selected.resultForm,
    payload := (← constructionPayload selected.resultForm completed formalDiagramData packetData)
    categoryContext := some selected.context, objectObserved := true,
    constructionInputs := some (completed.apex, constructionInputs.map Prod.fst),
    constructionInputOwnership := constructionInputs.map Prod.snd,
    serviceHandles := handles }

def realizeLimitWith
    (realizeUnobserved : Harness → Trace → String → Expr → TermElabM Wire)
    (captureCompleteCallable : Harness → Trace → Wire → CategoryContext →
      (endpoints : optParam (Option (Wire × Wire)) none) →
      (publicFrame : optParam Bool true) → TermElabM Wire)
    (captureMapRoute : Harness → Trace → Wire → Array EdgeRef → Array Expr → TermElabM Wire)
    (realizedEdgeData : Harness → Trace → EdgeRef → Expr →
      TermElabM (DataOwnership.Data × Array Wire))
    (capturedEdgeData : Harness → Trace → EdgeRef → Expr → TermElabM ActionDataTemplate)
    (extentFragment? : Harness → Trace → Expr →
      TermElabM (Option (DataOwnership.Data × Array Wire)))
    (h : Harness) (trace : Trace) (state : RegistryState) (what : String)
    (id : LimitId) (D : Expr) (lift? : Option LiftId) : TermElabM Wire := do
  let some row := state.limits.find? (·.id == id) | unreachable!
  if let some liftId := lift? then
    let some creation := state.lifts.find? (·.id == liftId)
      | throwStratum .noImplementation m!"the requested creation lift {liftId.raw} is not registered"
    if row.colimit then
      throwStratum .noImplementation m!"the requested lift {liftId.raw} cannot create a colimit"
    unless creation.kind == .createsLimits row.shape do
      throwStratum .noImplementation m!"the requested lift {liftId.raw} does not create {row.shape} limits"
    let some edge := state.structuralEdge? creation.edge
      | throwStratum .noImplementation m!"the requested creation lift {liftId.raw} has no registered functor"
    let U ← Semantic.asFunctor (← Semantic.edgeFunctor state creation.edge)
    let functorType ← withTransparency .all <| whnf (← inferType U)
    unless functorType.isAppOfArity ``CategoryTheory.Functor 4 do
      throwStratum .noImplementation m!"the requested creation lift {liftId.raw} has no full functor type"
    let diagramType ← withTransparency .all <| whnf (← inferType D)
    unless diagramType.isAppOfArity ``CategoryTheory.Functor 4 do
      throwStratum .noImplementation m!"the requested creation lift {liftId.raw} has no full diagram category"
    unless (← withTransparency .all <|
        isDefEq (diagramType.getAppArgs[2]!) (functorType.getAppArgs[0]!)) &&
        (← withTransparency .all <|
          isDefEq (diagramType.getAppArgs[3]!) (functorType.getAppArgs[1]!)) do
      throwStratum .noImplementation m!"the requested creation lift {liftId.raw} has a different source diagram category"
    let some target := state.category? edge.target
      | throwStratum .noImplementation m!"the requested creation lift {liftId.raw} has no target category"
    unless target.id == row.category do
      throwStratum .noImplementation m!"the requested creation lift {liftId.raw} does not target {row.category.raw}"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "internal registry inconsistency: the category of {id.raw} is not registered"
  -- The diagram's data: the explicit arguments of its standard form, in their forms.
  let D ← instantiateMVars D
  let mut D := D.consumeMData
  while D.isAppOfArity ``id 2 do D := D.appArg!.consumeMData
  let .const standard _ := D.getAppFn
    | throwStratum .noImplementation m!"nothing computes {what}: its diagram is not in a \
        standard form"
  let some constructor ← Semantic.diagramConstructor row
    | throwStratum .noImplementation "the selected construction has no registered diagram telescope"
  unless standard == constructor do
    throwError "the selected construction changed its registered diagram telescope"
  let infos ← forallTelescopeReducing (← getConstInfo standard).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let data := (D.getAppArgs.zip infos).filterMap fun (a, i) =>
    if i.isExplicit then some a else none
  -- The independently selected diagram fixes the complete original category.
  -- Capture every argument and callable frame before observing any sibling.
  let (_, sourceBundle) ← functorCategoryBundles D
  let sourceExpression ← match lift? with
    | none => pure category.expression
    | some liftId => do
      let some lift := state.lifts.find? (·.id == liftId)
        | throwError "the checked creation lift is no longer registered"
      let some expression := state.selectedEdgeSource? lift.edge
        | throwError "the checked creation lift lost its full source expression"
      pure expression
  let sourceContext : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
  let preparing := { h with demandObjectActions := false }
  let readArgument := fun a => do
    if let some (json, dependencies) ← extentFragment? preparing trace a then
      let literal ← realizeUnobserved preparing trace s!"a diagram object of {what}" a
      return { literal with payload := (← combinedRecipePayload a json (#[literal] ++ dependencies)) }
    if (← trace.node? a).isNone then
      discard <| Semantic.recordNamedObject a (some trace)
      let mut application := a.consumeMData
      while application.isAppOfArity ``id 2 do
        application := application.appArg!.consumeMData
      if let some entry := state.morphisms.find? fun entry =>
          application.getAppFn.constName? == some entry.declaration then
        Semantic.namedMorphism entry a (some trace)
      if (← trace.node? a).isNone then
        if let some sourceCategory := CategoryContext.named? state sourceContext.expression then
          discard <| Semantic.recordRegisteredMorphism sourceCategory.id a (some trace)
    if (← trace.node? a).isNone then
      let type ← inferType a
      if type.isAppOf ``Quiver.Hom then
        let endpoints := type.getAppArgs
        let source := endpoints[endpoints.size - 2]!
        let target := endpoints[endpoints.size - 1]!
        let mut tag? : Option String := none
        if ← withoutModifyingState (isDefEq source target) then
          let identity ← elabTermAndSynthesize
            (← `(CategoryTheory.CategoryStruct.id $(← exprToSyntax source))) (some type)
          if ← withoutModifyingState (isDefEq identity a) then tag? := some "identity"
        if tag?.isNone then
          let instanceType ← elabTermAndSynthesize
            (← `(CategoryTheory.Limits.HasZeroMorphisms $(← exprToSyntax (← inferType source)))) none
          if (← trySynthInstance instanceType).toOption.isSome then
            let zero ← elabTermAndSynthesize (← `(0)) (some type)
            if ← withoutModifyingState (isDefEq zero a) then tag? := some "zero"
        if let some tag := tag? then
          discard <| Semantic.recordNamedObject source (some trace)
          discard <| Semantic.recordNamedObject target (some trace)
          let sourceWire ← realizeUnobserved preparing trace
            s!"a canonical diagram arrow's source in {what}" source
          let targetWire ← realizeUnobserved preparing trace
            s!"a canonical diagram arrow's target in {what}" target
          CategoryContext.checkMorphism sourceContext a sourceWire.value targetWire.value
          let template : ActionDataTemplate :=
            .ctor tag #[.wire .object sourceWire, .wire .object targetWire]
          let (json, dependencies) ← renderCapturedActionData template
          let wire : Wire := {
            form := contextualForm state sourceContext (.canonicalMorphism category) true
            payload := (← combinedRecipePayload a json dependencies)
            categoryContext := some sourceContext }
          let wire ← retainIntrinsicAssembly wire .map sourceContext template
          return ← retainCallableEndpoints wire sourceWire targetWire sourceContext
    realizeUnobserved preparing trace s!"the diagram of {id.raw} in {what}" a
  let sourceInputs ← data.mapM fun a => do
    let wire ← readArgument a
    match Language.homEnds? (← inferType wire.value) with
    | none =>
      CategoryContext.checkObject sourceContext wire.value
      discard <| framingContext (some sourceContext) wire.categoryContext
      return (wire, (none : Option (Wire × Wire)), (none : Option DataOwnership.Data))
    | some (source, target) =>
      CategoryContext.checkMorphism sourceContext wire.value source target
      for endpoint in #[source, target] do
        if (← trace.node? endpoint).isNone then
          discard <| Semantic.recordNamedObject endpoint (some trace)
      let complete ← captureCompleteCallable preparing trace wire sourceContext none true
      let some endpoints ← retainedCallableEndpoints? complete sourceContext
        | throwError "the prepared diagram map lost its exact complete endpoint occurrences"
      -- The existing graph optimization applies to these exact original bytes.
      -- A presentation conversion in the callable body cannot be discarded.
      let graph ← match wire.form with
        | .graph _ => do
          let some frame := ComputationalData.recordPayload? complete.fragment | pure none
          if (Backend.TypedMap.decode frame.json).isOk then
            let body ← checkedFragment (frame.project #[.field "args", .index 2])
            pure (if body == wire.fragment then some wire.fragment else none)
          else pure none
        | _ => pure none
      return (complete, some endpoints, graph)
  let sourceWires := sourceInputs.map (·.1)
  let sourceDiagram ← mkAppM standard (sourceWires.map (·.value))
  let (targetContext, mappedInputs) ←
    match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
    | none => pure (sourceContext, sourceInputs.map fun (wire, endpoints, _) =>
        (wire, endpoints, (none : Option DataOwnership.Data)))
    | some lift => do
      let action ← Semantic.asFunctor (← Semantic.edgeFunctor state lift.edge)
      let (_, targetBundle) ← functorCategoryBundles action
      let targetContext : CategoryContext := { expression := category.expression, bundle := targetBundle }
      let mapped ← sourceInputs.mapM fun (wire, endpoints, graph) => do
        match endpoints with
        | none =>
          let image ← transport trace wire #[lift.edge] (some (realizedEdgeData preparing trace))
            (some (capturedEdgeData preparing trace))
          CategoryContext.checkObject targetContext image.value
          discard <| framingContext (some targetContext) image.categoryContext
          return (image, (none : Option (Wire × Wire)), (none : Option DataOwnership.Data))
        | some _ =>
          -- The creation branch has no surface map Trace node. Its accepted
          -- action and exact input belong to the shared typed action producer.
          let image ← captureMapRoute preparing trace wire #[lift.edge] #[action]
          let image ← captureCompleteCallable preparing trace image targetContext none true
          let some endpoints ← retainedCallableEndpoints? image targetContext
            | throwError "the prepared creation map lost its exact image endpoints"
          let graph ← match graph with
            | none => pure none
            | some graph => do
              -- Preserve the existing independently decoded target-map check.
              -- Computational endpoint validation follows on actual images.
              let decoded ← decodeValue trace category (← inferType image.value) graph.json
              let unchanged ← match decoded with
                | .error _ => pure false
                | .ok (targetMap, _) => do
                  if ← withTransparency .all <| withoutModifyingState
                      (isDefEq image.value targetMap) then pure true
                  else do
                    let condition ← mkEq image.value targetMap
                    match ← Codec.conditionProof condition with
                    | some proof => Decide.kernelAccepts condition proof
                    | none => pure false
              pure (if unchanged then some graph else none)
          return (image, some endpoints, graph)
      pure (targetContext, mapped)
  let wires := mappedInputs.map (·.1)
  let sent ← mkAppM standard (wires.map (·.value))
  let mut lowerComparison? : Option Expr := none
  if let some liftId := lift? then
    let some creation := state.lifts.find? (·.id == liftId)
      | throwStratum .noImplementation "the requested creation lift is not registered"
    let U ← Semantic.asFunctor (← Semantic.edgeFunctor state creation.edge)
    let expected ← withTransparency .all <| mkFunctorComp sourceDiagram U
    let comparison ← match row.standardization with
      | some declaration =>
          StructuredResult.checkReconstruction (← mkAppM declaration #[expected])
      | none =>
          if ← withTransparency .all <| isDefEq expected sent then
            StructuredResult.checkReconstruction (← mkAppM ``CategoryTheory.Iso.refl #[expected])
          else
            throwStratum .noImplementation
              "the registered presentation has no diagram standardization comparison"
    let comparisonType ← mkAppM ``CategoryTheory.Iso #[expected, sent]
    unless ← withTransparency .all <| isDefEq (← inferType comparison) comparisonType do
      throwError "the selected diagram comparison has different complete endpoints"
    lowerComparison? := some comparison
  let encodingPresentation ← Semantic.limitPresentation row sent
  let plan ← match ← StructuredResult.dataPlan row sent encodingPresentation with
    | .error message => throwStratum .noImplementation m!"the formal construction has no computational data schema: {message}"
    | .ok plan => pure plan
  let formalLowerPresentation ← match lowerComparison? with
    | none => pure encodingPresentation
    | some comparison => do
        let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[encodingPresentation]
        let proof ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[encodingPresentation]
        let transported ← mkAppM ``CategoryTheory.Limits.Cone.postcompose
          #[← mkAppM ``CategoryTheory.Iso.inv #[comparison]]
        let transported ← mkAppM ``CategoryTheory.Functor.obj #[transported, cone]
        let equivalence ← mkAppM ``CategoryTheory.Limits.IsLimit.postcomposeInvEquiv
          #[comparison, cone]
        let proof ← mkAppM ``Equiv.toFun
          #[← mkAppM ``Equiv.symm #[equivalence], proof]
        StructuredResult.checkReconstruction
          (← mkAppM ``CategoryTheory.Limits.LimitCone.mk #[transported, proof])
  let formalPresentation ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
    | none => Semantic.limitPresentation row sent
    | some lift => do
      let some edge := state.structuralEdge? lift.edge | unreachable!
      let some source := state.categories.find? (·.expression.syntacticEq edge.source)
        | throwError "the creation lift has no registered full source category"
      Semantic.limit row.colimit row.shape sourceDiagram source.id.raw none
  let form ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
    | none => pure (.limitApex row)
    | some lift => do
      let some edge := state.structuralEdge? lift.edge | unreachable!
      let some source := state.categories.find? (·.expression.syntacticEq edge.source)
        | throwError "the creation lift has no registered source schema"
      pure (.createdApex row source.id)
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[formalPresentation]
  let apex ← StructuredResult.checkReconstruction (← mkAppM (if row.colimit then
    ``CategoryTheory.Limits.Cocone.pt else ``CategoryTheory.Limits.Cone.pt) #[cone])
  CategoryContext.checkObject sourceContext apex
  let mut operands : Array InvocationOperand := #[]
  let mut sources : Array UniversalInputOccurrence := #[]
  let mut images : Array UniversalInputOccurrence := #[]
  for (inputs, phase) in #[sourceInputs, mappedInputs].zipIdx do
    let mut occurrences : Array UniversalInputOccurrence := #[]
    for (wire, endpoints, graph) in inputs do
      let operand := operands.size
      operands := operands.push {
        formal := wire.value, expectedType := ← inferType wire.value,
        role := if endpoints.isSome then .map else .object, wire }
      let mut endpointIndices := none
      if let some (source, target) := endpoints then
        let sourceIndex := operands.size
        operands := operands.push {
          formal := source.value, expectedType := ← inferType source.value,
          role := .object, wire := source }
        let targetIndex := operands.size
        operands := operands.push {
          formal := target.value, expectedType := ← inferType target.value,
          role := .object, wire := target }
        endpointIndices := some (sourceIndex, targetIndex)
      occurrences := occurrences.push { operand, endpoints := endpointIndices, unchangedGraph := graph }
    if phase == 0 then sources := occurrences else images := occurrences
  -- Empty diagrams have two empty arrays; do not infer a semantic role from length.
  if sourceInputs.isEmpty then images := #[]
  let descriptor ← scopedNode (Codec.label standard) (wires.map (·.fragment))
  let original : Wire := {
    form, payload := (← combinedRecipePayload apex descriptor (sourceWires ++ wires))
    categoryContext := some sourceContext }
  retainCapturedInvocation h original (.structured {
    address := id.raw, application := encodingPresentation, formal := apex,
    fragment := descriptor, context := sourceContext, inputForm := .diagrams category,
    resultForm := form, row, standard, sourceContext, targetContext, sourceDiagram,
    targetDiagram := sent, encodingPresentation, formalPresentation, formalLowerPresentation,
    lowerComparison := lowerComparison?, creation := lift?.bind (fun id => state.lifts.find? (·.id == id)),
    plan, operands, sourceInputs := sources, imageInputs := images })

/-- Compare the selection before and after the checked product action. Only
the separately derived current comparisons and exact dependency allocation may
change; the producer's recursive component context remains the original one. -/
def checkOperationNormalizedEndpoint (original normalized : Wire) : TermElabM Unit := do
  unless sameCompleteWireContext original { normalized with
      objectIso := original.objectIso, endpointPresentation := original.endpointPresentation } do
    throwError "operation argument framing changed its original complete endpoint selection"

def sameOperationEndpointAction (left right : Option EndpointPresentation) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right => left.comparison == right.comparison &&
      left.forwardFragment == right.forwardFragment && left.backwardFragment == right.backwardFragment &&
      sameEndpointComparisonMaps left.maps right.maps &&
      sameNamedRefinementOrigin left.namedRefinement right.namedRefinement
  | _, _ => false

/-- Ephemeral typed interpretation of a callable slot. Capture retains the
selected occurrence, prospective inspection returns its private interface, and
execution observes that same occurrence. Observation does not add a new
presentation frame or change the public encoding. No closure is stored on a Wire. -/
structure CallablePreparationReader where
  observe : CategoryContext → Wire → TermElabM Wire
  observeData : ActionDataRole → Wire → TermElabM Wire := fun _ wire => pure wire
  objects : TermElabM ComputationalData.InterfaceObjects := pure #[]

/-- Native point and scalar slots keep their own result interface. Whole-map
framing is selected explicitly by its producer, not by this data-slot reader. -/
def CallablePreparationReader.readData (reader : CallablePreparationReader)
    (role : ActionDataRole) (original : Wire) : TermElabM Wire := do
  let observed ← reader.observeData role original
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType observed.value) (← inferType original.value) <&&>
        isDefEq observed.value original.value) do
    throwError "the prepared input changed its independently fixed typed occurrence"
  discard <| framingContext original.categoryContext observed.categoryContext
  forwardRetainedValue observed original.value

/-- Private output references supplement the positioned request context. An
existing declared binding remains authoritative; equality cannot select a new
occurrence or replace an incompatible complete interface. -/
def CallablePreparationReader.interfaceObjects (reader : CallablePreparationReader)
    (objects : ComputationalData.InterfaceObjects) :
    TermElabM ComputationalData.InterfaceObjects := do
  mergeCallableInterfaceObjects objects (← reader.objects)

/-- One direction of an accepted endpoint comparison, with both of its exact
endpoint occurrences. The selected comparison, not returned data, fixes its
formal direction and the actual-side endpoint packet. -/
structure PreparedEndpointComparison where
  original : Wire
  comparisonMap : Wire
  semantic : Wire
  actual : Wire

def prepareEndpointComparisonWith (reader : CallablePreparationReader)
    (context : CategoryContext) (wire : Wire) (forward : Bool)
    (retained : Option Wire := none) : TermElabM (Option PreparedEndpointComparison) := do
  let some presentation := wire.endpointPresentation | do
    if retained.isSome then
      throwError "a callable frame supplied an unselected endpoint comparison"
    return none
  let (semantic, actual) ← operationComparisonEnds context presentation.comparison
  let maps ← endpointPresentationMaps wire context presentation
  let selected := retained.getD (if forward then maps.1 else maps.2)
  let expected ← mkAppM (if forward then ``CategoryTheory.Iso.hom else ``CategoryTheory.Iso.inv)
    #[presentation.comparison]
  let check := fun (comparisonMap : Wire) => do
    discard <| framingContext (some context) comparisonMap.categoryContext
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType comparisonMap.value) (← inferType expected) <&&>
          isDefEq comparisonMap.value expected) do
      throwError "the callable frame changed its complete selected comparison direction"
    let some endpoints ← retainedCallableEndpoints? comparisonMap context
      | throwStratum .noImplementation
          "the selected comparison has no complete retained endpoint interface"
    let semanticEndpoint := if forward then endpoints.1 else endpoints.2
    let actualEndpoint := if forward then endpoints.2 else endpoints.1
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType semanticEndpoint.value) (← inferType semantic) <&&>
          isDefEq semanticEndpoint.value semantic <&&>
        isDefEq (← inferType actualEndpoint.value) (← inferType actual) <&&>
          isDefEq actualEndpoint.value actual) do
      throwError "the comparison changed an independently fixed complete endpoint"
    return (semanticEndpoint, actualEndpoint)
  let (_, originalActual) ← check selected
  unless originalActual.fragment == wire.fragment do
    throwStratum .unavailable
      "the selected comparison lost its original actual endpoint packet or suppliers"
  let observed ← reader.observe context selected
  let (semanticEndpoint, actualEndpoint) ← check observed
  unless actualEndpoint.fragment == wire.fragment do
    throwStratum .malformed
      "the comparison did not reuse its fixed actual endpoint packet and suppliers"
  return some {
    original := selected, comparisonMap := observed,
    semantic := semanticEndpoint, actual := actualEndpoint }

/-- A computational frame keeps the logical map and its independently checked
actual full Hom separate. The validation template names exact endpoint slots;
its body is never discovered by equality with another packet. -/
structure PreparedMorphismFrame where
  wire : Wire
  actual : Expr
  source : Wire
  target : Wire
  template : ActionDataTemplate
  dependencies : Array Wire

/-- Open only the existing transparent value and typed-map envelopes. A caller
has already obtained this whole map from its retained typed producer. Literal
body data here describe that exact output role; they are not an evaluator. -/
partial def completeCallableValidationTemplate (data : DataOwnership.Data)
    (source target : Wire) : TermElabM ActionDataTemplate := do
  let .ok (tag, fields) := ComputationalData.envelope data.json
    | throwStratum .malformed "the complete callable omitted its declared typed-map frame"
  if tag == "valueData" && fields.size == 1 then
    return .ctor "valueData" #[← completeCallableValidationTemplate
      (← checkedFragment (data.project #[.field "args", .index 0])) source target]
  unless tag == "typedMap" && fields.size == 3 do
    throwStratum .malformed "the complete callable omitted its declared typed-map frame"
  let selectedSource ← checkedFragment (data.project #[.field "args", .index 0])
  let selectedTarget ← checkedFragment (data.project #[.field "args", .index 1])
  unless selectedSource == source.fragment && selectedTarget == target.fragment do
    throwStratum .malformed "the whole callable changed its complete invocation endpoint occurrences"
  let body ← checkedFragment (data.project #[.field "args", .index 2])
  return .ctor "typedMap" #[.wire .retained source, .wire .retained target, .literal body]

/-- Metadata-only actual endpoint views come from the accepted comparison's
retained map endpoints. A whole-map result has already consumed the comparison;
reading this view does not execute or apply its map a second time. -/
def callableActualEndpoint (context : CategoryContext) (wire : Wire)
    (source : Bool) : TermElabM Wire := do
  let some presentation := wire.endpointPresentation | return wire
  let maps ← endpointPresentationMaps wire context presentation
  let selected := if source then maps.2 else maps.1
  let some endpoints ← retainedCallableEndpoints? selected context
    | throwStratum .noImplementation "the whole callable lost its selected actual endpoint view"
  let endpoint := if source then endpoints.1 else endpoints.2
  unless endpoint.fragment == wire.fragment do
    throwStratum .unavailable "the whole callable changed its fixed actual endpoint occurrence"
  return endpoint

/-- Apply only the directions retained by this exact frame. Existing frames are
replayed before reading their children, including when their bytes are unchanged.
A whole-map producer is observed through its complete output interface instead
of applying an already consumed endpoint comparison again. -/
partial def prepareMorphismFrameWith (reader : CallablePreparationReader)
    (context : CategoryContext) (input source target : Wire)
    (comparisons : Option (Option Wire × Option Wire) := none) :
    TermElabM PreparedMorphismFrame := do
  CategoryContext.checkMorphism context input.value source.value target.value
  discard <| framingContext (some context) input.categoryContext
  if let some frame := input.morphismFraming then
    let replayed ← presentMorphism frame.input frame.source frame.target frame.context frame.comparisons
    unless sameCompleteWireContext replayed input do
      throwStratum .unavailable "the callable lost its exact retained framing producer"
    unless sameCompleteWireContext frame.source source &&
        sameCompleteWireContext frame.target target do
      throwStratum .unavailable "the callable frame changed its original complete endpoint occurrences"
    if comparisons.isSome then
      throwError "a retained frame cannot acquire a second comparison selection"
    return ← prepareMorphismFrameWith reader context frame.input source target frame.comparisons
  let (actual, _, _) ← operationFramedPoint context input source target
  if input.morphismFramed then
    let some originalEndpoints ← retainedCallableEndpoints? input context
      | throwStratum .noImplementation "the framed callable has no retained complete output interface"
    for (original, endpoint) in #[(originalEndpoints.1, source), (originalEndpoints.2, target)] do
      unless sameCompleteWireContext original
          (← forwardRetainedValue endpoint original.value) do
        throwStratum .noImplementation
          "the whole callable requires its original complete invocation endpoint interface"
    let observed ← reader.observe context input
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType observed.value) (← inferType input.value) <&&>
          isDefEq observed.value input.value) do
      throwError "the whole callable observer changed its complete selected map"
    let observed ← forwardRetainedValue observed input.value
    let some endpoints ← retainedCallableEndpoints? observed context
      | throwError "the whole callable observer omitted its fixed complete endpoint interface"
    unless sameCompleteWireContext endpoints.1 (← forwardRetainedValue source endpoints.1.value) &&
        sameCompleteWireContext endpoints.2 (← forwardRetainedValue target endpoints.2.value) do
      throwStratum .malformed "the whole callable changed its independently fixed endpoint occurrences"
    let actualSource ← callableActualEndpoint context source true
    let actualTarget ← callableActualEndpoint context target false
    let template ← match ComputationalData.recordPayload? observed.fragment with
      | some body =>
        if (body.json.getObjValAs? String "ctor").toOption == some "typedMap" then
          completeCallableValidationTemplate observed.fragment actualSource actualTarget
        else pure (.wire .map observed)
      | none => pure (.wire .map observed)
    return {
      wire := observed, actual, source := actualSource, target := actualTarget,
      template, dependencies := #[input, observed, source, target] }
  let sourceComparison ← prepareEndpointComparisonWith reader context source false
    (comparisons.bind (·.1))
  let targetComparison ← prepareEndpointComparisonWith reader context target true
    (comparisons.bind (·.2))
  let sourceMap := sourceComparison.map (·.comparisonMap)
  let targetMap := targetComparison.map (·.comparisonMap)
  let actualSource := (sourceComparison.map (·.actual)).getD source
  let actualTarget := (targetComparison.map (·.actual)).getD target
  -- A returned comparison may compute its semantic endpoint as well. A raw
  -- point already framed at another packet cannot silently move to that new
  -- representation without its own declared computational action.
  if let some data := ComputationalData.recordPayload? input.fragment then
    if (Backend.TypedMap.decode data.json).isOk then
      let semanticSource := (sourceComparison.map (·.semantic)).getD source
      let semanticTarget := (targetComparison.map (·.semantic)).getD target
      let suppliedSource ← checkedFragment (data.project #[.field "args", .index 0])
      let suppliedTarget ← checkedFragment (data.project #[.field "args", .index 1])
      unless suppliedSource == semanticSource.fragment && suppliedTarget == semanticTarget.fragment do
        throwStratum .noImplementation
          "the raw callable needs its retained action to the comparison's computed semantic endpoints"
  let framed ← presentMorphism input source target (some context) (some (sourceMap, targetMap))
  let dependencies := #[input, source, target] ++
    sourceComparison.toArray.flatMap (fun selected => #[selected.original, selected.comparisonMap]) ++
    targetComparison.toArray.flatMap (fun selected => #[selected.original, selected.comparisonMap])
  return {
    wire := framed, actual, source := actualSource, target := actualTarget,
    template := .wire .map framed, dependencies }

/-- A public wrapper retains the exact framed child and the actual endpoint
views selected above. Its logical map and original semantic endpoints remain
fixed; the wrapper introduces no new mathematical selection. -/
def publicMorphismFrame (context : CategoryContext) (source target : Wire)
    (frame : PreparedMorphismFrame) : TermElabM PreparedMorphismFrame := do
  if let some payload := ComputationalData.recordPayload? frame.wire.fragment then
    if (Backend.TypedMap.decode payload.json).isOk then return frame
  let template : ActionDataTemplate := .ctor "typedMap"
    #[.wire .retained frame.source, .wire .retained frame.target, frame.template]
  let (data, dependencies) ← renderCapturedActionData template
  let result := { frame.wire with
    payload := (← combinedRecipePayload frame.wire.value data dependencies)
    morphismFraming := none, actionRecipe := none, intrinsicAssembly := none,
    capturedInvocation := none, callableEndpoints := none }
  let result ← retainIntrinsicAssembly result .map context template #[] #[] (.retained, .retained)
  let result ← retainCallableEndpoints result source target context
  return { frame with
    wire := result, template,
    dependencies := frame.dependencies ++ dependencies }

/-- Demand an existing frame through its retained input and exact comparisons.
A changed child can consume the outer frame only when its whole result retains
that same complete endpoint interface. Otherwise its independently fixed
semantic endpoint interface must match the comparison maps before composition. -/
def observeRetainedMorphismFrameWith (reader : CallablePreparationReader)
    (wire : Wire) (frame : MorphismFraming) : TermElabM PreparedMorphismFrame := do
  let replayed ← presentMorphism frame.input frame.source frame.target frame.context frame.comparisons
  unless sameCompleteWireContext replayed wire do
    throwStratum .unavailable "the observed callable lost its complete retained framing producer"
  let context ← completedCallableContext frame.input frame.source frame.target
  discard <| framingContext (some context) frame.context
  let observed ← reader.observe context frame.input
  let observed ← forwardRetainedValue observed frame.input.value
  if sameCompleteWireContext observed frame.input then
    return ← prepareMorphismFrameWith reader context frame.input frame.source frame.target frame.comparisons
  let some endpoints ← retainedCallableEndpoints? observed context
    | throwError "the observed frame input omitted its complete whole-map interface"
  let consumed := observed.morphismFramed && sameCompleteWireContext endpoints.1
      (← forwardRetainedValue frame.source endpoints.1.value) &&
    sameCompleteWireContext endpoints.2
      (← forwardRetainedValue frame.target endpoints.2.value)
  let retainedReader := { reader with observe := fun _ selected => pure selected }
  if consumed then
    let prepared ← prepareMorphismFrameWith retainedReader context observed frame.source frame.target
    return { prepared with dependencies := #[wire, frame.input] ++ prepared.dependencies }
  let sourceComparison ← prepareEndpointComparisonWith reader context frame.source false
    (frame.comparisons.bind (·.1))
  let targetComparison ← prepareEndpointComparisonWith reader context frame.target true
    (frame.comparisons.bind (·.2))
  -- Without a selected comparison, this frame still owns the original object
  -- occurrence and its pending action. Read that exact occurrence just as the
  -- raw callable reads its retained endpoints; equality selects neither input.
  -- A selected comparison continues to own both of its checked endpoint views.
  let source ← if sourceComparison.isSome then pure frame.source
    else reader.readData .object frame.source
  let target ← if targetComparison.isSome then pure frame.target
    else reader.readData .object frame.target
  let semanticSource := (sourceComparison.map (·.semantic)).getD source
  let semanticTarget := (targetComparison.map (·.semantic)).getD target
  unless sameCompleteWireContext endpoints.1
      (← forwardRetainedValue semanticSource endpoints.1.value) &&
      sameCompleteWireContext endpoints.2
        (← forwardRetainedValue semanticTarget endpoints.2.value) do
    throwStratum .noImplementation
      "the observed callable has no retained action to the selected comparison's complete semantic endpoints"
  -- This is a new outer representation frame over the exact whole child.
  -- Its intrinsic alias retains that child; no payload is reconstructed or
  -- promoted, and the old whole frame remains an explicit dependency.
  let input := { observed with
    morphismFramed := false, morphismFraming := none, intrinsicAssembly := none,
    actionRecipe := none, capturedInvocation := none, callableEndpoints := none }
  let input ← retainIntrinsicAssembly input .map context
    (.retained (.wire .map observed)) #[] #[] (.retained, .retained)
  let input ← retainCallableEndpoints input semanticSource semanticTarget context
  let comparisons := some (sourceComparison.map (·.comparisonMap), targetComparison.map (·.comparisonMap))
  let prepared ← prepareMorphismFrameWith retainedReader context input source target comparisons
  return { prepared with
    dependencies := #[wire, frame.input, observed] ++ prepared.dependencies ++
      sourceComparison.toArray.flatMap (fun selected => #[selected.original, selected.comparisonMap]) ++
      targetComparison.toArray.flatMap (fun selected => #[selected.original, selected.comparisonMap]) }

/-- Read only a template's explicitly retained whole occurrence. A constructed
packet has no such receipt merely because its rendered bytes agree with one. -/
partial def capturedTemplateWire? : ActionDataTemplate → Option Wire
  | .wire _ wire => some wire
  | .retained child | .logical child => capturedTemplateWire? child
  | _ => none

/-- Obtain actual validation views solely from the complete retained endpoint
comparisons in this request. No carrier or data lookup selects a presentation. -/
def operationArgumentObjects (h : Harness) (context : CategoryContext)
    (wires : Array Wire) : TermElabM (Array Wire × Array (Wire × Expr)) := do
  let retained ← h.serviceOperands.get
  let mut inputs := wires
  for wire in wires do
    for handle in ← normalizedOperationClosure retained wire do
      let some input := retained[handle]?
        | throwError "the prepared argument lost an exact normalized dependency"
      inputs := inputs.push input
  let mut views := #[]
  for input in inputs do
    if input.form.category == CategoryId.sets &&
        (← whnfR (← inferType input.value)).isSort then
      if let some presentation := input.endpointPresentation then
        let (original, actual) ← operationComparisonEnds context presentation.comparison
        unless ← withoutModifyingState (withTransparency .all <| isDefEq original input.value) do
          throwError "the argument comparison changed its complete selected endpoint"
        views := views.push (input, actual)
  return (inputs, views)

/-- Retain the whole prepared packet at the original independently selected
point. Nested service lookup can then reuse it without interpreting a fresh
mediator or reconstructing an opaque child's meaning. A producer may supply its
already complete framed Wire; unchanged data preserve the original context. -/
def retainPreparedOperationArgument (h : Harness) (context : CategoryContext)
    (point : Wire) (data : DataOwnership.Data) (template : ActionDataTemplate) (actual : Expr)
    (dependencies : Array Wire) (framed : Option Wire := none) :
    TermElabM PreparedOperationArgument := do
  let (captured, _) ← renderCapturedActionData template
  unless captured == data do
    throwError "the prepared argument changed its exact retained field template"
  let prepared ← match framed with
    | some framed => do
      unless framed.value == point.value && framed.fragment == data do
        throwError "the prepared argument producer changed its complete point or packet"
      discard <| framingContext (some context) framed.categoryContext
      pure framed
    | none =>
      if data == point.fragment then pure point else
        pure { point with
          payload := (← combinedRecipePayload point.value data dependencies)
          morphismFramed := true, morphismFraming := none
          categoryContext := some context }
  let prepared := { prepared with
    serviceHandles := prepared.serviceHandles ++ (← retainServiceOperands h dependencies) }
  return { data, template, actual, dependencies := #[prepared] ++ dependencies }

/-- Reproduce the ordinary point frame from supplied endpoint occurrences.
No expression cache or fresh endpoint selection participates in reassembly. -/
def frameRetainedPoint (context : CategoryContext) (point source target : Wire) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  CategoryContext.checkMorphism context point.value source.value target.value
  if point.morphismFramed then return (point.fragment, #[])
  let graph := point.json.getArr?.isOk ||
    (point.json.getObjValAs? String "ctor").toOption == some "finiteGraph"
  let coordinatePoint ← if (point.json.getObjValAs? String "ctor").toOption ==
      some "element" then
    withoutModifyingState <| withTransparency .all <|
      isDefEq source.value (← closedElementDomain (← registryState))
  else pure false
  unless coordinatePoint || graph || source.endpointPresentation.isSome ||
      target.endpointPresentation.isSome do return (point.fragment, #[])
  let framed ← presentMorphism point source target (some context)
  if !graph && !coordinatePoint then return (framed.fragment, #[source, target])
  return (← scopedNode "typedMap" #[source.fragment, target.fragment, framed.fragment],
    #[source, target])

/-- Prepare an original point at the normalized actual endpoints. Products are
reconstructed through their captured presentation and ordered child occurrences.
Each child consumes its domain inverse and target forward exactly once. -/
partial def prepareOperationPointArgumentWith
    (readRecipe : Wire → TermElabM (Array Wire))
    (reader : CallablePreparationReader)
    (h : Harness)
    (context : CategoryContext) (point originalDomain originalTarget domain target : Wire)
    (data : DataOwnership.Data) (parameters : Array Wire) : TermElabM PreparedOperationArgument := do
  checkOperationNormalizedEndpoint originalDomain domain
  checkOperationNormalizedEndpoint originalTarget target
  -- The caller supplies the original complete occurrences selected by the
  -- positioned point/field checks, or by the checked ordered product context.
  -- Their presentation and refinement history are inputs: a fresh read of a
  -- formal Hom cannot reconstruct that independently selected context.
  for endpoint in #[originalDomain, originalTarget] do
    CategoryContext.checkObject context endpoint.value
    discard <| framingContext (some context) endpoint.categoryContext
  let retained ← h.serviceOperands.get
  for input in #[point, originalDomain, originalTarget] do
    discard <| operationPresentationOperandClosure retained input
  CategoryContext.checkMorphism context point.value originalDomain.value originalTarget.value
  discard <| framingContext (some context) point.categoryContext
  discard <| checkedFragment data.validate
  if point.completedData || point.callableObserved then
    throwStratum .noImplementation "a completed point retains its own actual invocation interface"
  if data != point.fragment then
    let (framed, _) ← frameRetainedPoint context point originalDomain originalTarget
    unless framed == data do
      throwStratum .unavailable "the prepared operation argument changed an original positioned point"
  let retainedPoint := point
  let mut point := point
  let mut data := data
  let mut comparisons : Option (Option Wire × Option Wire) := none
  let changed := !sameOperationEndpointAction originalDomain.endpointPresentation domain.endpointPresentation ||
    !sameOperationEndpointAction originalTarget.endpointPresentation target.endpointPresentation
  if let some origin := point.morphismFraming then
    unless sameCompleteWireContext origin.source originalDomain &&
        sameCompleteWireContext origin.target originalTarget do
      throwStratum .ambiguousRealization
        "the original point frame has different complete selected endpoint occurrences"
    let replayed ← presentMorphism origin.input origin.source origin.target origin.context origin.comparisons
    unless sameCompleteWireContext replayed point do
      throwStratum .unavailable
        "the original point framing does not reproduce its complete packet and provenance"
    -- Service preparation may append or freshly allocate dependency handles.
    -- The complete framing selection above still agrees exactly; separately
    -- validate every original and current occurrence graph without comparing
    -- the allocation numbers or selecting a dependency by its data.
    let retained ← h.serviceOperands.get
    for input in #[point, origin.input, origin.source, origin.target, originalDomain, originalTarget] do
      discard <| operationPresentationOperandClosure retained input
    -- Keep the supplied framed occurrence as the service dependency. Its
    -- checked raw input is local producer provenance, not a second competing
    -- copied packet when framing left the bytes unchanged.
    point := origin.input
    data := origin.input.fragment
    if !changed then comparisons := origin.comparisons
  let (expected, actualDomain, actualTarget) ← operationFramedPoint context point domain target
  if let some origin ← retainedPointOrigin? point then
    if let .product presentation retainedDomain first second firstPath secondPath := origin.recipe then
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq retainedDomain originalDomain.value) do
        throwError "the prepared product point changed its original generalized domain"
      let #[firstTarget, secondTarget] := originalTarget.productComponents
        | throwStratum .noImplementation
            "the original product point has no retained complete ordered target context"
      let product ← withTransparency .all <| whnf originalTarget.value
      unless product.isAppOfArity ``Prod 2 do
        throwError "the prepared product point has a different complete target"
      let fields := product.getAppArgs
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq firstTarget.value fields[0]! <&&> isDefEq secondTarget.value fields[1]!) do
        throwError "the original product point changed its ordered complete factors"
      unless data == origin.fragment do
        throwStratum .unavailable "the product argument lost its original positioned child data"
      let paths := #[firstPath, secondPath]
      let originalFan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[first.value, second.value]
      let original ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
        #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[presentation], originalFan]
      unless ← withoutModifyingState (withTransparency .all <| isDefEq original point.value) do
        throwError "the original product trace changed its complete selected mediator"
      let (children, _) ← normalizeOperationProducts h context #[firstTarget, secondTarget] parameters (← reader.objects)
      let #[normalizedFirst, normalizedSecond] := children
        | throwError "the prepared product lost its ordered normalized factors"
      let first ← prepareOperationPointArgumentWith readRecipe reader h context first originalDomain firstTarget
        domain normalizedFirst (← checkedFragment (data.project paths[0]!)) parameters
      let second ← prepareOperationPointArgumentWith readRecipe reader h context second originalDomain secondTarget
        domain normalizedSecond (← checkedFragment (data.project paths[1]!)) parameters
      let some (_, firstActual) := Language.homEnds? (← inferType first.actual)
        | throwError "the prepared first component lost its complete actual target"
      let some (_, secondActual) := Language.homEnds? (← inferType second.actual)
        | throwError "the prepared second component lost its complete actual target"
      let legs ← operationProductLegs context firstActual secondActual
        normalizedFirst.fragment normalizedSecond.fragment
      let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[first.actual, second.actual]
      let actual ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
        #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[legs.presentation], fan]
      discard <| StructuredResult.checkReconstruction actual
      CategoryContext.checkMorphism context actual actualDomain actualTarget
      unless ← withoutModifyingState (withTransparency .all <| isDefEq actual expected) do
        throwError "the prepared product argument changed its original complete comparison composite"
      let template ← if firstPath == #[.index 0] && secondPath == #[.index 1] then
          pure (ActionDataTemplate.array #[first.template, second.template])
        else do
          let actualSource ← callableActualEndpoint context domain true
          let actualTarget ← callableActualEndpoint context target false
          pure (.ctor "typedMap" #[.wire .retained actualSource, .wire .retained actualTarget,
            .ctor "mediator" #[first.template, second.template]])
      let (prepared, _) ← renderCapturedActionData template
      return ← retainPreparedOperationArgument h context retainedPoint prepared template actual
        (#[retainedPoint, domain, target, normalizedFirst, normalizedSecond] ++
          first.dependencies ++ second.dependencies)
  let recipeInputs ← readRecipe point
  let (recipeInputs, _) ← normalizeOperationProducts h context recipeInputs parameters (← reader.objects)
  let (inputs, views) ← operationArgumentObjects h context
    (#[domain, target] ++ parameters ++ recipeInputs)
  if point.morphismFramed then
    let framed ← prepareMorphismFrameWith reader context point domain target comparisons
    let framed ← publicMorphismFrame context domain target framed
    unless ← withoutModifyingState (withTransparency .all <| isDefEq framed.actual expected) do
      throwError "the whole point observer changed its selected actual comparison composite"
    let localInputs ← IO.mkRef #[domain, target]
    let scope ← callableTemplateValidationScope context expected framed.wire.fragment framed.template
      (some localInputs)
    let objects ← reader.interfaceObjects
      (← operationPresentationObjects inputs views (← localInputs.get))
    validateOperationPresentationMap expected framed.source.fragment framed.target.fragment
      framed.wire.fragment objects (some scope)
    return ← retainPreparedOperationArgument h context retainedPoint framed.wire.fragment (.wire .map framed.wire) expected
      (#[retainedPoint] ++ inputs ++ framed.dependencies) (some framed.wire)
  let sourceAction ← operationComponentPresentation context domain inputs views (← reader.objects)
  let targetAction ← operationComponentPresentation context target inputs views (← reader.objects)
  -- The raw callable keeps its original semantic endpoint occurrences. Their
  -- local positions, rather than equal packet keys, select the validation Hom.
  let originalTemplate : ActionDataTemplate :=
    if (point.json.getObjValAs? String "ctor").toOption == some "typedMap" then
      .retained (.wire .map point)
    else .ctor "typedMap" #[.wire .retained sourceAction.semanticEndpoint,
      .wire .retained targetAction.semanticEndpoint, .retained (.wire .map point)]
  let (original, originalInputs) ← renderCapturedActionData originalTemplate
  let localInputs ← IO.mkRef #[domain, target]
  let scope ← callableTemplateValidationScope context point.value original originalTemplate (some localInputs)
  let objects ← reader.interfaceObjects
    (← operationPresentationObjects inputs views (← localInputs.get))
  validateOperationPresentationMap point.value sourceAction.semanticData targetAction.semanticData
    original objects (some scope)
  let input := { point with
    payload := (← combinedRecipePayload point.value original (#[point] ++ originalInputs))
    morphismFramed := false, morphismFraming := none, intrinsicAssembly := none,
    actionRecipe := none, capturedInvocation := none, callableEndpoints := none,
    pointDataInterface := none, pointOrigin := none }
  let input ← retainIntrinsicAssembly input .map context originalTemplate #[] #[] (.retained, .retained)
  let input ← retainCallableEndpoints input sourceAction.semanticEndpoint targetAction.semanticEndpoint context
  let framed ← prepareMorphismFrameWith reader context input domain target comparisons
  let framed ← publicMorphismFrame context domain target framed
  unless ← withoutModifyingState (withTransparency .all <| isDefEq framed.actual expected) do
    throwError "the point frame changed its independently selected actual comparison composite"
  let scope ← callableTemplateValidationScope context expected framed.wire.fragment framed.template
    (some localInputs)
  let objects ← reader.interfaceObjects
    (← operationPresentationObjects inputs views (← localInputs.get))
  validateOperationPresentationMap expected framed.source.fragment framed.target.fragment
    framed.wire.fragment objects (some scope)
  retainPreparedOperationArgument h context retainedPoint framed.wire.fragment (.wire .map framed.wire) expected
    (#[retainedPoint] ++ inputs ++ framed.dependencies) (some framed.wire)

/-- Native point data have an explicitly declared conversion to a whole map.
Every other map keeps its current representation: observation cannot introduce
a fresh endpoint-comparison frame and pretend it has already been consumed. -/
def capturePointCallableWith
    (readEndpoints : Wire → CategoryContext → TermElabM (Wire × Wire))
    (input : Wire) (context : CategoryContext) : TermElabM Wire := do
  if input.pointDataInterface.isSome then
    captureCompleteCallableWith readEndpoints input context
  else pure input

/-- A product point's positioned child is either its complete original map or
the exact frame already supplied for that map. A public typed-map wrapper keeps
the frame's selected actual endpoints; equal terms or packets select nothing. -/
def checkIntrinsicProductChild (context : CategoryContext) (original : Wire)
    (template : ActionDataTemplate) : TermElabM Unit := do
  let (selected, publicEndpoints) ← match template with
    | .wire .map selected => pure (selected, none)
    | .ctor "typedMap" #[.wire .retained source, .wire .retained target, .wire .map selected] =>
        pure (selected, some (source, target))
    | _ => throwStratum .unavailable "the product point lost its positioned typed child"
  unless sameCompleteWireContext selected original do
    let some frame := selected.morphismFraming
      | throwStratum .unavailable "the product point changed its complete selected child"
    let replayed ← presentMorphism frame.input frame.source frame.target frame.context frame.comparisons
    unless sameCompleteWireContext replayed selected do
      throwStratum .unavailable "the product point lost its exact child frame"
    unless sameCompleteWireContext frame.input original do
      -- Observation can retain the whole current child in a new outer frame.
      -- Follow that explicit alias only; its packet equality does not choose it.
      let some retainedChild ← retainedIntrinsicAssembly? frame.input .map
        | throwStratum .unavailable "the product point frame belongs to a different child"
      let .retained (.wire .map child) := retainedChild.template
        | throwStratum .unavailable "the product point frame lost its exact whole child"
      unless retainedChild.endpointRoles == (.retained, .retained) &&
          sameCompleteWireContext child original do
        throwStratum .unavailable "the product point frame changed its retained child occurrence"
  if let some (source, target) := publicEndpoints then
    let some endpoints ← retainedCallableEndpoints? selected context
      | throwStratum .unavailable "the product point frame lost its complete endpoint receipt"
    let actualSource ← callableActualEndpoint context endpoints.1 true
    let actualTarget ← callableActualEndpoint context endpoints.2 false
    unless sameCompleteWireContext source actualSource && sameCompleteWireContext target actualTarget do
      throwStratum .unavailable "the product point wrapper changed its selected frame endpoints"

/-- Both intrinsic observation entries consume this same checked tree body.
Only their entry checks differ: a supplied assembly is authenticated, while the
current entry reads the assembly directly from its sole Wire input. -/
private def observeIntrinsicAssemblyBodyWith
    (observeChild : ActionDataRole → Wire → TermElabM Wire)
    (readEndpoints : Wire → CategoryContext → TermElabM (Wire × Wire))
    (h : Harness) (wire : Wire) (assembly : IntrinsicAssembly) : TermElabM Wire := do
  let (original, _) ← renderCapturedActionData assembly.template
  unless original == wire.fragment do
    throwStratum .unavailable "the intrinsic assembly changed its original positioned child data"
  -- A literal point's typed owner slot licenses refreshing its point receipt.
  -- A matching packet tag or historical PointOrigin is insufficient.
  let literalPointData ← match assembly.template with
    | .ctor "element" #[.wire .object owner, .ctor "numeral" #[.literal number]] => do
      let .map context := assembly.result
        | throwError "the captured literal point changed its complete result role"
      unless assembly.endpointRoles == (.object, .object) do
        throwError "the captured literal point changed its original endpoint roles"
      let some origin ← retainedPointOrigin? wire
        | throwStratum .unavailable "the captured literal point lost its current original producer"
      unless origin.formal == wire.value && origin.fragment == wire.fragment &&
          origin.context.bundle == context.bundle &&
          origin.context.expression.syntacticEq context.expression do
        throwStratum .unavailable "the captured literal point changed its original full context"
      let .element selected inputs := origin.recipe
        | throwError "the captured literal point changed its original construction"
      unless inputs.isEmpty && sameCompleteWireContext selected owner do
        throwStratum .unavailable "the captured literal point changed its complete selected owner"
      unless sameCallableEndpoints wire.callableEndpoints (some {
          formal := origin.formal, fragment := origin.fragment, context := origin.context,
          source := origin.source, target := origin.target }) &&
          (← retainedCallableEndpoints? wire context).isSome do
        throwStratum .unavailable "the captured literal point changed its original endpoint receipt"
      pure (some number)
    | _ => pure none
  -- A current product recipe records the selected presentation and the two
  -- original children. Authenticate its exact assembly positions before those
  -- children are observed; historical origins cannot license a new receipt.
  let productPointRecipe : Option PointRecipe ← match wire.pointOrigin with
    | some origin => match origin.recipe with
      | .product _ _ first second firstPath secondPath => do
        if wire.completedData || origin.formal != wire.value || origin.fragment != wire.fragment then
          pure none
        else do
          let .map context := assembly.result
            | throwError "the captured product point changed its complete result role"
          unless assembly.endpointRoles == (.object, .object) &&
              origin.context.bundle == context.bundle &&
              origin.context.expression.syntacticEq context.expression do
            throwStratum .unavailable "the captured product point changed its original full context"
          unless sameCallableEndpoints wire.callableEndpoints (some {
              formal := origin.formal, fragment := origin.fragment, context := origin.context,
              source := origin.source, target := origin.target }) &&
              (← retainedCallableEndpoints? wire context).isSome do
            throwStratum .unavailable "the captured product point changed its original endpoint receipt"
          let (firstTemplate, secondTemplate) ← match assembly.template with
            | .ctor "mediator" #[firstTemplate, secondTemplate] => do
              unless firstPath == #[.field "args", .index 0] &&
                  secondPath == #[.field "args", .index 1] do
                throwError "the captured product point changed its mediator child positions"
              pure (firstTemplate, secondTemplate)
            | .array #[firstTemplate, secondTemplate] => do
              unless firstPath == #[.index 0] && secondPath == #[.index 1] do
                throwError "the captured product point changed its ordered array positions"
              pure (firstTemplate, secondTemplate)
            | _ => throwStratum .unavailable "the product point lost its original typed assembly"
          checkIntrinsicProductChild context first firstTemplate
          checkIntrinsicProductChild context second secondTemplate
          pure (some origin.recipe)
      | _ => pure none
    | none => pure none
  let observed ← IO.mkRef (#[] : Array (ActionDataRole × Wire × Wire))
  let observe := fun (role : ActionDataRole) (original : Wire) => do
    if let some (_, _, actual) := (← observed.get).find? (fun (selected, input, _) =>
        selected == role && sameCompleteWireContext input original) then return actual
    let actual ← observeChild role original
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType actual.value) (← inferType original.value) <&&>
          isDefEq actual.value original.value) do
      throwError "an intrinsic child observation changed its complete formal selection"
    discard <| framingContext original.categoryContext actual.categoryContext
    observed.modify (·.push (role, original, actual))
    return actual
  let template ← mapActionTemplateWires observe assembly.template
  let checkEndpoint := fun (index : Nat) (direction : String)
      (fields : IntrinsicMapFields) (callable expected actual : Wire) => do
    let context := fields.context
    discard <| framingContext (some context) expected.categoryContext
    discard <| framingContext (some context) actual.categoryContext
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType expected.value) (← inferType actual.value) <&&>
          isDefEq expected.value actual.value) do
      throwError "an intrinsic callable field changed its complete selected endpoint"
    let returned := actual
    let actual ← forwardRetainedValue actual expected.value
    unless sameCompleteWireContext expected actual do
      -- Report exact comparison failures only after the existing guard fails.
      -- Hashes abbreviate formal terms; neither hashes nor packet equality select data.
      let sameContext := fun (left right : Option CategoryContext) =>
        match left, right with
        | none, none => true
        | some left, some right => left.expression.syntacticEq right.expression
        | _, _ => false
      let wireFlags := fun (left right : Wire) => (#[("value", left.value == right.value),
        ("json", left.json == right.json), ("ownership", left.ownership == right.ownership),
        ("serviceInputPaths", left.serviceInputPaths == right.serviceInputPaths),
        ("pointDataInterface", left.pointDataInterface == right.pointDataInterface),
        ("objectIso", left.objectIso == right.objectIso),
        ("endpointPresentation.comparison",
          left.endpointPresentation.map (·.comparison) == right.endpointPresentation.map (·.comparison)),
        ("endpointPresentation.forward",
          left.endpointPresentation.map (·.forward) == right.endpointPresentation.map (·.forward)),
        ("endpointPresentation.backward",
          left.endpointPresentation.map (·.backward) == right.endpointPresentation.map (·.backward)),
        ("endpointPresentation.forwardOwnership", left.endpointPresentation.map (·.forwardOwnership) ==
          right.endpointPresentation.map (·.forwardOwnership)),
        ("endpointPresentation.backwardOwnership", left.endpointPresentation.map (·.backwardOwnership) ==
          right.endpointPresentation.map (·.backwardOwnership)),
        ("endpointPresentation.maps", sameEndpointComparisonMaps
          (left.endpointPresentation.bind (·.maps)) (right.endpointPresentation.bind (·.maps))),
        ("endpointPresentation.namedRefinement", sameNamedRefinementOrigin
          (left.endpointPresentation.bind (·.namedRefinement))
          (right.endpointPresentation.bind (·.namedRefinement))),
        ("productComponents", sameProductComponents left.productComponents right.productComponents),
        ("morphismFraming", sameMorphismFraming left.morphismFraming right.morphismFraming),
        ("actionRecipe", sameActionRecipe left.actionRecipe right.actionRecipe),
        ("intrinsicAssembly", sameIntrinsicAssembly left.intrinsicAssembly right.intrinsicAssembly),
        ("capturedInvocation.occurrence",
          left.capturedInvocation.map (·.occurrence) == right.capturedInvocation.map (·.occurrence)),
        ("callableEndpoints", sameCallableEndpoints left.callableEndpoints right.callableEndpoints),
        ("pointOrigin", samePointOrigin left.pointOrigin right.pointOrigin),
        ("payload", sameOperationPresentationPayload left.payload right.payload),
        ("form", sameOperationPresentationForm left.form right.form),
        ("morphismFramed", left.morphismFramed == right.morphismFramed),
        ("callableObserved", left.callableObserved == right.callableObserved),
        ("objectObserved", left.objectObserved == right.objectObserved),
        ("presentationIsos", left.presentationIsos == right.presentationIsos),
        ("category.bundle", left.categoryContext.map (·.bundle) == right.categoryContext.map (·.bundle)),
        ("category.expression", sameContext left.categoryContext right.categoryContext),
        ("constructionInputs", left.constructionInputs == right.constructionInputs),
        ("constructionInputOwnership", left.constructionInputOwnership == right.constructionInputOwnership),
        ("liftExecution", sameRetainedLiftExecution left.liftExecution right.liftExecution),
        ("proofSources", left.proofSources.length == right.proofSources.length &&
          (left.proofSources.zip right.proofSources).all (fun (a, b) =>
            sameCompleteWireContext (retainedSnapshotWire a) (retainedSnapshotWire b)))] :
          Array (String × Bool))
      let summary := fun (input : Wire) => Json.mkObj [
        ("form", toJson input.form.id), ("category", toJson input.form.category.raw),
        ("formalHash", toJson (toString (hash input.value))),
        ("producer", toJson ((Trace.producerAnchor? input.value).map (·.occurrence))),
        ("contextHash", toJson (input.categoryContext.map fun c => toString (hash c.bundle))),
        ("packetCtor", toJson ((input.json.getObjValAs? String "ctor").toOption)),
        ("payload", toJson (match input.payload with
          | .ordinary .. => "ordinary"
          | .construction .. => "construction"
          | .computed _ data => match data with
            | .inline _ => "computed.inline" | .opaque .. => "computed.opaque"
            | .owned .. => "computed.owned" | .scoped _ => "computed.scoped"
            | .recipe _ => "computed.recipe")),
        ("ownershipSlots", toJson input.ownership.size),
        ("actualData", toJson input.actualData), ("completedData", toJson input.completedData),
        ("objectObserved", toJson input.objectObserved),
        ("callableObserved", toJson input.callableObserved),
        ("morphismFramed", toJson input.morphismFramed),
        ("morphismFraming", toJson input.morphismFraming.isSome),
        ("endpointPresentation", toJson input.endpointPresentation.isSome),
        ("pointDataInterface", toJson input.pointDataInterface.isSome),
        ("actionRecipe", toJson input.actionRecipe.isSome),
        ("intrinsicAssembly", toJson input.intrinsicAssembly.isSome),
        ("callableEndpoints", toJson input.callableEndpoints.isSome),
        ("pointOrigin", toJson input.pointOrigin.isSome),
        ("invocation", toJson (input.capturedInvocation.map (·.occurrence)))]
      let mut flags := wireFlags expected actual
      let mut children : Array (String × Wire × Wire) := #[]
      if let (some left, some right) := (expected.callableEndpoints, actual.callableEndpoints) then
        flags := flags ++ #[("callableEndpoints.formal", left.formal == right.formal),
          ("callableEndpoints.fragment", left.fragment == right.fragment),
          ("callableEndpoints.context.bundle", left.context.bundle == right.context.bundle),
          ("callableEndpoints.context.expression", left.context.expression.syntacticEq right.context.expression)]
        children := children ++ #[("callableEndpoints.source", left.source, right.source),
          ("callableEndpoints.target", left.target, right.target)]
      if let (some left, some right) := (expected.actionRecipe, actual.actionRecipe) then
        flags := flags ++ #[("actionRecipe.morphism", left.morphism == right.morphism),
          ("actionRecipe.owner", left.owner == right.owner),
          ("actionRecipe.application", left.application == right.application),
          ("actionRecipe.formal", left.formal == right.formal),
          ("actionRecipe.fragment", left.fragment == right.fragment),
          ("actionRecipe.source.bundle", left.source.bundle == right.source.bundle),
          ("actionRecipe.source.expression", left.source.expression.syntacticEq right.source.expression),
          ("actionRecipe.target.bundle", left.target.bundle == right.target.bundle),
          ("actionRecipe.target.expression", left.target.expression.syntacticEq right.target.expression),
          ("actionRecipe.descriptor", sameActionTemplate left.descriptor right.descriptor),
          ("actionRecipe.endpoints", sameEndpointComparisonMaps left.endpoints right.endpoints),
          ("actionRecipe.imageEndpoints", sameEndpointComparisonMaps left.imageEndpoints right.imageEndpoints)]
        children := children.push ("actionRecipe.original", left.original, right.original)
      if let (some left, some right) := (expected.morphismFraming, actual.morphismFraming) then
        flags := flags ++ #[("morphismFraming.context.bundle",
          left.context.map (·.bundle) == right.context.map (·.bundle)),
          ("morphismFraming.context.expression", sameContext left.context right.context),
          ("morphismFraming.comparisons", match left.comparisons, right.comparisons with
            | none, none => true
            | some (a, b), some (c, d) =>
                sameProductComponents a.toArray c.toArray && sameProductComponents b.toArray d.toArray
            | _, _ => false)]
        children := children ++ #[("morphismFraming.input", left.input, right.input),
          ("morphismFraming.source", left.source, right.source),
          ("morphismFraming.target", left.target, right.target)]
      if let (some left, some right) := (expected.intrinsicAssembly, actual.intrinsicAssembly) then
        flags := flags ++ #[("intrinsicAssembly.result", match left.result, right.result with
            | .object a, .object b | .map a, .map b =>
                a.expression.syntacticEq b.expression && a.bundle == b.bundle
            | .value a, .value b => a == b
            | _, _ => false),
          ("intrinsicAssembly.formal", left.formal == right.formal),
          ("intrinsicAssembly.fragment", left.fragment == right.fragment),
          ("intrinsicAssembly.endpointRoles", left.endpointRoles == right.endpointRoles),
          ("intrinsicAssembly.template", sameActionTemplate left.template right.template),
          ("intrinsicAssembly.maps.size", left.maps.size == right.maps.size),
          ("intrinsicAssembly.equalObjects.size", left.equalObjects.size == right.equalObjects.size)]
        for ((a, b), position) in (left.maps.zip right.maps).zipIdx do
          flags := flags ++ #[(s!"intrinsicAssembly.maps[{position}].context.bundle", a.context.bundle == b.context.bundle),
            (s!"intrinsicAssembly.maps[{position}].context.expression", a.context.expression.syntacticEq b.context.expression)]
          children := children ++ #[(s!"intrinsicAssembly.maps[{position}].source", a.source, b.source),
            (s!"intrinsicAssembly.maps[{position}].target", a.target, b.target),
            (s!"intrinsicAssembly.maps[{position}].callable", a.callable, b.callable)]
        for ((a, b), position) in ((actionTemplateInputs left.template).zip
            (actionTemplateInputs right.template)).zipIdx do
          children := children.push (s!"intrinsicAssembly.template.input[{position}]", a, b)
        for (((a, b), (c, d)), position) in (left.equalObjects.zip right.equalObjects).zipIdx do
          children := children ++ #[(s!"intrinsicAssembly.equalObjects[{position}].first", a, c),
            (s!"intrinsicAssembly.equalObjects[{position}].second", b, d)]
      if let (some left, some right) := (expected.pointOrigin, actual.pointOrigin) then
        flags := flags ++ #[("pointOrigin.formal", left.formal == right.formal),
          ("pointOrigin.fragment", left.fragment == right.fragment),
          ("pointOrigin.context.bundle", left.context.bundle == right.context.bundle),
          ("pointOrigin.context.expression", left.context.expression.syntacticEq right.context.expression)]
        children := children ++ #[("pointOrigin.source", left.source, right.source),
          ("pointOrigin.target", left.target, right.target)]
        match left.recipe, right.recipe with
        | .element a inputs, .element b actualInputs =>
            flags := flags.push ("pointOrigin.element.dependencies", sameProductComponents inputs actualInputs)
            children := children.push ("pointOrigin.element.owner", a, b)
        | .product p d a b x y, .product q e c f u v =>
            flags := flags ++ #[("pointOrigin.product.presentation", p == q),
              ("pointOrigin.product.domain", d == e), ("pointOrigin.product.paths", x == u && y == v)]
            children := children ++ #[("pointOrigin.product.first", a, c), ("pointOrigin.product.second", b, f)]
        | .alias a, .alias b => children := children.push ("pointOrigin.alias", a, b)
        | _, _ => flags := flags.push ("pointOrigin.recipe", false)
      for ((left, right), position) in (expected.productComponents.zip actual.productComponents).zipIdx do
        children := children.push (s!"productComponents[{position}]", left, right)
      let mut childDetails : Array Json := #[]
      for (path, left, right) in children do
        unless sameCompleteWireContext left right do
          flags := flags ++ (wireFlags left right).map fun (field, same) => (path ++ "." ++ field, same)
          childDetails := childDetails.push (Json.mkObj [
            ("path", toJson path), ("expected", summary left), ("actual", summary right)])
      let result := match assembly.result with
        | .object _ => "object" | .map _ => "map" | .value _ => "value"
      let roleName := fun (role : ActionDataRole) => match role with
        | .parameter => "parameter" | .object => "object" | .map => "map" | .retained => "retained"
      let originalEndpoint := if direction == "source" then fields.source else fields.target
      let details := Json.mkObj [
        ("assembly", summary wire), ("resultRole", toJson result),
        ("assemblyFormalHash", toJson (toString (hash assembly.formal))),
        ("endpointRoles", toJson #[roleName assembly.endpointRoles.1, roleName assembly.endpointRoles.2]),
        ("fieldContextHash", toJson (toString (hash fields.context.bundle))),
        ("mapIndex", toJson index), ("direction", toJson direction),
        ("originalCallable", summary fields.callable), ("observedCallable", summary callable),
        ("originalEndpoint", summary originalEndpoint),
        ("observedEndpointChanges", toJson ((wireFlags originalEndpoint expected).filterMap
          fun (field, same) => if same then none else some field)),
        ("expected", summary expected), ("returned", summary returned), ("actual", summary actual),
        ("unequal", toJson (flags.filterMap fun (field, same) => if same then none else some field)),
        ("children", Json.arr (childDetails.extract 0 8)),
        ("omittedChildSummaries", toJson (childDetails.size - 8))]
      throwStratum .malformed
        m!"an intrinsic callable field changed its complete endpoint occurrence or presentation; {details.compress}"
  let maps ← assembly.maps.mapIdxM fun index fields => do
    let source ← observe .object fields.source
    let target ← observe .object fields.target
    let callable ← observe .map fields.callable
    CategoryContext.checkMorphism fields.context callable.value source.value target.value
    -- An unchanged framed occurrence already owns its exact presentation.
    -- Do not strip its frame or reconstruct either endpoint from a formal key.
    unless sameCompleteWireContext source fields.source &&
        sameCompleteWireContext target fields.target &&
        sameCompleteWireContext callable fields.callable do
      let (left, right) ← readEndpoints callable fields.context
      checkEndpoint index "source" fields callable source left
      checkEndpoint index "target" fields callable target right
    return { fields with source, target, callable }
  let equalObjects ← assembly.equalObjects.mapM fun (first, second) => do
    let first ← observe .object first
    let second ← observe .object second
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType first.value) (← inferType second.value) <&&>
          isDefEq first.value second.value) do
      throwError "the intrinsic composition changed its complete shared endpoint"
    let compared ← forwardRetainedValue second first.value
    unless sameCompleteWireContext first compared do
      throwStratum .noImplementation
        "the intrinsic composition requires a selected comparison between its actual middle endpoints"
    return (first, second)
  -- A pending public frame owns its three typed slots. Once that exact child
  -- returns a complete map at the checked endpoint occurrences, keep the whole
  -- returned frame instead of inserting it as the body of a second typedMap.
  -- The map-field witness ties this refresh to the original producer's slots;
  -- a matching packet shape alone cannot discard a wrapper or a point role.
  let refreshTemplate : TermElabM ActionDataTemplate := do
    let .map context := assembly.result | pure template
    let .ctor "typedMap" #[.wire .object actualSource, .wire .object actualTarget,
        .wire .map actual] := template | pure template
    unless actual.completedData && actual.morphismFramed &&
        actual.pointDataInterface.isNone do return template
    let some data := ComputationalData.recordPayload? actual.fragment | pure template
    unless (Backend.TypedMap.decode data.json).isOk do return template
    let .ctor "typedMap" #[.wire .object source, .wire .object target,
        .wire .map original] := assembly.template | pure template
    let #[fields] := assembly.maps | pure template
    unless context.expression.syntacticEq fields.context.expression &&
        sameCompleteWireContext fields.source source &&
        sameCompleteWireContext fields.target target &&
        sameCompleteWireContext fields.callable original do return template
    discard <| framingContext (some context) (some fields.context)
    discard <| framingContext (some context) actual.categoryContext
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType actual.value) (← inferType wire.value) <&&>
          isDefEq actual.value wire.value) do return template
    let some (source, target) ← retainedCallableEndpoints? actual context | pure template
    let sourceView ← forwardRetainedValue source actualSource.value
    let targetView ← forwardRetainedValue target actualTarget.value
    unless sameCompleteWireContext sourceView actualSource &&
        sameCompleteWireContext targetView actualTarget do
      throwStratum .malformed "the completed public frame changed its checked endpoint occurrences"
    let suppliedSource ← checkedFragment (data.project #[.field "args", .index 0])
    let suppliedTarget ← checkedFragment (data.project #[.field "args", .index 1])
    unless suppliedSource == source.fragment && suppliedTarget == target.fragment do
      throwStratum .malformed "the completed public frame changed its exact endpoint packets or suppliers"
    return ActionDataTemplate.wire .map actual
  let template ← refreshTemplate
  let (data, dependencies) ← renderCapturedActionData template
  let same := sameActionTemplate template assembly.template
  let isAlias ← match actionTemplateExecution template with
    | .wire _ child =>
      withoutModifyingState <| withTransparency .all <|
        isDefEq (← inferType child.value) (← inferType wire.value) <&&>
          isDefEq child.value wire.value
    | _ => pure false
  let mut result ← if same && data == wire.fragment then pure wire else do
    -- A direct typed wrapper forwards the child's completed point/map role as
    -- well as its data only for a checked mathematical alias. Reifying a whole
    -- callable as one point keeps its different, independently fixed outer role.
    match actionTemplateExecution template with
    | .wire _ child =>
      if isAlias then do
        let child ← forwardRetainedValue child wire.value
        let context ← match assembly.result with
          | .object context | .map context =>
              framingContext (some context) child.categoryContext
          | .value _ => pure none
        let child := { child with
          form := wire.form, categoryContext := context, morphismFraming := none
          actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none }
        if let .value _ := assembly.result then
          pure { child with
            pointDataInterface := none, morphismFramed := false,
            objectObserved := false, callableObserved := false }
        else pure child
      else pure { wire with
        payload := (← combinedRecipePayload wire.value data dependencies)
        intrinsicAssembly := none, callableEndpoints := none }
    | _ => pure { wire with
        payload := (← combinedRecipePayload wire.value data dependencies)
        intrinsicAssembly := none, callableEndpoints := none }
  if let .inventoryMap _ _ _ original := actionTemplateExecution template then
    if let .map _ := assembly.result then
      if original.completedData then
        result := { result with payload := (← scopedPayload wire.value data), callableObserved := true }
  result ← retainIntrinsicResultAssembly result assembly.result template maps equalObjects assembly.endpointRoles
  let originalChildren := actionTemplateInputs assembly.template
  if !wire.productComponents.isEmpty &&
      sameProductComponents wire.productComponents originalChildren then
    result := { result with productComponents := actionTemplateInputs template }
  if let .map context := assembly.result then
    let forwardedEndpoints ← match actionTemplateExecution template with
      | .wire .map child =>
          if same || !isAlias then pure none else some <$> readEndpoints child context
      | .pointCallable _ _ _ point =>
          if same then pure none else some <$> readEndpoints point context
      | _ => pure none
    match forwardedEndpoints with
    | some (source, target) =>
        result ← retainCallableEndpoints result source target context
    | none =>
        if let some (source, target) ← retainedCallableEndpoints? wire context then
          let source ← observe assembly.endpointRoles.1 source
          let target ← observe assembly.endpointRoles.2 target
          result ← retainCallableEndpoints result source target context
          if let some number := literalPointData then
            let .ctor "element" #[.wire .object owner, .ctor "numeral" #[.literal actualNumber]] := template
              | throwError "the observed literal point lost its original typed owner slot"
            unless actualNumber == number do
              throwError "the observed literal point changed its captured numeral"
            -- These are the same original endpoint observations and the same
            -- positioned owner read. No point execution or new meaning is added.
            result ← retainPointOrigin result context source target (.element owner #[])
          if let some (.product presentation domain first second firstPath secondPath) := productPointRecipe then
            let first ← observe .map first
            let second ← observe .map second
            result ← retainPointOrigin result context source target
              (.product presentation domain first second firstPath secondPath)
        else if literalPointData.isSome || productPointRecipe.isSome then
          throwStratum .unavailable "the captured point lost its original endpoint receipt"
  if sameCompleteWireContext result wire then return wire
  result := { result with
    serviceHandles := (← retainServiceOperands h (dependencies ++ (← observed.get).map (·.2.2))) }
  return result

/-- Observe the current intrinsic tree selected by this Wire. Its callbacks
receive complete retained occurrences; there is no second assembly argument,
expression-cache lookup, producer restart, or registration selection. -/
def observeCurrentIntrinsicAssemblyWith
    (observeChild : ActionDataRole → Wire → TermElabM Wire)
    (readEndpoints : Wire → CategoryContext → TermElabM (Wire × Wire))
    (h : Harness) (wire : Wire) : TermElabM Wire := private_decl% (do
  let some assembly ← currentIntrinsicAssembly? wire
    | throwStratum .unavailable "historical intrinsic context cannot rebuild a different current value"
  observeIntrinsicAssemblyBodyWith observeChild readEndpoints h wire assembly)

/-- A separately supplied assembly retains the original complete selection
guard before its selected tree enters the shared observation body. -/
def observeIntrinsicAssemblyWith
    (observeChild : ActionDataRole → Wire → TermElabM Wire)
    (readEndpoints : Wire → CategoryContext → TermElabM (Wire × Wire))
    (h : Harness) (wire : Wire) (assembly : IntrinsicAssembly) : TermElabM Wire := private_decl% (do
  let some current ← currentIntrinsicAssembly? wire
    | throwStratum .unavailable "historical intrinsic context cannot rebuild a different current value"
  unless sameIntrinsicAssembly (some current) (some assembly) do
    throwStratum .unavailable "the intrinsic observer changed its current producer selection"
  observeIntrinsicAssemblyBodyWith observeChild readEndpoints h wire assembly)

def routedBoundaryContext (wire : Wire) : TermElabM CategoryContext := do
  if let some context := wire.categoryContext then
    CategoryContext.checkObject context wire.value
    return context
  let some category := (← registryState).categories.find? (·.id == wire.form.category)
    | throwError "the routed input lost its independently selected complete category"
  CategoryContext.ofNamed category wire.value

/-- Carry an inspection's exact prepared request through registration choice.
The chosen boundary does not need to be rediscovered by equal expressions,
equal packets, or reconstructed parameter templates. -/
def routedInvocationSelectionDataWith {Data : Type} (h : Harness)
    (selected : SelectedRoutedInvocation)
    (inspect : SelectedRoutedBoundary → TermElabM (Wire × Data)) :
    TermElabM (SelectedRoutedBoundary × Option Registration × Data) := do
  let prepare := fun (boundary : SelectedRoutedBoundary) => do
    try
      let (request, data) ← inspect boundary
      let complete := !(boundary.prefixActions.isEmpty && boundary.parameters.isEmpty)
      let rows ← admittedRegistrations h selected.method.id.raw request complete
      return Except.ok (data, rows)
    catch error =>
      if !Exception.hasConflictingStrata error &&
          Exception.stratum? error == some .noImplementation then
        return Except.error error
      else throw error
  let mut attempts := #[]
  let mut candidates : Array (SelectedRoutedBoundary × Registration × Data) := #[]
  for boundary in selected.boundaries do
    let prepared ← prepare boundary
    attempts := attempts.push (boundary, prepared)
    if let .ok (data, rows) := prepared then
      for row in rows do
        unless candidates.any (fun (_, registration, _) =>
            sameRegistration registration row.registration) do
          candidates := candidates.push (boundary, row.registration, data)
  match candidates with
  | #[(boundary, registration, data)] => return (boundary, some registration, data)
  | #[] =>
    let mut failures := #[]
    for (boundary, prepared) in attempts do
      match prepared with
      | .ok (data, _) => return (boundary, none, data)
      | .error error => failures := failures.push error.toMessageData
    throwStratum .noImplementation
      m!"no exact method boundary has a complete prepared request: {failures}"
  | _ =>
    let choices := candidates.map fun (_, registration, _) =>
      (registration.operation, registration.input, registration.backend)
    throwStratum .ambiguousRealization
      m!"several admitted registrations compute the complete selected method: {choices}"

/-- The request-only compatibility API shares the same complete selection. -/
def routedInvocationSelectionWith (h : Harness)
    (selected : SelectedRoutedInvocation)
    (inspect : SelectedRoutedBoundary → TermElabM Wire) :
    TermElabM (SelectedRoutedBoundary × Option Registration) := do
  let (boundary, registration, _) ← routedInvocationSelectionDataWith h selected
    (fun boundary => do return (← inspect boundary, ()))
  return (boundary, registration)

/-- Local result-schema indices name the original suffix through this explicit
offset. The source boundary remains authoritative for every action, descriptor
and independently captured declaration parameter, including ignored values. -/
def checkRoutedBoundaryPositions (selected : SelectedRoutedInvocation)
    (boundary : SelectedRoutedBoundary) : TermElabM Unit := do
  let original := selected.canonical
  let count := original.prefixActions.size
  unless original.routeOffset == 0 && !original.materializeRoute &&
      original.descriptors.size == count && original.images.size == count &&
      boundary.routeOffset + boundary.prefixActions.size == count &&
      boundary.prefixActions == original.prefixActions.extract boundary.routeOffset count &&
      boundary.descriptors.size == boundary.prefixActions.size &&
      boundary.images.size == boundary.prefixActions.size do
    throwError "the selected method boundary changed its original complete route positions"
  if boundary.materializeRoute then
    unless boundary.routeOffset == count && boundary.prefixActions.isEmpty do
      throwError "a transported method boundary omitted an original action position"
  let descriptors := original.descriptors.extract boundary.routeOffset count
  unless (descriptors.zip boundary.descriptors).all (fun (a, b) => sameActionTemplate a b) do
    throwError "the selected method boundary changed an original positioned action descriptor"
  let parameters := original.parameters.filter (fun parameter =>
    boundary.routeOffset <= parameter.slot.actionIndex)
  unless parameters.size == boundary.parameters.size do
    throwError "the selected method boundary omitted an original declaration parameter position"
  let sameContext := fun (left right : CategoryContext) =>
    left.expression.syntacticEq right.expression && left.bundle == right.bundle
  for (original, actual) in parameters.zip boundary.parameters do
    let sameRole := match original.interface.role, actual.interface.role with
      | .value, .value => true
      | .object left, .object right => sameContext left right
      | .map left a b, .map right c d => sameContext left right && a == c && b == d
      | _, _ => false
    unless actual.slot.actionIndex + boundary.routeOffset == original.slot.actionIndex &&
        actual.interface.actionIndex + boundary.routeOffset == original.interface.actionIndex &&
        actual.slot.declarationIndex == original.slot.declarationIndex &&
        actual.slot.dataIndex == original.slot.dataIndex &&
        actual.interface.dataIndex == original.interface.dataIndex &&
        actual.slot.formal == original.slot.formal &&
        actual.slot.expectedType == original.slot.expectedType &&
        actual.interface.formal == original.interface.formal &&
        actual.interface.expectedType == original.interface.expectedType && sameRole &&
        sameActionTemplate actual.template original.template do
      throwError "the selected method boundary replaced an original positioned parameter supplier"

/-- Closing this pure schema may not reread a parameter or replace a captured
declaration occurrence. A missing schema at another boundary is not consulted. -/
def routedInvocationResultPlan (selected : SelectedRoutedInvocation)
    (boundary : SelectedRoutedBoundary) : TermElabM RoutedResultPlan.Plan := do
  checkRoutedBoundaryPositions selected boundary
  let plan ← RoutedResultPlan.select selected.method selected.application
    boundary.receiver.value boundary.context selected.context boundary.prefixActions
    (boundary.parameters.map (·.interface))
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType plan.formal) (← inferType selected.formal) <&&>
        isDefEq plan.formal selected.formal) do
    throwError "the selected routed boundary changed its complete mathematical result"
  unless plan.parameters.size == boundary.parameters.size do
    throwError "the selected routed schema changed its declaration parameter positions"
  for (parameter, original) in plan.parameters.zip boundary.parameters do
    unless parameter.actionIndex == original.slot.actionIndex &&
        parameter.declarationIndex == original.slot.declarationIndex &&
        parameter.dataIndex == original.slot.dataIndex do
      throwError "the selected routed schema replaced a declared parameter position"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq parameter.expectedType original.slot.expectedType <&&>
          isDefEq parameter.formal original.slot.formal) do
      throwError "the selected routed schema changed an original complete parameter"
  return plan

def routedParameterOccurrence (boundary : SelectedRoutedBoundary)
    (actionIndex dataIndex : Nat) : TermElabM RoutedParameterOccurrence := do
  let candidates := boundary.parameters.filter fun parameter =>
    parameter.slot.actionIndex == actionIndex && parameter.slot.dataIndex == dataIndex
  let #[parameter] := candidates
    | throwError "the routed result lost its unique positioned parameter occurrence"
  return parameter
/-- One declaration parameter is materialized through its original typed
template. The same helper serves complete requests and lazy known-field reads. -/
def readRoutedParameterWith
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (fallback : Form) (parameter : RoutedParameterOccurrence) :
    TermElabM (Wire × Array Wire) := do
  let template ← mapActionTemplateWires observe parameter.template
  let (data, children) ← renderCapturedActionData template
  let selected ← match actionTemplateExecution template with
    | .wire _ actual => do
      unless actual.fragment == data do
        throwError "the routed parameter observer changed its exact retained occurrence"
      forwardRetainedValue actual parameter.slot.formal
    | _ => do
      let result : IntrinsicResultInterface := .value parameter.slot.expectedType
      let actual : Wire := {
        form := fallback,
        payload := (← combinedRecipePayload parameter.slot.formal data children) }
      -- Preserve the same positioned typed children in the current value
      -- interface after reading them; dependencies alone do not supply roles.
      retainIntrinsicResultAssembly actual result template
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType selected.value) parameter.slot.expectedType <&&>
        isDefEq selected.value parameter.slot.formal) do
    throwError "the routed input changed a complete declared parameter"
  let result : IntrinsicResultInterface := match parameter.interface.role with
    | .object context => .object context
    | .map context .. => .map context
    | .value => .value parameter.slot.expectedType
  let selected ← match result with
    | .value _ => do
      let actual : Wire := {
        form := selected.form,
        payload := (← combinedRecipePayload parameter.slot.formal data children) }
      -- The original typed template remains executable under a lazy reader.
      -- Only an explicitly retained source slot suppresses its child demand.
      retainIntrinsicResultAssembly actual result template
    | _ => pure selected
  checkCapturedResultInterface selected result
  return (selected, children)

/-- Read all original declaration positions through one typed observer. Whole
Wire leaves retain their comparison and callable metadata. Other templates keep
their existing typed children and their declared scalar/dictionary value role. -/
def readRoutedInputsWith
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (boundary : SelectedRoutedBoundary)
    (frameReceiver : Wire → TermElabM Wire := pure) : TermElabM RoutedInputData := do
  let receiver ← observe .object boundary.receiver
  let receiver ← frameReceiver receiver
  let receiver ← forwardRetainedValue receiver boundary.receiver.value
  discard <| framingContext (some boundary.context) receiver.categoryContext
  let mut parameters := #[]
  let mut dependencies := #[receiver]
  for parameter in boundary.parameters do
    let (selected, children) ← readRoutedParameterWith observe receiver.form parameter
    dependencies := dependencies ++ children
    parameters := parameters.push
      (.parameter parameter.slot.actionIndex parameter.slot.dataIndex, selected)
  return { receiver, parameters, dependencies, routeOffset := boundary.routeOffset }

/-- Materialize a chosen transported boundary in forward order and retain that
same chain as its request receipt. These are the actions whose last result is
transmitted; a fused source boundary never evaluates them independently. -/
def readSelectedRoutedInputsWith
    (observe : ActionDataRole → Wire → TermElabM Wire)
    (selected : SelectedRoutedInvocation) (boundary : SelectedRoutedBoundary)
    (frameReceiver : Wire → TermElabM Wire := pure) : TermElabM RoutedInputData := do
  checkRoutedBoundaryPositions selected boundary
  if !boundary.materializeRoute || selected.canonical.prefixActions.isEmpty then
    let inputs ← readRoutedInputsWith observe boundary frameReceiver
    if boundary.routeOffset == 0 then return inputs
    unless boundary.routeOffset <= selected.canonical.prefixActions.size &&
        selected.canonical.prefixActions.size == selected.canonical.descriptors.size &&
        selected.canonical.prefixActions.size == selected.canonical.images.size do
      throwError "the named method boundary lost its original complete prefix positions"
    let routePrefix : RoutedPrefixInput := {
      receiver := selected.canonical.receiver,
      actions := selected.canonical.prefixActions.extract 0 boundary.routeOffset,
      descriptors := selected.canonical.descriptors.extract 0 boundary.routeOffset,
      images := selected.canonical.images.extract 0 boundary.routeOffset }
    return { inputs with «prefix» := some routePrefix }
  let route := selected.canonical.prefixActions
  unless route.size == selected.canonical.descriptors.size &&
      route.size == selected.canonical.images.size do
    throwError "the transported request lost its ordered original action occurrences"
  let mut current ← observe .object selected.canonical.receiver
  let mut sources := #[]
  let mut images := #[]
  let mut dependencies := #[current]
  for ((edge, application), index) in route.zipIdx do
    let some template := selected.canonical.descriptors[index]?
      | throwError "the transported request lost an original action parameter position"
    let some captured := selected.canonical.images[index]?
      | throwError "the transported request lost its complete selected image interface"
    let descriptor ← mapActionTemplateWires observe template
    let (_, target) ← actionOwnerContexts (.edge edge) application current false
    let formal ← Semantic.objOf application current.value
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType captured.value) (← inferType formal) <&&>
          isDefEq captured.value formal) do
      throwError "the transported request changed an original complete route image"
    discard <| framingContext (some target) captured.categoryContext
    let pending ← captureRegisteredObjectAction (.edge edge) application current
      formal captured.form target descriptor
    let actual ← observe .object pending
    let actual ← forwardRetainedValue actual formal
    checkCapturedResultInterface actual (.object target)
    sources := sources.push current
    images := images.push actual
    dependencies := dependencies ++ actionTemplateInputs descriptor ++ #[actual]
    current := actual
  let receiver ← forwardRetainedValue current boundary.receiver.value
  discard <| framingContext (some boundary.context) receiver.categoryContext
  let inputs ← readRoutedInputsWith observe { boundary with receiver } frameReceiver
  -- Receiver framing is itself an accepted public view of this last image.
  -- Preserve exactly that view, which is the packet the method will receive.
  let finalImages := images.set! (images.size - 1) inputs.receiver
  return { inputs with
    routeSources := sources, routeImages := finalImages,
    dependencies := dependencies ++ inputs.dependencies }

/-- One typed field fold serves actual execution and private admission. Only
returned leaves are supplied by the caller; retained fields use original input
projections, and complete records use the shared public assembler. -/
def foldRoutedResultWith (reader : RetainedRecordReader)
    (plan : RoutedResultPlan.Plan) (inputs : RoutedInputData) (fallback : Form)
    (returned : Nat → RoutedResultPlan.Slot → Array Wire → TermElabM Wire)
    (packets : Option (Array DataOwnership.Data) := none) :
    TermElabM (Array Wire) := do
  let state ← registryState
  let mut values : Array Wire := #[]
  for index in [:plan.slots.size] do
    let some slot := plan.slots[index]?
      | throwError "the routed result omitted an independently selected field"
    let result := routedSlotInterface slot
    let form := routedSlotForm state fallback slot
    let selected ← match slot.node with
      | .retained input projection =>
        projectRetainedRecordWith reader (← inputs.read input) projection slot.formal result form
      | .returned => returned index slot values
      | .record codec indices => do
        let mut children := #[]
        for index in indices do
          let some child := values[index]?
            | throwError "a routed record field was requested before its declared inputs"
          children := children.push child
        let packet ← match packets with
          | none => pure none
          | some packets =>
            let some packet := packets[index]?
              | throwError "the routed result lost a complete original record packet"
            pure (some packet)
        assembleRetainedRecordWith codec children slot.formal result form packet
    let selected ← forwardRetainedValue selected slot.formal
    checkCapturedResultInterface selected result
    if let .map context sourceIndex targetIndex := slot.role then
      let some source := values[sourceIndex]?
        | throwError "the routed map lost its preceding source field"
      let some target := values[targetIndex]?
        | throwError "the routed map lost its preceding target field"
      CategoryContext.checkMorphism context slot.formal source.value target.value
      let some (originalSource, originalTarget) ← retainedCallableEndpoints? selected context
        | throwError "the routed map lost its complete retained endpoint occurrences"
      let originalSource ← forwardRetainedValue originalSource source.value
      let originalTarget ← forwardRetainedValue originalTarget target.value
      unless sameCompleteWireContext originalSource source &&
          sameCompleteWireContext originalTarget target do
        throwStratum .noImplementation
          "the routed result map requires its exact declared endpoint occurrences"
    values := values.push selected
  return values
structure RoutedMethodInput where
  inputs : RoutedInputData
  request : Wire
  descriptors : Array ActionDataTemplate

/-- Assemble the complete selected method request from the same positioned
inputs used by its result schema. Every residual action and the final method
functor transmits its full original parameter occurrences. A parameter's owner
cannot disappear merely because its bytes are absent from the receiver. -/
def routedMethodRequest (selected : SelectedRoutedInvocation)
    (boundary : SelectedRoutedBoundary) (inputs : RoutedInputData)
    (objects : ComputationalData.InterfaceObjects := #[]) : TermElabM RoutedMethodInput := do
  checkRoutedBoundaryPositions selected boundary
  unless inputs.routeOffset == boundary.routeOffset do
    throwError "the selected method request changed its original action offset"
  let actions := boundary.prefixActions.push (.functor selected.functor.id, selected.application)
  let mut descriptors : Array DataOwnership.Data := #[]
  let mut descriptorTemplates : Array ActionDataTemplate := #[]
  for ((edge, application), actionIndex) in actions.zipIdx do
    let positions := boundary.parameters.filter (·.slot.actionIndex == actionIndex)
    let mut parameters : Array ActionDataTemplate := #[]
    for (parameter, dataIndex) in positions.zipIdx do
      unless parameter.slot.dataIndex == dataIndex do
        throwError "the complete method request changed its declaration parameter order"
      let actual ← inputs.read (.parameter actionIndex dataIndex)
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual.value) parameter.slot.expectedType <&&>
            isDefEq actual.value parameter.slot.formal) do
        throwError "the complete method request changed an original full parameter"
      let role := match parameter.interface.role with
        | .object _ => ActionDataRole.object
        | .map .. => ActionDataRole.map
        | .value => ActionDataRole.parameter
      parameters := parameters.push (.wire role actual)
    let template := ActionDataTemplate.logical (routedActionDescriptor edge parameters)
    let (descriptor, _) ← renderCapturedActionData template
    let scope ← templateValidationScope template
    unless scope.data == descriptor do
      throwError "the method descriptor changed its exact positioned suppliers"
    if let .error message ← ComputationalData.validateAction
        (← Semantic.asFunctor application) descriptor.json objects (some scope) then
      throwStratum .noImplementation
        m!"the complete selected method action has no supported parameter interface: {message}"
    descriptors := descriptors.push descriptor
    descriptorTemplates := descriptorTemplates.push template
  unless descriptors.size == boundary.prefixActions.size + 1 do
    throwError "the complete method request lost its selected final functor"
  let receiver := inputs.receiver
  discard <| framingContext (some boundary.context) receiver.categoryContext
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType receiver.value) (← inferType boundary.receiver.value) <&&>
        isDefEq receiver.value boundary.receiver.value) do
    throwError "the complete method request replaced its original typed receiver"
  let data ← checkedFragment (DataOwnership.Data.object [
    ("ctor", { json := toJson selected.method.id.raw }),
    ("args", DataOwnership.Data.array descriptors), ("receiver", receiver.fragment)])
  let encoded := Backend.ConstructionInvocation.encode {
    construction := selected.method.id.raw, parameters := descriptors.map (·.json),
    receiver := receiver.json }
  unless data.json == encoded do
    throwError "the complete method changed the existing public invocation framing"
  let dependencies := inputs.dependencies ++ #[receiver] ++ inputs.parameters.map (·.2)
  -- The historical receiver-only form is complete exactly in this checked
  -- subset. The public decoder never guesses it from packet bytes.
  let legacy := boundary.prefixActions.isEmpty && boundary.parameters.isEmpty
  let request : Wire ← if legacy then pure { receiver with
      serviceHandles := dependencies.flatMap (·.serviceHandles) }
    else do
      pure {
        form := receiver.form
        payload := (← combinedRecipePayload receiver.value data dependencies)
        categoryContext := receiver.categoryContext
        serviceHandles := dependencies.flatMap (·.serviceHandles) }
  return { inputs, request, descriptors := descriptorTemplates }
/-- The accepted Core constructor wraps a retained object occurrence. This is
public data assembly; it does not execute an object action or identify carriers. -/
def captureRoutedCoreObject (original : Wire) (base coreContext : CategoryContext) :
    TermElabM Wire := do
  discard <| framingContext (some base) original.categoryContext
  CategoryContext.checkObject base original.value
  let formal ← mkAppM ``CategoryTheory.Core.mk #[original.value]
  CategoryContext.checkObject coreContext formal
  let template : ActionDataTemplate := .ctor "coreObject" #[.wire .object original]
  let (data, dependencies) ← renderCapturedActionData template
  let result : Wire := {
    form := contextualForm (← registryState) coreContext original.form,
    payload := (← combinedRecipePayload formal data dependencies), categoryContext := some coreContext }
  retainIntrinsicAssembly result .object coreContext template

/-- Lift an already accepted full comparison through Mathlib's Core.isoMk.
The complete category dictionary and both explicit Core endpoints are supplied;
no inverse law or new mathematical comparison is established by the kernel. -/
def routedCoreComparison (base : CategoryContext) (comparison : Expr) : TermElabM Expr := do
  let (source, target) ← operationComparisonEnds base comparison
  let source ← mkAppM ``CategoryTheory.Core.mk #[source]
  let target ← mkAppM ``CategoryTheory.Core.mk #[target]
  StructuredResult.checkReconstruction (← mkAppOptM ``CategoryTheory.Core.isoMk
    #[some (← CategoryContext.carrier base), some (← CategoryContext.dictionary base),
      some source, some target, some comparison])

/-- An isomorphism-invariant method consumes the existing complete Core data
interface. Its comparison directions retain the original computational maps
and endpoint occurrences, rather than replacing an Iso by an identity. -/
def captureRoutedMethodArgument (method : MethodEntry) (original : Wire)
    (context : CategoryContext) : TermElabM Wire := do
  match method.shape with
  | .isoInvariant =>
    let #[constructor] := (← registryState).constructors.filter
        (·.semantics == `CasCatalogue.Constructors.core)
      | throwError "the selected method lost the accepted unique Core constructor"
    let coreContext ← CategoryContext.construct context constructor.id
    let mut result ← captureRoutedCoreObject original context coreContext
    if let some comparison := original.objectIso then
      result := { result with objectIso := some (← routedCoreComparison context comparison) }
    if let some presentation := original.endpointPresentation then
      let (forward, backward) ← endpointPresentationMaps original context presentation
      let some (source, target) ← retainedCallableEndpoints? forward context
        | throwError "the Core comparison lost its complete underlying endpoints"
      let coreSource ← captureRoutedCoreObject source context coreContext
      let coreTarget ← captureRoutedCoreObject target context coreContext
      let comparison ← routedCoreComparison context presentation.comparison
      let capture := fun (formal : Expr) (left right coreLeft coreRight first second : Wire) => do
        let template : ActionDataTemplate := .logical (.ctor "coreIso"
          #[.wire .object left, .wire .object right, .wire .map first, .wire .map second])
        let (data, dependencies) ← renderCapturedActionData template
        let output : Wire := {
          form := contextualForm (← registryState) coreContext first.form true,
          payload := (← combinedRecipePayload formal data dependencies),
          categoryContext := some coreContext, morphismFramed := true }
        let output ← retainIntrinsicAssembly output .map coreContext template
          #[{ context, source := left, target := right, callable := first },
            { context, source := right, target := left, callable := second }]
        retainCallableEndpoints output coreLeft coreRight coreContext
      let first ← capture (← mkAppM ``CategoryTheory.Iso.hom #[comparison])
        source target coreSource coreTarget forward backward
      let second ← capture (← mkAppM ``CategoryTheory.Iso.inv #[comparison])
        target source coreTarget coreSource backward forward
      result ← retainEndpointPresentationMaps result coreContext comparison first second
    return result
  | _ => return original

/-- Preserve comparisons through the already selected residual route and method.
The final actual image is the completed invocation's own result occurrence.
Intermediate map/object actions remain ordinary captured registered actions. -/
def retainRoutedResultComparison (trace : Trace) (selected : SelectedRoutedInvocation)
    (boundary : SelectedRoutedBoundary) (receiver result : Wire)
    (descriptors : Array ActionDataTemplate) : TermElabM Wire := do
  discard <| framingContext (some selected.context) result.categoryContext
  CategoryContext.checkObject selected.context result.value
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType result.value) (← inferType selected.expected) <&&>
        isDefEq result.value selected.expected) do
    throwError "the routed comparison changed its independently selected complete result"
  let mut current := receiver
  unless descriptors.size == boundary.prefixActions.size + 1 do
    throwError "the routed comparison lost a positioned action descriptor"
  for ((edge, application), descriptor) in boundary.prefixActions.zip
      (descriptors.extract 0 boundary.prefixActions.size) do
    let capture : CapturedActionEncoder := fun selected actual => do
      unless selected == edge && (← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual) (← inferType application) <&&>
            isDefEq actual application)) do
        throwError "the routed comparison changed its fixed action application"
      return descriptor
    current ← transportImage trace current #[edge] (some #[application]) none (some capture)
  let context ← routedBoundaryContext current
  let argument ← captureRoutedMethodArgument selected.method current context
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType argument.value) (← inferType selected.acceptedInput) <&&>
        isDefEq argument.value selected.acceptedInput) do
    throwError "the routed comparison changed its complete selected method argument"
  let result := { result with objectIso :=
    (← mapObjectComparison selected.application argument.value argument.objectIso) }
  let some descriptor := descriptors.back?
    | throwError "the routed comparison omitted its complete selected method descriptor"
  retainMappedEndpointPresentation (.edge (.functor selected.functor.id))
    selected.application argument result descriptor
/-- Optional intrinsic/schema inspection cannot hide another failure stage.
The required selected-boundary path calls routedInvocationResultPlan directly. -/
def optionalRoutedResultPlan (selected : SelectedRoutedInvocation)
    (boundary : SelectedRoutedBoundary) : TermElabM (Option RoutedResultPlan.Plan) := do
  try
    return some (← routedInvocationResultPlan selected boundary)
  catch error =>
    if !Exception.hasConflictingStrata error &&
        Exception.stratum? error == some .noImplementation then return none else throw error

partial def projectionSourceLiterals : RoutedResultPlan.ProjectionParameterSource → Array Json
  | .literal data => #[data]
  | .record _ fields => fields.flatMap projectionSourceLiterals
  | .retained .. | .intermediate .. => #[]

/-- Projection declarations can contain independently fixed portable literals
which did not occur in the original request bytes. Reserve them before allocating
private future references. This inspection neither admits a row nor demands an
input, and an unsupported unused boundary remains diagnostically inert. -/
def routedReservedProjectionData (selected : SelectedRoutedInvocation) :
    TermElabM (Array Json) := do
  let mut literals := #[]
  for boundary in selected.boundaries do
    if let some plan ← optionalRoutedResultPlan selected boundary then
      for selected in plan.projectionActions do
        if let .ok action := selected.action then
          for parameter in action.parameters do
            literals := literals ++ projectionSourceLiterals parameter.source
      for stage in plan.stages do
        for selected in stage.projectionActions do
          if let .ok action := selected.action then
            for parameter in action.parameters do
              literals := literals ++ projectionSourceLiterals parameter.source
        for completion in stage.completions do
          match completion with
          | .retained source =>
            literals := literals ++ projectionSourceLiterals source
          | .action selected =>
            literals := literals ++ projectionSourceLiterals selected.source
            for step in selected.steps do
              for parameter in step.parameters do
                literals := literals ++ projectionSourceLiterals parameter.source
          | .record .. | .unavailable _ => pure ()
  return literals

/-- Read one exact original input slot without observing unrelated declaration
parameters. The caller subsequently observes only the requested public subtree. -/
def routedOriginalInput (boundary : SelectedRoutedBoundary) (input : RoutedResultPlan.Input) :
    TermElabM Wire := do
  match input with
  | .receiver => return boundary.receiver
  | .parameter actionIndex dataIndex =>
    let parameter ← routedParameterOccurrence boundary actionIndex dataIndex
    return (← readRoutedParameterWith (fun _ original => pure original)
      boundary.receiver.form parameter).1

/-- Decide the whole required field DAG before reading any input. Endpoint
positions are dependencies of a complete map even if its body is retained. -/
def routedKnownSlots (plan : RoutedResultPlan.Plan) : TermElabM (Array Bool) := do
  let mut known : Array Bool := #[]
  for slot in plan.slots do
    let preceding := known
    let earlier := fun (index : Nat) => do
      let some available := preceding[index]?
        | throwError "the routed field schema refers to a nonpreceding dependency"
      return available
    let available ← match slot.node with
      | .retained .. => pure true
      | .returned => pure false
      | .record _ fields => do
        let dependencies ← fields.mapM earlier
        pure (dependencies.all id)
    let available ← match slot.role with
      | .map _ source target => do
        let source ← earlier source
        let target ← earlier target
        pure (available && source && target)
      | _ => pure available
    known := known.push available
  return known

/-- Restrict an already selected structural projection to one declared output
path. No receiver is demanded to discover which original child supplies it. -/
partial def routedProjectionAtPath (projection : ComputationalData.RecordProjectionPlan)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM ComputationalData.RecordProjectionPlan := do
  if path.isEmpty then return projection
  match projection with
  | .input original => return .input (original ++ path)
  | .record codec fields =>
    let some step := path[0]?
      | throwError "a nonempty routed field path lost its first declaration step"
    unless step.codec == codec && step.count == fields.size do
      throwError "the routed projection changed its selected output-record codec"
    let some child := fields[step.index]?
      | throwError "the routed projection selected an absent original record field"
    routedProjectionAtPath child (path.extract 1 path.size)

/-- Select a remaining public path at its full declared formal/result interface.
This helper reads no computational packet or global category association. -/
def routedPublicField (formal : Expr) (result : IntrinsicResultInterface)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM (Expr × IntrinsicResultInterface) := do
  let mut currentFormal := formal
  let mut currentResult := result
  for step in path do
    let (_, fields) ← publicRecordFields currentFormal currentResult
    let selected := fields.filter fun field => sameOperationFieldPath #[field.step] #[step]
    let #[field] := selected
      | throwStratum .invalid "the routed projection is outside its original public field schema"
    currentFormal := field.formal
    currentResult := field.result
  return (currentFormal, currentResult)

/-- Materialize an already known slot. Retained fields keep their own current
presentations; assembling a record retains its typed children and invents no
whole-record isomorphism or constructor-induced comparison action. -/
partial def readRoutedKnownSlotWith (reader : RetainedRecordReader)
    (observe : IntrinsicResultInterface → Wire → TermElabM Wire)
    (boundary : SelectedRoutedBoundary) (plan : RoutedResultPlan.Plan)
    (known : Array Bool) (memo : IO.Ref (Array (Nat × Wire))) (index : Nat) :
    TermElabM Wire := do
  if let some (_, previous) := (← memo.get).find? (·.1 == index) then return previous
  unless known[index]?.getD false do
    throwError "the intrinsic routed reader reached an unknown returned result slot"
  let some slot := plan.slots[index]?
    | throwError "the intrinsic routed reader lost its original field slot"
  let result := routedSlotInterface slot
  let form := routedSlotForm (← registryState) boundary.receiver.form slot
  let actual ← match slot.node with
    | .retained input projection =>
      projectRetainedRecordWith reader (← routedOriginalInput boundary input)
        projection slot.formal result form
    | .returned => throwError "an unknown returned field cannot be read intrinsically"
    | .record codec fields => do
      let children ← fields.mapM (readRoutedKnownSlotWith reader observe boundary plan known memo)
      assembleRetainedRecordWith codec children slot.formal result form
  let actual ← observe result actual
  let actual ← forwardRetainedValue actual slot.formal
  checkCapturedResultInterface actual result
  if let .map context sourceIndex targetIndex := slot.role then
    let source ← readRoutedKnownSlotWith reader observe boundary plan known memo sourceIndex
    let target ← readRoutedKnownSlotWith reader observe boundary plan known memo targetIndex
    let some (originalSource, originalTarget) ← retainedCallableEndpoints? actual context
      | throwError "the intrinsic routed map lost its complete endpoint occurrences"
    let originalSource ← forwardRetainedValue originalSource source.value
    let originalTarget ← forwardRetainedValue originalTarget target.value
    unless sameCompleteWireContext originalSource source &&
        sameCompleteWireContext originalTarget target do
      throwStratum .noImplementation
        "the retained routed map requires its exact declared endpoint occurrences"
  memo.modify (·.push (index, actual))
  return actual

/-- A pending invocation exposes only fields retained from its original
source-boundary inputs. A field produced by an intervening action stays pending
until the selected invocation supplies it; another evaluation of that action
cannot become this fused reply's field occurrence. A longer path through a
whole retained input is composed into its public projection before any demand.

An optional intrinsic boundary with no complete schema yields no shortcut; the
ordinary selected request/result path remains responsible for that boundary.
Internal inconsistencies and mathematical ambiguity are never hidden. -/
def routedKnownFieldWith (reader : RetainedRecordReader)
    (observe : IntrinsicResultInterface → Wire → TermElabM Wire)
    (selected : SelectedRoutedInvocation) (path : ComputationalData.RecordFieldPath) :
    TermElabM (Option Wire) := do
  let boundary := selected.canonical
  let plan ← optionalRoutedResultPlan selected boundary
  let some plan := plan | return none
  let known ← routedKnownSlots plan
  let mut position : Option (Nat × Nat) := none
  for index in [:plan.slots.size] do
    let some slot := plan.slots[index]?
      | throwError "the known-field schema lost a declared output position"
    if recordPathPrefix slot.replyPath path then
      if let some (_, length) := position then
        if length == slot.replyPath.size then
          throwError "the routed result repeats one public field declaration path"
        if length > slot.replyPath.size then continue
      position := some (index, slot.replyPath.size)
  let some (index, length) := position | return none
  let some slot := plan.slots[index]?
    | throwError "the known-field schema lost its selected output position"
  let suffix := path.extract length path.size
  if suffix.isEmpty then
    unless known[index]?.getD false do return none
    let memo ← IO.mkRef (#[] : Array (Nat × Wire))
    return some (← readRoutedKnownSlotWith reader observe boundary plan known memo index)
  let .retained input projection := slot.node | return none
  let (formal, result) ← routedPublicField slot.formal (routedSlotInterface slot) suffix
  let projection ← routedProjectionAtPath projection suffix
  let original ← routedOriginalInput boundary input
  let state ← registryState
  let form := match result with
    | .object context => contextualForm state context original.form
    | .map context => contextualForm state context original.form true
    | .value _ => original.form
  let actual ← projectRetainedRecordWith reader original projection formal result form
  let actual ← observe result actual
  let actual ← forwardRetainedValue actual formal
  checkCapturedResultInterface actual result
  return some actual


/-- A method that is wholly an input projection still owns a complete result
interface. Preserve its lazy original inputs and every typed field, so a later
prescribed lift does not lose its producer plan merely because no leaf ran. -/
def knownRoutedResultWith (reader : RetainedRecordReader)
    (observe : IntrinsicResultInterface → Wire → TermElabM Wire)
    (selected : SelectedRoutedInvocation) :
    TermElabM (Option (Wire × RetainedResultFields)) := do
  let boundary := selected.canonical
  let some plan ← optionalRoutedResultPlan selected boundary | return none
  let known ← routedKnownSlots plan
  unless known[plan.output]?.getD false do return none
  unless known.all id do
    throwError "a wholly retained result contains an unrelated unproduced public field"
  let memo ← IO.mkRef (#[] : Array (Nat × Wire))
  let values ← (Array.range plan.slots.size).mapM
    (readRoutedKnownSlotWith reader observe boundary plan known memo)
  let some output := values[plan.output]?
    | throwError "the known method omitted its complete output occurrence"
  let mut parameters := #[]
  let mut dependencies := #[boundary.receiver]
  for parameter in boundary.parameters do
    let position := RoutedResultPlan.Input.parameter
      parameter.slot.actionIndex parameter.slot.dataIndex
    let original ← routedOriginalInput boundary position
    parameters := parameters.push (position, original)
    dependencies := dependencies.push original
  let inputs : RoutedInputData := { receiver := boundary.receiver, parameters, dependencies }
  let intermediates ← IO.mkRef ({} : IntermediateResultState)
  return some (output, {
    plan, values, inputs := some inputs, intermediates := some intermediates })

/-- A prospective action key has the same selected inputs as an execution
receipt, but is not a receipt and never enters `Harness.actions`. -/
structure ProspectiveActionKey where
  operation : String
  action : Expr
  input : Wire
  parameters : Array Json
  parameterOwnership : DataOwnership.Table
  dependencies : Array Wire
  images : Array Wire

def sameProspectiveAction (left right : ProspectiveActionKey) : Bool :=
  left.operation == right.operation && left.action == right.action &&
    sameCompleteWireContext left.input right.input && left.parameters == right.parameters &&
    left.parameterOwnership == right.parameterOwnership &&
    sameProductComponents left.dependencies right.dependencies &&
    sameProductComponents left.images right.images

/-- Private prospective views keep the exact input telescope and independent
result ports. They contain no execution receipt or actual universal result. -/
structure ProspectiveInvocationData where
  result : Wire
  recordFields : Option RetainedResultFields := none
  inputs : Array Wire := #[]
  fields : Array Wire := #[]
  diagram : Option DataOwnership.Data := none
  packet : Option DataOwnership.Data := none
  selection : Option SelectedStructuredInvocation := none
  liftStages : Array (LiftStageExecution.Input Wire × LiftStageExecution.Result Wire) := #[]

/-- This private table describes possible output slots only. It owns no backend,
session, service handle, validation receipt, or completed computational result. -/
structure ProspectiveData where
  occurrences : Array (ActionDataRole × Wire × Wire) := #[]
  actions : Array (ProspectiveActionKey × Wire) := #[]
  invocations : Array (Nat × ProspectiveInvocationData) := #[]
  activeInvocations : Array Nat := #[]
  objects : ComputationalData.InterfaceObjects := #[]
  reserved : Array Json := #[]
  nextReference : Nat := 0

/-- Equality here reserves an identifier; it never selects a child or interprets
a data constructor. Actual result references cannot collide with private ones. -/
partial def containsProspectiveJson (needle : Json) (data : Json) : Bool :=
  needle == data || match data with
    | .arr values => values.any (containsProspectiveJson needle)
    | .obj fields => fields.any fun _ value => containsProspectiveJson needle value
    | _ => false

mutual

partial def prospectiveReservedTemplate (template : ActionDataTemplate) : Array Json :=
  match template with
  | .literal data => #[data.json]
  | .wire _ wire => prospectiveReservedWire wire
  | .pointCallable _ _ _ wire => prospectiveReservedWire wire
  | .inventoryMap _ source target original =>
      #[original, source, target].flatMap prospectiveReservedWire
  | .retained child | .logical child | .project _ child => prospectiveReservedTemplate child
  | .object fields => fields.flatMap (fun (_, child) => prospectiveReservedTemplate child)
  | .ctor _ children | .array children => children.flatMap prospectiveReservedTemplate

/-- Reserve bytes from complete producer-owned context, including fields which
a projection may later expose. This traversal observes and dispatches nothing. -/
partial def prospectiveReservedWire (wire : Wire) : Array Json :=
  #[wire.json] ++
    (wire.liftExecution.toArray.flatMap fun execution =>
      execution.actions ++ execution.parameters.map Json.arr ++ execution.sources ++ execution.bases ++
        execution.outputs.flatMap id ++ execution.sourceImages ++ execution.comparisonImages) ++
    wire.productComponents.flatMap prospectiveReservedWire ++
    wire.proofSources.toArray.flatMap (fun source => prospectiveReservedWire (retainedSnapshotWire source)) ++
    (wire.morphismFraming.toArray.flatMap fun frame =>
      (#[frame.input, frame.source, frame.target] ++
        frame.comparisons.toArray.flatMap (fun (source, target) => source.toArray ++ target.toArray)).flatMap
          prospectiveReservedWire) ++
    (wire.actionRecipe.toArray.flatMap fun recipe =>
      prospectiveReservedWire recipe.original ++ prospectiveReservedTemplate recipe.descriptor ++
        recipe.endpoints.toArray.flatMap (fun (a, b) =>
          prospectiveReservedWire a ++ prospectiveReservedWire b) ++
        recipe.imageEndpoints.toArray.flatMap (fun (a, b) =>
          prospectiveReservedWire a ++ prospectiveReservedWire b)) ++
    (wire.intrinsicAssembly.toArray.flatMap fun assembly =>
      prospectiveReservedTemplate assembly.template ++
        assembly.maps.flatMap (fun fields =>
          #[fields.source, fields.target, fields.callable].flatMap prospectiveReservedWire) ++
        assembly.equalObjects.flatMap (fun (a, b) =>
          prospectiveReservedWire a ++ prospectiveReservedWire b)) ++
    (wire.capturedInvocation.toArray.flatMap fun captured =>
      prospectiveReservedInvocation captured.interface) ++
    (wire.callableEndpoints.toArray.flatMap fun endpoints =>
      prospectiveReservedWire endpoints.source ++ prospectiveReservedWire endpoints.target) ++
    (wire.pointOrigin.toArray.flatMap fun origin =>
      prospectiveReservedWire origin.source ++ prospectiveReservedWire origin.target ++
        (match origin.recipe with
          | .element owner inputs => (#[owner] ++ inputs).flatMap prospectiveReservedWire
          | .product _ _ first second _ _ => #[first, second].flatMap prospectiveReservedWire
          | .alias original => prospectiveReservedWire original)) ++
    (wire.endpointPresentation.toArray.flatMap fun presentation =>
      #[presentation.forward, presentation.backward] ++
        presentation.maps.toArray.flatMap (fun (a, b) =>
          prospectiveReservedWire a ++ prospectiveReservedWire b) ++
        presentation.namedRefinement.toArray.flatMap (fun origin =>
          prospectiveReservedWire origin.source ++
            (origin.templates ++ origin.descriptors).flatMap prospectiveReservedTemplate)) ++
    (wire.pointDataInterface.toArray.flatMap fun point =>
      #[point.domainData.json, point.targetData.json])

partial def prospectiveReservedInvocation (selected : CapturedInvocationInterface) : Array Json :=
  match selected with
  | .intrinsic selected => #[selected.fragment.json] ++
      prospectiveReservedTemplate selected.template ++
      selected.maps.flatMap (fun fields =>
        #[fields.source, fields.target, fields.callable].flatMap prospectiveReservedWire) ++
      selected.equalObjects.flatMap (fun (a, b) =>
        prospectiveReservedWire a ++ prospectiveReservedWire b)
  | .directLift selected => #[selected.fragment.json] ++
      selected.operands.flatMap (fun operand => prospectiveReservedWire operand.wire)
  | .liftField selected => #[selected.fragment.json] ++ prospectiveReservedWire selected.parent
  | .liftFactor selected => #[selected.fragment.json] ++
      selected.operands.flatMap (fun operand => prospectiveReservedWire operand.wire)
  | .routed selected => #[selected.fragment.json] ++
      (#[selected.original] ++ selected.boundaries.map (·.receiver)).flatMap
        prospectiveReservedWire ++
      prospectiveReservedTemplate selected.descriptor ++
      (selected.boundaries.flatMap (·.descriptors)).flatMap
        prospectiveReservedTemplate ++
      (selected.boundaries.flatMap (·.parameters)).flatMap
        (fun parameter => prospectiveReservedTemplate parameter.template)
  | .structured selected => #[selected.fragment.json] ++
      selected.operands.flatMap (fun operand => prospectiveReservedWire operand.wire) ++
      (selected.sourceInputs ++ selected.imageInputs).flatMap (fun input =>
        input.unchangedGraph.toArray.map (·.json))
  | .prescribed selected => #[selected.fragment.json] ++
      (#[selected.original, selected.base] ++ selected.sources ++ selected.images).flatMap
        prospectiveReservedWire ++
      selected.parameters.flatMap (fun fields => fields.flatMap prospectiveReservedTemplate) ++
      selected.actions.flatMap prospectiveReservedTemplate
  | .recordProjection selected => #[selected.fragment.json] ++ prospectiveReservedWire selected.parent ++
      selected.endpoints.toArray.flatMap (fun (source, target) =>
        prospectiveReservedWire source ++ prospectiveReservedWire target)
  | .projection selected => #[selected.fragment.json] ++ prospectiveReservedWire selected.parent ++
      selected.endpoints.toArray.flatMap (fun (source, target) =>
        prospectiveReservedWire source ++ prospectiveReservedWire target) ++
      selected.legData.toArray.map (·.json)
  | .callable selected => #[selected.fragment.json] ++
      prospectiveReservedTemplate selected.descriptor ++
      selected.parameters.flatMap prospectiveReservedTemplate ++
      selected.declarationParameters.flatMap (fun parameter =>
        parameter.templates.flatMap prospectiveReservedTemplate) ++
      #[selected.source, selected.target, selected.argument].flatMap prospectiveReservedWire ++
      selected.operationRequest.toArray.flatMap (fun request =>
        #[request.argumentData.json, request.targetData] ++
        #[request.original, request.owner, request.argument, request.argumentDomain,
          request.domainWire, request.sourceWire, request.targetWire, request.input].flatMap prospectiveReservedWire ++
        prospectiveReservedTemplate request.argumentTemplate ++
        request.argumentDependencies.flatMap prospectiveReservedWire ++
        request.parameterOccurrences.flatMap (fun parameter =>
          parameter.data.map (·.json) ++ parameter.templates.flatMap prospectiveReservedTemplate ++
            parameter.dependencies.flatMap prospectiveReservedWire))

end

def ProspectiveData.containsFuture (state : ProspectiveData) (data : Json) : Bool :=
  state.objects.any fun (reference, _) => containsProspectiveJson reference data

/-- All callbacks below are metadata readers or checked intrinsic assemblers.
The live harness is read only; the inspection harness has no executable ports. -/
structure ProspectiveReader where
  live : Harness
  inspect : Harness
  trace : Trace
  state : IO.Ref ProspectiveData
  objectTemplate : ActionRecipe → Wire → DataOwnership.Data → Array Wire → TermElabM Wire
  invocation : ActionOwner → DataOwnership.Data → Bool →
    TermElabM (String × Array DataOwnership.Data)
  endpoints : Wire → CategoryContext → TermElabM (Wire × Wire)

/-- One unique future datum per exact selected action input. A whole-map future
keeps its independently fixed image endpoints, including their actual owners. -/
def prospectiveActionValue (reader : ProspectiveReader) (key : ProspectiveActionKey)
    (template : Wire) (context : CategoryContext) (morphism : Bool) : TermElabM Wire := do
  if let some (_, previous) := (← reader.state.get).actions.find?
      (fun (selected, _) => sameProspectiveAction selected key) then
    return ← forwardRetainedValue previous template.value
  let state ← reader.state.get
  let mut index := state.nextReference
  while state.reserved.any (containsProspectiveJson (Backend.resultRef index)) do
    index := index + 1
  let reference := Backend.resultRef index
  reader.state.modify fun state => { state with
    nextReference := index + 1, objects := state.objects.push (reference, template.value) }
  let data ← if morphism then do
      let #[source, target] := key.images
        | throwError "the prospective map lost its complete image endpoints"
      scopedNode "typedMap" #[source.fragment, target.fragment, { json := reference }]
    else pure ({ json := reference } : DataOwnership.Data)
  let mut future : Wire := { template with
    payload := (← recipePayload template.value data)
    objectObserved := false, callableObserved := false, serviceHandles := #[]
    pointDataInterface := none, pointOrigin := none, liftExecution := none, morphismFraming := none
    actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none, capturedInvocation := none
    morphismFramed := morphism, productComponents := #[], proofSources := []
    constructionInputs := none, constructionInputOwnership := #[] }
  if morphism then
    let #[source, target] := key.images
      | throwError "the prospective map lost its complete image endpoints"
    future ← retainCallableEndpoints future source target context
  reader.state.modify fun state => { state with actions := state.actions.push (key, future) }
  return future

/-- Allocate only a typed private future datum. The reference has no supplier
and never becomes an actual payload, service operand, or execution receipt. -/
def prospectiveDatum (reader : ProspectiveReader) (formal : Expr) :
    TermElabM DataOwnership.Data := do
  let state ← reader.state.get
  let mut index := state.nextReference
  while state.reserved.any (containsProspectiveJson (Backend.resultRef index)) do
    index := index + 1
  let reference := Backend.resultRef index
  reader.state.modify fun state => { state with
    nextReference := index + 1, objects := state.objects.push (reference, formal) }
  return { json := reference }

/-- Preserve the complete fixed interface around an unknown output. This only
constructs a private recipe and never asserts that a point or map was computed. -/
def prospectiveResultWire (template : Wire) (data : DataOwnership.Data)
    (result : IntrinsicResultInterface) (endpoints : Option (Wire × Wire) := none) : TermElabM Wire := do
  let wire : Wire := { template with
    payload := (← recipePayload template.value data), categoryContext := result.context?,
    objectObserved := false, callableObserved := false, serviceHandles := #[],
    pointDataInterface := none, pointOrigin := none, liftExecution := none,
    morphismFraming := none, actionRecipe := none, intrinsicAssembly := none,
    callableEndpoints := none, morphismFramed := endpoints.isSome,
    productComponents := #[], proofSources := [],
    constructionInputs := none, constructionInputOwnership := #[] }
  match result, endpoints with
  | .map context, some (source, target) => retainCallableEndpoints wire source target context
  | .map _, none => throwError "a prospective map result lost its declared complete endpoint interface"
  | .object _, none => pure wire
  | .value _, none => retainIntrinsicResultAssembly wire result (.literal data)
  | _, some _ => throwError "a prospective value acquired an unrelated map result interface"

/-- Checked aliases preserve a private future's exact whole-result identity.
This reference is meaningful only in the current prospective table. -/
def forwardProspectiveValue (reader : ProspectiveReader) (source : Wire) (formal : Expr) :
    TermElabM Wire := do
  let actual ← forwardRetainedValue source formal
  if (← reader.state.get).containsFuture source.json then
    if let some captured := source.capturedInvocation then
      return { actual with capturedInvocation := some {
        captured with interface := captured.interface.reanchor formal } }
  return actual

/-- Recover a private whole-construction view by its exact retained invocation
identity. A field or another equal object cannot be substituted for that view. -/
partial def prospectiveConstructionView (reader : ProspectiveReader) (parent : Wire) :
    TermElabM (Option ProspectiveInvocationData) := do
  if let some assembly ← retainedIntrinsicAssembly? parent .object then
    if let .wire .object child := assembly.template then
      let child ← forwardProspectiveValue reader child parent.value
      if sameCompleteWireContext { child with
          intrinsicAssembly := parent.intrinsicAssembly,
          capturedInvocation := parent.capturedInvocation } parent then
        return ← prospectiveConstructionView reader child
  let some captured := parent.capturedInvocation | return none
  let some (_, prospectiveData) := (← reader.state.get).invocations.find? (·.1 == captured.occurrence)
    | return none
  let expected ← forwardProspectiveValue reader prospectiveData.result parent.value
  unless sameCompleteWireContext expected parent do return none
  return some prospectiveData

/-- Receiver framing consumes only the private table's authenticated complete
construction view. Historical metadata on a coincident field is insufficient. -/
def prospectiveApexReceiver (reader : ProspectiveReader) (wire : Wire) : TermElabM Wire := do
  let prospectiveData ← prospectiveConstructionView reader wire
  computationalApexReceiver reader.trace wire (← reader.state.get).objects
    (prospectiveData.bind (·.selection))


/-- A live canonical field table belongs to one authenticated completed parent.
A still-pending request is observed by the caller before consulting its result. -/
def actualRecordFields? (h : Harness) (parent : Wire) :
    TermElabM (Option RetainedResultFields) := do
  let some captured := parent.capturedInvocation | return none
  let some record := (← h.invocations.get).find? (·.captured.occurrence == captured.occurrence)
    | throwStratum .unavailable "the result field's original preparation scope has expired"
  let some actual := record.result | return none
  let actual ← forwardRetainedValue actual parent.value
  if sameCompleteWireContext actual parent then return record.recordFields
  let originalInput ← forwardRetainedValue record.input parent.value
  if sameCompleteWireContext originalInput { parent with capturedInvocation := none } then return none
  throwStratum .unavailable "the result field changed its exact completed parent occurrence"


mutual

/-- The private result table is authoritative only for its exact whole future
view. Its fields never acquire a live service handle, supplier, or receipt. -/
partial def prospectiveRecordFields? (reader : ProspectiveReader) (parent : Wire) :
    TermElabM (Option RetainedResultFields) := do
  let some captured := parent.capturedInvocation | return none
  if let some (_, selected) := (← reader.state.get).invocations.find?
      (·.1 == captured.occurrence) then
    let expected ← forwardProspectiveValue reader selected.result parent.value
    if sameCompleteWireContext expected parent then return selected.recordFields
    let some current ← retainedCapturedInvocation? parent
      | throwStratum .unavailable "the private field table describes a different complete result occurrence"
    discard <| prospectiveInvocationRecord reader parent current
    return none
  if (← reader.live.invocations.get).any (·.captured.occurrence == captured.occurrence) then
    let some fields ← actualRecordFields? reader.live parent | return none
    -- The checked field/input Wires are immutable and may be reused. The
    -- completion cache is a separate private scope: prospective futures must
    -- never be written into the committed live invocation's cache.
    let values ← match fields.intermediates with
      | some cache => pure (← cache.get).values
      | none => pure #[]
    let intermediates ← IO.mkRef ({ values } : IntermediateResultState)
    let fields := { fields with intermediates := some intermediates }
    reader.state.modify fun state => { state with
      invocations := state.invocations.push (captured.occurrence, {
        result := parent, recordFields := some fields }) }
    return some fields
  let some current ← retainedCapturedInvocation? parent
    | throwStratum .unavailable "the field has no current private preparation scope"
  discard <| prospectiveInvocationRecord reader parent current
  return none

/-- Prospective projection consumes the exact private fields and attaches only
selected comparison metadata. It never allocates in the live invocation table. -/
partial def prospectiveRetainedRecordReader (reader : ProspectiveReader)
    (pendingField? : PendingRecordFieldReader := fun _ _ => pure none) :
    TermElabM RetainedRecordReader := do
  let access : RetainedRecordAccess := {
    fields := prospectiveRecordFields? reader, pendingField? := pendingField?
    observe := fun result wire => prospectiveWireWith reader result.role wire
    presentField := fun origin parent step field => do
      let action ← standaloneRecordProjectionActionWith
        (← prospectiveRetainedRecordReader reader pendingField?) parent step
      applyRecordFieldComparison reader.inspect action parent step field none origin }
  return { readField := readRetainedRecordFieldWith access }

partial def prospectiveRecordProjection (reader : ProspectiveReader)
    (selected : SelectedRecordProjection)
    (pendingField? : PendingRecordFieldReader := fun _ _ => pure none) : TermElabM ProspectiveInvocationData := do
  let field ← (← prospectiveRetainedRecordReader reader pendingField?).readField selected.parent selected.path
  let field ← forwardProspectiveValue reader field selected.formal
  checkCapturedResultInterface field selected.result
  return { result := field }


/-- Authenticate one immutable pending occurrence in its live or private
preparation table. The canonical input/interface owns the producer selection;
copied current metadata cannot supply another body with the same occurrence ID. -/
partial def prospectiveInvocationRecord (reader : ProspectiveReader) (wire : Wire)
    (captured : CapturedInvocation) : TermElabM InvocationExecution := do
  let live := (← reader.live.invocations.get).filter
    (·.captured.occurrence == captured.occurrence)
  let staged := (← reader.inspect.invocations.get).filter
    (·.captured.occurrence == captured.occurrence)
  let #[record] := live ++ staged
    | throwStratum .unavailable "the prospective invocation lost its unique original preparation scope"
  let original ← forwardRetainedValue record.input wire.value
  unless sameCompleteWireContext original { wire with capturedInvocation := none } do
    throwStratum .unavailable "prospective admission changed an original typed invocation occurrence"
  return record

/-- A complete method request and all its private parameter outputs live in one
reader scope. Only the receiver position uses the selected apex framing policy. -/
partial def prospectiveRoutedMethodInputWith (reader : ProspectiveReader)
    (selected : SelectedRoutedInvocation) (boundary : SelectedRoutedBoundary) :
    TermElabM RoutedMethodInput := do
  let inputs ← readSelectedRoutedInputsWith (prospectiveWireWith reader) selected boundary
    (prospectiveApexReceiver reader)
  routedMethodRequest selected boundary inputs (← reader.state.get).objects

/-- Preserve the exact chosen private request; the result fold consumes these
same positioned inputs and descriptors, with no second boundary lookup. -/
partial def prospectiveRoutedSelectionWith (reader : ProspectiveReader)
    (selected : SelectedRoutedInvocation) :
    TermElabM (SelectedRoutedBoundary × Option Registration × RoutedMethodInput) := do
  routedInvocationSelectionDataWith reader.live selected fun boundary => do
    let prepared ← prospectiveRoutedMethodInputWith reader selected boundary
    return (prepared.request, prepared)

/-- Read a declared result role without reclassifying a scalar by its Lean type.
Private maps retain their complete original endpoints and accepted frame. -/
partial def prospectiveRoutedObserve (reader : ProspectiveReader)
    (result : IntrinsicResultInterface) (wire : Wire) : TermElabM Wire := do
  checkCapturedResultInterface wire result
  let actual ← prospectiveWireWith reader result.role wire
  let actual ← forwardProspectiveValue reader actual wire.value
  checkCapturedResultInterface actual result
  return actual

/-- A pending routed field first uses its already completed/private canonical
result, then a purely retained subtree of its immutable selected method. Cycles
are keyed by occurrence identity and no live execution table is mutated. -/
partial def prospectivePendingRoutedFieldWith (reader : ProspectiveReader)
    (wire : Wire) (path : ComputationalData.RecordFieldPath) : TermElabM (Option Wire) := do
  let some captured ← retainedCapturedInvocation? wire | return none
  let record ← prospectiveInvocationRecord reader wire captured
  let .routed selected := record.captured.interface | return none
  let fields ← prospectiveRetainedRecordReader reader (prospectivePendingRoutedFieldWith reader)
  if let some actual := record.result then
    checkDataOwners reader.live actual.fragment
    return some (← fields.readField (← forwardRetainedValue actual wire.value) path)
  if let some (_, actual) := (← reader.state.get).invocations.find?
      (·.1 == captured.occurrence) then
    return some (← fields.readField (← forwardProspectiveValue reader actual.result wire.value) path)
  if (← reader.state.get).activeInvocations.contains captured.occurrence then
    throwStratum .unavailable "prospective routed field inputs form a cycle"
  reader.state.modify fun state => { state with
    activeInvocations := state.activeInvocations.push captured.occurrence }
  try
    routedKnownFieldWith fields (prospectiveRoutedObserve reader) selected path
  finally
    reader.state.modify fun state => { state with
      activeInvocations := state.activeInvocations.filter (· != captured.occurrence) }

/-- A private routed result uses the same complete request boundary and typed
field fold as execution. Only genuinely returned leaves get supplier-free future
references; known fields and all original suppliers remain exact. -/
partial def prospectiveRoutedWith (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedRoutedInvocation) (captured : CapturedInvocation) :
    TermElabM ProspectiveInvocationData := do
  let fields ← prospectiveRetainedRecordReader reader (prospectivePendingRoutedFieldWith reader)
  if let some (intrinsic, recordFields) ←
      knownRoutedResultWith fields (prospectiveRoutedObserve reader) selected then
    let result ← forwardProspectiveValue reader intrinsic wire.value
    return {
      result := { result with capturedInvocation := some captured }
      inputs := recordFields.inputs.toArray.flatMap (fun inputs =>
        inputs.dependencies ++ inputs.parameters.map (·.2)),
      recordFields := some recordFields }
  let (boundary, _, prepared) ← prospectiveRoutedSelectionWith reader selected
  let plan ← routedInvocationResultPlan selected boundary
  let state ← registryState
  let values ← foldRoutedResultWith fields plan prepared.inputs selected.form
    (fun _ slot preceding => do
      let result := routedSlotInterface slot
      let endpoints ← match slot.role with
        | .map _ sourceIndex targetIndex =>
          let some source := preceding[sourceIndex]?
            | throwError "the prospective routed map lost its preceding source field"
          let some target := preceding[targetIndex]?
            | throwError "the prospective routed map lost its preceding target field"
          pure (some (source, target))
        | _ => pure none
      let body ← prospectiveDatum reader slot.formal
      let data ← match endpoints with
        | none => pure body
        | some (source, target) => scopedNode "typedMap" #[source.fragment, target.fragment, body]
      let template : Wire := {
        form := routedSlotForm state selected.form slot,
        payload := (← recipePayload slot.formal data), categoryContext := result.context? }
      prospectiveResultWire template data result endpoints)
  let some output := values[plan.output]?
    | throwError "the prospective routed result lost its selected whole output"
  let output ← retainRoutedResultComparison reader.trace selected boundary prepared.inputs.receiver
    output prepared.descriptors
  let values := values.set! plan.output output
  let intermediates ← IO.mkRef ({} : IntermediateResultState)
  let recordFields ← retainRecordResultComparisonsWith reader.inspect
    (fun current parentSlot fieldSlot => do
      let action ← plan.projectionAction parentSlot fieldSlot
      return some (← materializeRecordProjectionActionWith fields prepared.inputs.read action
        (readCompletedProducedProjectionWith fields current)))
    { plan, values, inputs := some prepared.inputs, intermediates := some intermediates }
  let some output := recordFields.values[plan.output]?
    | throwError "the prospective routed comparison lost its whole output"
  let output ← forwardProspectiveValue reader output wire.value
  let result := { output with capturedInvocation := some captured }
  checkCapturedResultInterface result (.object selected.context)
  return {
    result, inputs := prepared.inputs.dependencies ++ prepared.inputs.parameters.map (·.2),
    recordFields := some recordFields }

/-- The private base supplies its own positioned result fields and exact
request inputs to the same intermediate-completion provider as execution. -/
partial def prospectivePrescribedRouteInputs (reader : ProspectiveReader)
    (selected : SelectedPrescribedInvocation) (base : Wire) :
    TermElabM (Array Wire × Array Wire) := do
  let some fields ← prospectiveRecordFields? reader base
    | throwStratum .noImplementation
        "the selected prescribed base has no retained complete routed result interface"
  let access ← prospectiveRetainedRecordReader reader (prospectivePendingRoutedFieldWith reader)
  prescribedRouteInputsWith access (prospectiveWireWith reader) selected base fields

/-- Prospective prescribed execution exposes all four fields of every selected
stage through the same typed fold as actual execution. Its route provider reads
the selected boundary's private producer positions; no future becomes a receipt. -/
partial def prospectivePrescribedWith (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedPrescribedInvocation) (captured : CapturedInvocation)
    (routeInputs : SelectedPrescribedInvocation → Wire → TermElabM (Array Wire × Array Wire)) :
    TermElabM ProspectiveInvocationData := do
  let original ← prospectiveWireWith reader .object selected.original
  let base ← prospectiveWireWith reader .object selected.base
  let (sources, images) ← routeInputs selected base
  let recordReader ← prospectiveRetainedRecordReader reader (prospectivePendingRoutedFieldWith reader)
  let state ← registryState
  let parameters ← selected.parameters.mapM fun templates => do
    let fields ← templates.mapM (renderActionDataWith (prospectiveWireWith reader))
    return (fields.map (·.1), fields.flatMap (·.2))
  let actionTemplates ← selected.actions.mapM
    (mapActionTemplateWires (prospectiveWireWith reader))
  let actions ← actionTemplates.mapM renderCapturedActionData
  let actionValues ← actionTemplates.zipIdx.mapM fun (template, index) => do
    let some component := selected.plan.components[index]?
      | throwError "the prospective lift action lost its selected stage"
    retainedLiftActionValue component.selection original.form template
  let actions := (actions.zip actionValues).map fun ((data, dependencies), action) =>
    (data, dependencies.push action)
  let run ← executePrescribedRetainedWith recordReader selected.plan original base sources images
    parameters actions
    (fun _ _ => pure none)
    (fun _ input _ field => do
      let body ← prospectiveDatum reader field.formal
      let endpoint := fun (role : LiftStageExecution.EndpointRole Wire) => do
        match role with
        | .retained value => pure value
        | .produced formal =>
            let data ← prospectiveDatum reader formal
            let template : Wire := {
              form := contextualForm state field.context input.original.form,
              payload := (← recipePayload formal data), categoryContext := some field.context }
            prospectiveResultWire template data (.object field.context)
      let endpoints ← field.endpoints.mapM fun (source, target) => do
        pure (← endpoint source, ← endpoint target)
      let data ← match endpoints with
        | none => pure body
        | some (source, target) => scopedNode "typedMap" #[source.fragment, target.fragment, body]
      let result := if field.index == 0 then IntrinsicResultInterface.object field.context
        else .map field.context
      let template : Wire := {
        form := contextualForm state field.context input.original.form (field.index != 0),
        payload := (← recipePayload field.formal data), categoryContext := some field.context }
      prospectiveResultWire template data result endpoints)
  let result ← forwardProspectiveValue reader run.result selected.formal
  let result := { result with form := wire.form }
  let result := { result with capturedInvocation := some captured }
  return {
    result, inputs := run.dependencies, fields := run.stages.flatMap (·.2.outputs)
    packet := some run.packet, liftStages := run.stages }

/-- Inert admission for the same four-field selected plan. Only private future
data is allocated; the live invocation owner receives no completion. -/
partial def prospectiveDirectLift (reader : ProspectiveReader)
    (selected : SelectedDirectLiftInvocation) (captured : CapturedInvocation) :
    TermElabM ProspectiveInvocationData := do
  let operands ← selected.operands.mapM fun operand =>
    prospectiveWireWith reader operand.role operand.wire
  let prepared ← directLiftInputs reader.inspect selected operands
  let result ← LiftStageExecution.fold Wire.fragment prepared.input (fun _ => pure none)
    (fun field => do
      let body ← prospectiveDatum reader field.formal
      let endpoint := fun (role : LiftStageExecution.EndpointRole Wire) => do
        match role with
        | .retained value => pure value
        | .produced formal =>
            let data ← prospectiveDatum reader formal
            let template : Wire := {
              form := contextualForm (← registryState) field.context prepared.form,
              payload := (← recipePayload formal data), categoryContext := some field.context }
            prospectiveResultWire template data (.object field.context)
      let endpoints ← field.endpoints.mapM fun (source, target) => do
        pure (← endpoint source, ← endpoint target)
      let data ← match endpoints with
        | none => pure body
        | some (source, target) => scopedNode "typedMap" #[source.fragment, target.fragment, body]
      let result := if field.index == 0 then IntrinsicResultInterface.object field.context
        else .map field.context
      let template : Wire := {
        form := contextualForm (← registryState) field.context prepared.form (field.index != 0),
        payload := (← recipePayload field.formal data), categoryContext := some field.context }
      prospectiveResultWire template data result endpoints)
    liftStageEndpoints
  let output ← directLiftResult reader.inspect selected prepared result
  let output := { output with
    payload := (← recipePayload selected.formal output.fragment)
    objectObserved := false, capturedInvocation := some captured }
  return {
    result := output, inputs := operands, fields := result.outputs
    packet := some result.step, liftStages := #[(prepared.input, result)] }

/-- Projection follows the exact parent occurrence in the private or live
owner; equal apices and equal packets do not participate in field selection. -/
partial def prospectiveLiftField (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedLiftFieldInvocation) (captured : CapturedInvocation) :
    TermElabM ProspectiveInvocationData := do
  let parent ← prospectiveWireWith reader .object selected.parent
  let parentView ← prospectiveConstructionView reader parent
  let fields ← match parentView with
    | some data => pure data.fields
    | none => do
      let some execution := parent.liftExecution
        | throwError "the prospective lift field lost its complete parent construction"
      captureLiftFields reader.live execution
  let some field := fields[selected.index]?
    | throwError "the prospective lift field lost its fixed output position"
  let field ← forwardProspectiveValue reader field selected.formal
  checkCapturedResultInterface field selected.result
  let result := { field with form := wire.form, capturedInvocation := some captured }
  if selected.index == 0 then
    if let some parentView := parentView then
      return { parentView with result, inputs := #[parent] }
    return {
      result := { result with liftExecution := parent.liftExecution }
      inputs := #[parent], fields }
  return { result, inputs := #[parent] }

/-- A future factor has the declared cone domain and its original selected
apex. Its private packet supplies no factorization or correctness evidence. -/
partial def prospectiveLiftFactor (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedLiftFactorInvocation) (captured : CapturedInvocation) :
    TermElabM ProspectiveInvocationData := do
  let operands ← selected.operands.mapM fun operand =>
    prospectiveWireWith reader operand.role operand.wire
  let some parent := operands[0]?
    | throwError "the prospective factor lost its selected construction"
  let some cone := operands[2]?
    | throwError "the prospective factor lost its source cone"
  let (domain, _) ← reader.endpoints cone selected.context
  let body ← prospectiveDatum reader selected.formal
  let data ← scopedNode "typedMap" #[domain.fragment, parent.fragment, body]
  let template : Wire := {
    form := wire.form,
    payload := (← recipePayload selected.formal data), categoryContext := some selected.context,
    capturedInvocation := some captured }
  let result ← prospectiveResultWire template data (.map selected.context) (some (domain, parent))
  return { result, inputs := operands }

/-- Project producer-declared slots only. Actual data and retained descriptor
leaves stay exact; no trace or JSON tag authorizes erasing their supplier table. -/
partial def prospectiveWireWith (reader : ProspectiveReader) (role : ActionDataRole)
    (wire : Wire) : TermElabM Wire := do
  if role == .retained then return wire
  let valueInterface ← if role == .parameter then retainedValueResultInterface? wire else pure none
  let valueAssembly ← if role == .parameter then retainedIntrinsicValueAssembly? wire else pure none
  let role ← if role == .parameter && valueInterface.isNone then do
      match ← reader.trace.node? wire.value with
      | some (.operationApply ..) | some (.operationPoint ..) |
          some (.operationEquivalence ..) | some (.morphismTransport ..) |
          some (.constructionMap ..) | some (.contextualRoute _ _ _ _ _ true) => pure .map
      | _ => pure .object
    else pure role
  if (wire.actualData || (role == .map && wire.callableObserved) ||
      (role == .object && wire.objectObserved)) &&
      !(role == .map && wire.morphismFraming.isSome) then
    return wire
  if let some (_, _, previous) := (← reader.state.get).occurrences.find?
      (fun (selected, original, _) => selected == role && sameCompleteWireContext original wire) then
    return previous
  let assembly ← match valueAssembly with
    | some assembly => pure (some assembly)
    | none => retainedIntrinsicAssembly? wire role
  let captured ← retainedCapturedInvocation? wire
  let projected ← if let some origin :=
      (if role == .object then wire.endpointPresentation.bind (·.namedRefinement) else none) then
      materializeNamedRefinementWith (prospectiveWireWith reader) reader.trace wire origin
    else if let some captured := captured then
      prospectiveInvocationWith reader wire captured
    else if assembly.isSome then
      observeCurrentIntrinsicAssemblyWith (prospectiveWireWith reader) reader.endpoints
        reader.inspect wire
    else if role == .map && wire.morphismFraming.isSome then do
      let some frame := wire.morphismFraming | unreachable!
      let callableReader : CallablePreparationReader := {
        observe := fun context input => do
          let projected ← prospectiveWireWith reader .map input
          capturePointCallableWith reader.endpoints projected context
        observeData := prospectiveWireWith reader
        objects := do return (← reader.state.get).objects }
      let projected ← observeRetainedMorphismFrameWith callableReader wire frame
      pure projected.wire
    else if let some recipe := wire.actionRecipe then do
      unless recipe.morphism == (role == .map) do
        throwError "the prospective action changed its producer-declared data role"
      let actual ← prospectiveActionWith reader wire recipe
      forwardRetainedValue actual wire.value
    else pure wire
  reader.state.modify fun state => { state with
    occurrences := state.occurrences.push (role, wire, projected) }
  return projected

/-- Inspect one canonical captured occurrence without executing its producer.
The only memo key is its immutable occurrence ID; live tables are read only. -/
partial def prospectiveInvocationWith (reader : ProspectiveReader) (wire : Wire)
    (captured : CapturedInvocation) : TermElabM Wire := do
  let record ← prospectiveInvocationRecord reader wire captured
  if let some actual := record.result then
    checkDataOwners reader.live actual.fragment
    return ← forwardRetainedValue actual wire.value
  if let some (_, prospectiveData) := (← reader.state.get).invocations.find? (·.1 == captured.occurrence) then
    return ← forwardProspectiveValue reader prospectiveData.result wire.value
  if (← reader.state.get).activeInvocations.contains captured.occurrence then
    throwStratum .unavailable "prospective invocation inputs form a cycle"
  reader.state.modify fun state => { state with
    activeInvocations := state.activeInvocations.push captured.occurrence }
  try
    let prospectiveData ← match record.captured.interface with
      | .intrinsic _ => do
          let result ← observeCurrentIntrinsicAssemblyWith (prospectiveWireWith reader) reader.endpoints
            reader.inspect record.input
          pure { result }
      | .callable selected => prospectiveCallableWith reader record.input selected record.captured
      | .structured selected => prospectiveUniversalWith reader record.input selected record.captured
      | .projection selected => prospectiveProjectionWith reader record.input selected
      | .recordProjection selected =>
        prospectiveRecordProjection reader selected (prospectivePendingRoutedFieldWith reader)
      | .routed selected => prospectiveRoutedWith reader record.input selected record.captured
      | .prescribed selected =>
          prospectivePrescribedWith reader record.input selected record.captured
            (prospectivePrescribedRouteInputs reader)
      | .directLift selected => prospectiveDirectLift reader selected record.captured
      | .liftField selected => prospectiveLiftField reader record.input selected record.captured
      | .liftFactor selected => prospectiveLiftFactor reader record.input selected record.captured
    reader.state.modify fun state => { state with
      invocations := state.invocations.push (captured.occurrence, prospectiveData) }
    forwardProspectiveValue reader prospectiveData.result wire.value
  finally
    reader.state.modify fun state => { state with
      activeInvocations := state.activeInvocations.filter (· != captured.occurrence) }

/-- The callable interface is the whole observable Hom, including when its
primitive reply is a point that the normal observer converts into that Hom. -/
partial def prospectiveCallableWith (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedCallableInvocation) (captured : CapturedInvocation) :
    TermElabM ProspectiveInvocationData := do
  let (descriptor, dependencies) ← renderActionDataWith
    (prospectiveWireWith reader) selected.descriptor
  -- Declaration parameters may be retained in both a descriptor and the public
  -- invocation. Every slot keeps its original typed producer and role.
  for parameter in selected.parameters do
    discard <| renderActionDataWith (prospectiveWireWith reader) parameter
  let raw : Wire := { wire with
    payload := (← combinedRecipePayload wire.value descriptor dependencies),
    capturedInvocation := none, categoryContext := some selected.context }
  let endpoint := fun (original : Wire) (origin : CallableEndpointOrigin) (source : Bool) => do
    match origin with
    | .retained => prospectiveWireWith reader .object original
    | .reference => callableEndpointReference raw original.value source (some selected.context)
  let source ← endpoint selected.source selected.sourceOrigin true
  let target ← endpoint selected.target selected.targetOrigin false
  CategoryContext.checkMorphism selected.context selected.formal source.value target.value
  let body ← prospectiveDatum reader selected.formal
  let data ← scopedNode "typedMap" #[source.fragment, target.fragment, body]
  let result ← prospectiveResultWire { wire with capturedInvocation := some captured }
    data (.map selected.context) (some (source, target))
  return { result }

/-- Preserve the selected universal input telescope. Returned fields are the
only new futures; each known argument and endpoint retains its original owner. -/
partial def prospectiveUniversalWith (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedStructuredInvocation) (captured : CapturedInvocation) :
    TermElabM ProspectiveInvocationData := do
  let read := fun (index : Nat) => do
    let some operand := selected.operands[index]?
      | throwError "the prospective construction lost a typed input occurrence"
    unless operand.wire.value == operand.formal && (← withoutModifyingState
        (withTransparency .all <| isDefEq (← inferType operand.wire.value) operand.expectedType)) do
      throwError "the prospective construction changed a declared input type"
    return operand
  let objectInput := fun (wire : Wire) => do
    let actual ← prospectiveWireWith reader .object wire
    prospectiveApexReceiver reader actual
  let project := fun (input : UniversalInputOccurrence) => do
    let operand ← read input.operand
    if operand.role == .object then objectInput operand.wire
    else prospectiveWireWith reader operand.role operand.wire
  let mut sources : Array Wire := #[]
  let mut images : Array Wire := #[]
  for index in [:selected.sourceInputs.size] do
    let some source := selected.sourceInputs[index]?
      | throwError "the prospective construction lost an original argument position"
    let some image := selected.imageInputs[index]?
      | throwError "the prospective construction lost an image argument position"
    let original ← read source.operand
    let sourceWire ← project source
    let imageWire ← if selected.creation.isNone then pure sourceWire else do
      let mut intrinsic : Option Wire := none
      if let (some graph, some (left, right)) := (image.unchangedGraph, image.endpoints) then
        if sameCompleteWireContext original.wire sourceWire then
          let left ← objectInput (← read left).wire
          let right ← objectInput (← read right).wire
          let expected ← read image.operand
          if !(← reader.state.get).containsFuture left.json &&
              !(← reader.state.get).containsFuture right.json &&
              (← ComputationalData.validateEndpointPort expected.formal left.json right.json graph.json).isOk then
            let data ← scopedNode "typedMap" #[left.fragment, right.fragment, graph]
            let mapped : Wire := {
              form := expected.wire.form, payload := (← scopedPayload expected.formal data),
              categoryContext := some selected.targetContext,
              callableObserved := true, morphismFramed := true }
            intrinsic := some (← retainCallableEndpoints mapped left right selected.targetContext)
      match intrinsic with
      | some available => pure available
      | none => project image
    sources := sources.push sourceWire
    images := images.push imageWire
  unless selected.imageInputs.size == images.size do
    throwError "the prospective construction changed its image telescope length"
  let roles ← images.mapM fun image => do
    if (Language.homEnds? (← inferType image.value)).isNone then
      return (image, (none : Option (Wire × Wire)))
    let endpoints ← reader.endpoints image selected.targetContext
    return (image, some endpoints)
  let resolveInput := fun (role : StructuredResult.InputRole) => do
    match role with
    | .argument position => return (← roles[position]?).1
    | .source position =>
      let (_, endpoints) ← roles[position]?
      let (source, _) ← endpoints
      return source
    | .target position =>
      let (_, endpoints) ← roles[position]?
      let (_, target) ← endpoints
      return target
  let external := fun (binder : Nat) => do
    let binding ← selected.plan.binders[binder]?
    let role ← binding.inputRoles[0]?
    let first ← resolveInput role
    if binding.inputRoles.all (fun role =>
        (resolveInput role).any (fun other => other.fragment == first.fragment)) then some first
    else none
  let mut fields : Array Wire := #[]
  for port in selected.plan.ports do
    unless port.index == fields.size do
      throwError "the prospective constructor changed its ordered data-port schema"
    let body ← prospectiveDatum reader port.formalField
    let endpoint := fun (binder : Option Nat) (formal : Expr) (source : Bool) => do
      let retained ← match binder with
        | none => pure none
        | some binder =>
          let some binding := selected.plan.binders[binder]?
            | throwError "the prospective data port lost an endpoint binder"
          match binding.port with
          | some index =>
            let some field := fields[index]?
              | throwError "the selected data plan has an unresolved earlier endpoint port"
            pure (some field)
          | none =>
            let some input := external binder
              | throwStratum .noImplementation
                  "the selected data plan has no agreed computational input for this endpoint binder"
            pure (some input)
      match retained with
      | some retained => forwardProspectiveValue reader retained formal
      | none =>
        -- A complete Hom declares its endpoint projection even when no separate
        -- constructor binder supplies that endpoint's data representation.
        let reference : Wire := {
          form := contextualForm (← registryState) selected.targetContext wire.form true,
          payload := (← recipePayload port.formalField body),
          categoryContext := some selected.targetContext }
        callableEndpointReference reference formal source (some selected.targetContext)
    let result ← constructionResultInterface selected.targetContext port.formalField port.expectedType
    let endpoints ← match result with
      | .map _ =>
        let some (source, target) := Language.homEnds? port.expectedType
          | throwError "the prospective map port lost its independently selected endpoint types"
        pure (some (← endpoint port.domainBinder source true,
          ← endpoint port.codomainBinder target false))
      | _ => pure none
    let data ← match endpoints with
      | none => pure body
      | some (source, target) => scopedNode "typedMap" #[source.fragment, target.fragment, body]
    let form ← match result with
      | .object context => pure (contextualForm (← registryState) context wire.form)
      | .map context => pure (contextualForm (← registryState) context wire.form true)
      | .value _ => pure wire.form
    let template : Wire := {
      form, payload := (← recipePayload port.formalField data), categoryContext := result.context? }
    let field ← prospectiveResultWire template data result endpoints
    fields := fields.push field
  let sourceDiagram ← scopedNode (Codec.label selected.standard) (sources.map (·.fragment))
  let targetDiagram ← scopedNode (Codec.label selected.standard) (images.map (·.fragment))
  let answer ← scopedNode (if selected.plan.colimit then "cocone" else "cone") (fields.map (·.fragment))
  let (diagram, packet) ← match selected.creation with
    | none => pure (targetDiagram, answer)
    | some creation => do
      let packet ← scopedNode "createdCone" #[{ json := toJson creation.id.raw }, sourceDiagram, answer]
      pure (sourceDiagram, packet)
  let data ← scopedNode "constructionApex" #[{ json := toJson selected.resultForm.id }, diagram, packet]
  let result ← prospectiveResultWire { wire with capturedInvocation := some captured }
    data (.object selected.context)
  let inputs := selected.plan.binders.filterMap fun binding => do
    if binding.port.isSome then none else do
      let formal ← binding.formalValue
      let actual ← external binding.index
      return (actual.fragment, formal)
  let result := { result with
    constructionInputs := some (selected.formal, inputs.map fun (data, formal) => (data.json, formal)),
    constructionInputOwnership := inputs.map (·.1.ownership) }
  return {
    result, inputs := sources ++ images, fields, diagram := some diagram,
    packet := some packet, selection := some selected }

/-- Project exactly the same private parent fields and original input positions
that the ordinary structured observer uses after actual completion. -/
partial def prospectiveProjectionWith (reader : ProspectiveReader) (wire : Wire)
    (selected : SelectedStructuredProjection) : TermElabM ProspectiveInvocationData := do
  let parent ← prospectiveWireWith reader .object selected.parent
  let prospectiveData ← prospectiveConstructionView reader parent
  if !selected.inputOccurrences.isEmpty then
    let actual ← selected.inputOccurrences.mapM fun (position, endpoint) => do
      let input ← match prospectiveData with
        | some prospectiveData =>
          let some input := prospectiveData.inputs[position]?
            | throwError "the prospective construction lost an original typed input position"
          pure input
        | none =>
          let some handle := parent.serviceHandles[position]?
            | throwError "the completed construction lost an original typed input handle"
          let some input := (← reader.live.serviceOperands.get)[handle]?
            | throwStratum .unavailable "the constructor input's owning scope has expired"
          pure input
      let input ← match endpoint with
        | none => pure input
        | some source =>
          let (domain, target) ← reader.endpoints input selected.context
          pure (if source then domain else target)
      forwardProspectiveValue reader input selected.formal
    let some first := actual[0]? | unreachable!
    unless actual.all (sameCompleteWireContext first) do
      throwStratum .noImplementation
        "one constructor binder has distinct prospective input presentations without a selected comparison"
    match selected.result with
    | .value _ =>
      let output : Wire := {
        form := first.form,
        payload := (← if first.actualData then scopedPayload selected.formal first.fragment
          else recipePayload selected.formal first.fragment),
        serviceHandles := first.serviceHandles }
      let output ← if first.actualData then retainCompletedResultInterface output selected.result
        else retainIntrinsicResultAssembly output selected.result (.literal output.fragment)
      return { result := output }
    | _ =>
      checkCapturedResultInterface first selected.result
      return { result := first }
  let (diagram, packet, direct) ← match prospectiveData with
    | some prospectiveData =>
      let some diagram := prospectiveData.diagram
        | throwError "the prospective parent has no selected complete diagram interface"
      let some packet := prospectiveData.packet
        | throwError "the prospective parent has no selected complete result packet interface"
      pure (diagram, packet, selected.construction.lift.isNone)
    | none =>
      let .construction result _ := parent.payload
        | throwStratum .noImplementation "the projection has no retained complete parent interface"
      let diagram ← checkedFragment (parent.fragment.project #[.field "args", .index 1])
      let packet ← checkedFragment (parent.fragment.project #[.field "args", .index 2])
      pure (diagram, packet, match result.packet with | .direct _ => true | .created .. => false)
  let data ← match selected.port, selected.leg with
    | some port, none =>
      if direct then checkedFragment (packet.project #[.field "args", .index port.index])
      else scopedNode "constructionField" #[{ json := toJson selected.construction.row.id.raw },
        diagram, packet, { json := toJson port.index }]
    | none, some _ =>
      let some index := selected.legData
        | throwError "the prospective defining leg lost its fixed index"
      scopedNode "constructionLeg" #[{ json := toJson selected.construction.row.id.raw }, diagram, packet, index]
    | _, _ => throwError "the prospective projection lost its unique selected result role"
  let data ← match selected.endpoint with
    | none => pure data
    | some source =>
      placedData
        (Backend.MorphismEndpoint.encode { callable := data.json, source })
        #[(#[.field "args", .index 0], data)]
  let endpoints ← selected.endpoints.mapM fun (source, target) => do
    return (← prospectiveWireWith reader .object source, ← prospectiveWireWith reader .object target)
  let data ← match endpoints with
    | none => pure data
    | some (source, target) =>
      -- The parent port already retains any known typed endpoint fields. A
      -- public complete-map wrapper adds only its independently selected view.
      match Backend.TypedMap.decode data.json with
      | .ok _ => pure data
      | .error _ => scopedNode "typedMap" #[source.fragment, target.fragment, data]
  let result ← prospectiveResultWire { wire with capturedInvocation := none } data selected.result endpoints
  return { result }

/-- Inspect the same selected primitive as execution, stopping at an unknown
output. Known intrinsic fields and exact completed receipts retain actual data;
the output of an unexecuted port is the only supplier-free future slot. -/
partial def prospectiveActionWith (reader : ProspectiveReader) (wire : Wire)
    (recipe : ActionRecipe) : TermElabM Wire := do
  checkActionRecipe wire recipe
  let original ← prospectiveWireWith reader (if recipe.morphism then .map else .object) recipe.original
  let (descriptor, dependencies) ← renderActionDataWith (prospectiveWireWith reader) recipe.descriptor
  let (operation, parameters) ← reader.invocation recipe.owner descriptor recipe.morphism
  let action ← instantiateMVars (← Semantic.asFunctor recipe.application)
  let projected ← if !recipe.morphism then do
      if let .edge edge := recipe.owner then
        if let .proofRefinement _ classifier _ := original.form then
          if edge == .classifierForget classifier then
            return ← prospectiveWireWith reader .object (← proofRefinementBase reader.trace original action)
      let template ← reader.objectTemplate recipe original descriptor dependencies
      if let .edge edge := recipe.owner then
        if let some data ← intrinsicObjectEdgeData? reader.trace edge action original template.value
            descriptor (← reader.state.get).objects then
          let pending := (← reader.state.get).containsFuture data.json
          return { template with
            payload := (← if pending then recipePayload template.value data else scopedPayload template.value data)
            objectObserved := !pending }
      let key : ProspectiveActionKey := {
        operation, action, input := original, parameters := parameters.map (·.json)
        parameterOwnership := (DataOwnership.Data.array parameters).ownership, dependencies, images := #[] }
      if let some actual ← retainedActionResult? reader.live operation action original key.parameters
          dependencies #[] key.parameterOwnership then
        return ← forwardRetainedValue actual template.value
      prospectiveActionValue reader key template recipe.target false
    else do
      let endpoints ← if sameCompleteWireContext original recipe.original then
          match recipe.endpoints with
          | some endpoints => pure endpoints
          | none => throwError "the prospective map lost its original complete endpoint occurrences"
        else reader.endpoints original recipe.source
      let images ← match recipe.imageEndpoints with
        | some (source, target) => pure #[
            ← prospectiveWireWith reader .object source,
            ← prospectiveWireWith reader .object target]
        | none => do
          let mut images := #[]
          for endpoint in #[endpoints.1, endpoints.2] do
            let formal ← Semantic.objOf action endpoint.value
            let endpointRecipe := { recipe with
              morphism := false, original := endpoint, formal, endpoints := none,
              imageEndpoints := none }
            let image ← reader.objectTemplate endpointRecipe endpoint descriptor dependencies
            let endpointRecipe := { endpointRecipe with formal := image.value, fragment := image.fragment }
            let image ← prospectiveActionWith reader image endpointRecipe
            images := images.push image
          pure images
      let key : ProspectiveActionKey := {
        operation, action, input := original, parameters := parameters.map (·.json)
        parameterOwnership := (DataOwnership.Data.array parameters).ownership
        dependencies := dependencies ++ #[endpoints.1, endpoints.2], images }
      if let some actual ← retainedActionResult? reader.live operation action original key.parameters
          key.dependencies images key.parameterOwnership then
        return ← forwardRetainedValue actual wire.value
      prospectiveActionValue reader key wire recipe.target true
  -- Observation fills the captured result's data slots; rebuilding an action
  -- template must not change the caller's already selected public input form.
  return { projected with form := wire.form }

end

/-- Read the callable specialization of the shared producer-owned invocation.
The shared occurrence owner distinguishes current metadata from historical plans. -/
def retainedSelectedCallableInvocation? (wire : Wire) :
    TermElabM (Option SelectedCallableInvocation) := do
  let some captured ← retainedCapturedInvocation? wire | return none
  let .callable selected := captured.interface | return none
  CategoryContext.checkMorphism selected.context wire.value selected.source.value selected.target.value
  return some selected

/-- The existing complete-callable execution boundary, supplied with already
selected typed occurrences. Only the public invocation encoder builds its wire;
the original domain selects the point or whole-callable result interface. -/
def dispatchSelectedCallable (h : Harness) (wire : Wire) (selected : SelectedCallableInvocation)
    (parameters : Array DataOwnership.Data) (arrow : Wire)
    (source target : Wire) (dependencies : Array Wire) : TermElabM Wire := do
  CategoryContext.checkMorphism selected.context wire.value source.value target.value
  CategoryContext.checkMorphism selected.context arrow.value source.value target.value
  discard <| framingContext (some selected.context) arrow.categoryContext
  let arrow ← forwardRetainedValue arrow wire.value
  let pointInterface ← pointDataInterfaceAt source.value target.value
    source.fragment target.fragment
  -- The generalized identity is reassembled at its selected actual domain.
  -- It remains a full typed operand of this request, alongside the exact
  -- materialized callable, so services never rediscover either from old bytes.
  let argument ← selectedCallableIdentity selected.context source
  let argument ← forwardRetainedValue argument selected.argument.value
  let invocation ← match selected.inverse with
    | some inverse =>
      presentationInvocationData parameters inverse source.fragment target.fragment argument.fragment
    | none =>
      pointInvocationData selected.address parameters arrow.fragment source.fragment
        source.fragment target.fragment argument.fragment
  let operands := #[arrow, source, target, argument] ++ dependencies
  let input : Wire := {
    form := source.form
    payload := (← combinedRecipePayload wire.value invocation operands)
    serviceHandles := (← retainServiceOperands h operands) }
  let reply ← sendData h selected.address input (completeRequest := true)
  let answer := reply.data.json
  let checked ← if pointInterface.isSome then
    ComputationalData.validateElementAt target.value target.json
      (← ServiceRequest.pointResultValue wire.value) answer
  else ComputationalData.validateEndpointPort wire.value source.json target.json answer
  if let .error message := checked then
    malformed reply.backend selected.address answer message
  let data ← receiveReplyData h selected.address reply true
  let result : Wire := { wire with
    payload := .computed wire.value data
    categoryContext := some selected.context
    morphismFramed := true, morphismFraming := none
    callableObserved := true, pointDataInterface := pointInterface
    actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none
    capturedInvocation := none }
  retainPointOrMapEndpoints result source target

/-- The actual callable validator owns a private computational endpoint view.
Its slot indices are declaration positions, not equal-value or packet keys. -/
abbrev RoutedMapValidator := RoutedResultPlan.Plan → Nat → Wire →
  Nat → Wire → Nat → Wire → TermElabM (Except String Unit)

/-- A returned leaf is a local candidate at an independently fixed interface.
No candidate is registered as a trusted result until the complete field fold has
been validated. Raw callable packets retain their existing wire representation. -/
def routedReturnedField (plan : RoutedResultPlan.Plan)
    (packets : Array DataOwnership.Data) (fallback : Form)
    (index : Nat) (slot : RoutedResultPlan.Slot) (values : Array Wire) :
    TermElabM Wire := do
  let some packet := packets[index]?
    | throwError "the complete reply lost an independently selected field packet"
  let result := routedSlotInterface slot
  let field : Wire := {
    form := routedSlotForm (← registryState) fallback slot,
    payload := (← scopedPayload slot.formal packet), categoryContext := result.context? }
  match slot.role with
  | .map context sourceIndex targetIndex =>
    let some source := values[sourceIndex]?
      | throwError "a returned callable precedes its declared source field"
    let some target := values[targetIndex]?
      | throwError "a returned callable precedes its declared target field"
    unless sourceIndex < index && targetIndex < index do
      throwError "the selected callable endpoint roles are not preceding result positions"
    CategoryContext.checkMorphism context slot.formal source.value target.value
    -- A complete graph, named map or opaque callable has the same endpoint
    -- occurrence receipt. This receipt does not certify the candidate body.
    retainCallableEndpoints { field with morphismFramed := true } source target context
  | _ => pure field

/-- Construct a private validation view from the whole result's independently
retained actual-side endpoint. Public paths and endpoint positions are fixed by
the selected schema; no packet supplies an object, type, dictionary or proof.
These neutral views carry no executable comparison or captured invocation.
They are used only by the following raw-reply validator. -/
def routedValidationFields (fields : RetainedResultFields) : TermElabM RetainedResultFields := do
  let some output := fields.values[fields.plan.output]?
    | throwError "the result validator lost the whole selected output occurrence"
  let actual ← endpointValidationView output fields.plan.resultContext true
  unless actual.fragment == output.fragment do
    throwError "the actual result interface changed its original packet or suppliers"
  let mut slots : Array RoutedResultPlan.Slot := #[]
  let mut values : Array Wire := #[]
  for index in [:fields.plan.slots.size] do
    let some slot := fields.plan.slots[index]?
      | throwError "the raw result validator lost a selected field position"
    let some original := fields.values[index]?
      | throwError "the raw result validator lost an original field packet"
    let (formal, result) ← routedPublicField actual.value
      (.object fields.plan.resultContext) slot.replyPath
    let role ← match slot.role, result with
      | .object expected, .object context => do
        discard <| framingContext (some expected) (some context)
        pure (RoutedResultPlan.Role.object context)
      | .map expected source target, .map context => do
        discard <| framingContext (some expected) (some context)
        pure (RoutedResultPlan.Role.map context source target)
      | .value, .value _ => pure RoutedResultPlan.Role.value
      | _, _ => throwError "the accepted result comparison changed a public field's declared role"
    let selected : Wire := {
      form := original.form, payload := (← scopedPayload formal original.fragment),
      categoryContext := result.context? }
    let selected ← match role with
      | .map context sourceIndex targetIndex => do
        let some source := values[sourceIndex]?
          | throwError "the raw callable validator lost its preceding source position"
        let some target := values[targetIndex]?
          | throwError "the raw callable validator lost its preceding target position"
        CategoryContext.checkMorphism context formal source.value target.value
        retainCallableEndpoints { selected with morphismFramed := true } source target context
      | _ => pure selected
    checkCapturedResultInterface selected result
    slots := slots.push { slot with formal, expectedType := (← inferType formal), role }
    values := values.push selected
  return {
    plan := { fields.plan with formal := actual.value, slots }, values }

/-- Validate the raw candidate packets before constructing executable result
comparisons. The accepted whole-result endpoint supplies the actual interfaces;
each root remains neutral and only already checked children enter record scopes.
The private validation view never replaces the invocation's mathematical plan. -/
def validateRoutedResultFields (validateMap : RoutedMapValidator)
    (h : Harness) (fields : RetainedResultFields)
    (packets : Array DataOwnership.Data) : TermElabM (Except String Unit) := do
  unless fields.values.size == fields.plan.slots.size &&
      packets.size == fields.plan.slots.size do
    throwError "the complete result changed its independently fixed field count"
  let fields ← routedValidationFields fields
  for index in [:fields.plan.slots.size] do
    let some slot := fields.plan.slots[index]?
      | throwError "the complete result lost a declared slot"
    let some field := fields.values[index]?
      | throwError "the complete result lost a selected field occurrence"
    let some packet := packets[index]?
      | throwError "the complete result lost its original positioned reply data"
    checkDataOwners h field.fragment
    unless field.fragment == packet do
      return .error "the reply replaced a retained field or one of its supplying occurrences"
    checkCapturedResultInterface field (routedSlotInterface slot)
    let validation ← match slot.node with
      | .retained .. => pure (.ok ())
      | .returned =>
        match slot.role with
        | .map _ sourceIndex targetIndex => do
          let some source := fields.values[sourceIndex]?
            | throwError "the returned callable lost its declared source occurrence"
          let some target := fields.values[targetIndex]?
            | throwError "the returned callable lost its declared target occurrence"
          validateMap fields.plan index field sourceIndex source targetIndex target
        | .object context => do
          let actual ← endpointValidationView field context true
          unless actual.fragment == packet do
            throwError "a result comparison changed a candidate object's data or suppliers"
          ComputationalData.validatePort actual.value (← inferType actual.value) packet.json
            (scope := some { data := packet })
        | .value =>
          ComputationalData.validatePort slot.formal slot.expectedType packet.json
            (scope := some { data := packet })
      | .record _ children =>
        ComputationalData.validateRecordFieldsWith slot.formal packet
          (fun step formal data => do
            let some childIndex := children[step.index]?
              | throwError "the record validator requested an undeclared field position"
            unless childIndex < index do
              throwError "the record validator requested a child before its validation"
            let some childSlot := fields.plan.slots[childIndex]?
              | throwError "the record validator lost a declared child slot"
            let some child := fields.values[childIndex]?
              | throwError "the record validator lost an exact validated child"
            let some declaredStep := childSlot.replyPath.back?
              | throwError "a nested result field lost its public declaration path"
            unless step.sameDeclaration declaredStep &&
                childSlot.replyPath.size == slot.replyPath.size + 1 &&
                sameOperationFieldPath slot.replyPath
                  (childSlot.replyPath.extract 0 slot.replyPath.size) do
              throwError "the record validator replaced a selected public child position"
            unless child.fragment == data do
              throwError "the record validator replaced a validated child's exact suppliers"
            unless ← withoutModifyingState (withTransparency .all <|
                isDefEq (← inferType formal) childSlot.expectedType <&&>
                  isDefEq formal childSlot.formal) do
              throwError "the record validator changed a child's full selected interface"
            let role := (routedSlotInterface childSlot).role
            wireValidationScope role child (routedSlotInterface childSlot).context?
              (mapView := .logical))
    if let .error message := validation then return .error message
  return .ok ()

/-- Complete the public method reply locally before the invocation observer
commits a canonical result. All field comparisons use the pure plan's original
parameter origins and the same observed input occurrences as the request. -/
def completeRoutedResultWith (validateMap : RoutedMapValidator)
    (reader : RetainedRecordReader)
    (h : Harness) (trace : Trace) (selected : SelectedRoutedInvocation)
    (boundary : SelectedRoutedBoundary) (materialized : RoutedMethodInput)
    (plan : RoutedResultPlan.Plan) (reply : ComputationalReply) :
    TermElabM (Wire × RetainedResultFields) := do
  let answer ← receiveReplyFragment h selected.method.id.raw reply true
  let packets ← projectRoutedResultShape plan answer
  let values ← foldRoutedResultWith reader plan materialized.inputs selected.form
    (routedReturnedField plan packets selected.form) (some packets)
  let some output := values[plan.output]?
    | throwError "the complete method lost its declared output field"
  let output ← retainRoutedResultComparison trace selected boundary
    materialized.inputs.receiver output materialized.descriptors
  let intermediates ← IO.mkRef ({} : IntermediateResultState)
  let fields : RetainedResultFields := {
    plan, values := values.set! plan.output output,
    inputs := some materialized.inputs, intermediates := some intermediates }
  -- The accepted whole-result comparison fixes all actual public interfaces
  -- without executing field actions. Reject malformed packets before any
  -- descriptor reader can demand another computation using a returned field.
  if let .error message ← validateRoutedResultFields validateMap h fields packets then
    malformed reply.backend selected.method.id.raw reply.data.json message
  let fields ← retainRecordResultComparisonsWith h (fun current parent child => do
    let action ← plan.projectionAction parent child
    return some (← materializeRecordProjectionActionWith reader
      materialized.inputs.read action (readCompletedProducedProjectionWith reader current))) fields
  for ((slot, field), packet) in (plan.slots.zip fields.values).zip packets do
    unless field.fragment == packet do
      throwError "completing a validated result comparison changed an original packet or supplier"
    checkCapturedResultInterface field (routedSlotInterface slot)
  let some output := fields.values[plan.output]?
    | throwError "the checked method result lost its complete output occurrence"
  checkDataOwners h output.fragment
  return (output, fields)

/-- A computational endpoint alias is justified by its original symbolic
input projection, never by equal closed expressions or equal reply bytes. -/
partial def sameRoutedInputProjection
    (first second : ComputationalData.RecordProjectionPlan) : Bool :=
  match first, second with
  | .input left, .input right => sameOperationFieldPath left right
  | .record firstCodec left, .record secondCodec right =>
    firstCodec == secondCodec && left.size == right.size &&
      (left.zip right).all (fun (a, b) => sameRoutedInputProjection a b)
  | _, _ => false

def routedEndpointIdentity (plan : RoutedResultPlan.Plan) (index : Nat) : TermElabM Nat := do
  let some selected := plan.slots[index]?
    | throwError "the computational endpoint lost its declared result position"
  let .retained input projection := selected.node | return index
  for earlier in [:index] do
    let some slot := plan.slots[earlier]?
      | throwError "the computational endpoint lost a preceding schema position"
    let .object context := slot.role | continue
    let .object expected := selected.role
      | throwError "the selected computational endpoint lost its complete object role"
    let .retained original originalProjection := slot.node | continue
    unless original == input && sameRoutedInputProjection originalProjection projection do continue
    discard <| framingContext (some expected) (some context)
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq slot.expectedType selected.expectedType <&&>
          isDefEq slot.formal selected.formal) do
      throwError "a shared symbolic endpoint origin changed its complete typed role"
    return earlier
  return index

/-- All callable representations use one private computational Hom at the exact
declared endpoint occurrences. The requested formal map and accepted comparison
metadata remain unchanged outside that framing check. -/
def validateRoutedMap : RoutedMapValidator := fun plan index field
    sourceIndex source targetIndex target => do
  let some slot := plan.slots[index]?
    | throwError "the returned callable lost its independently fixed result slot"
  let .map context declaredSource declaredTarget := slot.role
    | throwError "a returned non-map field requested a callable validator"
  unless sourceIndex == declaredSource && targetIndex == declaredTarget do
    throwError "the returned callable changed its original endpoint role positions"
  let formal ← validationMapFormal field context true
  let source ← endpointValidationView source context true
  let target ← endpointValidationView target context true
  let scope : ComputationalData.InterfaceScope := { data := field.fragment }
  ComputationalData.validateEndpointSlots formal
    { index := (← routedEndpointIdentity plan sourceIndex),
      formal := source.value, data := source.fragment }
    { index := (← routedEndpointIdentity plan targetIndex),
      formal := target.value, data := target.fragment }
    field.fragment (scope := some scope)

/-- Compile the recorded-node evaluator separately from its recursive callers.
The callbacks are exactly the existing realization operations; the body retains
its original harness, trace, call order, data ownership, and failure checks.
This compilation boundary avoids compiling the complete evaluator and every
observer in one recursive compiler component. -/
def realizeFreshWith
    (elementFragment : Harness → Trace → Expr →
      TermElabM (DataOwnership.Data × Array Wire))
    (realizedParameterData : Harness → Trace → Array Expr →
      TermElabM (Array DataOwnership.Data × Array Wire))
    (realizedEdgeData : Harness → Trace → EdgeRef → Expr →
      TermElabM (DataOwnership.Data × Array Wire))
    (capturedEdgeData : Harness → Trace → EdgeRef → Expr → TermElabM ActionDataTemplate)
    (capturedParameterData : Harness → Trace → Array Expr →
      TermElabM (Array ActionDataTemplate))
    (capturedCallableParameters : Harness → Trace → Array Expr → Array (Nat × Wire) →
      TermElabM (Array SelectedCallableParameter))
    (captureSelectedCallable : Harness → Trace → Wire → String → Expr →
      Array SelectedCallableParameter → ActionDataTemplate → Array ActionDataTemplate →
      Option CategoryContext → Option (CallableEndpointData × CallableEndpointData) →
      Option Bool → TermElabM Wire)
    (captureRoutedInvocation : Harness → Trace → String → Expr → MethodId →
      Array EdgeRef → Expr → Array (RouteComparison × Expr) →
      MethodApplication → Array LiftId → TermElabM Wire)
    (actionMapEndpoint : Harness → Trace → Wire → Option CategoryContext → Expr → Bool →
      TermElabM Wire)
    (realizeObjectObservation : Harness → Trace → Wire → TermElabM Wire)
    (realizeArrowObservation : Harness → Trace → Wire → TermElabM Wire)
    (computationalOperationReceiver : Harness → Trace → String → Wire →
      Array EdgeRef → Wire → TermElabM Wire)
    (extentFragment? : Harness → Trace → Expr →
      TermElabM (Option (DataOwnership.Data × Array Wire)))
    (realizeEndpoint : Harness → Trace → String → Expr →
      (recoverAction : optParam Bool true) → (recoverNamed : optParam Bool true) →
      TermElabM Wire)
    (realizeCallableEndpoint : Harness → Trace → Wire → Expr → Bool →
      (context : optParam (Option CategoryContext) none) → TermElabM Wire)
    (frameMorphismTemplate : Harness → Trace → Expr → Expr → Wire →
      (context : optParam (Option CategoryContext) none) →
      (pointAsMap : optParam Bool false) → TermElabM ActionDataTemplate)
    (captureCompleteCallable : Harness → Trace → Wire → CategoryContext →
      (endpoints : optParam (Option (Wire × Wire)) none) →
      (publicFrame : optParam Bool true) → TermElabM Wire)
    (callableObjectPlan? : Expr → TermElabM (Option DeclaredAdmission.Plan))
    (capturedMapEndpoints : Harness → Trace → Wire → CategoryContext → TermElabM (Wire × Wire))
    (pointAtAdmissionDomain : Harness → Trace → Wire → Expr → Expr → Expr → TermElabM Wire)
    (wholeCallablePoint : Harness → Trace → Wire → Expr → Expr → Expr →
      CategoryContext → DeclaredAdmission.Plan → TermElabM Wire)
    (realizeObjectPresentation : Harness → Trace → ObjectEntry → Array Expr →
      Array DataOwnership.Data → Array Wire → Array ActionDataTemplate → TermElabM (Option Wire))
    (contextualAction : Harness → Trace → Expr → Expr → CategoryContext → CategoryContext →
      Array EdgeRef → Array Expr → Bool → TermElabM Wire)
    (captureMapRoute : Harness → Trace → Wire → Array EdgeRef → Array Expr → TermElabM Wire)
    (captureConstructionMap : Harness → Trace → Expr → DirectConstruction.Action → Wire →
      TermElabM Wire)
    (contextualComposition : Harness → Trace → Expr → CategoryContext →
      Expr → Expr → Expr → Expr → Expr → TermElabM Wire)
    (structuredProjection : Harness → Trace → Expr → Expr → String → Option Nat → TermElabM Wire)
    (captureConstructionLeg : Harness → Trace → Expr → Expr → Expr → TermElabM Wire)
    (retainedLiftExecution : Harness → Trace → Expr → TermElabM (Wire × LiftExecution))
    (composedLiftExecution : Harness → Trace → Expr → Expr → TermElabM Wire)
    (captureDirectLiftInvocation : Harness → Trace → SelectedLift.Plan → Expr → TermElabM Wire)
    (captureLiftField : Harness → Trace → Expr → Expr → Nat → TermElabM Wire)
    (captureLiftFactor : Harness → Trace → Expr → Expr → Expr → Expr → Expr → TermElabM Wire)
    (realize : Harness → Trace → String → Expr → TermElabM Wire)
    (realizeUnobserved : Harness → Trace → String → Expr → TermElabM Wire)
    (realizeFresh : Harness → Trace → String → Expr → TermElabM Wire)
    (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  -- Building a complete public request does not itself demand every action
  -- occurring in a selected parameter. A direct port may implement that fixed
  -- composite. Shared caches still supply every already computed occurrence;
  -- the outer observer and explicit action executors demand their own results.
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let e ← instantiateMVars e
  let some node ← (trace.node? e : IO _)
    | do
      -- Reduction can remove the surface action from a complete selected object.
      -- Recover only its literal original child and already checked full action;
      -- an equal result elsewhere in the cache cannot supply this presentation.
      if h.parameterRecovery.contains e then
        throwStratum .noImplementation m!"the complete selected object action has cyclic data dependencies"
      -- Literal projections select their exact source and action parameters even
      -- when a different projection spelling has no exact trace node. Recurse
      -- through that child before considering genuinely reduced presentations.
      if let some (action, receiver) := FunctorActionData.objectAction? e then
        if let some selected ← FunctorActionData.registeredComposite? state action then
          let h := { h with parameterRecovery := h.parameterRecovery.push e }
          let source ← realizeEndpoint h trace "the literal action's selected source" receiver
          let image ← transportImage trace source (selected.map (·.edge))
            (some (selected.map (·.application)))
            (some fun edge application => do
              let components := selected.filter fun candidate =>
                candidate.edge == edge && candidate.application == application
              let some component := components[0]?
                | throwError "the literal action lost its exact declared parameter presentation"
              unless components.all (fun candidate =>
                  candidate.declarationApplication == component.declarationApplication) do
                throwError "the literal action has distinct retained parameter presentations"
              -- Parameter provenance belongs to the declaration above; the
              -- strict descriptor checker consumes this complete selected functor.
              realizedEdgeData h trace edge application)
            (some fun edge application => do
              let components := selected.filter fun candidate =>
                candidate.edge == edge && candidate.application == application
              let some component := components[0]?
                | throwError "the literal action lost its exact captured parameter presentation"
              unless components.all (fun candidate =>
                  candidate.declarationApplication == component.declarationApplication) do
                throwError "the literal action has distinct captured parameter presentations"
              capturedEdgeData h trace edge application)
          unless ← withTransparency .all <|
              isDefEq (← inferType image.value) (← inferType e) <&&> isDefEq image.value e do
            throwError "the literal action changed the complete selected object"
          return { image with payload := forwardPayload image e image.json }
      if let some selected ← FunctorActionData.retainedParameterAction? trace e then
        let h := { h with parameterRecovery := h.parameterRecovery.push e }
        let source ← realizeEndpoint h trace "the reduced selected object's retained source" selected.receiver
        let image ← transportImage trace source selected.route (some selected.applications)
          (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
        unless ← withTransparency .all <|
            isDefEq (← inferType image.value) (← inferType e) <&&> isDefEq image.value e do
          throwError "the recovered action changed the complete selected object"
        return { image with payload := forwardPayload image e image.json }
      if let some original ← retainedConstructionResult? trace e then
        let actual ← realize { h with parameterRecovery := h.parameterRecovery.push e }
          trace "the original complete selected construction" original
        return { actual with payload := forwardPayload actual e actual.json }
      if (← recordCompleteConstruction trace e) || (← recordCompleteNamedCategory trace e) then
        return ← realizeFresh h trace what e
      if ← recordCompleteNamedObject trace e then
        return ← realizeFresh h trace what e
      if ← recordCompleteUniversalObject trace e then
        let actual ← realizeFresh h trace what e
        return { actual with payload := forwardPayload actual e actual.json }
      throwStratum .noImplementation m!"nothing computes {what}: it is not formed by a \
        catalogue operation the realized reading evaluates (a named object at its parameters, \
        a method of one); the term is {e}"
  match node with
  | .operationEquivalence representative chosen candidates comparisons =>
      checkOperationEquivalence e representative chosen candidates comparisons
      let actual ← realizeUnobserved h trace "the checked operation agreement's selected result" representative
      forwardOperationEquivalent e representative actual
  | .categoryParameter id params =>
      let some entry := state.categories.find? (·.id == id)
        | throwError "the selected category parameter is no longer registered"
      let application ← DirectConstruction.instantiate entry.declaration (← params.mapM exprToSyntax)
      unless ← withTransparency .all <|
          isDefEq (← inferType application.value) (← inferType e) <&&>
            isDefEq application.value e do
        throwError "the selected category parameter changed its complete dictionary"
      let _ ← DirectConstruction.close application
      let (parameters, dependencies) ← realizedParameterData h trace params
      let data ← scopedNode "category" #[{ json := toJson id.raw },
        DataOwnership.Data.array parameters]
      return { form := .diagrams entry, payload := (← combinedRecipePayload e data dependencies) }
  | .functorParameter id params =>
      let some entry := state.functor? id
        | throwError "the selected functor parameter is no longer registered"
      let application ← DirectConstruction.instantiate entry.declaration (← params.mapM exprToSyntax)
      let functor ← Semantic.asFunctor application.value
      unless ← withTransparency .all <|
          isDefEq (← inferType functor) (← inferType e) <&&> isDefEq functor e do
        throwError "the selected functor parameter changed its complete action"
      let _ ← DirectConstruction.close application
      let (parameters, dependencies) ← realizedParameterData h trace params
      let data ← scopedNode "functor" #[{ json := toJson id.raw },
        DataOwnership.Data.array parameters]
      let category ← Semantic.namedCategoryFor state entry.target
      return { form := .diagrams category, payload := (← combinedRecipePayload e data dependencies) }
  | .coreObject context object =>
      CategoryContext.checkObject context object
      let #[constructor] := state.constructors.filter
          (·.semantics == `CasCatalogue.Constructors.core)
        | throwError "the accepted core context is absent or ambiguous"
      let coreContext ← CategoryContext.construct context constructor.id
      let value ← mkAppM ``CategoryTheory.Core.mk #[object]
      unless ← withTransparency .all <| isDefEq value e do
        throwError "the core object changed its complete underlying source"
      let original ← realizeEndpoint h trace "the complete original core object" object
      let template : ActionDataTemplate := .ctor "coreObject" #[.wire .object original]
      let (data, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := contextualForm state coreContext original.form
        payload := (← combinedRecipePayload e data dependencies)
        categoryContext := some coreContext }
      retainIntrinsicAssembly result .object coreContext template
  | .coreIso context source target forward backward =>
      CategoryContext.checkMorphism context forward source target
      CategoryContext.checkMorphism context backward target source
      let #[constructor] := state.constructors.filter
          (·.semantics == `CasCatalogue.Constructors.core)
        | throwError "the accepted core context is absent or ambiguous"
      let coreContext ← CategoryContext.construct context constructor.id
      CategoryContext.checkMorphism coreContext e
        (← mkAppM ``CategoryTheory.Core.mk #[source]) (← mkAppM ``CategoryTheory.Core.mk #[target])
      let comparison ← mkAppM ``CategoryTheory.CoreHom.iso #[e]
      unless ← withTransparency .all <| isDefEq
          (← mkAppM ``CategoryTheory.Iso.hom #[comparison]) forward <&&>
          isDefEq (← mkAppM ``CategoryTheory.Iso.inv #[comparison]) backward do
        throwError "the complete core map changed an accepted comparison direction"
      let sourceWire ← realizeEndpoint h trace "the core comparison source" source
      let targetWire ← realizeEndpoint h trace "the core comparison target" target
      let forwardWire ← realize h trace "the core comparison forward map" forward
      let backwardWire ← realize h trace "the core comparison backward map" backward
      let data ← scopedNode "coreIso" #[sourceWire.fragment, targetWire.fragment,
        forwardWire.fragment, backwardWire.fragment]
      return {
        form := contextualForm state coreContext sourceWire.form true
        payload := (← combinedRecipePayload e data #[sourceWire, targetWire, forwardWire, backwardWire])
        categoryContext := some coreContext }
  | .contextualRoute source target route applications receiver morphism =>
      contextualAction h trace e receiver source target route applications morphism
  | .contextualComposition context first second source middle target =>
      contextualComposition h trace e context first second source middle target
  | .contextualIdentity context object =>
      let original ← realizeEndpoint h trace "the contextual identity's complete object" object
      captureIntrinsicIdentity e (contextualForm state context original.form true) context original
  | .contextualArrow context hom source target =>
      CategoryContext.checkMorphism context hom source target
      let #[constructor] := state.constructors.filter
          (·.semantics == `CasCatalogue.Constructors.arrow)
        | throwError "the accepted Arrow context is absent or ambiguous"
      let arrowContext ← CategoryContext.construct context constructor.id
      let expected ← mkAppOptM ``CategoryTheory.Arrow.mk
        #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
          some source, some target, some hom]
      unless ← withTransparency .all <| isDefEq e expected do
        throwError "the contextual Arrow changed its complete defining morphism"
      let homWire ← realize h trace "the contextual Arrow defining map" hom
      let homWire ← captureCompleteCallable h trace homWire context none false
      let some (sourceWire, targetWire) ← retainedCallableEndpoints? homWire context
        | throwError "the contextual Arrow lost its retained complete map endpoints"
      let template : ActionDataTemplate := .ctor "arrow"
        #[.wire .object sourceWire, .wire .object targetWire, .wire .map homWire]
      let (data, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := contextualForm state arrowContext sourceWire.form
        payload := (← combinedRecipePayload e data dependencies)
        categoryContext := some arrowContext }
      retainIntrinsicAssembly result .object arrowContext template
        #[{ context, source := sourceWire, target := targetWire, callable := homWire }]
  | .construction id params receiver =>
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the selected construction is no longer registered"
      let selected ← DirectConstruction.select entry (← params.mapM exprToSyntax) receiver
      let expected ← DirectConstruction.obj selected receiver
      unless ← withTransparency .all <| isDefEq expected e do
        throwError "the direct construction changed its complete selected formal result"
      let original ← realizeUnobserved h trace
        "the construction's complete selected source" receiver
      let descriptor := ActionDataTemplate.ctor id.raw
        (← capturedParameterData h trace selected.parameters)
      let some resultForm := state.constructionForm? entry.id.raw
        | throwError "the construction lost its registered complete result form"
      captureRegisteredObjectAction (.construction id selected.parameters) selected.functor
        original e resultForm selected.target descriptor
  | .constructionMap id params source target morphism =>
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the selected construction map is no longer registered"
      let selected ← DirectConstruction.select entry (← params.mapM exprToSyntax) source
      let expected ← DirectConstruction.map selected source target morphism
      unless ← withTransparency .all <| isDefEq expected e do
        throwError "the construction map changed its exact selected action or endpoints"
      let original ← realizeUnobserved h trace "the complete selected construction source map" morphism
      captureConstructionMap h trace e selected original
  | .selectedLift id params source inclusion monic =>
      let some entry := state.lifts.find? (·.id == id)
        | throwError "the explicitly selected lift is no longer registered"
      let plan ← SelectedLift.select entry (← params.mapM exprToSyntax) source inclusion monic
      unless ← withTransparency .all <| isDefEq plan.ports[0]! e do
        throwError "the explicit lift changed its complete formal object output"
      captureDirectLiftInvocation h trace plan e
  | .liftProjection receiver field =>
      if field == "composed" then return ← composedLiftExecution h trace e receiver
      let some index := LiftField.all.findIdx? (·.label == field)
        | throwError "the selected lift projection is not a public field"
      captureLiftField h trace e receiver index
  | .structuredProjection receiver field index =>
      structuredProjection h trace e receiver field index
  | .callableEndpoint context receiver source =>
      let parent ← realizeUnobserved h trace "the selected endpoint's complete callable producer" receiver
      let (left, right) ← capturedMapEndpoints h trace parent context
      let endpoint := if source then left else right
      return ← forwardRetainedValue endpoint e
  | .cartesian id params baseMorphism receiver field =>
      let some entry := state.functor? id
        | throwError "the selected family reindexing is no longer registered"
      let original ← realizeUnobserved h trace "the cartesian map's complete original receiver" receiver
      let sourceContext ← match original.categoryContext with
        | some context => pure context
        | none => CategoryContext.ofNamed (← Semantic.namedCategoryFor state entry.source) receiver
      CategoryContext.checkObject sourceContext receiver
      let plan ← ReindexAction.select entry (← params.mapM exprToSyntax) baseMorphism sourceContext
      let (hom, source, target) ← ReindexAction.cartesian plan receiver
      let expected := if field == "hom" then hom else if field == "source" then source else target
      unless #["hom", "source", "target"].contains field &&
          (← withTransparency .all <| isDefEq expected e) do
        throwError "the selected cartesian field changed its original complete type"
      let base ← realizeUnobserved h trace "the cartesian map's original complete base map" baseMorphism
      let mut baseSlots : Array Nat := #[]
      for index in [:params.size] do
        if ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType params[index]!) (← inferType baseMorphism) <&&>
              isDefEq params[index]! baseMorphism) then
          baseSlots := baseSlots.push index
      let #[baseSlot] := baseSlots
        | throwError "the cartesian invocation lost its independently selected base-map parameter slot"
      let parameters ← capturedCallableParameters h trace params #[(baseSlot, base)]
      let fields := parameters.flatMap (·.templates)
      let invocationParameters : Array ActionDataTemplate := #[.array fields, .wire .object original]
      let descriptor : ActionDataTemplate := .ctor "cartesianMap"
        (#[.literal { json := toJson id.raw }] ++ invocationParameters)
      let (callable, dependencies) ← renderCapturedActionData descriptor
      let some inputForm := state.cartesianForm? entry.cartesianAddress
        | throwError "the cartesian map has no accepted complete invocation address"
      if field != "hom" then
        let data ← scopedNode "morphismEndpoint" #[callable, { json := toJson field }]
        return {
          form := contextualForm state plan.total inputForm
          payload := (← combinedRecipePayload e data dependencies)
          categoryContext := some plan.total }
      let wire : Wire := {
        form := inputForm, payload := (← combinedRecipePayload e callable dependencies)
        categoryContext := some plan.total }
      -- These are the producer's own projections of this complete cartesian
      -- invocation, not separately cached objects with equal formal values.
      let source ← callableEndpointReference wire source true (some plan.total)
      let target ← callableEndpointReference wire target false (some plan.total)
      captureSelectedCallable h trace wire entry.cartesianAddress plan.action parameters descriptor
        invocationParameters (some plan.total)
        (some ({ wire := source, origin := .reference }, { wire := target, origin := .reference })) none
  | .liftFactor receiver baseMap cone proof =>
      captureLiftFactor h trace e receiver baseMap cone proof
  | .cellComponent id params constructors inverse receiver =>
      let some entry := state.cells.find? (·.id == id)
        | throwError "the selected cell is no longer registered"
      let action ← CellAction.select entry (← params.mapM exprToSyntax) constructors inverse receiver
      unless ← withTransparency .all <| isDefEq (← CellAction.component action receiver) e do
        throwError "the selected cell changed its actual full component"
      let original ← realizeUnobserved h trace "the natural component's complete selected receiver" receiver
      let parameters ← capturedCallableParameters h trace params #[]
      let fields := parameters.flatMap (·.templates)
      let invocationParameters : Array ActionDataTemplate :=
        #[.array fields, .wire .object original, .literal { json := toJson inverse }]
      let base : ActionDataTemplate := .ctor "cellComponent"
        (#[.literal { json := toJson id.raw }] ++ invocationParameters)
      let descriptor := if constructors.isEmpty then base else
        ActionDataTemplate.ctor "constructedCellComponent"
          #[.literal { json := toJson (constructors.map (·.raw)) }, base]
      let (data, dependencies) ← renderCapturedActionData descriptor
      let some form := state.componentForm? (entry.componentAddress constructors)
        | throwError "the component's complete accepted input form is absent"
      let context : CategoryContext := { expression := action.target, bundle := action.targetBundle }
      let source ← transportImage trace original action.leftRoute (some action.leftApplications)
        (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      let target ← transportImage trace original action.rightRoute (some action.rightApplications)
        (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      CategoryContext.checkMorphism context e source.value target.value
      let wire : Wire := {
        form, payload := (← combinedRecipePayload e data dependencies)
        categoryContext := some context }
      captureSelectedCallable h trace wire (entry.componentAddress constructors) action.transformation
        parameters descriptor invocationParameters (some context)
        (some ({ wire := source, origin := .retained }, { wire := target, origin := .retained })) none
  | .cellEndpoint id params constructors inverse right receiver =>
      let some entry := state.cells.find? (·.id == id)
        | throwError "the selected endpoint's cell is no longer registered"
      let action ← CellAction.select entry (← params.mapM exprToSyntax) constructors inverse receiver
      let (source, target) ← CellAction.objects action receiver
      unless ← withTransparency .all <| isDefEq e (if right then target else source) do
        throwError "the component endpoint changed its exact selected object action"
      contextualAction h trace e receiver
        { expression := action.source, bundle := action.sourceBundle }
        { expression := action.target, bundle := action.targetBundle }
        (if right then action.rightRoute else action.leftRoute)
        (if right then action.rightApplications else action.leftApplications) false
  | .callableRecipe categoryId domain target body =>
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the callable recipe category is not registered"
      let expected ← mkAppM ``Quiver.Hom #[domain, target]
      unless ← withoutModifyingState (isDefEq (← inferType body) expected) do
        throwError "the callable recipe changed its complete formal endpoints"
      let wire ← realize h trace "the retained callable body" body
      let context ← CategoryContext.ofNamed category domain
      let complete ← captureCompleteCallable h trace wire context none false
      let some (sourceWire, targetWire) ← retainedCallableEndpoints? complete context
        | throwError "the callable wrapper lost its original complete endpoints"
      let result : Wire := { wire with
        form := .canonicalMorphism category, payload := forwardPayload wire e wire.json
        categoryContext := some context, morphismFraming := none
        actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none }
      let result ← retainIntrinsicAssembly result .map context (.wire .map wire)
      retainCallableEndpoints result sourceWire targetWire context
  | .object id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let captured ← capturedParameterData h trace params
      let parameters ← captured.mapM renderCapturedActionData
      let args := parameters.map Prod.fst
      let dependencies := parameters.foldl (fun result parameter => result ++ parameter.2) #[]
      if let some presented ← realizeObjectPresentation h trace entry params args dependencies captured then
        unless ← withTransparency .all <|
            isDefEq (← inferType presented.value) (← inferType e) <&&>
              isDefEq presented.value e do
          throwError "the named-object presentation changed its complete selected result"
        return ← forwardRetainedValue presented e
      let json ← scopedNode id.raw args
      let some category := state.categories.find? (·.id == entry.category)
        | throwError "the named constructor lost its complete declared category"
      let context ← CategoryContext.ofNamed category e
      let wire : Wire := {
        form := .object entry, payload := (← combinedRecipePayload e json dependencies),
        categoryContext := some context }
      return ← retainIntrinsicAssembly wire .object context (.ctor id.raw captured)
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      let input ← realize h trace s!"the structural parameter of {what}" receiver
      let .object entry := input.form
        | throwStratum .noImplementation m!"a structural parameter has no named-object presentation"
      unless entry.id == source && entry.category == sourceCategory do
        throwStratum .noImplementation m!"a structural parameter has a different source presentation"
      let output ← transport trace input route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      let image ← if route.isEmpty then pure receiver
        else Semantic.objOf (← Semantic.routeFunctor state route) receiver
      unless ← withoutModifyingState (isDefEq image e) do
        throwError "the structural parameter disagrees with its recorded semantic route"
      unless ← withTransparency .all <|
          isDefEq (← inferType output.value) (← inferType e) <&&> isDefEq output.value e do
        throwError "the realized structural parameter has an incompatible full structured type"
      if output.form.category == targetCategory then return output
      let some target := state.categories.find? (·.id == targetCategory)
        | throwError "the structural parameter target schema is not registered"
      let some edge := route.back?
        | throwError "an empty structural route changed its selected category"
      let actual ← transportImage trace input route none
        (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual.value) (← inferType image) <&&>
            isDefEq actual.value image) do
        throwError "the structural parameter fallback changed its complete selected action"
      return { actual with
        form := imageForm state edge target
        payload := forwardPayload actual image actual.json }
  | .proofRefinement classifier sourceCategory targetCategory source action identity =>
      let some target := state.categories.find? (·.id == targetCategory)
        | throwError "the proof refinement total schema is no longer registered"
      let completed ← ProofRefinement.construct state classifier target source
      unless (← withTransparency .all <| isDefEq completed.value e) &&
          (← withTransparency .all <| isDefEq completed.action action) do
        throwError "the proof refinement changed its complete supplied formal object"
      let image ← Semantic.objOf action e
      unless !identity.hasSorry && (← Decide.kernelAccepts (← mkEq image source) identity) do
        throwError "the proof refinement has no accepted full forgetful-image identification"
      let original ← realize h trace s!"the full source of the proof refinement in {what}" source
      unless original.form.category == sourceCategory do
        throwError "the proof refinement source has a different registered category"
      checkProofRefinementSource original source
      let snapshot : WireSnapshot := {
        form := original.form, payload := original.payload,
        presentationIsos := original.presentationIsos, objectIso := original.objectIso,
        callableObserved := original.callableObserved,
        objectObserved := original.objectObserved,
        liftExecution := original.liftExecution,
        categoryContext := original.categoryContext,
        endpointPresentation := original.endpointPresentation,
        constructionInputs := original.constructionInputs,
        constructionInputOwnership := original.constructionInputOwnership,
        serviceHandles := original.serviceHandles,
        serviceInputPaths := original.serviceInputPaths,
        pointDataInterface := original.pointDataInterface,
        productComponents := original.productComponents, actionRecipe := original.actionRecipe,
        intrinsicAssembly := original.intrinsicAssembly, capturedInvocation := original.capturedInvocation,
        callableEndpoints := original.callableEndpoints,
        pointOrigin := original.pointOrigin,
        morphismFramed := original.morphismFramed,
        morphismFraming := original.morphismFraming }
      return {
        form := .proofRefinement target classifier original.form,
        payload := forwardPayload original e original.json,
        proofSources := snapshot :: original.proofSources }
  | .parameterEquivalence expectedType representative sources =>
      unless ← isDefEq representative e do
        throwError "the parameter identity class has a different requested representative"
      let some chosen := sources[0]?
        | throwError "the parameter identity class has no accepted source"
      for source in sources do
        let some entry := state.objects.find? (·.id == source.source)
          | throwError "the parameter identity class has an unregistered source"
        unless entry.category == source.sourceCategory do
          throwError "the parameter identity class has a different declared source category"
        let object ← objectAt trace entry source.params
        unless ← isDefEq object source.object do
          throwError "the parameter identity class lost its exact declared source arguments"
        unless source.route.size == source.applications.size do
          throwError "the parameter identity class lost its complete ordered edge applications"
        let mut image := object
        for (step, application) in source.route.zip source.applications do
          if application.hasMVar || application.hasLevelMVar || application.hasFVar ||
              application.hasLooseBVars then
            throwError "the parameter identity class has an unresolved selected edge application"
          discard <| edgeDescriptor trace step application h.parameterRecovery
          image ← Semantic.objOf application image
        unless (← isDefEq image source.image) && (← isDefEq (← inferType image) expectedType) do
          throwError "the parameter identity class has an incompatible full structured image"
        unless ← Decide.kernelAccepts (← mkEq source.image representative) source.identity do
          throwError "the parameter identity class has no checked full-object identification"
      if representative != e then
        let actual ← realize h trace s!"the retained actual parameter in {what}" representative
        unless ← withTransparency .all <| isDefEq (← inferType actual.value) expectedType do
          throwError "the retained parameter result changed its complete selected type"
        return { actual with payload := forwardPayload actual e actual.json }
      let input ← realize h trace s!"the accepted source of the parameter in {what}" chosen.object
      let output ← transportImage trace input chosen.route (some chosen.applications)
        (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      unless ← isDefEq (← inferType output.value) expectedType do
        throwError "the realized parameter identity class has an incompatible structured type"
      return output
  | .namedMorphism id params =>
      let some entry := state.morphisms.find? (·.id == id) | unreachable!
      let parameters ← capturedCallableParameters h trace params #[]
      let fields := parameters.flatMap (·.templates)
      let descriptor : ActionDataTemplate := .ctor id.raw fields
      let (json, dependencies) ← renderCapturedActionData descriptor
      let wire : Wire := {
        form := .namedMorphism entry
        payload := (← combinedRecipePayload e json dependencies) }
      captureSelectedCallable h trace wire id.raw e parameters descriptor fields none none none
  | .namedInclusion id categoryId params source target =>
      let some entry := state.inclusions.find? (·.id == id)
        | throwError "the retained inclusion is not a published row"
      unless entry.category == categoryId do
        throwError "the retained inclusion changed its registered category"
      unless ← withTransparency .all <| isDefEq (← inferType e)
          (← mkAppM ``Quiver.Hom #[source, target]) do
        throwError "the retained inclusion changed its full endpoint types"
      let (parameters, dependencies) ← realizedParameterData h trace params
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let json ← scopedNode id.raw parameters
      return {
        form := .canonicalMorphism category
        payload := (← combinedRecipePayload e json dependencies) }
  | .powerObjectMap id field params =>
      let some entry := state.powerObjects.find? (·.id == id)
        | throwError "the retained power object is not registered"
      let declaration ← match field with
        | "member" => pure entry.member
        | "terminal" => pure entry.terminal
        | "transpose" => pure entry.transpose
        | "image" => pure entry.image
        | "truth" => pure entry.truth
        | _ => throwError "the retained power object registers no {field} map"
      -- The field's complete original application fixes its declaration and
      -- ordered parameters; no reconstructed application supplies this receipt.
      let application ← StructuredResult.checkReconstruction (operationApplicationBody e)
      unless application.getAppFn.constName? == some declaration do
        throwError "the retained power-object field changed its complete registered declaration"
      let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
        fields.mapM (·.fvarId!.getBinderInfo)
      unless application.getAppNumArgs == infos.size do
        throwError "the retained power-object field lost its complete declaration application"
      let explicit := (application.getAppArgs.zip infos).filterMap fun (value, info) =>
        if info.isExplicit then some value else none
      unless explicit.size == params.size do
        throwError "the retained power-object field lost an ordered declaration parameter"
      for (formal, selected) in explicit.zip params do
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType formal) (← inferType selected) <&&>
              isDefEq formal selected) do
          throwError "the retained power-object field changed a complete declaration parameter"
      let some object := state.objects.find? (·.id == entry.object)
        | throwError "the retained power object lost its registered object family"
      let some category := state.categories.find? (·.id == object.category)
        | throwError "the retained power object lost its registered complete category"
      let some (source, target) := Language.homEnds? (← inferType e)
        | throwError "the retained power-object field lost its complete declared Hom"
      let context ← CategoryContext.ofNamed category source
      CategoryContext.checkMorphism context e source target
      let parameters ← capturedCallableParameters h trace params #[]
      let descriptor : ActionDataTemplate := .ctor "powerObjectMap"
        #[.literal { json := toJson id.raw }, .literal { json := toJson field },
          .array (parameters.flatMap (·.templates))]
      let (json, dependencies) ← renderCapturedActionData descriptor
      let wire : Wire := {
        form := .canonicalMorphism category
        payload := (← combinedRecipePayload e json dependencies)
        categoryContext := some context }
      -- Capture the same initial endpoint occurrences before the raw callable
      -- leaves its producer. Observation refreshes them and the parameter slots
      -- through their retained typed children, never through a later cache read.
      let (source, target) ← capturedMapEndpoints
        { h with demandObjectActions := false } trace wire context
      let wire ← retainIntrinsicAssembly wire .map context descriptor
      retainCallableEndpoints wire source target context
  | .objectField id field categoryId params =>
      let some entry := state.objects.find? (·.id == id)
        | throwError "the retained field owner is not registered"
      let declared := ObjectPresentation.fieldDeclaration entry field
      unless declared.isSome do
        throwError "the retained object row registers no {field} map"
      unless (← ObjectPresentation.fieldCategory entry field) == categoryId do
        throwError "the retained object field changed its complete declared category"
      let actual ← ObjectPresentation.field entry field params
      unless ← withTransparency .all <| isDefEq actual e do
        throwError "the retained object field changed its accepted map or direction"
      let (parameters, dependencies) ← realizedParameterData h trace params
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let json ← scopedNode "objectField" #[{ json := toJson id.raw },
        { json := toJson field }, DataOwnership.Data.array parameters]
      return {
        form := .canonicalMorphism category
        payload := (← combinedRecipePayload e json dependencies) }
  | .constrainedPoint constructor categoryId domain source target original =>
      let some schema ← ConstrainedPoint.schema? target
        | throwError "the retained constrained point lost its fixed constructor interface"
      unless schema.constructor == constructor && categoryId == CategoryId.sets &&
          (← withTransparency .all <| isDefEq schema.dataType source) do
        throwError "the retained constrained point changed its constructor or original data type"
      let expected ← mkAppM ``Quiver.Hom #[domain, target]
      let originalExpected ← mkAppM ``Quiver.Hom #[domain, source]
      unless (← withTransparency .all <| isDefEq (← inferType e) expected) &&
          (← withTransparency .all <| isDefEq (← inferType original) originalExpected) do
        throwError "the retained constrained point changed its complete endpoints"
      let projected ← ConstrainedPoint.project schema (← Language.functionOf e)
      unless ← withTransparency .all <| isDefEq projected (← Language.functionOf original) do
        throwError "the constrained constructor changed the original formal point data"
      let datum ← realize h trace "the original constrained computational point" original
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the constrained point category is not registered"
      let context ← CategoryContext.ofNamed category domain
      CategoryContext.checkMorphism context e domain target
      let domainWire ← realizeCallableEndpoint h trace datum domain true (some context)
      let sourceWire ← realizeCallableEndpoint h trace datum source false (some context)
      let targetWire ← realizeEndpoint h trace "the constrained point selected target" target
      let template : ActionDataTemplate := .ctor "constrainedPoint"
        #[.literal { json := toJson constructor.toString }, .wire .retained domainWire,
          .wire .retained sourceWire, .wire .retained targetWire, .wire .map datum]
      let (json, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := .canonicalMorphism category
        payload := (← combinedRecipePayload e json dependencies)
        categoryContext := some context }
      let result ← retainIntrinsicAssembly result .map context template #[] #[]
        (.retained, .retained)
      return ← retainCallableEndpoints result domainWire targetWire context
  | .admittedPoint id categoryId params original originalCategory originalSource originalTarget =>
      let some entry := state.objects.find? (·.id == id)
        | throwError "the admitted point owner is not registered"
      unless entry.category == categoryId && entry.admission.isSome do
        throwError "the admitted point changed its published owner or category"
      let datum ← realize h trace "the original admitted computational point" original
      let some originalSchema := state.categories.find? (·.id == originalCategory)
        | throwError "the admitted point's original category is not registered"
      let family ← instantiateFresh originalSchema.declaration
      let objects ← mkAppM ``CategoryTheory.Bundled.α #[family]
      unless ← isDefEq (← inferType originalSource) objects <&&>
          isDefEq (← inferType originalTarget) objects do
        throwError "the admitted point's endpoints left their original category"
      let family ← instantiateMVars family
      let objects ← instantiateMVars objects
      let dictionary ← mkAppM ``CategoryTheory.Cat.str #[family]
      let categoryStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some objects, some dictionary]
      let quiver ← mkAppOptM ``CategoryTheory.CategoryStruct.toQuiver
        #[some objects, some categoryStruct]
      let pointType ← mkAppOptM ``Quiver.Hom
        #[some objects, some quiver, some originalSource, some originalTarget]
      -- The element descriptor names its selected structured object. Its owner
      -- category need not be the category of the original point's actual arrow.
      unless ← withTransparency .all <| isDefEq (← inferType datum.value) pointType do
        throwError "the admitted point changed its original computational arrow type"
      let parameterTemplates ← capturedParameterData h trace params
      let renderedParameters ← parameterTemplates.mapM renderCapturedActionData
      let parameters := renderedParameters.map Prod.fst
      let some (domain, selected) := Language.homEnds? (← inferType e)
        | throwError "the admitted point lost its full formal endpoints"
      let dataParameters ← DirectConstruction.dataArguments params
      unless dataParameters.size == parameters.size do
        throwError "the admitted point lost an ordered data parameter"
      let objects : ComputationalData.InterfaceObjects :=
        (parameters.zip dataParameters).map fun (data, formal) => (data.json, formal)
      let .ok input ← ComputationalData.admissionInterface objects entry
          (← inferType e) (parameters.map (·.json))
        | throwError "the admitted point changed its complete published input interface"
      let originalContext : CategoryContext := {
        expression := originalSchema.expression, bundle := (← instantiateMVars family) }
      let (datum, inputObject) ← if ← withoutModifyingState (withTransparency .all <|
          isDefEq originalTarget input) then do
        let point ← pointAtAdmissionDomain h trace datum originalSource originalTarget domain
        pure (point, originalTarget)
      else do
        let some owner ← callableObjectPlan? input
          | throwStratum .noImplementation
              "the admission's complete whole-function input has no registered object presentation"
        let point ← wholeCallablePoint h trace datum originalSource originalTarget domain
          originalContext owner
        pure (point, owner.application.value)
      unless ← withTransparency .all <| isDefEq (← inferType datum.value)
          (← mkAppM ``Quiver.Hom #[domain, input]) do
        throwError "the original admission datum changed its complete point domain or input type"
      -- The outer point domain comes from this actual admission declaration.
      -- A whole function's internal domain remains in its selected object and
      -- complete original callable data, never in place of this outer source.
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the admitted point category is not registered"
      let context ← CategoryContext.ofNamed category domain
      CategoryContext.checkMorphism context e domain selected
      let source ← realizeCallableEndpoint h trace datum domain true
      let target ← realizeCallableEndpoint h trace datum inputObject false
      discard <| Semantic.recordNamedObject selected (some trace)
      let selected ← realizeEndpoint h trace "the admitted point selected target" selected
      let template : ActionDataTemplate := .ctor "admittedPoint"
        #[.literal { json := toJson id.raw }, .retained (.array parameterTemplates),
          .wire .retained source, .wire .retained target, .wire .retained selected,
          .wire .map datum]
      let (json, dependencies) ← renderCapturedActionData template
      let payload ← combinedRecipePayload e json dependencies
      let result : Wire := {
        form := .canonicalMorphism category
        payload := payload
        categoryContext := some context
        serviceHandles := (← retainLiftOperands h dependencies) }
      let result ← retainIntrinsicAssembly result .map context template #[] #[]
        (.retained, .retained)
      return ← retainCallableEndpoints result source selected context
  | .namedCallable address categoryId params =>
      let some (_, declaredCategory) := state.callable? address
        | throwError "the callable is not published by its registered owner"
      unless declaredCategory == categoryId do
        throwError "the callable changed its declared category"
      let form ← match state.form? address with
        | some form => pure form
        | none =>
          let some category := state.categories.find? (·.id == categoryId)
            | throwError "the callable has no registered categorical map interface"
          pure (.canonicalMorphism category)
      let parameters ← capturedCallableParameters h trace params #[]
      let fields := parameters.flatMap (·.templates)
      let descriptor : ActionDataTemplate := .ctor address fields
      let (json, dependencies) ← renderCapturedActionData descriptor
      let wire : Wire := { form, payload := (← combinedRecipePayload e json dependencies) }
      captureSelectedCallable h trace wire address e parameters descriptor fields none none none
  | .pointView source target route applications argument =>
      let original ← realize h trace "the original point structure" source
      let selected ← realize h trace "the selected forward point structure" target
      unless route.size == applications.size do
        throwError "the point view omitted an actual edge application"
      let some originalCategory := state.categories.find? (·.id == original.form.category)
        | throwError "the original point structure category is not registered"
      let mut currentCategory := originalCategory.expression
      let mut image := original.value
      let mut targetData := original.fragment
      let mut routeDependencies := #[]
      for (edgeRef, application) in route.zip applications do
        let some edge := (state.edgesFrom currentCategory).find? (·.ref == edgeRef)
          | throwError "the point view does not use an accepted structural route"
        let application ← StructuredResult.checkReconstruction application
        let declared ← Semantic.edgeFunctor state edgeRef
        unless ← withoutModifyingState (isDefEq declared application) do
          throwError "the retained point action is not its registered edge application"
        image ← Semantic.objOf application image
        let (descriptor, dependencies) ← realizedEdgeData h trace edgeRef application
        targetData ← scopedNode "functorAction" #[descriptor, targetData]
        routeDependencies := routeDependencies ++ dependencies
        currentCategory := edge.target
      unless ← withTransparency .all <| isDefEq image selected.value do
        throwError "the forward point view disagrees with its full selected structure"
      let point ← realize h trace "the original closed point" argument
      unless ← withTransparency .all <| isDefEq (← inferType point.value) (← inferType e) do
        throwStratum .noImplementation "the structural view does not preserve this point's carrier"
      unless ← withTransparency .all <| isDefEq point.value e do
        throwError "the forward carrier identification changed the actual closed point"
      let some (domain, _) := Language.homEnds? (← inferType e)
        | throwError "the retained point view lost its exact domain"
      discard <| Semantic.recordNamedObject domain (some trace)
      let domainWire ← realize h trace "the exact generalized point domain" domain
      let sourceAnswer ← scopedNode "element" #[original.fragment,
        ← scopedNode "point" #[point.fragment]]
      let json ← scopedNode "pointView" #[targetData, sourceAnswer, domainWire.fragment]
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      return {
        form := .canonicalMorphism sets
        payload := (← combinedRecipePayload e json (#[original, selected, point, domainWire] ++ routeDependencies)) }
  | .limitProjection receiver index =>
      captureConstructionLeg h trace e receiver index
  | .arrowProjection receiver =>
      let wire ← realize h trace "the stored arrow object" receiver
      let some expression := state.formExpression? wire.form
        | throwError "the stored Arrow lost its accepted category expression"
      let .construct constructor #[.category base] := expression
        | throwStratum .invalid "the receiver is not a registered arrow construction"
      unless (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        throwStratum .invalid "the receiver uses a different registered construction"
      let arrowType ← StructuredProjection.interfaceType (← inferType receiver)
      unless arrowType.isAppOfArity ``CategoryTheory.Arrow 2 do
        throwError "the stored Arrow lost its exact typed category"
      let bundle ← mkAppOptM ``CategoryTheory.Cat.of
        #[some arrowType.getAppArgs[0]!, some arrowType.getAppArgs[1]!]
      let baseContext ← CategoryContext.presented { expression := base, bundle }
      if let some iso := wire.objectIso then
        unless ← withTransparency .all <| isDefEq (← inferType iso)
            (← mkAppM ``CategoryTheory.Iso #[receiver, wire.value]) do
          throwError "the stored Arrow comparison changes its full independently selected receiver"
      let value ← alignedArrowHom wire.value wire.objectIso
      unless ← isDefEq (← inferType value) (← inferType e) do
        throwError "the stored arrow projection changed its fixed endpoints"
      let json ← match wire.json.getObjValAs? String "ctor",
          (wire.json.getObjVal? "args").bind (·.getArr?) with
        | .ok "arrow", .ok #[_, _, _] =>
            if wire.objectIso.isNone then
              checkedFragment (wire.fragment.project #[.field "args", .index 2])
            else scopedNode "arrowHom" #[wire.fragment]
        | _, _ => scopedNode "arrowHom" #[wire.fragment]
      return {
        form := contextualForm state baseContext wire.form true
        payload := (← combinedRecipePayload e json #[wire])
        categoryContext := some baseContext }
  | .morphismIdentity categoryId object =>
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let context ← CategoryContext.ofNamed category object
      let endpoint ← realizeEndpoint h trace "the identity endpoint" object
      captureIntrinsicIdentity e (.canonicalMorphism category) context endpoint
  | .productMediator categoryId presentation domain left right =>
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the formal product mediator category is not registered"
      let first ← realize h trace "the first product point" left
      let second ← realize h trace "the second product point" right
      let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
      let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
      unless ← withTransparency .all <| isDefEq (← inferType e)
          (← mkAppM ``Quiver.Hom #[domain, apex]) do
        throwError "the product point changed its independently fixed formal type"
      let context ← CategoryContext.ofNamed category domain
      let source ← realizeEndpoint h trace "the product point's generalized domain" domain
      let target ← realizeEndpoint h trace "the product point's complete target" apex
      -- A child with a current callable receipt owns its complete endpoints.
      -- Native point data keep their original interface; this producer does not
      -- invent a whole-map receipt for them from the parent or a formal key.
      let childFields ← #[first, second].mapM fun child => do
        let endpoints ← retainedCallableEndpoints? child context
        return endpoints.map fun (source, target) =>
          ({ context, source, target, callable := child } : IntrinsicMapFields)
      let maps := childFields.filterMap id
      let mut equalObjects := maps.map fun fields => (source, fields.source)
      if let #[firstTarget, secondTarget] := target.productComponents then
        for (fields, component) in childFields.zip #[firstTarget, secondTarget] do
          if let some fields := fields then
            equalObjects := equalObjects.push (component, fields.target)
      -- Generalized maps and closed point arrays keep their existing distinct
      -- public encodings. Their ordered child occurrences are fixed here.
      unless ← withTransparency .all <| isDefEq domain (← closedElementDomain state) do
        let template : ActionDataTemplate := .ctor "mediator"
          #[.wire .map first, .wire .map second]
        let (json, dependencies) ← renderCapturedActionData template
        let point : Wire := {
          form := .canonicalMorphism category
          payload := (← combinedRecipePayload e json dependencies) }
        let point ← retainPointOrigin point context source target
          (.product presentation domain first second
            #[.field "args", .index 0] #[.field "args", .index 1])
        return ← retainIntrinsicAssembly point .map context template maps equalObjects
      -- A symbolic element retains its arithmetic owner, which may differ from
      -- this component's complete coordinate. Keep both in the existing public
      -- callable frame. Actual returned point data keep their original encoding.
      let framePoint (wire : Wire) : TermElabM ActionDataTemplate := do
        unless (wire.json.getObjValAs? String "ctor").toOption == some "element" do
          return .wire .map wire
        let some (_, endpoint) := Language.homEnds? (← inferType wire.value)
          | throwError "the product's symbolic point lost its complete endpoint"
        frameMorphismTemplate h trace domain endpoint wire
      let template : ActionDataTemplate := .array #[← framePoint first, ← framePoint second]
      let (data, dependencies) ← renderCapturedActionData template
      let payload ← combinedRecipePayload e data (#[first, second] ++ dependencies)
      -- This array is the product point's two ordered components, not a graph
      -- over its generalized domain. Apply the complete endpoint presentations
      -- here so later callable framing preserves the released point encoding.
      let point : Wire := { form := .canonicalMorphism category, payload }
      let point ← retainPointOrigin point context source target
        (.product presentation domain first second #[.index 0] #[.index 1])
      let point ← retainIntrinsicAssembly point .map context template maps equalObjects
      presentMorphism point source target
  | .morphismComposition categoryId first second source middle target =>
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      -- The recorded composition, not a child data form, selects this full
      -- category. A point in a declared Hom object can carry a reduced bundled
      -- map type while still being exactly this independently selected arrow.
      let context ← CategoryContext.ofNamed category source
      CategoryContext.checkMorphism context first source middle
      CategoryContext.checkMorphism context second middle target
      CategoryContext.checkMorphism context e source target
      let specialized ← match ← (trace.node? second : IO _) with
        | some (.constructionMap id params _ _ _) => do
          if h.demandObjectActions then pure none
          else do
            let some entry := state.constructions.find? (·.id == id)
              | throwError "the applied construction map is no longer registered"
            let (parameters, dependencies) ← realizedParameterData h trace params
            pure (some (entry.mapAddress, parameters, dependencies,
              Form.constructionInput entry categoryId))
        | some (.cellComponent id params constructors inverse receiver) => do
          let some entry := state.cells.find? (·.id == id)
            | throwError "the applied cell is no longer registered"
          let (parameters, dependencies) ← realizedParameterData h trace params
          let original ← realize h trace "the component's complete selected receiver" receiver
          pure (some (entry.componentAddress constructors,
            #[DataOwnership.Data.array parameters, original.fragment, { json := toJson inverse }],
            dependencies.push original,
            Form.cellComponent entry constructors categoryId))
        | _ => pure none
      if let some (address, parameters, dependencies, inputForm) := specialized then
        let argument ← realize h trace "the original generalized point of the selected action" first
        let arrow ← realize h trace "the complete selected callable action" second
        let domainWire ← realizeEndpoint h trace "the selected action's original generalized domain" source
        let sourceWire ← realizeEndpoint h trace "the selected action's complete source" middle
        let targetWire ← realizeEndpoint h trace "the selected action's complete target" target
        let invocation ← pointInvocationData address parameters arrow.fragment
          domainWire.fragment sourceWire.fragment targetWire.fragment argument.fragment
        let input : Wire := {
          form := inputForm
          payload := (← combinedRecipePayload e invocation
            (#[argument, arrow, domainWire, sourceWire, targetWire] ++ dependencies))
          serviceHandles := (← retainServiceOperands h
            (#[argument, arrow, domainWire, sourceWire, targetWire] ++ dependencies)) }
        let reply ← sendData h address input (completeRequest := true)
        let answer := reply.data.json
        let backend := reply.backend
        let validation ← if ← withTransparency .all <| isDefEq source (← closedElementDomain state) then
          ComputationalData.validateElementAt target targetWire.json (← pointResultValue state e) answer
        else ComputationalData.validateEndpointPort e domainWire.json targetWire.json answer
        match validation with
        | .error message => malformed backend address answer message
        | .ok () => pure ()
        let data ← receiveReplyData h address reply
        let result : Wire := {
          form := .canonicalMorphism category, payload := .computed e data
          categoryContext := some context
          pointDataInterface := (← pointInvocationInterface e input.fragment) }
        return ← retainPointOrMapEndpoints result domainWire targetWire
      let callable ← match ← (trace.node? second : IO _) with
        | some (.namedMorphism id params) => pure (some (id.raw, params))
        | some (.namedCallable address _ params) => pure (some (address, params))
        | _ => pure none
      -- Composition with a registered callable is point evaluation only when
      -- the first arrow starts at the published generalized-point domain.
      -- Otherwise it is genuine categorical composition (e.g. rev ∘ rev).
      let pointApplication ← withTransparency .all <| withoutModifyingState
        (isDefEq source (← closedElementDomain state))
      if let some (address, params) := if pointApplication then callable else none then
        let some (_, declaredCategory) := state.callable? address
          | throwError "the applied map is not registered"
        unless declaredCategory == categoryId do
          throwError "the applied map changed its declared category"
        let argument ← realize h trace "the generalized point supplied to the operation" first
        unless ← withTransparency .all <| isDefEq (← inferType argument.value)
            (← mkAppM ``Quiver.Hom #[source, middle]) do
          throwError "the computational argument changed its independently fixed endpoints"
        let (parameters, parameterWires) ← realizedParameterData h trace params
        for object in #[source, middle, target] do
          discard <| Semantic.recordNamedObject object (some trace)
        let domainWire ← realizeEndpoint h trace "the generalized point domain" source
        let sourceWire ← realizeEndpoint h trace "the applied operation source" middle
        let targetWire ← realizeEndpoint h trace "the applied operation target" target
        let operationWire ← realize h trace "the complete applied operation" second
        let (arrow, operationEndpoints) ← renderCapturedActionData (← frameMorphismTemplate
          h trace middle target operationWire (some context) (pointAsMap := true))
        let (argumentData, argumentEndpoints) ← renderCapturedActionData (← frameMorphismTemplate
          h trace source middle argument (some context))
        let requestData ← pointInvocationData address parameters arrow domainWire.fragment
          sourceWire.fragment targetWire.fragment argumentData
        let payload ← combinedRecipePayload e requestData
          (#[argument, operationWire, domainWire, sourceWire, targetWire] ++
            parameterWires ++ operationEndpoints ++ argumentEndpoints)
        let request : Wire := {
          form := sourceWire.form, payload
          serviceHandles := (← retainServiceOperands h
            (#[argument, operationWire, domainWire, sourceWire, targetWire] ++
              parameterWires ++ operationEndpoints ++ argumentEndpoints)) }
        let reply ← sendData h address request (completeRequest := true)
        let answer := reply.data.json
        let backend := reply.backend
        match ← ComputationalData.validateElementAt target targetWire.json
            (← pointResultValue state e) answer with
        | .error message => malformed backend address answer message
        | .ok () => pure ()
        let data ← receiveReplyData h address reply
        return {
          form := .canonicalMorphism category, payload := .computed e data
          categoryContext := some context
          pointDataInterface := (← pointInvocationInterface e request.fragment)
          morphismFramed := true }
      let a ← realize h trace "the first composed map" first
      let b ← realize h trace "the second composed map" second
      unless ← isDefEq (← inferType a.value) (← mkAppM ``Quiver.Hom #[source, middle]) do
        throwError "the first computed arrow changed its fixed endpoints"
      unless ← isDefEq (← inferType b.value) (← mkAppM ``Quiver.Hom #[middle, target]) do
        throwError "the second computed arrow changed its fixed endpoints"
      let value ← mkAppM ``CategoryTheory.CategoryStruct.comp #[a.value, b.value]
      discard <| StructuredResult.checkReconstruction value
      let firstWire ← captureCompleteCallable h trace a context
      let secondWire ← captureCompleteCallable h trace b context
      let some (domainWire, firstTarget) ← retainedCallableEndpoints? firstWire context
        | throwError "the intrinsic composition lost its first complete endpoints"
      let some (secondSource, targetWire) ← retainedCallableEndpoints? secondWire context
        | throwError "the intrinsic composition lost its second complete endpoints"
      let template : ActionDataTemplate := .ctor "compose"
        #[.wire .map firstWire, .wire .map secondWire]
      let (data, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := .canonicalMorphism category
        payload := (← combinedRecipePayload e data dependencies)
        morphismFramed := true
        categoryContext := some context }
      let result ← retainIntrinsicAssembly result .map context template #[]
        #[(firstTarget, secondSource)]
      retainCallableEndpoints result domainWire targetWire context
  | .presentation id params inverse =>
      let some entry := state.presentations.find? (·.id == id) | unreachable!
      let application ← DirectConstruction.instantiate entry.declaration (← params.mapM exprToSyntax)
      let application ← DirectConstruction.close application
      let comparison ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom)
        #[application.value]
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType comparison) (← inferType e) <&&> isDefEq comparison e) do
        throwError "the captured presentation changed its complete accepted direction"
      let parameters ← capturedCallableParameters h trace params #[]
      let fields := parameters.flatMap (·.templates)
      let some source := state.objects.find? (·.id == entry.source) | unreachable!
      let descriptor : ActionDataTemplate := .ctor "presentation"
        #[.literal { json := toJson id.raw }, .array fields, .literal { json := toJson inverse }]
      let (json, dependencies) ← renderCapturedActionData descriptor
      let wire : Wire := {
        form := .presentation entry source.category
        payload := (← combinedRecipePayload e json dependencies) }
      captureSelectedCallable h trace wire id.raw application.value parameters descriptor fields none none (some inverse)
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let (args, dependencies) ← realizedParameterData h trace params
      let json ← scopedNode "generator" #[{ json := toJson id.raw }, DataOwnership.Data.array args]
      let wire : Wire := {
        form := .generator entry, payload := (← combinedRecipePayload e json dependencies) }
      let some (source, target) := Language.homEnds? (← inferType e)
        | throwError "the registered generator lost its complete point endpoints"
      let some category := state.categories.find? (·.id == entry.category)
        | throwError "the registered generator lost its declared category"
      let context ← CategoryContext.ofNamed category source
      CategoryContext.checkMorphism context e source target
      let sourceWire ← realizeCallableEndpoint h trace wire source true (some context)
      let targetWire ← realizeCallableEndpoint h trace wire target false (some context)
      retainCallableEndpoints wire sourceWire targetWire context
  | .operationPoint id params comparison operation target selected =>
      let some entry := state.operations.find? (·.id == id) | unreachable!
      let accepted ← elabTermAndSynthesize
        (← `($(mkCIdent entry.declaration) $(← params.mapM exprToSyntax)*)) none
      unless ← withTransparency .all <| isDefEq accepted operation do
        throwError "the terminal point changed its registered operation"
      discard <| StructuredResult.checkReconstruction comparison
      discard <| StructuredResult.checkReconstruction operation
      discard <| StructuredResult.checkReconstruction target
      discard <| StructuredResult.checkReconstruction selected
      let comparisonWire ← realize h trace "the accepted singleton comparison" comparison
      unless ← withTransparency .all <| isDefEq comparisonWire.value comparison do
        throwError "the terminal comparison changed its accepted map"
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparisonWire.value, operation]
      let singleton ← closedElementDomain state
      let compositeType ← whnfR (← inferType composite)
      let compositeArgs := compositeType.getAppArgs
      unless compositeArgs.size >= 2 &&
          (← withTransparency .all <| isDefEq compositeArgs[compositeArgs.size - 2]! singleton) do
        throwError "the accepted terminal comparison has a different singleton source"
      let globalPoint ← Language.globalPoint.run {}
      let point ← elabTermAndSynthesize
        (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax composite)
          $(← exprToSyntax globalPoint))) none
      let homType ← whnfR (← inferType e)
      let homArgs := homType.getAppArgs
      let some domain := homArgs[homArgs.size - 2]? | throwError "the terminal point has no domain"
      let function ← withLocalDeclD `point domain fun argument => do
        mkLambdaFVars #[argument] point
      let value ← mkAppM ``TypeCat.ofHom #[function]
      unless ← withTransparency .all <| isDefEq value e do
        throwError "the canonical terminal data changed its requested point"
      let value ← StructuredResult.checkReconstruction (← mkExpectedTypeHint value (← inferType e))
      discard <| Semantic.recordNamedObject selected (some trace)
      let selectedWire ← realize h trace "the terminal point's selected target" selected
      let domainWire ← realize h trace "the terminal point's original domain" domain
      let (parameterData, dependencies) ← realizedParameterData h trace params
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      let data ← scopedNode "operationPoint" #[{ json := toJson id.raw },
        DataOwnership.Data.array parameterData, comparisonWire.fragment,
        domainWire.fragment, selectedWire.fragment]
      return {
        form := .canonicalMorphism sets
        payload := (← combinedRecipePayload e data (#[comparisonWire, domainWire, selectedWire] ++ dependencies)) }
  | .elementValue point target selected =>
      let globalPoint ← Language.globalPoint.run {}
      let action ← Language.functionOf point
      let value := mkApp action globalPoint
      unless ← withTransparency .all <| isDefEq (← inferType value) target do
        throwError "the closed parameter lost its independently selected point carrier"
      let some projected ← DeclaredAdmission.projectedValue? value (← inferType e)
        | throwError "the closed parameter has no declared single-data-field extraction"
      unless ← withTransparency .all <| isDefEq projected e do
        throwError "the closed parameter lost its independently selected point and carrier"
      discard <| Semantic.recordNamedObject selected (some trace)
      let pointWire ← realize h trace "the closed computational parameter" point
      let selectedWire ← if ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType selected) (← inferType target) <&&>
            isDefEq selected target) then
        -- The actual complete point already fixes this exact endpoint. Its public
        -- endpoint frame also works when a dependent structured parameter has no
        -- separately named presentation. A different structure on the same carrier
        -- still needs its own selected descriptor below.
        realizeCallableEndpoint h trace pointWire selected false
      else realize h trace "the selected parameter structure" selected
      let template : ActionDataTemplate := .ctor "element"
        #[.wire .retained selectedWire, .ctor "point" #[.wire .map pointWire]]
      let (json, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := .element selectedWire.form
        payload := (← combinedRecipePayload e json dependencies) }
      return ← retainIntrinsicResultAssembly result (.value (← inferType e)) template
  | .elementNumeral _ target selected | .operationApply _ _ _ target selected =>
      if let .operationApply _ _ operands _ _ := node then
        for operand in operands do
          discard <| realize h trace "the operation's actual constituent" operand
      discard <| Semantic.recordNamedObject selected (some trace)
      let selectedWire ← realize h trace "the selected element structure" selected
      let (expression, dependencies) ← elementFragment h trace e
      let answer ← scopedNode "element" #[selectedWire.fragment, expression]
      let some (domain, endpoint) := Language.homEnds? (← inferType e)
        | throwError "the retained element expression lost its categorical point endpoints"
      unless ← withTransparency .all <| isDefEq endpoint target do
        throwError "the retained element expression changed its selected target"
      if e.hasMVar || e.hasLevelMVar || e.hasFVar then
        throwError "the retained element expression is not closed"
      unless ← isTypeCorrect e do
        throwError "the retained formal element expression is outside its declared signature"
      let point : Wire := {
        form := .element selectedWire.form
        payload := (← combinedRecipePayload e answer (#[selectedWire] ++ dependencies)) }
      let some sets := state.categories.find? (·.id == CategoryId.sets)
        | throwError "the element point lost its complete data category"
      let context ← CategoryContext.ofNamed sets domain
      let sourceWire ← realizeCallableEndpoint h trace point domain true (some context)
      let targetWire ← realizeCallableEndpoint h trace point endpoint false (some context)
      let point ← retainPointOrigin point context sourceWire targetWire (.element selectedWire dependencies)
      if let .elementNumeral value _ _ := node then
        unless dependencies.isEmpty do
          throwError "the literal point changed its captured numeral expression inputs"
        let template : ActionDataTemplate := .ctor "element" #[
          .wire .object selectedWire, .ctor "numeral" #[.literal { json := toJson value }]]
        return ← retainIntrinsicAssembly point .map context template
      return point
  | .presentationApply id params inverse source target argument =>
      let some entry := state.presentations.find? (·.id == id) | unreachable!
      let comparison ← elabTermAndSynthesize
        (← `($(mkCIdent entry.declaration) $(← params.mapM exprToSyntax)*)) none
      let arrow ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[comparison]
      let exactEndpoints ← mkAppM ``Quiver.Hom #[source, target]
      unless ← isDefEq (← inferType arrow) exactEndpoints do
        throwError "the sealed presentation application disagrees with its accepted endpoints"
      discard <| Semantic.recordNamedObject source (some trace)
      discard <| Semantic.recordNamedObject target (some trace)
      let sourceWire ← realize h trace "the selected presentation source" source
      let targetWire ← realize h trace "the selected presentation target" target
      let argumentWire ← realize h trace "the selected presentation argument" argument
      -- A declared generator is a map descriptor in its own right. At an explicitly
      -- selected presentation it is a closed element of that exact source, just like
      -- every other retained operation expression. Computed points keep their actual
      -- returned data and live owner instead of being expanded back into their plan.
      let (argumentData, argumentDependencies) ← match argumentWire.payload with
        | .ordinary .. => do
            let (expression, dependencies) ← elementFragment h trace argument
            pure (← scopedNode "element" #[sourceWire.fragment, expression], dependencies)
        | _ => pure (argumentWire.fragment, #[])
      let (args, dependencies) ← realizedParameterData h trace params
      let request := { sourceWire with
        payload := (← combinedRecipePayload sourceWire.value
          (← presentationInvocationData args inverse sourceWire.fragment targetWire.fragment argumentData)
          (#[sourceWire, targetWire, argumentWire] ++ argumentDependencies ++ dependencies))
        serviceHandles := (← retainServiceOperands h
          (#[sourceWire, targetWire, argumentWire] ++ argumentDependencies ++ dependencies)) }
      let reply ← sendData h id.raw request #[] true
      let answer := reply.data.json
      let backend := reply.backend
      let expectedPoint ← pointResultValue state e
      match ← ComputationalData.validateElementAt target targetWire.json expectedPoint answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let data ← receiveReplyData h id.raw reply true
      let some (domain, _) := Language.homEnds? (← inferType e)
        | throwError "the completed presentation point lost its original domain"
      let domainWire ← realizeCallableEndpoint h trace argumentWire domain true
      return {
        form := .element targetWire.form, payload := .computed e data
        pointDataInterface := (← pointDataInterfaceAt domain target
          domainWire.fragment targetWire.fragment) }

  | .morphismTransport sourceCategory targetCategory route receiver =>
      let input ← realizeUnobserved h trace "the map before structural transport" receiver
      unless input.form.category == sourceCategory do
        throwError "the structural map has the wrong recorded source category"
      let applications ← route.mapM (fun edge => do Semantic.edgeFunctor state edge)
      let output ← captureMapRoute h trace input route applications
      let requested ← Semantic.mapOf (← Semantic.routeFunctor state route) receiver
      unless ← withTransparency .all <|
          isDefEq requested e <&&> isDefEq output.value e do
        throwError "the recorded map transport differs from its complete semantic request"
      let some category := state.categories.find? (·.id == targetCategory)
        | throwError "the structural map's target category is not registered"
      return { output with
        form := .canonicalMorphism category,
        payload := forwardPayload output e output.json }
  | .functor id params receiver =>
      let some entry := state.functor? id | unreachable!
      -- The reader already selected the whole action, including its implicit
      -- dictionaries. Keep that literal child instead of elaborating its name
      -- again from only the explicit parameter vector.
      let some (retainedAction, retainedReceiver) := FunctorActionData.objectAction? e
        | throwError "the recorded functor lost its complete selected object action"
      let receiver ← instantiateMVars receiver
      unless (← instantiateMVars retainedReceiver) == receiver do
        throwError "the recorded functor changed its original receiver occurrence"
      let F ← instantiateMVars (← Semantic.asFunctor retainedAction)
      let actualParameters ← actionDeclarationParameters state (.functor id) F true
      unless actualParameters == (← params.mapM instantiateMVars) do
        throwError "the recorded functor changed its ordered declaration parameters"
      let input ← realizeUnobserved h trace s!"the source of {id.raw} in {what}" receiver
      let semanticImage ← Semantic.objOf F receiver
      unless ← withoutModifyingState (isDefEq semanticImage e) do
        throwError "the recorded selected functor action disagrees with the semantic request"
      let image ← Semantic.objOf F input.value
      unless ← isDefEq (← inferType image) (← inferType e) do
        throwError "the recorded functor parameters have incompatible typed endpoints"
      let (_, bundle) ← functorCategoryBundles F
      let context ← CategoryContext.presented { expression := entry.target, bundle }
      let target? := CategoryContext.named? state entry.target
      let form := match target? with
        | some target => imageForm state (.functor id) target
        | none => Form.contextual entry.target input.form
      let descriptorTemplate ← capturedEdgeData h trace (.functor id) F
      let (descriptor, _) ← renderCapturedActionData descriptorTemplate
      let projected ← projectObjectFragmentWithOrigin trace entry.source (.functor id)
        F receiver input.fragment (some descriptor)
      if let some projected := projected then
        if projected.isStructural && input.completedData then
          let output : Wire := {
            form, categoryContext := some context, objectObserved := true
            objectIso := (← mapObjectComparison F input.value input.objectIso)
            endpointPresentation := (← mapEndpointPresentation F descriptor.json
              input.endpointPresentation descriptor.ownership)
            payload := (← scopedPayload e projected.data) }
          return ← retainMappedEndpointPresentation (.edge (.functor id)) F input output
            descriptorTemplate
      -- Whether this registered functor is structural does not decide when its
      -- computation executes. Every pending image retains the same typed action
      -- boundary; an observation invokes its ordinary registered object port.
      captureRegisteredObjectAction (.edge (.functor id)) F input e form context
        descriptorTemplate (projected.map (·.data))
  | .retainedRoute _ targetCategory route applications receiver =>
      let input ← realize h trace "the retained structural source" receiver
      let result ← transport trace input route (some (realizedEdgeData h trace))
        (some (capturedEdgeData h trace)) (some applications)
      unless result.form.category == targetCategory &&
          (← withTransparency .all <|
            isDefEq (← inferType result.value) (← inferType e) <&&> isDefEq result.value e) do
        throwError "the retained route changed its full selected target category"
      let mut expected := receiver
      for application in applications do expected ← Semantic.objOf application expected
      unless ← withTransparency .all <| isDefEq expected e do
        throwError "the retained route changed its independently fixed semantic image"
      return result
  | .structureTransport sourceCategory targetCategory route receiver =>
      let semanticImage ← if route.isEmpty then pure receiver
        else Semantic.objOf (← Semantic.routeFunctor state route) receiver
      unless ← withoutModifyingState (isDefEq semanticImage e) do
        throwError "the selected structural route disagrees with the semantic request"
      let input ← realize h trace s!"the selected structure of {what}" receiver
      unless input.form.category == sourceCategory do
        throwError "the selected structure has the wrong recorded source category"
      let output ← transport trace input route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      unless ← withTransparency .all <|
          isDefEq (← inferType output.value) (← inferType e) <&&> isDefEq output.value e do
        throwError "the selected structure action has an incompatible full structured type"
      if output.form.category == targetCategory then return output
      let some target := state.categories.find? (·.id == targetCategory)
        | throwError "the selected structural target schema is not registered"
      let some edge := route.back?
        | throwError "an empty selected route changed its category"
      let actual ← transportImage trace input route none
        (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual.value) (← inferType semanticImage) <&&>
            isDefEq actual.value semanticImage) do
        throwError "the selected structure fallback changed its complete selected action"
      return { actual with
        form := imageForm state edge target
        payload := forwardPayload actual semanticImage actual.json }
  | .binder id params _ _ admitted =>
      let some entry := state.binders.find? (·.id == id) | unreachable!
      let operation := id.raw
      let arrow ← elabTermAndSynthesize
        (← `($(mkCIdent entry.operation) $(← params.mapM exprToSyntax)*)) none
      let some (source, target) := Language.homEnds? (← inferType arrow)
        | throwError "the published binder callable lost its complete map endpoints"
      let input ← realize h trace s!"the admitted map of {id.raw}" admitted
      let some (domain, admittedTarget) := Language.homEnds? (← inferType input.value)
        | throwError "the admitted binder input lost its generalized point endpoints"
      unless ← withTransparency .all <| isDefEq admittedTarget source do
        throwError "the admitted binder input changed the published callable source"
      unless ← withTransparency .all <| isDefEq e
          (← mkAppM ``CategoryTheory.CategoryStruct.comp #[input.value, arrow]) do
        throwError "the selected binder changed its independently fixed complete result"
      for object in #[domain, source, target] do
        if (← trace.node? object).isNone then
          discard <| Semantic.recordNamedObject object (some trace)
      let domainWire ← realize h trace "the binder's generalized point domain" domain
      let sourceWire ← realize h trace "the binder's admitted input object" source
      let targetWire ← realize h trace "the binder's selected output object" target
      let (parameters, parameterWires) ← realizedParameterData h trace params
      let invocation ← pointInvocationData operation parameters
        (← scopedNode operation parameters) domainWire.fragment sourceWire.fragment
        targetWire.fragment input.fragment
      let request : Wire := {
        form := input.form
        payload := (← combinedRecipePayload arrow invocation
          (#[input, domainWire, sourceWire, targetWire] ++ parameterWires))
        serviceHandles := (← retainServiceOperands h
          (#[input, domainWire, sourceWire, targetWire] ++ parameterWires)) }
      let reply ← sendData h operation request (completeRequest := true)
      let answer := reply.data.json
      let backend := reply.backend
      let checked ← if ← withTransparency .all <| isDefEq domain (← closedElementDomain state) then
        ComputationalData.validateElementAt target targetWire.json (← pointResultValue state e) answer
      else ComputationalData.validateEndpointPort e domainWire.json targetWire.json answer
      match checked with
      | .error message => malformed backend operation answer message
      | .ok () => pure ()
      let data ← receiveReplyData h operation reply
      let some category := state.categories.find? (·.id == entry.category) | unreachable!
      let result : Wire := {
        form := .canonicalMorphism category, payload := .computed e data
        pointDataInterface := (← pointInvocationInterface e request.fragment) }
      return ← retainPointOrMapEndpoints result domainWire targetWire
  | .arrow category morphism source target =>
      let some recorded := state.categories.find? (·.id == category)
        | throwError "the recorded arrow context is not registered"
      let isArrow : Bool := match recorded.expression with
        | .construct constructor #[.category _] =>
            (state.constructors.find? (·.id == constructor)).any
              (·.semantics == `CasCatalogue.Constructors.arrow)
        | _ => false
      let expression ← if isArrow then pure recorded.expression else do
        let some expression := state.arrowsOf? recorded.expression
          | throwError "the recorded arrow's constructor is not registered"
        pure expression
      let #[entry] := state.categories.filter (·.expression.syntacticEq expression)
        | throwError "the recorded arrow has no unique registered Arrow category"
      unless ← withTransparency .all <|
          isDefEq (← inferType e) (← categoryCarrierInstance entry) do
        throwError "the recorded arrow context disagrees with its complete typed value"
      let morphism ← realize h trace s!"the defining map of {what}" morphism
      let context ← CategoryContext.ofNamed entry e
      let some plan ← StructuredProjection.arrow? e context
        | throwError "the recorded arrow lost its complete accepted projection interface"
      CategoryContext.checkMorphism plan.base morphism.value source target
      let morphism ← captureCompleteCallable h trace morphism plan.base none false
      let some (source, target) ← retainedCallableEndpoints? morphism plan.base
        | throwError "the recorded Arrow lost its retained complete map endpoints"
      let template : ActionDataTemplate := .ctor "arrow"
        #[.wire .object source, .wire .object target, .wire .map morphism]
      let (data, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := .arrow entry
        payload := (← combinedRecipePayload e data dependencies)
        categoryContext := some context }
      retainIntrinsicAssembly result .object context template
        #[{ context := plan.base, source, target, callable := morphism }]
  | .literal id literal =>
      let some form := state.form? id.raw
        | throwError "{id.raw} is not a registered literal form"
      match ← Codec.encode literal with
      | .ok json =>
          let wire : Wire := { form, payload := .ordinary e json }
          let categoryId ← match form with
            | .graph entry => pure (some entry.category)
            | .subset _ category => pure (some category)
            | _ => pure none
          let some categoryId := categoryId | return wire
          let some category := state.categories.find? (·.id == categoryId)
            | throwError "the registered map literal lost its declared category"
          let some (source, target) := Language.homEnds? (← inferType e)
            | throwError "the registered map literal lost its complete endpoints"
          let context ← CategoryContext.ofNamed category source
          CategoryContext.checkMorphism context e source target
          let sourceWire ← realizeCallableEndpoint h trace wire source true (some context)
          let targetWire ← realizeCallableEndpoint h trace wire target false (some context)
          retainCallableEndpoints wire sourceWire targetWire context
      | .error message =>
          throwStratum .noImplementation m!"{what} is not sent: the literal {literal} of \
            {id.raw} is not encoded ({message})"
  | .limit id D lift? =>
      realizeLimitWith realizeUnobserved
        (fun h trace input context endpoints publicFrame =>
          captureCompleteCallable h trace input context endpoints publicFrame)
        captureMapRoute
        realizedEdgeData capturedEdgeData extentFragment?
        h trace state what id D lift?
  | .method id route receiver recordedComparisons interpreted =>
      captureRoutedInvocation h trace what e id route receiver recordedComparisons interpreted #[]
  | .methodWithLifts id route lifts receiver recordedComparisons interpreted =>
      captureRoutedInvocation h trace what e id route receiver recordedComparisons interpreted lifts
  | .property id _ _ _ =>
      throwError "the decision {id.raw} is not a value"

end Realize

end CasCatalogue
