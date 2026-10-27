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
public import CasCatalogue.LiftedSubobjectData
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
# The realized reading (`specs/leaf-registration.md`)

A statement's semantic reading elaborates it into its claim (`Language.Claim`): a proposition of
the catalogue's mathematics, and the term it is about. This module decides the claim:

1. **Lean discharge first.** The proposition is decided in Lean, generically
   (`decideEvaluated`): the registered evaluations of the literal forms whose denotations occur
   in it (a literal row's `evaluation`, a `meta` procedure of `lean-categories`, run through the
   one sanctioned runner `Language.runProcedure`, LC-18) rewrite the images of literals under the
   catalogue's operations to literals, and the goal that remains is proved by
   `of_decide_eq_true (Eq.refl true)` (Lean's `mkDecideProof`, on `Decidable` instances alone,
   running no tactic of the kernel's); the proof so formed is checked by Lean's kernel,
   synchronously, within a fixed heartbeat budget; refutation is the same proof of `¬p`. If Lean
   proves it, the statement holds as proved and no leaf is consulted. If Lean refutes it, the
   assertion is refuted and reports a wrong answer. Nothing is decided by evaluation outside the
   kernel.
2. **Otherwise, realize.** The same term is evaluated bottom-up through the operations the
   semantic reading recorded (`CasCatalogue.Trace`): a named object at its parameters is its
   form, encoded by the kernel; a literal (a morphism by its graph) is its form; the receiver of
   a method or property is sent along the route the semantic reading resolved, as far as the
   catalogue's refinement rows take it (CC-TRANSPORT, `transport`); an operation applied to a
   value of a form selects the admitted registration of that operation on that form
   (`CasCatalogue.Admission`), sends the encoded input over the port, and decodes the answer in
   the operation's declared result interface. A registered limit is an operation on its diagram,
   sent in the forms of its objects and arrows. The accepted constructor supplies the complete
   computational field schema for its apex and defining maps. Missing or ill-framed fields are
   malformed; the returned maps and their laws are never promoted to mathematical evidence.
   Projections and later operations retain these actual fields and any owning session. No
   registration is a gap; two are a gap reported as ambiguous; a backend that cannot start is
   unavailable; a rejected answer is malformed.
3. **Comparison.** `assert X = L` holds when the decoded value equals `L`, by the decidable
   equality of the form's type, checked by the kernel the same way. A decision is compared as a
   three-valued answer. Nothing a leaf returned is used as evidence of anything but its own
   answer.

The kernel supplies no `Decidable` instance of its own: which propositions Lean decides is the
catalogue's and Mathlib's. (Equality of morphisms of a concrete category, decided on their
functions, is mathematics; it belongs to `lean-categories`.)
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
structure LiftExecution where
  selections : Array SelectedLift.Plan
  actions : Array Json
  parameters : Array (Array Json)
  sources : Array Json
  bases : Array Json
  outputs : Array (Array Json)
  /-- Each table is relative to its corresponding retained field. Parameter
  tables cover the whole parameter array; output tables cover each output. -/
  actionOwnership : Array DataOwnership.Table := #[]
  parameterOwnership : Array DataOwnership.Table := #[]
  sourceOwnership : Array DataOwnership.Table := #[]
  baseOwnership : Array DataOwnership.Table := #[]
  outputOwnership : Array (Array DataOwnership.Table) := #[]

/-- An accepted change from the fixed semantic endpoint to the representation
used by its actual computational data. Both map descriptors retain their complete
declaration parameters; the comparison itself comes only from the catalogue. -/
structure EndpointPresentation where
  comparison : Expr
  forward : Json
  backward : Json
  forwardOwnership : DataOwnership.Table := #[]
  backwardOwnership : DataOwnership.Table := #[]

def EndpointPresentation.forwardFragment (presentation : EndpointPresentation) : DataOwnership.Data :=
  { json := presentation.forward, ownership := presentation.forwardOwnership }

def EndpointPresentation.backwardFragment (presentation : EndpointPresentation) : DataOwnership.Data :=
  { json := presentation.backward, ownership := presentation.backwardOwnership }

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

/-- The complete output type of an intrinsic assembly is independent of its
children's observation roles. Scalar data do not acquire a category dictionary. -/
inductive IntrinsicResultInterface where
  | object (context : CategoryContext)
  | map (context : CategoryContext)
  | value (expectedType : Expr)

inductive CallableEndpointOrigin where
  | retained
  | reference
  deriving BEq, Inhabited

mutual

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

/-- Only a producer builds this assembly tree. Literal data retain their exact
suppliers; typed leaves retain complete occurrences without expression lookup. -/
inductive ActionDataTemplate where
  | literal (data : DataOwnership.Data)
  | wire (role : ActionDataRole) (input : Wire)
  | ctor (tag : String) (children : Array ActionDataTemplate)
  | array (children : Array ActionDataTemplate)
  /-- Fixed descriptor context retains all typed slots without demanding them. -/
  | retained (child : ActionDataTemplate)
  /-- The existing point-data interface selects this representation conversion.
  Its original typed point, rather than returned bytes, determines the role. -/
  | pointCallable (context : CategoryContext) (source target : Expr) (point : Wire)

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
  context : CategoryContext
  parent : Wire
  construction : StructuredProjection.ConstructionPlan
  plan : Option StructuredResult.DataPlan := none
  port : Option StructuredResult.DataPort
  inputOccurrences : Array (Nat × Option Bool) := #[]
  endpoint : Option Bool := none
  leg : Option Expr := none
  legData : Option DataOwnership.Data := none
  endpoints : Option (Wire × Wire) := none

/-- Result protocols share occurrence identity and completion reuse. Protocol
kind does not assert that any computational data has been received. -/
inductive CapturedInvocationInterface where
  | callable (selected : SelectedCallableInvocation)
  | structured (selected : SelectedStructuredInvocation)
  | projection (selected : SelectedStructuredProjection)

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

end

initialize nextInvocationOccurrence : IO.Ref Nat ← IO.mkRef 0

/-- A harness-owned immutable producer occurrence and its optional completed
result. Equal formal terms or bytes never select a different occurrence. -/
structure InvocationExecution where
  input : Wire
  captured : CapturedInvocation
  result : Option Wire := none

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
      left.actionOwnership == right.actionOwnership && left.parameterOwnership == right.parameterOwnership &&
      left.sourceOwnership == right.sourceOwnership && left.baseOwnership == right.baseOwnership &&
      left.outputOwnership == right.outputOwnership
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
  serviceHandles := snapshot.serviceHandles, pointDataInterface := snapshot.pointDataInterface
  productComponents := snapshot.productComponents, actionRecipe := snapshot.actionRecipe
  intrinsicAssembly := snapshot.intrinsicAssembly, capturedInvocation := snapshot.capturedInvocation,
  callableEndpoints := snapshot.callableEndpoints
  pointOrigin := snapshot.pointOrigin
  morphismFramed := snapshot.morphismFramed, morphismFraming := snapshot.morphismFraming }

def CapturedInvocationInterface.formal : CapturedInvocationInterface → Expr
  | .callable selected => selected.formal
  | .structured selected => selected.formal
  | .projection selected => selected.formal

def CapturedInvocationInterface.fragment : CapturedInvocationInterface → DataOwnership.Data
  | .callable selected => selected.fragment
  | .structured selected => selected.fragment
  | .projection selected => selected.fragment

def CapturedInvocationInterface.context : CapturedInvocationInterface → CategoryContext
  | .callable selected => selected.context
  | .structured selected => selected.context
  | .projection selected => selected.context

def CapturedInvocationInterface.reanchor (selected : CapturedInvocationInterface)
    (formal : Expr) : CapturedInvocationInterface :=
  match selected with
  | .callable selected => .callable { selected with formal }
  | .structured selected => .structured { selected with formal }
  | .projection selected => .projection { selected with formal }

mutual

/-- Computational occurrence identity never compares carriers or mathematical
values for equality. Distinct actual packets and live owners remain distinct. -/
partial def sameActionOperand (left right : Wire) : Bool :=
  left.value == right.value && left.json == right.json && left.ownership == right.ownership &&
    left.pointDataInterface == right.pointDataInterface &&
    left.objectIso == right.objectIso &&
    left.endpointPresentation.map (·.comparison) == right.endpointPresentation.map (·.comparison) &&
    left.endpointPresentation.map (·.forward) == right.endpointPresentation.map (·.forward) &&
    left.endpointPresentation.map (·.backward) == right.endpointPresentation.map (·.backward) &&
    left.endpointPresentation.map (·.forwardOwnership) ==
      right.endpointPresentation.map (·.forwardOwnership) &&
    left.endpointPresentation.map (·.backwardOwnership) ==
      right.endpointPresentation.map (·.backwardOwnership) &&
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

partial def sameMorphismFraming (left right : Option MorphismFraming) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
    sameCompleteWireContext left.input right.input &&
      sameCompleteWireContext left.source right.source &&
      sameCompleteWireContext left.target right.target &&
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
  | .retained left, .retained right => sameActionTemplate left right
  | .pointCallable a s t x, .pointCallable b u v y =>
      a.expression.syntacticEq b.expression && a.bundle == b.bundle &&
        s == u && t == v && sameCompleteWireContext x y
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
      a.formal == b.formal && a.data == b.data && sameProductComponents a.dependencies b.dependencies) &&
    sameCompleteWireContext left.original right.original &&
    sameCompleteWireContext left.owner right.owner &&
    sameCompleteWireContext left.argument right.argument &&
    sameCompleteWireContext left.argumentDomain right.argumentDomain &&
    left.argumentData == right.argumentData &&
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
Operation-use restrictions are checked separately; dependency handle allocation
does not choose a mathematical context. -/
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
    (context : Option CategoryContext := none) : TermElabM Wire := do
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
  let mut data := input.fragment
  if let some presentation := source.endpointPresentation then
    let type ← whnfR (← inferType presentation.comparison)
    unless type.isAppOf ``CategoryTheory.Iso &&
        (← withTransparency .all <| isDefEq type.getAppArgs[type.getAppArgs.size - 2]!
          source.value) do
      throwError "the domain comparison starts at a different complete object"
    actual ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison], actual]
    data ← scopedNode "compose" #[presentation.backwardFragment, data]
  if let some presentation := target.endpointPresentation then
    let type ← whnfR (← inferType presentation.comparison)
    unless type.isAppOf ``CategoryTheory.Iso &&
        (← withTransparency .all <| isDefEq type.getAppArgs[type.getAppArgs.size - 2]!
          target.value) do
      throwError "the codomain comparison starts at a different complete object"
    actual ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[actual, ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]]
    data ← scopedNode "compose" #[data, presentation.forwardFragment]
  discard <| StructuredResult.checkReconstruction actual
  -- A data-preserving frame over a completed callable is itself complete.
  -- New comparison maps keep their explicit current framing recipe: their
  -- mathematical comparison alone is not computational completion provenance.
  let completed := (input.actualData || input.callableObserved) &&
    source.endpointPresentation.isNone && target.endpointPresentation.isNone
  let result := { input with
    morphismFramed := true
    morphismFraming := some { input, source, target, context }
    -- The exact input keeps its own pending producer. This framing layer is
    -- the current owner even when an identity frame preserves the same bytes.
    intrinsicAssembly := none, capturedInvocation := none, actionRecipe := none
    objectObserved := false, callableObserved := completed
    categoryContext := context
    payload := (← if completed then scopedPayload input.value data
      else combinedRecipePayload input.value data #[input, source, target]) }
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
  | .retained child => renderActionDataWith (fun _ wire => pure wire) child
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

def renderCapturedActionData (template : ActionDataTemplate) :
    TermElabM (DataOwnership.Data × Array Wire) :=
  renderActionDataWith (fun _ wire => pure wire) template

partial def actionTemplateInputs (template : ActionDataTemplate) : Array Wire :=
  match template with
  | .literal _ => #[]
  | .wire _ input => #[input]
  | .pointCallable _ _ _ input => #[input]
  | .retained child => actionTemplateInputs child
  | .ctor _ children | .array children => children.flatMap actionTemplateInputs

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
  | .retained child => return .retained child
  | .pointCallable context source target point =>
      return .pointCallable context source target (← observe .map point)

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
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context
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

def forwardRetainedValue (source : Wire) (formal : Expr) : TermElabM Wire := do
  if source.value == formal then return source
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType source.value) (← inferType formal) <&&>
        isDefEq source.value formal) do
    throwError "the retained data alias changed its complete mathematical value"
  let mut result := { source with
    capturedInvocation := forwardCapturedInvocation source formal, payload := forwardPayload source formal source.json }
  if let some framing := source.morphismFraming then
    -- The old frame belongs to its exact original input. Keep that whole
    -- occurrence as a typed child rather than rewriting its historical anchor
    -- or weakening the replay check to equality of mathematical values.
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context
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
    result := { result with morphismFraming := none, actionRecipe := none,
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

/-- Historical producer metadata cannot describe a new current value. -/
def retainedCapturedInvocation? (wire : Wire) : TermElabM (Option CapturedInvocation) := do
  let some captured := wire.capturedInvocation | return none
  let selected := captured.interface
  unless wire.value == selected.formal && wire.fragment == selected.fragment do return none
  let some context := wire.categoryContext | return none
  unless context.expression.syntacticEq selected.context.expression do return none
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq context.bundle selected.context.bundle) do return none
  return some captured

/-- Capture allocates private occurrence identity only. It neither chooses an
implementation nor creates an actual packet or a dispatch receipt. -/
def retainCapturedInvocation (h : Harness) (wire : Wire)
    (interface : CapturedInvocationInterface) : TermElabM Wire := do
  unless wire.value == interface.formal && wire.fragment == interface.fragment do
    throwError "the captured invocation changed its original selected anchor"
  discard <| framingContext (some interface.context) wire.categoryContext
  unless wire.capturedInvocation.isNone do
    throwError "a fresh invocation must retain its previous producer as an explicit operand"
  let occurrence ← nextInvocationOccurrence.modifyGet fun next => (next, next + 1)
  let captured : CapturedInvocation := { occurrence, interface }
  h.invocations.modify (·.push { input := wire, captured })
  return { wire with capturedInvocation := some captured }

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

/-- Reuse a completed action only on the same selected functor and actual
operands. Map keys include both actual image endpoints, as well as the source map. -/
def retainedActionResult? (h : Harness) (operation : String) (action : Expr)
    (input : Wire) (parameters : Array Json) (dependencies images : Array Wire)
    (parameterOwnership : DataOwnership.Table := #[]) : TermElabM (Option Wire) := do
  let result := ((← h.actions.get).find? fun record =>
    record.operation == operation && record.action == action &&
      sameActionOperand record.input input && record.parameters == parameters &&
      record.parameterOwnership == parameterOwnership &&
      sameActionOperands record.parameterInputs dependencies &&
      sameActionOperands record.imageEndpoints images).map (·.result)
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
  let mut selected := value.consumeMData
  while selected.isAppOfArity ``id 2 do selected := selected.appArg!.consumeMData
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
    withoutModifyingState do
  let value ← instantiateMVars value
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return none
  let mut literal := value.consumeMData
  while literal.isAppOfArity ``id 2 ||
      (asFunctor && literal.isAppOf ``CategoryTheory.Cat.Hom.toFunctor) do
    literal := literal.appArg!.consumeMData
  let application ← if literal.getAppFn.constName? == some declaration then pure literal
    else instantiateFresh declaration
  let compared ← if asFunctor then Semantic.asFunctor application else pure application
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType compared) (← inferType value) <&&> isDefEq compared value) do
    CategoryContext.exposeStructureParameters application
  unless ← withTransparency .all <|
      isDefEq (← inferType compared) (← inferType value) <&&> isDefEq compared value do
    return none
  let application ← instantiateMVars application
  let compared ← instantiateMVars compared
  unless FunctorActionData.closedParameter application && (← isTypeCorrect application) do
    return none
  let infos ← forallTelescopeReducing (← inferType application.getAppFn) fun fields _ =>
    fields.mapM (·.fvarId!.getBinderInfo)
  unless application.getAppNumArgs == infos.size do return none
  unless ← Decide.kernelAccepts (← mkEq compared value) (← mkEqRefl compared) do
    throwError "the complete declaration presentation failed its original kernel check"
  return some (application, (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none)

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
  let mut selected := value.consumeMData
  while selected.isAppOfArity ``id 2 do selected := selected.appArg!.consumeMData
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
  let literal := receiver.consumeMData
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
  let mut literal := functor.consumeMData
  while literal.isAppOfArity ``id 2 || literal.isAppOf ``CategoryTheory.Cat.Hom.toFunctor do
    literal := literal.appArg!.consumeMData
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
      let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[application]
      let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt) #[cone]
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
  unless FunctorActionData.closedParameter action && (← isTypeCorrect action) do
    throwError "the executable edge requires its complete selected action"
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
    (endpoints : Option (Wire × Wire) := none) : TermElabM Wire := do
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
  return { output with capturedInvocation := none, actionRecipe := some {
    morphism, owner, application, original, descriptor, source, target,
    formal := output.value, fragment := output.fragment, endpoints } }

def retainActionInput (morphism : Bool) (edge : EdgeRef) (application : Expr)
    (original output : Wire) (descriptor : ActionDataTemplate)
    (endpoints : Option (Wire × Wire) := none) : TermElabM Wire :=
  retainRegisteredActionInput (.edge edge) morphism application original output descriptor endpoints

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
  retainRegisteredActionInput owner false action original output descriptor

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
  return some (← retainRegisteredActionInput recipe.owner false recipe.application
    endpoint output recipe.descriptor)

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
    if !completed then
      if let some descriptor := captured then
        result ← retainActionInput false step U original result descriptor
    expression := edge.target
  return result

partial def transport (trace : Trace) (w : Wire) (route : Array EdgeRef)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none) : TermElabM Wire := do
  if w.form.namedCategory?.isNone then return ← transportImage trace w route none encoder? capture?
  if w.owner?.isSome || (match w.payload with | .computed .. | .construction .. => true | _ => false) then
    return ← transportImage trace w route none encoder? capture?
  if w.objectIso.isSome then return ← transportImage trace w route none encoder? capture?
  let state ← registryState
  if let .arrow category := w.form then
    -- Runtime actions preserve every original endpoint and selected parameter;
    -- the legacy named-arrow optimization is only a metadata presentation path.
    if encoder?.isSome || capture?.isSome then return ← transportImage trace w route none encoder? capture?
    unless route.all (fun step => match step with
      | .constructMap constructor (.functor _) =>
          (state.constructors.find? (·.id == constructor)).any
            (·.semantics == `CasCatalogue.Constructors.arrow)
      | _ => false) do
      return ← transportImage trace w route none encoder? capture?
    let some (.arrow _ hom source target) ← (trace.node? w.value : IO _)
      | return ← transportImage trace w route none encoder? capture?
    let .ok wireArgs := (w.json.getObjVal? "args").bind (·.getArr?)
      | throwError "the recorded arrow has no complete wire fields"
    unless wireArgs.size == 3 do throwError "the recorded arrow has incomplete wire fields"
    let mut result := w
    let mut currentSource := source
    let mut currentTarget := target
    let mut currentHom := hom
    for step in route do
      let .ok wireArgs := (result.json.getObjVal? "args").bind (·.getArr?)
        | throwError "the transported arrow lost its complete wire fields"
      let .constructMap constructor (.functor id) := step
        | throwStratum .noImplementation m!"the arrow route {step.label} has no registered wire action"
      unless (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        throwError "the recorded arrow route uses a different constructor"
      let some functor := state.functor? id | unreachable!
      let some targetCategory := state.categories.find? (·.expression.syntacticEq
          (.construct constructor #[.category functor.target]))
        | throwError "the target arrow category has no named declaration"
      let endpoint := fun value json => do
        let some (.object id _) ← (trace.node? value : IO _)
          | throwStratum .noImplementation m!"an arrow endpoint has no registered object presentation"
        let some entry := state.objects.find? (·.id == id) | unreachable!
        transport trace { form := .object entry, payload := .ordinary (value) (json) } #[.functor functor.id]
      let sourceWire ← endpoint currentSource wireArgs[0]!
      let targetWire ← endpoint currentTarget wireArgs[1]!
      let U ← Semantic.edgeFunctor state (.functor id)
      let sourceImage ← Semantic.objOf U currentSource
      let targetImage ← Semantic.objOf U currentTarget
      currentHom ← Semantic.mapOf U currentHom
      currentSource := sourceWire.value
      currentTarget := targetWire.value
      let mut mapped := Json.mkObj [("ctor", "map"), ("args", Json.arr #[
        (← edgeDescriptor trace (.functor id) U), wireArgs[2]!])]
      let identificationMap := fun wire image inverse => do
        let some iso := wire.presentationIsos.back?
          | throwStratum .noImplementation m!"the arrow endpoint lacks an accepted presentation identification"
        let identificationArrow ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[iso]
        let endpoints ← mkAppM ``Quiver.Hom #[image, wire.value]
        let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
        unless ← isDefEq (← inferType hom) endpoints do
          throwError "the retained endpoint identification has incompatible endpoints"
        match ← Codec.encode identificationArrow with
        | .ok json => pure (identificationArrow, json)
        | .error message => throwStratum .noImplementation m!"the accepted endpoint identification has no data encoding: {message}"
      unless ← isDefEq sourceImage sourceWire.value do
        let (identificationArrow, json) ← identificationMap sourceWire sourceImage true
        currentHom ← mkAppM ``CategoryTheory.CategoryStruct.comp #[identificationArrow, currentHom]
        mapped := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[json, mapped])]
      unless ← isDefEq targetImage targetWire.value do
        let (identificationArrow, json) ← identificationMap targetWire targetImage false
        currentHom ← mkAppM ``CategoryTheory.CategoryStruct.comp #[currentHom, identificationArrow]
        mapped := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[mapped, json])]
      let value ← mkAppM ``CategoryTheory.Arrow.mk #[currentHom]
      Trace.record (some trace) value (.arrow targetCategory.id currentHom currentSource currentTarget)
      result := { result with form := .arrow targetCategory, presentationIsos := sourceWire.presentationIsos ++ targetWire.presentationIsos, payload := .ordinary (value) (Json.mkObj [("ctor", "arrow"), ("args", Json.arr #[sourceWire.json,targetWire.json,mapped])]) }
    return result
  let .object entry := w.form | transportImage trace w route none encoder? capture?
  let some (.object _ params) ← (trace.node? w.value : IO _)
    | return ← transportImage trace w route none encoder? capture?
  let mut current := entry
  let mut remaining := route
  let mut value := w.value
  let mut identifications := w.presentationIsos
  for _ in [:state.objects.size + 1] do
    let some refinement := current.refines | break
    unless !refinement.route.isEmpty &&
        remaining.extract 0 refinement.route.size == refinement.route do break
    let some target := state.objects.find? (·.id == refinement.base)
      | throwError "the accepted refinement has no target object"
    let next ← objectAt trace target params
    let identification ← elabTermAndSynthesize
      (← `($(mkCIdent refinement.identification) $(← params.mapM exprToSyntax)*)) none
    let image ← Semantic.objOf (← Semantic.routeFunctor state refinement.route) value
    let expected ← mkAppM ``CategoryTheory.Iso #[image, next]
    unless ← isDefEq (← inferType identification) expected do
      throwError "the accepted presentation identification has incompatible endpoints"
    let identification ← instantiateMVars identification
    if identification.hasMVar || identification.hasLevelMVar then
      throwError "the accepted presentation identification is not closed"
    identifications := identifications.push identification
    current := target
    value := next
    remaining := remaining.extract refinement.route.size remaining.size
  if current.id == entry.id then return ← transportImage trace w remaining none encoder? capture?
  let context : Option CategoryContext ← match w.categoryContext with
    | none => pure none
    | some source => do
        let some expression := state.formExpression? w.form
          | throwError "the named presentation source lost its accepted category"
        unless source.expression.syntacticEq expression do
          throwError "the named presentation source has a different retained category"
        CategoryContext.checkObject source w.value
        let some category := state.categories.find? (·.id == current.category)
          | throwError "the named presentation target category is not registered"
        pure (some (← CategoryContext.ofNamed category value))
  let args := (w.json.getObjVal? "args").toOption.getD (Json.arr #[])
  let refined := { w with
    form := .object current, presentationIsos := identifications,
    categoryContext := context, actionRecipe := none,
    payload := .ordinary value (Json.mkObj [("ctor", current.id.raw), ("args", args)]) }
  transportImage trace refined remaining none encoder? capture?

/-- Consume exact checked proof-refinement and named-presentation prefixes while
retaining the complete residual route. A later category-wide operation can then
apply every residual action without undoing the registered presentation. -/
partial def canonicalOperationInput (trace : Trace) (wire : Wire) (route : Array EdgeRef)
    (encoder? : Option ScopedActionEncoder := none)
    (capture? : Option CapturedActionEncoder := none) :
    TermElabM (Wire × Array EdgeRef) := do
  let state ← registryState
  match wire.form with
  | .contextual .. => return (← transportImage trace wire route none encoder? capture?, #[])
  | .proofRefinement _ classifier _ =>
      if route[0]? == some (.classifierForget classifier) then
        let action ← Semantic.edgeFunctor state (.classifierForget classifier)
        let original ← proofRefinementBase trace wire action
        return ← canonicalOperationInput trace original (route.extract 1 route.size) encoder? capture?
      return (wire, route)
  | .object entry =>
      let (_, remaining) := state.transport entry route
      return (← transport trace wire (route.extract 0 (route.size - remaining.size)) encoder? capture?, remaining)
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
      Trace.record (some trace) value (.object entry.id params)
      return .ok (entry, value)

/-- Recover ordered application arguments beneath elaborator type hints. -/
def actualApplicationArguments (application : Expr) : Array Expr := Id.run do
  let mut application := application.consumeMData
  while application.isAppOfArity ``id 2 do
    application := application.appArg!.consumeMData
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
          Semantic.namedMorphism entry value (some trace)
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
          Semantic.namedMorphism entry value (some trace)
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
          if let some (graph, _) := fields[0]? then
            Trace.record (some trace) hom (.literal form.id graph)
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
      Trace.record (some trace) value (.literal form.id literal)
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
      none
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
    let some (.methodWithLifts id route lifts receiver _) ← trace.node? fixed
      | return .error "the lifted child has no independently retained prescribed operation"
    let some method := state.methods.find? (·.id == id)
      | return .error "the lifted child operation is not registered"
    let some entry := state.functor? method.functor
      | return .error "the lifted child operation has no registered action"
    let mut transported := receiver
    for step in route do
      transported ← Semantic.objOf (← Semantic.edgeFunctor state step) transported
    let (base, _) ← Semantic.applyRegisteredFunctor entry
      (← methodArgument method transported) #[] (some trace)
    return ← decodeLiftedAt trace category (← inferType fixed)
      { fixedSource := receiver, prescribed := lifts, fixedBase := base } json
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
    execution.sourceOwnership.isEmpty && execution.baseOwnership.isEmpty && execution.outputOwnership.isEmpty
  let scope := fun json => match legacyOwner with
    | some owner => DataOwnership.capture json owner
    | none => #[]
  let execution := if absent then { execution with
      actionOwnership := execution.actions.map scope
      parameterOwnership := execution.parameters.map (fun data => scope (Json.arr data))
      sourceOwnership := execution.sources.map scope
      baseOwnership := execution.bases.map scope
      outputOwnership := execution.outputs.map (fun fields => fields.map scope) }
    else execution
  let count := execution.selections.size
  unless count > 0 && execution.actions.size == count && execution.parameters.size == count &&
      execution.sources.size == count && execution.bases.size == count && execution.outputs.size == count &&
      execution.actionOwnership.size == count && execution.parameterOwnership.size == count &&
      execution.sourceOwnership.size == count && execution.baseOwnership.size == count &&
      execution.outputOwnership.size == count && execution.outputs.all (·.size == 4) &&
      execution.outputOwnership.all (·.size == 4) do
    throwError "the selected lift cache omits a required component output or exact scope"
  for index in [:count] do
    for (json, ownership) in #[
        (execution.actions[index]!, execution.actionOwnership[index]!),
        (Json.arr execution.parameters[index]!, execution.parameterOwnership[index]!),
        (execution.sources[index]!, execution.sourceOwnership[index]!),
        (execution.bases[index]!, execution.baseOwnership[index]!)] do
      discard <| checkedFragment (DataOwnership.checkCoverage json ownership)
    for (json, ownership) in execution.outputs[index]!.zip execution.outputOwnership[index]! do
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

/-- Existing lift request/step framing, with every input positioned explicitly. -/
def liftStageData (tag id : String) (parameters : DataOwnership.Data)
    (action source base : DataOwnership.Data) (outputs : Array DataOwnership.Data) :
    TermElabM DataOwnership.Data :=
  checkedFragment (DataOwnership.Data.object [
    ("ctor", { json := toJson tag }), ("parameters", parameters),
    ("args", DataOwnership.Data.array #[{ json := toJson id }, action, source, base,
      DataOwnership.Data.array outputs])])

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
    let some (source, target) := Language.homEnds? (← inferType formal)
      | throwError "the retained lift operand lost its complete Hom type"
    CategoryContext.checkMorphism context formal source target
  else CategoryContext.checkObject context formal
  return {
    form := contextualForm (← registryState) context origin morphism
    payload := (← scopedPayload formal data observed), categoryContext := some context
    objectObserved := observed && !morphism, callableObserved := observed && morphism }

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

/-- Execute every selected public lift field on preceding actual data, in reverse route order.
The formal plan is fixed before dispatch; no reply supplies a semantic term or lift law.
Action data and their owners are fixed by the supplied encoder before any field dispatch. -/
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
    let mut outputs : Array DataOwnership.Data := #[]
    let mut outputWires : Array Wire := #[]
    for field in LiftField.all do
      let request ← liftStageData "liftInput" row.id.raw parameterData
        actions[index]! sources[index]! currentBase outputs
      let input : Wire := {
        form, payload := (← recipePayload component.receiver request)
        serviceHandles := (← retainLiftOperands h
          (#[source, base, sourceView, baseView] ++ parameters[index]!.2 ++
            (actionDependencies.extract 0 (index + 1)).flatMap id ++ outputWires)) }
      let operation := row.fieldAddress field
      let reply ← sendData h operation input
      outputs := outputs.push reply.data
      match ← LiftedSubobjectData.validatePrefix component actions[index]!.json
          sources[index]!.json currentBase.json (outputs.map (·.json)) with
      | .error message => malformed reply.backend operation reply.data.json message
      | .ok () => pure ()
      let position := outputWires.size
      let context ← SelectedLift.context component.selection (position >= 2)
      let output ← liftOperand component.ports[position]! context form reply.data (position != 0) true
      outputWires := outputWires.push { output with serviceHandles := input.serviceHandles }
    steps := steps.set! index (← liftStageData "liftStep" row.id.raw parameterData
      actions[index]! sources[index]! currentBase outputs)
    let .ok next := LiftedSubobjectData.nextBase sources[index]!.json (outputs.map (·.json))
      | throwError "the completed lift omitted its actual next object or inclusion"
    currentBase ← retagLiftMap "subobject" outputs[1]!
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

/-- Extract an actual apex with its independently checked base-category image.
Success is explicit: an unprojected complete packet is never a creating image.
No actual object is identified with the formal universal construction. -/
def computationalApexImage? (_trace : Trace) (input : Wire) :
    TermElabM (Option Wire) := do
  let state ← registryState
  if let some (receiver, _) := input.constructionInputs then
    unless ← withoutModifyingState <| withTransparency .all <|
        isDefEq receiver input.value do return none
  let objects := input.constructionInputs.map Prod.snd |>.getD #[]
  let mut answer := input.json
  let mut answerPath : DataOwnership.Path := #[]
  let mut apexCategory := input.form.category
  let mut apexShape : Option String := none
  let mut fixed := input.value
  -- Complete construction wrappers retain their actual returned apex. An
  -- unexecuted functor action must remain intact because it can change that apex.
  while true do
    let tag := (answer.getObjValAs? String "ctor").toOption
    let .ok args := (answer.getObjVal? "args").bind (·.getArr?) | break
    if tag == some "functorAction" then
      -- An arbitrary accepted action can change the computational object. Its
      -- descriptor must travel to the leaf; a named inner apex is no substitute.
      return none
    else if tag == some "constructionApex" then
      let some identifier := args[0]? | return none
      let .ok name := identifier.getStr? | return none
      let some row := state.limits.find? (·.id.raw == name) | return none
      apexCategory := row.category
      apexShape := some row.shape
      let some child := args[2]? | break
      answer := child
      answerPath := answerPath ++ #[.field "args", .index 2]
    else if tag == some "createdCone" then
      let some identifier := args[0]? | return none
      let .ok name := identifier.getStr? | return none
      let some lift := state.lifts.find? (·.id.raw == name) | return none
      let some shape := apexShape | return none
      unless lift.kind == .createsLimits shape do return none
      let some edge := state.structuralEdge? lift.edge | return none
      let some category := state.categories.find? (·.id == apexCategory) | return none
      unless edge.target.syntacticEq category.expression do return none
      let action ← Semantic.asFunctor (← Semantic.edgeFunctor state lift.edge)
      let actionType ← whnfR (← inferType action)
      unless actionType.isAppOf ``CategoryTheory.Functor do return none
      unless ← isDefEq (← inferType fixed) actionType.getAppArgs[0]! do return none
      fixed ← Semantic.objOf action fixed
      let some child := args[2]? | break
      answer := child
      answerPath := answerPath ++ #[.field "args", .index 2]
    else break
  unless ((answer.getObjValAs? String "ctor").toOption == some "cone" ||
      (answer.getObjValAs? String "ctor").toOption == some "cocone") do
    return none
  let .ok args := (answer.getObjVal? "args").bind (·.getArr?) | return none
  let some apexJson := args[0]? | return none
  -- Only the exact inner object descriptor selects a registered form. The
  -- full finiteData envelope remains the computational receiver payload.
  let mut descriptor := apexJson
  if (apexJson.getObjValAs? String "ctor").toOption == some "finiteData" then
    let .ok (_, fields) := ComputationalData.envelope apexJson | return none
    unless fields.size == 2 do return none
    descriptor := fields[0]!
  let some category := state.categories.find? (·.id == apexCategory) | return none
  let carrier ← categoryCarrierInstance category
  -- Preserve any independently fixed category parameters, without identifying
  -- the returned object with the formal universal apex. A created cone can
  -- retain a source-side formal object while its packet is in the base category.
  unless ← withoutModifyingState (isDefEq (← inferType fixed) carrier) do return none
  discard <| isDefEq (← inferType fixed) carrier
  let carrier ← instantiateMVars carrier
  if carrier.hasMVar || carrier.hasLevelMVar then return none
  if let .error _ ← ComputationalData.validatePort fixed carrier apexJson objects then
    return none
  let named := state.objects.find? fun entry =>
    (descriptor.getObjValAs? String "ctor").toOption == some entry.id.raw
  if let some entry := named then
    unless entry.category == apexCategory do return none
  let form := named.map Form.object |>.getD (.diagrams category)
  -- The selected apex retains only the suppliers at its exact packet position.
  -- Other defining maps remain in the original complete construction.
  let apex ← checkedFragment (input.fragment.project
    (answerPath ++ #[.field "args", .index 0]))
  let payload ← scopedPayload fixed apex
  return some { input with form, payload }

/-- Project only the computational receiver's actual fields. Its original
formal occurrence remains intact even when a created packet is represented in
a base category. Applying the creating functor uses the checked image above. -/
def computationalApexReceiver (trace : Trace) (input : Wire) : TermElabM Wire := do
  let some image ← computationalApexImage? trace input | return input
  return { image with payload := (← scopedPayload input.value image.fragment) }

/-- The no-dispatch object cases of an accepted edge. Both actual execution and
prospective ownership inspection use the same retained creation and checked
record projection. Typed inputs affect framing only, never the selected edge. -/
def intrinsicObjectEdgeData? (trace : Trace) (edge : EdgeRef) (action : Expr)
    (original : Wire) (imageValue : Expr) (descriptor : DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Option DataOwnership.Data) := do
  let state ← registryState
  let some source := state.selectedEdgeSource? edge
    | throwError "the intrinsic object action lost its registered source"
  if let .construction result _ := original.payload then
    if let .created liftId _ _ := result.packet then
      let some creation := state.lifts.find? (·.id.raw == liftId)
        | throwError "the completed construction lost its registered creation"
      if creation.edge == edge then
        let selected ← Semantic.asFunctor (← Semantic.edgeFunctor state creation.edge)
        if ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType action) (← inferType selected) <&&> isDefEq action selected) then
          if let some image ← computationalApexImage? trace original then
            unless ← withoutModifyingState (withTransparency .all <|
                isDefEq (← inferType image.value) (← inferType imageValue) <&&>
                  isDefEq image.value imageValue) do
              throwError "the retained creation image changed its complete selected target"
            return some image.fragment
  if let some (.structural projected) ← projectObjectFragmentWithOrigin trace source edge action
      original.value original.fragment (some descriptor) true objects then
    return some projected
  return none

/-- The power object, ambient set and subset of `e` when `e` is the extent of a subset, the
set `po.extent X A` that `Language.asObject` forms. -/
def extentOf? (state : RegistryState) (e : Expr) :
    TermElabM (Option (PowerObjectEntry × Expr × Expr)) := do
  let e := e.consumeMData
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
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context
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
  dependencies : Array Wire

structure PreparedOperationArgument where
  data : DataOwnership.Data
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
  for component in wire.productComponents do
    result := result ++ (← operationPresentationOperandClosure retained component active)
  if let some recipe := wire.actionRecipe then
    for component in #[recipe.original] ++ actionTemplateInputs recipe.descriptor ++
        (recipe.endpoints.toArray.flatMap fun (source, target) => #[source, target]) do
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

/-- An endpoint's actual validation view comes only from its retained comparison.
Other selected parameters keep their original full values. Repeated descriptor
keys must have the same complete source context before they can share a view. -/
def operationPresentationObjects (inputs : Array Wire)
    (views : Array (Wire × Expr) := #[]) : TermElabM ComputationalData.InterfaceObjects := do
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

/-- Original callable recipes and actual graph packets use their respective
existing validators. In particular, a formal finite carrier supplies no keys. -/
def validateOperationPresentationMap (formal : Expr) (source target data : DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects) : TermElabM Unit := do
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
    ComputationalData.validateEndpointPort formal source.json target.json data.json objects
  else do
    ComputationalData.validateCallableAt objects (← inferType formal) data.json
  if let .error message := checked then
    throwStratum .malformed m!"the operation comparison has incompatible complete framing: {message}"

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
    actual ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison], actual]
  if let some presentation := target.endpointPresentation then
    let (original, selected) ← operationComparisonEnds context presentation.comparison
    unless ← withoutModifyingState (withTransparency .all <| isDefEq original target.value) do
      throwError "the original point's target comparison changed its complete selected source"
    actualTarget := selected
    actual ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[actual, ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]]
  discard <| StructuredResult.checkReconstruction actual
  CategoryContext.checkMorphism context actual actualSource actualTarget
  return (actual, actualSource, actualTarget)

structure OperationProductLegs where
  presentation : Expr
  first : Expr
  second : Expr
  firstData : DataOwnership.Data
  secondData : DataOwnership.Data

/-- The existing registered product cone supplies both projections and their
exact diagram indices. Forward and backward uses call this on different fixed
endpoint pairs, never reuse one side's descriptor for the other. -/
def operationProductLegs (context : CategoryContext) (first second : Expr)
    (firstData secondData : DataOwnership.Data) : TermElabM OperationProductLegs := do
  let row ← operationProductRow
  let (diagram, presentation) ← operationProductCone context row first second
  let some constructor := diagram.getAppFn.constName?
    | throwError "the selected product diagram lost its registered declaration"
  let diagramData ← scopedNode (Codec.label constructor) #[firstData, secondData]
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let expected ← mkAppM ``Prod #[first, second]
  let maps ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
  let mut values := #[]
  let mut data := #[]
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
  return {
    presentation
    first := values[0]!
    second := values[1]!
    firstData := data[0]!
    secondData := data[1]! }

structure OperationComponentPresentation where
  comparison : Expr
  actual : Expr
  semanticData : DataOwnership.Data
  forward : DataOwnership.Data
  backward : DataOwnership.Data
  forwardValue : Expr
  backwardValue : Expr
  inputs : Array Wire
  objects : ComputationalData.InterfaceObjects

/-- Preserve the original selected component and its actual packet. The
semantic-side descriptor is projected only from its complete retained forward
comparison, with formal-name recovery disabled. -/
def operationComponentPresentation (context : CategoryContext) (wire : Wire)
    (inputs : Array Wire) (views : Array (Wire × Expr)) : TermElabM OperationComponentPresentation := do
  CategoryContext.checkObject context wire.value
  discard <| framingContext (some context) wire.categoryContext
  let some presentation := wire.endpointPresentation | do
    let comparison ← mkAppOptM ``CategoryTheory.Iso.refl
      #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
        some wire.value]
    let value ← identityAtContext context wire.value
    let data ← scopedNode "identity" #[wire.fragment, wire.fragment]
    let objects ← operationPresentationObjects inputs (views.push (wire, wire.value))
    return {
      comparison
      actual := wire.value
      semanticData := wire.fragment
      forward := data
      backward := data
      forwardValue := value
      backwardValue := value
      inputs
      objects }
  let (source, actual) ← operationComparisonEnds context presentation.comparison
  unless ← withoutModifyingState (withTransparency .all <| isDefEq source wire.value) do
    throwError "the component presentation starts at a different complete selected object"
  let forwardValue ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]
  let backwardValue ← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison]
  let semanticData ← checkedFragment (← ComputationalData.interfaceEndpointData #[]
    forwardValue presentation.forwardFragment true false)
  let objects ← operationPresentationObjects inputs (views.push (wire, actual))
  let objects ← operationInterfaceBinding objects semanticData wire.value
  validateOperationPresentationMap forwardValue semanticData wire.fragment presentation.forwardFragment objects
  validateOperationPresentationMap backwardValue wire.fragment semanticData presentation.backwardFragment objects
  return {
    comparison := presentation.comparison
    actual
    semanticData
    forward := presentation.forwardFragment
    backward := presentation.backwardFragment
    forwardValue
    backwardValue
    inputs
    objects }

/-- Build current comparisons only for the exact producer-recorded product.
The recursive child selections remain unchanged; derived current maps are kept
separately from them and from historical named-refinement comparisons. -/
def operationProductPresentation (h : Harness) (context : CategoryContext)
    (wire : Wire) (children : Array Wire) (views : Array (Wire × Expr))
    (parameters : Array Wire := #[]) (parameterHandles : Array Nat := #[]) : TermElabM Wire := do
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
  let firstAction ← operationComponentPresentation context first inputs views
  let secondAction ← operationComponentPresentation context second inputs views
  let comparison ← operationProductIso context firstAction.comparison secondAction.comparison
  let (semantic, actual) ← operationComparisonEnds context comparison
  unless ← withoutModifyingState (withTransparency .all <| isDefEq semantic wire.value) do
    throwError "the product action starts at a different complete original product"
  let sourceData ← scopedNode "objectProduct" #[firstAction.semanticData, secondAction.semanticData]
  let sourceLegs ← operationProductLegs context first.value second.value
    firstAction.semanticData secondAction.semanticData
  let targetLegs ← operationProductLegs context firstAction.actual secondAction.actual
    first.fragment second.fragment
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
  let mut objects ← operationPresentationObjects inputs (views ++ #[(first, firstAction.actual), (second, secondAction.actual)])
  for (data, value) in #[(firstAction.semanticData, first.value),
      (secondAction.semanticData, second.value), (sourceData, wire.value), (wire.fragment, actual)] do
    objects ← operationInterfaceBinding objects data value
  validateOperationPresentationMap forwardValue sourceData wire.fragment forward objects
  validateOperationPresentationMap backwardValue wire.fragment sourceData backward objects
  let presentation : EndpointPresentation := {
    comparison, forward := forward.json, backward := backward.json,
    forwardOwnership := forward.ownership, backwardOwnership := backward.ownership }
  if let some original := wire.endpointPresentation then
    unless original.comparison == presentation.comparison &&
        original.forwardFragment == presentation.forwardFragment &&
        original.backwardFragment == presentation.backwardFragment do
      throwStratum .ambiguousRealization "the whole product has a conflicting complete endpoint action"
  let some category := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the product comparison lost its accepted complete category"
  let maps ← #[(firstAction.forwardValue, firstAction.forward),
      (firstAction.backwardValue, firstAction.backward),
      (secondAction.forwardValue, secondAction.forward),
      (secondAction.backwardValue, secondAction.backward),
      (forwardValue, forward), (backwardValue, backward)].mapM fun (value, data) => do
    return ({
      form := .canonicalMorphism category
      payload := (← combinedRecipePayload value data #[first, second])
      categoryContext := some context
      serviceHandles := wire.serviceHandles ++ parameterHandles } : Wire)
  let handles ← retainServiceOperands h maps
  return { wire with
    objectIso
    endpointPresentation := some presentation
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
    scope.parameters scope.parameterHandles
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
    (wires parameters : Array Wire) : TermElabM (Array Wire × Array Nat) := do
  let original ← h.serviceOperands.get
  -- Validate the original graph before appending any new handle: a dangling
  -- original index cannot accidentally resolve to a newly allocated entry.
  for wire in wires ++ parameters do
    discard <| operationPresentationOperandClosure original wire
  let scope : OperationProductNormalization := {
    harness := h, context, original, memo := (← IO.mkRef {}) }
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
    return { received with morphismFramed := true, morphismFraming := none,
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
      outputOwnership := execution.outputOwnership.extract start execution.outputOwnership.size }
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
    (dependencies : Array Wire) (parameterOwnership : DataOwnership.Table := #[]) :
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
    serviceHandles := (← retainServiceOperands h (#[original] ++ dependencies)) }
  let reply ← sendData h operation request (completeRequest := true)
  let answer := reply.data.json
  let backend := reply.backend
  if let .error message ← ComputationalData.validatePort template.value
      (← inferType template.value) answer then
    malformed backend operation answer message
  let data ← receiveReplyData h operation reply true
  let result := { template with
    payload := WirePayload.computed template.value data
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
    (h : Harness) (operation : String)
    (action : Expr) (sourceContext targetContext : CategoryContext)
    (original template : Wire) (descriptor : Json) (parameters : Array Json)
    (dependencies : Array Wire) (objectImage : Wire → TermElabM Wire)
    (descriptorOwnership : DataOwnership.Table := #[])
    (parameterOwnership : DataOwnership.Table := #[]) : TermElabM Wire := do
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
  let imageSource ← objectImage sourceWire
  let imageTarget ← objectImage targetWire
  CategoryContext.checkMorphism targetContext template.value imageSource.value imageTarget.value
  let parametersInputs := dependencies ++ #[sourceWire, targetWire]
  let images := #[imageSource, imageTarget]
  if let some actual ← retainedActionResult? h operation action original
      parameters parametersInputs images parameterOwnership then
    return ← forwardRetainedValue actual template.value
  let presented ← if original.pointDataInterface.isSome then pure original
    else presentMorphism original sourceWire targetWire (some sourceContext)
  let presentedData ← if let some selected := original.pointDataInterface then
    pointCallableFragment original sourceWire.value targetWire.value selected
  else pure presented.fragment
  let sourceMap ← if let .ok framed := Backend.TypedMap.decode presentedData.json then do
      unless framed.source == sourceWire.json && framed.target == targetWire.json &&
          DataOwnership.project #[.field "args", .index 0] presentedData.ownership == sourceWire.ownership &&
          DataOwnership.project #[.field "args", .index 1] presentedData.ownership == targetWire.ownership do
        throwStratum .malformed "the complete source map changed an actual endpoint packet"
      pure presentedData
    else scopedNode "typedMap" #[sourceWire.fragment, targetWire.fragment, presentedData]
  let arrow ← scopedNode "map" #[{ json := descriptor, ownership := descriptorOwnership }, sourceMap]
  let identity ← scopedNode "identity" #[imageSource.fragment, imageSource.fragment]
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
      (#[original, presented] ++ parametersInputs ++ images)) }
  let reply ← sendData h operation request (completeRequest := true)
  let answer := reply.data.json
  let backend := reply.backend
  if let .error message ← ComputationalData.validateEndpointPort template.value
      imageSource.json imageTarget.json answer then
    malformed backend operation answer message
  let data ← receiveReplyData h operation reply true
  let received := { template with
    payload := WirePayload.computed template.value data
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
    | some lift => scopedNode "createdCone"
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
      operands := operands.push { formal := wire.value, expectedType := ← inferType wire.value,
        role := if endpoints.isSome then .map else .object, wire }
      let mut endpointIndices := none
      if let some (source, target) := endpoints then
        let sourceIndex := operands.size
        operands := operands.push { formal := source.value, expectedType := ← inferType source.value,
          role := .object, wire := source }
        let targetIndex := operands.size
        operands := operands.push { formal := target.value, expectedType := ← inferType target.value,
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
      left.forwardFragment == right.forwardFragment && left.backwardFragment == right.backwardFragment
  | _, _ => false

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
    (point : Wire) (data : DataOwnership.Data) (actual : Expr)
    (dependencies : Array Wire) (framed : Option Wire := none) :
    TermElabM PreparedOperationArgument := do
  let prepared ← if data == point.fragment then pure point else
    match framed with
    | some framed => do
      unless framed.value == point.value && framed.fragment == data do
        throwError "the prepared argument producer changed its complete point or packet"
      discard <| framingContext (some context) framed.categoryContext
      pure framed
    | none => pure { point with
        payload := (← combinedRecipePayload point.value data dependencies)
        morphismFramed := true, morphismFraming := none
        categoryContext := some context }
  let prepared := { prepared with
    serviceHandles := prepared.serviceHandles ++ (← retainServiceOperands h dependencies) }
  return { data, actual, dependencies := #[prepared] ++ dependencies }

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
  let productPoint := (← retainedPointOrigin? point).any fun origin =>
    match origin.recipe with | .product .. => true | _ => false
  let changed := !sameOperationEndpointAction originalDomain.endpointPresentation domain.endpointPresentation ||
    !sameOperationEndpointAction originalTarget.endpointPresentation target.endpointPresentation
  if point.morphismFramed && (changed || productPoint) then
    if let some origin := point.morphismFraming then
      unless sameCompleteWireContext origin.source originalDomain &&
          sameCompleteWireContext origin.target originalTarget do
        throwStratum .ambiguousRealization
          "the original point frame has different complete selected endpoint occurrences"
      let replayed ← presentMorphism origin.input origin.source origin.target origin.context
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
      let (children, _) ← normalizeOperationProducts h context #[firstTarget, secondTarget] parameters
      let #[normalizedFirst, normalizedSecond] := children
        | throwError "the prepared product lost its ordered normalized factors"
      let first ← prepareOperationPointArgumentWith readRecipe h context first originalDomain firstTarget
        domain normalizedFirst (← checkedFragment (data.project paths[0]!)) parameters
      let second ← prepareOperationPointArgumentWith readRecipe h context second originalDomain secondTarget
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
      let prepared ← if firstPath == #[.index 0] && secondPath == #[.index 1] then
        pure (DataOwnership.Data.array #[first.data, second.data])
      else scopedNode "typedMap" #[domain.fragment, target.fragment,
        ← scopedNode "mediator" #[first.data, second.data]]
      return ← retainPreparedOperationArgument h context retainedPoint prepared actual
        (#[retainedPoint, domain, target, normalizedFirst, normalizedSecond] ++
          first.dependencies ++ second.dependencies)
  let recipeInputs ← readRecipe point
  let (recipeInputs, _) ← normalizeOperationProducts h context recipeInputs parameters
  let (inputs, views) ← operationArgumentObjects h context
    (#[domain, target] ++ parameters ++ recipeInputs)
  if point.morphismFramed then
    -- A pre-existing frame can be reused only at the same complete comparisons.
    -- Its Boolean flag cannot certify a newly introduced product-domain map.
    unless sameOperationEndpointAction originalDomain.endpointPresentation domain.endpointPresentation &&
        sameOperationEndpointAction originalTarget.endpointPresentation target.endpointPresentation do
      throwStratum .noImplementation
        "the already framed point requires its original complete framing provenance"
    let objects ← operationPresentationObjects inputs views
    let framed ← if (data.json.getObjValAs? String "ctor").toOption == some "typedMap" then
        pure data
      else scopedNode "typedMap" #[domain.fragment, target.fragment, data]
    validateOperationPresentationMap expected domain.fragment target.fragment framed objects
    return ← retainPreparedOperationArgument h context retainedPoint framed expected (#[retainedPoint] ++ inputs)
  let sourceAction ← operationComponentPresentation context domain inputs views
  let targetAction ← operationComponentPresentation context target inputs views
  -- The endpoint interfaces are the independently declared sources of the two
  -- comparisons; the original callable packet is embedded without rewriting it.
  let mut objects ← operationInterfaceBinding (← operationPresentationObjects inputs views)
    sourceAction.semanticData originalDomain.value
  objects ← operationInterfaceBinding objects targetAction.semanticData originalTarget.value
  let original ← if (point.json.getObjValAs? String "ctor").toOption == some "typedMap" then
      pure point.fragment
    else do
      scopedNode "typedMap"
        #[sourceAction.semanticData, targetAction.semanticData, point.fragment]
  validateOperationPresentationMap point.value sourceAction.semanticData targetAction.semanticData original objects
  let input := { point with payload := (← combinedRecipePayload point.value original (#[point] ++ inputs)) }
  let framed ← presentMorphism input domain target (some context)
  let prepared ← if domain.endpointPresentation.isNone && target.endpointPresentation.isNone then
      pure framed.fragment
    else scopedNode "typedMap" #[domain.fragment, target.fragment, framed.fragment]
  validateOperationPresentationMap expected domain.fragment target.fragment prepared objects
  -- The exact producer knows when framing is byte-for-byte unchanged. Do not
  -- expose its status/provenance-only copy alongside the original occurrence.
  let dependencies := if prepared == retainedPoint.fragment then #[retainedPoint] ++ inputs
    else #[retainedPoint, framed] ++ inputs
  retainPreparedOperationArgument h context retainedPoint prepared expected dependencies
    (if prepared != retainedPoint.fragment && prepared == framed.fragment then some framed else none)

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

/-- Observe one producer-owned intrinsic tree. The callbacks receive complete
retained occurrences; this function performs no expression-cache lookup and
never restarts a specialized producer or chooses a computational registration. -/
def observeIntrinsicAssemblyWith
    (observeChild : ActionDataRole → Wire → TermElabM Wire)
    (readEndpoints : Wire → CategoryContext → TermElabM (Wire × Wire))
    (h : Harness) (wire : Wire) (assembly : IntrinsicAssembly) : TermElabM Wire := do
  let some current ← currentIntrinsicAssembly? wire
    | throwStratum .unavailable "historical intrinsic context cannot rebuild a different current value"
  unless sameIntrinsicAssembly (some current) (some assembly) do
    throwStratum .unavailable "the intrinsic observer changed its current producer selection"
  let (original, _) ← renderCapturedActionData assembly.template
  unless original == wire.fragment do
    throwStratum .unavailable "the intrinsic assembly changed its original positioned child data"
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
  let checkEndpoint := fun (context : CategoryContext) (expected actual : Wire) => do
    discard <| framingContext (some context) expected.categoryContext
    discard <| framingContext (some context) actual.categoryContext
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType expected.value) (← inferType actual.value) <&&>
          isDefEq expected.value actual.value) do
      throwError "an intrinsic callable field changed its complete selected endpoint"
    let actual ← forwardRetainedValue actual expected.value
    unless sameCompleteWireContext expected actual do
      throwStratum .malformed
        "an intrinsic callable field changed its complete endpoint occurrence or presentation"
  let maps ← assembly.maps.mapM fun fields => do
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
      checkEndpoint fields.context source left
      checkEndpoint fields.context target right
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
  let (data, dependencies) ← renderCapturedActionData template
  let same := sameActionTemplate template assembly.template
  let alias ← match template with
    | .wire _ child => withoutModifyingState <| withTransparency .all <|
        isDefEq (← inferType child.value) (← inferType wire.value) <&&>
          isDefEq child.value wire.value
    | _ => pure false
  let mut result ← if same && data == wire.fragment then pure wire else do
    -- A direct typed wrapper forwards the child's completed point/map role as
    -- well as its data only for a checked mathematical alias. Reifying a whole
    -- callable as one point keeps its different, independently fixed outer role.
    match template with
    | .wire _ child =>
      if alias then do
        let child ← forwardRetainedValue child wire.value
        let context ← match assembly.result with
          | .object context | .map context =>
              framingContext (some context) child.categoryContext
          | .value _ => pure none
        let child := { child with
          form := wire.form, categoryContext := context, morphismFraming := none
          actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none }
        if let .value _ := assembly.result then
          pure { child with pointDataInterface := none, morphismFramed := false,
            objectObserved := false, callableObserved := false }
        else pure child
      else pure { wire with
        payload := (← combinedRecipePayload wire.value data dependencies)
        intrinsicAssembly := none, callableEndpoints := none }
    | _ => pure { wire with
        payload := (← combinedRecipePayload wire.value data dependencies)
        intrinsicAssembly := none, callableEndpoints := none }
  result ← retainIntrinsicResultAssembly result assembly.result template maps equalObjects assembly.endpointRoles
  let originalChildren := actionTemplateInputs assembly.template
  if !wire.productComponents.isEmpty &&
      sameProductComponents wire.productComponents originalChildren then
    result := { result with productComponents := actionTemplateInputs template }
  if let .map context := assembly.result then
    let forwardedEndpoints ← match template with
      | .wire .map child =>
          if same || !alias then pure none else some <$> readEndpoints child context
      | .pointCallable _ _ _ point =>
          if same then pure none else some <$> readEndpoints point context
      | _ => pure none
    match forwardedEndpoints with
    | some (source, target) =>
        result ← retainCallableEndpoints result source target context
    | none =>
        if let some (source, target) ← retainedCallableEndpoints? wire context then
          result ← retainCallableEndpoints result (← observe assembly.endpointRoles.1 source)
            (← observe assembly.endpointRoles.2 target) context
  if sameCompleteWireContext result wire then return wire
  result := { result with
    serviceHandles := (← retainServiceOperands h (dependencies ++ (← observed.get).map (·.2.2))) }
  return result

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

/-- This private table describes possible output slots only. It owns no backend,
session, service handle, validation receipt, or completed computational result. -/
structure ProspectiveData where
  occurrences : Array (ActionDataRole × Wire × Wire) := #[]
  actions : Array (ProspectiveActionKey × Wire) := #[]
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
  | .retained child => prospectiveReservedTemplate child
  | .ctor _ children | .array children => children.flatMap prospectiveReservedTemplate

/-- Reserve bytes from complete producer-owned context, including fields which
a projection may later expose. This traversal observes and dispatches nothing. -/
partial def prospectiveReservedWire (wire : Wire) : Array Json :=
  #[wire.json] ++
    wire.productComponents.flatMap prospectiveReservedWire ++
    wire.proofSources.toArray.flatMap (fun source => prospectiveReservedWire (retainedSnapshotWire source)) ++
    (wire.morphismFraming.toArray.flatMap fun frame =>
      #[frame.input, frame.source, frame.target].flatMap prospectiveReservedWire) ++
    (wire.actionRecipe.toArray.flatMap fun recipe =>
      prospectiveReservedWire recipe.original ++ prospectiveReservedTemplate recipe.descriptor ++
        recipe.endpoints.toArray.flatMap (fun (a, b) =>
          prospectiveReservedWire a ++ prospectiveReservedWire b)) ++
    (wire.intrinsicAssembly.toArray.flatMap fun assembly =>
      prospectiveReservedTemplate assembly.template ++
        assembly.maps.flatMap (fun fields =>
          #[fields.source, fields.target, fields.callable].flatMap prospectiveReservedWire) ++
        assembly.equalObjects.flatMap (fun (a, b) =>
          prospectiveReservedWire a ++ prospectiveReservedWire b)) ++
    (wire.callableEndpoints.toArray.flatMap fun endpoints =>
      prospectiveReservedWire endpoints.source ++ prospectiveReservedWire endpoints.target) ++
    (wire.pointOrigin.toArray.flatMap fun origin =>
      prospectiveReservedWire origin.source ++ prospectiveReservedWire origin.target ++
        (match origin.recipe with
          | .element owner inputs => (#[owner] ++ inputs).flatMap prospectiveReservedWire
          | .product _ _ first second _ _ => #[first, second].flatMap prospectiveReservedWire
          | .alias original => prospectiveReservedWire original)) ++
    (wire.endpointPresentation.toArray.flatMap fun presentation =>
      #[presentation.forward, presentation.backward]) ++
    (wire.pointDataInterface.toArray.flatMap fun point =>
      #[point.domainData.json, point.targetData.json])

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
    pointDataInterface := none, liftExecution := none, morphismFraming := none
    actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none
    morphismFramed := morphism, productComponents := #[], proofSources := []
    constructionInputs := none, constructionInputOwnership := #[] }
  if morphism then
    future ← retainCallableEndpoints future key.images[0]! key.images[1]! context
  reader.state.modify fun state => { state with actions := state.actions.push (key, future) }
  return future

mutual

/-- Project producer-declared slots only. Actual data and retained descriptor
leaves stay exact; no trace or JSON tag authorizes erasing their supplier table. -/
partial def prospectiveWireWith (reader : ProspectiveReader) (role : ActionDataRole)
    (wire : Wire) : TermElabM Wire := do
  if role == .retained then return wire
  let valueAssembly ← if role == .parameter then retainedIntrinsicValueAssembly? wire else pure none
  let role ← if role == .parameter && valueAssembly.isNone then do
      match ← reader.trace.node? wire.value with
      | some (.operationApply ..) | some (.operationPoint ..) |
          some (.operationEquivalence ..) | some (.morphismTransport ..) |
          some (.constructionMap ..) | some (.contextualRoute _ _ _ _ _ true) => pure .map
      | _ => pure .object
    else pure role
  if wire.actualData || (role == .map && wire.callableObserved) ||
      (role == .object && wire.objectObserved) then
    return wire
  if let some (_, _, previous) := (← reader.state.get).occurrences.find?
      (fun (selected, original, _) => selected == role && sameCompleteWireContext original wire) then
    return previous
  let assembly ← match valueAssembly with
    | some assembly => pure (some assembly)
    | none => retainedIntrinsicAssembly? wire role
  let projected ← if let some assembly := assembly then
      observeIntrinsicAssemblyWith (prospectiveWireWith reader) reader.endpoints
        reader.inspect wire assembly
    else if role == .map && wire.morphismFraming.isSome then do
      let some frame := wire.morphismFraming | unreachable!
      let replayed ← presentMorphism frame.input frame.source frame.target frame.context
      unless sameCompleteWireContext replayed wire do
        throwStratum .unavailable "the prospective map lost its exact framing producer"
      let actual ← prospectiveWireWith reader .map frame.input
      if sameCompleteWireContext actual frame.input then pure wire else do
        let some context ← framingContext frame.context actual.categoryContext
          | throwError "the prospective map lost its complete framing context"
        let (source, target) ← reader.endpoints actual context
        retainCallableEndpoints actual source target context
    else if let some recipe := wire.actionRecipe then do
      unless recipe.morphism == (role == .map) do
        throwError "the prospective action changed its producer-declared data role"
      let actual ← prospectiveActionWith reader wire recipe
      forwardRetainedValue actual wire.value
    else pure wire
  reader.state.modify fun state => { state with
    occurrences := state.occurrences.push (role, wire, projected) }
  return projected

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
  if !recipe.morphism then
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
  else
    let endpoints ← if sameCompleteWireContext original recipe.original then
        match recipe.endpoints with
        | some endpoints => pure endpoints
        | none => throwError "the prospective map lost its original complete endpoint occurrences"
      else reader.endpoints original recipe.source
    let mut images := #[]
    for endpoint in #[endpoints.1, endpoints.2] do
      let formal ← Semantic.objOf action endpoint.value
      let endpointRecipe := { recipe with
        morphism := false, original := endpoint, formal, endpoints := none }
      let image ← reader.objectTemplate endpointRecipe endpoint descriptor dependencies
      let endpointRecipe := { endpointRecipe with formal := image.value, fragment := image.fragment }
      let image ← prospectiveActionWith reader image endpointRecipe
      images := images.push image
    let key : ProspectiveActionKey := {
      operation, action, input := original, parameters := parameters.map (·.json)
      parameterOwnership := (DataOwnership.Data.array parameters).ownership
      dependencies := dependencies ++ #[endpoints.1, endpoints.2], images }
    if let some actual ← retainedActionResult? reader.live operation action original key.parameters
        key.dependencies images key.parameterOwnership then
      return ← forwardRetainedValue actual wire.value
    prospectiveActionValue reader key wire recipe.target true

end

/-- Read the callable specialization of the shared producer-owned invocation.
The shared occurrence owner distinguishes current metadata from historical plans. -/
def retainedSelectedCallableInvocation? (wire : Wire) :
    TermElabM (Option SelectedCallableInvocation) := do
  let some captured ← retainedCapturedInvocation? wire | return none
  let .callable selected := captured.interface | return none
  CategoryContext.checkMorphism selected.context wire.value selected.source.value selected.target.value
  return some selected

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
  retainCapturedInvocation h { wire with categoryContext := some selected.context }
    (.callable selected)

def selectedCallableIdentity (context : CategoryContext) (source : Wire) : TermElabM Wire := do
  let formal ← identityAtContext context source.value
  captureIntrinsicIdentity formal (contextualForm (← registryState) context source.form true)
    context source

/-- The existing complete-callable execution boundary, supplied with already
selected typed occurrences. Only the public invocation encoder builds its wire;
the original endpoint validator still checks the returned whole callable. -/
def dispatchSelectedCallable (h : Harness) (wire : Wire) (selected : SelectedCallableInvocation)
    (parameters : Array DataOwnership.Data) (arrow : Wire)
    (source target : Wire) (dependencies : Array Wire) : TermElabM Wire := do
  CategoryContext.checkMorphism selected.context wire.value source.value target.value
  CategoryContext.checkMorphism selected.context arrow.value source.value target.value
  discard <| framingContext (some selected.context) arrow.categoryContext
  let arrow ← forwardRetainedValue arrow wire.value
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
  if let .error message ← ComputationalData.validateEndpointPort wire.value
      source.json target.json answer then
    malformed reply.backend selected.address answer message
  let data ← receiveReplyData h selected.address reply true
  let result : Wire := { wire with
    payload := .computed wire.value data
    categoryContext := some selected.context
    morphismFramed := true, morphismFraming := none
    callableObserved := true, pointDataInterface := none
    actionRecipe := none, intrinsicAssembly := none, callableEndpoints := none
    capturedInvocation := none }
  let result ← retainMapImageEndpoints result source target
  retainCallableEndpoints result source target selected.context

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
    (frameMorphismFragment : Harness → Trace → Expr → Expr → Wire →
      (context : optParam (Option CategoryContext) none) →
      (pointAsMap : optParam Bool false) → TermElabM (DataOwnership.Data × Array Wire))
    (captureCompleteCallable : Harness → Trace → Wire → CategoryContext →
      (endpoints : optParam (Option (Wire × Wire)) none) →
      (publicFrame : optParam Bool true) → TermElabM Wire)
    (callableObjectPlan? : Expr → TermElabM (Option DeclaredAdmission.Plan))
    (pointAtAdmissionDomain : Harness → Trace → Wire → Expr → Expr → Expr → TermElabM Wire)
    (wholeCallablePoint : Harness → Trace → Wire → Expr → Expr → Expr →
      CategoryContext → DeclaredAdmission.Plan → TermElabM Wire)
    (realizeObjectPresentation : Harness → Trace → ObjectEntry → Array Expr →
      Array DataOwnership.Data → Array Wire → TermElabM (Option Wire))
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
    (selectedLiftExecution : Harness → Trace → SelectedLift.Plan → Expr → TermElabM Wire)
    (executeLiftFactor : Harness → Trace → Expr → Expr → Expr → Expr → Expr → TermElabM Wire)
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
              realizedEdgeData h trace edge component.declarationApplication)
            (some fun edge application => do
              let components := selected.filter fun candidate =>
                candidate.edge == edge && candidate.application == application
              let some component := components[0]?
                | throwError "the literal action lost its exact captured parameter presentation"
              unless components.all (fun candidate =>
                  candidate.declarationApplication == component.declarationApplication) do
                throwError "the literal action has distinct captured parameter presentations"
              capturedEdgeData h trace edge component.declarationApplication)
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
      selectedLiftExecution h trace plan e
  | .liftProjection receiver field =>
      if field == "composed" then return ← composedLiftExecution h trace e receiver
      let (original, execution) ← retainedLiftExecution h trace receiver
      let some index := LiftField.all.findIdx? (·.label == field)
        | throwError "the selected lift projection is not a public field"
      let expected ← SelectedLift.port execution.selections index
      unless ← withTransparency .all <| isDefEq expected e do
        throwError "the lift projection changed its complete selected formal type"
      let data ← liftProjectionFragment execution index
      let some selection := if index < 2 then execution.selections[0]?
          else execution.selections.back?
        | throwError "the retained selected lift is empty"
      let context ← SelectedLift.context selection (index >= 2)
      return {
        form := contextualForm state context original.form (index != 0)
        payload := (← if index < 2 then scopedPayload e data else recipePayload e data)
        liftExecution := if index == 0 then some execution else none
        serviceHandles := original.serviceHandles
        categoryContext := some context }
  | .structuredProjection receiver field index =>
      structuredProjection h trace e receiver field index
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
      executeLiftFactor h trace e receiver baseMap cone proof
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
      let (args, dependencies) ← realizedParameterData h trace params
      if let some presented ← realizeObjectPresentation h trace entry params args dependencies then
        unless ← withTransparency .all <|
            isDefEq (← inferType presented.value) (← inferType e) <&&>
              isDefEq presented.value e do
          throwError "the named-object presentation changed its complete selected result"
        return { presented with payload := forwardPayload presented e presented.json }
      let json ← scopedNode id.raw args
      return { form := .object entry, payload := (← combinedRecipePayload e json dependencies) }
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
      unless ← isDefEq (← inferType output.value) (← inferType e) do
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
      unless state.powerObjects.any (·.id == id) do
        throwError "the retained power object is not registered"
      let (parameters, wires) ← realizedParameterData h trace params
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      let json ← scopedNode "powerObjectMap" #[{ json := toJson id.raw },
        { json := toJson field }, DataOwnership.Data.array parameters]
      return { form := .canonicalMorphism sets, payload := (← combinedRecipePayload e json wires) }
  | .objectField id field categoryId params =>
      let some entry := state.objects.find? (·.id == id)
        | throwError "the retained field owner is not registered"
      let declared := ObjectPresentation.fieldDeclaration entry field
      unless declared.isSome do
        throwError "the retained object row registers no {field} map"
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
      -- Generalized maps and closed point arrays keep their existing distinct
      -- public encodings. Their ordered child occurrences are fixed here.
      unless ← withTransparency .all <| isDefEq domain (← closedElementDomain state) do
        let json ← scopedNode "mediator" #[first.fragment, second.fragment]
        let point : Wire := {
          form := .canonicalMorphism category
          payload := (← combinedRecipePayload e json #[first, second]) }
        return ← retainPointOrigin point context source target
          (.product presentation domain first second
            #[.field "args", .index 0] #[.field "args", .index 1])
      -- A symbolic element retains its arithmetic owner, which may differ from
      -- this component's complete coordinate. Keep both in the existing public
      -- callable frame. Actual returned point data keep their original encoding.
      let framePoint (wire : Wire) : TermElabM (DataOwnership.Data × Array Wire) := do
        unless (wire.json.getObjValAs? String "ctor").toOption == some "element" do
          return (wire.fragment, #[])
        let some (_, endpoint) := Language.homEnds? (← inferType wire.value)
          | throwError "the product's symbolic point lost its complete endpoint"
        frameMorphismFragment h trace domain endpoint wire
      let (firstData, firstEndpoints) ← framePoint first
      let (secondData, secondEndpoints) ← framePoint second
      let payload ← combinedRecipePayload e (DataOwnership.Data.array #[firstData, secondData])
        (#[first, second] ++ firstEndpoints ++ secondEndpoints)
      -- This array is the product point's two ordered components, not a graph
      -- over its generalized domain. Apply the complete endpoint presentations
      -- here so later callable framing preserves the released point encoding.
      let point : Wire := { form := .canonicalMorphism category, payload }
      let point ← retainPointOrigin point context source target
        (.product presentation domain first second #[.index 0] #[.index 1])
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
        let (arrow, operationEndpoints) ← frameMorphismFragment h trace middle target operationWire
          (some context) (pointAsMap := true)
        let (argumentData, argumentEndpoints) ← frameMorphismFragment h trace source middle argument (some context)
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
      retainPointOrigin point context sourceWire targetWire (.element selectedWire dependencies)
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
      let applications ← route.mapM (Semantic.edgeFunctor state)
      let output ← captureMapRoute h trace input route applications
      let requested ← Semantic.mapOf (← Semantic.routeFunctor state route) receiver
      unless ← withTransparency .all <|
          isDefEq requested e <&&> isDefEq output.value e do
        throwError "the recorded map transport differs from its complete semantic request"
      let some category := state.categories.find? (·.id == targetCategory)
        | throwError "the structural map's target category is not registered"
      return { output with form := .canonicalMorphism category,
        payload := forwardPayload output e output.json }
  | .functor id params receiver =>
      let some entry := state.functor? id | unreachable!
      let input ← realizeUnobserved h trace s!"the source of {id.raw} in {what}" receiver
      let raw ← elabTermAndSynthesize
        (← `($(mkCIdent entry.declaration) $(← params.mapM exprToSyntax)*)) none
      let F ← if (← whnf (← inferType raw)).isAppOf ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[raw] else pure raw
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
          return {
            form, categoryContext := some context, objectObserved := true
            objectIso := (← mapObjectComparison F input.value input.objectIso)
            endpointPresentation := (← mapEndpointPresentation F descriptor.json
              input.endpointPresentation descriptor.ownership)
            payload := (← scopedPayload e projected.data) }
      -- Whether this registered functor is structural does not decide when its
      -- computation executes. Every pending image retains the same typed action
      -- boundary; an observation invokes its ordinary registered object port.
      captureRegisteredObjectAction (.edge (.functor id)) F input e form context
        descriptorTemplate (projected.map (·.data))
  | .retainedRoute _ targetCategory route applications receiver =>
      let input ← realize h trace "the retained structural source" receiver
      -- An exact application of the registered route can use its published
      -- refinement identifications. Non-definitional applications retain the
      -- complete action descriptors and are never silently replaced.
      let mut registered := route.size == applications.size
      if registered then
        for (step, application) in route.zip applications do
          unless ← withTransparency .all <| withoutModifyingState
              (isDefEq application (← Semantic.edgeFunctor state step)) do
            registered := false
            break
      let result ← if registered then
        transport trace input route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      else transportImage trace input route (some applications) (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      unless result.form.category == targetCategory &&
          (← withTransparency .all <| isDefEq (← inferType result.value) (← inferType e)) do
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
      unless ← isDefEq (← inferType output.value) (← inferType e) do
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
      realizeLimitWith realizeUnobserved captureCompleteCallable captureMapRoute
        realizedEdgeData capturedEdgeData extentFragment?
        h trace state what id D lift?
  | .method id route receiver recordedComparisons =>
      let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let (request, input) ← operationReceiver trace original route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor
        | throwError "{id.raw} has no registered functor"
      let F ← registeredFunctorInstance functor
      let acceptedInput ← methodArgument method input
      let expected ← Semantic.objOf F acceptedInput
      let (_, bundle) ← functorCategoryBundles (← Semantic.asFunctor F)
      let context ← CategoryContext.presented { expression := functor.target, bundle }
      let target? := CategoryContext.named? state functor.target
      let form := match target? with
        | some target => imageForm state (.functor functor.id) target
        | none => Form.contextual functor.target request.form
      -- The registered comparisons that identified the recorded route among its competitors.
      let some receiverExpression := state.formExpression? original.form
        | throwError "the method receiver lost its complete accepted category expression"
      let resolution ← match state.resolveMethod receiverExpression method.name with
        | .ok resolution => pure resolution
        | .error error => throwResolutionError state error
      unless resolution.route.refs == route do
        throwError "the recorded route of {id.raw} is not the route its resolution selects"
      let comparisonTerms ← Semantic.validateResolutionComparisons state resolution (some receiver)
      Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses
        comparisonTerms recordedComparisons
      let comparisons := resolution.comparisons
      let request ← computationalOperationReceiver h trace id.raw original route request
      let request ← computationalApexReceiver trace (← realizeObjectObservation h trace request)
      if ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType request.value) (← inferType acceptedInput) <&&>
            isDefEq request.value acceptedInput) then
        if let some (.structural projected) ← projectObjectFragmentWithOrigin trace functor.source (.functor functor.id)
            F acceptedInput request.fragment then
          unless ← withTransparency .all <| isDefEq expected e do
            throwError "the projected method changed its independently retained formal result"
          return {
            form, categoryContext := some context, objectObserved := true
            payload := (← scopedPayload e projected) }
      let reply ← sendData h id.raw request comparisons
      let json := reply.data.json
      let backend := reply.backend
      let checked ← match target? with
        | some target => validateComputationalObject trace target expected json
        | none => ComputationalData.validatePort expected (← inferType expected) json
      match checked with
      | .error message => malformed backend id.raw json message
      | .ok () => pure ()
      let data ← receiveReplyData h id.raw reply true
      let result : Wire := { form, payload := .computed e data, categoryContext := some context }
      return result
  | .methodWithLifts id route lifts receiver recordedComparisons =>
      let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let (request, input) ← operationReceiver trace original route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor | unreachable!
      let some target := state.category? functor.target | unreachable!
      let F ← registeredFunctorInstance functor
      let acceptedInput ← methodArgument method input
      let expected ← Semantic.objOf F acceptedInput
      let (retainedBase, _) ← Semantic.applyRegisteredFunctor functor acceptedInput #[] (some trace)
      unless ← withTransparency .all <| isDefEq retainedBase expected do
        throwError "the prescribed base action changed its full retained method input"
      let some sourceExpression := state.formExpression? original.form
        | throwError "the prescribed method lost its complete accepted source expression"
      let resolution ← match state.resolveMethod sourceExpression method.name with
        | .ok resolution => pure resolution
        | .error error => throwResolutionError state error
      unless resolution.route.refs == route && resolution.lifts == lifts do
        throwError "the prescribed operation changed its registered route or ordered lifts"
      let comparisonTerms ← Semantic.validateResolutionComparisons state resolution (some receiver)
      Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses
        comparisonTerms recordedComparisons
      let .construct arrowConstructor #[source] := sourceExpression
        | throwError "the prescribed method receiver is not a complete Arrow"
      unless (state.constructors.find? (·.id == arrowConstructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        throwError "the prescribed method receiver uses a different constructor"
      let some constructor := state.constructors.find?
          (·.semantics == `CasCatalogue.Constructors.subobjects)
        | throwError "the prescribed method has no registered subobjects schema"
      let resultExpression := CategoryExpr.construct constructor.id #[source]
      let prepared ← LiftedSubobjectData.planIn (← inferType e) resultExpression receiver lifts retainedBase
      let plan ← match prepared with
        | .ok plan => pure plan
        | .error message => throwError "{message}"
      let request ← computationalOperationReceiver h trace id.raw original route request
      let request ← computationalApexReceiver trace (← realizeObjectObservation h trace request)
      let reply ← sendData h id.raw request resolution.comparisons
      let answer := reply.data.json
      let backend := reply.backend
      match ← validateComputationalObject trace target expected answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let baseData ← receiveReplyData h id.raw reply true
      let receivedBase : Wire := {
        form := .subobject target, payload := .computed retainedBase baseData
        serviceHandles := request.serviceHandles }
      let base := receivedBase
      let parameters ← plan.components.mapM fun component => do
        realizedParameterData h trace (← DirectConstruction.dataArguments component.selection.parameters)
      let dependencies ← IO.mkRef (#[original, base] ++ parameters.flatMap (·.2))
      let lifted ← executePrescribedLiftData h trace plan original base parameters
        (some fun edge action => do
          let encoded ← realizedEdgeData h trace edge action
          dependencies.modify (· ++ encoded.2)
          return encoded)
      let liftedJson := lifted.json
      let some checked ← LiftedSubobjectData.decodeIn (← inferType e) resultExpression
          receiver lifts retainedBase liftedJson
          (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
          (fun _ formal data objects => do
            ComputationalData.validatePort formal (← inferType formal) data objects)
          (some (parameters.map (fun data => data.1.map (·.json))))
        | throwError "the prescribed method has no complete computational lift packet"
      let packet ← match checked with
        | .ok packet => pure packet
        | .error message => malformed backend id.raw liftedJson message
      unless ← withTransparency .all <| isDefEq packet.formalResult e do
        throwError "the independent prescribed lift changed its formal result"
      unless packet.data == liftedJson do
        throwError "the completed lift decoder changed its actual scoped packet"
      let payload ← scopedPayload e lifted
      let .ok complete := LiftedSubobjectData.fields "liftedSubobject" 4 packet.data
        | throwError "the completed lift lost its full ordered packet"
      let .ok steps := complete[3]!.getArr?
        | throwError "the completed lift lost its ordered component data"
      let mut actions := #[]
      let mut sources := #[]
      let mut bases := #[]
      let mut actionOwnership : Array DataOwnership.Table := #[]
      let mut sourceOwnership : Array DataOwnership.Table := #[]
      let mut baseOwnership : Array DataOwnership.Table := #[]
      let mut outputOwnership : Array (Array DataOwnership.Table) := #[]
      unless packet.outputs.size == steps.size do
        throwError "the completed lift changed its ordered output stages"
      for (step, index) in steps.zipIdx do
        let .ok fields := LiftedSubobjectData.fields "liftStep" 5 step
          | throwError "the completed lift lost a selected step"
        let .ok sourceFields := LiftedSubobjectData.fields "arrow" 3 fields[2]!
          | throwError "the completed lift lost its original complete source Arrow"
        actions := actions.push fields[1]!
        sources := sources.push sourceFields[0]!
        bases := bases.push fields[3]!
        let stepData ← checkedFragment (lifted.project #[.field "args", .index 3, .index index])
        actionOwnership := actionOwnership.push
          (← checkedFragment (stepData.project #[.field "args", .index 1])).ownership
        sourceOwnership := sourceOwnership.push (← checkedFragment
          (stepData.project #[.field "args", .index 2, .field "args", .index 0])).ownership
        baseOwnership := baseOwnership.push
          (← checkedFragment (stepData.project #[.field "args", .index 3])).ownership
        let outputs ← checkedFragment (stepData.project #[.field "args", .index 4])
        let some component := plan.components[index]?
          | throwError "the completed lift lost its independently fixed component"
        let (sourceView, baseView) ← prescribedLiftViews component original base
          (← checkedFragment (stepData.project #[.field "args", .index 2]))
          (← checkedFragment (stepData.project #[.field "args", .index 3]))
        let sourceView := if index == 0 then original else sourceView
        let baseView := if index + 1 == plan.components.size then base else baseView
        dependencies.modify (· ++ #[sourceView, baseView])
        let some origin := state.liftInputForm? component.selection.entry.inputAddress
          | throwError "the completed lift lost its complete public input context"
        let mut fieldOwnership : Array DataOwnership.Table := #[]
        for field in [:packet.outputs[index]!.size] do
          let data ← checkedFragment (outputs.project #[.index field])
          fieldOwnership := fieldOwnership.push data.ownership
          let context ← SelectedLift.context component.selection (field >= 2)
          let output ← liftOperand component.ports[field]! context origin data (field != 0) true
          dependencies.modify (·.push output)
        outputOwnership := outputOwnership.push fieldOwnership
      let execution : LiftExecution := {
        selections := plan.components.map (·.selection), actions,
        parameters := parameters.map (fun data => data.1.map (·.json)), sources, bases, outputs := packet.outputs
        actionOwnership, sourceOwnership, baseOwnership, outputOwnership
        parameterOwnership := parameters.map (fun data => (DataOwnership.Data.array data.1).ownership) }
      let handles ← retainLiftOperands h (← dependencies.get)
      cacheLiftFields h execution none handles
      let some first := execution.selections[0]?
        | throwError "the completed method lost its selected source lift"
      let context ← CategoryContext.construct (← SelectedLift.context first) constructor.id
      unless context.expression.syntacticEq resultExpression do
        throwError "the completed method changed its accepted constructed result category"
      return {
        form := match CategoryContext.named? state resultExpression with
          | some category => .subobject category
          | none => .contextual resultExpression original.form
        payload, liftExecution := some execution, categoryContext := some context
        serviceHandles := handles }
  | .property id _ _ _ =>
      throwError "the decision {id.raw} is not a value"

mutual

-- Closed element data comes from the formal operation trace, never from carrier matching.
partial def elementFragment (h : Harness) (trace : Trace) (e : Expr) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  if let some actual := (← h.results.get)[e]? then
    if actual.actualData || actual.callableObserved then
      return (← scopedNode "point" #[actual.fragment], #[actual])
  let state ← registryState
  let some node ← trace.node? e
    | throwStratum .noImplementation m!"the closed element has no retained construction"
  match node with
  | .operationEquivalence representative chosen candidates comparisons =>
      checkOperationEquivalence e representative chosen candidates comparisons
      elementFragment h trace representative
  | .elementNumeral n _ _ =>
      return (← scopedNode "numeral" #[{ json := toJson n }], #[])
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      unless entry.generator.isSome do throwError "the retained object has no generator"
      let (_, infos, _) ← forallMetaTelescope (← getConstInfo entry.declaration).type
      let objectArity := (infos.filter (·.isExplicit)).size
      let (index, dependencies) ← realizedParameterData h trace (params.extract objectArity params.size)
      return (← scopedNode "generator" index, dependencies)
  | .operationApply id params operands _ _ =>
      let some entry := state.operations.find? (·.id == id) | unreachable!
      unless operands.size == entry.arity do
        throwError "the retained operation expression changed its declared arity"
      let (parameters, parameterWires) ← realizedParameterData h trace params
      let arguments ← operands.mapM (elementFragment h trace)
      return (← scopedNode "operationExpression"
        #[{ json := toJson id.raw }, DataOwnership.Data.array parameters,
          DataOwnership.Data.array (arguments.map Prod.fst)],
        arguments.foldl (fun dependencies argument => dependencies ++ argument.2) parameterWires)
  -- Any other closed point `1 ⟶ X` is sent as the point it is, in its published morphism
  -- encoding (a named morphism, a composite, a mediator, an admitted point).
  | _ =>
      let point ← realize h trace "a point of a closed element" e
      return (← scopedNode "point" #[point.fragment], #[point])

/-- Capture an object's accepted route at its original runtime occurrence.
The literal/reduced selectors supply mathematics; this helper retains data only. -/
partial def captureParameterAction (h : Harness) (trace : Trace) (formal receiver : Expr)
    (route : Array EdgeRef) (applications : Array Expr) : TermElabM Wire := do
  if h.parameterRecovery.contains formal then
    throwStratum .noImplementation "the selected parameter action has cyclic data dependencies"
  let h := { h with demandObjectActions := false,
    parameterRecovery := h.parameterRecovery.push formal }
  let original ← realizeUnobserved h trace "the captured parameter action source" receiver
  let result ← transportImage trace original route (some applications)
    (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType result.value) (← inferType formal) <&&> isDefEq result.value formal) do
    throwError "the captured parameter action changed its complete selected result"
  return { result with payload := forwardPayload result formal result.json }

partial def capturedObjectParameter? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option Wire) := do
  let some (action, source) := FunctorActionData.objectAction? (← instantiateMVars value)
    | return none
  let some selected ← FunctorActionData.registeredComposite? (← registryState) action
    | return none
  return some (← captureParameterAction h trace value source
    (selected.map (·.edge)) (selected.map (·.application)))

partial def capturedRetainedParameter? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option Wire) := do
  let some selected ← FunctorActionData.retainedParameterAction? trace value | return none
  return some (← captureParameterAction h trace value selected.receiver
    selected.route selected.applications)

/-- Preserve the same independently selected parameter constructors and roles.
Every dynamic child is stored when its producer places it, never located later
by equal JSON or an expression-keyed cache. -/
partial def capturedParameterData (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array ActionDataTemplate) := do
  let h := { h with demandObjectActions := false }
  let mut data : Array ActionDataTemplate := #[]
  for parameter in parameters do
    if ← isProp (← inferType parameter) then continue
    let extent ← if (← trace.node? parameter).any (fun node =>
        match node with | .literal .. => true | _ => false) then
      extentOf? (← registryState) parameter
    else pure none
    if let some (power, ambient, element) := extent then
      let ambient ← realizeUnobserved h trace "the captured extent ambient" ambient
      let literal ← realizeUnobserved h trace "the captured extent literal" element
      data := data.push (.ctor "extent" #[.literal { json := toJson power.id.raw },
        .wire .parameter ambient, .wire .retained literal])
    else if (← h.results.get)[parameter]?.isSome || (← trace.node? parameter).isSome then
      let wire ← realizeUnobserved h trace "the captured complete parameter" parameter
      data := data.push (.wire .parameter wire)
    else
      let selected := (← instantiateMVars parameter).consumeMData
      let selectedFunctor := if selected.isAppOf ``CategoryTheory.Cat.Hom.toFunctor then
        selected.appArg! else selected
      let state ← registryState
      let declaration? :=
        (state.categories.find? (fun row => selected.getAppFn.constName? == some row.declaration)).map
          (fun row => ("category", row.id.raw, row.declaration, selected)) <|>
        (state.constructors.find? (fun row => selected.getAppFn.constName? == some row.semantics)).map
          (fun row => ("constructedCategory", row.id.raw, row.semantics, selected)) <|>
        (state.functors.find? (fun row => selectedFunctor.getAppFn.constName? == some row.declaration)).map
          (fun row => ("functor", row.id.raw, row.declaration, selectedFunctor))
      if let some (tag, id, declaration, application) := declaration? then
        let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
          fields.mapM (·.fvarId!.getBinderInfo)
        unless application.getAppNumArgs == infos.size do
          throwError "the selected dictionary lost its complete declaration application"
        let arguments := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
          if info.isExplicit then some argument else none
        let arguments ← capturedParameterData h trace arguments
        if tag == "constructedCategory" then
          let some constructor := state.constructor? ⟨id⟩ | unreachable!
          unless arguments.size == constructor.signature.size do
            throwError "the constructed category lost a declared ordered argument"
        data := data.push (.ctor tag #[.literal { json := toJson id }, .array arguments])
      else if let some image ← capturedObjectParameter? h trace parameter then
        data := data.push (.wire .object image)
      else if let some image ← capturedRetainedParameter? h trace parameter then
        data := data.push (.wire .object image)
      else if let some original ← retainedConstructionResult? trace parameter then
        if h.parameterRecovery.contains parameter then
          throwStratum .noImplementation "the selected construction has cyclic data dependencies"
        let actual ← realizeUnobserved
          { h with parameterRecovery := h.parameterRecovery.push parameter }
          trace "the original complete parameter construction" original
        data := data.push (.wire .parameter actual)
      else if (← recordCompleteConstruction trace parameter) ||
          (← recordCompleteNamedCategory trace parameter) ||
          (← recordCompleteUniversalObject trace parameter) then
        if h.parameterRecovery.contains parameter then
          throwStratum .noImplementation "the selected complete declaration has cyclic data dependencies"
        let actual ← realizeUnobserved
          { h with parameterRecovery := h.parameterRecovery.push parameter }
          trace "the complete selected parameter declaration" parameter
        data := data.push (.wire .parameter actual)
      else data := data.push (.literal {
        json := ← parameterData trace parameter h.parameterRecovery })
  return data

/-- Capture declaration slots at their original positions. An explicitly
retained operand overrides only its independently selected formal slot. -/
partial def capturedCallableParameters (h : Harness) (trace : Trace) (parameters : Array Expr)
    (overrides : Array (Nat × Wire) := #[]) : TermElabM (Array SelectedCallableParameter) := do
  let h := { h with demandObjectActions := false }
  let mut result := #[]
  for index in [:parameters.size] do
    let formal := parameters[index]!
    let expectedType ← instantiateMVars (← inferType formal)
    let matches := overrides.filter (·.1 == index)
    let templates ← match matches with
      | #[] => capturedParameterData h trace #[formal]
      | #[(_, original)] => do
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType original.value) expectedType <&&> isDefEq original.value formal) do
          throwError "the retained declaration slot changed its complete selected operand"
        unless !(← isProp expectedType) do
          throwError "a proof parameter cannot carry a computational occurrence"
        pure #[ActionDataTemplate.wire .parameter original]
      | _ => throwError "the declaration slot has several retained operand occurrences"
    -- Explicit object/retained roles and a current scalar value interface
    -- belong to their producers. Only a generic parameter slot may request a
    -- whole-map observation from its independently declared Hom input type.
    let templates ← if (Language.homEnds? expectedType).isSome then
      templates.mapM fun template => match template with
        | .wire .parameter original => do
            if (← retainedIntrinsicValueAssembly? original).isSome then pure template
            else pure (.wire .map original)
        | _ => pure template
      else pure templates
    result := result.push { formal, expectedType, templates }
  for (index, _) in overrides do
    unless index < parameters.size do
      throwError "the retained declaration operand lies outside its selected telescope"
  return result

/-- All supported callable producers use this same captured invocation. The
existing OperationObservation is retained directly when that port owns dispatch;
its original Wire predates this attachment, so no recursive cycle is introduced. -/
partial def captureSelectedCallable (h : Harness) (trace : Trace) (wire : Wire)
    (address : String) (application : Expr)
    (parameters : Array SelectedCallableParameter) (descriptor : ActionDataTemplate)
    (invocationParameters : Array ActionDataTemplate)
    (context? : Option CategoryContext := none)
    (endpoints? : Option (CallableEndpointData × CallableEndpointData) := none)
    (inverse : Option Bool := none) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let some operation := state.operation? address
    | throwError "the captured callable has no accepted operation address"
  discard <| StructuredResult.checkReconstruction application
  if let some (declaration, _) := state.callable? address then
    let selected := operationApplicationBody application
    unless selected.getAppFn.constName? == some declaration do
      throwError "the captured callable changed its complete registered declaration"
    let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
      fields.mapM (·.fvarId!.getBinderInfo)
    unless selected.getAppNumArgs == infos.size do
      throwError "the captured callable lost its complete declaration application"
    let explicit := (selected.getAppArgs.zip infos).filterMap fun (value, info) =>
      if info.isExplicit then some value else none
    unless explicit.size == parameters.size do
      throwError "the captured callable lost an ordered declaration parameter"
    for (formal, retained) in explicit.zip parameters do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType formal) retained.expectedType <&&>
            isDefEq formal retained.formal) do
        throwError "the captured callable changed a complete declaration parameter"
  let (data, _) ← renderCapturedActionData descriptor
  unless data == wire.fragment do
    throwError "the callable producer changed its original descriptor occurrences"
  if let .operation entry := operation then
    unless endpoints?.isNone && inverse.isNone do
      throwError "the declared operation changed its selected whole-domain invocation role"
    let occurrences ← parameters.mapM fun parameter => do
      let rendered ← parameter.templates.mapM renderCapturedActionData
      pure ({ formal := parameter.formal, data := rendered.map Prod.fst,
        dependencies := rendered.foldl (fun inputs item => inputs ++ item.2) #[] } :
          OperationParameterOccurrence)
    let owner ← realizedOperationOwner h trace entry (operationApplicationBody wire.value)
    let request ← prepareOperationObservation h trace wire entry.id (parameters.map (·.formal))
      (some owner) (initialParameters := some occurrences)
    let context ← completedCallableContext wire request.domainWire request.targetWire
    return ← retainSelectedCallableInvocation h wire {
      address, application, formal := wire.value, fragment := wire.fragment, context
      declarationParameters := parameters, descriptor, parameters := invocationParameters
      source := request.domainWire, target := request.targetWire
      sourceOrigin := .retained, targetOrigin := request.targetOrigin
      argument := request.argument, inverse, operationRequest := some request }
  let (source, target) ← match Language.homEnds? (← inferType wire.value) with
    | some endpoints => pure endpoints
    | none =>
      let signature ← whnfR (← inferType wire.value)
      unless signature.isForall && !signature.bindingBody!.hasLooseBVars do
        throwError "the captured callable has no independently fixed complete endpoints"
      pure (signature.bindingDomain!, signature.bindingBody!)
  let context ← match context? with
    | some context => pure context
    | none =>
      let some category := state.categories.find? (·.id == wire.form.category)
        | throwError "the captured callable lost its registered complete category"
      CategoryContext.ofNamed category source
  CategoryContext.checkMorphism context wire.value source target
  let (source, target) ← match endpoints? with
    | some endpoints => pure endpoints
    | none => pure (
        ← realizeCallableEndpointWithOrigin h trace wire source true (some context),
        ← realizeCallableEndpointWithOrigin h trace wire target false (some context))
  CategoryContext.checkMorphism context wire.value source.wire.value target.wire.value
  let argument ← selectedCallableIdentity context source.wire
  retainSelectedCallableInvocation h wire {
    address, application, formal := wire.value, fragment := wire.fragment, context
    declarationParameters := parameters, descriptor, parameters := invocationParameters
    source := source.wire, target := target.wire
    sourceOrigin := source.origin, targetOrigin := target.origin
    argument, inverse }

/-- The descriptor's declaration application is checked independently of data.
Only its producer-declared parameter slots can later request observation. -/
partial def capturedEdgeData (h : Harness) (trace : Trace) (edge : EdgeRef)
    (actual : Expr) : TermElabM ActionDataTemplate := do
  let state ← registryState
  checkExecutableEdgeAction state edge (← Semantic.asFunctor actual)
  if let .constructMap constructor inner := edge then
    let original ← constructorActionArgument state constructor actual
    return .ctor "constructorMap" #[.literal { json := toJson constructor.raw },
      ← capturedEdgeData h trace inner original]
  let parameters ← actionDeclarationParameters state edge actual true
  let data ← capturedParameterData h trace parameters
  match edge with
  | .functor id => return .ctor id.raw data
  | .classifierForget id => return .ctor "classifierForget"
      #[.literal { json := toJson id.raw }, .array data]
  | _ => unreachable!

/-- Observe an already captured parameter occurrence through existing typed
owners. The ordinary parameter demand policy remains distinct from a whole-map
observation; inert element/admission context is not scanned for action tags. -/
partial def observeActionDataWire (h : Harness) (trace : Trace)
    (role : ActionDataRole) (wire : Wire) : TermElabM Wire := do
  if !h.demandObjectActions then return wire
  match role with
  | .retained => return wire
  | .object => realizeObjectObservation h trace wire
  | .map => realizeArrowObservation h trace wire
  | .parameter =>
      let wire ← realizeValueObservation h trace wire
      let wire ← match ← trace.node? wire.value with
        | some (.operationApply ..) | some (.operationPoint ..) |
            some (.operationEquivalence ..) => realizeArrowObservation h trace wire true
        | some (.morphismTransport ..) | some (.constructionMap ..) |
            some (.contextualRoute _ _ _ _ _ true) => realizeArrowObservation h trace wire
        | _ => pure wire
      realizeObjectObservation h trace wire

partial def realizedParameterData (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array DataOwnership.Data × Array Wire) := do
  let templates ← capturedParameterData h trace parameters
  let rendered ← templates.mapM (renderActionDataWith (observeActionDataWire h trace))
  return (rendered.map Prod.fst, rendered.foldl (fun result child => result ++ child.2) #[])

partial def realizedObjectParameterData? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option (DataOwnership.Data × Array Wire)) := do
  let some wire ← capturedObjectParameter? h trace value | return none
  return some (← renderActionDataWith (observeActionDataWire h trace) (.wire .object wire))

partial def realizedRetainedParameterData? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option (DataOwnership.Data × Array Wire)) := do
  let some wire ← capturedRetainedParameter? h trace value | return none
  return some (← renderActionDataWith (observeActionDataWire h trace) (.wire .object wire))

partial def realizedEdgeData (h : Harness) (trace : Trace) (edge : EdgeRef)
    (actual : Expr) : TermElabM (DataOwnership.Data × Array Wire) := do
  renderActionDataWith (observeActionDataWire h trace) (← capturedEdgeData h trace edge actual)

/-- Use the shared recursive observer while the complete action executor remains independent. -/
partial def executeObjectAction (h : Harness) (trace : Trace) (operation : String)
    (action : Expr) (original template : Wire) (parameters : Array Json)
    (dependencies : Array Wire) (parameterOwnership : DataOwnership.Table := #[]) :
    TermElabM Wire :=
  executeObjectActionWith (realizeObjectObservation h trace) h operation action original template
    parameters dependencies parameterOwnership

/-- The complete selected action determines both full contexts. Named target
schemas affect the registration address only; they never supply a dictionary. -/
partial def objectActionTemplate (h : Harness) (trace : Trace) (edge : EdgeRef)
    (action : Expr) (original : Wire) (encoder? : Option ScopedActionEncoder := none) :
    TermElabM (Wire × DataOwnership.Data × Array Wire) := do
  let state ← registryState
  let some source := state.selectedEdgeSource? edge
    | throwError "the executable action lost its registered source"
  let some target := state.selectedEdgeTarget? edge
    | throwError "the executable action lost its registered target"
  let action ← Semantic.asFunctor action
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  let sourceContext : CategoryContext := { expression := source, bundle := sourceBundle }
  CategoryContext.checkObject sourceContext original.value
  discard <| framingContext (some sourceContext) original.categoryContext
  let value ← Semantic.objOf action original.value
  let context : CategoryContext := { expression := target, bundle := targetBundle }
  CategoryContext.checkObject context value
  let (descriptor, dependencies) ← match encoder? with
    | some encoder => encoder edge action
    | none => realizedEdgeData { h with demandObjectActions := true } trace edge action
  let form := match imageCategory? state target with
    | some category => imageForm state edge category
    | none => .contextual target original.form
  let data ← scopedNode "functorAction" #[descriptor, original.fragment]
  return ({
    form, payload := (← combinedRecipePayload value data (#[original] ++ dependencies))
    categoryContext := some context
    objectIso := (← mapObjectComparison action original.value original.objectIso)
    endpointPresentation := (← mapEndpointPresentation action descriptor.json
      original.endpointPresentation descriptor.ownership)
  }, descriptor, dependencies)

/-- A primitive action executes at its own boundary. The only intrinsic object
case reads a mathematically checked projection from actual complete record fields.
All other actions need their own admitted implementation, never a target decoder. -/
partial def executeObjectEdge (h : Harness) (trace : Trace) (edge : EdgeRef)
    (action : Expr) (original : Wire) (encoder? : Option ScopedActionEncoder := none) :
    TermElabM Wire := do
  let state ← registryState
  discard <| Semantic.objOf action original.value
  let action ← instantiateMVars (← Semantic.asFunctor action)
  checkExecutableEdgeAction state edge action
  let original ← realizeObjectObservation h trace original
  if let .proofRefinement _ classifier _ := original.form then
    if edge == .classifierForget classifier then return ← proofRefinementBase trace original action
  let (template, descriptor, dependencies) ← objectActionTemplate h trace edge action original encoder?
  if let some projected ← intrinsicObjectEdgeData? trace edge action original template.value descriptor then
    return { template with payload := (← scopedPayload template.value projected),
      objectObserved := true }
  let (operation, parameters) ← edgeActionDataInvocation state edge descriptor false
  executeObjectAction h trace operation action original template (parameters.map (·.json)) dependencies
    (DataOwnership.Data.array parameters).ownership

/-- Execute a prescribed composite in categorical order, retaining and reusing
each actual intermediate image. No failed primitive chooses a different route. -/
partial def executeObjectRoute (h : Harness) (trace : Trace) (original : Wire)
    (route : Array EdgeRef) (applications : Array Expr) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the executable route lost an ordered complete action"
  let mut result := original
  for (edge, action) in route.zip applications do
    result ← executeObjectEdge h trace edge action result
  return result

/-- A returned complete map owns its actual endpoint fields. Otherwise the
independently selected signature supplies the endpoint before action execution.
No named object with an equal carrier replaces an existing endpoint packet. -/
partial def actionMapEndpoint (h : Harness) (trace : Trace) (original : Wire)
    (context : Option CategoryContext) (formal : Expr) (source : Bool) : TermElabM Wire := do
  let context ← framingContext context original.categoryContext
  if let some context := context then CategoryContext.checkObject context formal
  if let some endpoint ← retainedCallableEndpoint? original formal source context then
    return endpoint
  if let some endpoint ← retainedActionEndpoint? original context formal source then
    return endpoint
  let .ok data := ComputationalData.valuePayload original.json
    | throwStratum .malformed "the complete callable has an invalid computational envelope"
  let tag := (data.getObjValAs? String "ctor").toOption.getD ""
  if original.completedData || #["typedMap", "identity", "zero", "compose", "map"].contains tag then
    let some (left, right) := Language.homEnds? (← inferType original.value)
      | throwError "the complete callable lost its independently selected hom signature"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq formal (if source then left else right)) do
      throwError "the callable endpoint differs from its complete selected signature"
    if let some context := context then
      CategoryContext.checkMorphism context original.value left right
    discard <| checkedFragment original.fragment.validate
    let recoverFormal := !original.completedData
    let .ok projection ← ComputationalData.interfaceEndpointDataWithOrigin #[] original.value
        original.fragment source recoverFormal
      | throwStratum .malformed "the complete callable lost its retained endpoint data"
    if projection.origin == .action then
      if original.completedData then
        return { (← callableEndpointReference original formal source context) with objectObserved := true }
      throwStratum .noImplementation
        "the deferred callable endpoint has no retained typed action producer"
    let endpoint := projection.data
    let completed := original.completedData && projection.origin == .projection
    if let .error message ← ComputationalData.validatePort formal (← inferType formal)
        endpoint.json then
      throwStratum .malformed m!"the source map has an incompatible complete endpoint: {message}"
    let state ← registryState
    let form ← match context with
      | some context => pure (contextualForm state context original.form)
      | none =>
        let some category := state.categories.find? (·.id == original.form.category)
          | throwError "the callable endpoint lost its complete registered category"
        pure (.diagrams category)
    -- A complete endpoint keeps its own actual data. Portable endpoint fields
    -- need no unrelated opaque callable owner, even inside a composed map.
    return {
      form
      payload := (← scopedPayload formal endpoint completed)
      categoryContext := context
      objectObserved := completed }
  let endpoint ← realizeCallableEndpoint h trace original formal source context
  realizeObjectObservation h trace endpoint

/-- Supply complete recursive endpoint observation to the independent map executor. -/
partial def executeMapAction (h : Harness) (trace : Trace) (operation : String)
    (action : Expr) (sourceContext targetContext : CategoryContext)
    (original template : Wire) (descriptor : Json) (parameters : Array Json)
    (dependencies : Array Wire) (objectImage : Wire → TermElabM Wire)
    (descriptorOwnership : DataOwnership.Table := #[])
    (parameterOwnership : DataOwnership.Table := #[])
    (endpoint? : Option ActionEndpointReader := none) : TermElabM Wire :=
  executeMapActionWithEndpoints (endpoint?.getD (actionMapEndpoint h trace)) h operation action sourceContext
    targetContext original template descriptor parameters dependencies objectImage
    descriptorOwnership parameterOwnership

/-- Read complete endpoints from an actual callable or a producer's exact
framing origin. Only initial preparation may consult the formal endpoint reader;
a new returned callable always projects its own packet with recovery disabled. -/
partial def capturedMapEndpoints (h : Harness) (trace : Trace) (wire : Wire)
    (context : CategoryContext) (returned : Bool := false) : TermElabM (Wire × Wire) := do
  let (source, target) ← contextualMorphismEndpoints context wire.value
  if let some left ← retainedCallableEndpoint? wire source true (some context) then
    let some right ← retainedCallableEndpoint? wire target false (some context)
      | throwError "the captured callable omitted one retained endpoint occurrence"
    return (left, right)
  if let some left ← retainedActionEndpoint? wire (some context) source true then
    let some right ← retainedActionEndpoint? wire (some context) target false
      | throwError "the captured map lost one of its ordered action endpoints"
    return (left, right)
  let retained := wire.pointDataInterface
  let tag := (wire.json.getObjValAs? String "ctor").toOption.getD ""
  let ownsEndpoints := returned || wire.completedData || retained.isSome ||
    #["typedMap", "identity", "zero", "compose", "map"].contains tag
  let endpoint := fun (formal : Expr) (isSource : Bool) => do
    if !ownsEndpoints then
      return ← realizeCallableEndpoint { h with demandObjectActions := false }
        trace wire formal isSource (some context)
    let (data, projected) ← match retained with
      | some selected => do
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq selected.domain source <&&> isDefEq selected.target target) do
            throwError "the captured point changed its independently selected endpoints"
          pure ((if isSource then selected.domainData else selected.targetData), true)
      | none => do
          let projection ← checkedFragment (← ComputationalData.interfaceEndpointDataWithOrigin
            #[] wire.value wire.fragment isSource false)
          if projection.origin == .action then
            if wire.completedData then
              let reference ← callableEndpointReference wire formal isSource (some context)
              pure (reference.fragment, true)
            else throwStratum .noImplementation
              "the deferred map endpoint has no retained typed action producer"
          else pure (projection.data, projection.origin == .projection)
    let completed := wire.completedData && projected
    if let .error message ← ComputationalData.validatePort formal (← inferType formal) data.json then
      throwStratum .malformed m!"the captured map has an incompatible complete endpoint: {message}"
    return ({
      form := contextualForm (← registryState) context wire.form
      payload := (← if completed then scopedPayload formal data else recipePayload formal data)
      categoryContext := some context
      objectObserved := completed } : Wire)
  return (← endpoint source true, ← endpoint target false)

/-- Supply initial endpoint capture to the shared intrinsic framing owner. -/
partial def captureCompleteCallable (h : Harness) (trace : Trace) (input : Wire)
    (context : CategoryContext) (endpoints : Option (Wire × Wire) := none)
    (publicFrame : Bool := true) : TermElabM Wire :=
  captureCompleteCallableWith
    (fun wire context => capturedMapEndpoints { h with demandObjectActions := false }
      trace wire context) input context endpoints publicFrame

/-- Both object records and callable composites share typed child observation. -/
partial def observeIntrinsicAssembly (h : Harness) (trace : Trace) (wire : Wire)
    (assembly : IntrinsicAssembly) (registeredOnly : Bool := false) : TermElabM Wire := do
  let h := { h with demandObjectActions := true }
  observeIntrinsicAssemblyWith
    (fun role input => match role with
      | .map => realizeArrowObservation h trace input registeredOnly
      | _ => observeActionDataWire h trace role input)
    (fun input context => capturedMapEndpoints h trace input context true) h wire assembly

/-- A scalar result is observed through its retained typed producer. It is
neither an object nor a map, and no category is inferred from its carrier. -/
partial def realizeValueObservation (h : Harness) (trace : Trace) (wire : Wire) :
    TermElabM Wire := do
  if wire.actualData then return wire
  let some assembly ← retainedIntrinsicValueAssembly? wire | return wire
  observeIntrinsicAssembly h trace wire assembly

/-- Capture each complete map action before observing any selected primitive.
The original occurrence and endpoint frame remain attached to that exact step. -/
partial def captureMapRoute (h : Harness) (trace : Trace) (original : Wire)
    (route : Array EdgeRef) (applications : Array Expr) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the captured map route lost an ordered complete application"
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let mut result := original
  for (edge, application) in route.zip applications do
    let application ← instantiateMVars (← Semantic.asFunctor application)
    checkExecutableEdgeAction state edge application
    let some sourceExpression := state.selectedEdgeSource? edge
      | throwError "the captured map lost its complete source"
    let some targetExpression := state.selectedEdgeTarget? edge
      | throwError "the captured map lost its complete target"
    let (sourceBundle, targetBundle) ← functorCategoryBundles application
    let source : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let target : CategoryContext := { expression := targetExpression, bundle := targetBundle }
    let endpoints ← capturedMapEndpoints h trace result source
    let presented ← if result.pointDataInterface.isSome then pure result
      else presentMorphism result endpoints.1 endpoints.2 (some source)
    let inputData ← if let some selected := result.pointDataInterface then
      pointCallableFragment result endpoints.1.value endpoints.2.value selected
    else pure presented.fragment
    let descriptor ← capturedEdgeData h trace edge application
    let (data, dependencies) ← renderCapturedActionData descriptor
    let formal ← Semantic.mapOf application result.value
    let output : Wire := {
      form := contextualForm state target result.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map" #[data, inputData])
        (#[result, presented, endpoints.1, endpoints.2] ++ dependencies))
      morphismFramed := true
      categoryContext := some target }
    result ← retainActionInput true edge application result output descriptor (some endpoints)
  return result

/-- Direct constructions retain the same original map, endpoint occurrences
and parameter assembly as accepted structural routes. Their own registration
remains the only owner of the selected computation. -/
partial def captureConstructionMap (h : Harness) (trace : Trace) (formal : Expr)
    (selected : DirectConstruction.Action) (original : Wire) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let owner := ActionOwner.construction selected.entry.id selected.parameters
  let (source, target) ← actionOwnerContexts owner selected.functor original true
  let endpoints ← capturedMapEndpoints h trace original source
  let presented ← if original.pointDataInterface.isSome then pure original
    else presentMorphism original endpoints.1 endpoints.2 (some source)
  let inputData ← if let some interface := original.pointDataInterface then
    pointCallableFragment original endpoints.1.value endpoints.2.value interface
  else pure presented.fragment
  let descriptor := ActionDataTemplate.ctor selected.entry.id.raw
    (← capturedParameterData h trace selected.parameters)
  let (data, dependencies) ← renderCapturedActionData descriptor
  let some resultForm := (← registryState).constructionForm? selected.entry.id.raw
    | throwError "the captured construction map lost its complete result form"
  let output : Wire := {
    form := contextualForm (← registryState) target resultForm true
    payload := (← combinedRecipePayload formal (← scopedNode "map" #[data, inputData])
      (#[original, presented, endpoints.1, endpoints.2] ++ dependencies))
    morphismFramed := true, categoryContext := some target }
  retainRegisteredActionInput owner true selected.functor original output descriptor (some endpoints)

/-- Read only the parameter slots declared by the construction producer. -/
partial def capturedConstructionParameters (id : ConstructionId) (descriptor : DataOwnership.Data) :
    TermElabM (Array DataOwnership.Data) := do
  let .ok tag := descriptor.json.getObjValAs? String "ctor"
    | throwError "the captured construction lost its complete action descriptor"
  unless tag == id.raw do
    throwError "the captured descriptor belongs to a different construction"
  let .ok arguments := (descriptor.json.getObjVal? "args").bind (·.getArr?)
    | throwError "the captured construction lost its ordered action parameters"
  arguments.mapIdxM fun index _ =>
    checkedFragment (descriptor.project #[.field "args", .index index])

/-- Build the dependent construction's fixed image without observing its
source or selecting a port. Actual and prospective execution share this builder. -/
partial def capturedConstructionObjectTemplate (id : ConstructionId)
    (action : Expr) (target : CategoryContext)
    (descriptor : DataOwnership.Data) (dependencies : Array Wire) (input : Wire) :
    TermElabM Wire := do
  let state ← registryState
  let some resultForm := state.constructionForm? id.raw
    | throwError "the captured construction lost its complete image form"
  let value ← Semantic.objOf action input.value
  return {
    form := resultForm
    payload := (← combinedRecipePayload value (← scopedNode "functorAction"
      #[descriptor, input.fragment]) (#[input] ++ dependencies))
    categoryContext := some target
    objectIso := (← mapObjectComparison action input.value input.objectIso)
    endpointPresentation := (← mapEndpointPresentation action descriptor.json
      input.endpointPresentation descriptor.ownership) }

/-- Reuse the existing object executor at the dependent construction's own
registered address with already materialized captured parameters. -/
partial def executeCapturedConstructionObject (h : Harness) (trace : Trace)
    (id : ConstructionId) (action : Expr) (target : CategoryContext)
    (descriptor : DataOwnership.Data) (dependencies : Array Wire) (input : Wire) :
    TermElabM Wire := do
  let input ← realizeObjectObservation h trace input
  let parameters ← capturedConstructionParameters id descriptor
  let template ← capturedConstructionObjectTemplate id action target descriptor dependencies input
  executeObjectAction h trace id.raw action input template (parameters.map (·.json)) dependencies
    (DataOwnership.Data.array parameters).ownership

/-- Primitive map actions share the object-image executor. A composite is a
sequence of these complete actions, never a recipe delegated to its final user. -/
partial def executeMapRoute (h : Harness) (trace : Trace) (original : Wire)
    (route : Array EdgeRef) (applications : Array Expr)
    (encoder? : Option ScopedActionEncoder := none)
    (endpoint? : Option ActionEndpointReader := none) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the executable map route lost an ordered complete action"
  let state ← registryState
  let mut result := original
  for (edge, action) in route.zip applications do
    discard <| Semantic.mapOf action result.value
    let action ← instantiateMVars (← Semantic.asFunctor action)
    checkExecutableEdgeAction state edge action
    let some sourceExpression := state.selectedEdgeSource? edge
      | throwError "the executable map lost its complete registered source"
    let some targetExpression := state.selectedEdgeTarget? edge
      | throwError "the executable map lost its complete registered target"
    let (sourceBundle, targetBundle) ← functorCategoryBundles action
    let source : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let target : CategoryContext := { expression := targetExpression, bundle := targetBundle }
    let (descriptor, dependencies) ← match encoder? with
      | some encoder => encoder edge action
      | none => realizedEdgeData { h with demandObjectActions := true } trace edge action
    let (operation, parameters) ← edgeActionDataInvocation state edge descriptor true
    let formal ← Semantic.mapOf action result.value
    let template : Wire := {
      form := contextualForm state target result.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map" #[descriptor, result.fragment])
        (#[result] ++ dependencies))
      categoryContext := some target }
    result ← executeMapAction h trace operation action source target result template
      descriptor.json (parameters.map (·.json)) dependencies
      (fun original => executeObjectEdge h trace edge action original encoder?)
      descriptor.ownership (DataOwnership.Data.array parameters).ownership endpoint?
  return result

/-- Execute only a current producer-owned step. Complete result dictionaries,
fragments and suppliers are checked before any selected parameter is observed. -/
partial def observeActionRecipe (h : Harness) (trace : Trace) (wire : Wire)
    (recipe : ActionRecipe) : TermElabM Wire := do
  checkActionRecipe wire recipe
  let h := { h with demandObjectActions := true }
  checkDataOwners h wire.fragment
  let original ← if recipe.morphism then realizeArrowObservation h trace recipe.original
    else realizeObjectObservation h trace recipe.original
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType original.value) (← inferType recipe.original.value) <&&>
        isDefEq original.value recipe.original.value) do
    throwError "observing an action input changed its complete selected source"
  discard <| framingContext (some recipe.source) original.categoryContext
  let (descriptor, dependencies) ← renderActionDataWith (observeActionDataWire h trace) recipe.descriptor
  let endpoint? : Option ActionEndpointReader ← if recipe.morphism then do
    let endpoints ← if sameCompleteWireContext original recipe.original then
      match recipe.endpoints with
      | some endpoints => pure endpoints
      | none => throwError "the captured map omitted its complete original endpoint occurrences"
    else capturedMapEndpoints h trace original recipe.source true
    let endpoint : ActionEndpointReader := fun current context formal source => do
      unless sameCompleteWireContext current original do
        throwStratum .unavailable "the selected map changed its captured complete source occurrence"
      let retained := if source then endpoints.1 else endpoints.2
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType retained.value) (← inferType formal) <&&>
            isDefEq retained.value formal) do
        throwError "the selected map changed a captured complete endpoint"
      discard <| framingContext context retained.categoryContext
      return retained
    pure (some endpoint)
  else pure none
  let actual ← match recipe.owner with
    | .edge selected => do
        let encoder : ScopedActionEncoder := fun edge action => do
          unless edge == selected && (← withoutModifyingState (withTransparency .all <|
              isDefEq (← inferType action) (← inferType recipe.application) <&&>
                isDefEq action recipe.application)) do
            throwError "the captured descriptor was requested by a different complete action"
          return (descriptor, dependencies)
        if recipe.morphism then
          executeMapRoute h trace original #[selected] #[recipe.application]
            (some encoder) endpoint?
        else executeObjectEdge h trace selected recipe.application original (some encoder)
    | .construction id _ => do
        let some entry := (← registryState).constructions.find? (·.id == id)
          | throwError "the captured construction is no longer registered"
        let image := executeCapturedConstructionObject h trace id recipe.application
          recipe.target descriptor dependencies
        if recipe.morphism then
          let parameters ← capturedConstructionParameters id descriptor
          executeMapAction h trace entry.mapAddress recipe.application recipe.source recipe.target
            original wire descriptor.json (parameters.map (·.json)) dependencies image
            descriptor.ownership (DataOwnership.Data.array parameters).ownership endpoint?
        else image original
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType actual.value) (← inferType recipe.formal) <&&>
        isDefEq actual.value recipe.formal) do
    throwError "the observed action changed its complete retained result"
  discard <| framingContext (some recipe.target) actual.categoryContext
  let result ← forwardRetainedValue actual wire.value
  let result := { result with actionRecipe := none }
  unless wire.value.hasMVar || wire.value.hasLevelMVar || wire.value.hasFVar || wire.value.hasLooseBVars do
    h.results.modify (·.insert wire.value result)
  return result

/-- Demand object-action data only at a computational boundary. Formal recipes
remain useful for interpretation and metadata; an unrelated target operation
never receives an unexecuted source action in place of its selected target data. -/
partial def realizeObjectObservation (h : Harness) (trace : Trace) (wire : Wire) :
    TermElabM Wire := do
  if wire.objectObserved || wire.actualData then return wire
  if let some captured ← retainedCapturedInvocation? wire then
    return ← observeCapturedInvocation h trace wire captured
  if let some assembly ← retainedIntrinsicAssembly? wire .object then
    return ← observeIntrinsicAssembly h trace wire assembly
  if let some recipe := wire.actionRecipe then
    if recipe.morphism then
      throwError "an object observation cannot consume a retained map-action role"
    return ← observeActionRecipe h trace wire recipe
  unless (wire.json.getObjValAs? String "ctor").toOption == some "functorAction" do return wire
  throwStratum .noImplementation
    "the pending object action has no retained typed producer occurrence"

/-- Choose an admitted computational representation of the already fixed full
operation. An exact source-form registration may implement the declared composite
in one call; a registration at the operation's owner receives every intervening
object action. Distinct admitted registrations remain peers. A single registration
address receives the complete transported packet when it accepts that packet.
No failed backend call selects a different implementation or changes meaning. -/
partial def computationalOperationReceiver (h : Harness) (trace : Trace) (operation : String)
    (original : Wire) (route : Array EdgeRef) (canonical : Wire) : TermElabM Wire := do
  let state ← registryState
  let some declared := state.operation? operation
    | throwError "the selected computational operation is no longer registered"
  -- Registered presentation prefixes remain useful to old operation implementations.
  -- The residual general action also supports arbitrary unnamed Arrow endpoints.
  let encoder := realizedEdgeData h trace
  let (prepared, remaining) ← canonicalOperationInput trace original route (some encoder)
    (some (capturedEdgeData h trace))
  unless canonical.form.id == prepared.form.id &&
      (← withTransparency .all <| isDefEq canonical.value prepared.value) do
    throwError "the operation input changed its independently normalized receiver"
  let transported ← computationalApexReceiver trace
    (← transportImage trace prepared remaining none (some encoder)
      (some (capturedEdgeData h trace)))
  -- Reuse the same prefix with its actual action parameters for source-composite
  -- registrations too; metadata-only callers cannot supply replacement data.
  let canonical ← computationalApexReceiver trace prepared
  let fullAddresses := state.inputAddresses declared transported.form
  let sourceAddresses := state.inputAddresses declared canonical.form
  let accepts := fun (input : Wire) (addresses : Array String) (deferred : Bool) (row : Admitted) =>
    row.registration.operation == operation && addresses.contains row.registration.input &&
      (deferred || (DataOwnership.owners input.ownership).all
        (fun owner => owner.1 == row.registration.backend))
  -- An executed action can export portable target data. The source owner's
  -- identity cannot silently remove a competing target registration before that
  -- boundary has run; the actual returned owner is checked again at dispatch.
  let deferred := !transported.objectObserved &&
    (transported.json.getObjValAs? String "ctor").toOption == some "functorAction"
  let mut candidates : Array (Wire × Registration) := #[]
  for row in h.admitted do
    if accepts transported fullAddresses deferred row then
      candidates := candidates.push (transported, row.registration)
    else if accepts canonical sourceAddresses false row then
      candidates := candidates.push (canonical, row.registration)
  match candidates with
  | #[(input, _)] => return input
  | #[] => return transported
  | _ =>
      let addresses := candidates.toList.map fun (_, row) =>
        s!"{row.input} by {row.backend}"
      throwStratum .ambiguousRealization m!"several admitted registrations compute \
        the selected composite {operation} ({addresses}); which one is used is a choice \
        the kernel does not make"

/-- A set formed as the extent of a subset literal (`Language.asObject`), where a set is
expected, is sent as that extent: the power object, its ambient set and the literal. -/
partial def extentFragment? (h : Harness) (trace : Trace) (p : Expr) :
    TermElabM (Option (DataOwnership.Data × Array Wire)) := do
  let some (.literal _ _) ← (trace.node? p : IO _) | return none
  let some (po, X, element) ← extentOf? (← registryState) p | return none
  let ambient ← realize h trace "the ambient set of an extent" X
  let literal ← realize h trace "the literal of an extent" element
  return some (← scopedNode "extent"
    #[{ json := toJson po.id.raw }, ambient.fragment, literal.fragment], #[ambient, literal])

/-- A declared callable endpoint is a data descriptor, not an observation of a
universal construction. The public structural product frame describes an actual
product type without demanding a cone computation. Named selected objects and
previously computed objects keep their exact presentations and live dependencies.
Only the formal type supplies this structural frame; no backend determines it. -/
partial def realizeEndpoint (h : Harness) (trace : Trace) (what : String)
    (value : Expr) (recoverAction : Bool := true) (recoverNamed : Bool := true) :
    TermElabM Wire := do
  let value ← instantiateMVars value
  if let some computed := (← h.results.get)[value]? then return computed
  let node ← trace.node? value
  let structural := match node with
    | some (.object ..) | some (.parameterTransport ..) | some (.retainedRoute ..) |
        some (.parameterEquivalence ..) | some (.functor ..) | some (.proofRefinement ..) |
        some (.operationEquivalence ..) |
        some (.construction ..) | some (.selectedLift ..) | some (.liftProjection ..) => false
    | _ => true
  if structural && (← whnfR (← inferType value)).isSort then
    let reduced ← withTransparency .all <| whnf value
    if reduced.isAppOfArity ``Prod 2 then
      let fields := reduced.getAppArgs
      let first ← realizeEndpoint h trace "the first declared endpoint component"
        fields[0]! recoverAction recoverNamed
      let second ← realizeEndpoint h trace "the second declared endpoint component"
        fields[1]! recoverAction recoverNamed
      let some category := (← registryState).categories.find? (·.id == CategoryId.sets)
        | throwError "the declared product endpoint has no set category"
      let context ← CategoryContext.ofNamed category value
      let template : ActionDataTemplate := .ctor "objectProduct"
        #[.wire .object first, .wire .object second]
      let (data, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := .diagrams category
        payload := (← combinedRecipePayload value data dependencies)
        categoryContext := some context
        productComponents := #[first, second] }
      return ← retainIntrinsicAssembly result .object context template
  if node.isNone then discard <| Semantic.recordNamedObject value (some trace)
  if !recoverAction && (← trace.node? value).isNone then
    unless recoverNamed do
      throwStratum .noImplementation "the actual callable retains its own anonymous endpoint"
    -- A reduced endpoint can still be one uniquely accepted complete named
    -- object. Retained action provenance has priority, including ambiguity;
    -- this optional path must not choose between those source presentations.
    let hasRetainedAction ← try
      pure (← FunctorActionData.retainedParameterAction? trace value).isSome
    catch error =>
      if Exception.stratum? error == some .ambiguousRealization then pure true
      else throw error
    unless !hasRetainedAction && (← recordCompleteNamedObject trace value) do
      throwStratum .noImplementation "the endpoint has no separately selected computational presentation"
  realize h trace what value

/-- A complete callable supplies an endpoint descriptor even when that exact
object has no separately registered presentation. Only missing computation takes
this path; malformed values, unavailable owners and internal failures propagate. -/
partial def realizeCallableEndpointWithOrigin (h : Harness) (trace : Trace) (wire : Wire)
    (value : Expr) (source : Bool) (context : Option CategoryContext := none) :
    TermElabM CallableEndpointData := do
  let context ← framingContext context wire.categoryContext
  if let some context := context then CategoryContext.checkObject context value
  -- Current retained interfaces belong to this occurrence even before its
  -- computation completes. A formal cache entry cannot replace their fields.
  if let some endpoint ← retainedCallableEndpoint? wire value source context then
    return { wire := endpoint, origin := .retained }
  -- Actual callable/point data carries its own endpoint interface. A later
  -- expression-keyed cache entry is not a field of this returned occurrence.
  if wire.completedData then
    return { wire := ← actionMapEndpoint h trace wire context value source, origin := .retained }
  try
    -- A complete callable already fixes its anonymous endpoints. Only an exact
    -- retained or named presentation may replace that public endpoint descriptor;
    -- unrelated actions with an equal carrier do not select its presentation.
    -- Actual returned data fixes its own anonymous presentation. A newly found
    -- definitionally equal name cannot replace that computational endpoint.
    let recoverNamed := match wire.payload with | .ordinary .. => true | _ => false
    let endpoint ← realizeEndpoint h trace "the callable's complete selected endpoint"
      value false recoverNamed
    if let some context := context then
      discard <| framingContext (some context) endpoint.categoryContext
    return { wire := endpoint, origin := .retained }
  catch error =>
    unless !Exception.hasConflictingStrata error &&
        CasCatalogue.Exception.stratum? error == some .noImplementation do throw error
    return { wire := ← callableEndpointReference wire value source context, origin := .reference }

/-- Existing callers retain the endpoint-only interface. Rebuilders can also
retain which typed endpoint role the same producer selected. -/
partial def realizeCallableEndpoint (h : Harness) (trace : Trace) (wire : Wire)
    (value : Expr) (source : Bool) (context : Option CategoryContext := none) :
    TermElabM Wire := do
  return (← realizeCallableEndpointWithOrigin h trace wire value source context).wire

/-- Retain the independently selected complete endpoints of a callable before
placing it in another map expression. A symbolic point's scalar owner need not be
its selected coordinate, and an owned callable supplies data rather than a new
endpoint choice. The public typed-map frame keeps that original data unchanged. -/
partial def frameMorphismFragment (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : Option CategoryContext := none) (pointAsMap : Bool := false) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  let context ← framingContext context wire.categoryContext
  if let some context := context then
    CategoryContext.checkMorphism context wire.value source target
  if context.isNone then
    let type ← whnfR (← inferType wire.value)
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the callable lost its independently selected complete hom signature"
    let arguments := type.getAppArgs
    unless ← withTransparency .all <|
        isDefEq arguments[2]! source <&&> isDefEq arguments[3]! target do
      throwError "the callable changed its independently selected complete endpoints"
  if pointAsMap then
    if let some selected := wire.pointDataInterface then
      return (← pointCallableFragment wire source target selected, #[])
  -- This flag records already applied endpoint presentations. Check the complete
  -- formal signature even on reuse, then preserve the already framed data.
  if wire.morphismFramed then return (wire.fragment, #[])
  let graph := wire.json.getArr?.isOk ||
    (wire.json.getObjValAs? String "ctor").toOption == some "finiteGraph"
  let state ← registryState
  let coordinatePoint ← if (wire.json.getObjValAs? String "ctor").toOption ==
      some "element" then
    withTransparency .all <| withoutModifyingState
      (isDefEq source (← closedElementDomain state))
  else pure false
  let needsPresentation := fun endpoint => do
    if let some actual := (← h.results.get)[endpoint]? then
      if actual.endpointPresentation.isSome then return true
    if let some (.object id _) ← trace.node? endpoint then
      return (state.objects.find? (·.id == id)).any (·.functorPresentation.isSome)
    return false
  unless coordinatePoint || graph || (← needsPresentation source) ||
      (← needsPresentation target) do return (wire.fragment, #[])
  for object in #[source, target] do
    if (← trace.node? object).isNone then
      discard <| Semantic.recordNamedObject object (some trace)
  let sourceWire ← realizeCallableEndpoint h trace wire source true context
  let targetWire ← realizeCallableEndpoint h trace wire target false context
  let presented ← presentMorphism wire sourceWire targetWire context
  if !graph && !coordinatePoint then return (presented.fragment, #[sourceWire, targetWire])
  return (← scopedNode "typedMap" #[sourceWire.fragment, targetWire.fragment, presented.fragment],
    #[sourceWire, targetWire])

/-- A whole callable used as one data value keeps its original complete Hom
interface. The existing framing owner applies endpoint presentations once;
this additional public frame only makes the retained endpoints explicit. -/
partial def completeCallableFragment (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : CategoryContext) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  let (data, dependencies) ← frameMorphismFragment h trace source target wire
    (some context) (pointAsMap := true)
  let checkEndpoints (sourceData targetData : DataOwnership.Data) : TermElabM Unit := do
    let .ok _ := Backend.TypedMap.decode data.json
      | throwError "the complete callable lost its checked typed-map frame"
    let actualSource ← checkedFragment (data.project #[.field "args", .index 0])
    let actualTarget ← checkedFragment (data.project #[.field "args", .index 1])
    unless actualSource == sourceData && actualTarget == targetData do
      throwStratum .ambiguousRealization
        "the complete callable changed an actual scoped endpoint presentation"
  if let some selected := wire.pointDataInterface then
    -- The completed point, not a newly recovered name, owns these exact
    -- endpoint packets. The framing owner checked its full formal signature.
    checkEndpoints selected.domainData selected.targetData
    return (data, dependencies)
  let sourceWire ← realizeCallableEndpoint h trace wire source true (some context)
  let targetWire ← realizeCallableEndpoint h trace wire target false (some context)
  let dependencies := dependencies ++ #[sourceWire, targetWire]
  if (Backend.TypedMap.decode data.json).isOk then
    checkEndpoints sourceWire.fragment targetWire.fragment
    return (data, dependencies)
  return (← scopedNode "typedMap" #[sourceWire.fragment, targetWire.fragment, data],
    dependencies)

/-- Realization may name only a uniquely registered object at the complete
independently demanded type. It does not select a row by available computation. -/
partial def callableObjectPlan? (expected : Expr) :
    TermElabM (Option DeclaredAdmission.Plan) := do
  try DeclaredAdmission.resolve? CategoryId.sets expected
  catch error =>
    if Exception.interpretationKind error == .ambiguous then
      throwStratum .ambiguousRealization
        "the complete callable type has several registered object presentations"
    else throw error

/-- A function-wrapper projection is available only in the actual full Sets
category. A structured Hom never selects a function object by its carrier. -/
partial def callableHasSetsContext (context : CategoryContext) (source : Expr) :
    TermElabM Bool := withoutModifyingState do
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the callable data category is not registered"
  try
    let selected ← CategoryContext.ofNamed sets source
    withTransparency .all <| isDefEq context.bundle selected.bundle
  catch error =>
    if Exception.interpretationKind error == .invalid then pure false else throw error

/-- Prefer the exact full Hom object. Only the complete Sets dictionary permits
the declared one-data-field wrapper projection to its underlying function. -/
partial def wholeCallableObject (formal source target : Expr) (context : CategoryContext) :
    TermElabM DeclaredAdmission.Plan := do
  CategoryContext.checkMorphism context formal source target
  if let some owner ← callableObjectPlan? (← inferType formal) then return owner
  unless ← callableHasSetsContext context source do
    throwStratum .noImplementation
      "the complete structured Hom has no registered object for whole-callable observation"
  let functionType ← mkArrow source target
  let some function ← DeclaredAdmission.projectedValue? formal functionType
    | throwStratum .noImplementation "the Sets Hom has no complete declared function projection"
  let some owner ← callableObjectPlan? (← inferType function)
    | throwStratum .noImplementation "the complete function type has no registered object presentation"
  return owner

/-- Restage actual point data only through the existing registered comparison
with the language's global-point source. Other singleton objects are not given
that source's scalar convention or a fabricated computational inventory. -/
partial def pointAtAdmissionDomain (h : Harness) (trace : Trace) (wire : Wire)
    (source target domain : Expr) : TermElabM Wire := do
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the admitted point data category is not registered"
  let context ← CategoryContext.ofNamed sets source
  discard <| framingContext (some context) wire.categoryContext
  CategoryContext.checkMorphism context wire.value source target
  if ← withoutModifyingState (withTransparency .all <| isDefEq source domain) then
    return wire
  let one ← closedElementDomain (← registryState)
  unless ← withoutModifyingState (withTransparency .all <| isDefEq source one) do
    throwStratum .noImplementation
      "the admitted point has no accepted comparison from its original generalized domain"
  let comparison ← try
    (Language.operationPointComparison domain).run { trace := some trace }
  catch error =>
    if Exception.interpretationKind error == .ambiguous then
      throwStratum .ambiguousRealization
        "the admission domain has several accepted global-point comparisons"
    else throw error
  let some comparison := comparison
    | throwStratum .noImplementation "the admission domain has no accepted global-point comparison"
  let (_, _, inverse) ← (Language.constructionCoreMap comparison one domain).run
    { trace := some trace }
  let inverseWire ← realize h trace "the admission's actual inverse point-domain comparison" inverse
  unless ← withoutModifyingState (withTransparency .all <| isDefEq inverseWire.value inverse) do
    throwError "the admission changed its independently accepted point-domain comparison"
  let argument ← captureCompleteCallable h trace wire context
  let some (argumentDomain, argumentTarget) ← retainedCallableEndpoints? argument context
    | throwError "the admission lost its original complete point endpoint occurrences"
  let inverseContext ← CategoryContext.ofNamed sets domain
  let comparison ← captureCompleteCallable h trace inverseWire inverseContext
  let some (comparisonDomain, comparisonTarget) ← retainedCallableEndpoints? comparison inverseContext
    | throwError "the admission lost its accepted comparison endpoint occurrences"
  let comparisonTarget ← forwardRetainedValue comparisonTarget argumentDomain.value
  unless sameCompleteWireContext comparisonTarget argumentDomain do
    throwStratum .ambiguousRealization
      "the admission's point-domain comparison and original point have different complete endpoint occurrences"
  let actual ← StructuredResult.checkReconstruction
    (← mkAppM ``CategoryTheory.CategoryStruct.comp #[inverseWire.value, wire.value])
  CategoryContext.checkMorphism inverseContext actual domain target
  let template : ActionDataTemplate := .ctor "typedMap"
    #[.wire .object comparisonDomain, .wire .object argumentTarget,
      .ctor "compose" #[.wire .map comparison, .wire .map argument]]
  let (data, dependencies) ← renderCapturedActionData template
  let result : Wire := {
    form := .canonicalMorphism sets
    payload := (← combinedRecipePayload actual data dependencies)
    categoryContext := some inverseContext
    -- Each complete constituent retains its own pending execution and exact
    -- frame. The composition consumes those frames without presenting again.
    morphismFramed := true
    serviceHandles := (← retainLiftOperands h dependencies) }
  let result ← retainIntrinsicAssembly result .map inverseContext template
    #[{ context := inverseContext, source := comparisonDomain, target := comparisonTarget,
        callable := comparison },
      { context, source := argumentDomain, target := argumentTarget, callable := argument }]
    #[(comparisonTarget, argumentDomain)]
  retainCallableEndpoints result comparisonDomain argumentTarget inverseContext

/-- Regard the actual whole callable as one point of its already selected full
function/Hom object. The constant formal point supplies only its type; every
computational byte and opaque occurrence still comes from the original wire. -/
partial def wholeCallablePoint (h : Harness) (trace : Trace) (wire : Wire)
    (source target domain : Expr) (context : CategoryContext)
    (owner : DeclaredAdmission.Plan) : TermElabM Wire := do
  CategoryContext.checkMorphism context wire.value source target
  let selected := owner.application.value
  let value ← if ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType wire.value) selected) then pure wire.value
    else do
      unless ← callableHasSetsContext context source do
        throwStratum .noImplementation
          "a structured Hom cannot be replaced by its erased carrier function"
      let some value ← DeclaredAdmission.projectedValue? wire.value selected
        | throwStratum .noImplementation
            "the whole callable has no data-only projection to its complete selected object"
      pure value
  let one ← closedElementDomain (← registryState)
  let function ← withLocalDeclD `point one fun point => mkLambdaFVars #[point] value
  let formal ← StructuredResult.checkReconstruction
    (← mkAppOptM ``TypeCat.ofHom #[some one, some selected, some function])
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the whole-callable point category is not registered"
  let pointContext ← CategoryContext.ofNamed sets one
  CategoryContext.checkMorphism pointContext formal one selected
  discard <| Semantic.recordNamedObject selected (some trace)
  let domainWire ← realizeEndpoint h trace "the whole-callable point's actual global domain" one
  let targetWire ← realizeEndpoint h trace "the complete registered callable object" selected
  let complete ← captureCompleteCallable h trace wire context
  let template : ActionDataTemplate := .wire .map complete
  let (data, children) ← renderCapturedActionData template
  let dependencies := children ++ #[domainWire, targetWire]
  let point : Wire := {
    form := .canonicalMorphism sets
    payload := (← combinedRecipePayload formal data dependencies)
    categoryContext := some pointContext
    pointDataInterface := (← pointDataInterfaceAt one selected domainWire.fragment targetWire.fragment)
    serviceHandles := (← retainLiftOperands h dependencies) }
  let point ← retainIntrinsicAssembly point .map pointContext template #[] #[]
    (.retained, .retained)
  let point ← retainCallableEndpoints point domainWire targetWire pointContext
  pointAtAdmissionDomain h trace point one selected domain

/-- Execute a named object's published presentation only when its input parameters
already depend on actual computations. Ordinary named descriptors keep their
existing dispatch. The accepted comparison remains explicit on every later map. -/
partial def realizeObjectPresentation (h : Harness) (trace : Trace) (entry : ObjectEntry)
    (parameters : Array Expr) (data : Array DataOwnership.Data) (dependencies : Array Wire) :
    TermElabM (Option Wire) := do
  unless dependencies.any (fun wire => match wire.payload with
      | .ordinary .. => false | _ => true) do return none
  let some presentation ← ObjectPresentation.plan entry parameters (some trace) | return none
  let some published := entry.functorPresentation | unreachable!
  let state ← registryState
  let some functor := state.functor? published.functor | unreachable!
  if (← h.results.get)[presentation.argument]?.isNone then
    let mut sources : Array Wire := #[]
    for dependency in dependencies do
      if ← withoutModifyingState (withTransparency .all <|
          isDefEq dependency.value presentation.argument) then
        if !sources.any (fun other => other.json == dependency.json &&
            other.ownership == dependency.ownership) then
          sources := sources.push dependency
    if let #[source] := sources then
      h.results.modify (·.insert presentation.argument
        { source with payload := forwardPayload source presentation.argument source.json })
    else if sources.size > 1 then
      throwStratum .ambiguousRealization "the presentation argument has several actual supplied representations"
  discard <| realizeEndpoint h trace "the full registered presentation argument" presentation.argument
  let (image, _) ← Semantic.applyRegisteredFunctor functor presentation.argument #[] (some trace)
  let original ← realize h trace "the registered object presentation" image
  let actual ← transportImage trace original presentation.route (some presentation.applications)
    (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
  unless ← withTransparency .all <| isDefEq actual.value presentation.image do
    throwError "the computed object presentation changed its complete formal image"
  let fieldData := fun (selector : String) => scopedNode "objectField"
    #[{ json := toJson entry.id.raw }, { json := toJson selector }, DataOwnership.Data.array data]
  let mut comparison ← mkAppM ``CategoryTheory.Iso.symm #[presentation.identification]
  let mut forward ← fieldData "inversePresentation"
  let mut backward ← fieldData "presentation"
  if let some retained := actual.endpointPresentation then
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[comparison, retained.comparison]
    forward ← scopedNode "compose" #[forward, retained.forwardFragment]
    backward ← scopedNode "compose" #[retained.backwardFragment, backward]
  return some {
    form := .object entry
    payload := forwardPayload actual presentation.object actual.json
    objectObserved := actual.objectObserved
    serviceHandles := (← retainServiceOperands h dependencies) ++ actual.serviceHandles
    endpointPresentation := some {
      comparison, forward := forward.json, backward := backward.json
      forwardOwnership := forward.ownership, backwardOwnership := backward.ownership } }

/-- Execute exact accepted applications while retaining unnamed category contexts and
the original data owner. Both object and map actions use the same declared descriptors. -/
partial def contextualAction (h : Harness) (trace : Trace) (formal receiver : Expr)
    (source target : CategoryContext) (route : Array EdgeRef) (applications : Array Expr)
    (morphism : Bool) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the contextual route omitted a complete selected application"
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let original ← realizeUnobserved h trace "the contextual action's complete original value" receiver
  discard <| framingContext (some source) original.categoryContext
  let mut currentContext := source
  let mut result := original
  for (step, application) in route.zip applications do
    let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state step)
    unless ← withTransparency .all <| isDefEq accepted application do
      throwError "the contextual action differs from its exact accepted declaration"
    let (sourceBundle, targetBundle) ← functorCategoryBundles application
    unless ← withTransparency .all <| isDefEq sourceBundle currentContext.bundle do
      throwError "a contextual action changed its complete source bundle"
    let some targetExpression := state.selectedEdgeTarget? step
      | throwError "a contextual action has no accepted target expression"
    let next : CategoryContext := {
      expression := targetExpression, bundle := (← instantiateMVars targetBundle) }
    if morphism then
      result ← captureMapRoute h trace result #[step] #[application]
    else
      CategoryContext.checkObject currentContext result.value
      let captured ← capturedEdgeData h trace step application
      let (descriptor, dependencies) ← renderCapturedActionData captured
      let projected ← projectObjectFragmentWithOrigin trace currentContext.expression step application
        result.value result.fragment (some descriptor)
      let data ← match projected with
        | some selected => pure selected.data
        | none => scopedNode "functorAction" #[descriptor, result.fragment]
      let completed := result.completedData && projected.any (·.isStructural)
      let value ← Semantic.objOf application result.value
      let output : Wire := {
        form := contextualForm state next result.form
        payload := (← if completed then scopedPayload value data
          else combinedRecipePayload value data (#[result] ++ dependencies))
        categoryContext := some next
        objectObserved := completed
        objectIso := (← mapObjectComparison application result.value result.objectIso)
        endpointPresentation := (← mapEndpointPresentation application descriptor.json
          result.endpointPresentation descriptor.ownership) }
      result ← if completed then pure output
        else retainActionInput false step application result output captured
    currentContext := next
  unless ← withTransparency .all <| isDefEq result.value formal <&&>
      isDefEq currentContext.bundle target.bundle do
    throwError "the contextual route changed its fixed result or full target bundle"
  unless currentContext.expression.syntacticEq target.expression do
    throwError "the contextual route changed its accepted target category expression"
  return { result with
    form := contextualForm state target original.form morphism
    payload := forwardPayload result formal result.json
    categoryContext := some target }

/-- Generic composition and selected action application retain the original full domain. -/
partial def contextualComposition (h : Harness) (trace : Trace) (formal : Expr)
    (context : CategoryContext) (first second source middle target : Expr) : TermElabM Wire := do
  let state ← registryState
  CategoryContext.checkMorphism context first source middle
  CategoryContext.checkMorphism context second middle target
  CategoryContext.checkMorphism context formal source target
  unless ← withTransparency .all <| isDefEq formal
      (← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]) do
    throwError "the contextual composition changed its fixed categorical value"
  let a ← realize h trace "the complete first contextual map" first
  let b ← realize h trace "the complete second contextual map" second
  let (firstData, firstDependencies) ← frameMorphismFragment h trace source middle a (some context) (pointAsMap := true)
  let (secondData, secondDependencies) ← frameMorphismFragment h trace middle target b (some context) (pointAsMap := true)
  let selected ← match ← trace.node? second with
    | some (.cellComponent id params constructors inverse receiver) => do
      let some entry := state.cells.find? (·.id == id)
        | throwError "the selected component is no longer registered"
      let (parameters, dependencies) ← realizedParameterData h trace params
      let original ← realize h trace "the selected component's complete receiver" receiver
      let some inputForm := state.componentForm? (entry.componentAddress constructors)
        | throwError "the selected component has no admitted full input address"
      pure (some (entry.componentAddress constructors,
        #[DataOwnership.Data.array parameters, original.fragment, { json := toJson inverse }],
        dependencies.push original, inputForm))
    | some (.constructionMap id params _ _ _) => do
      if h.demandObjectActions then pure none
      else do
        let some entry := state.constructions.find? (·.id == id)
          | throwError "the selected construction is no longer registered"
        let (parameters, dependencies) ← realizedParameterData h trace params
        let some inputForm := state.constructionForm? entry.inputAddress
          | throwError "the selected construction has no complete input address"
        pure (some (entry.mapAddress, parameters, dependencies, inputForm))
    | some (.cartesian id params _ receiver "hom") => do
      let some entry := state.functor? id
        | throwError "the selected family reindexing is no longer registered"
      let (parameters, dependencies) ← realizedParameterData h trace params
      let original ← realize h trace "the cartesian map's original receiver" receiver
      let some inputForm := state.cartesianForm? entry.cartesianAddress
        | throwError "the cartesian map has no accepted complete input address"
      pure (some (entry.cartesianAddress, #[DataOwnership.Data.array parameters, original.fragment],
        dependencies.push original, inputForm))
    | _ => pure none
  let dependencies := #[a, b] ++ firstDependencies ++ secondDependencies
  if let some (operation, parameters, parameterWires, inputForm) := selected then
    let domainWire ← realizeEndpoint h trace "the contextual map's original domain" source
    let middleWire ← realizeEndpoint h trace "the contextual map's complete argument target" middle
    let targetWire ← realizeEndpoint h trace "the contextual map's complete result target" target
    let invocation : Backend.PointInvocation := {
      operation, parameters := parameters.map (·.json)
      arrow := secondData.json
      domain := domainWire.json
      source := middleWire.json
      target := targetWire.json
      argument := firstData.json }
    let input : Wire := {
      form := inputForm
      payload := (← combinedRecipePayload formal (← placedData invocation.encode #[
        (#[.field "args", .index 1], DataOwnership.Data.array parameters),
        (#[.field "args", .index 2], secondData),
        (#[.field "args", .index 3], domainWire.fragment),
        (#[.field "args", .index 4], middleWire.fragment),
        (#[.field "args", .index 5], targetWire.fragment),
        (#[.field "args", .index 6], firstData)])
        (dependencies ++ parameterWires ++ #[domainWire, middleWire, targetWire]))
      serviceHandles := (← retainServiceOperands h
        (dependencies ++ parameterWires ++ #[domainWire, middleWire, targetWire])) }
    let reply ← sendData h operation input (completeRequest := true)
    let answer := reply.data.json
    let backend := reply.backend
    let validation ← if ← withTransparency .all <| isDefEq source (← closedElementDomain state) then
      ComputationalData.validateElementAt target targetWire.json (← pointResultValue state formal) answer
    else ComputationalData.validateEndpointPort formal domainWire.json targetWire.json answer
    if let .error message := validation then malformed backend operation answer message
    let data ← receiveReplyData h operation reply true
    let returned : Wire := {
      form := contextualForm state context b.form true
      payload := .computed formal data
      morphismFramed := true
      pointDataInterface := (← pointInvocationInterface formal input.fragment)
      categoryContext := some context }
    return ← retainPointOrMapEndpoints returned domainWire targetWire
  let firstWire ← captureCompleteCallable h trace a context
  let secondWire ← captureCompleteCallable h trace b context
  let some (domainWire, firstTarget) ← retainedCallableEndpoints? firstWire context
    | throwError "the intrinsic contextual composition lost its first complete endpoints"
  let some (secondSource, targetWire) ← retainedCallableEndpoints? secondWire context
    | throwError "the intrinsic contextual composition lost its second complete endpoints"
  let template : ActionDataTemplate := .ctor "compose"
    #[.wire .map firstWire, .wire .map secondWire]
  let (data, inputs) ← renderCapturedActionData template
  let result : Wire := {
    form := contextualForm state context b.form true
    payload := (← combinedRecipePayload formal data inputs)
    morphismFramed := true
    categoryContext := some context }
  let result ← retainIntrinsicAssembly result .map context template #[]
    #[(firstTarget, secondSource)]
  retainCallableEndpoints result domainWire targetWire context

/-- Read the formal construction already attached to this exact parent. For a
pending invocation this uses its selected schema without asking it for data. -/
partial def capturedConstructionInterface (h : Harness) (trace : Trace) (parent : Wire)
    (receiver : Expr) : TermElabM (StructuredProjection.ConstructionPlan × Option StructuredResult.DataPlan) := do
  let context ← match parent.categoryContext with
    | some context => pure context
    | none =>
      let some category := (← registryState).categories.find? (·.id == parent.form.category)
        | throwError "the structured result lost its complete registered category"
      CategoryContext.ofNamed category receiver
  if let some assembly ← retainedIntrinsicAssembly? parent .object then
    if let .wire .object child := assembly.template then
      let forwarded ← forwardRetainedValue child parent.value
      if sameCompleteWireContext { forwarded with
          intrinsicAssembly := parent.intrinsicAssembly,
          capturedInvocation := parent.capturedInvocation } parent then
        return ← capturedConstructionInterface h trace child receiver
  let retained ← match ← retainedCapturedInvocation? parent with
    | some captured => pure (some captured)
    | none =>
      if let some captured := parent.capturedInvocation then
        let some record := (← h.invocations.get).find? (·.captured.occurrence == captured.occurrence)
          | throwStratum .unavailable "the structured result's original invocation scope has expired"
        let some actual := record.result
          | throwError "the structured result's retained invocation has not completed"
        let actual ← forwardRetainedValue actual parent.value
        unless sameCompleteWireContext actual parent do
          throwStratum .unavailable "the structured result changed its exact completed invocation occurrence"
        pure (some record.captured)
      else pure none
  if let some captured := retained then
    if let .structured selected := captured.interface then
      let diagram := if selected.creation.isSome then selected.sourceDiagram else selected.targetDiagram
      let cone ← mkAppM (if selected.row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[selected.formalPresentation]
      let construction : StructuredProjection.ConstructionPlan := {
        row := selected.row, lift := selected.creation.map (·.id), diagram,
        presentation := selected.formalPresentation, cone, apex := receiver, context }
      return (construction, some selected.plan)
  let some construction ← StructuredProjection.construction? receiver context (some trace)
    | throwStratum .invalid "the selected field has no independently retained construction"
  let plan ← if construction.lift.isSome then pure none else some <$> construction.dataPlan
  return (construction, plan)

/-- A constructor input role addresses a retained argument or one of its exact
endpoints. It never searches the result cache or locates an equal JSON packet. -/
partial def capturedUniversalRole (selected : SelectedStructuredInvocation)
    (role : StructuredResult.InputRole) : TermElabM Wire := do
  let inputs := if selected.creation.isSome then selected.sourceInputs else selected.imageInputs
  let position := match role with
    | .argument position | .source position | .target position => position
  let some input := inputs[position]?
    | throwError "the constructor schema lost an explicit input occurrence"
  let slot ← match role with
    | .argument _ => pure input.operand
    | .source _ =>
      let some endpoints := input.endpoints
        | throwError "the constructor schema selects an absent source endpoint"
      pure endpoints.1
    | .target _ =>
      let some endpoints := input.endpoints
        | throwError "the constructor schema selects an absent target endpoint"
      pure endpoints.2
  let some input := selected.operands[slot]?
    | throwError "the constructor schema points outside its captured input telescope"
  return input.wire

/-- Bind a formal constructor input to its declared original occurrence(s).
Repeated binder roles are retained together and checked after materialization. -/
partial def captureConstructionInput (h : Harness) (trace : Trace) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (binding : StructuredResult.DataBinder) (context? : Option CategoryContext := none) : TermElabM Wire := do
  let context := context?.getD construction.context
  let some formal := binding.formalValue
    | throwError "the selected constructor input has no fixed formal value"
  if let some captured ← retainedCapturedInvocation? parent then
    if let .structured selected := captured.interface then
      let originals ← binding.inputRoles.mapM (capturedUniversalRole selected)
      if let some first := originals[0]? then
        let first ← forwardRetainedValue first formal
        let inputOccurrences := binding.inputRoles.map fun role =>
          let (position, endpoint) := match role with
            | .argument position => (position, none)
            | .source position => (position, some true)
            | .target position => (position, some false)
          (position + (if selected.creation.isSome then 0 else selected.sourceInputs.size), endpoint)
        let mut original : Wire := {
          form := first.form,
          payload := (← combinedRecipePayload formal parent.fragment #[parent]),
          categoryContext := some context }
        let endpoints ← if (Language.homEnds? (← inferType formal)).isSome then do
          let complete ← captureCompleteCallable { h with demandObjectActions := false }
            trace first context
          retainedCallableEndpoints? complete context
        else pure none
        if let some (source, target) := endpoints then
          original ← retainCallableEndpoints original source target context
        return ← retainCapturedInvocation h original (.projection {
          formal, fragment := parent.fragment, context, parent, construction, plan := some plan,
          port := none, inputOccurrences, endpoints })
  let inputs ← constructionInputFragments parent
  match selectedConstructionInput inputs formal with
  | .error message => throwStratum .ambiguousRealization message
  | .ok (some data) =>
    let morphism := (Language.homEnds? (← inferType formal)).isSome
    return {
      form := contextualForm (← registryState) context parent.form morphism,
      payload := (← scopedPayload formal data true), categoryContext := some context,
      objectObserved := !morphism, callableObserved := morphism }
  | .ok none =>
    -- This is still preparation of a formal input, never a returned-data decoder.
    discard <| Semantic.recordNamedObject formal (some trace)
    realizeUnobserved { h with demandObjectActions := false } trace
      "the constructor's fixed formal input" formal

/-- A complete map may carry an opaque callable whose endpoint is exposed by
its public projection interface. Retain that map-field occurrence explicitly. -/
partial def captureConstructionEndpoint (h : Harness) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (formal : Expr) (source : Bool)
    (context : CategoryContext) : TermElabM Wire := do
  let some (domain, target) := Language.homEnds? port.expectedType
    | throwError "an endpoint projection requires a selected complete map port"
  let expected := if source then domain else target
  unless ← withoutModifyingState (withTransparency .all <| isDefEq expected formal) do
    throwError "the constructor endpoint changed its fixed formal role"
  let original : Wire := {
    form := contextualForm (← registryState) context parent.form,
    payload := (← combinedRecipePayload formal parent.fragment #[parent]),
    categoryContext := some context }
  retainCapturedInvocation h original (.projection {
    formal, fragment := parent.fragment, context := context,
    parent, construction, plan := some plan, port := some port, endpoint := some source })

/-- Constructor ports and endpoint binders are selected from one DataPlan. A
later field result cannot choose another parent, binder or full category. -/
partial def captureConstructionPort (h : Harness) (trace : Trace) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (ancestors : Array Nat := #[])
    (context? : Option CategoryContext := none) : TermElabM Wire := do
  let context := context?.getD construction.context
  if ancestors.contains port.index then
    throwError "the accepted constructor data plan has cyclic endpoint ports"
  let ancestors := ancestors.push port.index
  let endpoint := fun (binder : Nat) => do
    let some binding := plan.binders[binder]?
      | throwError "the selected constructor field lost its endpoint binder"
    match binding.port with
    | some index =>
      let some selected := plan.ports[index]?
        | throwError "the endpoint binder points outside the selected data plan"
      captureConstructionPort h trace parent construction plan selected ancestors (some context)
    | none => captureConstructionInput h trace parent construction plan binding (some context)
  let endpoints ← match Language.homEnds? port.expectedType with
    | none => pure none
    | some (sourceValue, targetValue) => do
      let source ← match port.domainBinder with
        | some binder => endpoint binder
        | none => captureConstructionEndpoint h parent construction plan port sourceValue true context
      let target ← match port.codomainBinder with
        | some binder => endpoint binder
        | none => captureConstructionEndpoint h parent construction plan port targetValue false context
      CategoryContext.checkMorphism context port.formalField source.value target.value
      pure (some (source, target))
  let original : Wire := {
    form := contextualForm (← registryState) context parent.form endpoints.isSome,
    -- The private pending anchor is the parent's request data. It is not a
    -- fictitious cone or an already returned constructor field.
    payload := (← combinedRecipePayload port.formalField parent.fragment #[parent]),
    categoryContext := some context }
  let original ← match endpoints with
    | some (source, target) => retainCallableEndpoints original source target context
    | none => pure original
  retainCapturedInvocation h original (.projection {
    formal := port.formalField, fragment := parent.fragment, context := context,
    parent, construction, plan := some plan, port := some port, endpoints })

/-- Project actual scoped data only after the exact captured parent has completed.
A returned field supplies neither a formal object nor a comparison cell. -/
partial def observeStructuredProjection (h : Harness) (trace : Trace) (_wire : Wire)
    (selected : SelectedStructuredProjection) : TermElabM Wire := do
  let parent ← realizeObjectObservation h trace selected.parent
  let .construction result _ := parent.payload
    | throwStratum .noImplementation "the structured projection has no complete returned construction"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq result.diagram selected.construction.diagram) do
    throwError "the observed structured parent changed its selected formal diagram"
  if !selected.inputOccurrences.isEmpty then
    let retained ← h.serviceOperands.get
    let actual ← selected.inputOccurrences.mapM fun (position, endpoint) => do
      let some handle := parent.serviceHandles[position]?
        | throwError "the complete construction lost its original typed input handle"
      let some original := retained[handle]?
        | throwStratum .unavailable "the constructor input occurrence's owning scope has expired"
      let original ← match endpoint with
        | none => pure original
        | some source =>
          let some (domain, target) ← retainedCallableEndpoints? original selected.context
            | throwError "the complete constructor input lost its exact endpoint occurrences"
          pure (if source then domain else target)
      forwardRetainedValue original selected.formal
    let some first := actual[0]? | unreachable!
    unless actual.all (sameCompleteWireContext first) do
      throwStratum .noImplementation
        "one constructor binder has distinct actual input presentations without a selected comparison"
    return first
  let diagramData ← checkedFragment (parent.fragment.project #[.field "args", .index 1])
  let packetData ← checkedFragment (parent.fragment.project #[.field "args", .index 2])
  let data ← match selected.port, selected.leg, result.packet with
    | some port, none, .direct _ =>
      checkedFragment (packetData.project #[.field "args", .index port.index])
    | some port, none, .created .. =>
      scopedNode "constructionField" #[{ json := toJson selected.construction.row.id.raw },
        diagramData, packetData, { json := toJson port.index }]
    | none, some _, _ =>
      let some index := selected.legData
        | throwError "the selected defining leg lost its independently encoded index"
      scopedNode "constructionLeg" #[{ json := toJson selected.construction.row.id.raw },
        diagramData, packetData, index]
    | _, _, _ => throwError "the selected projection lost its unique constructor role"
  let data ← match selected.endpoint with
    | none => pure data
    | some source => placedData
        (Backend.MorphismEndpoint.encode { callable := data.json, source })
        #[(#[.field "args", .index 0], data)]
  let resultWire : Wire := {
    form := contextualForm (← registryState) selected.context parent.form selected.endpoints.isSome,
    payload := (← scopedPayload selected.formal data true), categoryContext := some selected.context,
    objectObserved := selected.endpoints.isNone, callableObserved := selected.endpoints.isSome,
    serviceHandles := (← retainServiceOperands h #[parent]) }
  match selected.endpoints with
  | none => pure resultWire
  | some (source, target) => do
    let source ← realizeObjectObservation h trace source
    let target ← realizeObjectObservation h trace target
    CategoryContext.checkMorphism selected.context selected.formal source.value target.value
    if let .error message ← ComputationalData.validateEndpointPort selected.formal
        source.json target.json data.json then
      throwStratum .malformed m!"the projected construction map changed its complete endpoint data: {message}"
    retainCallableEndpoints resultWire source target selected.context

/-- Compile the already selected defining-map algebra to ordinary typed producer
nodes. Registered map actions remain actions and are executed by their existing
observer; they do not become an opaque graph or a leaf-interpreted recipe. -/
partial def captureConstructionExpression (h : Harness) (trace : Trace) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (projection : StructuredResult.DataProjection) (context? : Option CategoryContext := none) :
    TermElabM Wire := do
  let context := context?.getD construction.context
  let state ← registryState
  match projection with
  | .field index =>
    let some port := plan.ports[index]?
      | throwError "the defining-map expression selects an absent constructor field"
    captureConstructionPort h trace parent construction plan port #[] (some context)
  | .input formal =>
    let bindings := plan.binders.filter fun binding =>
      binding.port.isNone && binding.formalValue == some formal
    if let some binding := bindings[0]? then
      -- Every retained binder role belongs to this same formal input. No
      -- returned bytes decide which original occurrence supplied it.
      let binding := { binding with inputRoles := bindings.flatMap (·.inputRoles) }
      return ← captureConstructionInput h trace parent construction plan binding (some context)
    discard <| Semantic.recordNamedObject formal (some trace)
    realizeUnobserved { h with demandObjectActions := false } trace
      "the defining map's fixed input" formal
  | .identity object =>
    let object ← captureConstructionExpression h trace parent construction plan object (some context)
    let carrier ← CategoryContext.carrier context
    let dictionary ← CategoryContext.dictionary context
    let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
      #[some carrier, some dictionary]
    let identity ← mkAppOptM ``CategoryTheory.CategoryStruct.id
      #[some carrier, some categoryStructure, some object.value]
    let template : ActionDataTemplate := .ctor "identity"
      #[.wire .object object, .wire .object object]
    let (data, dependencies) ← renderCapturedActionData template
    let wire : Wire := {
      form := contextualForm state context parent.form true,
      payload := (← combinedRecipePayload identity data dependencies), categoryContext := some context }
    let wire ← retainIntrinsicAssembly wire .map context template
    retainCallableEndpoints wire object object context
  | .composition first second =>
    let first ← captureConstructionExpression h trace parent construction plan first (some context)
    let second ← captureConstructionExpression h trace parent construction plan second (some context)
    let first ← captureCompleteCallable h trace first context
    let second ← captureCompleteCallable h trace second context
    let some (source, middle) ← retainedCallableEndpoints? first context
      | throwError "the defining-map composite lost its first complete endpoint pair"
    let some (middle', target) ← retainedCallableEndpoints? second context
      | throwError "the defining-map composite lost its second complete endpoint pair"
    let formal ← ServiceRequest.compose context source.value middle.value target.value
      first.value second.value
    let template : ActionDataTemplate := .ctor "compose" #[.wire .map first, .wire .map second]
    let (data, dependencies) ← renderCapturedActionData template
    let wire : Wire := {
      form := contextualForm state context parent.form true,
      payload := (← combinedRecipePayload formal data dependencies), categoryContext := some context }
    let wire ← retainIntrinsicAssembly wire .map context template
      #[{ context, source, target := middle, callable := first },
        { context, source := middle', target, callable := second }] #[(middle, middle')]
    retainCallableEndpoints wire source target context
  | .map action arrow =>
    let some actions ← FunctorActionData.registeredComposite? state action
      | throwStratum .noImplementation "the defining-map action has no complete registered interface"
    let some first := actions[0]?
      | throwError "the defining-map action lost its first selected component"
    let some sourceExpression := state.selectedEdgeSource? first.edge
      | throwError "the defining-map action lost its full source category expression"
    let (sourceBundle, targetBundle) ← functorCategoryBundles (← Semantic.asFunctor action)
    unless ← withoutModifyingState (withTransparency .all <| isDefEq targetBundle context.bundle) do
      throwError "the defining-map action changed its selected full target category"
    let sourceContext : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let arrow ← captureConstructionExpression h trace parent construction plan arrow (some sourceContext)
    captureMapRoute { h with demandObjectActions := false } trace arrow
      (actions.map (·.edge)) (actions.map (·.application))

/-- Form a defining map while its universal result is still pending. Direct
constructors compile their formal DataProjection algebra; created constructions
retain their existing complete creation projection and its accepted source role. -/
partial def captureConstructionLeg (h : Harness) (trace : Trace) (formal receiver index : Expr) :
    TermElabM Wire := do
  let parent ← realizeUnobserved { h with demandObjectActions := false } trace
    "the complete construction defining this leg" receiver
  let (construction, plan) ← capturedConstructionInterface h trace parent receiver
  if construction.lift.isNone then
    let some plan := plan
      | throwError "the selected direct defining map lost its complete data plan"
    let .ok (projection, count) ← StructuredResult.dataProjection construction.row construction.diagram index
      | throwStratum .noImplementation "the accepted defining map has no complete computational projection algebra"
    unless count == plan.ports.size do
      throwError "the defining-map projection changed its selected constructor port count"
    let result ← captureConstructionExpression h trace parent construction plan projection
    return ← forwardRetainedValue result formal
  let indexType ← inferType index
  let diagramType ← withTransparency .all <| whnf (← inferType construction.diagram)
  unless diagramType.isAppOfArity ``CategoryTheory.Functor 4 &&
      (← withTransparency .all <| isDefEq indexType diagramType.getAppArgs[0]!) do
    throwError "the created defining map changed its exact diagram-index type"
  let .ok indexData ← Codec.encode index
    | throwStratum .noImplementation "the defining-map index has no public encoding"
  let maps ← mkAppM (if construction.row.colimit then ``CategoryTheory.Limits.Cocone.ι
    else ``CategoryTheory.Limits.Cone.π) #[construction.cone]
  let expected ← mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
  unless ← withoutModifyingState (withTransparency .all <| isDefEq expected formal) do
    throwError "the created defining map changed its original complete formal question"
  let some (source, target) := Language.homEnds? (← inferType formal)
    | throwError "the created defining map has no complete categorical endpoints"
  let endpoint := fun value => do
    if ← withoutModifyingState (withTransparency .all <| isDefEq value parent.value) then
      return ← forwardRetainedValue parent value
    discard <| Semantic.recordNamedObject value (some trace)
    realizeUnobserved { h with demandObjectActions := false } trace
      "the created defining map's selected endpoint" value
  let source ← endpoint source
  let target ← endpoint target
  let original : Wire := {
    form := contextualForm (← registryState) construction.context parent.form true,
    payload := (← combinedRecipePayload formal parent.fragment #[parent]),
    categoryContext := some construction.context }
  let original ← retainCallableEndpoints original source target construction.context
  retainCapturedInvocation h original (.projection {
    formal, fragment := parent.fragment, context := construction.context, parent,
    construction, plan, port := none, leg := some index, legData := some { json := indexData },
    endpoints := some (source, target) })

/-- Complete ordinary result fields are projections of their retained formal schema
and actual returned packet. A computational field supplies neither a formal object
identification nor any law about the construction. -/
partial def structuredProjection (h : Harness) (trace : Trace) (formal receiver : Expr)
    (field : String) (index : Option Nat) : TermElabM Wire := do
  let state ← registryState
  let original ← realizeUnobserved { h with demandObjectActions := false } trace "the complete structured result" receiver
  let context ← match original.categoryContext with
    | some context => pure context
    | none => do
      let some category := state.categories.find? (·.id == original.form.category)
        | throwError "the structured result lost its complete category context"
      CategoryContext.ofNamed category receiver
  if let some index := index then
    let (construction, retainedPlan) ← capturedConstructionInterface h trace original receiver
    let dataPlan ← if construction.lift.isSome then construction.dataPlan else
      match retainedPlan with
      | some plan => pure plan
      | none => throwError "the selected direct construction lost its retained data plan"
    let some port := dataPlan.ports[index]?
      | throwStratum .invalid "the selected field is outside its registered constructor schema"
    unless ← withoutModifyingState (withTransparency .all <| isDefEq port.formalField formal) do
      throwError "the selected data port changed its complete formal field"
    let result ← captureConstructionPort h trace original construction dataPlan port
    return ← forwardRetainedValue result formal
  let original ← realizeObjectObservation h trace original
  let some plan ← StructuredProjection.arrow? receiver context
    | throwError "the selected result has no accepted Arrow or subobject projection"
  let (expected, targetContext, morphism) ← plan.field field
  unless ← withTransparency .all <| isDefEq expected formal do
    throwError "the structured projection changed its complete formal field"
  let some actual ← StructuredProjection.arrow? original.value context
    | throwError "the retained complete result lost its actual structured type"
  let arrowComparison ← original.objectIso.mapM plan.arrowComparison
  let callable ← scopedNode (if plan.subobject then "subobjectInclusion" else "arrowHom")
    #[original.fragment]
  let sourceData ← if plan.subobject then
      scopedNode "subobjectApex" #[original.fragment]
    else
      placedData (Backend.MorphismEndpoint.encode { callable := callable.json, source := true })
        #[(#[.field "args", .index 0], callable)]
  let targetData ← placedData
    (Backend.MorphismEndpoint.encode { callable := callable.json, source := false })
    #[(#[.field "args", .index 0], callable)]
  let data ← match field with
    | "obj" | "source" => pure sourceData
    | "target" => pure targetData
    | "hom" => pure callable
    | "inclusion" => scopedNode "arrow" #[sourceData, targetData, callable]
    | _ => unreachable!
  if morphism then
    let aligned ← alignedArrowHom actual.arrow arrowComparison
    unless ← withTransparency .all <| isDefEq (← inferType aligned) (← inferType formal) do
      throwError "the structured map projection changed its original complete endpoints"
    let unframed : Wire := {
      form := contextualForm state targetContext original.form true
      payload := (← combinedRecipePayload formal data #[original])
      categoryContext := some targetContext }
    let (data, endpoints) ← frameMorphismFragment h trace plan.source plan.target unframed
    return { unframed with
      payload := (← combinedRecipePayload formal data (endpoints.push original))
      morphismFramed := true }
  let action ← plan.projectionFunctor field
  let some (.construct constructor _) := some context.expression | unreachable!
  let (parameters, dependencies) ← realizedParameterData h trace #[plan.base.bundle]
  let categoryData ← scopedNode "constructedCategory"
    #[{ json := toJson constructor.raw }, DataOwnership.Data.array parameters]
  let selector := if field == "obj" then "source" else field
  let descriptor ← scopedNode "structuredProjectionAction" #[categoryData, { json := toJson selector }]
  let (value, _, _) ← actual.field field
  let objectIso ← mapObjectComparison action original.value original.objectIso
  let endpointPresentation ← mapEndpointPresentation action descriptor.json original.endpointPresentation
    descriptor.ownership
  return {
    form := contextualForm state targetContext original.form
    payload := (← combinedRecipePayload value data (dependencies.push original))
    objectIso, endpointPresentation, categoryContext := some targetContext }

/-- Read the preserved actual fields of a completed lift without rerunning its ports. -/
partial def retainedLiftExecution (h : Harness) (trace : Trace) (receiver : Expr) :
    TermElabM (Wire × LiftExecution) := do
  let wire ← realize h trace "the complete selected lift" receiver
  let some execution := wire.liftExecution
    | throwError "the completed lift lost its selected computation and actual four-field outputs"
  let legacyOwner := match wire.payload with
    | .computed _ (.owned backend session _) | .computed _ (.opaque backend session _) |
        .construction _ (.owned backend session) => some (backend, session)
    | _ => none
  let execution ← scopedLiftExecution execution legacyOwner
  return (wire, execution)

/-- Explicitly compose retained stages without rerunning their four ports or replacing
the ordinary outer selection's cache. Only its recorded defining-map links form the chain. -/
partial def composedLiftExecution (h : Harness) (trace : Trace) (formal receiver : Expr) :
    TermElabM Wire := do
  let recorded ← SelectedLift.recorded trace receiver true
  let mut execution : LiftExecution := {
    selections := #[], actions := #[], parameters := #[], sources := #[], bases := #[], outputs := #[] }
  let mut dependencies := #[]
  for (segment, plans) in recorded.segments do
    let (wire, retained) ← retainedLiftExecution h trace segment
    unless retained.selections.size == plans.size do
      throwError "a composed lift packet changed the number of its selected stages"
    for (expected, actual) in plans.zip retained.selections do
      checkRetainedLiftPlan expected actual
    execution := {
      selections := execution.selections ++ retained.selections
      actions := execution.actions ++ retained.actions
      parameters := execution.parameters ++ retained.parameters
      sources := execution.sources ++ retained.sources
      bases := execution.bases ++ retained.bases
      outputs := execution.outputs ++ retained.outputs
      actionOwnership := execution.actionOwnership ++ retained.actionOwnership
      parameterOwnership := execution.parameterOwnership ++ retained.parameterOwnership
      sourceOwnership := execution.sourceOwnership ++ retained.sourceOwnership
      baseOwnership := execution.baseOwnership ++ retained.baseOwnership
      outputOwnership := execution.outputOwnership ++ retained.outputOwnership }
    dependencies := dependencies.push wire
  let some first := execution.selections[0]?
    | throwError "the composed lift has no complete retained stage"
  let some original := dependencies[0]? | unreachable!
  unless ← withTransparency .all <| isDefEq (← SelectedLift.port execution.selections 0) formal do
    throwError "the composed lift changed its original formal object"
  let context ← SelectedLift.context first
  return {
    form := contextualForm (← registryState) context original.form
    payload := (← scopedPayload formal (← liftProjectionFragment execution 0))
    liftExecution := some execution
    categoryContext := some context
    serviceHandles := (← retainLiftOperands h dependencies) }

partial def selectedLiftExecution (h : Harness) (trace : Trace) (plan : SelectedLift.Plan)
    (formal : Expr) : TermElabM Wire := do
  let state ← registryState
  let inner ← SelectedLift.innerEdge state plan.entry
  let captured ← capturedEdgeData h trace inner plan.action
  let (action, actionWires) ← renderActionDataWith (observeActionDataWire h trace) captured
  let source ← realizeEndpoint h trace "the selected lift's original source object" plan.source
  let inclusion ← realize h trace "the selected lift's complete base inclusion" plan.inclusion
  let some (baseSource, baseTarget) := Language.homEnds? (← inferType plan.inclusion)
    | throwError "the selected lift lost its original base inclusion endpoints"
  let baseSource ← realizeEndpoint h trace "the selected lift's base apex" baseSource
  let baseTarget ← if (← trace.node? baseTarget).isSome || (← h.results.get).contains baseTarget then
    realizeEndpoint h trace "the selected lift's exact image ambient" baseTarget
  else do
    let context ← SelectedLift.context plan true
    let data ← scopedNode "functorAction" #[action, source.fragment]
    let image : Wire := {
      form := contextualForm state context source.form
      payload := (← combinedRecipePayload baseTarget data (#[source] ++ actionWires))
      categoryContext := some context }
    retainActionInput false inner plan.action source image captured
  let base ← scopedNode "subobject" #[baseSource.fragment, baseTarget.fragment, inclusion.fragment]
  let (parameters, parameterWires) ← realizedParameterData h trace plan.parameters
  let some form := state.liftInputForm? plan.entry.inputAddress
    | throwError "the selected lift has no published complete input form"
  let parameterData := DataOwnership.Data.array parameters
  let baseOperand ← selectedLiftBaseOperand plan form base
  let dependencies := #[source, inclusion, baseSource, baseTarget, baseOperand] ++
    parameterWires ++ actionWires
  let mut outputs : Array DataOwnership.Data := #[]
  let mut outputWires : Array Wire := #[]
  for field in LiftField.all do
    let request ← liftStageData "monoLiftInput" plan.entry.id.raw parameterData
      action source.fragment base outputs
    let input : Wire := {
      form, payload := (← recipePayload formal request)
      serviceHandles := (← retainLiftOperands h (dependencies ++ outputWires)) }
    let operation := plan.entry.fieldAddress field
    let reply ← sendData h operation input
    outputs := outputs.push reply.data
    match ← LiftedSubobjectData.validateSelectionPrefix plan action.json source.json base.json
        (outputs.map (·.json)) with
    | .error message => malformed reply.backend operation reply.data.json message
    | .ok () => pure ()
    let position := outputWires.size
    let context ← SelectedLift.context plan (position >= 2)
    let output ← liftOperand plan.ports[position]! context form reply.data (position != 0) true
    outputWires := outputWires.push { output with serviceHandles := input.serviceHandles }
  let context ← SelectedLift.context plan
  let execution : LiftExecution := {
    selections := #[plan], actions := #[action.json], parameters := #[parameters.map (·.json)],
    sources := #[source.json], bases := #[base.json], outputs := #[outputs.map (·.json)]
    actionOwnership := #[action.ownership], parameterOwnership := #[parameterData.ownership]
    sourceOwnership := #[source.ownership], baseOwnership := #[base.ownership]
    outputOwnership := #[outputs.map (·.ownership)] }
  let handles ← retainLiftOperands h (dependencies ++ outputWires)
  cacheLiftFields h execution none handles
  return {
    form := contextualForm state context source.form
    payload := (← scopedPayload formal outputs[0]!)
    liftExecution := some execution
    categoryContext := some context, serviceHandles := handles }

/-- Every stage's actual returned factor becomes the next stage's base map. The formal
plans supply domain equations; no returned value can choose a lift or certify a factor. -/
partial def executeLiftFactor (h : Harness) (trace : Trace) (formal receiver baseMap cone proof : Expr) :
    TermElabM Wire := do
  let state ← registryState
  let (liftWire, execution) ← retainedLiftExecution h trace receiver
  let steps ← SelectedLift.factors execution.selections baseMap cone proof
  let baseWire ← realize h trace "the factor's original complete base map" baseMap
  let coneWire ← realize h trace "the factor's original complete source cone" cone
  let some (domain, _) := Language.homEnds? (← inferType cone)
    | throwError "the factor cone lost its original generalized domain"
  let domainWire ← realizeEndpoint h trace "the factor's original generalized domain" domain
  let originalBase ← execution.baseFragment (execution.bases.size - 1)
  let .ok _ := LiftedSubobjectData.subobjectFields originalBase.json
    | throwError "the factor lost the selected original complete base"
  let originalApex ← checkedFragment (originalBase.project #[.field "args", .index 0])
  let mut domains := #[]
  let mut cones := #[]
  let mut currentDomain := domainWire.fragment
  let mut currentCone ← scopedNode "typedMap"
    #[currentDomain, ← execution.sourceFragment 0, coneWire.fragment]
  for index in [:execution.selections.size] do
    domains := domains.push currentDomain
    cones := cones.push currentCone
    let action ← execution.actionFragment index
    currentDomain ← scopedNode "functorAction" #[action, currentDomain]
    let target ← scopedNode "functorAction" #[action, ← execution.sourceFragment index]
    currentCone ← scopedNode "typedMap" #[currentDomain, target,
      ← scopedNode "map" #[action, currentCone]]
  let mut currentBase ← scopedNode "typedMap" #[currentDomain, originalApex, baseWire.fragment]
  let mut baseObserved := baseWire.callableObserved
  let mut handles : Array Nat := #[]
  for (index, step) in (List.range execution.selections.size).reverse.toArray.zip steps do
    let some selection := execution.selections[index]? | unreachable!
    let .ok baseMap := Backend.TypedMap.decode currentBase.json
      | throwError "the factor's preceding actual output lost its complete typed map"
    let .ok cone := Backend.TypedMap.decode cones[index]!.json
      | throwError "the factor's actual cone lost its complete original endpoints"
    let invocation : Backend.LiftFactorInput := {
      lift := selection.entry.id.raw, action := execution.actions[index]!,
      source := execution.sources[index]!, base := execution.bases[index]!,
      outputs := execution.outputs[index]!, parameters := execution.parameters[index]!, baseMap, cone }
    let some form := state.liftInputForm? selection.entry.inputAddress
      | throwError "the selected factor has no published complete input form"
    let request ← placedData invocation.encode #[
      (#[.field "parameters"], ← execution.parameterFragment index),
      (#[.field "args", .index 1], ← execution.actionFragment index),
      (#[.field "args", .index 2], ← execution.sourceFragment index),
      (#[.field "args", .index 3], ← execution.baseFragment index),
      (#[.field "args", .index 4], DataOwnership.Data.array (← execution.outputFragments index)),
      (#[.field "args", .index 5], ← retagLiftMap "typedMap" currentBase),
      (#[.field "args", .index 6], ← retagLiftMap "typedMap" cones[index]!)]
    let baseOperand ← liftOperand step.baseMap (← SelectedLift.context selection true)
      baseWire.form (← retagLiftMap "typedMap" currentBase) true baseObserved
    let coneOperand ← liftOperand step.cone (← SelectedLift.context selection)
      coneWire.form cones[index]! true (index == 0 && coneWire.callableObserved)
    handles ← retainLiftOperands h #[liftWire, baseWire, coneWire, domainWire, baseOperand, coneOperand]
    let input : Wire := {
      form, payload := (← recipePayload formal request), serviceHandles := handles }
    let operation := selection.entry.factorAddress
    let reply ← sendData h operation input
    let answer := reply.data.json
    let backend := reply.backend
    match ← LiftedSubobjectData.validateMap step.factor domains[index]!.json
        (execution.outputs[index]!)[0]! answer with
    | .error message => malformed backend operation answer message
    | .ok () => pure ()
    currentBase := reply.data
    baseObserved := true
  let some last := steps.back? | throwError "the universal factor has no selected final stage"
  unless ← withTransparency .all <| isDefEq last.factor formal do
    throwError "the staged universal factor changed its independently fixed formal value"
  let some selection := execution.selections[0]? | unreachable!
  let context ← SelectedLift.context selection
  return {
    form := contextualForm state context coneWire.form true
    payload := (← scopedPayload formal currentBase)
    categoryContext := some context, serviceHandles := handles }

/-- Evaluate the recorded term `e`, the value of `what`, to a value of a form, through the
admitted registrations. -/
partial def realize (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let e ← instantiateMVars e
  let closed := !e.hasMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars
  let cached ← if closed then pure ((← h.results.get)[e]?) else pure none
  let wire ← match cached with
    | some wire => pure wire
    | none => realizeFresh h trace what e
  -- An installed operation computes its own result before a later consumer sees
  -- it. A portable expression remains available when no complete registration
  -- applies; a failed or ambiguous dispatch is never retried as an expression.
  let wire ← match ← trace.node? e with
    | some (.operationApply ..) | some (.operationPoint ..) |
        some (.operationEquivalence ..) => realizeArrowObservation h trace wire true
    | some (.limit ..) => realizeObjectObservation h trace wire
    | some (.limitProjection ..) => realizeArrowObservation h trace wire
    | some (.structuredProjection _ _ (some _)) =>
      if (Language.homEnds? (← inferType wire.value)).isSome then
        realizeArrowObservation h trace wire else realizeObjectObservation h trace wire
    | some (.morphismTransport ..) | some (.constructionMap ..) |
        some (.contextualRoute _ _ _ _ _ true) =>
      if h.demandObjectActions then realizeArrowObservation h trace wire else pure wire
    | _ => pure wire
  let wire ← if h.demandObjectActions then do
      let wire ← realizeValueObservation h trace wire
      realizeObjectObservation h trace wire
    else pure wire
  -- A completed construction supplies its own exact apex expression. Its
  -- checked presentation can differ syntactically from the reader's original
  -- limit expression, and a subsequent selected action is applied to this
  -- actual apex. Retain that precise occurrence with its complete packet and
  -- owners; never reconstruct it by searching for an equal carrier or JSON.
  if let .construction .. := wire.payload then
    let apex := wire.value
    unless apex.hasMVar || apex.hasLevelMVar || apex.hasFVar || apex.hasLooseBVars do
      h.results.modify (·.insert apex wire)
  if closed then
    if wire.liftExecution.isSome then
      h.results.modify (·.insert e wire)
    else
      match wire.payload with
      | .ordinary .. => pure ()
      | .computed .. | .construction .. => h.results.modify (·.insert e wire)
  return wire

/-- Prepare a candidate's public recipe without selecting its own registration.
Operation equivalence checks every retained candidate before a single dispatch.
Already returned data retain their exact owning session and observed status. -/
partial def realizeUnobserved (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let e ← instantiateMVars e
  if !e.hasMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars then
    if let some wire := (← h.results.get)[e]? then return wire
  realizeFresh h trace what e

/-- Supply the same recursive operations to the separately compiled node evaluator. -/
partial def realizeFresh (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire :=
  realizeFreshWith elementFragment realizedParameterData realizedEdgeData capturedEdgeData
    capturedParameterData capturedCallableParameters captureSelectedCallable
    actionMapEndpoint realizeObjectObservation
    (fun h trace wire => realizeArrowObservation h trace wire)
    computationalOperationReceiver extentFragment?
    (fun h trace what value recoverAction recoverNamed =>
      realizeEndpoint h trace what value recoverAction recoverNamed)
    (fun h trace wire value source context =>
      realizeCallableEndpoint h trace wire value source context)
    (fun h trace source target wire context pointAsMap =>
      frameMorphismFragment h trace source target wire context pointAsMap)
    (fun h trace input context endpoints publicFrame =>
      captureCompleteCallable h trace input context endpoints publicFrame)
    callableObjectPlan? pointAtAdmissionDomain wholeCallablePoint realizeObjectPresentation
    contextualAction captureMapRoute captureConstructionMap contextualComposition
    structuredProjection captureConstructionLeg retainedLiftExecution
    composedLiftExecution selectedLiftExecution executeLiftFactor realize realizeUnobserved
    realizeFresh h trace what e

/-- An accepted operation's actual owner is the declaration argument preceding
its numeral parameters. Its set-valued source and result do not select that owner. -/
partial def realizedOperationOwner (h : Harness) (trace : Trace) (entry : OperationEntry)
    (application : Expr) (actual : Option Wire := none) : TermElabM Wire := do
  let state ← registryState
  let arguments := (operationApplicationBody application).getAppArgs
  let some receiver := arguments[arguments.size - 1 - entry.numerals]?
    | throwError "the complete operation lost its declared owner parameter"
  let some category := state.categories.find? (·.id == entry.category)
    | throwError "the complete operation lost its accepted owner category"
  let receiverContext ← CategoryContext.ofNamed category receiver
  let wire ← match actual with
    | some actual => pure actual
    | none => try
        realizeEndpoint h trace "the operation's exact declared owner" receiver
      catch error =>
        unless Exception.stratum? error == some .noImplementation do throw error
        let (data, dependencies) ← realizedParameterData h trace #[receiver]
        let #[data] := data | throwError "the operation's declared owner lost its parameter data"
        let retained : Wire := {
          form := .diagrams category
          payload := (← combinedRecipePayload receiver data dependencies)
          categoryContext := some receiverContext }
        pure retained
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType wire.value) (← inferType receiver) <&&>
        isDefEq wire.value receiver) do
    throwError "the operation's actual owner changed its complete declaration argument"
  discard <| framingContext (some receiverContext) wire.categoryContext
  unless state.accepts (.operation entry) wire.form do
    throwError "the complete operation's owner representation changed its declared category"
  return wire

/-- Bind the owner's data at its declaration-relative parameter occurrence.
Administrative wrappers need not be the same cache key. No equal carrier or
equal packet selects an occurrence, and all other parameters keep their own
retained data and suppliers. -/
partial def realizedOperationParameterData (h : Harness) (trace : Trace)
    (entry : OperationEntry) (application : Expr) (parameters : Array Expr)
    (owner : Wire) (retained : Option (Array OperationParameterOccurrence) := none) :
    TermElabM (Array DataOwnership.Data × Array Wire × Array OperationParameterOccurrence) := do
  let application := operationApplicationBody application
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun arguments _ =>
    arguments.mapM (·.fvarId!.getBinderInfo)
  unless application.getAppNumArgs == infos.size && infos.size > entry.numerals do
    throwError "the operation parameters lost their complete declaration telescope"
  let ownerSlot := infos.size - 1 - entry.numerals
  let ownerParameter := if infos[ownerSlot]!.isExplicit then
      some (((infos.extract 0 ownerSlot).filter (·.isExplicit)).size)
    else none
  unless parameters.size == (infos.filter (·.isExplicit)).size do
    throwError "the operation changed its ordered explicit parameters"
  if let some retained := retained then
    unless retained.size == parameters.size do
      throwError "the operation lost its retained ordered parameter occurrences"
  let mut data := #[]
  let mut dependencies := #[]
  let mut occurrences := #[]
  for index in [:parameters.size] do
    let parameter := parameters[index]!
    let occurrence : OperationParameterOccurrence ← if some index == ownerParameter then do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType parameter) (← inferType owner.value) <&&>
            isDefEq parameter owner.value) do
        throwError "the operation parameter changed its complete selected owner"
      pure { formal := parameter, data := #[owner.fragment]
        dependencies := #[{ owner with payload := forwardPayload owner parameter owner.json }] }
    else if let some retained := retained then do
      let previous := retained[index]!
      unless previous.formal == parameter do
        throwError "the operation changed an original nonowner parameter occurrence"
      pure previous
    else do
      let (fields, inputs) ← realizedParameterData h trace #[parameter]
      pure { formal := parameter, data := fields, dependencies := inputs }
    data := data ++ occurrence.data
    dependencies := dependencies ++ occurrence.dependencies
    occurrences := occurrences.push occurrence
  return (data, dependencies, occurrences)

/-- The element producer retains its exact owner and expression inputs. Neither
an equal formal cache key nor a later trace replay can replace those occurrences. -/
partial def operationPointRecipeInputs (_h : Harness) (_trace : Trace) (point : Wire) :
    TermElabM (Array Wire) := do
  if point.completedData || point.callableObserved then
    throwError "a completed point cannot select an unobserved operation recipe interface"
  if let some origin ← retainedPointOrigin? point then
    if let .element owner dependencies := origin.recipe then
      return #[owner] ++ dependencies
    return #[]
  if (point.json.getObjValAs? String "ctor").toOption == some "element" then
    throwStratum .noImplementation "the original element has no retained producer occurrence"
  return #[]

/-- Read input presentation occurrences through their retained point roles.
A product is decomposed only through its producer's exact ordered children and
encoding positions. No trace replay or expression lookup selects those inputs. -/
partial def operationPointPresentations (h : Harness) (trace : Trace)
    (context : CategoryContext) (role : OperationEndpointRole) (point : Wire)
    (domain target : Expr) (domainWire : Wire) (data : DataOwnership.Data)
    (bindings : Array OperationPointPresentation := #[]) :
    TermElabM (Array OperationPointPresentation × Bool × Array Wire) := do
  CategoryContext.checkMorphism context point.value domain target
  discard <| framingContext (some context) point.categoryContext
  discard <| checkedFragment data.validate
  match role with
  | .field path =>
    if point.completedData || point.callableObserved then return (bindings, false, #[])
    let some (pointDomain, pointTarget) := Language.homEnds? (← inferType point.value)
      | throwError "the original operation point lost its complete declared endpoints"
    let .ok unwrapped := ComputationalData.valuePayload data.json
      | throwError "the retained operation point has an incomplete value envelope"
    -- A generalized mediator retains its raw child occurrence. A closed product
    -- may already contain the ordinary typed-map framing of that same child.
    -- Both are reproduced before any normalized presentation is introduced.
    let endpoints ← match ← retainedPointOrigin? point with
      | some origin => pure (some (origin.source, origin.target))
      | none => do
        let source ← retainedCallableEndpoint? point pointDomain true (some context)
        let target ← retainedCallableEndpoint? point pointTarget false (some context)
        pure (source.bind fun source => target.map fun target => (source, target))
    let some (sourceWire, targetWire) := endpoints | return (bindings, false, #[])
    let sourceWire ← forwardRetainedValue sourceWire pointDomain
    let targetWire ← forwardRetainedValue targetWire pointTarget
    if data != point.fragment then
      let (framed, _) ← frameRetainedPoint context point sourceWire targetWire
      unless framed == data do
        throwStratum .unavailable "the operation point changed its retained computational occurrence"
    if (unwrapped.getObjValAs? String "ctor").toOption == some "typedMap" then
      let sourceData ← checkedFragment (← ComputationalData.interfaceEndpointData
        #[] point.value data true false)
      let targetData ← checkedFragment (← ComputationalData.interfaceEndpointData
        #[] point.value data false false)
      unless sourceWire.fragment == sourceData && targetWire.fragment == targetData do
        throwStratum .noImplementation
          "the operation point has no retained complete endpoint presentation"
    checkOperationPointPresentation sourceWire
    checkOperationPointPresentation domainWire
    unless sameOperationPointPresentation sourceWire domainWire do
      throwStratum .noImplementation
        "the operation point has a distinct complete generalized-domain presentation"
    if sourceWire.json == targetWire.json &&
        !sameOperationPointPresentation sourceWire targetWire then
      throwStratum .ambiguousRealization
        "the operation point repeats endpoint bytes in different complete contexts"
    let recipeInputs ← operationPointRecipeInputs h trace point
    let mut inputs : Array Wire := #[]
    for input in #[sourceWire, targetWire] ++ recipeInputs do
      checkOperationPointPresentation input
      for previous in inputs do
        if previous.json == input.json && !sameOperationPointPresentation previous input then
          throwStratum .ambiguousRealization
            "the point recipe repeats a descriptor in distinct complete input contexts"
      inputs := inputs.push input
    let bindings ← bindOperationPointPresentation bindings path targetWire
    return (bindings, true, #[point] ++ inputs)
  | .product leftRole rightRole =>
    let some origin ← retainedPointOrigin? point | return (bindings, false, #[])
    let .product _ retainedDomain first second firstPath secondPath := origin.recipe
      | return (bindings, false, #[])
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType retainedDomain) (← inferType domain) <&&>
          isDefEq retainedDomain domain) do
      throwError "the original product point changed its complete domain"
    if data != point.fragment then
      let (framed, _) ← frameRetainedPoint context point origin.source origin.target
      unless framed == data do
        throwStratum .unavailable "the product point changed its retained computational occurrence"
    let componentPaths := #[firstPath, secondPath]
    let product ← withTransparency .all <| whnf target
    unless product.isAppOfArity ``Prod 2 do
      throwError "the original product point changed its declared target"
    let coordinates := product.getAppArgs
    let firstData ← checkedFragment (origin.fragment.project componentPaths[0]!)
    let secondData ← checkedFragment (origin.fragment.project componentPaths[1]!)
    let (bindings, leftComplete, firstEndpoints) ← operationPointPresentations h trace context
      leftRole first domain coordinates[0]! domainWire firstData bindings
    let (bindings, rightComplete, secondEndpoints) ← operationPointPresentations h trace context
      rightRole second domain coordinates[1]! domainWire secondData bindings
    return (bindings, leftComplete && rightComplete, firstEndpoints ++ secondEndpoints)

/-- Reconstruct only the declared product of the already bound endpoint data.
This does not inspect values to infer a product or choose a field presentation. -/
partial def operationPresentationData (role : OperationEndpointRole)
    (bindings : Array OperationPointPresentation) : TermElabM DataOwnership.Data := do
  match role with
  | .field path =>
    let some binding := bindings.find? fun binding => sameOperationFieldPath binding.path path
      | throwError "the complete operation source omitted a declared presentation role"
    return binding.endpoint.fragment
  | .product left right =>
    scopedNode "objectProduct" #[← operationPresentationData left bindings,
      ← operationPresentationData right bindings]

/-- Supply the exact realizer operations to the separately compiled argument
builder. The callbacks retain this same harness and trace; no alternate
selection, decoding rule or execution policy is introduced. -/
partial def prepareOperationPointArgument (h : Harness) (trace : Trace)
    (context : CategoryContext) (point originalDomain originalTarget domain target : Wire)
    (data : DataOwnership.Data) (parameters : Array Wire) : TermElabM PreparedOperationArgument :=
  prepareOperationPointArgumentWith
    (fun point => operationPointRecipeInputs h trace point)
    h context point originalDomain originalTarget domain target data parameters

/-- A pending operation uses one presentation for every occurrence of a
declared field role. The full actual owner stays in the operation parameters.
Already returned callables and unrelated map-action endpoints never enter here. -/
partial def operationPointEndpoints? (h : Harness) (trace : Trace) (context : CategoryContext)
    (entry : OperationEntry) (application : Expr) (receiver point : Wire)
    (domain source target : Expr) (domainWire : Wire) (data : DataOwnership.Data)
    (parameters : Array Wire) : TermElabM (Option PreparedOperationPoints) := do
  let some (sourceRole, targetPath) ← operationPointRoles? entry application receiver | return none
  -- Metadata inspection may reuse completed inputs, but it cannot start a new
  -- implementation merely to recover an endpoint presentation.
  let inspect := { h with
    admitted := #[]
    backends := #[]
    deferred := none
    derivation := none
    dispatches := none
    demandObjectActions := false }
  let (bindings, complete, dependencies) ← operationPointPresentations inspect trace context
    sourceRole point domain source domainWire data
  if bindings.isEmpty then return none
  unless complete do
    throwStratum .noImplementation
      "the original operation points do not retain one complete presentation for every source role"
  let some sourceWire ← retainedCallableEndpoint? point source false (some context)
    | throwStratum .noImplementation
        "the operation argument has no retained complete source endpoint occurrence"
  checkOperationPointPresentation sourceWire
  let sourceData ← operationPresentationData sourceRole bindings
  unless sourceWire.fragment == sourceData do
    throwStratum .noImplementation
      "the operation source differs from its original complete point presentations"
  match sourceRole with
  | .field path =>
    let some selected := bindings.find? fun binding => sameOperationFieldPath binding.path path
      | throwError "the complete operation source lost its retained endpoint presentation"
    unless sameOperationPointPresentation sourceWire selected.endpoint do
      throwStratum .noImplementation
        "the operation source changed its complete retained point context"
  | .product .. =>
    unless (← checkOperationProductContext context sourceRole sourceWire bindings) == bindings.size do
      throwError "the operation product changed its complete ordered role inventory"
  let mut targetWire := none
  if let some selected := bindings.find? fun binding => sameOperationFieldPath binding.path targetPath then
    let endpoint := selected.endpoint
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType endpoint.value) (← inferType target) <&&>
          isDefEq endpoint.value target) do
      throwError "the declared result field changed its independently selected complete endpoint"
    CategoryContext.checkObject context target
    discard <| framingContext (some context) endpoint.categoryContext
    targetWire := some { endpoint with payload := forwardPayload endpoint target endpoint.json }
  -- Fix the actual domain and source before constructing the argument packet.
  -- The same normalization applies to every exact retained occurrence, rather
  -- than adding comparison metadata only after an invocation has been framed.
  let (parameters, _) ← normalizeOperationProducts h context parameters #[]
  let targetInputs := (targetWire.map fun wire => #[wire]).getD #[]
  let (normalized, _) ← normalizeOperationProducts h context
    (#[domainWire, sourceWire] ++ targetInputs ++ dependencies) parameters
  let some actualDomain := normalized[0]?
    | throwError "the operation point lost its complete normalized domain"
  let some actualSource := normalized[1]?
    | throwError "the operation point lost its complete normalized source"
  let actualTarget := if targetWire.isSome then normalized[2]? else none
  let argument ← prepareOperationPointArgument inspect trace context point domainWire sourceWire
    actualDomain actualSource data parameters
  return some {
    domain := actualDomain, source := actualSource, target := actualTarget
    argument := argument.data
    dependencies := normalized.extract (2 + targetInputs.size) normalized.size ++
      argument.dependencies }

/-- Prepare an operation's actual complete request without dispatching it. This
also covers nullary and staged operations, using their original typed argument. -/
partial def prepareOperationObservation (h : Harness) (trace : Trace) (wire : Wire)
    (id : OperationId) (parameters : Array Expr) (actualOwner : Option Wire := none)
    (retained : Option OperationObservation := none)
    (objects : ComputationalData.InterfaceObjects := #[])
    (initialParameters : Option (Array OperationParameterOccurrence) := none) :
    TermElabM OperationObservation := do
  let h := { h with demandObjectActions := false }
  if let some actual := operationRecipeId? wire then
    unless actual == id.raw do
      throwError "the retained operation recipe changed its accepted operation"
  let state ← registryState
  let some entry := state.operations.find? (·.id == id)
    | throwError "the retained operation is no longer registered"
  let formal := wire.value
  if let some retained := retained then
    unless retained.original.value == formal && retained.operation == id &&
        retained.parameters == parameters do
      throwError "the operation rebuild changed its original selected request"
  let namedRecipe ← match ← trace.node? formal with
    | some (.namedCallable address _ _) => pure (address == id.raw &&
        (wire.json.getObjValAs? String "ctor").toOption == some address)
    | _ => pure false
  let (arguments, operation) := operationApplicationSpine formal
  let application := operationApplicationBody operation
  unless application.getAppFn.constName? == some entry.declaration do
    throwError "the complete operation recipe changed its accepted declaration"
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun arguments _ =>
    arguments.mapM (·.fvarId!.getBinderInfo)
  unless application.getAppNumArgs == infos.size do
    throwError "the complete operation recipe lost its full declaration application"
  let actualParameters := (application.getAppArgs.zip infos).filterMap fun (value, info) =>
    if info.isExplicit then some value else none
  unless actualParameters.size == parameters.size do
    throwError "the complete operation recipe changed its ordered declaration parameters"
  for (actual, retained) in actualParameters.zip parameters do
    unless ← withTransparency .all <| isDefEq actual retained do
      throwError "the complete operation recipe changed a selected declaration parameter"
  let some (source, target) := Language.homEnds? (← inferType operation)
    | throwError "the accepted operation lost its complete callable signature"
  let some dataCategory := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the point invocation's declared data category is absent"
  let dataContext ← CategoryContext.ofNamed dataCategory source
  CategoryContext.checkMorphism dataContext operation source target
  let argument ← match arguments[0]? with
    | none => do
      let identity ← identityAtContext dataContext source
      Trace.record (some trace) identity (.contextualIdentity dataContext source)
      pure identity
    | some first => do
      let mut argument := first
      for next in arguments.extract 1 arguments.size do
        let some (domain, middle) := Language.homEnds? (← inferType argument)
          | throwError "the operation's staged argument lost its complete source"
        let some (nextSource, target) := Language.homEnds? (← inferType next)
          | throwError "the operation's staged argument lost its complete target"
        unless ← withTransparency .all <| isDefEq middle nextSource do
          throwError "the operation's staged argument changed a selected intermediate endpoint"
        let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[argument, next]
        CategoryContext.checkMorphism dataContext composite domain target
        Trace.record (some trace) composite
          (.contextualComposition dataContext argument next domain middle target)
        argument := composite
      pure argument
  let some (domain, originalSource) := Language.homEnds? (← inferType argument)
    | throwError "the retained operation argument lost its original generalized domain"
  let some (resultDomain, resultTarget) := Language.homEnds? (← inferType formal)
    | throwError "the complete operation result lost its original typed endpoints"
  unless ← withTransparency .all <| isDefEq originalSource source <&&>
      isDefEq resultDomain domain <&&> isDefEq resultTarget target do
    throwError "the complete operation recipe changed its original composition endpoints"
  unless ← withTransparency .all <|
      isDefEq formal (← mkAppM ``CategoryTheory.CategoryStruct.comp #[argument, operation]) do
    throwError "the complete operation recipe changed its original typed composition"
  let receiverWire ← realizedOperationOwner h trace entry application actualOwner
  let (recordSource, recordTarget) ← operationRecordEndpointData entry application receiverWire objects
  let (parameterData, parameterWires, parameterOccurrences) ←
    realizedOperationParameterData h trace entry application parameters receiverWire
      ((retained.map (·.parameterOccurrences)).orElse fun _ => initialParameters)
  let callable : Wire := {
    form := wire.form
    payload := (← combinedRecipePayload operation
      (← scopedNode id.raw parameterData) parameterWires) }
  let argumentWire ← match retained with
    | some retained => pure retained.argument
    | none => realize h trace "the operation's original generalized argument" argument
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType argumentWire.value) (← inferType argument) <&&>
        isDefEq argumentWire.value argument) do
    throwError "the operation changed its retained generalized argument occurrence"
  -- The original complete result retains the reader's selected endpoint presentations.
  -- The stripped declaration supplies the internal callable signature checked above.
  let argumentDomain ← match retained with
    | some retained => pure retained.argumentDomain
    | none => realizeCallableEndpoint h trace argumentWire resultDomain true
  let domainWire := argumentDomain
  let pointEndpoints ← if !wire.callableObserved && !wire.completedData &&
      operationRecipe wire id && recordSource.isSome && recordTarget.isSome then
    operationPointEndpoints? h trace dataContext entry application receiverWire argumentWire
      resultDomain originalSource resultTarget domainWire argumentWire.fragment parameterWires
  else pure none
  let (argumentData, endpoints) ← match pointEndpoints with
    | some prepared => pure (prepared.argument, prepared.dependencies)
    | none => match retained with
      | some retained => pure (retained.argumentData, retained.argumentDependencies)
      | none => frameMorphismFragment h trace resultDomain originalSource argumentWire
  let domainWire := (pointEndpoints.map (·.domain)).getD domainWire
  -- The argument's actual target supplies the selected input presentation. The
  -- declaration may expose only a reduced carrier with several accepted names;
  -- its complete equality with this original endpoint was checked above.
  let sourceWire ← match pointEndpoints with
    | some prepared => pure prepared.source
    | none => match recordSource with
      | some data => pure {
          form := .diagrams dataCategory
          payload := (← scopedPayload originalSource data receiverWire.completedData)
          categoryContext := some dataContext }
      | none => match retained with
        | some retained => pure retained.sourceWire
        | none => realizeCallableEndpoint h trace argumentWire originalSource false
  let targetEndpoint : CallableEndpointData ← match pointEndpoints.bind (·.target) with
    | some target => pure { wire := target, origin := .retained }
    | none => match recordTarget with
      | some data => pure { origin := .retained, wire := {
          form := .diagrams dataCategory
          payload := (← scopedPayload resultTarget data receiverWire.completedData)
          categoryContext := some dataContext } }
      | none => match retained with
        | some retained =>
          if retained.targetOrigin == .reference then do
            let context ← framingContext (some dataContext) retained.targetWire.categoryContext
            pure { origin := .reference
              wire := ← callableEndpointReference callable resultTarget false context }
          else pure { wire := retained.targetWire, origin := .retained }
        | none => realizeCallableEndpointWithOrigin h trace callable resultTarget false
            (some dataContext)
  let targetWire := targetEndpoint.wire
  for (endpoint, expected) in #[(domainWire, resultDomain), (sourceWire, originalSource),
      (targetWire, resultTarget)] do
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType endpoint.value) (← inferType expected) <&&>
          isDefEq endpoint.value expected) do
      throwError "the operation changed a retained complete endpoint occurrence"
  let callable ← if pointEndpoints.isSome then do
      let dataParameters ← DirectConstruction.dataArguments parameters
      unless dataParameters.size == parameterData.size do
        throwError "the operation presentation lost a complete parameter occurrence"
      let mut objects : ComputationalData.InterfaceObjects := objects
      for (data, parameter) in parameterData.zip dataParameters do
        for (previous, selected) in objects do
          if previous == data.json && selected != parameter then
            throwStratum .ambiguousRealization
              "the operation parameters repeat bytes in distinct complete selected contexts"
        objects := objects.push (data.json, parameter)
      if let .error message ← ComputationalData.validateCallableAt objects
          (← inferType operation) callable.json then
        throwStratum .malformed m!"the retained operation has incompatible complete parameters: {message}"
      presentMorphism callable sourceWire targetWire (some dataContext)
    else pure callable
  let invocation ← pointInvocationData id.raw parameterData callable.fragment
    domainWire.fragment sourceWire.fragment targetWire.fragment argumentData
  let operands := #[wire, receiverWire, callable, argumentWire, domainWire, sourceWire, targetWire] ++
    parameterWires ++ endpoints
  let handles ← if pointEndpoints.isSome then do
      let (_, handles) ← normalizeOperationProducts h dataContext operands parameterWires
      pure handles
    else retainServiceOperands h operands
  let input : Wire := {
    form := receiverWire.form
    payload := (← combinedRecipePayload formal invocation operands)
    serviceHandles := handles }
  return {
    original := wire
    operation := id
    trace, parameters, parameterOccurrences, owner := receiverWire
    argument := argumentWire, argumentDomain, argumentData, argumentDependencies := endpoints
    domainWire, sourceWire, targetWire, targetOrigin := targetEndpoint.origin
    input
    domain := resultDomain
    target := resultTarget
    targetData := targetWire.json
    materialized := wire.actualData || wire.callableObserved ||
      (!namedRecipe && !operationRecipe wire id) }

/-- Inspect one owner through current typed producers. The inspection harness
cannot dispatch, derive, or mutate live caches; only its resulting supplier
constraints will be used by ordinary registration admission. -/
partial def prospectiveOwnerData (h inspect : Harness) (trace : Trace) (owner : Wire)
    (inputs : Array Wire := #[]) :
    TermElabM (Wire × ComputationalData.InterfaceObjects) := do
  let receipts ← h.actions.get
  let reserved := prospectiveReservedWire owner ++ inputs.flatMap prospectiveReservedWire ++
    (← h.serviceOperands.get).flatMap prospectiveReservedWire ++
    (← h.results.get).toArray.flatMap (fun (_, wire) => prospectiveReservedWire wire) ++
    receipts.flatMap (fun receipt => #[Json.arr receipt.parameters] ++
      (#[receipt.input, receipt.result] ++ receipt.parameterInputs ++ receipt.imageEndpoints).flatMap
        prospectiveReservedWire)
  let state ← IO.mkRef ({ reserved } : ProspectiveData)
  let reader : ProspectiveReader := {
    live := h, inspect, trace, state
    objectTemplate := fun recipe original descriptor dependencies => do
      match recipe.owner with
      | .edge selected =>
          let encoder : ScopedActionEncoder := fun edge action => do
            unless edge == selected && (← withoutModifyingState (withTransparency .all <|
                isDefEq (← inferType action) (← inferType recipe.application) <&&>
                  isDefEq action recipe.application)) do
              throwError "the prospective descriptor changed its complete selected action"
            return (descriptor, dependencies)
          let (template, _, _) ← objectActionTemplate inspect trace selected
            recipe.application original (some encoder)
          pure template
      | .construction id _ =>
          capturedConstructionObjectTemplate id recipe.application recipe.target descriptor dependencies original
    invocation := fun owner descriptor morphism => do
      match owner with
      | .edge edge => edgeActionDataInvocation (← registryState) edge descriptor morphism
      | .construction id _ =>
          let some entry := (← registryState).constructions.find? (·.id == id)
            | throwError "the prospective construction lost its accepted operation"
          return (if morphism then entry.mapAddress else id.raw,
            ← capturedConstructionParameters id descriptor)
    endpoints := fun wire context => capturedMapEndpoints inspect trace wire context true }
  let owner ← prospectiveWireWith reader .object owner
  return (owner, (← state.get).objects)

/-- Admission projects only unfinished action output slots. Nested intrinsic
records retain every actual sibling and its suppliers. Future references are
bound solely in an isolated metadata harness; no projected Wire, cache entry,
service handle, receipt, or invocation escapes this check. -/
partial def operationObservationRegistrations (h : Harness) (request : OperationObservation) :
    TermElabM (Array Admitted) := do
  checkDataOwners h request.input.fragment
  if request.owner.objectObserved || request.owner.actualData then
    return ← admittedRegistrations h request.operation.raw request.input true
  let privateTrace ← IO.mkRef (← request.trace.get)
  let inspect ← Harness.empty
  inspect.connections.set (← h.connections.get)
  inspect.serviceOperands.set (← h.serviceOperands.get)
  inspect.results.set (← h.results.get)
  let (owner, objects) ← prospectiveOwnerData h inspect privateTrace request.owner #[request.input]
  if sameCompleteWireContext owner request.owner then
    return ← admittedRegistrations h request.operation.raw request.input true
  let projected ← prepareOperationObservation inspect privateTrace request.original request.operation
    request.parameters (some owner) (some request) objects
  unless projected.input.form.id == request.input.form.id &&
      (← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType projected.input.value) (← inferType request.input.value) <&&>
          isDefEq projected.input.value request.input.value)) do
    throwError "prospective admission changed the complete operation or input address"
  admittedRegistrations h request.operation.raw projected.input true

/-- Candidate preparation retains recipes. Only a selected direct target
registration demands its exact owner image, then rebuilds the complete request
with that actual data. Missing direct implementations keep the existing proved
derivation path; neither a primitive failure nor changed ownership selects a
different direct registration after this boundary. -/
partial def executeOperationObservation (h : Harness) (request : OperationObservation)
    (selected : Option Registration := none) :
    TermElabM Wire := do
  if request.materialized then return request.original
  let registrations ← if selected.isNone then operationObservationRegistrations h request
    else pure #[]
  if selected.isNone && registrations.isEmpty then
    return ← dispatchOperationObservation h request
  let selected ← match selected with
    | some selected => pure selected
    | none => do
      match registrations with
      | #[selected] => pure selected.registration
      | _ =>
        let choices := registrations.map fun row =>
          (row.registration.operation, row.registration.input, row.registration.backend)
        throwStratum .ambiguousRealization
          m!"several admitted registrations compute the selected operation: {choices}"
  let owner ← realizeObjectObservation { h with demandObjectActions := true }
    request.trace request.owner
  -- An unchanged complete owner leaves this immutable prepared request and
  -- all of its original occurrence inputs unchanged. Dispatch still rechecks
  -- the selected registration and live suppliers at the ordinary boundary.
  if sameCompleteWireContext owner request.owner then
    return ← dispatchOperationObservation h request (some selected)
  let actual ← prepareOperationObservation h request.trace request.original request.operation
    request.parameters (some owner) (some request)
  dispatchOperationObservation h actual (some selected)

/-- Complete one exact retained occurrence. The table owns the canonical source
and selected interface; a copied alias cannot install a different producer. -/
partial def observeCapturedInvocation (h : Harness) (trace : Trace) (wire : Wire)
    (captured : CapturedInvocation) : TermElabM Wire := do
  let some current ← retainedCapturedInvocation? wire
    | throwStratum .unavailable "the invocation has no current complete producer occurrence"
  unless current.occurrence == captured.occurrence do
    throwError "the invocation observer changed its retained occurrence identity"
  let records ← h.invocations.get
  let some position := records.findIdx? (·.captured.occurrence == captured.occurrence)
    | throwStratum .unavailable "the invocation's owning preparation scope has expired"
  let some record := records[position]?
    | throwError "the captured invocation table lost its selected occurrence"
  unless record.captured.occurrence == captured.occurrence do
    throwError "the invocation table changed its immutable occurrence identity"
  let original ← forwardRetainedValue record.input wire.value
  unless sameCompleteWireContext original { wire with capturedInvocation := none } do
    throwStratum .unavailable "the invocation changed its original complete typed input occurrence"
  if let some result := record.result then
    checkDataOwners h result.fragment
    return ← forwardRetainedValue result wire.value
  if h.invocationStack.contains captured.occurrence then
    throwStratum .unavailable "the captured computation has cyclic operand dependencies"
  let active := { h with invocationStack := h.invocationStack.push captured.occurrence }
  let result ← match record.captured.interface with
    | .callable selected => observeSelectedCallable active trace record.input selected
    | .structured selected => observeStructuredInvocationWith
        realizeObjectObservation (fun h trace wire => realizeArrowObservation h trace wire)
        (fun h trace wire context endpoints publicFrame =>
          captureCompleteCallable h trace wire context endpoints publicFrame)
        active trace selected
    | .projection selected => observeStructuredProjection active trace record.input selected
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType result.value) (← inferType record.input.value) <&&>
        isDefEq result.value record.input.value) do
    throwError "the completed invocation changed its independently selected result"
  let result ← forwardRetainedValue result record.input.value
  let result := { result with capturedInvocation := some record.captured }
  checkDataOwners h result.fragment
  h.invocations.modify fun records => records.modify position fun item =>
    { item with result := some result }
  forwardRetainedValue result wire.value

/-- Observe the original typed inputs of one selected registered invocation.
No trace expression or cache entry can replace a captured parameter, receiver,
base map, or endpoint. Actual replies retain their distinct completed origin. -/
partial def observeSelectedCallable (h : Harness) (trace : Trace) (wire : Wire)
    (selected : SelectedCallableInvocation) : TermElabM Wire := do
  checkSelectedCallableInvocation wire selected
  let state ← registryState
  let some operation := state.operation? selected.address
    | throwError "the captured callable operation is no longer registered"
  match selected.operationRequest, operation with
  | some request, .operation entry =>
      unless entry.id == request.operation && request.parameters ==
          selected.declarationParameters.map (·.formal) do
        throwError "the captured callable changed its existing operation-owner request"
      let actual ← executeOperationObservation h request
      let actual ← forwardRetainedValue actual wire.value
      if actual.pointDataInterface.isSome then
        return ← captureCompleteCallable h trace actual selected.context
      return actual
  | some _, _ | none, .operation _ =>
      throwError "the captured callable changed its independently selected dispatch owner"
  | none, _ => pure ()
  let h := { h with demandObjectActions := true }
  let observed ← IO.mkRef (#[] : Array (ActionDataRole × Wire × Wire))
  let observe := fun (role : ActionDataRole) (original : Wire) => do
    if let some (_, _, actual) := (← observed.get).find? (fun (selected, input, _) =>
        selected == role && sameCompleteWireContext input original) then return actual
    let actual ← observeActionDataWire h trace role original
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType actual.value) (← inferType original.value) <&&>
          isDefEq actual.value original.value) do
      throwError "the callable input changed its complete independently selected value"
    let actual ← forwardRetainedValue actual original.value
    observed.modify (·.push (role, original, actual))
    return actual
  -- Both templates share the same exact operand occurrences. Memoization is
  -- by complete typed selection, never by equal bytes or formal cache keys.
  let (descriptor, descriptorInputs) ← renderActionDataWith observe selected.descriptor
  let parameters ← selected.parameters.mapM (renderActionDataWith observe)
  let raw : Wire := { wire with
    payload := (← combinedRecipePayload wire.value descriptor descriptorInputs)
    categoryContext := some selected.context
    capturedInvocation := none, callableEndpoints := none
    intrinsicAssembly := none, actionRecipe := none
    morphismFramed := false, morphismFraming := none }
  let endpoint := fun (original : Wire) (origin : CallableEndpointOrigin) (source : Bool) => do
    match origin with
    | .retained => observe .object original
    | .reference => callableEndpointReference raw original.value source (some selected.context)
  let source ← endpoint selected.source selected.sourceOrigin true
  let target ← endpoint selected.target selected.targetOrigin false
  CategoryContext.checkMorphism selected.context wire.value source.value target.value
  let framed ← presentMorphism raw source target (some selected.context)
  let dependencies := descriptorInputs ++
    parameters.foldl (fun inputs item => inputs ++ item.2) #[] ++
    (← observed.get).map (·.2.2)
  dispatchSelectedCallable h wire selected (parameters.map Prod.fst) framed
    source target dependencies

/-- Compatibility entry point for callers that already hold the producer's
complete selected invocation. Supplied metadata checks that same record; it
cannot reconstruct a missing producer from trace expressions or a cache. -/
partial def realizeCallableObservation (h : Harness) (trace : Trace) (wire : Wire)
    (address : String) (parameters : Array DataOwnership.Data) (_dependencies : Array Wire := #[])
    (inverse : Option Bool := none) : TermElabM Wire := do
  if wire.callableObserved || wire.actualData then return wire
  let some captured ← retainedCapturedInvocation? wire
    | throwStratum .noImplementation "the pending callable has no retained typed invocation"
  let some selected ← retainedSelectedCallableInvocation? wire
    | throwStratum .noImplementation "the pending callable has no retained typed invocation"
  let original ← selected.parameters.mapM renderCapturedActionData
  unless address == selected.address && inverse == selected.inverse &&
      parameters == original.map Prod.fst do
    throwError "the callable observation changed its original selected invocation metadata"
  observeCapturedInvocation h trace wire captured

/-- Demand the computational value of an entire arrow. Merely forming a named arrow,
including one used inside a later point invocation, retains its public descriptor.
Only this observation demand dispatches that descriptor. Structural composites are
rebuilt from the observed children through the ordinary checked realization paths,
retaining their exact endpoint frames, declared actions and session dependencies. -/
partial def realizeArrowObservation (h : Harness) (trace : Trace) (wire : Wire)
    (registeredOnly : Bool := false) :
    TermElabM Wire := do
  if wire.callableObserved || wire.actualData then return wire
  if let some assembly ← retainedIntrinsicAssembly? wire .map then
    return ← observeIntrinsicAssembly h trace wire assembly registeredOnly
  if let some framing := wire.morphismFraming then
    let replayed ← presentMorphism framing.input framing.source framing.target framing.context
    unless sameCompleteWireContext replayed wire do
      throwStratum .unavailable "the observed map lost its complete framing producer"
    let actual ← realizeArrowObservation h trace framing.input registeredOnly
    if sameCompleteWireContext actual framing.input then return wire
    let context ← framingContext framing.context actual.categoryContext
    let some context := context
      | throwError "the observed map lost its complete framing category"
    let (source, target) ← capturedMapEndpoints h trace actual context true
    -- A newly observed complete callable is already expressed at the endpoints
    -- fixed by its invocation. Reusing the old comparison would apply it twice.
    return ← retainCallableEndpoints actual source target context
  if let some recipe := wire.actionRecipe then
    unless recipe.morphism do
      throwError "a map observation cannot consume a retained object-action role"
    return ← observeActionRecipe h trace wire recipe
  if let some captured ← retainedCapturedInvocation? wire then
    return ← observeCapturedInvocation h trace wire captured
  let formal := wire.value
  let some node ← (trace.node? formal : IO _) | return wire
  let rebuild (children : Array Expr) : TermElabM Wire := do
    for child in children do
      let input ← realize h trace "the observed arrow's constituent" child
      let actual ← realizeArrowObservation h trace input registeredOnly
      -- The recursive observation caches actual returned data. Ordinary descriptors
      -- remain ordinary inputs and are not promoted to computed values by this demand.
      match actual.payload with
      | .ordinary .. => pure ()
      | _ =>
          if !child.hasMVar && !child.hasLevelMVar && !child.hasFVar && !child.hasLooseBVars then
            h.results.modify (·.insert child actual)
    realizeFresh h trace "the observed complete arrow" formal
  let tag := (wire.json.getObjValAs? String "ctor").toOption
  let actual ← match node with
    | .operationEquivalence representative chosen candidates comparisons => do
        checkOperationEquivalence formal representative chosen candidates comparisons
        -- Use the incoming actual payload at the verified original trace. In particular,
        -- a returned whole callable does not become its formal recipe when only the
        -- transparent wrapper is present in the result cache.
        let input := { wire with payload := forwardPayload wire representative wire.json }
        let some representativeNode ← trace.node? representative
          | throwError "the checked operation class lost its selected trace"
        let operationId ← match representativeNode with
          | .operationApply id .. | .operationPoint id .. => pure id
          | _ => throwError "the checked operation class has no complete operation trace"
        if let some actual := operationRecipeId? input then
          unless actual == operationId.raw do
            throwError "the operation class's representative has a different retained recipe"
        unless operationRecipe input operationId do return wire
        if registeredOnly && !h.admitted.any (fun admitted =>
            candidates.any (·.operation.raw == admitted.registration.operation)) then
          unless ← candidates.anyM (fun candidate => hasGroundedDerivation h candidate.operation.raw) do
            return wire
        let mut applicable : Array (OperationObservation × Registration) := #[]
        let mut requests : Array OperationObservation := #[]
        for candidate in candidates do
          let candidateWire ← if candidate.result == representative then pure input
            else realizeUnobserved h trace "a checked equivalent operation's complete result" candidate.result
          let some candidateNode ← trace.node? candidate.result
            | throwError "a checked equivalent operation lost its retained trace"
          let (id, parameters) ← match candidateNode with
            | .operationApply id parameters .. | .operationPoint id parameters .. =>
                pure (id, parameters)
            | _ => throwError "a checked equivalent operation lost its exact callable address"
          unless id == candidate.operation do
            throwError "a checked equivalent operation changed its accepted address"
          let request ← prepareOperationObservation h trace candidateWire id parameters
          requests := requests.push request
          checkDataOwners h request.input.fragment
          let registrations ← operationObservationRegistrations h request
          applicable := applicable ++ registrations.map (fun admitted => (request, admitted.registration))
        let mut selected : Option (OperationObservation × Wire) := none
        let mut gaps : Array String := #[]
        match applicable with
          | #[(request, registration)] =>
              selected := some (request, ← executeOperationObservation h request (some registration))
          | #[] =>
              -- The whole-family operation agreement was checked above. A
              -- proved plan computes one of these fixed meanings; it cannot
              -- create another route or hide an ambiguous direct registration.
              for request in requests.qsort (fun left right => left.operation.raw < right.operation.raw) do
                unless ← hasGroundedDerivation h request.operation.raw do continue
                let failures ← h.portFailures.get
                try
                  selected := some (request, ← executeOperationObservation h request)
                  break
                catch error =>
                  unless !Exception.hasConflictingStrata error &&
                      Exception.stratum? error == some .noImplementation &&
                      (← h.portFailures.get) == failures do throw error
                  gaps := gaps.push (← error.toMessageData.toString)
          | _ => do
              let choices := applicable.map fun (_, registration) =>
                (registration.operation, registration.input, registration.backend)
              throwStratum .ambiguousRealization m!"several admitted registered requests compute the checked operation class: {choices}"
        let some (request, actual) := selected
          | if registeredOnly then return wire else
            throwStratum .noImplementation m!"no admitted registration or applicable proved plan computes the checked operation class {candidates.map (·.operation.raw)}; {gaps}"
        match actual.payload with
        | .ordinary .. => pure ()
        | _ => h.results.modify (·.insert request.original.value actual)
        let framed ← forwardOperationEquivalent formal representative actual
        -- The canonical formal interface is unchanged; only the checked candidate's
        -- actual returned data and owning session cross the equality substitution.
        let result := { wire with
          payload := framed.payload, callableObserved := framed.callableObserved
          pointDataInterface := framed.pointDataInterface
          morphismFramed := framed.morphismFramed, morphismFraming := framed.morphismFraming
          actionRecipe := framed.actionRecipe, intrinsicAssembly := framed.intrinsicAssembly
          callableEndpoints := framed.callableEndpoints }
        match result.payload with
        | .ordinary .. => pure ()
        | _ =>
          let retained ← forwardRetainedValue result representative
          h.results.modify (·.insert representative retained)
        pure result
    | .namedMorphism id _ => do
        unless tag == some id.raw do return wire
        throwStratum .noImplementation "the pending named map has no retained typed invocation"
    | .namedCallable address _ _ => do
        unless tag == some address do return wire
        throwStratum .noImplementation "the pending named callable has no retained typed invocation"
    | .presentation _ _ _ => do
        unless tag == some "presentation" do return wire
        throwStratum .noImplementation "the pending presentation has no retained typed invocation"
    | .cellComponent .. => do
        unless tag == some "cellComponent" || tag == some "constructedCellComponent" do return wire
        throwStratum .noImplementation "the pending component has no retained typed invocation"
    | .cartesian _ _ _ _ "hom" => do
        unless tag == some "cartesianMap" do return wire
        throwStratum .noImplementation "the pending cartesian map has no retained typed invocation"
    | .constructionMap .. =>
        throwStratum .noImplementation
          "the pending construction map has no retained typed producer occurrence"
    | .operationApply id parameters _ _ _ | .operationPoint id parameters .. => do
        unless operationRecipe wire id do return wire
        let derived ← hasGroundedDerivation h id.raw
        if registeredOnly && !derived &&
            !h.admitted.any (·.registration.operation == id.raw) then return wire
        let request ← prepareOperationObservation h trace wire id parameters
        let direct ← operationObservationRegistrations h request
        if registeredOnly && !derived && direct.isEmpty then
          return wire
        let failures ← h.portFailures.get
        try executeOperationObservation h request
        catch error =>
          if registeredOnly && direct.isEmpty && !Exception.hasConflictingStrata error &&
              Exception.stratum? error == some .noImplementation &&
              (← h.portFailures.get) == failures then return wire
          throw error
    | .admittedPoint .. | .constrainedPoint .. | .elementValue .. =>
        throwStratum .noImplementation
          "the intrinsic point or value has no current retained typed child occurrences"
    | .morphismComposition .. | .contextualComposition .. | .callableRecipe .. |
        .contextualIdentity .. =>
        throwStratum .noImplementation
          "the intrinsic callable has no current retained typed child occurrences"
    | .morphismTransport _ _ route _ | .contextualRoute _ _ route _ _ true =>
        if route.isEmpty then return wire
        throwStratum .noImplementation
          "the pending map action has no retained typed producer occurrence"
    | _ => pure wire
  if !formal.hasMVar && !formal.hasLevelMVar && !formal.hasFVar && !formal.hasLooseBVars then
    match actual.payload with
    | .ordinary .. => pure ()
    | _ => h.results.modify (·.insert formal actual)
  return actual

end

/-- Materialize a retained generalized operation through its complete public port. -/
partial def realizeOperationObservation (h : Harness) (trace : Trace) (wire : Wire)
    (id : OperationId) (parameters : Array Expr) : TermElabM Wire := do
  if let some actual := operationRecipeId? wire then
    unless actual == id.raw do
      throwError "the retained operation recipe changed its accepted operation"
  unless operationRecipe wire id do return wire
  executeOperationObservation h (← prepareOperationObservation h trace wire id parameters)


-- Legacy prescribed lift adapter
/-- Recover raw inspection arguments from their independently fixed formal
roles and explicit retained dependencies. The private cache never chooses
between distinct occurrences with the same formal key and never starts a port. -/
def legacyLiftRecovery (h : Harness) (dependencies : Array Wire) : TermElabM Harness := do
  let mut supplied : Array Wire := #[]
  for dependency in dependencies do
    discard <| checkedFragment dependency.fragment.validate
    if let some previous := supplied.find? (·.value == dependency.value) then
      unless sameActionOperand previous dependency do
        throwStratum .unavailable "the raw lift arguments have distinct retained occurrences of one formal dependency"
    else supplied := supplied.push dependency
  let results ← IO.mkRef (← h.results.get)
  for dependency in supplied do
    results.modify (·.insert dependency.value dependency)
  return { h with
    results := results
    admitted := #[]
    backends := #[]
    deferred := none
    derivation := none
    dispatches := none }

/-- Raw inspection compatibility only. Production uses `executePrescribedLiftData`.
The old result can retain at most one supplying session, so a multi-supplier
result must use the scoped interface rather than discard occurrence ownership. -/
def executePrescribedLift (h : Harness) (trace : Trace) (plan : LiftedSubobjectData.Plan)
    (source base : Wire) (parameters : Array (Array Json × Array Wire))
    (encoder? : Option ActionEncoder := none) :
    TermElabM (Json × Option (String × Nat)) := do
  unless parameters.size == plan.components.size do
    throwError "the prescribed lift lost its complete selected evidence parameters"
  let state ← registryState
  let mut edges : Array EdgeRef := #[]
  let mut rawActions : Array (Option (Json × Array Wire)) := #[]
  for component in plan.components do
    let some row := state.lifts.find? (·.id == component.lift)
      | throwError "the fixed lift plan lost its registered row"
    let .constructMap _ inner := row.edge
      | throwError "the fixed lift plan lost its selected inner action"
    edges := edges.push inner
    rawActions := rawActions.push (← match encoder? with
      | some encoder => some <$> encoder inner component.action
      | none => pure none)
  let mut scopedParameters : Array (Array DataOwnership.Data × Array Wire) := #[]
  let mut scopedActions : Array (EdgeRef × Expr × DataOwnership.Data × Array Wire) := #[]
  for (component, index) in plan.components.zipIdx do
    let actionDependencies := (rawActions[index]!.map Prod.snd).getD #[]
    let recovery ← legacyLiftRecovery h (parameters[index]!.2 ++ actionDependencies)
    let fixed ← DirectConstruction.dataArguments component.selection.parameters
    let (actualParameters, parameterDependencies) ← realizedParameterData recovery trace fixed
    unless actualParameters.map (·.json) == parameters[index]!.1 &&
        sameActionOperands parameterDependencies parameters[index]!.2 do
      throwStratum .unavailable "the raw lift parameters differ from their exact independently retained data or dependencies"
    let (actualAction, actualDependencies) ← realizedEdgeData recovery trace edges[index]! component.action
    if let some (rawAction, dependencies) := rawActions[index]! then
      unless rawAction == actualAction.json && sameActionOperands dependencies actualDependencies do
        throwStratum .unavailable "the raw lift action differs from its exact independently retained descriptor or dependencies"
    scopedParameters := scopedParameters.push (actualParameters, parameterDependencies)
    scopedActions := scopedActions.push (edges[index]!, component.action, actualAction, actualDependencies)
  let position ← IO.mkRef (0 : Nat)
  let encoder : ScopedActionEncoder := fun edge action => do
    let index ← position.modifyGet fun index => (index, index + 1)
    let some (expectedEdge, expectedAction, descriptor, dependencies) := scopedActions[index]?
      | throwError "the scoped lift encoder requested an unretained stage"
    unless edge == expectedEdge && action == expectedAction do
      throwError "the scoped lift encoder changed its independently selected stage"
    return (descriptor, dependencies)
  let data ← executePrescribedLiftData h trace plan source base scopedParameters (some encoder)
  unless (← position.get) == scopedActions.size do
    throwError "the scoped lift encoder omitted a selected stage"
  let owner ← match DataOwnership.owners data.ownership with
    | #[] => pure none
    | #[owner] => pure (some owner)
    | _ =>
      throwStratum .noImplementation
        "the legacy raw lift interface cannot retain multiple supplying sessions; use the scoped interface"
  return (data.json, owner)
-- End legacy prescribed lift adapter

/-- Raw inspection interfaces preserve the existing engineering consumers.
Production assembly uses the fragment-returning owners above. -/
def realizedParameters (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array Json × Array Wire) := do
  let (data, dependencies) ← realizedParameterData h trace parameters
  return (data.map (·.json), dependencies)

def realizedEdgeDescriptor (h : Harness) (trace : Trace) (edge : EdgeRef) (actual : Expr) :
    TermElabM (Json × Array Wire) := do
  let (data, dependencies) ← realizedEdgeData h trace edge actual
  return (data.json, dependencies)

def elementExpression (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Json × Array Wire) := do
  let (data, dependencies) ← elementFragment h trace value
  return (data.json, dependencies)

def frameMorphismData (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : Option CategoryContext := none) :
    TermElabM (Json × Array Wire) := do
  let (data, dependencies) ← frameMorphismFragment h trace source target wire context
  return (data.json, dependencies)

/-- Select the equality observation by its declared syntax and complete signature.
The registered power object supplies the truth-value object. Every candidate is
checked on fresh arguments against equality, so another predicate with the same
spelling cannot observe the fixed question. No stable row identifier or row order
selects its mathematical meaning. The returned parameters are the actual closed
explicit data parameters of the accepted declaration. -/
def equalityObservation (state : RegistryState) (target : Expr) :
    TermElabM (MorphismEntry × Expr × Array Expr × Expr × Expr) := do
  let power ← Language.powerObjectIn state CategoryId.sets
  let truth ← instantiateFresh power.truth
  let some (_, omega) := Language.homEnds? (← inferType truth)
    | throwError "the registered truth map has no complete target"
  let source ← mkAppM ``Prod #[target, target]
  let mut candidates := #[]
  for entry in state.morphisms do
    unless entry.name == "=" && entry.category == CategoryId.sets do continue
    let candidate ← withoutModifyingState do
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType declaration)
      let some (input, output) := Language.homEnds? type | return none
      unless (← withTransparency .all <| isDefEq input source) &&
          (← withTransparency .all <| isDefEq output omega) do return none
      let .ok arrow ← completeArrow declaration parameters | return none
      let function ← Language.functionOf arrow
      let identifies ← withLocalDeclD `x target fun x =>
        withLocalDeclD `y target fun y => do
          let pair ← mkAppM ``Prod.mk #[x, y]
          withTransparency .all <| isDefEq (mkApp function pair) (← mkEq x y)
      unless identifies do return none
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let mut data := #[]
      for (parameter, info) in parameters.zip infos do
        let parameter ← instantiateMVars parameter
        if info.isExplicit && !(← isProp (← inferType parameter)) then
          data := data.push parameter
      return some (entry, arrow, data, ← instantiateMVars input, ← instantiateMVars output)
    if let some candidate := candidate then candidates := candidates.push candidate
  match candidates with
  | #[candidate] => return candidate
  | #[] =>
    throwStratum .noImplementation
      "the selected carrier has no registered equality observation with the complete declared meaning"
  | _ =>
    throwStratum .ambiguousRealization
      "the selected carrier has several registered equality observations"

/-- Observe the actual data of two points through the uniquely registered equality
characteristic map. The response is computational data and supplies no proof. -/
def observeEquality (h : Harness) (trace : Trace) (first second : Wire) (domain target : Expr) :
    TermElabM Bool := do
  let state ← registryState
  let (equality, arrow, parameterValues, _, truth) ← equalityObservation state target
  for object in #[domain, target, truth] do
    discard <| Semantic.recordNamedObject object (some trace)
  let domainWire ← realize h trace "the computational equality's point domain" domain
  let valueWire ← realize h trace "the computational equality's selected carrier" target
  let sourceData ← scopedNode "objectProduct" #[valueWire.fragment, valueWire.fragment]
  let truthWire ← realize h trace "the computational equality's truth-value carrier" truth
  let (parameters, parameterWires) ← realizedParameterData h trace parameterValues
  let invocation ← pointInvocationData equality.id.raw parameters
    (← scopedNode equality.id.raw parameters) domainWire.fragment sourceData truthWire.fragment
    (DataOwnership.Data.array #[first.fragment, second.fragment])
  let payload ← combinedRecipePayload arrow invocation
    (#[first, second, domainWire, valueWire, truthWire] ++ parameterWires)
  let request : Wire := {
    form := .namedMorphism equality, payload
    serviceHandles := (← retainLiftOperands h
      (#[first, second, domainWire, valueWire, truthWire] ++ parameterWires)) }
  let reply ← sendData h equality.id.raw request (completeRequest := true)
  let answer := reply.data.json
  let backend := reply.backend
  match Backend.ComputationalValue.decode answer with
  | .ok (.inline (.bool truth)) => return truth
  | .ok _ => malformed backend equality.id.raw answer "the declared truth observation requires inline Boolean data"
  | .error message => malformed backend equality.id.raw answer message

/-- Evaluate the recorded decision `p` to a three-valued answer (`Option Bool`), through the
admitted registration of its property on the form of its receiver, sent along the resolved
route. -/
partial def realizeDecision (h : Harness) (trace : Trace) (what : String) (p : Expr) :
    TermElabM (Expr × Json) := do
  let p ← instantiateMVars p
  let some (.property id route receiver recordedComparisons) ← (trace.node? p : IO _)
    | do
      -- `¬ q` (`x ∉ A`) is the negated decision of `q`.
      if let some q := p.not? then
        let (answer, json) ← realizeDecision h trace what q
        return (← mkAppM ``Option.map #[mkConst ``not, answer], json)
      -- A truth value compared with `⊤` (`x ∈ A`) is an equation between two points
      -- `1 ⟶ Ω`: it is observed through the registered equality of `Ω`.
      if let some (_, a, b) := p.eq? then
        if (← (trace.node? a : IO _)).isSome && (← (trace.node? b : IO _)).isSome then
          if let some (domain, target) := Language.homEnds? (← inferType a) then
            let first ← realize h trace s!"the left side of {what}" a
            let second ← realize h trace s!"the right side of {what}" b
            let truth ← observeEquality h trace first second domain target
            return (toExpr (some truth), toJson truth)
      throwStratum .noImplementation m!"nothing decides {what}: it is not a registered \
        property of a value the realized reading evaluates"
  let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
  let (request, input) ← operationReceiver trace original route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
  let state ← registryState
  let some property := state.properties.find? (·.id == id)
    | throwError "the recorded property is not registered"
  let some receiverExpression := state.formExpression? original.form
    | throwError "the property receiver lost its accepted category expression"
  let resolution ← match state.resolveProperty receiverExpression property.name with
    | .ok resolution => pure resolution
    | .error error => throwResolutionError state error
  unless resolution.route.refs == route do
    throwError "the recorded property changed its full registered route"
  let comparisonTerms ← Semantic.validatePropertyResolutionComparisons state resolution (some receiver)
  Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses
    comparisonTerms recordedComparisons
  let some classifier := state.classifier? property.classifier
    | throwError "the recorded property's classifier is not registered"
  -- Check the full selected domain without requiring an encoding of every intermediate image.
  let classifier ← classifierInstance classifier
  discard <| elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax input))) none
  let request ← computationalOperationReceiver h trace id.raw original route request
  let request ← computationalApexReceiver trace (← realizeObjectObservation h trace request)
  call h id.raw request
    (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) resolution.comparisons

/-- A deferred program resolves references by exact occurrence, independently of
expression-keyed execution caches. `known` contains only operands of its parent
request; it is not a registry of alternate meanings for arbitrary JSON. -/
structure ServiceScope where
  harness : Harness
  trace : Trace
  references : Array Wire
  known : Array Wire
  operands : IO.Ref (Array Wire)
  backend : String
  /-- A formal derivation gives each original runtime operand its own transparent
  expression key before building dependent applications. Ordinary service calls
  keep their existing keys. Equal formal values never merge actual suppliers. -/
  operandBinding : Option String := none

partial def serviceContainsRef (data : Json) : Bool :=
  if (data.getObjValAs? String "ctor").toOption == some "resultRef" then true
  else match data with
    | .arr values => values.any serviceContainsRef
    | .obj fields => fields.any fun _ value => serviceContainsRef value
    | _ => false

def checkServiceOwner (h : Harness) (wire : Wire) : TermElabM Unit := do
  checkDataOwners h wire.fragment

/-- A compiler key denotes one retained operand occurrence. The actual Wire is
kept unchanged, including structured packets and their authoritative fields. -/
def serviceOperandValue (scope : ServiceScope) (handle : Nat) (value : Expr) :
    TermElabM Expr := do
  match scope.operandBinding with
  | none => return value
  | some binding =>
    return ← mkAppM ``Trace.operationResult #[toExpr s!"{binding}:operand:{handle}", value]

def serviceRegister (scope : ServiceScope) (wire : Wire) : TermElabM ServiceRequest.Operand := do
  checkServiceOwner scope.harness wire
  let handle ← scope.operands.modifyGet fun values => (values.size, values.push wire)
  let value ← serviceOperandValue scope handle wire.value
  if value != wire.value then Trace.alias (some scope.trace) wire.value value
  return {
    value := value, data := wire.json, handle
    ownership := wire.ownership
    form := some wire.form, context := wire.categoryContext }

def serviceWire (scope : ServiceScope) (operand : ServiceRequest.Operand) : TermElabM Wire := do
  let some wire := (← scope.operands.get)[operand.handle]?
    | throwError "a typed service operand lost its retained occurrence handle"
  unless (← serviceOperandValue scope operand.handle wire.value) == operand.value &&
      wire.json == operand.data &&
      wire.ownership == operand.ownership do
    throwError "a typed service operand changed its retained occurrence"
  checkServiceOwner scope.harness wire
  return wire

/-- Copied bytes cannot choose between different complete formal selections.
This deliberately uses expression identity, including the full selected dictionary,
instead of conversion of mathematical values. Explicit references remain occurrence based. -/
def sameServiceSelection (left right : Wire) : Bool :=
  sameActionOperand left right && left.form.id == right.form.id &&
    left.presentationIsos == right.presentationIsos &&
    left.categoryContext.map (·.bundle) == right.categoryContext.map (·.bundle) &&
    (match left.categoryContext, right.categoryContext with
      | none, none => true
      | some left, some right => left.expression.syntacticEq right.expression
      | _, _ => false) &&
    left.constructionInputs == right.constructionInputs &&
    left.constructionInputOwnership == right.constructionInputOwnership

/-- Two actions can produce the very same formal value and packet. Their action
receipts still distinguish the selected computation, so copied bytes are ambiguous;
a result reference supplies the required occurrence without consulting this lookup. -/
def distinctServiceActionOrigins (scope : ServiceScope) (wire : Wire) : IO Bool := do
  let origins := (← scope.harness.actions.get).filter fun record =>
    sameServiceSelection record.result wire
  return origins.any fun left => origins.any fun right =>
    left.operation != right.operation || left.action != right.action ||
      !sameServiceSelection left.input right.input || left.parameters != right.parameters ||
      left.parameterOwnership != right.parameterOwnership ||
      !sameActionOperands left.parameterInputs right.parameterInputs ||
      !sameActionOperands left.imageEndpoints right.imageEndpoints

/-- A reference has an already fixed formal value. A copied original packet is
accepted only from the exact parent scope, with ambiguity retained. -/
def serviceRetained (scope : ServiceScope) (data : Json) (expected : Option Expr := none) :
    TermElabM (Option Wire) := do
  let index ← match Backend.resultRefIndex? data with
    | .ok index => pure index
    | .error message => throwStratum .malformed message
  if let some index := index then
    let some wire := scope.references[index]?
      | throwStratum .malformed "a service reference is outside its completed local scope"
    checkServiceOwner scope.harness wire
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType wire.value) expected do
        throwStratum .malformed "a service reference has a different complete declared type"
    return some wire
  let mut candidates : Array Wire := #[]
  for wire in scope.known do
    unless wire.json == data do continue
    if let some expected := expected then
      unless ← withoutModifyingState <| withTransparency .all <|
          isDefEq (← inferType wire.value) expected do continue
    checkServiceOwner scope.harness wire
    let repeated := candidates.any (sameServiceSelection · wire)
    unless repeated do candidates := candidates.push wire
  match candidates with
  | #[] => return none
  | #[wire] =>
    if ← distinctServiceActionOrigins scope wire then
      throwStratum .ambiguousRealization
        "the parent packet has distinct retained complete action occurrences"
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType wire.value) expected do
        throwError "the retained service input lost its selected full type"
    return some wire
  | _ => do
    throwStratum .ambiguousRealization
      "the parent request has distinct typed occurrences of the same computational packet"

def serviceLiteralWire (scope : ServiceScope) (formal : Expr) (data : Json)
    (dependencies : Array ServiceRequest.Operand := #[]) (form : Option Form := none)
    (context : Option CategoryContext := none) (ownership : DataOwnership.Table := #[])
    (productComponents : Array Wire := #[]) (completed : Bool := true) :
    TermElabM ServiceRequest.Operand := do
  let formal ← SimpleServiceRequest.checkClosed formal
  let wires ← dependencies.mapM (serviceWire scope)
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the published data category is absent"
  let form := form.getD (context.map (ServiceRequest.formFor state · (.diagrams sets))
    |>.getD (.diagrams sets))
  let completed := completed && wires.all (fun wire => match wire.payload with
    | .computed _ (.recipe _) => wire.completedData
    | _ => true)
  let payload ← if completed then scopedPayload formal { json := data, ownership }
    else recipePayload formal { json := data, ownership }
  let wire : Wire := {
    form, payload, categoryContext := context
    objectObserved := completed, callableObserved := completed, productComponents }
  serviceRegister scope wire

/-- An existing action descriptor selects only its already published projection
addresses. Availability never changes this mathematical selection. -/
def serviceActionInvocation (selected : SimpleServiceRequest.SelectedAction) (morphismAction : Bool) :
    TermElabM (String × Array Json) := do
  let state ← registryState
  let .ok (tag, _) := ComputationalData.envelope selected.descriptor
    | throwError "the selected service action lost its complete descriptor"
  if let some entry := state.functors.find? (·.id.raw == tag) then
    return (if morphismAction then entry.mapAddress else entry.id.raw, selected.parameters)
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    return (if morphismAction then entry.mapAddress else entry.id.raw, selected.parameters)
  let identity ← SimpleServiceRequest.actionIdentity selected.descriptor
  let some edge := state.actionIdentityEdge? identity
    | throwStratum .malformed "the service action has no accepted complete projection identity"
  edgeActionInvocation state edge selected.descriptor morphismAction

/-- A nested public action is a computational demand, not a target data codec.
It crosses the same complete image boundary before a downstream operation runs. -/
def serviceObjectImage (scope : ServiceScope) (selected : SimpleServiceRequest.SelectedAction)
    (target : CategoryContext) (original : Wire) (dependencies : Array Wire) :
    TermElabM Wire := do
  let formal ← Semantic.objOf selected.value original.value
  let (operation, parameters) ← serviceActionInvocation selected false
  let template : Wire := {
    form := ServiceRequest.formFor (← registryState) target original.form
    payload := (← combinedRecipePayload formal (← scopedNode "functorAction"
      #[{ json := selected.descriptor, ownership := selected.descriptorOwnership }, original.fragment])
      (dependencies.push original))
    categoryContext := some target }
  executeObjectAction scope.harness scope.trace operation selected.value original
    template parameters dependencies selected.parameterOwnership

mutual

/-- Instantiate the existing public dependent telescope, retaining every actual
explicit data operand. Formal proof/class obligations are closed separately. -/
partial def serviceDeclaration (scope : ServiceScope) (name : Name) (data : Array Json) :
    TermElabM ServiceRequest.Declaration := do
  let constant ← mkConstWithFreshMVarLevels name
  let (fields, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let mut operands : Array ServiceRequest.Operand := #[]
  let mut explicit := #[]
  let mut position := 0
  for (field, info) in fields.zip infos do
    if info.isExplicit then explicit := explicit.push field
    let type ← instantiateMVars (← inferType field)
    unless info.isExplicit && !(← isProp type) do continue
    let some datum := data[position]?
      | throwStratum .malformed "the service declaration omitted an ordered data parameter"
    let operand ← serviceArgument scope type datum
    unless ← withTransparency .all <| isDefEq field operand.value do
      throwStratum .malformed "a service parameter changes its complete dependent interface"
    operands := operands.push operand
    position := position + 1
  unless position == data.size do
    throwStratum .malformed "the service declaration supplied an extra parameter or proof"
  return {
    application := { value := mkAppN constant fields, arguments := fields, explicit }
    operands }

partial def serviceNamed (scope : ServiceScope) (data : Json) (expected : Option Expr := none) :
    TermElabM (Option ServiceRequest.Operand) := do
  let .ok (tag, arguments) := ComputationalData.envelope data | return none
  let state ← registryState
  let selected := (state.objects.find? (·.id.raw == tag)).map
      (fun row => (row.declaration, some (Form.object row), some row.category)) <|>
    (state.callable? tag).map (fun (name, category) => (name, state.form? tag, some category))
  if let some (name, form, category) := selected then
    let declaration ← serviceDeclaration scope name arguments
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType declaration.application.value) expected do
        throwStratum .malformed "a named service operand changes its complete declared type"
    let application ← DirectConstruction.close declaration.application
    let formal ← SimpleServiceRequest.checkClosed application.value
    let context ← match category.bind (fun id => state.categories.find? (·.id == id)) with
      | none => pure none
      | some category =>
        let object := (Language.homEnds? (← inferType formal)).map Prod.fst |>.getD formal
        pure (some (← CategoryContext.ofNamed category object))
    return some (← serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag (declaration.operands.map (·.data)))
      declaration.operands form context
      (DataOwnership.prefix #[.field "args"]
        (ServiceRequest.operandArrayOwnership declaration.operands))
      (completed := (state.objects.find? (·.id.raw == tag)).isSome))
  if #["category", "constructedCategory", "functor"].contains tag then
    let #[.str id, .arr parameters] := arguments
      | throwStratum .malformed "a service dictionary requires its full ordered parameters"
    let declaration := if tag == "category" then
      (state.categories.find? (·.id.raw == id)).map (·.declaration)
    else if tag == "constructedCategory" then
      (state.constructors.find? (·.id.raw == id)).map (·.semantics)
    else (state.functors.find? (·.id.raw == id)).map (·.declaration)
    let some declaration := declaration
      | throwStratum .malformed "the service dictionary is not mathematically published"
    let selected ← serviceDeclaration scope declaration parameters
    if let some expected := expected then
      let formal ← if tag == "functor" then Semantic.asFunctor selected.application.value
        else pure selected.application.value
      unless ← withTransparency .all <| isDefEq (← inferType formal) expected do
        throwStratum .malformed "a service dictionary changes its complete declared parameter type"
    let application ← DirectConstruction.close selected.application
    let formal ← if tag == "functor" then Semantic.asFunctor application.value
      else pure application.value
    return some (← serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag #[toJson id, Json.arr (selected.operands.map (·.data))])
      selected.operands none none
      (ServiceRequest.argsOwnership #[#[], ServiceRequest.operandArrayOwnership selected.operands]))
  return none

partial def serviceObject (scope : ServiceScope) (data : Json) :
    TermElabM ServiceRequest.Operand := do
  if let some wire ← serviceRetained scope data then return ← serviceRegister scope wire
  if let some projected ← serviceProjection? scope data then return projected
  if let some selected ← serviceNamed scope data then return selected
  let .ok (tag, arguments) := ComputationalData.envelope data
    | throwStratum .malformed "a service object requires its complete declared interface"
  match tag, arguments with
  | "valueData", #[child] => serviceObject scope child
  | "objectProduct", #[left, right] =>
    let left ← serviceObject scope left
    let right ← serviceObject scope right
    let formal ← mkAppM ``Prod #[left.value, right.value]
    serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag #[left.data, right.data]) #[left, right] none none
      (ServiceRequest.argsOwnership #[left.ownership, right.ownership])
      #[← serviceWire scope left, ← serviceWire scope right]
  | "arrow", #[source, target, hom] =>
    let source ← serviceObject scope source
    let target ← serviceObject scope target
    let hom ← serviceArgument scope (← mkAppM ``Quiver.Hom #[source.value, target.value]) hom
    let formal ← mkAppM ``CategoryTheory.Arrow.mk #[hom.value]
    let context ← match source.context with
      | some context => do
        let state ← registryState
        let #[constructor] := state.constructors.filter
            (·.semantics == `CasCatalogue.Constructors.arrow)
          | throwError "the public Arrow category constructor is absent or ambiguous"
        pure (some (← CategoryContext.construct context constructor.id))
      | none => pure none
    serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag #[source.data, target.data, hom.data])
      #[source, target, hom] none context
      (ServiceRequest.argsOwnership #[source.ownership, target.ownership, hom.ownership])
  | "coreObject", #[original] =>
    let original ← serviceObject scope original
    let formal ← mkAppM ``CategoryTheory.Core.mk #[original.value]
    let context ← match original.context with
      | some context => do
        let state ← registryState
        let #[constructor] := state.constructors.filter
            (·.semantics == `CasCatalogue.Constructors.core)
          | throwError "the public Core category constructor is absent or ambiguous"
        pure (some (← CategoryContext.construct context constructor.id))
      | none => pure none
    serviceLiteralWire scope formal (SimpleServiceRequest.node tag #[original.data])
      #[original] none context (ServiceRequest.argsOwnership #[original.ownership])
  | "functorAction", #[descriptor, original] =>
    let selected ← SimpleServiceRequest.action (← serviceDecoder scope) descriptor
    let (source, _) ← functorCategoryBundles selected.value
    let original ← serviceArgument scope (← mkAppM ``CategoryTheory.Bundled.α #[source]) original
    let formal ← Semantic.objOf selected.value original.value
    let selected ← SimpleServiceRequest.closeAction selected
    let (_, target) ← functorCategoryBundles selected.value
    let context : CategoryContext := { expression := selected.target, bundle := target }
    let formal ← SimpleServiceRequest.checkClosed formal
    let actual ← serviceObjectImage scope selected context (← serviceWire scope original)
      (← selected.dependencies.mapM (serviceWire scope))
    SimpleServiceRequest.sameValue actual.value formal "nested object action"
    serviceRegister scope actual
  | _, _ =>
    if serviceContainsRef data then
      throwStratum .noImplementation
        "unfinished kernel service preparation: this public object form has unresolved typed reference roles"
    let state ← registryState
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the published data category is absent"
    let .ok formal ← decodeObjectData scope.trace sets data
      | throwStratum .malformed "the service object has no independently recoverable complete interface"
    serviceLiteralWire scope formal data

partial def serviceArrow (scope : ServiceScope) (data : Json) (expected : Option Expr := none) :
    TermElabM ServiceRequest.Operand := do
  if let some wire ← serviceRetained scope data expected then
    unless (Language.homEnds? (← inferType wire.value)).isSome do
      throwStratum .malformed "a service callable reference is not a categorical morphism"
    return ← serviceRegister scope wire
  if let some projected ← serviceProjection? scope data then
    unless (Language.homEnds? (← inferType projected.value)).isSome do
      throwStratum .malformed "the service projection does not select a complete callable"
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType projected.value) expected do
        throwStratum .malformed "the service projection changes its complete selected Hom"
    return projected
  if let some selected ← serviceNamed scope data expected then
    unless (Language.homEnds? (← inferType selected.value)).isSome do
      throwStratum .malformed "the service callable descriptor names an object"
    return selected
  let result ← match ComputationalData.envelope data with
  | .ok ("valueData", #[child]) => serviceArrow scope child expected
  | .ok ("typedMap", #[source, target, callable]) =>
    let source ← serviceObject scope source
    let target ← serviceObject scope target
    let type ← match source.context with
      | some context => CategoryContext.hom context source.value target.value
      | none => mkAppM ``Quiver.Hom #[source.value, target.value]
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq type expected do
        throwStratum .malformed "the service typed map changes its complete declared endpoints"
    let callable ← serviceArgument scope type callable
    serviceLiteralWire scope callable.value
      (Backend.TypedMap.encode { source := source.data, target := target.data, callable := callable.data })
      #[source, target, callable] callable.form source.context
      (ServiceRequest.argsOwnership #[source.ownership, target.ownership, callable.ownership])
  | .ok ("identity", #[source, target]) =>
    let source ← serviceObject scope source
    let target ← serviceObject scope target
    SimpleServiceRequest.sameValue target.value source.value "identity endpoint"
    discard <| framingContext source.context target.context
    let formal ← match source.context with
      | some context => identityAtContext context source.value
      | none => mkAppM ``CategoryTheory.CategoryStruct.id #[source.value]
    serviceLiteralWire scope formal
      (SimpleServiceRequest.node "identity" #[source.data, target.data])
      #[source, target] none source.context
      (ServiceRequest.argsOwnership #[source.ownership, target.ownership])
  | .ok ("compose", #[first, second]) =>
    let first ← serviceArrow scope first
    let second ← serviceArrow scope second
    let some (domain, middle) := Language.homEnds? (← inferType first.value)
      | throwStratum .malformed "the first service composite operand has no complete Hom"
    let some (middle', target) := Language.homEnds? (← inferType second.value)
      | throwStratum .malformed "the second service composite operand has no complete Hom"
    SimpleServiceRequest.sameValue middle middle' "composite middle object"
    let formal ← match first.context with
      | some context => ServiceRequest.compose context domain middle target first.value second.value
      | none => mkAppM ``CategoryTheory.CategoryStruct.comp #[first.value, second.value]
    serviceLiteralWire scope formal
      (SimpleServiceRequest.node "compose" #[first.data, second.data])
      #[first, second] none first.context
      (ServiceRequest.argsOwnership #[first.ownership, second.ownership])
  | .ok ("map", #[descriptor, original]) =>
    let selected ← SimpleServiceRequest.action (← serviceDecoder scope) descriptor
    let original ← serviceArrow scope original
    let formal ← Semantic.mapOf selected.value original.value
    let selected ← SimpleServiceRequest.closeAction selected
    let (_, target) ← functorCategoryBundles selected.value
    let context : CategoryContext := { expression := selected.target, bundle := target }
    let formal ← SimpleServiceRequest.checkClosed formal
    let (sourceBundle, _) ← functorCategoryBundles selected.value
    let some sourceExpression := selected.source <|> original.context.map (·.expression) <|>
        (original.form.bind (← registryState).formExpression?)
      | throwStratum .malformed "the nested map lost its complete original category context"
    let sourceContext : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let original ← serviceWire scope original
    let dependencies ← selected.dependencies.mapM (serviceWire scope)
    let (operation, parameters) ← serviceActionInvocation selected true
    let template : Wire := {
      form := ServiceRequest.formFor (← registryState) context original.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map"
        #[{ json := selected.descriptor, ownership := selected.descriptorOwnership }, original.fragment])
        (dependencies.push original))
      categoryContext := some context }
    let actual ← executeMapAction scope.harness scope.trace operation selected.value
      sourceContext context original template selected.descriptor parameters dependencies
      (fun source => serviceObjectImage scope selected context source dependencies)
      selected.descriptorOwnership selected.parameterOwnership
    serviceRegister scope actual
  | _ =>
    if serviceContainsRef data then
      throwStratum .noImplementation
        "unfinished kernel service preparation: this public callable form has unresolved typed reference roles"
    let state ← registryState
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the published data category is absent"
    let decoded ← match expected with
      | some expected => decodeValue scope.trace sets expected data
      | none => pure ((← decodeArrowData scope.trace sets data).map (·, none))
    let .ok (formal, form) := decoded
      | throwStratum .malformed "the service callable has no independently recoverable full signature"
    serviceLiteralWire scope formal data #[] form
  if let some expected := expected then
    unless ← withTransparency .all <| isDefEq (← inferType result.value) expected do
      throwStratum .malformed "the service callable differs from its complete selected Hom type"
  return result

partial def serviceArgument (scope : ServiceScope) (expected : Expr) (data : Json) :
    TermElabM ServiceRequest.Operand := do
  let expected ← instantiateMVars expected
  if ← isProp expected then
    throwStratum .malformed "a proof is not a service data argument"
  if let .ok ("valueData", #[child]) := ComputationalData.envelope data then
    return ← serviceArgument scope expected child
  if let some wire ← serviceRetained scope data (some expected) then
    return ← serviceRegister scope wire
  let result ← if (Language.homEnds? expected).isSome then serviceArrow scope data (some expected)
  else if let some projected ← serviceProjection? scope data then pure projected
  else if let some selected ← serviceNamed scope data (some expected) then pure selected
  else if let .ok (tag, _) := ComputationalData.envelope data then
    if #["objectProduct", "arrow", "coreObject", "functorAction"].contains tag then
      serviceObject scope data
    else servicePlainArgument scope expected data
  else servicePlainArgument scope expected data
  unless ← withTransparency .all <| isDefEq (← inferType result.value) expected do
    throwStratum .malformed "the service operand differs from its complete declared parameter type"
  return result

partial def servicePlainArgument (scope : ServiceScope) (expected : Expr) (data : Json) :
    TermElabM ServiceRequest.Operand := do
  let type ← withTransparency .all <| whnf expected
  if let .arr values := data then
    if type.isAppOfArity ``Prod 2 && values.size == 2 then
      let first ← serviceArgument scope type.getAppArgs[0]! values[0]!
      let second ← serviceArgument scope type.getAppArgs[1]! values[1]!
      let formal ← mkAppM ``Prod.mk #[first.value, second.value]
      return ← serviceLiteralWire scope formal (Json.arr #[first.data, second.data]) #[first, second]
        none none (ServiceRequest.arrayOwnership #[first.ownership, second.ownership])
    if type.isAppOfArity ``List 1 || type.isAppOfArity ``Array 1 then
      let values ← values.mapM (serviceArgument scope type.getAppArgs[0]!)
      let formal ← if type.isAppOf ``List then mkListLit type.getAppArgs[0]! (values.map (·.value)).toList
        else mkArrayLit type.getAppArgs[0]! (values.map (·.value)).toList
      return ← serviceLiteralWire scope formal (Json.arr (values.map (·.data))) values
        none none (ServiceRequest.operandArrayOwnership values)
  if serviceContainsRef data then
    throwStratum .noImplementation
      "unfinished kernel service preparation: this data form has unresolved typed reference roles"
  if containsOpaqueData data then
    throwStratum .unavailable "the service cannot infer a new opaque value's mathematical interface"
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the published data category is absent"
  let .ok (formal, form) ← decodeValue scope.trace sets expected data
    | throwStratum .malformed "the service argument does not decode at its full published type"
  serviceLiteralWire scope formal data #[] form

partial def serviceDecoder (scope : ServiceScope) : TermElabM ServiceRequest.Decoder := pure {
  argument := serviceArgument scope
  object := serviceObject scope
  arrow := fun data => serviceArrow scope data
  endpoint := serviceEndpoint scope
  project := serviceProject scope
  condition := serviceCondition scope
  declaration := serviceDeclaration scope }

partial def serviceEndpoint (scope : ServiceScope) (operand : ServiceRequest.Operand)
    (source : Bool) : TermElabM ServiceRequest.Operand := do
  let wire ← serviceWire scope operand
  let some (left, right) := Language.homEnds? (← inferType wire.value)
    | throwStratum .malformed "the service endpoint requires the original whole callable"
  let formal := if source then left else right
  if let some endpoint ← retainedCallableEndpoint? wire formal source wire.categoryContext then
    return ← serviceRegister scope endpoint
  if let some endpoint ← retainedActionEndpoint? wire wire.categoryContext formal source then
    let endpoint := { endpoint with
      serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
    return ← serviceRegister scope endpoint
  let state ← registryState
  let form := wire.categoryContext.map (ServiceRequest.formFor state · wire.form) |>.getD wire.form
  let .ok projection ← ComputationalData.interfaceEndpointDataWithOrigin #[] wire.value
      wire.fragment source false
    | throwStratum .malformed "the service endpoint lost its original complete callable data"
  if projection.origin == .action then
    unless wire.completedData do
      throwStratum .noImplementation
        "the service endpoint has no retained typed action producer"
    let endpoint := { (← callableEndpointReference wire formal source wire.categoryContext) with
      objectObserved := true
      serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
    return ← serviceRegister scope endpoint
  let completed := wire.completedData && projection.origin == .projection
  let endpoint : Wire := {
    form, payload := (← scopedPayload formal projection.data completed)
    categoryContext := wire.categoryContext, objectObserved := completed
    serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
  serviceRegister scope endpoint

partial def serviceProject (scope : ServiceScope) (operand : ServiceRequest.Operand)
    (field : String) (index : Option Nat) : TermElabM ServiceRequest.Operand := do
  let wire ← serviceWire scope operand
  let state ← registryState
  let context ← match wire.categoryContext with
    | some context => pure context
    | none => do
      let some category := state.categories.find? (·.id == wire.form.category)
        | throwStratum .malformed "the service record lost its complete declared category"
      CategoryContext.ofNamed category wire.value
  let (formal, targetContext, morphism) ← match index with
    | some index =>
      let some plan ← StructuredProjection.construction? wire.value context (some scope.trace)
        | throwStratum .malformed "the service record has no selected universal data ports"
      let port ← plan.selectPort (some index)
      pure (port.formalField, context, (Language.homEnds? port.expectedType).isSome)
    | none =>
      let some plan ← StructuredProjection.arrow? wire.value context
        | throwStratum .malformed "the service record is not a complete Arrow or subobject"
      plan.field field
  let literal ← match index with
    | some index =>
      let .construction result _ := wire.payload
        | throwStratum .malformed "the selected data field lost its retained universal packet"
      match result.packet with
      | .created .. => pure none
      | .direct answer =>
        let .ok (_, fields) := ComputationalData.envelope answer
          | throwError "a retained universal packet lost its checked data constructor"
        let some _ := fields[index]?
          | throwError "a retained universal packet lost its checked field"
        pure (some (← checkedFragment <| wire.fragment.project
          #[.field "args", .index 2, .field "args", .index index]))
    | none =>
      if wire.objectIso.isSome || wire.endpointPresentation.isSome ||
          !wire.presentationIsos.isEmpty then pure none
      else if let some fields := subobjectFragments? wire.fragment then
        match field with
        | "source" | "obj" => pure fields[0]?
        | "target" => pure fields[1]?
        | "hom" =>
          let #[source, target, callable] := fields | unreachable!
          if let .ok framed := Backend.TypedMap.decode callable.json then
            unless framed.source == source.json && framed.target == target.json &&
                DataOwnership.project #[.field "args", .index 0] callable.ownership ==
                  source.ownership &&
                DataOwnership.project #[.field "args", .index 1] callable.ownership ==
                  target.ownership do
              throwStratum .malformed "a retained Arrow field changes its actual complete endpoints"
            pure (some callable)
          else pure (some (← scopedNode "typedMap" #[source, target, callable]))
        | "inclusion" => pure (some (← scopedNode "arrow" fields))
        | _ => pure none
      else pure none
  if let some data := literal then
    let completed := wire.completedData
    let projected : Wire := {
      form := ServiceRequest.formFor state targetContext wire.form morphism
      payload := (← scopedPayload formal data completed)
      categoryContext := some targetContext
      objectObserved := completed && !morphism, callableObserved := completed && morphism
      serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
    return ← serviceRegister scope projected
  let results ← IO.mkRef (({} : Std.HashMap Expr Wire).insert wire.value wire)
  let localHarness := { scope.harness with results }
  let projected ← structuredProjection localHarness scope.trace formal wire.value field index
  serviceRegister scope { projected with
    serviceHandles := (← retainServiceOperands scope.harness #[wire]) }

/-- A returned universal packet is resolved through its retained authoritative
Result, never by interpreting the packet as a proof-bearing cone. The repeated
row and diagram are checked against that exact original occurrence. -/
partial def serviceConstructionRecord (scope : ServiceScope) (id : String)
    (diagram packet : Json) : TermElabM ServiceRequest.Operand := do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == id)
    | throwStratum .malformed "the construction projection has no published owner"
  let original ← if let some wire ← serviceRetained scope packet then pure wire else do
    let candidates := scope.known.filter fun wire => match wire.payload with
      | .construction result _ => result.json == packet
      | _ => false
    let mut unique := #[]
    for wire in candidates do
      unless unique.any (sameServiceSelection · wire) do unique := unique.push wire
    let #[wire] := unique
      | if unique.isEmpty then
          throwStratum .noImplementation
            "unfinished kernel service preparation: the construction packet has no retained universal context"
        else
          throwStratum .ambiguousRealization
            "the construction packet has distinct retained universal occurrences"
    checkServiceOwner scope.harness wire
    pure wire
  let .construction result _ := original.payload
    | throwStratum .malformed "a construction packet reference is not a retained universal result"
  unless original.form.id == id && result.colimit == row.colimit do
    throwStratum .malformed "the construction projection changed its exact registered owner"
  if let some retained ← serviceRetained scope diagram then
    SimpleServiceRequest.sameValue retained.value result.diagram "construction diagram"
    unless retained.json == result.diagramJson && retained.ownership ==
        DataOwnership.project #[.field "args", .index 1] original.ownership do
      throwStratum .malformed "the construction projection changed its actual retained diagram"
  else if diagram != result.diagramJson then
    let some category := state.categories.find? (·.id == row.category)
      | throwError "the retained universal row lost its declared category"
    let prepared ← UniversalServiceRequest.limit (← serviceDecoder scope) row (.diagrams category) diagram
    SimpleServiceRequest.sameValue prepared.requestValue result.diagram "construction diagram"
    unless prepared.request == result.diagramJson && prepared.requestOwnership ==
        DataOwnership.project #[.field "args", .index 1] original.ownership do
      throwStratum .malformed "the construction projection changed its actual retained diagram"
  serviceRegister scope original

/-- Released projection envelopes select typed fields of the original occurrence.
The selector is literal; only declared operand/data roles can contain references. -/
partial def serviceProjection? (scope : ServiceScope) (data : Json) :
    TermElabM (Option ServiceRequest.Operand) := do
  let .ok (tag, arguments) := ComputationalData.envelope data | return none
  match tag, arguments with
  | "morphismEndpoint", #[callable, .str side] =>
    unless side == "source" || side == "target" do
      throwStratum .malformed "the endpoint projection has no declared side"
    return some (← serviceEndpoint scope (← serviceArrow scope callable) (side == "source"))
  | "arrowHom", #[receiver] | "subobjectApex", #[receiver] |
      "subobjectInclusion", #[receiver] =>
    let original ← serviceObject scope receiver
    let wire ← serviceWire scope original
    let some context := wire.categoryContext
      | throwStratum .malformed "the structured projection lost its full selected category"
    let some plan ← StructuredProjection.arrow? wire.value context
      | throwStratum .malformed "the structured projection requires its complete declared Arrow interface"
    unless plan.subobject == (tag != "arrowHom") do
      throwStratum .malformed "the structured projection changed its accepted refinement interface"
    return some (← serviceProject scope original
      (if tag == "subobjectApex" then "source" else "hom") none)
  | "constructionApex", #[.str id, diagram, packet] =>
    return some (← serviceConstructionRecord scope id diagram packet)
  | "constructionField", #[.str id, diagram, packet, index] =>
    let .ok index := index.getNat?
      | throwStratum .malformed "the construction field requires its literal data-port index"
    return some (← serviceProject scope
      (← serviceConstructionRecord scope id diagram packet) "field" (some index))
  | "constructionLeg", #[.str id, diagram, packet, index] =>
    let original ← serviceConstructionRecord scope id diagram packet
    let wire ← serviceWire scope original
    let .construction result _ := wire.payload | unreachable!
    let type ← whnfR (← inferType result.diagram)
    unless type.isAppOfArity ``CategoryTheory.Functor 4 do
      throwError "the retained construction lost its complete diagram type"
    let index ← serviceArgument scope type.getAppArgs[0]! index
    let formal ← SimpleServiceRequest.checkClosed (← result.leg index.value)
    let state ← registryState
    let some row := state.limits.find? (·.id.raw == id) | unreachable!
    let inputs ← constructionInputFragments wire
    let diagramData ← checkedFragment (wire.fragment.project #[.field "args", .index 1])
    let packetData ← checkedFragment (wire.fragment.project #[.field "args", .index 2])
    let projection : ProjectedObjectFragment ← match result.packet with
      | .created .. =>
        return .deferredAction (← scopedNode "constructionLeg"
          #[{ json := toJson id }, diagramData, packetData, index.fragment])
      | .direct answer =>
        let encodeInput := fun value => do
          match selectedConstructionInput inputs value with
          | .error message => return .error message
          | .ok (some data) => return .ok (.structural data)
          | .ok none => return ((← Codec.encode value).bind DataOwnership.Data.portable).map
              ProjectedObjectFragment.structural
        let encodeAction := fun action => do
          let mut descriptors := #[]
          for entry in state.functors do
            let descriptor ← withoutModifyingState do
              let declared ← Semantic.asFunctor (← instantiateFresh entry.declaration)
              unless ← withTransparency .all <| isDefEq declared action do return none
              return some (← realizedEdgeData scope.harness scope.trace (.functor entry.id) action).1
            if let some descriptor := descriptor then descriptors := descriptors.push descriptor
          let #[descriptor] := descriptors
            | return .error "the defining map has no unique complete registered action"
          return .ok (ProjectedObjectFragment.structural descriptor)
        match ← StructuredResult.projectDataWith row result.diagram answer index.value
            (fun field _ => pure ((packetData.project #[.field "args", .index field]).map
              ProjectedObjectFragment.structural))
            encodeInput encodeAction (fun tag fields => do
              let data ← DataOwnership.Data.ctor tag (fields.map (·.data))
              return if tag != "map" && fields.all (·.isStructural) then .structural data
                else .deferredAction data) with
        | .ok data => pure data
        | .error message => throwStratum .noImplementation message
    let projected : Wire := {
      form := wire.categoryContext.map (ServiceRequest.formFor state · wire.form true) |>.getD wire.form
      payload := (← scopedPayload formal projection.data projection.isStructural)
      categoryContext := wire.categoryContext, callableObserved := projection.isStructural }
    return some (← serviceRegister scope projected)
  | _, _ => return none

partial def serviceCondition (scope : ServiceScope) (proposition : Expr) : TermElabM Expr := do
  let proposition ← instantiateMVars proposition
  unless ← isProp proposition do throwError "a formal service condition is not a proposition"
  let mut candidates := #[]
  for (_, node) in (← scope.trace.get).toArray do
    if let .liftFactor _ _ _ proof := node then candidates := candidates.push proof
  if let some proof ← Codec.conditionProof proposition then candidates := candidates.push proof
  for proof in candidates do
    unless proof.hasSorry do
      if ← Decide.kernelAccepts proposition proof then return proof
  throwStratum .noImplementation
    "the service request lacks its independently established formal condition"

end

/-- Request preparation is exhaustive over the existing admitted operation
families. It derives meaning before inspecting availability or asking a backend. -/
def prepareServiceRequest (scope : ServiceScope) (operation : String) (input : Form)
    (template : Json) : TermElabM ServiceRequest.Prepared := do
  let state ← registryState
  let some selected := state.operation? operation
    | throwStratum .malformed "a deferred call names an unpublished operation"
  unless state.accepts selected input do
    throwStratum .malformed "a deferred call uses an incompatible published input form"
  let decoder ← serviceDecoder scope
  if let some prepared ← SimpleServiceRequest.prepare? decoder selected input template then
    return prepared
  if let some prepared ← StructuredServiceRequest.prepare? decoder selected input template then
    return prepared
  if let some prepared ← UniversalServiceRequest.prepare? decoder selected input template then
    return prepared
  throwStratum .noImplementation
    "unfinished kernel service preparation: this published operation family has no typed preparer"

/-- Only explicitly retained operands of this request are available as copied
input packets. A global cache entry or earlier action receipt with equal bytes
does not establish that its occurrence was placed in this request. -/
def serviceKnownInputs (h : Harness) (input : Wire) : TermElabM (Array Wire) := do
  let retained ← h.serviceOperands.get
  let mut known := #[input]
  for handle in input.serviceHandles do
    let some wire := retained[handle]?
      | throwError "a service request lost an exact operand occurrence"
    known := known.push wire
  return known

/-- A template with references has only public data envelopes. Extra object
fields cannot hide unchecked references from a declared data-port validator. -/
partial def checkServiceTemplateFraming (template : Json) : TermElabM Unit := do
  if !serviceContainsRef template then return
  if let .ok (some _) := Backend.resultRefIndex? template then return
  match template with
  | .arr values => for value in values do checkServiceTemplateFraming value
  | .obj fields =>
    let keys := fields.toList.map Prod.fst
    unless keys.length == 2 && keys.contains "ctor" && keys.contains "args" do
      throwStratum .malformed "a result reference occurs outside a complete public data envelope"
    let .ok _ := template.getObjValAs? String "ctor"
      | throwStratum .malformed "a result reference cannot select a data constructor"
    let .ok arguments := (template.getObjVal? "args").bind (·.getArr?)
      | throwStratum .malformed "a referenced data envelope has no ordered data fields"
    for argument in arguments do checkServiceTemplateFraming argument
  | _ => pure ()

/-- Validate every reference at a pre-existing complete formal data port before
substituting actual packets. The referenced value need not equal the caller's
formal result: a well-framed wrong computation stays available for checking. -/
partial def validateServiceResultTemplate (scope : ServiceScope)
    (prepared : ServiceRequest.Prepared) (template : Json) : TermElabM Unit := do
  if !serviceContainsRef template then return
  checkServiceTemplateFraming template
  let interfaces := scope.references.mapIdx fun index wire =>
    (Backend.resultRef index, wire.value)
  let validate : Expr → Json → TermElabM Unit := fun formal data => do
    if !serviceContainsRef data then return
    let expected ← inferType formal
    if let .error message ← withoutModifyingState <|
        ComputationalData.validatePort formal expected data interfaces then
      throwStratum .malformed m!"a deferred result reference changes its complete data role: {message}"
  if prepared.decisionResult then
    let data := match ComputationalData.envelope template with
      | .ok ("valueData", #[data]) => data
      | _ => template
    let .ok (some index) := Backend.resultRefIndex? data
      | throwStratum .malformed "a decision reference must occupy the entire decision result"
    let some wire := scope.references[index]?
      | throwStratum .malformed "a decision reference is outside its completed scope"
    unless ← isProp wire.value do
      throwStratum .malformed "a decision reference does not retain a declared proposition"
    return
  if let some validatePorts := prepared.validateTemplate then
    validatePorts validate template
  else
    validate prepared.result template

/-- Substitute only already checked references. Ownership follows actual opaque
packets; the entire DAG remains retained separately even when this result is portable. -/
partial def assembleServiceResult (scope : ServiceScope) (template : Json) :
    TermElabM DataOwnership.Data := do
  match Backend.resultRefIndex? template with
  | .error message => throwStratum .malformed message
  | .ok (some index) =>
    let some wire := scope.references[index]?
      | throwStratum .malformed "a final result reference is outside its completed local scope"
    checkServiceOwner scope.harness wire
    return wire.fragment
  | .ok none => pure ()
  if (template.getObjValAs? String "ctor").toOption == some "opaqueData" then
    let some (.ok session) := (← scope.harness.connections.get)[scope.backend]?
      | throwStratum .unavailable "a deferred result's supplying session is unavailable"
    return DataOwnership.Data.capture template (scope.backend, session.identity)
  match template with
  | .arr values =>
    return DataOwnership.Data.array (← values.mapM (assembleServiceResult scope))
  | .obj fields =>
    let mut actual := []
    for (key, value) in fields.toList do
      actual := actual ++ [(key, ← assembleServiceResult scope value)]
    checkedFragment (DataOwnership.Data.object actual)
  | _ => return { json := template }

/-- A service node uses the same dispatch, action execution, completion and
semantic method/property paths as an ordinary computation. Its occurrence handles
are kept independently of the expression-indexed ordinary result cache. -/
partial def executeServiceRequest (scope : ServiceScope) (operation : String) (input : Form)
    (prepared : ServiceRequest.Prepared) : TermElabM ServiceNodeExecution := do
  let h := scope.harness
  checkServiceCallableInterface prepared
  let endpointWires ← match prepared.callableEndpointOperands with
    | none => pure none
    | some (source, target) => do
      let some (.endpoints domain codomain _ _) := prepared.callableInterface
        | throwError "the service endpoint occurrences lost their selected result role"
      let source ← forwardRetainedValue (← serviceWire scope source) domain
      let target ← forwardRetainedValue (← serviceWire scope target) codomain
      return some (source, target)
  let dependencies ← prepared.dependencies.mapM (serviceWire scope)
  let request : Wire := {
    form := input
    payload := (← combinedRecipePayload prepared.requestValue prepared.fragment dependencies)
    serviceHandles := (← retainServiceOperands h dependencies) }
  let template : Wire := {
    form := prepared.resultForm
    payload := (← combinedRecipePayload prepared.result prepared.fragment dependencies)
    categoryContext := prepared.resultContext
    constructionInputs := prepared.constructionInputs
    constructionInputOwnership := prepared.constructionInputOwnership }
  let result ← match prepared.action with
    | some (.object action original parameters parameterOperands) =>
      executeObjectAction h scope.trace operation action (← serviceWire scope original)
        template parameters (← parameterOperands.mapM (serviceWire scope))
        (DataOwnership.project #[.field "args"] prepared.requestOwnership)
    | some (.wholeMap action source target original descriptor parameters parameterOperands
        imageSource imageTarget) => do
      let images ← #[imageSource, imageTarget].mapM (serviceWire scope)
      let position ← IO.mkRef (0 : Nat)
      let image : Wire → TermElabM Wire := fun original => do
        let index : Nat ← position.modifyGet fun index => (index, index + 1)
        let some actual := images[index]?
          | throwError "the whole service action requested an extra image endpoint"
        let expected ← Semantic.objOf action original.value
        SimpleServiceRequest.sameValue actual.value expected "retained image endpoint"
        checkServiceOwner h actual
        return actual
      executeMapAction h scope.trace operation action source target (← serviceWire scope original)
        template descriptor parameters (← parameterOperands.mapM (serviceWire scope)) image
        (DataOwnership.project #[.field "args", .index 2, .field "args", .index 0]
          prepared.requestOwnership)
        (DataOwnership.project #[.field "args", .index 1] prepared.requestOwnership)
    | none =>
      if let some trace := prepared.trace then do
        let #[original] := dependencies
          | throwError "the semantic service request lost its unique original receiver"
        let results ← IO.mkRef (({} : Std.HashMap Expr Wire).insert original.value original)
        let h := { h with results }
        if prepared.decisionResult then
          let (_, data) ← realizeDecision h trace "the deferred declared decision" prepared.result
          pure { template with payload := .computed prepared.result (.inline data) }
        else
          let result ← realizeFresh h trace "the deferred declared method" prepared.result
          if prepared.objectResult then realizeObjectObservation h trace result else pure result
      else do
        let reply ← sendData h operation request (completeRequest := true)
        let answer := reply.data.json
        let backend := reply.backend
        let completed ← match ← prepared.complete answer with
          | .ok completed => pure completed
          | .error message => malformed backend operation answer message
        match completed with
        | some completed =>
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq (← inferType completed.apex) (← inferType prepared.result) <&&>
                isDefEq completed.apex prepared.result) do
            throwError "a completed service construction changed its independently derived apex"
          let answer ← receiveReplyFragment h operation reply true
          let packet ← match completed.packet with
            | .direct _ => pure answer
            | .created lift _ _ =>
              scopedNode "createdCone" #[{ json := toJson lift }, request.fragment, answer]
          pure { template with payload := (← constructionPayload template.form completed
            request.fragment packet), objectObserved := true }
        | none =>
          let data ← receiveReplyData h operation reply true
          let received : Wire := { template with
            payload := .computed prepared.result data
            objectObserved := prepared.objectResult, callableObserved := prepared.callableResult }
          retainServiceCallableResult prepared received endpointWires
  checkServiceOwner h result
  return { operation, input := input.id, request, dependencies, result }

/-- Execute one untrusted deferred program in a local reference scope. Every node
has an independently derived formal application and an actual retained Wire.
The enclosing ordinary caller still owns its original formal result expression. -/
partial def completeServiceReply (h : Harness) (trace : Trace)
    (stack : Array (String × Wire))
    (operation : String) (input : Wire) (reply : ComputationalReply) :
    TermElabM ComputationalReply := do
  let answer := reply.data.json
  let backend := reply.backend
  unless (answer.getObjValAs? String "ctor").toOption == some "deferredData" do
    return reply
  let .ok program := Backend.DeferredData.decode answer
    | throwStratum .malformed "the deferred service reply has malformed or out-of-scope references"
  if stack.any (fun (previous, wire) => previous == operation && sameServiceSelection wire input) then
    throwStratum .unavailable "a deferred computation recursively requests the same complete input"
  let stack := stack.push (operation, input)
  let active := { h with deferred := some (completeServiceReply h trace stack) }
  let known ← serviceKnownInputs h input
  let operands ← IO.mkRef #[]
  let mut scope : ServiceScope := { harness := active, trace, references := #[], known, operands, backend }
  let index ← h.services.modifyGet fun records => (records.size, records.push {
    operation, input, backend, original := answer })
  let outer ← prepareServiceRequest scope operation input.form input.json
  let mut nodes := #[]
  for call in program.calls do
    let state ← registryState
    let some input := state.form? call.input
      | throwStratum .malformed "a deferred call names an unpublished input form"
    let prepared ← prepareServiceRequest scope call.operation input call.arguments
    let node ← executeServiceRequest scope call.operation input prepared
    nodes := nodes.push node
    h.services.modify fun records => records.modify index fun record => { record with nodes }
    scope := { scope with references := scope.references.push node.result }
  validateServiceResultTemplate scope outer program.result
  let result ← assembleServiceResult scope program.result
  checkDataOwners h result
  if let .error message ← outer.complete result.json then
    throwStratum .malformed m!"the completed deferred reply changes its original result interface: {message}"
  let owner := match DataOwnership.owners result.ownership with
    | #[owner] => some owner
    | _ => none
  h.services.modify fun records => records.modify index fun record =>
    { record with
      nodes, result := result.json, owner, ownership := result.ownership
      completed := true }
  return { data := result, backend := owner.map Prod.fst |>.getD backend }

/-- Retain only full category contexts supplied by the original typed operands.
An equal carrier or another registry object's declaration supplies no context. -/
def derivationContexts (wires : Array (Expr × Wire)) :
    TermElabM (Array CategoryContext × Array Language.Value) := do
  let state ← registryState
  let mut contexts : Array CategoryContext := #[]
  let mut objects : Array Language.Value := #[]
  for (key, wire) in wires do
    let some category := state.categories.find? (·.id == wire.form.category) | continue
    let candidate ← withoutModifyingState do
      try
        let context ← match wire.categoryContext with
          | some context => pure context
          | none => CategoryContext.ofNamed category wire.value
        CategoryContext.checkObject context key
        return some context
      catch error =>
        if Exception.interpretationKind error == .invalid then return none else throw error
    if let some context := candidate then
      unless contexts.any (· == context) do contexts := contexts.push context
      if context.expression.syntacticEq category.expression then
        objects := objects.push (.object key category none none none)
  return (contexts, objects)

/-- Execute a checked mathematical derivation using the ordinary typed readers,
actions, operation observations and service executor. The complete input fixes
the family application before the plan is specialized. All result data remain
untrusted; the retained family proof relates formal expressions only.

The finite family support graph rules out ungrounded cycles before expansion.
A revisit can still terminate at a directly applicable primitive, because the
ordinary dispatcher runs before this callback. Otherwise it is an explicit gap,
even when a cyclic plan changes its arguments on every recursive call. -/
partial def executeDerivedRequest (h : Harness) (trace : Trace)
    (stack : Array ComputationRef) (operation : String) (input : Wire)
    (_completeRequest : Bool) : TermElabM ComputationalReply := do
  let state ← registryState
  let some reference := (state.operation? operation).bind ComputationDerivation.reference?
    | throwStratum .noImplementation m!"no admitted registration or published derivation computes {operation} on {input.form.id}"
  if stack.contains reference then
    throwStratum .noImplementation m!"cyclic computational derivation has no applicable primitive at {operation}; family path {stack.map ComputationDerivation.address}"
  let entries ← computationDerivations
  let support ← derivationSupport h entries (stack.push reference)
  let candidates := (entries.filter fun entry => entry.target == reference &&
    entry.prerequisites.all support.contains).qsort fun left right => left.id.raw < right.id.raw
  if candidates.isEmpty then
    let requested := entries.filter (·.target == reference)
    let missing := requested.map fun entry => (entry.id.raw,
      entry.prerequisites.filter (!support.contains ·) |>.map ComputationDerivation.address)
    throwStratum .noImplementation m!"no finite primitive-supported computational derivation computes {operation} on {input.form.id}; missing or cyclic prerequisites {missing}"
  let known ← serviceKnownInputs h input
  let mut gaps : Array String := #[]
  for entry in candidates do
    let failures ← h.portFailures.get
    try
      let privateTrace ← IO.mkRef (← trace.get)
      let operands ← IO.mkRef #[]
      let binding ← mkFreshUserName `_computationalDerivation
      let scope : ServiceScope := {
        harness := h, trace := privateTrace, references := #[], known, operands
        backend := s!"derivation:{entry.id.raw}", operandBinding := some binding.toString }
      let prepared ← prepareServiceRequest scope operation input.form input.json
      let some application := prepared.familyApplication
        | throwStratum .noImplementation "the published request preparer does not retain a whole family application"
      let checked ← validateComputationDerivation state.toSemanticState entry
      let expansion ← ComputationDerivation.instantiate checked
        (← instantiateMVars application) (← instantiateMVars prepared.result)
      let originals ← (← operands.get).mapIdxM fun index wire => do
        return (← serviceOperandValue scope index wire.value, wire)
      let (contexts, knownObjects) ← derivationContexts originals
      let calls ← IO.mkRef #[]
      let compiler : ComputationDerivation.Compiler := {
        trace := privateTrace, slots := expansion.slots
        known := originals.map (·.1), knownObjects, contexts, calls }
      let compiled ← ComputationDerivation.compile compiler expansion.expanded
      ComputationDerivation.same expansion.expanded compiled
      let calls ← calls.get
      let index ← h.derivations.modifyGet fun records => (records.size, records.push {
        derivation := entry.id, target := entry.target, application := expansion.application
        original := expansion.original, identity := expansion.identity, input, prerequisites := calls })
      let results ← IO.mkRef (originals.foldl
        (fun cache (key, wire) => cache.insert key wire) ({} : Std.HashMap Expr Wire))
      let active := { h with
        results := results
        demandObjectActions := true
        derivation := some (executeDerivedRequest h privateTrace (stack.push reference)) }
      let active := { active with deferred := some (completeServiceReply active privateTrace #[]) }
      for call in calls do
        let actual ← realize active privateTrace "the formal derivation's published prerequisite" call.result
        let actual ← match call.reference with
          | .operation _ | .morphism _ => realizeArrowObservation active privateTrace actual
          | _ =>
            if (Language.homEnds? (← inferType call.result)).isSome then
              realizeArrowObservation active privateTrace actual
            else realizeObjectObservation active privateTrace actual
        checkServiceOwner active actual
        results.modify (·.insert call.result actual)
        h.derivations.modify fun records => records.modify index fun record =>
          { record with steps := record.steps.push actual }
      let result ← realize active privateTrace "the complete proved derivation" compiled
      let result ← if prepared.callableResult then
          realizeArrowObservation active privateTrace result
        else if prepared.objectResult then realizeObjectObservation active privateTrace result
        else pure result
      checkServiceOwner active result
      if let .error message ← prepared.complete result.json then
        throwStratum .malformed m!"the completed derivation changes its original result interface: {message}"
      let retained := { result with
        payload := forwardPayload result expansion.original result.json
        categoryContext := prepared.resultContext.orElse fun _ => result.categoryContext }
      h.derivations.modify fun records => records.modify index fun record =>
        { record with result := some retained }
      let owner := match DataOwnership.owners result.ownership with
        | #[owner] => some owner
        | _ => none
      return { data := result.fragment, backend := owner.map Prod.fst |>.getD scope.backend }
    catch error =>
      unless !Exception.hasConflictingStrata error &&
          Exception.stratum? error == some .noImplementation &&
          (← h.portFailures.get) == failures do throw error
      gaps := gaps.push s!"{entry.id.raw}: {← error.toMessageData.toString}"
  throwStratum .noImplementation m!"no applicable proved computational derivation computes {operation} on {input.form.id}; {gaps}"

/-- Install the same typed service and derivation boundary for production claims
and direct public Harness clients. No new mathematical selector is installed. -/
def enableService (h : Harness) (trace : Trace) : Harness :=
  let active := { h with derivation := some (executeDerivedRequest h trace #[]) }
  { active with deferred := some (completeServiceReply active trace #[]) }


/-- Whether two closed values of a type with decidable equality are equal: the kernel accepts
the proof by decision of `a = b`, or of `a ≠ b`. The literal forms are registered with decidable
equality; a decision is an `Option Bool`. -/
def evaluatedEq (a b : Expr) : MetaM Bool := do
  if ← isDefEq a b then return true
  if (← Codec.conditionProof (← mkEq a b)).isSome then return true
  match ← decideProp (← mkEq a b) with
  | some equal => return equal
  | none => throwStratum .noImplementation m!"the fixed typed values have no executable equality comparison"

/-- The registered evaluations that apply to the proposition `p`: the `evaluation` of each
registered literal form (a literal row's, a subset-literal row's) whose denotation occurs in `p`.
Each is a `meta` procedure of `lean-categories`, validated there with its row, which rewrites the
images of literals of its form under the catalogue's operations to literals, by the theorems of
its domain, and never closes a goal. -/
def evaluationsOf (state : RegistryState) (p : Expr) : Array Name :=
  let occurs (denotation : Name) : Bool := (p.find? (·.isConstOf denotation)).isSome
  (state.literals.filterMap fun form => if occurs form.denotation then form.evaluation else none)
    ++ (state.subsetLiterals.filterMap fun form =>
      if occurs form.denotation then form.evaluation else none)

/-- Select domain-owned point evaluators only from actual retained complete comparisons. -/
def presentationEvaluationsOf (trace : Trace) (p : Expr) : TermElabM (Array Name) := do
  let state ← registryState
  let some (carrier, _, _) := (← whnfR p).eq? | return #[]
  let pointDomain (type : Expr) : TermElabM (Option Expr) := do
    let type ← withTransparency .all <| whnf type
    if let .forallE _ domain _ _ := type then return some domain
    if type.getAppFn.constName? == some ``TypeCat.Hom && type.getAppNumArgs == 2 then
      return some type.getAppArgs[0]!
    return none
  let some domain ← pointDomain carrier | return #[]
  let mut evaluations := #[]
  for (point, node) in (← trace.get).toArray do
    let .presentationApply id params inverse source target argument := node | continue
    let some entry := state.presentations.find? (·.id == id) | continue
    let some evaluation := entry.evaluation | continue
    let terms := params ++ #[point, source, target, argument]
    if terms.any (fun term => term.hasMVar || term.hasLevelMVar || term.hasFVar ||
        term.hasLooseBVars) then continue
    let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
      xs.mapM (·.fvarId!.getBinderInfo)
    let some application := p.find? fun term =>
        term.getAppFn.constName? == some entry.declaration &&
        term.getAppNumArgs == infos.size | continue
    let actualParams := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
      if info.isExplicit then some arg else none
    unless actualParams.size == params.size do continue
    let same ← (actualParams.zip params).allM fun (actual, expected) =>
      withTransparency .all <| isDefEq actual expected
    unless same do continue
    let some argumentDomain ← pointDomain (← inferType argument) | continue
    unless ← withTransparency .all <| isDefEq argumentDomain domain do continue
    let arrow ← Semantic.presentationArrow entry application inverse
    unless ← withTransparency .all <| isDefEq (← inferType arrow)
        (← mkAppM ``Quiver.Hom #[source, target]) do continue
    let some actualDomain ← pointDomain (← inferType point) | continue
    unless ← withTransparency .all <| isDefEq actualDomain domain do continue
    unless evaluations.contains evaluation do evaluations := evaluations.push evaluation
  return evaluations

/-- Whether Lean's kernel accepts a proof of the closed proposition `p` by the registered
evaluations `evaluations` and decision: the goal `p` is given to each evaluation in turn, through
the one sanctioned runner (`Language.runProcedure`, LC-18). A closed remainder uses the existing
structural decision (`Codec.conditionProof`), retaining its complete declared types while
normalizing their presentation. Kernel-owned trace markers are removed only in this proof
presentation, so they cannot obstruct a registered literal's decision instance; the original
question and its operation records retain them. Ordinary `mkDecideProof` remains available for
a residue with local hypotheses. The assembled proof is checked against the original `p` by Lean's kernel,
synchronously within `decideBudget`. Failure to construct or check a proof decides nothing. -/
def evaluatedDecides (evaluations : Array Name) (p : Expr) : TermElabM Bool := do
  let attempt : TermElabM Bool := do
    let goal ← mkFreshExprMVar p .syntheticOpaque
    let mut remaining := [goal.mvarId!]
    for evaluation in evaluations do
      let [current] := remaining | return false
      match ← Language.runProcedure evaluation current with
      | .ok goals => remaining := goals
      -- not a reading fallback: an evaluation that fails decides nothing, and the claim is then
      -- realized, unchanged
      | .error _ => return false
    match remaining with
    | [] => pure ()
    | [residue] => residue.withContext do
        let condition ← instantiateMVars (← residue.getDecl).type
        let condition ← Core.transform condition (post := fun term => do
          let args := term.getAppArgs
          if term.isAppOf ``Trace.operationResult && args.size >= 3 then
            -- The marker's arguments are its binding, complete type, and value.
            -- A wrapped callable may have further arguments on the same spine.
            return .visit (mkAppN args[2]! (args.extract 3 args.size))
          return .done term)
        let structural ← if condition.hasFVar || condition.hasMVar || condition.hasLevelMVar then
          pure none else Codec.conditionProof condition
        let proof ← match structural with
          | some proof => pure proof
          | none => mkDecideProof condition
        residue.assign proof
    | _ => return false
    let proof ← instantiateMVars goal
    if proof.hasMVar || proof.hasLevelMVar || proof.hasSorry then return false
    kernelAccepts p proof
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|
      -- not a reading fallback: a proposition the evaluations and decision do not settle is not
      -- decided by Lean; the claim is then realized, unchanged
      tryCatchRuntimeEx attempt fun _ => pure false

/-- The proposition `p` decided in Lean, generically: `some true` when the kernel accepts its
proof by the registered evaluations that apply to it (`evaluationsOf`) and decision
(`evaluatedDecides`), `some false` when it accepts one of `¬p`, `none` otherwise. -/
def decideEvaluated (p : Expr) (trace? : Option Trace := none) : TermElabM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  let pointEvaluations ← match trace? with
    | some trace => presentationEvaluationsOf trace p
    | none => pure #[]
  let evaluations := pointEvaluations ++ evaluationsOf (← registryState) p
  if ← evaluatedDecides evaluations p then return some true
  if ← evaluatedDecides evaluations (mkNot p) then return some false
  return none

/-- Outcomes available to computation after interpretation. An execution path cannot
construct an authoritative semantic-invalidity or semantic-ambiguity judgement. -/
inductive ExecutionOutcome
  | holds
  | wrong (message : String)
  | gap (reason : String)
  | unavailable (reason : String)
  | malformed (reason : String)
  | internal (reason : String)
  deriving Inhabited, Repr

/-- The runner bridge preserves each computational stratum when reporting it. -/
def ExecutionOutcome.toOutcome : ExecutionOutcome → Outcome
  | .holds => .holds
  | .wrong reason => .wrong reason
  | .gap reason => .gap reason
  | .unavailable reason => .unavailable reason
  | .malformed reason => .malformed reason
  | .internal reason => .internal reason

/-- Discharge `claim` in Lean, generically (`decideEvaluated`): holds when its proposition is
decided true; wrong when it is decided false; `none` when Lean does not
decide it. -/
def discharge (claim : Claim) (trace? : Option Trace := none) :
    TermElabM (Option ExecutionOutcome) := do
  let refuted (what : String) : TermElabM (Option ExecutionOutcome) :=
    return some (.wrong s!"{what} is refuted: Lean decides it false")
  match claim with
  | .binding => return some (.internal "a binding entered execution")
  | .implemented _ => return none
  | .literal _ _ _ _ prop left right =>
      match ← decideEvaluated prop trace? with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .homs _ _ _ prop left right =>
      match ← decideEvaluated prop trace? with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .decision prop expected shown | .judged _ prop expected shown =>
      let some expected := expected | return none
      match ← decideEvaluated prop trace? with
      | some decided => if decided == expected then return some .holds else refuted shown
      | none => return none

/-- Compare the actual reconstructed points using their retained registered evaluator. -/
def evaluatedPointEq (trace : Trace) (a b : Expr) : TermElabM Bool := do
  let condition ← mkEq a b
  let evaluations ← presentationEvaluationsOf trace condition
  unless evaluations.isEmpty do
    if ← evaluatedDecides evaluations condition then return true
    if ← evaluatedDecides evaluations (mkNot condition) then return false
  evaluatedEq a b

/-- Interpret the port's finite function graphs under categorical composition.
This is execution data, not a proposition: the final graph is independently
decoded at the fixed formal morphism type before an equality is observed. -/
partial def composedFiniteGraph (json : Json) : Except String Json := do
  if json.getArr?.isOk then return json
  if (json.getObjValAs? String "ctor").toOption == some "typedMap" then
    let framed ← Backend.TypedMap.decode json
    return ← composedFiniteGraph framed.callable
  -- `finiteGraph`: an explicit domain inventory and a graph with exactly those keys, once each.
  if (json.getObjValAs? String "ctor").toOption == some "finiteGraph" then
    let #[inventory, graph] ← (json.getObjVal? "args").bind (·.getArr?)
      | throw "a finite graph has exactly an inventory and a graph"
    let inventory ← inventory.getArr?
    let entries ← graph.getArr?
    let keys ← entries.mapM fun entry => do
      let #[key, _] ← entry.getArr? | throw "a finite graph entry is not a pair"
      pure key
    unless keys.size == inventory.size && inventory.all (fun point => keys.contains point) &&
        keys.all (fun key => inventory.contains key) do
      throw "the finite graph's keys are not exactly its inventory"
    return graph
  unless (json.getObjValAs? String "ctor").toOption == some "compose" do
    throw "the computed finite map is neither a graph nor a composite of graphs"
  let #[first, second] ← (json.getObjVal? "args").bind (·.getArr?)
    | throw "the computed composition must have exactly two arrows"
  let first ← (← composedFiniteGraph first).getArr?
  let second ← (← composedFiniteGraph second).getArr?
  let mut result := #[]
  for entry in first do
    let #[input, middle] ← entry.getArr?
      | throw "the first finite map has a malformed graph entry"
    let mut outputs := #[]
    for entry' in second do
      let #[key, output] ← entry'.getArr?
        | throw "the second finite map has a malformed graph entry"
      if key == middle then outputs := outputs.push output
    let #[output] := outputs
      | throw "the second finite map is not uniquely defined on an intermediate point"
    result := result.push (Json.arr #[input, output])
  return Json.arr result

/-- Observe actual computational points through the published equality characteristic map.
The truth datum is never elaborated as a proposition or used as proof evidence. -/
def observeComputedPoints (h : Harness) (trace : Trace) (first second : Wire)
    (formal : Expr) : TermElabM Bool := do
  let state ← registryState
  let pointType ← inferType formal
  let some (domain, target) := Language.homEnds? pointType
    | throwStratum .noImplementation "the computational observation has no retained categorical point endpoints"
  let closedPoint ← withTransparency .all <| isDefEq domain (← closedElementDomain state)
  unless closedPoint do
    -- Decode a whole-arrow graph at the fixed Hom type. An ordinary named
    -- descriptor is not its computed value, even when Lean can evaluate its body.
    -- Explicit identity is structural input; all other values come from data.
    let finiteGraphValue (wire : Wire) : TermElabM (Option Expr) := do
      if let .ordinary value json := wire.payload then
        if let some (.morphismIdentity _ _) ← (trace.node? value : IO _) then
          if (json.getObjValAs? String "ctor").toOption == some "identity" then
            return some value
      let data? := match wire.payload with
        | .ordinary _ json => some json
        | .computed _ (.inline data) => some data
        | _ => none
      let some data := data? | return none
      match composedFiniteGraph data with
      | .ok graph =>
        match ← Codec.decode pointType graph with
        | .ok value => return some value
        | .error message => throwStratum .malformed m!"the computed finite graph is invalid: {message}"
      | .error _ => return none
    if let some actualFirst ← finiteGraphValue first then
      if let some actualSecond ← finiteGraphValue second then
        return ← evaluatedPointEq trace actualFirst actualSecond
    let retained ← framingContext first.categoryContext second.categoryContext
    let context ← match retained with
      | some context => pure context
      | none =>
        let some category := state.categories.find? (·.id == first.form.category)
          | throwError "the whole-callable observation lost its selected category"
        CategoryContext.ofNamed category domain
    CategoryContext.checkMorphism context formal domain target
    CategoryContext.checkMorphism context first.value domain target
    CategoryContext.checkMorphism context second.value domain target
    let owner ← wholeCallableObject formal domain target context
    let one ← closedElementDomain state
    let first ← wholeCallablePoint h trace first domain target one context owner
    let second ← wholeCallablePoint h trace second domain target one context owner
    return ← observeEquality h trace first second one owner.application.value
  -- Closed-point data belongs to the target. In particular a vector element
  -- can itself be a graph and is not the graph of the outer map `1 ⟶ target`.
  if ← ComputationalData.plainType (← withTransparency .all <| whnf target) then
    let observe (wire : Wire) : TermElabM (Option Expr) := do
      match wire.payload with
      | .computed _ (.inline data) =>
        match ← Codec.decode target data with
        | .ok value => return some value
        | .error _ => return none
      | .ordinary value json =>
        let actual? ← match ← (trace.node? value : IO _) with
          | some (.elementNumeral ..) => pure (some value)
          | some (.morphismIdentity ..) => pure (some value)
          | _ => do
            let some category := state.categories.find? (·.id == CategoryId.sets)
              | return none
            -- An ordinary input may be a literal point followed by a declared
            -- inclusion. Decode its actual public descriptor at the fixed point
            -- type; never substitute the retained formal expression for data.
            pure ((← decodeValue trace category pointType json).toOption.map Prod.fst)
        let some actual := actual? | return none
        return some (← withTransparency .all <| whnf (← pointResultValue state actual))
      | _ => return none
    if let some a ← observe first then
      if let some b ← observe second then
        let equation ← mkEq a b
        if let some answer ← Decide.decideProp equation then return answer
        -- The existing structural codec decides the same equation through
        -- declared aliases and inclusions, with independent kernel checking.
        if (← Codec.conditionProof equation).isSome then return true
        if (← Codec.conditionProof (mkNot equation)).isSome then return false
  observeEquality h trace first second domain target

def realizeClaim (h : Harness) (trace : Trace) (claim : Claim) : TermElabM ExecutionOutcome := do
  let h := enableService { h with demandObjectActions := true } trace
  match claim with
  | .binding => return .internal "a binding entered execution"
  | .implemented value =>
      -- A decision is realized as one; anything else as a value.
      if ← isProp value then discard <| realizeDecision h trace "the decision" value
      else
        let wire ← realize h trace "the value" value
        if (Language.homEnds? (← inferType value)).isSome then
          discard <| realizeArrowObservation h trace wire
      return .holds
  | .literal X _ form L _ left right =>
      let w ← realize h trace left X
      match w.form with
      | .literal form' =>
        unless form'.id == form.id do
          throwStratum .malformed m!"{left} is computed in a different declared literal form"
      | _ =>
        unless w.form.category == form.category do
          throwStratum .malformed m!"{left} changed the fixed literal observation category"
      let literalType ← mkConstWithFreshMVarLevels form.type
      unless ← ComputationalData.plainType literalType do
        throwStratum .noImplementation "the literal observation requires a proof-free declared data representation"
      let literal ← match ← Codec.decode literalType w.json with
        | .ok literal => pure literal
        | .error message => throwStratum .malformed m!"the realized literal no longer decodes: {message}"
      return if ← evaluatedEq literal L then .holds
        else .wrong s!"{left} is not {right}: the registration answered {w.json.compress}"
  | .homs f g _ _ left right =>
      let mut a ← realize h trace left f
      let mut b ← realize h trace right g
      unless (← isDefEq (← inferType a.value) (← inferType f)) &&
          (← isDefEq (← inferType b.value) (← inferType g)) do
        throwStratum .malformed m!"the computed arrows changed the fixed comparison endpoints"
      let some (domain, target) := Language.homEnds? (← inferType f)
        | throwStratum .noImplementation "the compared arrows have no retained categorical endpoints"
      unless ← withTransparency .all <| isDefEq domain (← closedElementDomain (← registryState)) do
        a ← realizeArrowObservation h trace a
        b ← realizeArrowObservation h trace b
        return if ← observeComputedPoints h trace a b f then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      if (match a.payload with | .computed .. => true | _ => false) ||
          (match b.payload with | .computed .. => true | _ => false) then
        return if ← observeComputedPoints h trace a b f then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      -- Only literal data on both sides is a value the kernel compares itself. Any other
      -- uncomputed side (an element expression, a power-object map, a composite) is a request
      -- that only a registered computation evaluates.
      unless (match a.form, b.form with | .literal _, .literal _ => true | _, _ => false) do
        return if ← observeEquality h trace a b domain target then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      -- The retained formal maps fix the question; only the actual computational answer
      -- data is compared here. Using Wire.value would hide a well-formed wrong answer.
      let observe (wire : Wire) (formal : Expr) : TermElabM Expr := do
        let state ← registryState
        let some category := state.categories.find? (·.id == wire.form.category)
          | throwStratum .malformed "the computed map has no declared category"
        match ← decodeValue trace category (← inferType formal) wire.json with
        | .ok (actual, _) => return actual
        | .error message =>
            throwStratum .noImplementation m!"the computational map has no independent observation decoder: {message}"
      let actualLeft ← observe a f
      let actualRight ← observe b g
      return if ← evaluatedPointEq trace actualLeft actualRight then .holds
        else .wrong s!"{left} is not {right}: computed as {a.json.compress} and \
          {b.json.compress}"
  | .decision prop expected shown | .judged _ prop expected shown =>
      let (answer, json) ← realizeDecision h trace shown prop
      return if ← evaluatedEq answer (toExpr expected) then .holds
        else .wrong s!"{shown} is not the answer: the registration answered {json.compress}"

/-- Representation-only normalization: metadata and bound-variable spelling carry no
mathematical identity. Operations, constants, routes, parameters and logical constructors
remain intact; there is no reduction by truth, provability or logical equivalence. -/
partial def canonicalTerm (term : Expr) : Expr :=
  Id.run (MonadStateCacheT.run (visit term))
where
  /-- Share only exact syntax within this traversal. Binder annotations and all
  data remain significant; neither reduction nor proof irrelevance is a cache key. -/
  visit (term : Expr) : MonadStateCacheT ExprStructEq Expr Id Expr :=
    checkCache (ExprStructEq.mk term) fun _ => do
      match term with
      | .mdata _ child => visit child
      | .app fn arg => return .app (← visit fn) (← visit arg)
      | .lam _ type body info => return .lam .anonymous (← visit type) (← visit body) info
      | .forallE _ type body info => return .forallE .anonymous (← visit type) (← visit body) info
      | .letE _ type value body nondep =>
          return .letE .anonymous (← visit type) (← visit value) (← visit body) nondep
      | .proj type index child => return .proj type index (← visit child)
      | term => return term

def questionTerm (term : Expr) : TermElabM Expr := do
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then throwError "question contains unresolved typed terms"
  return canonicalTerm term

/-- Instantiate the complete tree without reducing its relations or logic. -/
partial def instantiateQuestion : Question → TermElabM Question
  | .proposition term => return .proposition (← questionTerm term)
  | .judgement relation terms route declarations _ => do
      let terms ← terms.mapM questionTerm
      let types ← terms.mapM fun term => do questionTerm (← inferType term)
      return .judgement relation terms route declarations types
  | .conjunction left right => return .conjunction (← instantiateQuestion left) (← instantiateQuestion right)
  | .negation question => return .negation (← instantiateQuestion question)

partial def showQuestion : Question → TermElabM String
  | .proposition term => return s!"{← ppExpr term}"
  | .judgement relation terms route declarations _ => do
      let terms ← terms.mapM fun term => return s!"({← ppExpr term} : {← ppExpr (← inferType term)})"
      return s!"{relation} [{String.intercalate ", " terms.toList}] via {route.toList}; declarations {declarations.toList}"
  | .conjunction left right => return s!"({← showQuestion left}) and ({← showQuestion right})"
  | .negation question => return s!"not ({← showQuestion question})"

partial def encodeQuestion (table : TermTable) : Question → TermElabM Json
  | .proposition term => return Json.arr #[toJson "proposition", toJson (← table.encode term)]
  | .judgement relation terms route declarations types => do
      let terms ← terms.mapM table.encode
      let types ← types.mapM table.encode
      return Json.arr #[toJson "judgement", toJson relation, toJson terms,
        toJson (route.map reprStr), toJson (declarations.map reprStr), toJson types]
  | .conjunction left right =>
      return Json.arr #[toJson "and", ← encodeQuestion table left, ← encodeQuestion table right]
  | .negation question => return Json.arr #[toJson "not", ← encodeQuestion table question]

/-- The semantic question a claim asks, as a fingerprint of its elaborated proposition (and, for a
decision, the expected answer): what an admitted assertion means under this kernel, parser and
pin, compared across candidates by `scripts/check_question_permanence.py` (gov-meaning-permanence).
It is never the statement's text, its outcome, or whether it is provable. -/
def claimQuestion : Claim → TermElabM (String × String)
  | .binding => throwError "a binding has no assertion question"
  | .judged question proposition expected _ => do
      let question ← instantiateQuestion question
      let proposition ← questionTerm proposition
      unless ← isProp proposition do
        throwError "the judged claim has no proposition to evaluate"
      let propositionType ← questionTerm (← inferType proposition)
      let table ← TermTable.new
      let questionRoot ← encodeQuestion table question
      let proposition ← table.encode proposition
      let propositionType ← table.encode propositionType
      let roots := Json.mkObj [("question", questionRoot),
        ("proposition", toJson proposition), ("type", toJson propositionType)]
      return (s!"judged:{expected}:{← table.finish roots}",
        s!"judged:{expected}: {← showQuestion question}")
  | .implemented value => fingerprint "implemented" value
  | .literal _ _ _ _ prop .. => fingerprint "literal" prop
  | .homs _ _ _ prop .. => fingerprint "homs" prop
  | .decision prop expected _ => fingerprint s!"decision:{expected}" prop
where
  /-- The fingerprint, and the proposition as the acceptance author reads it to confirm the
  interpretation it records. -/
  fingerprint (kind : String) (e : Expr) : TermElabM (String × String) := do
    let e ← questionTerm e
    let type ← questionTerm (← inferType e)
    let table ← TermTable.new
    let root ← table.encode e
    let type ← table.encode type
    return (s!"{kind}:{← table.finish (Json.arr #[toJson root, toJson type])}",
      s!"{kind}: {← ppExpr e}")

/-- An interpreted request, prepared before discharge or realization. The claim and its
operation tree travel together: evaluation consumes this request, rather than elaborating a
second request or recovering a question from an answer. -/
structure TypedQuestion where
  claim : Claim
  trace : Std.HashMap Expr Node
  identity : String × String
  mathematicalRevision : String

/-- The complete existing presentation record, encoded once for both canonical keys
and the final operation snapshot. Ordered routes, parameters and applications are retained. -/
def encodeParameterPresentation (encode : Expr → TermElabM Nat)
    (source : ParameterPresentation) : TermElabM Json := do
  return Json.arr #[toJson source.source.raw, toJson source.sourceCategory.raw,
    toJson source.targetCategory.raw, toJson (← source.params.mapM encode),
    toJson (source.route.map reprStr), toJson (← source.applications.mapM encode),
    toJson (source.carrierRoute.map reprStr),
    toJson (source.identifications.map Name.toString), toJson (← encode source.object),
    toJson (← encode source.image), toJson (← encode source.identity)]

/-- Keep the prior source/route/parameter ordering where it distinguishes records,
and resolve its ties by every retained field. Source enumeration cannot select an order. -/
def orderParameterPresentations (source : TermTable) (presentations : Array ParameterPresentation) :
    TermElabM (Array ParameterPresentation) := do
  let keyed ← presentations.mapM fun presentation => do
    let parameters ← presentation.params.mapM fun term => do
      source.rootIdentity (← source.encode term)
    return (presentation.source.raw ++ reprStr presentation.route ++ reprStr parameters, presentation)
  QuestionIdentity.orderByCompleteKey keyed fun presentation => do
    let target ← TermTable.new
    let remap ← TermRemap.new source target
    let record ← encodeParameterPresentation remap.encodeTerm presentation
    target.finish record

/-- Complete operation source provenance, including each comparison's constructor
and whiskering contexts separately from its checked typed witness. -/
def encodeOperationSource (encode : Expr → TermElabM Nat) (source : OperationSource) :
    TermElabM Json :=
  OperationAgreement.encodeSource encode source

def encodeOperationCandidate (encode : Expr → TermElabM Nat) (candidate : OperationCandidate) :
    TermElabM Json :=
  OperationAgreement.encodeCandidate encode candidate

def encodeOperationFamilyComparison (encode : Expr → TermElabM Nat)
    (comparison : OperationFamilyComparison) : TermElabM Json := do
  return Json.arr #[toJson comparison.left, toJson comparison.right,
    toJson comparison.leftSource, toJson comparison.rightSource,
    toJson (← comparison.parameters.mapM encode), toJson (← encode comparison.leftFamily),
    toJson (← encode comparison.rightFamily), toJson (← encode comparison.leftType),
    toJson (← encode comparison.rightType), toJson (← encode comparison.identity)]

/-- The operation schema has one encoder. Complete tie keys and the final snapshot
both use this same field traversal; typed terms use the unchanged proof-proposition quotient. -/
def encodeSnapshotNode (source : TermTable) (encode : Expr → TermElabM Nat)
    (node : Node) : TermElabM Json := do
  let encodeContext (context : CategoryContext) : TermElabM Json := do
    return Json.arr #[toJson (reprStr context.expression), toJson (← encode context.bundle)]
  let encodeComparisons (comparisons : Array (RouteComparison × Expr)) : TermElabM Json := do
    return Json.arr (← comparisons.mapM fun (context, value) => do
      pure <| Json.arr #[OperationAgreement.encodeRouteComparison context, toJson (← encode value)])
  match node with
  | .object id parameters =>
      pure (Json.arr #[toJson "object", toJson id.raw, toJson (← parameters.mapM encode)])
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      pure (Json.arr #[toJson "parameterTransport", toJson source.raw,
        toJson sourceCategory.raw, toJson targetCategory.raw, toJson (route.map reprStr),
        toJson (← encode receiver)])
  | .structureTransport sourceCategory targetCategory route receiver =>
      pure (Json.arr #[toJson "structureTransport", toJson sourceCategory.raw,
        toJson targetCategory.raw, toJson (route.map reprStr), toJson (← encode receiver)])
  | .proofRefinement classifier sourceCategory targetCategory source action identity =>
      pure (Json.arr #[toJson "proofRefinement", toJson classifier.raw,
        toJson sourceCategory.raw, toJson targetCategory.raw,
        toJson (← encode source), toJson (← encode action), toJson (← encode identity)])
  | .parameterEquivalence expected representative sources => do
      let sources ← orderParameterPresentations source sources
      let data ← sources.mapM (encodeParameterPresentation encode)
      pure (Json.arr #[toJson "parameterEquivalence", toJson (← encode expected),
        toJson (← encode representative), Json.arr data])
  | .operationEquivalence representative chosen candidates comparisons =>
      pure (Json.arr #[toJson "operationEquivalence", toJson (← encode representative),
        toJson chosen, Json.arr (← candidates.mapM (encodeOperationCandidate encode)),
        Json.arr (← comparisons.mapM (encodeOperationFamilyComparison encode))])
  | .retainedRoute source target route applications receiver =>
      pure (Json.arr #[toJson "retainedRoute", toJson source.raw, toJson target.raw,
        toJson (route.map reprStr), toJson (← applications.mapM encode),
        toJson (← encode receiver)])
  | .namedMorphism id params =>
      pure (Json.arr #[toJson "namedMorphism", toJson id.raw, toJson (← params.mapM encode)])
  | .admittedPoint id category params original originalCategory source target =>
      pure (Json.arr #[toJson "admittedPoint", toJson id.raw, toJson category.raw,
        toJson (← params.mapM encode), toJson (← encode original),
        toJson originalCategory.raw, toJson (← encode source), toJson (← encode target)])
  | .constrainedPoint constructor category domain source target original =>
      pure (Json.arr #[toJson "constrainedPoint", toJson constructor.toString,
        toJson category.raw, toJson (← encode domain), toJson (← encode source),
        toJson (← encode target), toJson (← encode original)])
  | .powerObjectMap id field params =>
      pure (Json.arr #[toJson "powerObjectMap", toJson id.raw, toJson field,
        toJson (← params.mapM encode)])
  | .objectField id field category params =>
      pure (Json.arr #[toJson "objectField", toJson id.raw, toJson field, toJson category.raw,
        toJson (← params.mapM encode)])
  | .namedInclusion id category params source target =>
      pure (Json.arr #[toJson "namedInclusion", toJson id.raw, toJson category.raw,
        toJson (← params.mapM encode), toJson (← encode source),
        toJson (← encode target)])
  | .callableRecipe category domain target body =>
      pure (Json.arr #[toJson "callableRecipe", toJson category.raw,
        toJson (← encode domain), toJson (← encode target),
        toJson (← encode body)])
  | .namedCallable address category params =>
      pure (Json.arr #[toJson "namedCallable", toJson address, toJson category.raw,
        toJson (← params.mapM encode)])
  | .presentation id params inverse =>
      pure (Json.arr #[toJson "presentation", toJson id.raw,
        toJson (← params.mapM encode), toJson inverse])
  | .generator id params =>
      pure (Json.arr #[toJson "generator", toJson id.raw, toJson (← params.mapM encode)])
  | .elementNumeral value target selected =>
      pure (Json.arr #[toJson "elementNumeral", toJson value,
        toJson (← encode target), toJson (← encode selected)])
  | .elementValue point target selected =>
      pure (Json.arr #[toJson "elementValue", toJson (← encode point),
        toJson (← encode target), toJson (← encode selected)])
  | .productMediator category presentation domain left right =>
      pure (Json.arr #[toJson "productMediator", toJson category.raw,
        toJson (← encode presentation), toJson (← encode domain),
        toJson (← encode left), toJson (← encode right)])
  | .morphismComposition category first second source middle target =>
      pure (Json.arr #[toJson "morphismComposition", toJson category.raw,
        toJson (← encode first), toJson (← encode second),
        toJson (← encode source), toJson (← encode middle),
        toJson (← encode target)])
  | .morphismIdentity category object =>
      pure (Json.arr #[toJson "morphismIdentity", toJson category.raw,
        toJson (← encode object)])
  | .contextualRoute source target route applications receiver morphism =>
      pure (Json.arr #[toJson "contextualRoute", ← encodeContext source, ← encodeContext target,
        toJson (route.map reprStr), toJson (← applications.mapM encode),
        toJson (← encode receiver), toJson morphism])
  | .contextualComposition context first second source middle target =>
      pure (Json.arr #[toJson "contextualComposition", ← encodeContext context,
        toJson (← encode first), toJson (← encode second), toJson (← encode source),
        toJson (← encode middle), toJson (← encode target)])
  | .contextualIdentity context object =>
      pure (Json.arr #[toJson "contextualIdentity", ← encodeContext context,
        toJson (← encode object)])
  | .contextualArrow context hom source target =>
      pure (Json.arr #[toJson "contextualArrow", ← encodeContext context,
        toJson (← encode hom), toJson (← encode source), toJson (← encode target)])
  | .arrowProjection receiver =>
      pure (Json.arr #[toJson "arrowProjection", toJson (← encode receiver)])
  | .limitProjection receiver index =>
      pure (Json.arr #[toJson "limitProjection", toJson (← encode receiver),
        toJson (← encode index)])
  | .structuredProjection receiver field index =>
      pure (Json.arr #[toJson "structuredProjection", toJson (← encode receiver),
        toJson field, toJson index])
  | .pointView source target route applications argument =>
      pure (Json.arr #[toJson "pointView", toJson (← encode source),
        toJson (← encode target), toJson (route.map reprStr),
        toJson (← applications.mapM encode), toJson (← encode argument)])
  | .operationPoint id params comparison operation target selected =>
      pure (Json.arr #[toJson "operationPoint", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode comparison),
        toJson (← encode operation), toJson (← encode target),
        toJson (← encode selected)])
  | .operationApply id params operands target selected =>
      pure (Json.arr #[toJson "operationApply", toJson id.raw,
        toJson (← params.mapM encode), toJson (← operands.mapM encode),
        toJson (← encode target), toJson (← encode selected)])
  | .presentationApply id params inverse source target argument =>
      pure (Json.arr #[toJson "presentationApply", toJson id.raw,
        toJson (← params.mapM encode), toJson inverse, toJson (← encode source),
        toJson (← encode target), toJson (← encode argument)])
  | .morphismTransport sourceCategory targetCategory route receiver =>
      pure (Json.arr #[toJson "morphismTransport", toJson sourceCategory.raw,
        toJson targetCategory.raw, toJson (route.map reprStr), toJson (← encode receiver)])
  | .functor id params receiver =>
      pure (Json.arr #[toJson "functor", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode receiver)])
  | .categoryParameter id params =>
      pure (Json.arr #[toJson "categoryParameter", toJson id.raw, toJson (← params.mapM encode)])
  | .functorParameter id params =>
      pure (Json.arr #[toJson "functorParameter", toJson id.raw, toJson (← params.mapM encode)])
  | .cartesian id params baseMorphism receiver field =>
      pure (Json.arr #[toJson "cartesian", toJson id.raw, toJson (← params.mapM encode),
        toJson (← encode baseMorphism), toJson (← encode receiver), toJson field])
  | .construction id params receiver =>
      pure (Json.arr #[toJson "construction", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode receiver)])
  | .constructionMap id params source target morphism =>
      pure (Json.arr #[toJson "constructionMap", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode source),
        toJson (← encode target), toJson (← encode morphism)])
  | .coreObject category object =>
      pure (Json.arr #[toJson "coreObject", ← encodeContext category, toJson (← encode object)])
  | .coreIso category source target forward backward =>
      pure (Json.arr #[toJson "coreIso", ← encodeContext category,
        toJson (← encode source), toJson (← encode target),
        toJson (← encode forward), toJson (← encode backward)])
  | .selectedLift id params source inclusion monic =>
      pure (Json.arr #[toJson "selectedLift", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode source),
        toJson (← encode inclusion), toJson (← encode monic)])
  | .liftProjection receiver field =>
      pure (Json.arr #[toJson "liftProjection", toJson (← encode receiver), toJson field])
  | .liftFactor receiver baseMap cone proof =>
      pure (Json.arr #[toJson "liftFactor", toJson (← encode receiver),
        toJson (← encode baseMap), toJson (← encode cone), toJson (← encode proof)])
  | .cellComponent id params constructors inverse receiver =>
      pure (Json.arr #[toJson "cellComponent", toJson id.raw,
        toJson (← params.mapM encode), toJson (constructors.map (·.raw)),
        toJson inverse, toJson (← encode receiver)])
  | .cellEndpoint id params constructors inverse right receiver =>
      pure (Json.arr #[toJson "cellEndpoint", toJson id.raw,
        toJson (← params.mapM encode), toJson (constructors.map (·.raw)),
        toJson inverse, toJson right, toJson (← encode receiver)])
  | .binder id params domain body admitted =>
      pure (Json.arr #[toJson "binder", toJson id.raw, toJson (← params.mapM encode),
        toJson (← encode domain), toJson (← encode body),
        toJson (← encode admitted)])
  | .arrow category morphism source target =>
      pure (Json.arr #[toJson "arrow", toJson category.raw,
        toJson (← encode morphism), toJson (← encode source),
        toJson (← encode target)])
  | .literal form literal =>
      pure (Json.arr #[toJson "literal", toJson form.raw, toJson (← encode literal)])
  | .method id route receiver recordedComparisons =>
      pure (Json.arr #[toJson "method", toJson id.raw, toJson (route.map reprStr),
        toJson (← encode receiver), ← encodeComparisons recordedComparisons])
  | .methodWithLifts id route lifts receiver recordedComparisons =>
      pure (Json.arr #[toJson "methodWithLifts", toJson id.raw, toJson (route.map reprStr),
        toJson (lifts.map (·.raw)), toJson (← encode receiver),
        ← encodeComparisons recordedComparisons])
  | .property id route receiver recordedComparisons =>
      pure (Json.arr #[toJson "property", toJson id.raw, toJson (route.map reprStr),
        toJson (← encode receiver), ← encodeComparisons recordedComparisons])
  | .limit id diagram lift =>
      pure (Json.arr #[toJson "limit", toJson id.raw, toJson (← encode diagram),
        toJson (lift.map (·.raw))])

/-- Serialize every retained keyed operation independently of hash-map enumeration,
including distinct raw terms with the same proof-irrelevant root. No record is deduplicated.
Shared source encoding avoids reopening typed terms when a complete tie key is required. -/
def snapshot (nodes : Array (Expr × Node))
    (timings : Option (IO.Ref (Array (String × Nat))) := none) : TermElabM String := do
  let started ← IO.monoMsNow
  let record (stage : String) (before : Nat) : TermElabM Nat := do
    let now ← IO.monoMsNow
    if let some sink := timings then sink.modify (·.push (stage, now - before))
    return now
  let source ← TermTable.new
  let rooted ← nodes.mapM fun (term, node) => do
    return (← source.encode term, node)
  let afterSource ← record "source_encoding" started
  let keyed ← rooted.mapM fun (root, node) => do
    return (← source.rootIdentity root, (root, node))
  let ordered ← QuestionIdentity.orderByCompleteKey keyed fun (_, node) => do
    let target ← TermTable.new
    let remap ← TermRemap.new source target
    target.finish (← encodeSnapshotNode source remap.encodeTerm node)
  let afterKeys ← record "remapped_keys_and_sort" afterSource
  let table ← TermTable.new
  let remap ← TermRemap.new source table
  let operations ← ordered.mapM fun (sourceRoot, node) => do
    let root ← remap.encode sourceRoot
    let operation ← encodeSnapshotNode source remap.encodeTerm node
    return Json.arr #[toJson root, operation]
  let afterFields ← record "operation_fields" afterKeys
  let result ← table.finish (Json.arr operations)
  discard <| record "compression" afterFields
  return result

/-- Prepare the question against the current mathematical environment. A reader cannot
produce an interpretation record until its typed terms are complete. The optional timing
sink observes the production path without affecting the request or its identity. -/
def interpret (scope : Scope) (stx : Syntax)
    (timings : Option (IO.Ref (Array (String × Nat))) := none) : TermElabM TypedQuestion := do
  let started ← IO.monoMsNow
  let record (stage : String) (before : Nat) : TermElabM Nat := do
    let now ← IO.monoMsNow
    if let some sink := timings then sink.modify (·.push (stage, now - before))
    return now
  let trace ← (Trace.new : IO _)
  let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
  let claim ← (Language.claim scope stx).run { trace := some trace, closedTerms := some closedTerms }
  let afterRead ← record "semantic_reading" started
  let .ok manifest := Json.parse (← IO.FS.readFile "lake-manifest.json")
    | throwError "cannot identify the mathematical dependency revision"
  let .ok packages := (manifest.getObjVal? "packages").bind (·.getArr?)
    | throwError "cannot read the mathematical dependency revision"
  let some package := packages.find? fun package =>
      (package.getObjValAs? String "name").toOption == some "lean_categories"
    | throwError "no mathematical dependency revision"
  let .ok mathematicalRevision := package.getObjValAs? String "rev"
    | throwError "no pinned mathematical dependency revision"
  let (identity, shown) ← claimQuestion claim
  let afterQuestion ← record "question_construction" afterRead
  let instantiateContext (context : CategoryContext) : TermElabM CategoryContext := do
    return { context with bundle := (← instantiateMVars context.bundle) }
  let instantiateComparisons (comparisons : Array (RouteComparison × Expr)) :=
    comparisons.mapM fun (context, value) => do
      pure (context, ← instantiateMVars value)
  let nodes ← (← trace.get).toArray.mapM fun (term, node) => do
    let term ← instantiateMVars term
    let node : Node ← match node with
      | .object id parameters => pure (.object id (← parameters.mapM instantiateMVars))
      | .parameterTransport source sourceCategory targetCategory route receiver =>
          pure (.parameterTransport source sourceCategory targetCategory route (← instantiateMVars receiver))
      | .structureTransport sourceCategory targetCategory route receiver =>
          pure (.structureTransport sourceCategory targetCategory route (← instantiateMVars receiver))
      | .proofRefinement classifier sourceCategory targetCategory source action identity =>
          pure (.proofRefinement classifier sourceCategory targetCategory
            (← instantiateMVars source) (← instantiateMVars action) (← instantiateMVars identity))
      | .parameterEquivalence expected representative sources => do
          let sources ← sources.mapM fun source => do
            pure { source with
              params := ← source.params.mapM instantiateMVars
              applications := ← source.applications.mapM instantiateMVars
              object := ← instantiateMVars source.object
              image := ← instantiateMVars source.image
              identity := ← instantiateMVars source.identity }
          pure (.parameterEquivalence (← instantiateMVars expected)
            (← instantiateMVars representative) sources)
      | .operationEquivalence representative chosen candidates comparisons => do
          let candidates ← candidates.mapM fun candidate => do
            let sources ← candidate.sources.mapM fun source => do
              return { source with
                context := ← instantiateContext source.context
                receiver := ← instantiateMVars source.receiver
                applications := ← source.applications.mapM instantiateMVars
                comparisonWitnesses := ← source.comparisonWitnesses.mapM instantiateMVars }
            return { candidate with
              application := ← instantiateMVars candidate.application
              result := ← instantiateMVars candidate.result
              sources }
          let comparisons ← comparisons.mapM fun comparison => do
            return { comparison with
              parameters := ← comparison.parameters.mapM instantiateMVars
              leftFamily := ← instantiateMVars comparison.leftFamily
              rightFamily := ← instantiateMVars comparison.rightFamily
              leftType := ← instantiateMVars comparison.leftType
              rightType := ← instantiateMVars comparison.rightType
              identity := ← instantiateMVars comparison.identity }
          pure (.operationEquivalence (← instantiateMVars representative) chosen candidates comparisons)
      | .retainedRoute source target route applications receiver =>
          pure (.retainedRoute source target route (← applications.mapM instantiateMVars)
            (← instantiateMVars receiver))
      | .namedMorphism id params => pure (.namedMorphism id (← params.mapM instantiateMVars))
      | .powerObjectMap id field params =>
          pure (.powerObjectMap id field (← params.mapM instantiateMVars))
      | .objectField id field category params =>
          pure (.objectField id field category (← params.mapM instantiateMVars))
      | .namedInclusion id category params source target =>
          pure (.namedInclusion id category (← params.mapM instantiateMVars)
            (← instantiateMVars source) (← instantiateMVars target))
      | .callableRecipe category domain target body =>
          pure (.callableRecipe category (← instantiateMVars domain)
            (← instantiateMVars target) (← instantiateMVars body))
      | .namedCallable address category params =>
          pure (.namedCallable address category (← params.mapM instantiateMVars))
      | .admittedPoint id category params original originalCategory source target =>
          pure (.admittedPoint id category (← params.mapM instantiateMVars)
            (← instantiateMVars original) originalCategory
            (← instantiateMVars source) (← instantiateMVars target))
      | .constrainedPoint constructor category domain source target original =>
          pure (.constrainedPoint constructor category (← instantiateMVars domain)
            (← instantiateMVars source) (← instantiateMVars target) (← instantiateMVars original))
      | .presentation id params inverse =>
          pure (.presentation id (← params.mapM instantiateMVars) inverse)
      | .generator id params => pure (.generator id (← params.mapM instantiateMVars))
      | .elementNumeral value target selected =>
          pure (.elementNumeral value (← instantiateMVars target) (← instantiateMVars selected))
      | .elementValue point target selected =>
          pure (.elementValue (← instantiateMVars point) (← instantiateMVars target)
            (← instantiateMVars selected))
      | .productMediator category presentation domain left right =>
          pure (.productMediator category (← instantiateMVars presentation)
            (← instantiateMVars domain) (← instantiateMVars left) (← instantiateMVars right))
      | .morphismComposition category first second source middle target =>
          pure (.morphismComposition category (← instantiateMVars first)
            (← instantiateMVars second) (← instantiateMVars source)
            (← instantiateMVars middle) (← instantiateMVars target))
      | .morphismIdentity category object =>
          pure (.morphismIdentity category (← instantiateMVars object))
      | .contextualRoute source target route applications receiver morphism =>
          pure (.contextualRoute (← instantiateContext source) (← instantiateContext target)
            route (← applications.mapM instantiateMVars) (← instantiateMVars receiver) morphism)
      | .contextualComposition context first second source middle target =>
          pure (.contextualComposition (← instantiateContext context)
            (← instantiateMVars first) (← instantiateMVars second)
            (← instantiateMVars source) (← instantiateMVars middle) (← instantiateMVars target))
      | .contextualIdentity context object =>
          pure (.contextualIdentity (← instantiateContext context) (← instantiateMVars object))
      | .contextualArrow context hom source target =>
          pure (.contextualArrow (← instantiateContext context) (← instantiateMVars hom)
            (← instantiateMVars source) (← instantiateMVars target))
      | .arrowProjection receiver =>
          pure (.arrowProjection (← instantiateMVars receiver))
      | .limitProjection receiver index =>
          pure (.limitProjection (← instantiateMVars receiver) (← instantiateMVars index))
      | .structuredProjection receiver field index =>
          pure (.structuredProjection (← instantiateMVars receiver) field index)
      | .cartesian id params baseMorphism receiver field =>
          pure (.cartesian id (← params.mapM instantiateMVars)
            (← instantiateMVars baseMorphism) (← instantiateMVars receiver) field)
      | .pointView source target route applications argument =>
          pure (.pointView (← instantiateMVars source) (← instantiateMVars target) route
            (← applications.mapM instantiateMVars) (← instantiateMVars argument))
      | .operationPoint id params comparison operation target selected =>
          pure (.operationPoint id (← params.mapM instantiateMVars)
            (← instantiateMVars comparison) (← instantiateMVars operation)
            (← instantiateMVars target) (← instantiateMVars selected))
      | .operationApply id params operands target selected =>
          pure (.operationApply id (← params.mapM instantiateMVars)
            (← operands.mapM instantiateMVars) (← instantiateMVars target)
            (← instantiateMVars selected))
      | .presentationApply id params inverse source target argument =>
          pure (.presentationApply id (← params.mapM instantiateMVars) inverse
            (← instantiateMVars source) (← instantiateMVars target) (← instantiateMVars argument))
      | .morphismTransport sourceCategory targetCategory route receiver =>
          pure (.morphismTransport sourceCategory targetCategory route (← instantiateMVars receiver))
      | .functor id params receiver =>
          pure (.functor id (← params.mapM instantiateMVars) (← instantiateMVars receiver))
      | .categoryParameter id params =>
          pure (.categoryParameter id (← params.mapM instantiateMVars))
      | .functorParameter id params =>
          pure (.functorParameter id (← params.mapM instantiateMVars))
      | .construction id params receiver =>
          pure (.construction id (← params.mapM instantiateMVars) (← instantiateMVars receiver))
      | .constructionMap id params source target morphism =>
          pure (.constructionMap id (← params.mapM instantiateMVars)
            (← instantiateMVars source) (← instantiateMVars target) (← instantiateMVars morphism))
      | .coreObject context object =>
          pure (.coreObject (← instantiateContext context) (← instantiateMVars object))
      | .coreIso category source target forward backward =>
          pure (.coreIso (← instantiateContext category) (← instantiateMVars source) (← instantiateMVars target)
            (← instantiateMVars forward) (← instantiateMVars backward))
      | .selectedLift id params source inclusion monic =>
          pure (.selectedLift id (← params.mapM instantiateMVars) (← instantiateMVars source)
            (← instantiateMVars inclusion) (← instantiateMVars monic))
      | .liftProjection receiver field => pure (.liftProjection (← instantiateMVars receiver) field)
      | .liftFactor receiver baseMap cone proof =>
          pure (.liftFactor (← instantiateMVars receiver) (← instantiateMVars baseMap)
            (← instantiateMVars cone) (← instantiateMVars proof))
      | .cellComponent id params constructors inverse receiver =>
          pure (.cellComponent id (← params.mapM instantiateMVars) constructors inverse
            (← instantiateMVars receiver))
      | .cellEndpoint id params constructors inverse right receiver =>
          pure (.cellEndpoint id (← params.mapM instantiateMVars) constructors inverse right
            (← instantiateMVars receiver))
      | .binder id params domain body admitted =>
          pure (.binder id (← params.mapM instantiateMVars) (← instantiateMVars domain)
            (← instantiateMVars body) (← instantiateMVars admitted))
      | .arrow category morphism source target =>
          pure (.arrow category (← instantiateMVars morphism) (← instantiateMVars source)
            (← instantiateMVars target))
      | .literal form literal => pure (.literal form (← instantiateMVars literal))
      | .method id route receiver recordedComparisons =>
          pure (.method id route (← instantiateMVars receiver)
            (← instantiateComparisons recordedComparisons))
      | .methodWithLifts id route lifts receiver recordedComparisons =>
          pure (.methodWithLifts id route lifts (← instantiateMVars receiver)
            (← instantiateComparisons recordedComparisons))
      | .property id route receiver recordedComparisons =>
          pure (.property id route (← instantiateMVars receiver)
            (← instantiateComparisons recordedComparisons))
      | .limit id diagram lift => pure (.limit id (← instantiateMVars diagram) lift)
    return (term, node)
  discard <| record "trace_instantiation" afterQuestion
  let tree ← snapshot nodes timings
  return { claim := claim
           trace := Std.HashMap.ofArray nodes
           mathematicalRevision := mathematicalRevision
           identity := (s!"{identity}:operations:{tree}", shown) }

/-- Execute exactly the previously interpreted request. -/
def evaluate (h : Harness) (question : TypedQuestion) : TermElabM ExecutionOutcome := do
  let trace ← IO.mkRef question.trace
  unless h.computationOnly do
    let attempt ← discharge question.claim (some trace)
    if let some outcome := attempt then return outcome
  realizeClaim h trace question.claim

/-- Runtime failures cannot assert mathematical invalidity or semantic ambiguity. Those
judgements belong to interpretation; an unexpected semantic exception during evaluation is
an interpreter defect. -/
def executionFailure (e : Exception) : TermElabM ExecutionOutcome := do
  let reason ← e.toMessageData.toString
  if Exception.hasConflictingStrata e then return .internal reason
  return match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization => .gap reason
    | some .unavailable => .unavailable reason
    | some .malformed => .malformed reason
    | _ => .internal reason

/-- Interpret before execution, retaining the same request through every later outcome.
Bindings are read without being counted as assertions. Incomplete interpretations fail visibly;
no operand list or truth value stands in for their question. -/
def runAsking (h : Harness) (scope : Scope) (stx : Syntax) :
    TermElabM (Outcome × Scope × Option (String × String)) := do
  if let some (x, t) ← letBinding? stx then
    let bind : TermElabM (Outcome × Scope × Option (String × String)) := do
      -- A binding has the same closed reading context as an assertion. Keep this
      -- cache local to the statement: later bindings may change the scope.
      let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
      discard <| (Language.claim scope stx).run { closedTerms := some closedTerms }
      return (.holds, scope.insert x t, none)
    return ← tryCatchRuntimeEx bind fun e => return (← Outcome.ofException e, scope.insert x t, none)
  let interpreted ← tryCatchRuntimeEx (Except.ok <$> interpret scope stx)
    fun e => return .error (← Outcome.ofException e)
  match interpreted with
  | .error outcome => return (outcome, scope, none)
  | .ok question =>
      let outcome ← tryCatchRuntimeEx (evaluate h question) executionFailure
      return (outcome.toOutcome, scope, some question.identity)

/-- `runAsking` without the question. -/
def run (h : Harness) (scope : Scope) (stx : Syntax) : TermElabM (Outcome × Scope) := do
  let (outcome, scope, _) ← runAsking h scope stx
  return (outcome, scope)

end Realize

end CasCatalogue
