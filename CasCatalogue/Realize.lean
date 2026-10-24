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
public import CasCatalogue.ObjectPresentation
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

inductive ComputationScope where
  | portable
  | owned (backend : String) (session : Nat)

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

/-- An accepted change from the fixed semantic endpoint to the representation
used by its actual computational data. Both map descriptors retain their complete
declaration parameters; the comparison itself comes only from the catalogue. -/
structure EndpointPresentation where
  comparison : Expr
  forward : Json
  backward : Json

/-- A complete kernel-owned source snapshot for a proof-only refinement. -/
structure WireSnapshot where
  form : Form
  payload : WirePayload
  presentationIsos : Array Expr
  objectIso : Option Expr
  liftExecution : Option LiftExecution := none
  endpointPresentation : Option EndpointPresentation := none
  categoryContext : Option CategoryContext := none
  constructionInputs : Option (Expr × ComputationalData.InterfaceObjects) := none

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
  /-- Full source snapshots, restored only by their checked classifier forgetful prefixes. -/
  proofSources : List WireSnapshot := []
  liftExecution : Option LiftExecution := none
  categoryContext : Option CategoryContext := none
  /-- Original formal receiver and its complete pre-dispatch constructor input
  interfaces. Returned fields never populate this table or choose its receiver. -/
  constructionInputs : Option (Expr × ComputationalData.InterfaceObjects) := none

def Wire.value (wire : Wire) : Expr := match wire.payload with
  | .ordinary value _ | .computed value _ => value
  | .construction result _ => result.apex

def Wire.json (wire : Wire) : Json := match wire.payload with
  | .ordinary _ json => json
  | .computed _ (.inline data) => data
  | .computed _ (.opaque _ _ token) => Backend.ComputationalValue.encode (.opaque token)
  | .computed _ (.owned _ _ data) => data
  | .construction result _ => Json.mkObj [("ctor", "constructionApex"),
      ("args", Json.arr #[toJson wire.form.id, result.diagramJson, result.json])]

def Wire.formId (w : Wire) : String := w.form.id

def Wire.owner? (wire : Wire) : Option (String × Nat) := match wire.payload with
  | .computed _ (.opaque backend session _) | .computed _ (.owned backend session _) =>
      some (backend, session)
  | .construction _ (.owned backend session) => some (backend, session)
  | _ => none

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

def mergeOwners (first second : Option (String × Nat)) :
    TermElabM (Option (String × Nat)) := do
  match first, second with
  | none, owner | owner, none => return owner
  | some left, some right =>
      unless left == right do
        throwStratum .unavailable "the computational operands belong to different owning sessions"
      return some left

def sharedOwner (first second : Wire) : TermElabM (Option (String × Nat)) :=
  mergeOwners first.owner? second.owner?

/-- Forward data and its origin without turning a computational result into formal input data. -/
def forwardPayload (source : Wire) (formal : Expr) (json : Json) : WirePayload :=
  match source.owner? with
  | some (backend, session) => .computed formal (.owned backend session json)
  | none => match source.payload with
    | .computed .. | .construction .. => .computed formal (.inline json)
    | .ordinary .. => .ordinary formal json

/-- Combine actual data dependencies without losing portable computations or session ownership. -/
def combinedPayload (formal : Expr) (json : Json) (dependencies : Array Wire) :
    TermElabM WirePayload := do
  let mut owner := none
  let mut computed := false
  for dependency in dependencies do
    owner ← mergeOwners owner dependency.owner?
    computed := computed || (match dependency.payload with
      | .ordinary .. => false
      | _ => true)
  match owner with
  | some (backend, session) => return .computed formal (.owned backend session json)
  | none => return if computed then .computed formal (.inline json) else .ordinary formal json

/-- Transport an entire actual callable through independently accepted endpoint
presentations. No graph is enumerated, no data are recovered from its formal term,
and even a comparison with definitionally equal endpoints is retained. -/
def presentMorphism (input source target : Wire) : TermElabM Wire := do
  if input.morphismFramed then return input
  let type ← whnfR (← inferType input.value)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the whole computational arrow lost its complete hom signature"
  let arguments := type.getAppArgs
  unless ← withTransparency .all <|
      isDefEq arguments[2]! source.value <&&> isDefEq arguments[3]! target.value do
    throwError "the whole computational arrow changed its selected complete endpoints"
  let mut actual := input.value
  let mut data := input.json
  if let some presentation := source.endpointPresentation then
    let type ← whnfR (← inferType presentation.comparison)
    unless type.isAppOf ``CategoryTheory.Iso &&
        (← withTransparency .all <| isDefEq type.getAppArgs[type.getAppArgs.size - 2]!
          source.value) do
      throwError "the domain comparison starts at a different complete object"
    actual ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[← mkAppM ``CategoryTheory.Iso.inv #[presentation.comparison], actual]
    data := Json.mkObj [("ctor", "compose"),
      ("args", Json.arr #[presentation.backward, data])]
  if let some presentation := target.endpointPresentation then
    let type ← whnfR (← inferType presentation.comparison)
    unless type.isAppOf ``CategoryTheory.Iso &&
        (← withTransparency .all <| isDefEq type.getAppArgs[type.getAppArgs.size - 2]!
          target.value) do
      throwError "the codomain comparison starts at a different complete object"
    actual ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[actual, ← mkAppM ``CategoryTheory.Iso.hom #[presentation.comparison]]
    data := Json.mkObj [("ctor", "compose"),
      ("args", Json.arr #[data, presentation.forward])]
  discard <| StructuredResult.checkReconstruction actual
  return { input with
    morphismFramed := true
    payload := (← combinedPayload input.value data #[input, source, target]) }

def mapEndpointPresentation (action : Expr) (descriptor : Json)
    (presentation : Option EndpointPresentation) : TermElabM (Option EndpointPresentation) := do
  let some presentation := presentation | return none
  let mapData := fun data => Json.mkObj [("ctor", "map"), ("args", Json.arr #[descriptor, data])]
  return some {
    comparison := (← mkAppM ``CategoryTheory.Functor.mapIso
      #[← Semantic.asFunctor action, presentation.comparison])
    forward := mapData presentation.forward, backward := mapData presentation.backward }

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
  let object ← Language.oneObject.run {}
  (Language.semanticObject object).run {}

/-- The independently fixed result interface of a point invocation. Closed points use
the registry's selected global point; generalized maps retain their complete map type. -/
def pointResultValue (state : RegistryState) (point : Expr) : TermElabM Expr := do
  let some (domain, target) := Language.homEnds? (← inferType point)
    | throwError "the requested point result lost its complete categorical endpoints"
  unless ← withTransparency .all <| isDefEq domain (← closedElementDomain state) do
    return point
  let action ← Language.functionOf point
  let value := mkApp action (← Language.globalPoint.run {})
  unless ← withTransparency .all <| isDefEq (← inferType value) target do
    throwError "the requested point result changed its declared target"
  return value

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

/-- A harness with no leaf installed. -/
def Harness.empty : IO Harness := return { connections := ← IO.mkRef {}, results := ← IO.mkRef {} }

/-- The harness of the manifest `manifest`, at the directory `root`. -/
def Harness.ofManifest (root : System.FilePath) (manifest : Manifest) : CoreM Harness := do
  let admission := (← registryState).admit manifest
  return { admitted := admission.admitted, rejected := admission.rejected
           backends := manifest.backends, root, connections := ← IO.mkRef {}, results := ← IO.mkRef {} }

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
  -- A backend is killed, not asked to exit: nothing it does is waited on or believed, and
  -- closing its input cannot be relied on while other references to the handle are alive.
  for (_, connection) in connections.toList do
    if let .ok c := connection then Backend.abort c.connection.child

/-- Send the value `input` to the admitted registration of `operation` on its form, and read the
answer: untrusted JSON, with the backend that gave it. -/
def send (h : Harness) (operation : String) (input : Wire)
    (comparisons : Array NaturalTransformationId := #[]) (completeRequest : Bool := false) :
    TermElabM (Json × String) := do
  let state ← registryState
  let some declared := state.operation? operation
    | throwError "the requested computational operation is no longer registered"
  let mut addresses := state.inputAddresses declared input.form
  if completeRequest then
    match declared with
    | .presentation _ =>
      let .ok _ := Backend.PresentationInvocation.decode input.json
        | throwError "a complete comparison request lost its published presentation framing"
      addresses := state.presentationInputAddresses declared input.form
    | _ =>
      let .ok invocation := Backend.PointInvocation.decode input.json
        | throwError "a complete callable request lost its published point-invocation framing"
      unless invocation.operation == operation do
        throwError "a complete callable request changed its declared operation"
      addresses := state.pointInputAddresses declared input.form
  let registrations := h.admitted.filter fun a =>
    a.registration.operation == operation && addresses.contains a.registration.input &&
      (input.owner?.isNone || input.owner?.any (fun owner => owner.1 == a.registration.backend))
  let registration ← match registrations with
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
    ("inputOwner", toJson input.owner?), ("request", input.json)] ++
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
      return (answer, registration.backend)
  | .error e =>
      if let some observations := h.dispatches then
        if let some index := observedIndex then
          observations.modify fun entries =>
            entries.set! index (Json.mkObj (observation ++ [("failure", toJson e.render)]))
      throwStratum e.stratum m!"{e.render}"

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

def computationalScope (h : Harness) (backend : String) (json : Json) :
    TermElabM ComputationScope := do
  if !containsOpaqueData json then return .portable
  let some (.ok session) := (← h.connections.get)[backend]?
    | throwStratum .unavailable "the computational packet has no live owning session"
  return .owned backend session.identity

/-- Retain external data as external data; never elaborate its maps or construction laws. -/
def receiveComputationalData (h : Harness) (backend operation : String) (json : Json)
    (structured : Bool := false) : TermElabM ComputationData := do
  match Backend.ComputationalValue.decode json with
  | .ok (.opaque token) =>
      let some (.ok session) := (← h.connections.get)[backend]?
        | throwStratum .unavailable "the returned value has no live owning session"
      return .opaque backend session.identity token
  | .ok (.inline data) =>
      match ← computationalScope h backend data with
      | .portable => return .inline data
      | .owned backend session => return .owned backend session data
  | .error message =>
      unless structured do malformed backend operation json message
      match ← computationalScope h backend json with
      | .portable => return .inline json
      | .owned backend session => return .owned backend session json

/-- Call the admitted registration of `operation` on the value `input`, and decode the answer as
a value of `resultType`. -/
def call (h : Harness) (operation : String) (input : Wire) (resultType : Expr)
    (comparisons : Array NaturalTransformationId := #[]) :
    TermElabM (Expr × Json) := do
  let (answer, backend) ← send h operation input comparisons
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

mutual

/-- Closed parameter data retaining accepted named-object provenance when present. -/
partial def parameterData (trace : Trace) (value : Expr) : TermElabM Json := do
  let state ← registryState
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
    throwStratum .noImplementation m!"the exact functor parameter is not closed"
  let selected := value.consumeMData
  if let some category := state.categories.find?
      (fun row => selected.getAppFn.constName? == some row.declaration) then
    let data : Backend.CategoryParameter := {
      category := category.id.raw
      parameters := (← declarationData trace category.declaration selected) }
    return data.encode
  if let some constructor := state.constructors.find?
      (fun row => selected.getAppFn.constName? == some row.semantics) then
    let parameters ← declarationData trace constructor.semantics selected
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
      parameters := (← declarationData trace functor.declaration selectedFunctor) }
    return data.encode
  if let some (.object id params) ← (trace.node? value : IO _) then
    return Json.mkObj [("ctor", id.raw), ("args", Json.arr (← params.mapM (parameterData trace)))]
  -- A numeral point of a selected structure: its element descriptor.
  if let some (.elementNumeral n _ selected) ← (trace.node? value : IO _) then
    return Json.mkObj [("ctor", "element"), ("args", Json.arr #[← parameterData trace selected,
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
      Json.mkObj [("ctor", id.raw), ("args", Json.arr (← params.mapM (parameterData trace)))],
      ← parameterData trace receiver])]
  if let some (.retainedRoute _ _ route applications receiver) ← (trace.node? value : IO _) then
    unless route.size == applications.size do
      throwError "the parameter route lost its exact ordered edge applications"
    let mut image := receiver
    let mut json ← parameterData trace receiver
    for (step, application) in route.zip applications do
      if application.hasMVar || application.hasLevelMVar || application.hasFVar ||
          application.hasLooseBVars then
        throwError "the parameter route has an unresolved selected edge application"
      image ← Semantic.objOf application image
      json := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
        ← edgeDescriptor trace step application, json])]
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
        discard <| edgeDescriptor trace step application
        image ← Semantic.objOf application image
      unless (← isDefEq image source.image) && (← isDefEq (← inferType image) expectedType) do
        throwError "the parameter identity class has an incompatible full structured image"
      unless ← Decide.kernelAccepts (← mkEq source.image representative) source.identity do
        throwError "the parameter identity class has no checked full-object identification"
    -- The chosen source is already a checked registered application. Encoding it directly
    -- also avoids following the representative back into its own identity-class trace node.
    let mut json := Json.mkObj [("ctor", chosen.source.raw),
      ("args", Json.arr (← chosen.params.mapM (parameterData trace)))]
    for (step, application) in chosen.route.zip chosen.applications do
      json := Json.mkObj [("ctor", "functorAction"),
        ("args", Json.arr #[← edgeDescriptor trace step application, json])]
    return json
  if let .ok json ← Codec.encode value then return json
  -- `F.obj X` for a registered functor `F`, recognized by its declaration: the action of that
  -- functor on the presentation of `X`.
  let stripped := value.consumeMData
  if stripped.isAppOfArity ``Prefunctor.obj 6 then
    let prefunctor := stripped.getAppArgs[4]!.consumeMData
    let functor := if prefunctor.isAppOfArity ``CategoryTheory.Functor.toPrefunctor 5 then
      prefunctor.appArg! else prefunctor
    let head := (functor.find? fun term =>
      state.functors.any fun entry => term.isConstOf entry.declaration).bind (·.constName?)
    if let some declaration := head then
      if let some entry := state.functors.find? (·.declaration == declaration) then
        return Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
          ← edgeDescriptor trace (.functor entry.id) functor,
          ← parameterData trace stripped.appArg!])]
  let mut candidates : Array (ObjectEntry × Array Expr) := #[]
  let mut exact : Array (ObjectEntry × Array Expr) := #[]
  for entry in state.objects do
    let candidate ← withoutModifyingState do
      let application ← instantiateFresh entry.declaration
      unless ← isDefEq application value do return none
      let application ← instantiateMVars application
      if application.hasMVar || application.hasLevelMVar then return none
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      return some ((application.getAppArgs.zip infos).filterMap fun (arg, info) =>
        if info.isExplicit then some arg else none)
    if let some params := candidate then
      candidates := candidates.push (entry, params)
      -- Definitional equality may recognize several upstream presentations. A
      -- literal occurrence of the registered declaration supplies its own
      -- selected identity; no transparent alias is chosen by catalogue order.
      if value.getAppFn.constName? == some entry.declaration then
        exact := exact.push (entry, params)
  if let #[(entry, params)] := exact then
    return Json.mkObj [("ctor", entry.id.raw),
      ("args", Json.arr (← params.mapM (parameterData trace)))]
  let #[(entry, params)] := candidates
    | throwStratum .noImplementation m!"the exact functor parameter has no unique accepted data \
        presentation: {candidates.size} registered objects ({candidates.map (·.1.id.raw)}) \
        present {value}"
  return Json.mkObj [("ctor", entry.id.raw), ("args", Json.arr (← params.mapM (parameterData trace)))]

/-- The exact explicitly applied arguments of an accepted declaration inside its actual term. -/
partial def declarationData (trace : Trace) (declaration : Name) (actual : Expr) : TermElabM (Array Json) := do
  let actual ← instantiateMVars actual
  let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let some application := actual.find? fun term =>
      term.getAppFn.constName? == some declaration && term.getAppNumArgs == infos.size
    | throwError "the exact registered functor declaration application was lost"
  let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  (← DirectConstruction.dataArguments params).mapM (parameterData trace)

/-- Public edge data from the actual instantiated functor, preserving declaration arguments. -/
partial def edgeDescriptor (trace : Trace) (edge : EdgeRef) (actual : Expr) : TermElabM Json := do
  let state ← registryState
  match edge with
  | .functor id =>
      let some entry := state.functor? id | unreachable!
      return Json.mkObj [("ctor", id.raw), ("args", Json.arr (← declarationData trace entry.declaration actual))]
  | .classifierForget id =>
      let some entry := state.classifiers.find? (·.id == id) | unreachable!
      return Json.mkObj [("ctor", "classifierForget"), ("args", Json.arr #[toJson id.raw,
        Json.arr (← declarationData trace entry.declaration actual)])]
  | .constructMap constructor inner =>
      return Json.mkObj [("ctor", "constructorMap"),
        ("args", Json.arr #[toJson constructor.raw, ← edgeDescriptor trace inner actual])]

end

/-- Complete object action data at the actual typed source, retaining every edge parameter. -/
def actionObjectData (trace : Trace) (input : Wire) (route : Array EdgeRef) : TermElabM Json := do
  let state ← registryState
  let mut object := input.value
  let mut json := input.json
  for edge in route do
    let U ← Semantic.edgeFunctor state edge
    object ← Semantic.objOf U object
    let descriptor ← edgeDescriptor trace edge U
    json := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[descriptor, json])]
  return json

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
partial def subobjectFields? (data : Json) : Option (Array Json) := do
  let tag ← (data.getObjValAs? String "ctor").toOption
  let args ← ((data.getObjVal? "args").bind (·.getArr?)).toOption
  if tag == "arrow" || tag == "subobject" then
    unless args.size == 3 do none
    return args
  if tag == "objectPresentation" then
    let #[_, answer] := args | none
    return ← subobjectFields? answer
  if tag == "liftedSubobject" then
    let #[_, _, _, steps] := args | none
    let steps ← steps.getArr?.toOption
    let first ← steps[0]?
    let fields ← (LiftedSubobjectData.fields "liftStep" 5 first).toOption
    let outputs ← fields[4]!.getArr?.toOption
    let next ← (LiftedSubobjectData.nextBase fields[2]! outputs).toOption
    return ← subobjectFields? next
  none

/-- Compute a structural projection from the complete returned fields. The role of the
registered action is determined on a fresh symbolic receiver, so equal actual objects
cannot make unrelated functors look like projections. Opaque fields and their ownership
remain data. Other accepted actions retain their full functor descriptor. -/
def projectObjectAction (trace : Trace) (_source : CategoryExpr) (edge : EdgeRef)
    (action receiver : Expr) (data : Json) : TermElabM (Option Json) := do
  -- The exact typed record interface owns these fields, including full
  -- subcategories of arrows whose registered category expression is atomic.
  -- A fresh receiver prevents equal actual fields from selecting a false role.
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
  let some (role, subobjects) := role | return none
  let fields := if subobjects then subobjectFields? data else do
    let tag ← (data.getObjValAs? String "ctor").toOption
    unless tag == "arrow" do none
    let args ← ((data.getObjVal? "args").bind (·.getArr?)).toOption
    unless args.size == 3 do none
    pure args
  if let some fields := fields then
    if role == 0 then
      return some (Json.mkObj [("ctor", "arrow"), ("args", Json.arr fields)])
    return fields[role - 1]?
  return some (Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[← edgeDescriptor trace edge action, data])])

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
    liftExecution := snapshot.liftExecution,
    categoryContext := snapshot.categoryContext,
    endpointPresentation := snapshot.endpointPresentation,
    constructionInputs := snapshot.constructionInputs,
    proofSources := remaining }
  checkProofRefinementSource original source
  return original

/-- Retain every residual object action, including its complete instantiated edge data. -/
def transportImage (trace : Trace) (w : Wire) (route : Array EdgeRef)
    (applications : Option (Array Expr) := none) : TermElabM Wire := do
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
    let json ← match ← projectObjectAction trace expression step U result.value result.json with
      | some projected => pure projected
      | none => pure (Json.mkObj [("ctor", "functorAction"),
          ("args", Json.arr #[← edgeDescriptor trace step U, result.json])])
    let objectIso ← mapObjectComparison U result.value result.objectIso
    let endpointPresentation ← mapEndpointPresentation U (← edgeDescriptor trace step U)
      result.endpointPresentation
    result := { result with
      form := match target with
        | some target => imageForm state step target
        | none => .contextual edge.target result.form
      categoryContext := some {
        expression := edge.target, bundle := (← instantiateMVars targetBundle) }
      objectIso := objectIso
      endpointPresentation := endpointPresentation
      proofSources := []
      payload := forwardPayload result value json }
    expression := edge.target
  return result

partial def transport (trace : Trace) (w : Wire) (route : Array EdgeRef) : TermElabM Wire := do
  if w.form.namedCategory?.isNone then return ← transportImage trace w route
  if w.owner?.isSome || (match w.payload with | .computed .. | .construction .. => true | _ => false) then
    return ← transportImage trace w route
  if w.objectIso.isSome then return ← transportImage trace w route
  let state ← registryState
  if let .arrow category := w.form then
    unless route.all (fun step => match step with
      | .constructMap constructor (.functor _) =>
          (state.constructors.find? (·.id == constructor)).any
            (·.semantics == `CasCatalogue.Constructors.arrow)
      | _ => false) do
      return ← transportImage trace w route
    let some (.arrow _ hom source target) ← (trace.node? w.value : IO _)
      | return ← transportImage trace w route
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
  let .object entry := w.form | transportImage trace w route
  let some (.object _ params) ← (trace.node? w.value : IO _)
    | return ← transportImage trace w route
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
  if current.id == entry.id then return ← transportImage trace w remaining
  let args := (w.json.getObjVal? "args").toOption.getD (Json.arr #[])
  let refined := { w with form := .object current, presentationIsos := identifications, payload := .ordinary (value) (Json.mkObj [("ctor", current.id.raw), ("args", args)]) }
  transportImage trace refined remaining

/-- Canonical request input consumes only exact checked proof-refinement and named
refinement prefixes. All residual structural edges remain in the admitted source composite. -/
partial def canonicalOperationReceiver (trace : Trace) (wire : Wire) (route : Array EdgeRef) :
    TermElabM Wire := do
  let state ← registryState
  match wire.form with
  | .contextual .. => transportImage trace wire route
  | .proofRefinement _ classifier _ =>
      if route[0]? == some (.classifierForget classifier) then
        let action ← Semantic.edgeFunctor state (.classifierForget classifier)
        let original ← proofRefinementBase trace wire action
        return ← canonicalOperationReceiver trace original (route.extract 1 route.size)
      return wire
  | .object entry =>
      let (_, remaining) := state.transport entry route
      transport trace wire (route.extract 0 (route.size - remaining.size))
  | _ => return wire

/-- Keep the full mathematical receiver separate from its canonical computational input. -/
def operationReceiver (trace : Trace) (wire : Wire) (route : Array EdgeRef) :
    TermElabM (Wire × Expr) := do
  let state ← registryState
  let image ← if route.isEmpty then pure wire.value else
    Semantic.objOf (← Semantic.routeFunctor state route) wire.value
  return (← canonicalOperationReceiver trace wire route, image)

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
particular, no comparison or monomorphism law is obtained from the packet. -/
partial def decodeLiftedAt (_trace : Trace) (category : NamedCategoryEntry) (expected : Expr)
    (context : LiftReplayContext) (json : Json) :
    TermElabM (Except String (Expr × Option Expr)) := do
  let some checked ← LiftedSubobjectData.decode expected category context.fixedSource
      context.prescribed context.fixedBase json
      (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
      (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
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
    let some (.methodWithLifts id route lifts receiver) ← trace.node? fixed
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

/-- Execute every selected public lift field on preceding actual data, in reverse route order.
The formal plan is fixed before dispatch; no reply supplies a semantic term or lift law. -/
def executePrescribedLift (h : Harness) (trace : Trace) (plan : LiftedSubobjectData.Plan)
    (source base : Wire) (parameters : Array (Array Json × Array Wire)) :
    TermElabM (Json × Option (String × Nat)) := do
  unless parameters.size == plan.components.size do
    throwError "the prescribed lift lost its complete selected evidence parameters"
  let .ok _ := LiftedSubobjectData.subobjectFields base.json
    | throwStratum .malformed "the lift base omitted its complete apex, ambient and inclusion"
  let state ← registryState
  let mut sources : Array Json := #[]
  let mut actions : Array Json := #[]
  let mut currentSource := source.json
  for component in plan.components do
    let some row := state.lifts.find? (·.id == component.lift)
      | throwError "the fixed lift plan lost its registered row"
    let .constructMap _ inner := row.edge
      | throwError "the fixed lift plan lost its selected inner action"
    let action ← edgeDescriptor trace inner component.action
    sources := sources.push currentSource
    actions := actions.push action
    let .ok next := LiftedSubobjectData.mapArrowData action currentSource
      | throwStratum .malformed "the prescribed lift source omitted complete Arrow fields"
    currentSource := next
  let mut currentBase := base.json
  let mut owner ← sharedOwner source base
  let mut steps := Array.replicate plan.components.size Json.null
  for index in (List.range plan.components.size).reverse do
    let some component := plan.components[index]?
      | throwError "the fixed route lost a required computation component"
    let some row := state.lifts.find? (·.id == component.lift)
      | throwError "the fixed lift plan lost its public computation row"
    let some form := state.liftInputForm? row.inputAddress
      | throwError "the public lift request has no unique registered source context"
    for dependency in parameters[index]!.2 do
      owner ← mergeOwners owner dependency.owner?
    let mut outputs : Array Json := #[]
    for field in LiftField.all do
      let request := Json.mkObj [("ctor", "liftInput"),
        ("parameters", Json.arr parameters[index]!.1), ("args", Json.arr #[
        toJson row.id.raw, actions[index]!, sources[index]!, currentBase, Json.arr outputs])]
      let input : Wire := { form, payload := dataPayload component.receiver request owner }
      let operation := row.fieldAddress field
      let (answer, backend) ← send h operation input
      outputs := outputs.push answer
      match ← LiftedSubobjectData.validatePrefix component actions[index]!
          sources[index]! currentBase outputs with
      | .error message => malformed backend operation answer message
      | .ok () => pure ()
      let scope ← computationalScope h backend answer
      let returnedOwner := match scope with
        | .portable => none
        | .owned backend session => some (backend, session)
      owner ← mergeOwners owner returnedOwner
    steps := steps.set! index (Json.mkObj [("ctor", "liftStep"),
      ("parameters", Json.arr parameters[index]!.1), ("args", Json.arr #[
      toJson row.id.raw, actions[index]!, sources[index]!, currentBase, Json.arr outputs])])
    let .ok next := LiftedSubobjectData.nextBase sources[index]! outputs
      | throwError "the completed lift omitted its actual next object or inclusion"
    currentBase := next
  let json := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
    base.json, source.json, toJson (plan.components.map (·.lift.raw)), Json.arr steps])]
  return (json, owner)

/-- Validate computational object fields without proving construction laws. In particular,
subobject data carries its inclusion at the declared endpoints but is not promoted to a Lean
`Mono` instance or identified with the formal construction. -/
partial def validateComputationalObject (_trace : Trace) (_category : NamedCategoryEntry)
    (fixed : Expr) (json : Json) : TermElabM (Except String Unit) := do
  ComputationalData.validatePort fixed (← inferType fixed) json

/-- Dispatch a method on the backend's returned apex representation, without
identifying that representation with the formal universal object. The complete
construction and its independently fixed semantic value remain in `input`. -/
def computationalApexReceiver (_trace : Trace) (input : Wire) : TermElabM Wire := do
  let state ← registryState
  if let some (receiver, _) := input.constructionInputs then
    unless ← withoutModifyingState <| withTransparency .all <|
        isDefEq receiver input.value do return input
  let objects := input.constructionInputs.map Prod.snd |>.getD #[]
  let mut answer := input.json
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
      return input
    else if tag == some "constructionApex" then
      let some identifier := args[0]? | return input
      let .ok name := identifier.getStr? | return input
      let some row := state.limits.find? (·.id.raw == name) | return input
      apexCategory := row.category
      apexShape := some row.shape
      let some child := args[2]? | break
      answer := child
    else if tag == some "createdCone" then
      let some identifier := args[0]? | return input
      let .ok name := identifier.getStr? | return input
      let some lift := state.lifts.find? (·.id.raw == name) | return input
      let some shape := apexShape | return input
      unless lift.kind == .createsLimits shape do return input
      let some edge := state.structuralEdge? lift.edge | return input
      let some category := state.categories.find? (·.id == apexCategory) | return input
      unless edge.target.syntacticEq category.expression do return input
      let action ← Semantic.asFunctor (← Semantic.edgeFunctor state lift.edge)
      let actionType ← whnfR (← inferType action)
      unless actionType.isAppOf ``CategoryTheory.Functor do return input
      unless ← isDefEq (← inferType fixed) actionType.getAppArgs[0]! do return input
      fixed ← Semantic.objOf action fixed
      let some child := args[2]? | break
      answer := child
    else break
  unless ((answer.getObjValAs? String "ctor").toOption == some "cone" ||
      (answer.getObjValAs? String "ctor").toOption == some "cocone") do
    return input
  let .ok args := (answer.getObjVal? "args").bind (·.getArr?) | return input
  let some apexJson := args[0]? | return input
  -- Only the exact inner object descriptor selects a registered form. The
  -- full finiteData envelope remains the computational receiver payload.
  let mut descriptor := apexJson
  if (apexJson.getObjValAs? String "ctor").toOption == some "finiteData" then
    let .ok (_, fields) := ComputationalData.envelope apexJson | return input
    unless fields.size == 2 do return input
    descriptor := fields[0]!
  let some category := state.categories.find? (·.id == apexCategory) | return input
  let carrier ← categoryCarrierInstance category
  -- Preserve any independently fixed category parameters, without identifying
  -- the returned object with the formal universal apex. A created cone can
  -- retain a source-side formal object while its packet is in the base category.
  unless ← withoutModifyingState (isDefEq (← inferType fixed) carrier) do return input
  discard <| isDefEq (← inferType fixed) carrier
  let carrier ← instantiateMVars carrier
  if carrier.hasMVar || carrier.hasLevelMVar then return input
  if let .error _ ← ComputationalData.validatePort fixed carrier apexJson objects then
    return input
  let named := state.objects.find? fun entry =>
    (descriptor.getObjValAs? String "ctor").toOption == some entry.id.raw
  if let some entry := named then
    unless entry.category == apexCategory do return input
  let form := named.map Form.object |>.getD (.diagrams category)
  -- The complete selected descriptor retains every dependency sent by this
  -- request. Only its nested opaque data require the parent's live owner;
  -- unselected owned defining maps remain in the original complete result.
  let payload := if containsOpaqueData apexJson then forwardPayload input input.value apexJson
    else .computed input.value (.inline apexJson)
  return { input with form, payload }

/-- The power object, ambient set and subset of `e` when `e` is the extent of a subset, the
set `po.extent X A` that `Language.asObject` forms. -/
def extentOf? (state : RegistryState) (e : Expr) : Option (PowerObjectEntry × Expr × Expr) := do
  let e := e.consumeMData
  let po ← state.powerObjects.find? (e.isAppOf ·.extent)
  let #[X, A] := e.getAppArgs | none
  return (po, X, A)

mutual

-- Closed element data comes from the formal operation trace, never from carrier matching.
partial def elementExpression (h : Harness) (trace : Trace) (e : Expr) :
    TermElabM (Json × Array Wire) := do
  if let some actual := (← h.results.get)[e]? then
    unless actual.payload matches .ordinary .. do
      return (Json.mkObj [("ctor", "point"), ("args", Json.arr #[actual.json])], #[actual])
  let state ← registryState
  let some node ← trace.node? e
    | throwStratum .noImplementation m!"the closed element has no retained construction"
  match node with
  | .elementNumeral n _ _ =>
      return (Json.mkObj [("ctor", "numeral"), ("args", Json.arr #[toJson n])], #[])
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      unless entry.generator.isSome do throwError "the retained object has no generator"
      let (_, infos, _) ← forallMetaTelescope (← getConstInfo entry.declaration).type
      let objectArity := (infos.filter (·.isExplicit)).size
      let (index, dependencies) ← realizedParameters h trace (params.extract objectArity params.size)
      return (Json.mkObj [("ctor", "generator"), ("args", Json.arr index)], dependencies)
  | .operationApply id params operands _ _ =>
      let some entry := state.operations.find? (·.id == id) | unreachable!
      unless operands.size == entry.arity do
        throwError "the retained operation expression changed its declared arity"
      let (parameters, parameterWires) ← realizedParameters h trace params
      let arguments ← operands.mapM (elementExpression h trace)
      return (Json.mkObj [("ctor", "operationExpression"),
        ("args", Json.arr #[toJson id.raw, Json.arr parameters, Json.arr (arguments.map Prod.fst)])],
        arguments.foldl (fun dependencies argument => dependencies ++ argument.2) parameterWires)
  -- Any other closed point `1 ⟶ X` is sent as the point it is, in its published morphism
  -- encoding (a named morphism, a composite, a mediator, an admitted point).
  | _ =>
      let point ← realize h trace "a point of a closed element" e
      return (Json.mkObj [("ctor", "point"), ("args", Json.arr #[point.json])], #[point])

/-- Retain an exact declared object action even when it occurs only as a parameter
term. Computed source data and action parameters remain dependencies; a syntactic
composite is encoded in its original order rather than selecting an inner edge. -/
partial def realizedObjectParameterAction? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option (Json × Array Wire)) := do
  let mut selected := (← instantiateMVars value).consumeMData
  while selected.isAppOfArity ``id 2 do selected := selected.appArg!.consumeMData
  unless selected.isAppOfArity ``Prefunctor.obj 6 do return none
  let prefunctor := selected.getAppArgs[4]!.consumeMData
  unless prefunctor.isAppOfArity ``CategoryTheory.Functor.toPrefunctor 5 do return none
  let action := prefunctor.appArg!.consumeMData
  let source := selected.appArg!
  if action.isAppOf ``CategoryTheory.Functor.comp then
    let arguments := action.getAppArgs
    let intermediate ← Semantic.objOf arguments[arguments.size - 2]! source
    let nested ← Semantic.objOf arguments.back! intermediate
    unless ← withTransparency .all <| isDefEq nested value do
      throwError "the parameter composition changed its original complete object action"
    let (data, dependencies) ← realizedParameters h trace #[nested]
    let #[data] := data | throwError "the composed object parameter lost its complete data"
    return some (data, dependencies)
  let state ← registryState
  let mut candidates : Array EdgeRef := #[]
  for (edge, declaration) in
      (state.functors.map fun row => (EdgeRef.functor row.id, row.declaration)) ++
      (state.classifiers.map fun row => (EdgeRef.classifierForget row.id, row.declaration)) do
    unless (action.find? (·.isConstOf declaration)).isSome do continue
    let matches ← withoutModifyingState do
      let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state edge)
      withTransparency .all <| isDefEq accepted action
    if matches then candidates := candidates.push edge
  let edge ← match candidates with
    | #[] => return none
    | #[edge] => pure edge
    | _ => throwError "the complete object parameter names several accepted actions"
  let (descriptor, actionDependencies) ← realizedEdgeDescriptor h trace edge action
  let (sources, sourceDependencies) ← realizedParameters h trace #[source]
  let #[sourceData] := sources | throwError "the object parameter lost its original source data"
  unless ← withTransparency .all <| isDefEq (← Semantic.objOf action source) value do
    throwError "the object parameter changed its exact declared action"
  return some (Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[descriptor, sourceData])], actionDependencies ++ sourceDependencies)

partial def realizedParameters (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array Json × Array Wire) := do
  let mut data := #[]
  let mut dependencies := #[]
  for parameter in parameters do
    if ← isProp (← inferType parameter) then continue
    if let some (extent, wires) ← extentData? h trace parameter then
      data := data.push extent
      dependencies := dependencies ++ wires
    else if (← h.results.get)[parameter]?.isSome || (← trace.node? parameter).isSome then
      let wire ← realize h trace "the retained callable parameter" parameter
      data := data.push wire.json
      dependencies := dependencies.push wire
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
        let (arguments, wires) ← realizedParameters h trace arguments
        if tag == "constructedCategory" then
          let some constructor := state.constructor? ⟨id⟩ | unreachable!
          unless arguments.size == constructor.signature.size do
            throwError "the constructed category lost a declared ordered argument"
        data := data.push (Json.mkObj [("ctor", toJson tag),
          ("args", Json.arr #[toJson id, Json.arr arguments])])
        dependencies := dependencies ++ wires
      else if let some (image, wires) ← realizedObjectParameterAction? h trace parameter then
        data := data.push image
        dependencies := dependencies ++ wires
      else data := data.push (← parameterData trace parameter)
  return (data, dependencies)

/-- Encode each actual action parameter through the same dependency-preserving
path used by ordinary registered callables. -/
partial def realizedEdgeDescriptor (h : Harness) (trace : Trace) (edge : EdgeRef)
    (actual : Expr) : TermElabM (Json × Array Wire) := do
  let state ← registryState
  if let .constructMap constructor inner := edge then
    let (descriptor, dependencies) ← realizedEdgeDescriptor h trace inner actual
    return (Json.mkObj [("ctor", "constructorMap"),
      ("args", Json.arr #[toJson constructor.raw, descriptor])], dependencies)
  let declaration ← match edge with
    | .functor id =>
        let some entry := state.functor? id | throwError "the selected action is not registered"
        pure entry.declaration
    | .classifierForget id =>
        let some entry := state.classifiers.find? (·.id == id)
          | throwError "the selected classifier is not registered"
        pure entry.declaration
    | _ => unreachable!
  let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields =>
    fun _ => fields.mapM (·.fvarId!.getBinderInfo)
  let actual ← instantiateMVars actual
  let some application := actual.find? fun term =>
      term.getAppFn.constName? == some declaration && term.getAppNumArgs == infos.size
    | throwError "the complete selected action application was lost"
  let parameters := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none
  let (data, dependencies) ← realizedParameters h trace parameters
  let descriptor := match edge with
    | .functor id => Json.mkObj [("ctor", id.raw), ("args", Json.arr data)]
    | .classifierForget id => Json.mkObj [("ctor", "classifierForget"),
        ("args", Json.arr #[toJson id.raw, Json.arr data])]
    | _ => unreachable!
  return (descriptor, dependencies)

/-- A set formed as the extent of a subset literal (`Language.asObject`), where a set is
expected, is sent as that extent: the power object, its ambient set and the literal. -/
partial def extentData? (h : Harness) (trace : Trace) (p : Expr) :
    TermElabM (Option (Json × Array Wire)) := do
  let some (.literal _ _) ← (trace.node? p : IO _) | return none
  let some (po, X, element) := extentOf? (← registryState) p | return none
  let ambient ← realize h trace "the ambient set of an extent" X
  let literal ← realize h trace "the literal of an extent" element
  return some (Json.mkObj [("ctor", "extent"),
    ("args", Json.arr #[toJson po.id.raw, ambient.json, literal.json])], #[ambient, literal])

/-- A declared callable endpoint is a data descriptor, not an observation of a
universal construction. The public structural product frame describes an actual
product type without demanding a cone computation. Named selected objects and
previously computed objects keep their exact presentations and live dependencies.
Only the formal type supplies this structural frame; no backend determines it. -/
partial def realizeEndpoint (h : Harness) (trace : Trace) (what : String)
    (value : Expr) : TermElabM Wire := do
  let value ← instantiateMVars value
  if let some computed := (← h.results.get)[value]? then return computed
  let node ← trace.node? value
  let structural := match node with
    | some (.object ..) | some (.parameterTransport ..) | some (.retainedRoute ..) |
        some (.parameterEquivalence ..) | some (.functor ..) | some (.proofRefinement ..) |
        some (.construction ..) | some (.selectedLift ..) | some (.liftProjection ..) => false
    | _ => true
  if structural && (← whnfR (← inferType value)).isSort then
    let reduced ← withTransparency .all <| whnf value
    if reduced.isAppOfArity ``Prod 2 then
      let fields := reduced.getAppArgs
      let first ← realizeEndpoint h trace "the first declared endpoint component" fields[0]!
      let second ← realizeEndpoint h trace "the second declared endpoint component" fields[1]!
      let some category := (← registryState).categories.find? (·.id == CategoryId.sets)
        | throwError "the declared product endpoint has no set category"
      let json := Json.mkObj [("ctor", "objectProduct"),
        ("args", Json.arr #[first.json, second.json])]
      return {
        form := .diagrams category
        payload := (← combinedPayload value json #[first, second]) }
  if node.isNone then discard <| Semantic.recordNamedObject value (some trace)
  realize h trace what value

/-- A complete callable supplies an endpoint descriptor even when that exact
object has no separately registered presentation. Only missing computation takes
this path; malformed values, unavailable owners and internal failures propagate. -/
partial def realizeCallableEndpoint (h : Harness) (trace : Trace) (wire : Wire)
    (value : Expr) (source : Bool) (context : Option CategoryContext := none) :
    TermElabM Wire := do
  let context := context.orElse fun _ => wire.categoryContext
  if let some context := context then CategoryContext.checkObject context value
  try realizeEndpoint h trace "the callable's complete selected endpoint" value
  catch error =>
    unless !Exception.hasConflictingStrata error &&
        CasCatalogue.Exception.stratum? error == some .noImplementation do throw error
    let state ← registryState
    let form ← match context with
      | some context => pure (contextualForm state context wire.form)
      | none =>
        let some category := state.categories.find? (·.id == wire.form.category)
          | throwError "the callable endpoint lost its complete registered category"
        pure (.diagrams category)
    let data := Backend.MorphismEndpoint.encode { callable := wire.json, source }
    return { form, payload := forwardPayload wire value data, categoryContext := context }

/-- A bare graph has no chosen structured endpoints of its own. Retain those exact
objects in the public typed-map frame before placing it in another map expression.
Named descriptors and already framed or opaque callables keep their existing data. -/
partial def frameMorphismData (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) : TermElabM (Json × Array Wire) := do
  if wire.morphismFramed then return (wire.json, #[])
  let graph := wire.json.getArr?.isOk ||
    (wire.json.getObjValAs? String "ctor").toOption == some "finiteGraph"
  let state ← registryState
  let needsPresentation := fun endpoint => do
    if let some actual := (← h.results.get)[endpoint]? then
      if actual.endpointPresentation.isSome then return true
    if let some (.object id _) ← trace.node? endpoint then
      return (state.objects.find? (·.id == id)).any (·.functorPresentation.isSome)
    return false
  unless graph || (← needsPresentation source) || (← needsPresentation target) do
    return (wire.json, #[])
  let type ← whnfR (← inferType wire.value)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the graph lost its independently selected complete hom signature"
  let arguments := type.getAppArgs
  unless ← withTransparency .all <|
      isDefEq arguments[2]! source <&&> isDefEq arguments[3]! target do
    throwError "the graph changed its independently selected complete endpoints"
  for object in #[source, target] do
    if (← trace.node? object).isNone then
      discard <| Semantic.recordNamedObject object (some trace)
  let sourceWire ← realizeCallableEndpoint h trace wire source true
  let targetWire ← realizeCallableEndpoint h trace wire target false
  let presented ← presentMorphism wire sourceWire targetWire
  if !graph then return (presented.json, #[sourceWire, targetWire])
  return (Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[sourceWire.json, targetWire.json, presented.json])], #[sourceWire, targetWire])

/-- Execute a named object's published presentation only when its input parameters
already depend on actual computations. Ordinary named descriptors keep their
existing dispatch. The accepted comparison remains explicit on every later map. -/
partial def realizeObjectPresentation (h : Harness) (trace : Trace) (entry : ObjectEntry)
    (parameters : Array Expr) (data : Array Json) (dependencies : Array Wire) :
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
            other.owner? == dependency.owner?) then
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
  unless ← withTransparency .all <| isDefEq actual.value presentation.image do
    throwError "the computed object presentation changed its complete formal image"
  let fieldData := fun (selector : String) => Json.mkObj [("ctor", "objectField"),
    ("args", Json.arr #[toJson entry.id.raw, toJson selector, Json.arr data])]
  let mut comparison ← mkAppM ``CategoryTheory.Iso.symm #[presentation.identification]
  let mut forward := fieldData "inversePresentation"
  let mut backward := fieldData "presentation"
  if let some retained := actual.endpointPresentation then
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[comparison, retained.comparison]
    forward := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[forward, retained.forward])]
    backward := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[retained.backward, backward])]
  return some {
    form := .object entry
    payload := (← combinedPayload presentation.object actual.json (dependencies.push actual))
    endpointPresentation := some { comparison, forward, backward } }

/-- Execute exact accepted applications while retaining unnamed category contexts and
the original data owner. Both object and map actions use the same declared descriptors. -/
partial def contextualAction (h : Harness) (trace : Trace) (formal receiver : Expr)
    (source target : CategoryContext) (route : Array EdgeRef) (applications : Array Expr)
    (morphism : Bool) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the contextual route omitted a complete selected application"
  let state ← registryState
  let original ← realize h trace "the contextual action's complete original value" receiver
  let mut value := receiver
  let mut data := original.json
  let mut dependencies := #[original]
  if morphism then
    let some (first, second) := Language.homEnds? (← inferType receiver)
      | throwError "the retained map action lost its original complete endpoints"
    CategoryContext.checkMorphism source receiver first second
    let (framed, endpoints) ← frameMorphismData h trace first second original
    data := framed
    dependencies := dependencies ++ endpoints
  else CategoryContext.checkObject source receiver
  let mut currentContext := source
  let mut objectIso := original.objectIso
  let mut endpointPresentation := original.endpointPresentation
  for (step, application) in route.zip applications do
    let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state step)
    unless ← withTransparency .all <| isDefEq accepted application do
      throwError "the contextual action differs from its exact accepted declaration"
    let (sourceBundle, targetBundle) ← functorCategoryBundles application
    unless ← withTransparency .all <| isDefEq sourceBundle currentContext.bundle do
      throwError "a contextual action changed its complete source bundle"
    let some targetExpression := state.selectedEdgeTarget? step
      | throwError "a contextual action has no accepted target expression"
    let (descriptor, parameterWires) ← realizedEdgeDescriptor h trace step application
    dependencies := dependencies ++ parameterWires
    if morphism then
      data := Json.mkObj [("ctor", "map"), ("args", Json.arr #[descriptor, data])]
      value ← Semantic.mapOf application value
    else
      let projected ← projectObjectAction trace currentContext.expression step application value data
      data := projected.getD
        (Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[descriptor, data])])
      objectIso ← mapObjectComparison application value objectIso
      endpointPresentation ← mapEndpointPresentation application descriptor endpointPresentation
      value ← Semantic.objOf application value
    currentContext := { expression := targetExpression, bundle := (← instantiateMVars targetBundle) }
  unless ← withTransparency .all <| isDefEq value formal <&&>
      isDefEq currentContext.bundle target.bundle do
    throwError "the contextual route changed its fixed result or full target bundle"
  unless currentContext.expression.syntacticEq target.expression do
    throwError "the contextual route changed its accepted target category expression"
  return {
    form := contextualForm state target original.form morphism
    payload := (← combinedPayload formal data dependencies)
    categoryContext := some target
    objectIso := if morphism then none else objectIso
    endpointPresentation := if morphism then none else endpointPresentation }

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
  let (firstData, firstDependencies) ← frameMorphismData h trace source middle a
  let (secondData, secondDependencies) ← frameMorphismData h trace middle target b
  let selected ← match ← trace.node? second with
    | some (.cellComponent id params constructors inverse receiver) => do
      let some entry := state.cells.find? (·.id == id)
        | throwError "the selected component is no longer registered"
      let (parameters, dependencies) ← realizedParameters h trace params
      let original ← realize h trace "the selected component's complete receiver" receiver
      let some inputForm := state.componentForm? (entry.componentAddress constructors)
        | throwError "the selected component has no admitted full input address"
      pure (some (entry.componentAddress constructors,
        #[Json.arr parameters, original.json, toJson inverse], dependencies.push original, inputForm))
    | some (.constructionMap id params _ _ _) => do
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the selected construction is no longer registered"
      let (parameters, dependencies) ← realizedParameters h trace params
      let some inputForm := state.constructionForm? entry.inputAddress
        | throwError "the selected construction has no complete input address"
      pure (some (entry.mapAddress, parameters, dependencies, inputForm))
    | some (.cartesian id params _ receiver "hom") => do
      let some entry := state.functor? id
        | throwError "the selected family reindexing is no longer registered"
      let (parameters, dependencies) ← realizedParameters h trace params
      let original ← realize h trace "the cartesian map's original receiver" receiver
      let some inputForm := state.cartesianForm? entry.cartesianAddress
        | throwError "the cartesian map has no accepted complete input address"
      pure (some (entry.cartesianAddress, #[Json.arr parameters, original.json],
        dependencies.push original, inputForm))
    | _ => pure none
  let dependencies := #[a, b] ++ firstDependencies ++ secondDependencies
  if let some (operation, parameters, parameterWires, inputForm) := selected then
    let domainWire ← realizeEndpoint h trace "the contextual map's original domain" source
    let middleWire ← realizeEndpoint h trace "the contextual map's complete argument target" middle
    let targetWire ← realizeEndpoint h trace "the contextual map's complete result target" target
    let invocation : Backend.PointInvocation := {
      operation, parameters
      arrow := secondData
      domain := domainWire.json
      source := middleWire.json
      target := targetWire.json
      argument := firstData }
    let input : Wire := {
      form := inputForm
      payload := (← combinedPayload formal invocation.encode
        (dependencies ++ parameterWires ++ #[domainWire, middleWire, targetWire])) }
    let (answer, backend) ← send h operation input (completeRequest := true)
    let validation ← if ← withTransparency .all <| isDefEq source (← closedElementDomain state) then
      ComputationalData.validateElementAt target targetWire.json (← pointResultValue state formal) answer
    else ComputationalData.validateEndpointPort formal domainWire.json targetWire.json answer
    if let .error message := validation then malformed backend operation answer message
    let data ← receiveComputationalData h backend operation answer true
    let returned : Wire := {
      form := contextualForm state context b.form true
      payload := .computed formal data
      morphismFramed := true
      categoryContext := some context }
    let owner ← mergeOwners input.owner? returned.owner?
    return { returned with payload := computedPayload formal returned.json owner }
  let data := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[firstData, secondData])]
  return {
    form := contextualForm state context b.form true
    payload := (← combinedPayload formal data dependencies)
    morphismFramed := true
    categoryContext := some context }

/-- Complete ordinary result fields are projections of their retained formal schema
and actual returned packet. A computational field supplies neither a formal object
identification nor any law about the construction. -/
partial def structuredProjection (h : Harness) (trace : Trace) (formal receiver : Expr)
    (field : String) (index : Option Nat) : TermElabM Wire := do
  let state ← registryState
  let original ← realize h trace "the complete structured result" receiver
  let context ← match original.categoryContext with
    | some context => pure context
    | none => do
      let some category := state.categories.find? (·.id == original.form.category)
        | throwError "the structured result lost its complete category context"
      CategoryContext.ofNamed category receiver
  if let some index := index then
    let some plan ← StructuredProjection.construction? receiver context (some trace)
      | throwError "the selected data port has no independently retained construction"
    let port ← plan.selectPort (some index)
    unless ← withTransparency .all <| isDefEq port.formalField formal do
      throwError "the selected data port changed its complete formal field"
    let .construction result _ := original.payload
      | throwStratum .noImplementation "the structured data port has no complete returned packet"
    let data := Json.mkObj [("ctor", "constructionField"), ("args", Json.arr #[
      toJson plan.row.id.raw, result.diagramJson, result.json, toJson index])]
    return {
      form := contextualForm state context original.form (Language.homEnds? port.expectedType).isSome
      payload := forwardPayload original formal data
      categoryContext := some context }
  let some plan ← StructuredProjection.arrow? receiver context
    | throwError "the selected result has no accepted Arrow or subobject projection"
  let (expected, targetContext, morphism) ← plan.field field
  unless ← withTransparency .all <| isDefEq expected formal do
    throwError "the structured projection changed its complete formal field"
  let some actual ← StructuredProjection.arrow? original.value context
    | throwError "the retained complete result lost its actual structured type"
  let arrowComparison ← original.objectIso.mapM plan.arrowComparison
  let envelope := fun tag args => Json.mkObj [("ctor", toJson (tag : String)), ("args", Json.arr args)]
  let callable := envelope (if plan.subobject then "subobjectInclusion" else "arrowHom") #[original.json]
  let sourceData := if plan.subobject then envelope "subobjectApex" #[original.json]
    else Backend.MorphismEndpoint.encode { callable, source := true }
  let targetData := Backend.MorphismEndpoint.encode { callable, source := false }
  let data := match field with
    | "obj" | "source" => sourceData
    | "target" => targetData
    | "hom" => callable
    | "inclusion" => envelope "arrow" #[sourceData, targetData, callable]
    | _ => unreachable!
  if morphism then
    let aligned ← alignedArrowHom actual.arrow arrowComparison
    unless ← withTransparency .all <| isDefEq (← inferType aligned) (← inferType formal) do
      throwError "the structured map projection changed its original complete endpoints"
    let unframed : Wire := {
      form := contextualForm state targetContext original.form true
      payload := forwardPayload original formal data
      categoryContext := some targetContext }
    let (data, endpoints) ← frameMorphismData h trace plan.source plan.target unframed
    return { unframed with
      payload := (← combinedPayload formal data (endpoints.push original))
      morphismFramed := true }
  let action ← plan.projectionFunctor field
  let some (.construct constructor _) := some context.expression | unreachable!
  let (parameters, dependencies) ← realizedParameters h trace #[plan.base.bundle]
  let categoryData := envelope "constructedCategory" #[toJson constructor.raw, Json.arr parameters]
  let selector := if field == "obj" then "source" else field
  let descriptor := envelope "structuredProjectionAction" #[categoryData, toJson selector]
  let (value, _, _) ← actual.field field
  let objectIso ← mapObjectComparison action original.value original.objectIso
  let endpointPresentation ← mapEndpointPresentation action descriptor original.endpointPresentation
  return {
    form := contextualForm state targetContext original.form
    payload := (← combinedPayload value data (dependencies.push original))
    objectIso, endpointPresentation, categoryContext := some targetContext }

/-- Read the preserved actual fields of a completed lift without rerunning its ports. -/
partial def retainedLiftExecution (h : Harness) (trace : Trace) (receiver : Expr) :
    TermElabM (Wire × LiftExecution) := do
  let wire ← realize h trace "the complete selected lift" receiver
  let some execution := wire.liftExecution
    | throwError "the completed lift lost its selected computation and actual four-field outputs"
  unless !execution.selections.isEmpty &&
      execution.actions.size == execution.selections.size &&
      execution.parameters.size == execution.selections.size &&
      execution.sources.size == execution.selections.size &&
      execution.bases.size == execution.selections.size &&
      execution.outputs.size == execution.selections.size &&
      execution.outputs.all (·.size == 4) do
    throwError "the selected lift cache omits a required component output"
  return (wire, execution)

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

partial def liftProjectionData (execution : LiftExecution) (index : Nat) : TermElabM Json := do
  let some first := execution.outputs[0]?
    | throwError "the complete lift cache has no output fields"
  let some initial := first[index]? | throwError "the lift projection is not a public field"
  if index < 2 then return initial
  let mut result := initial
  for step in List.range (execution.outputs.size - 1) do
    let next := step + 1
    let mapped := Json.mkObj [("ctor", "map"),
      ("args", Json.arr #[execution.actions[next]!, result])]
    result := Json.mkObj [("ctor", "compose"), ("args", Json.arr
      (if index == 2 then #[mapped, (execution.outputs[next]!)[2]!]
        else #[(execution.outputs[next]!)[3]!, mapped]))]
  let .ok base := LiftedSubobjectData.subobjectFields execution.bases.back!
    | throwError "the retained lift lost its original complete base"
  let mut image := first[0]!
  for action in execution.actions do
    image := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[action, image])]
  return Json.mkObj [("ctor", "typedMap"), ("args", Json.arr
    (if index == 2 then #[image, base[0]!, result] else #[base[0]!, image, result]))]

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
      outputs := execution.outputs ++ retained.outputs }
    dependencies := dependencies.push wire
  let some first := execution.selections[0]?
    | throwError "the composed lift has no complete retained stage"
  let some original := dependencies[0]? | unreachable!
  unless ← withTransparency .all <| isDefEq (← SelectedLift.port execution.selections 0) formal do
    throwError "the composed lift changed its original formal object"
  let context ← SelectedLift.context first
  return {
    form := contextualForm (← registryState) context original.form
    payload := (← combinedPayload formal (← liftProjectionData execution 0) dependencies)
    liftExecution := some execution
    categoryContext := some context }

/-- Cache the entire output interface at exact formal expressions. In particular the
object field retains the complete selected suffix, so taking it does not discard lifts. -/
partial def cacheLiftFields (h : Harness) (execution : LiftExecution)
    (owner : Option (String × Nat)) : TermElabM Unit := do
  let state ← registryState
  for start in [:execution.selections.size] do
    let suffix : LiftExecution := {
      selections := execution.selections.extract start execution.selections.size,
      actions := execution.actions.extract start execution.actions.size,
      parameters := execution.parameters.extract start execution.parameters.size,
      sources := execution.sources.extract start execution.sources.size,
      bases := execution.bases.extract start execution.bases.size,
      outputs := execution.outputs.extract start execution.outputs.size }
    for index in [:4] do
      let formal ← SelectedLift.port suffix.selections index
      let some selection := if index < 2 then suffix.selections[0]?
          else suffix.selections.back?
        | throwError "the complete selected suffix is empty"
      let context ← SelectedLift.context selection (index >= 2)
      let some origin := state.liftInputForm? selection.entry.inputAddress
        | throwError "the cached lift field lost its complete input address"
      let data ← liftProjectionData suffix index
      let wire : Wire := {
        form := contextualForm state context origin (index != 0),
        payload := computedPayload formal data owner,
        liftExecution := if index == 0 then some suffix else none
        categoryContext := some context }
      h.results.modify (·.insert formal wire)

partial def selectedLiftExecution (h : Harness) (trace : Trace) (plan : SelectedLift.Plan)
    (formal : Expr) : TermElabM Wire := do
  let state ← registryState
  let inner ← SelectedLift.innerEdge state plan.entry
  let (action, actionWires) ← realizedEdgeDescriptor h trace inner plan.action
  let source ← realizeEndpoint h trace "the selected lift's original source object" plan.source
  let inclusion ← realize h trace "the selected lift's complete base inclusion" plan.inclusion
  let some (baseSource, baseTarget) := Language.homEnds? (← inferType plan.inclusion)
    | throwError "the selected lift lost its original base inclusion endpoints"
  let baseSource ← realizeEndpoint h trace "the selected lift's base apex" baseSource
  let baseTarget ← if (← trace.node? baseTarget).isSome || (← h.results.get).contains baseTarget then
    realizeEndpoint h trace "the selected lift's exact image ambient" baseTarget
  else do
    let context ← SelectedLift.context plan true
    let data := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[action, source.json])]
    pure {
      form := contextualForm state context source.form
      payload := (← combinedPayload baseTarget data (#[source] ++ actionWires))
      categoryContext := some context }
  let base := Json.mkObj [("ctor", "subobject"),
    ("args", Json.arr #[baseSource.json, baseTarget.json, inclusion.json])]
  let (parameters, parameterWires) ← realizedParameters h trace plan.parameters
  let some form := state.liftInputForm? plan.entry.inputAddress
    | throwError "the selected lift has no published complete input form"
  let initial ← combinedPayload formal base
    (#[source, inclusion, baseSource, baseTarget] ++ parameterWires ++ actionWires)
  let initial : Wire := { form, payload := initial }
  let mut owner := initial.owner?
  let mut outputs := #[]
  for field in LiftField.all do
    let invocation : Backend.LiftInput := {
      originalArrow := false
      lift := plan.entry.id.raw
      action
      source := source.json
      base, outputs, parameters }
    let input : Wire := { form, payload := dataPayload formal invocation.encode owner }
    let operation := plan.entry.fieldAddress field
    let (answer, backend) ← send h operation input
    outputs := outputs.push answer
    match ← LiftedSubobjectData.validateSelectionPrefix plan action source.json base outputs with
    | .error message => malformed backend operation answer message
    | .ok () => pure ()
    let returned ← computationalScope h backend answer
    owner ← mergeOwners owner (match returned with
      | .portable => none | .owned backend session => some (backend, session))
  let context ← SelectedLift.context plan
  let execution : LiftExecution := {
    selections := #[plan], actions := #[action], parameters := #[parameters],
    sources := #[source.json], bases := #[base], outputs := #[outputs] }
  cacheLiftFields h execution owner
  return {
    form := contextualForm state context source.form
    payload := computedPayload formal outputs[0]! owner
    liftExecution := some execution
    categoryContext := some context }

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
  let .ok originalBase := LiftedSubobjectData.subobjectFields execution.bases.back!
    | throwError "the factor lost the selected original complete base"
  let mut domains := #[]
  let mut cones := #[]
  let mut currentDomain := domainWire.json
  let mut currentCone := Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[currentDomain, execution.sources[0]!, coneWire.json])]
  for index in [:execution.selections.size] do
    domains := domains.push currentDomain
    cones := cones.push currentCone
    let action := execution.actions[index]!
    currentDomain := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[action, currentDomain])]
    let target := Json.mkObj [("ctor", "functorAction"),
      ("args", Json.arr #[action, execution.sources[index]!])]
    currentCone := Json.mkObj [("ctor", "typedMap"), ("args", Json.arr #[currentDomain, target,
      Json.mkObj [("ctor", "map"), ("args", Json.arr #[action, currentCone])]])]
  let mut currentBase := Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[currentDomain, originalBase[0]!, baseWire.json])]
  let payload ← combinedPayload formal currentBase #[liftWire, baseWire, coneWire, domainWire]
  let combined : Wire := { form := liftWire.form, payload }
  let mut owner := combined.owner?
  for (index, step) in (List.range execution.selections.size).reverse.toArray.zip steps do
    let some selection := execution.selections[index]? | unreachable!
    let .ok baseMap := Backend.TypedMap.decode currentBase
      | throwError "the factor's preceding actual output lost its complete typed map"
    let .ok cone := Backend.TypedMap.decode cones[index]!
      | throwError "the factor's actual cone lost its complete original endpoints"
    let invocation : Backend.LiftFactorInput := {
      lift := selection.entry.id.raw, action := execution.actions[index]!,
      source := execution.sources[index]!, base := execution.bases[index]!,
      outputs := execution.outputs[index]!, parameters := execution.parameters[index]!, baseMap, cone }
    let some form := state.liftInputForm? selection.entry.inputAddress
      | throwError "the selected factor has no published complete input form"
    let input : Wire := { form, payload := dataPayload formal invocation.encode owner }
    let operation := selection.entry.factorAddress
    let (answer, backend) ← send h operation input
    match ← LiftedSubobjectData.validateMap step.factor domains[index]!
        (execution.outputs[index]!)[0]! answer with
    | .error message => malformed backend operation answer message
    | .ok () => pure ()
    let returned ← computationalScope h backend answer
    owner ← mergeOwners owner (match returned with
      | .portable => none | .owned backend session => some (backend, session))
    currentBase := answer
  let some last := steps.back? | throwError "the universal factor has no selected final stage"
  unless ← withTransparency .all <| isDefEq last.factor formal do
    throwError "the staged universal factor changed its independently fixed formal value"
  let some selection := execution.selections[0]? | unreachable!
  let context ← SelectedLift.context selection
  return {
    form := contextualForm state context coneWire.form true
    payload := computedPayload formal currentBase owner
    categoryContext := some context }

/-- Evaluate the recorded term `e`, the value of `what`, to a value of a form, through the
admitted registrations. -/
partial def realize (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let e ← instantiateMVars e
  let closed := !e.hasMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars
  if closed then
    if let some wire := (← h.results.get)[e]? then return wire
  let wire ← realizeFresh h trace what e
  if closed then
    if wire.liftExecution.isSome then
      h.results.modify (·.insert e wire)
    else
      match wire.payload with
      | .ordinary .. => pure ()
      | .computed .. | .construction .. => h.results.modify (·.insert e wire)
  return wire

partial def realizeFresh (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let state ← registryState
  let e ← instantiateMVars e
  let some node ← (trace.node? e : IO _)
    | throwStratum .noImplementation m!"nothing computes {what}: it is not formed by a \
        catalogue operation the realized reading evaluates (a named object at its parameters, \
        a method of one); the term is {e}"
  match node with
  | .categoryParameter id params =>
      let some entry := state.categories.find? (·.id == id)
        | throwError "the selected category parameter is no longer registered"
      let application ← DirectConstruction.close
        (← DirectConstruction.instantiate entry.declaration (← params.mapM exprToSyntax))
      unless ← withTransparency .all <| isDefEq application.value e do
        throwError "the selected category parameter changed its complete dictionary"
      let (parameters, dependencies) ← realizedParameters h trace params
      let data : Backend.CategoryParameter := { category := id.raw, parameters }
      return { form := .diagrams entry, payload := (← combinedPayload e data.encode dependencies) }
  | .functorParameter id params =>
      let some entry := state.functor? id
        | throwError "the selected functor parameter is no longer registered"
      let application ← DirectConstruction.close
        (← DirectConstruction.instantiate entry.declaration (← params.mapM exprToSyntax))
      unless ← withTransparency .all <| isDefEq (← Semantic.asFunctor application.value) e do
        throwError "the selected functor parameter changed its complete action"
      let (parameters, dependencies) ← realizedParameters h trace params
      let data : Backend.FunctorParameter := { functor := id.raw, parameters }
      let category ← Semantic.namedCategoryFor state entry.target
      return { form := .diagrams category, payload := (← combinedPayload e data.encode dependencies) }
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
      let data : Backend.CoreObject := { receiver := original.json }
      return {
        form := contextualForm state coreContext original.form
        payload := forwardPayload original e data.encode
        categoryContext := some coreContext }
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
      let data : Backend.CoreIso := {
        source := sourceWire.json
        target := targetWire.json
        forward := forwardWire.json
        backward := backwardWire.json }
      return {
        form := contextualForm state coreContext sourceWire.form true
        payload := (← combinedPayload e data.encode #[sourceWire, targetWire, forwardWire, backwardWire])
        categoryContext := some coreContext }
  | .contextualRoute source target route applications receiver morphism =>
      contextualAction h trace e receiver source target route applications morphism
  | .contextualComposition context first second source middle target =>
      contextualComposition h trace e context first second source middle target
  | .contextualIdentity context object =>
      CategoryContext.checkMorphism context e object object
      let expected ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
      unless ← withTransparency .all <| isDefEq e expected do
        throwError "the contextual identity changed its independently fixed formal map"
      let original ← realizeEndpoint h trace "the contextual identity's complete object" object
      return {
        form := contextualForm state context original.form true
        payload := forwardPayload original e (Json.mkObj [("ctor", "identity"),
          ("args", Json.arr #[original.json, original.json])])
        categoryContext := some context }
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
      let sourceWire ← realizeCallableEndpoint h trace homWire source true (some context)
      let targetWire ← realizeCallableEndpoint h trace homWire target false (some context)
      let homWire ← presentMorphism homWire sourceWire targetWire
      let data := Json.mkObj [("ctor", "arrow"),
        ("args", Json.arr #[sourceWire.json, targetWire.json, homWire.json])]
      return {
        form := contextualForm state arrowContext sourceWire.form
        payload := (← combinedPayload e data #[sourceWire, targetWire, homWire])
        categoryContext := some arrowContext }
  | .construction id params receiver =>
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the selected construction is no longer registered"
      let selected ← DirectConstruction.select entry (← params.mapM exprToSyntax) receiver
      let expected ← DirectConstruction.obj selected receiver
      unless ← withTransparency .all <| isDefEq expected e do
        throwError "the direct construction changed its complete selected formal result"
      let original ← realize h trace "the construction's complete selected source" receiver
      let (parameters, parameterWires) ← realizedParameters h trace params
      let request : Backend.ConstructionInvocation := {
        construction := id.raw
        parameters
        receiver := original.json }
      let some inputForm := state.constructionForm? entry.inputAddress
        | throwError "the construction lost its registered complete input form"
      let some resultForm := state.constructionForm? entry.id.raw
        | throwError "the construction lost its registered complete result form"
      let input : Wire := {
        form := inputForm
        payload := (← combinedPayload receiver request.encode (#[original] ++ parameterWires)) }
      let (answer, backend) ← send h id.raw input
      let checked ← match CategoryContext.named? state selected.target.expression with
        | some target => validateComputationalObject trace target expected answer
        | none => ComputationalData.validatePort expected (← inferType expected) answer
      match checked with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw answer true
      let result : Wire := {
        form := resultForm
        payload := .computed e data
        categoryContext := some selected.target }
      let owner ← mergeOwners input.owner? result.owner?
      return { result with payload := computedPayload e result.json owner }
  | .constructionMap id params source target morphism =>
      let some entry := state.constructions.find? (·.id == id)
        | throwError "the selected construction map is no longer registered"
      let selected ← DirectConstruction.select entry (← params.mapM exprToSyntax) source
      let expected ← DirectConstruction.map selected source target morphism
      unless ← withTransparency .all <| isDefEq expected e do
        throwError "the construction map changed its exact selected action or endpoints"
      let original ← realize h trace "the complete selected construction source map" morphism
      let (parameters, parameterWires) ← realizedParameters h trace params
      let descriptor := Json.mkObj [("ctor", toJson id.raw), ("args", Json.arr parameters)]
      let data := Json.mkObj [("ctor", "map"), ("args", Json.arr #[descriptor, original.json])]
      let some resultForm := state.constructionForm? entry.id.raw
        | throwError "the construction map lost its registered complete result form"
      return {
        form := contextualForm state selected.target resultForm true
        payload := (← combinedPayload e data (#[original] ++ parameterWires))
        categoryContext := some selected.target }
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
      let data ← liftProjectionData execution index
      let some selection := if index < 2 then execution.selections[0]?
          else execution.selections.back?
        | throwError "the retained selected lift is empty"
      let context ← SelectedLift.context selection (index >= 2)
      return {
        form := contextualForm state context original.form (index != 0)
        payload := forwardPayload original e data
        liftExecution := if index == 0 then original.liftExecution else none
        categoryContext := some context }
  | .structuredProjection receiver field index =>
      structuredProjection h trace e receiver field index
  | .cartesian id params baseMorphism receiver field =>
      let some entry := state.functor? id
        | throwError "the selected family reindexing is no longer registered"
      let original ← realize h trace "the cartesian map's complete original receiver" receiver
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
      let (parameters, dependencies) ← realizedParameters h trace params
      let base ← realize h trace "the cartesian map's original complete base map" baseMorphism
      let callable := Json.mkObj [("ctor", "cartesianMap"), ("args", Json.arr #[
        toJson id.raw, Json.arr parameters, original.json])]
      let data := if field == "hom" then callable else
        Backend.MorphismEndpoint.encode { callable, source := field == "source" }
      let some inputForm := state.cartesianForm? entry.cartesianAddress
        | throwError "the cartesian map has no accepted complete invocation address"
      return {
        form := if field == "hom" then inputForm else contextualForm state plan.total inputForm
        payload := (← combinedPayload e data (dependencies ++ #[original, base]))
        categoryContext := some plan.total }
  | .liftFactor receiver baseMap cone proof =>
      executeLiftFactor h trace e receiver baseMap cone proof
  | .cellComponent id params constructors inverse receiver =>
      let some entry := state.cells.find? (·.id == id)
        | throwError "the selected cell is no longer registered"
      let action ← CellAction.select entry (← params.mapM exprToSyntax) constructors inverse receiver
      unless ← withTransparency .all <| isDefEq (← CellAction.component action receiver) e do
        throwError "the selected cell changed its actual full component"
      let original ← realize h trace "the natural component's complete selected receiver" receiver
      let (parameters, dependencies) ← realizedParameters h trace params
      let base : Backend.CellComponent := {
        cell := id.raw
        parameters
        receiver := original.json
        inverse }
      let data := if constructors.isEmpty then base.encode else
        Json.mkObj [("ctor", "constructedCellComponent"), ("args", Json.arr
          #[toJson (constructors.map (·.raw)), base.encode])]
      let some form := state.componentForm? (entry.componentAddress constructors)
        | throwError "the component's complete accepted input form is absent"
      return {
        form
        payload := (← combinedPayload e data (#[original] ++ dependencies))
        categoryContext := some { expression := action.target, bundle := action.targetBundle } }
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
      return { form := .canonicalMorphism category, payload := forwardPayload wire e wire.json }
  | .object id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let (args, dependencies) ← realizedParameters h trace params
      if let some presented ← realizeObjectPresentation h trace entry params args dependencies then
        return presented
      let json := Json.mkObj [("ctor", id.raw), ("args", Json.arr args)]
      return { form := .object entry, payload := (← combinedPayload e json dependencies) }
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      let input ← realize h trace s!"the structural parameter of {what}" receiver
      let .object entry := input.form
        | throwStratum .noImplementation m!"a structural parameter has no named-object presentation"
      unless entry.id == source && entry.category == sourceCategory do
        throwStratum .noImplementation m!"a structural parameter has a different source presentation"
      let output ← transport trace input route
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
      return { output with form := imageForm state edge target, payload := forwardPayload output image (← actionObjectData trace input route) }
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
        liftExecution := original.liftExecution,
        categoryContext := original.categoryContext,
        endpointPresentation := original.endpointPresentation,
        constructionInputs := original.constructionInputs }
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
          discard <| edgeDescriptor trace step application
          image ← Semantic.objOf application image
        unless (← isDefEq image source.image) && (← isDefEq (← inferType image) expectedType) do
          throwError "the parameter identity class has an incompatible full structured image"
        unless ← Decide.kernelAccepts (← mkEq source.image representative) source.identity do
          throwError "the parameter identity class has no checked full-object identification"
      let input ← realize h trace s!"the accepted source of the parameter in {what}" chosen.object
      let output ← transportImage trace input chosen.route (some chosen.applications)
      unless ← isDefEq (← inferType output.value) expectedType do
        throwError "the realized parameter identity class has an incompatible structured type"
      return output
  | .namedMorphism id params =>
      let some entry := state.morphisms.find? (·.id == id) | unreachable!
      let (args, dependencies) ← realizedParameters h trace params
      let json := Json.mkObj [("ctor", id.raw), ("args", Json.arr args)]
      return {
        form := .namedMorphism entry
        payload := (← combinedPayload e json dependencies) }
  | .namedInclusion id categoryId params source target =>
      let some entry := state.inclusions.find? (·.id == id)
        | throwError "the retained inclusion is not a published row"
      unless entry.category == categoryId do
        throwError "the retained inclusion changed its registered category"
      unless ← withTransparency .all <| isDefEq (← inferType e)
          (← mkAppM ``Quiver.Hom #[source, target]) do
        throwError "the retained inclusion changed its full endpoint types"
      let (parameters, dependencies) ← realizedParameters h trace params
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let json := Json.mkObj [("ctor", toJson id.raw), ("args", Json.arr parameters)]
      return {
        form := .canonicalMorphism category
        payload := (← combinedPayload e json dependencies) }
  | .powerObjectMap id field params =>
      unless state.powerObjects.any (·.id == id) do
        throwError "the retained power object is not registered"
      let (parameters, wires) ← realizedParameters h trace params
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      let json := Json.mkObj [("ctor", "powerObjectMap"),
        ("args", Json.arr #[toJson id.raw, toJson field, Json.arr parameters])]
      return { form := .canonicalMorphism sets, payload := (← combinedPayload e json wires) }
  | .objectField id field categoryId params =>
      let some entry := state.objects.find? (·.id == id)
        | throwError "the retained field owner is not registered"
      let declared := ObjectPresentation.fieldDeclaration entry field
      unless declared.isSome do
        throwError "the retained object row registers no {field} map"
      let actual ← ObjectPresentation.field entry field params
      unless ← withTransparency .all <| isDefEq actual e do
        throwError "the retained object field changed its accepted map or direction"
      let (parameters, dependencies) ← realizedParameters h trace params
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let json := Json.mkObj [("ctor", "objectField"),
        ("args", Json.arr #[toJson id.raw, toJson field, Json.arr parameters])]
      return {
        form := .canonicalMorphism category
        payload := (← combinedPayload e json dependencies) }
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
      let domainWire ← realizeEndpoint h trace "the constrained point original domain" domain
      let sourceWire ← realizeEndpoint h trace "the constrained point data-field type" source
      let targetWire ← realizeEndpoint h trace "the constrained point selected target" target
      let json := (Backend.ConstrainedPoint.mk constructor.toString domainWire.json
        sourceWire.json targetWire.json datum.json).encode
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the constrained point category is not registered"
      return {
        form := .canonicalMorphism category
        payload := (← combinedPayload e json #[datum, domainWire, sourceWire, targetWire]) }
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
      let (parameters, parameterWires) ← realizedParameters h trace params
      let source ← realizeEndpoint h trace "the admitted point original domain" originalSource
      let target ← realizeEndpoint h trace "the admitted point original codomain" originalTarget
      let some (_, selected) := Language.homEnds? (← inferType e)
        | throwError "the admitted point lost its full formal endpoints"
      discard <| Semantic.recordNamedObject selected (some trace)
      let selected ← realizeEndpoint h trace "the admitted point selected target" selected
      let json := Json.mkObj [("ctor", "admittedPoint"), ("args", Json.arr #[
        toJson id.raw, Json.arr parameters, source.json, target.json, selected.json, datum.json])]
      let payload ← combinedPayload e json (#[datum, source, target, selected] ++ parameterWires)
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the admitted point category is not registered"
      return { form := .canonicalMorphism category, payload }
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
      let (args, dependencies) ← realizedParameters h trace params
      let json := Json.mkObj [("ctor", toJson address), ("args", Json.arr args)]
      return { form, payload := (← combinedPayload e json dependencies) }
  | .pointView source target route applications argument =>
      let original ← realize h trace "the original point structure" source
      let selected ← realize h trace "the selected forward point structure" target
      unless route.size == applications.size do
        throwError "the point view omitted an actual edge application"
      let some originalCategory := state.categories.find? (·.id == original.form.category)
        | throwError "the original point structure category is not registered"
      let mut currentCategory := originalCategory.expression
      let mut image := original.value
      let mut targetJson := original.json
      for (edgeRef, application) in route.zip applications do
        let some edge := (state.edgesFrom currentCategory).find? (·.ref == edgeRef)
          | throwError "the point view does not use an accepted structural route"
        let application ← StructuredResult.checkReconstruction application
        let declared ← Semantic.edgeFunctor state edgeRef
        unless ← withoutModifyingState (isDefEq declared application) do
          throwError "the retained point action is not its registered edge application"
        image ← Semantic.objOf application image
        targetJson := Json.mkObj [("ctor", "functorAction"), ("args", Json.arr #[
          ← edgeDescriptor trace edgeRef application, targetJson])]
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
      let sourceAnswer := Json.mkObj [("ctor", "element"),
        ("args", Json.arr #[original.json,
          Json.mkObj [("ctor", "point"), ("args", Json.arr #[point.json])]])]
      let json := Json.mkObj [("ctor", "pointView"),
        ("args", Json.arr #[targetJson, sourceAnswer, domainWire.json])]
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      return {
        form := .canonicalMorphism sets
        payload := (← combinedPayload e json #[original, selected, point, domainWire]) }
  | .limitProjection receiver index =>
      let wire ← realize h trace "the complete construction defining this leg" receiver
      let .construction result _ := wire.payload
        | throwStratum .noImplementation "the receiver has no retained complete construction"
      let some (.limit id _ _) ← (trace.node? receiver : IO _)
        | throwStratum .invalid "the receiver is not a recorded formal construction"
      let value ← result.leg index
      unless ← withTransparency .all <| isDefEq value e do
        throwError "the retained formal defining leg changed its original question"
      let some category := state.categories.find? (·.id == wire.form.category) | unreachable!
      let some row := state.limits.find? (·.id == id)
        | throwError "the retained formal defining construction has no registered schema"
      let encodeInput := fun value => do
        if (← trace.node? value).isSome then
          return .ok (← realize h trace "an input of the defining map" value).json
        return .ok (← parameterData trace value)
      let encodeAction := fun action => do
        let mut descriptors : Array Json := #[]
        for entry in state.functors do
          let descriptor ← withoutModifyingState do
            let registered ← Semantic.asFunctor (← instantiateFresh entry.declaration)
            unless ← withTransparency .all <| isDefEq registered action do return none
            return some (← edgeDescriptor trace (.functor entry.id) action)
          if let some descriptor := descriptor then descriptors := descriptors.push descriptor
        let #[descriptor] := descriptors
          | return .error "the defining-map action has no unique registered descriptor"
        return .ok descriptor
      let json ← match ← StructuredResult.projectData row result.diagram result.answer index
          encodeInput encodeAction with
        | .ok data => pure data
        | .error message => throwStratum .noImplementation message
      return { form := .canonicalMorphism category, payload := forwardPayload wire e json }
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
      let json := match wire.json.getObjValAs? String "ctor",
          (wire.json.getObjVal? "args").bind (·.getArr?) with
        | .ok "arrow", .ok #[_, _, hom] =>
            if wire.objectIso.isNone then hom
            else Json.mkObj [("ctor", "arrowHom"), ("args", Json.arr #[wire.json])]
        | _, _ => Json.mkObj [("ctor", "arrowHom"), ("args", Json.arr #[wire.json])]
      return {
        form := contextualForm state baseContext wire.form true
        payload := forwardPayload wire e json
        categoryContext := some baseContext }
  | .morphismIdentity categoryId object =>
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let endpoint ← realizeEndpoint h trace "the identity endpoint" object
      let value ← mkAppM ``CategoryTheory.CategoryStruct.id #[endpoint.value]
      unless ← isDefEq (← inferType value) (← inferType e) do
        throwError "the identity endpoint changed its fixed type"
      let json := Json.mkObj [("ctor", "identity"),
        ("args", Json.arr #[endpoint.json, endpoint.json])]
      return { form := .canonicalMorphism category, payload := forwardPayload endpoint e json }
  | .productMediator categoryId presentation domain left right =>
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the formal product mediator category is not registered"
      let first ← realize h trace "the first product point" left
      let second ← realize h trace "the second product point" right
      -- A mediator of maps out of a generalized domain is the morphism `⟨f, g⟩`, sent with
      -- both maps; its endpoints are the declared domain and product apex.
      unless ← withTransparency .all <| isDefEq domain (← closedElementDomain state) do
        let json := Json.mkObj [("ctor", "mediator"), ("args", Json.arr #[first.json, second.json])]
        return {
          form := .canonicalMorphism category
          payload := (← combinedPayload e json #[first, second]) }
      let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
      let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
      unless ← withTransparency .all <| isDefEq (← inferType e)
          (← mkAppM ``Quiver.Hom #[domain, apex]) do
        throwError "the product point changed its independently fixed formal type"
      let payload ← combinedPayload e (Json.arr #[first.json, second.json]) #[first, second]
      -- This array is the product point's two ordered components, not a graph
      -- over its generalized domain. Apply the complete endpoint presentations
      -- here so later callable framing preserves the released point encoding.
      let point : Wire := { form := .canonicalMorphism category, payload }
      let source ← realizeEndpoint h trace "the product point's generalized domain" domain
      let target ← realizeEndpoint h trace "the product point's complete target" apex
      presentMorphism point source target
  | .morphismComposition categoryId first second source middle target =>
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let specialized ← match ← (trace.node? second : IO _) with
        | some (.constructionMap id params _ _ _) => do
          let some entry := state.constructions.find? (·.id == id)
            | throwError "the applied construction map is no longer registered"
          let (parameters, dependencies) ← realizedParameters h trace params
          pure (some (entry.mapAddress, parameters, dependencies,
            Form.constructionInput entry categoryId))
        | some (.cellComponent id params constructors inverse receiver) => do
          let some entry := state.cells.find? (·.id == id)
            | throwError "the applied cell is no longer registered"
          let (parameters, dependencies) ← realizedParameters h trace params
          let original ← realize h trace "the component's complete selected receiver" receiver
          pure (some (entry.componentAddress constructors,
            #[Json.arr parameters, original.json, toJson inverse], dependencies.push original,
            Form.cellComponent entry constructors categoryId))
        | _ => pure none
      if let some (address, parameters, dependencies, inputForm) := specialized then
        let argument ← realize h trace "the original generalized point of the selected action" first
        let arrow ← realize h trace "the complete selected callable action" second
        let domainWire ← realizeEndpoint h trace "the selected action's original generalized domain" source
        let sourceWire ← realizeEndpoint h trace "the selected action's complete source" middle
        let targetWire ← realizeEndpoint h trace "the selected action's complete target" target
        let invocation : Backend.PointInvocation := {
          operation := address
          parameters
          arrow := arrow.json
          domain := domainWire.json
          source := sourceWire.json
          target := targetWire.json
          argument := argument.json }
        let input : Wire := {
          form := inputForm
          payload := (← combinedPayload e invocation.encode
            (#[argument, arrow, domainWire, sourceWire, targetWire] ++ dependencies)) }
        let (answer, backend) ← send h address input (completeRequest := true)
        let validation ← if ← withTransparency .all <| isDefEq source (← closedElementDomain state) then
          ComputationalData.validateElementAt target targetWire.json (← pointResultValue state e) answer
        else ComputationalData.validateEndpointPort e domainWire.json targetWire.json answer
        match validation with
        | .error message => malformed backend address answer message
        | .ok () => pure ()
        let data ← receiveComputationalData h backend address answer
        let result : Wire := { form := .canonicalMorphism category, payload := .computed e data }
        return { result with payload := computedPayload e result.json (← mergeOwners input.owner? result.owner?) }
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
        let (parameters, parameterWires) ← realizedParameters h trace params
        for object in #[source, middle, target] do
          discard <| Semantic.recordNamedObject object (some trace)
        let domainWire ← realizeEndpoint h trace "the generalized point domain" source
        let sourceWire ← realizeEndpoint h trace "the applied operation source" middle
        let targetWire ← realizeEndpoint h trace "the applied operation target" target
        let operationWire ← realize h trace "the complete applied operation" second
        let (arrow, operationEndpoints) ← frameMorphismData h trace middle target operationWire
        let (argumentData, argumentEndpoints) ← frameMorphismData h trace source middle argument
        let invocation : Backend.PointInvocation := {
          operation := address, parameters, arrow,
          domain := domainWire.json, source := sourceWire.json, target := targetWire.json,
          argument := argumentData }
        let requestData := invocation.encode
        let payload ← combinedPayload e requestData
          (#[argument, operationWire, domainWire, sourceWire, targetWire] ++
            parameterWires ++ operationEndpoints ++ argumentEndpoints)
        let request : Wire := { form := sourceWire.form, payload }
        let (answer, backend) ← send h address request (completeRequest := true)
        match ← ComputationalData.validateElementAt target targetWire.json
            (← pointResultValue state e) answer with
        | .error message => malformed backend address answer message
        | .ok () => pure ()
        let data ← receiveComputationalData h backend address answer
        return {
          form := .canonicalMorphism category, payload := .computed e data
          morphismFramed := true }
      let a ← realize h trace "the first composed map" first
      let b ← realize h trace "the second composed map" second
      unless ← isDefEq (← inferType a.value) (← mkAppM ``Quiver.Hom #[source, middle]) do
        throwError "the first computed arrow changed its fixed endpoints"
      unless ← isDefEq (← inferType b.value) (← mkAppM ``Quiver.Hom #[middle, target]) do
        throwError "the second computed arrow changed its fixed endpoints"
      let value ← mkAppM ``CategoryTheory.CategoryStruct.comp #[a.value, b.value]
      discard <| StructuredResult.checkReconstruction value
      let (firstData, firstEndpoints) ← frameMorphismData h trace source middle a
      let (secondData, secondEndpoints) ← frameMorphismData h trace middle target b
      let json := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[firstData, secondData])]
      let payload ← combinedPayload e json (#[a, b] ++ firstEndpoints ++ secondEndpoints)
      return { form := .canonicalMorphism category, payload, morphismFramed := true }
  | .presentation id params inverse =>
      let some entry := state.presentations.find? (·.id == id) | unreachable!
      let (args, dependencies) ← realizedParameters h trace params
      let some source := state.objects.find? (·.id == entry.source) | unreachable!
      let json := Json.mkObj [("ctor", "presentation"),
        ("args", Json.arr #[toJson id.raw, Json.arr args, toJson inverse])]
      return {
        form := .presentation entry source.category
        payload := (← combinedPayload e json dependencies) }
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let (args, dependencies) ← realizedParameters h trace params
      let json := Json.mkObj [("ctor", "generator"), ("args", Json.arr #[toJson id.raw, Json.arr args])]
      return { form := .generator entry, payload := (← combinedPayload e json dependencies) }
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
      let (parameterData, dependencies) ← realizedParameters h trace params
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      let data := Json.mkObj [("ctor", "operationPoint"), ("args", Json.arr #[
          toJson id.raw, Json.arr parameterData, comparisonWire.json, domainWire.json, selectedWire.json])]
      return {
        form := .canonicalMorphism sets
        payload := (← combinedPayload e data (#[comparisonWire, domainWire, selectedWire] ++ dependencies)) }
  | .elementValue point target selected =>
      let globalPoint ← Language.globalPoint.run {}
      let action ← Language.functionOf point
      let value := mkApp action globalPoint
      unless (← withTransparency .all <| isDefEq (← inferType value) target) &&
          (← withTransparency .all <| isDefEq value e) do
        throwError "the closed parameter lost its independently selected point and carrier"
      discard <| Semantic.recordNamedObject selected (some trace)
      let selectedWire ← realize h trace "the selected parameter structure" selected
      let pointWire ← realize h trace "the closed computational parameter" point
      let json := Json.mkObj [("ctor", "element"), ("args", Json.arr #[selectedWire.json,
        Json.mkObj [("ctor", "point"), ("args", Json.arr #[pointWire.json])]])]
      return {
        form := .element selectedWire.form
        payload := (← combinedPayload e json #[selectedWire, pointWire]) }
  | .elementNumeral _ target selected | .operationApply _ _ _ target selected =>
      discard <| Semantic.recordNamedObject selected (some trace)
      let selectedWire ← realize h trace "the selected element structure" selected
      let (expression, dependencies) ← elementExpression h trace e
      let answer := Json.mkObj [("ctor", "element"),
        ("args", Json.arr #[selectedWire.json, expression])]
      let some (_, endpoint) := Language.homEnds? (← inferType e)
        | throwError "the retained element expression lost its categorical point endpoints"
      unless ← withTransparency .all <| isDefEq endpoint target do
        throwError "the retained element expression changed its selected target"
      if e.hasMVar || e.hasLevelMVar || e.hasFVar then
        throwError "the retained element expression is not closed"
      unless ← isTypeCorrect e do
        throwError "the retained formal element expression is outside its declared signature"
      return {
        form := .element selectedWire.form
        payload := (← combinedPayload e answer (#[selectedWire] ++ dependencies)) }
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
            let (expression, dependencies) ← elementExpression h trace argument
            pure (Json.mkObj [("ctor", "element"),
              ("args", Json.arr #[sourceWire.json, expression])], dependencies)
        | _ => pure (argumentWire.json, #[])
      let (args, dependencies) ← realizedParameters h trace params
      let request := { sourceWire with payload := (← combinedPayload sourceWire.value
        (Json.mkObj [("ctor", "presentationApply"),
          ("args", Json.arr #[Json.arr args, toJson inverse, sourceWire.json, targetWire.json, argumentData])])
        (#[sourceWire, targetWire, argumentWire] ++ argumentDependencies ++ dependencies)) }
      let (answer, backend) ← send h id.raw request #[] true
      let expectedPoint ← pointResultValue state e
      match ← ComputationalData.validateElementAt target targetWire.json expectedPoint answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw answer true
      return { form := .element targetWire.form, payload := .computed e data }

  | .morphismTransport sourceCategory targetCategory route receiver =>
      let input ← realize h trace "the map before structural transport" receiver
      unless input.form.category == sourceCategory do
        throwError "the structural map has the wrong recorded source category"
      let some (source, target) := Language.homEnds? (← inferType receiver)
        | throwError "the structural map has no complete selected endpoints"
      let (inputData, endpointDependencies) ← frameMorphismData h trace source target input
      let mut value := input.value
      let mut json := inputData
      let mut dependencies := #[input] ++ endpointDependencies
      for step in route do
        let U ← Semantic.edgeFunctor state step
        value ← Semantic.mapOf U value
        let (descriptor, parameters) ← realizedEdgeDescriptor h trace step U
        dependencies := dependencies ++ parameters
        json := Json.mkObj [("ctor", "map"), ("args", Json.arr #[
          descriptor, json])]
      let requested ← Semantic.mapOf (← Semantic.routeFunctor state route) receiver
      unless ← isDefEq requested e do
        throwError "the recorded map transport differs from the semantic request"
      let some category := state.categories.find? (·.id == targetCategory)
        | throwError "the structural map's target category is not registered"
      return {
        form := .canonicalMorphism category, morphismFramed := true
        payload := (← combinedPayload e json dependencies) }
  | .functor id params receiver =>
      let some entry := state.functor? id | unreachable!
      let input ← realize h trace s!"the source of {id.raw} in {what}" receiver
      let (args, dependencies) ← realizedParameters h trace params
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
      let endpointPresentation ← mapEndpointPresentation F
        (Json.mkObj [("ctor", id.raw), ("args", Json.arr args)]) input.endpointPresentation
      if let some projected ← projectObjectAction trace entry.source (.functor id)
          F receiver input.json then
        return {
          form
          endpointPresentation := endpointPresentation
          categoryContext := some context
          payload := (← combinedPayload e projected (#[input] ++ dependencies)) }
      let request := { input with payload := (← combinedPayload input.value (Json.mkObj [("ctor", id.raw),
        ("args", Json.arr args), ("receiver", input.json)]) (#[input] ++ dependencies)) }
      let (answer, backend) ← send h id.raw request
      let checked ← match target? with
        | some target => validateComputationalObject trace target e answer
        | none => ComputationalData.validatePort e (← inferType e) answer
      match checked with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw answer true
      let result : Wire := {
        form, payload := .computed e data
        endpointPresentation := endpointPresentation
        categoryContext := some context }
      let owner ← mergeOwners request.owner? result.owner?
      return { result with payload := computedPayload e result.json owner }
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
      let result ← if registered then transport trace input route
        else transportImage trace input route (some applications)
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
      let output ← transport trace input route
      unless ← isDefEq (← inferType output.value) (← inferType e) do
        throwError "the selected structure action has an incompatible full structured type"
      if output.form.category == targetCategory then return output
      let some target := state.categories.find? (·.id == targetCategory)
        | throwError "the selected structural target schema is not registered"
      let some edge := route.back?
        | throwError "an empty selected route changed its category"
      return { output with form := imageForm state edge target, payload := forwardPayload output semanticImage (← actionObjectData trace input route) }
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
      let (parameters, parameterWires) ← realizedParameters h trace params
      let invocation : Backend.PointInvocation := {
        operation, parameters,
        arrow := Json.mkObj [("ctor", toJson operation), ("args", Json.arr parameters)],
        domain := domainWire.json, source := sourceWire.json, target := targetWire.json,
        argument := input.json }
      let request : Wire := {
        form := input.form
        payload := (← combinedPayload arrow invocation.encode (#[input, domainWire, sourceWire, targetWire] ++ parameterWires)) }
      let (answer, backend) ← send h operation request (completeRequest := true)
      let checked ← if ← withTransparency .all <| isDefEq domain (← closedElementDomain state) then
        ComputationalData.validateElementAt target targetWire.json (← pointResultValue state e) answer
      else ComputationalData.validateEndpointPort e domainWire.json targetWire.json answer
      match checked with
      | .error message => malformed backend operation answer message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend operation answer
      let some category := state.categories.find? (·.id == entry.category) | unreachable!
      let result : Wire := { form := .canonicalMorphism category, payload := .computed e data }
      let owner ← mergeOwners request.owner? result.owner?
      return { result with payload := computedPayload e result.json owner }
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
      let source ← realizeCallableEndpoint h trace morphism source true (some plan.base)
      let target ← realizeCallableEndpoint h trace morphism target false (some plan.base)
      let morphism ← presentMorphism morphism source target
      let json := Json.mkObj [("ctor", "arrow"),
        ("args", Json.arr #[source.json, target.json, morphism.json])]
      return {
        form := .arrow entry
        payload := (← combinedPayload e json #[source, target, morphism])
        categoryContext := some context }
  | .literal id literal =>
      let some form := state.form? id.raw
        | throwError "{id.raw} is not a registered literal form"
      match ← Codec.encode literal with
      | .ok json => return { form := form, payload := .ordinary (e) (json) }
      | .error message =>
          throwStratum .noImplementation m!"{what} is not sent: the literal {literal} of \
            {id.raw} is not encoded ({message})"
  | .limit id D lift? =>
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
      let infos ← forallTelescopeReducing (← getConstInfo standard).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let data := (D.getAppArgs.zip infos).filterMap fun (a, i) =>
        if i.isExplicit then some a else none
      let wires ← data.mapM fun a => do
        if let some (json, dependencies) ← extentData? h trace a then
          let literal ← realize h trace s!"a diagram object of {what}" a
          return { literal with payload := (← combinedPayload a json (#[literal] ++ dependencies)) }
        if (← trace.node? a).isNone then
          discard <| Semantic.recordNamedObject a (some trace)
          let mut application := a.consumeMData
          while application.isAppOfArity ``id 2 do
            application := application.appArg!.consumeMData
          if let some entry := state.morphisms.find? fun entry =>
              application.getAppFn.constName? == some entry.declaration then
            Semantic.namedMorphism entry a (some trace)
          if (← trace.node? a).isNone then
            discard <| Semantic.recordRegisteredMorphism row.category a (some trace)
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
              let sourceWire ← realize h trace s!"a canonical diagram arrow's source in {what}" source
              let targetWire ← realize h trace s!"a canonical diagram arrow's target in {what}" target
              return { form := .canonicalMorphism category, payload := (← combinedPayload a
                (Json.mkObj [("ctor", toJson tag), ("args", Json.arr #[sourceWire.json, targetWire.json])])
                #[sourceWire, targetWire]) }
        realize h trace s!"the diagram of {id.raw} in {what}" a
      let sourceDiagram ← mkAppM standard (wires.map (·.value))
      let sourceWires := wires
      let (sent, wires) ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
        | none => pure (sourceDiagram, wires)
        | some lift => do
          let U ← Semantic.edgeFunctor state lift.edge
          let mapped ← wires.mapM fun wire => do
            match wire.form with
            | .object _ => transport trace wire #[lift.edge]
            | .graph _ =>
              let value ← Semantic.mapOf U wire.value
              let form := (state.graphLiterals.find? (·.category == category.id)).map Form.graph
                |>.getD (.canonicalMorphism category)
              -- Interpret the existing source graph as an arrow of the *target*
              -- graph-literal form, at the mapped arrow's exact typed endpoints.
              -- Reuse its bytes only if Lean identifies this independently
              -- reconstructed target map with the selected U.map source map.
              let decoded ← decodeValue trace category (← inferType value) wire.json
              let unchanged ← match decoded with
                | .error _ => pure false
                | .ok (targetMap, _) => do
                    if ← withTransparency .all <| withoutModifyingState
                        (isDefEq value targetMap) then pure true
                    else do
                      let condition ← mkEq value targetMap
                      match ← Codec.conditionProof condition with
                      | some proof => Decide.kernelAccepts condition proof
                      | none => pure false
              let unchanged ← if unchanged then do
                -- Check the target representation. A non-primitive concrete
                -- point type can use only its actual transported endpoint
                -- descriptors, never enumeration of the formal carrier.
                let checked ← ComputationalData.validatePort value (← inferType value) wire.json
                match checked with
                | .ok () => pure true
                | .error "the callable's point types require their released data representation" => do
                    let some (source, target) := Language.homEnds? (← inferType wire.value)
                      | pure false
                    let sourceWire ← realize h trace "the mapped graph source" source
                    let targetWire ← realize h trace "the mapped graph target" target
                    let sourceWire ← transport trace sourceWire #[lift.edge]
                    let targetWire ← transport trace targetWire #[lift.edge]
                    match ← ComputationalData.endpointKeys sourceWire.json,
                        ← ComputationalData.endpointKeys targetWire.json with
                    | .ok (some domain), .ok codomain =>
                        pure (ComputationalData.validateGraphEndpoints domain codomain wire.json).isOk
                    | _, _ => pure false
                | .error _ => pure false
              else pure false
              let json ← if unchanged then pure wire.json else
                pure <| Json.mkObj [("ctor", "map"), ("args", Json.arr #[
                  ← edgeDescriptor trace lift.edge U, wire.json])]
              pure { wire with form, payload := forwardPayload wire value json }
            | _ =>
              if (Language.homEnds? (← inferType wire.value)).isSome then
                let value ← Semantic.mapOf U wire.value
                let json := Json.mkObj [("ctor", "map"), ("args", Json.arr #[
                  ← edgeDescriptor trace lift.edge U, wire.json])]
                pure { wire with
                  form := .canonicalMorphism category
                  payload := forwardPayload wire value json }
              else
                transport trace wire #[lift.edge]
          pure (← mkAppM standard (mapped.map (·.value)), mapped)
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
      let mut inputRoles := #[]
      let mut retainedSourceWires := #[]
      let mut retainedWires := #[]
      for index in [:wires.size] do
        let some wire := wires[index]?
          | throwError "the constructed diagram lost an input wire"
        -- The source and target of U.map f need not be separately named
        -- objects. Their selected presentations are U applied to the
        -- original endpoints, not fresh interpretations of U.obj X.
        let some original := sourceWires[index]?
          | throwError "the constructed diagram lost its original input wire"
        match Language.homEnds? (← inferType original.value) with
        | none =>
            retainedSourceWires := retainedSourceWires.push original
            retainedWires := retainedWires.push wire
            inputRoles := inputRoles.push (wire.json, none, none)
        | some (source, target) =>
            for endpoint in #[source, target] do
              if (← trace.node? endpoint).isNone then
                discard <| Semantic.recordNamedObject endpoint (some trace)
            let source ← realize h trace "the construction input map's retained source" source
            let target ← realize h trace "the construction input map's retained target" target
            -- A graph's images cannot specify its chosen codomain. Keep the
            -- complete callable context in source packets and dispatched diagrams,
            -- so later operations can consume either without inventing endpoints.
            let sourceJson := Json.mkObj [("ctor", "typedMap"),
              ("args", Json.arr #[source.json, target.json, original.json])]
            let original := { original with payload :=
              (← combinedPayload original.value sourceJson #[original, source, target]) }
            retainedSourceWires := retainedSourceWires.push original
            let (source, target) ← match lift? with
              | none => pure (source, target)
              | some liftId => do
                  let some lift := state.lifts.find? (·.id == liftId)
                    | throwStratum .noImplementation "the source endpoint has no selected creation lift"
                  pure (← transport trace source #[lift.edge],
                    ← transport trace target #[lift.edge])
            let json := Json.mkObj [("ctor", "typedMap"),
              ("args", Json.arr #[source.json, target.json, wire.json])]
            let wire := { wire with payload :=
              (← combinedPayload wire.value json #[wire, source, target]) }
            retainedWires := retainedWires.push wire
            inputRoles := inputRoles.push (wire.json, some source.json, some target.json)
      let sourceDiagramJson := Json.mkObj [("ctor", Codec.label standard),
        ("args", Json.arr (retainedSourceWires.map (·.json)))]
      let diagramJson := Json.mkObj [("ctor", Codec.label standard),
        ("args", Json.arr (retainedWires.map (·.json)))]
      let input : Wire := {
        form := .diagrams category
        payload := (← combinedPayload sent diagramJson (retainedSourceWires ++ retainedWires)) }
      let resolveRole := fun role => do
        match role with
        | .argument position => return (← inputRoles[position]?).1
        | .source position => (← inputRoles[position]?).2.1
        | .target position => (← inputRoles[position]?).2.2
      let externalDescriptor := fun binder => do
        let binding ← plan.binders[binder]?
        let role ← binding.inputRoles[0]?
        let descriptor ← resolveRole role
        if binding.inputRoles.all (fun other => resolveRole other == some descriptor) then
          some descriptor
        else none
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
      let (rawAnswer, backend) ← send h id.raw input
      -- The public result envelope is independent of the complete cone schema.
      -- Retain its actual fields for both validation and later projections; nested
      -- opaque handles acquire their live owner below. A wholly opaque packet still
      -- fails the complete cone/cocone schema rather than hiding required fields.
      let answer := match Backend.ComputationalValue.decode rawAnswer with
        | .ok (.inline data) => data
        | _ => rawAnswer
      let mut createdPresentation? : Option Expr := none
      let formalPresentation ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
        | none => Semantic.limitPresentation row sent
        | some lift => do
          let some edge := state.structuralEdge? lift.edge | unreachable!
          let some source := state.categories.find? (·.expression.syntacticEq edge.source)
            | throwError "the creation lift has no registered full source category"
          Semantic.limit row.colimit row.shape sourceDiagram source.id.raw none
      let formalDiagram := if lift?.isSome then sourceDiagram else sent
      let formalDiagramJson := if lift?.isSome then sourceDiagramJson else input.json
      let packet ← match lift? with
        | none => pure (StructuredResult.ComputationPacket.direct answer)
        | some lift => pure (.created lift.raw sourceDiagramJson answer)
      let mut completed ← match ← StructuredResult.complete row formalDiagram formalDiagramJson
          packet formalPresentation (fun answer =>
            StructuredResult.validatePlannedData plan answer
              (fun port seen json => ComputationalData.validatePlannedPort plan port seen json
                externalDescriptor ComputationalData.endpointKeys)) with
        | .ok complete => pure complete
        | .error message => malformed backend id.raw rawAnswer message
      -- Validate the backend packet before reconstructing formal creation evidence:
      -- a malformed reply is not a missing universal-property implementation.
      if let some liftId := lift? then
        let some creation := state.lifts.find? (·.id == liftId)
          | throwStratum .noImplementation "the requested creation lift is not registered"
        let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[formalLowerPresentation]
        let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
        -- The lower universal cone has been transported along the checked
        -- cospan comparison: it is over sourceDiagram ⋙ U, not over the
        -- standard mapped cospan `sent` used as the computational wire.
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
      let form ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
        | none => pure (.limitApex row)
        | some lift => do
          let some edge := state.structuralEdge? lift.edge | unreachable!
          let some source := state.categories.find? (·.expression.syntacticEq edge.source)
            | throwError "the creation lift has no registered source schema"
          pure (.createdApex row source.id)
      let scope ← computationalScope h backend answer
      let returnedOwner := match scope with
        | .portable => none
        | .owned backend session => some (backend, session)
      let owner ← mergeOwners input.owner? returnedOwner
      let scope := match owner with
        | none => ComputationScope.portable
        | some (backend, session) => .owned backend session
      let constructionInputs : ComputationalData.InterfaceObjects :=
        plan.binders.filterMap fun binding => if binding.port.isSome then none else do
          let formal ← binding.formalValue
          let actual ← externalDescriptor binding.index
          return (actual, formal)
      return {
        form := form, payload := .construction completed scope
        constructionInputs := some (completed.apex, constructionInputs) }
  | .method id route receiver =>
      let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let (request, input) ← operationReceiver trace original route
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
      discard <| Semantic.validateResolutionComparisons state resolution (some receiver)
      let comparisons := resolution.comparisons
      if let some projected ← projectObjectAction trace functor.source (.functor functor.id)
          F acceptedInput request.json then
        unless ← withTransparency .all <| isDefEq expected e do
          throwError "the projected method changed its independently retained formal result"
        return {
          form
          categoryContext := some context
          payload := forwardPayload request e projected }
      let (json, backend) ← send h id.raw (← computationalApexReceiver trace request) comparisons
      let checked ← match target? with
        | some target => validateComputationalObject trace target expected json
        | none => ComputationalData.validatePort expected (← inferType expected) json
      match checked with
      | .error message => malformed backend id.raw json message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw json true
      let result : Wire := { form, payload := .computed e data, categoryContext := some context }
      let owner ← mergeOwners request.owner? result.owner?
      return { result with payload := computedPayload e result.json owner }
  | .methodWithLifts id route lifts receiver =>
      let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let (request, input) ← operationReceiver trace original route
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
      discard <| Semantic.validateResolutionComparisons state resolution (some receiver)
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
      let (answer, backend) ← send h id.raw request resolution.comparisons
      match ← validateComputationalObject trace target expected answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let baseData ← receiveComputationalData h backend id.raw answer true
      let receivedBase : Wire := { form := .subobject target, payload := .computed retainedBase baseData }
      let baseOwner ← mergeOwners request.owner? receivedBase.owner?
      let base := { receivedBase with payload := computedPayload retainedBase receivedBase.json baseOwner }
      let parameters ← plan.components.mapM fun component => do
        realizedParameters h trace (← DirectConstruction.dataArguments component.selection.parameters)
      let (liftedJson, owner) ← executePrescribedLift h trace plan original base parameters
      let some checked ← LiftedSubobjectData.decodeIn (← inferType e) resultExpression
          receiver lifts retainedBase liftedJson
          (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
          (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
        | throwError "the prescribed method has no complete computational lift packet"
      let packet ← match checked with
        | .ok packet => pure packet
        | .error message => malformed backend id.raw liftedJson message
      unless ← withTransparency .all <| isDefEq packet.formalResult e do
        throwError "the independent prescribed lift changed its formal result"
      let payload := match owner with
        | none => .computed e (.inline packet.data)
        | some (backend, session) => .computed e (.owned backend session packet.data)
      let .ok complete := LiftedSubobjectData.fields "liftedSubobject" 4 packet.data
        | throwError "the completed lift lost its full ordered packet"
      let .ok steps := complete[3]!.getArr?
        | throwError "the completed lift lost its ordered component data"
      let mut actions := #[]
      let mut sources := #[]
      let mut bases := #[]
      for step in steps do
        let .ok fields := LiftedSubobjectData.fields "liftStep" 5 step
          | throwError "the completed lift lost a selected step"
        let .ok sourceFields := LiftedSubobjectData.fields "arrow" 3 fields[2]!
          | throwError "the completed lift lost its original complete source Arrow"
        actions := actions.push fields[1]!
        sources := sources.push sourceFields[0]!
        bases := bases.push fields[3]!
      let execution : LiftExecution := {
        selections := plan.components.map (·.selection), actions,
        parameters := parameters.map Prod.fst, sources, bases, outputs := packet.outputs }
      cacheLiftFields h execution owner
      let some first := execution.selections[0]?
        | throwError "the completed method lost its selected source lift"
      let context ← CategoryContext.construct (← SelectedLift.context first) constructor.id
      unless context.expression.syntacticEq resultExpression do
        throwError "the completed method changed its accepted constructed result category"
      return {
        form := match CategoryContext.named? state resultExpression with
          | some category => .subobject category
          | none => .contextual resultExpression original.form
        payload, liftExecution := some execution, categoryContext := some context }
  | .property id _ _ =>
      throwError "the decision {id.raw} is not a value"

end

/-- Remove only the reader's administrative expected-type wrappers. The original
categorical composition and its complete selected argument remain unchanged. -/
def operationApplicationBody (value : Expr) : Expr := Id.run do
  let mut value := value.consumeMData
  while value.isAppOfArity ``id 2 do value := value.appArg!.consumeMData
  return value

/-- Materialize a retained generalized operation through its existing complete
callable interface. The source is the original composition argument, not a point
invented at the terminal object or a recipe recovered from the returned value. -/
def realizeOperationObservation (h : Harness) (trace : Trace) (wire : Wire)
    (id : OperationId) (parameters : Array Expr) : TermElabM Wire := do
  let .ok ("element", #[_, expression]) := ComputationalData.envelope wire.json
    | return wire
  let .ok ("operationExpression", #[operationId, _, _]) := ComputationalData.envelope expression
    | return wire
  unless operationId == toJson id.raw do
    throwError "the retained operation recipe changed its accepted operation"
  let state ← registryState
  let some entry := state.operations.find? (·.id == id)
    | throwError "the retained operation is no longer registered"
  let formal := wire.value
  let composition := operationApplicationBody formal
  unless composition.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 do
    throwStratum .noImplementation
      "the complete operation recipe has no retained generalized composition argument"
  let argument := composition.getAppArgs[5]!
  let operation := composition.getAppArgs[6]!
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
  let some (domain, originalSource) := Language.homEnds? (← inferType argument)
    | throwError "the retained operation argument lost its original generalized domain"
  let some (resultDomain, resultTarget) := Language.homEnds? (← inferType formal)
    | throwError "the complete operation result lost its original typed endpoints"
  unless ← withTransparency .all <| isDefEq originalSource source <&&>
      isDefEq resultDomain domain <&&> isDefEq resultTarget target do
    throwError "the complete operation recipe changed its original composition endpoints"
  -- The accepted operation signature fixes the owner at the last object binder,
  -- before its declared numeral parameters. The result's carrier is not its owner:
  -- an operation on a ring or module is itself a map of underlying sets.
  let arguments := application.getAppArgs
  let some receiver := arguments[arguments.size - 1 - entry.numerals]?
    | throwError "the complete operation recipe lost its declared owner parameter"
  let some category := state.categories.find? (·.id == entry.category)
    | throwError "the complete operation recipe lost its accepted owner category"
  let receiverContext ← CategoryContext.ofNamed category receiver
  let receiverWire ← try
      realizeEndpoint h trace "the operation's exact declared owner" receiver
    catch error =>
      unless Exception.stratum? error == some .noImplementation do throw error
      let (data, dependencies) ← realizedParameters h trace #[receiver]
      let #[data] := data | throwError "the operation's declared owner lost its parameter data"
      pure { form := .diagrams category,
        payload := (← combinedPayload receiver data dependencies),
        categoryContext := some receiverContext : Wire }
  unless state.accepts (.operation entry) receiverWire.form do
    throwError "the complete operation's owner representation changed its declared category"
  let (parameterData, parameterWires) ← realizedParameters h trace parameters
  let callable : Wire := {
    form := wire.form
    payload := (← combinedPayload operation
      (Json.mkObj [("ctor", toJson id.raw), ("args", Json.arr parameterData)]) parameterWires) }
  let argumentWire ← realize h trace "the operation's original generalized argument" argument
  let domainWire ← realizeCallableEndpoint h trace argumentWire domain true
  let sourceWire ← realizeCallableEndpoint h trace callable source true
  let targetWire ← realizeCallableEndpoint h trace callable target false
  let (argumentData, endpoints) ← frameMorphismData h trace domain source argumentWire
  let invocation : Backend.PointInvocation := {
    operation := id.raw
    parameters := parameterData
    arrow := callable.json
    domain := domainWire.json
    source := sourceWire.json
    target := targetWire.json
    argument := argumentData }
  let input : Wire := {
    form := receiverWire.form
    payload := (← combinedPayload formal invocation.encode
      (#[receiverWire, callable, argumentWire, domainWire, sourceWire, targetWire] ++
        parameterWires ++ endpoints)) }
  let (answer, backend) ← send h id.raw input (completeRequest := true)
  let checked ← if ← withTransparency .all <| isDefEq domain (← closedElementDomain state) then
    ComputationalData.validateElementAt target targetWire.json (← pointResultValue state formal) answer
  else ComputationalData.validateEndpointPort formal domainWire.json targetWire.json answer
  if let .error message := checked then malformed backend id.raw answer message
  let data ← receiveComputationalData h backend id.raw answer true
  let result : Wire := { wire with payload := .computed formal data }
  let owner ← mergeOwners input.owner? result.owner?
  return { result with payload := computedPayload formal result.json owner }

/-- Demand the computational value of an entire arrow. Merely forming a named arrow,
including one used inside a later point invocation, retains its public descriptor.
Only this observation demand dispatches that descriptor. Structural composites are
rebuilt from the observed children through the ordinary checked realization paths,
retaining their exact endpoint frames, declared actions and session dependencies. -/
partial def realizeArrowObservation (h : Harness) (trace : Trace) (wire : Wire) :
    TermElabM Wire := do
  let formal := wire.value
  let some node ← (trace.node? formal : IO _) | return wire
  let rebuild (children : Array Expr) : TermElabM Wire := do
    for child in children do
      let input ← realize h trace "the observed arrow's constituent" child
      let actual ← realizeArrowObservation h trace input
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
    | .namedMorphism id _ => do
        -- A cached graph or opaque callable is already actual data. Provenance alone
        -- cannot distinguish it from a descriptor whose parameters were computed.
        unless tag == some id.raw do return wire
        let (answer, backend) ← send h id.raw wire
        match ← ComputationalData.validatePort formal (← inferType formal) answer with
        | .error message => malformed backend id.raw answer message
        | .ok () => pure ()
        let data ← receiveComputationalData h backend id.raw answer true
        pure { wire with payload := .computed formal data }
    | .namedCallable address _ _ => do
        unless tag == some address do return wire
        let (answer, backend) ← send h address wire
        match ← ComputationalData.validatePort formal (← inferType formal) answer with
        | .error message => malformed backend address answer message
        | .ok () => pure ()
        let data ← receiveComputationalData h backend address answer true
        pure { wire with payload := .computed formal data }
    | .operationApply id parameters _ _ _ =>
        realizeOperationObservation h trace wire id parameters
    | .morphismComposition _ first second source _ _ => do
        unless tag == some "compose" do return wire
        -- A closed-point composition is already an `apply` invocation. Its returned
        -- datum can itself be a callable and must not be replaced by its formal plan.
        if ← withTransparency .all <| isDefEq source (← closedElementDomain (← registryState)) then
          return wire
        rebuild #[first, second]
    | .morphismTransport _ _ _ receiver => do
        unless tag == some "map" do return wire
        rebuild #[receiver]
    | .contextualRoute _ _ route _ receiver true => do
        unless tag == some "map" || route.isEmpty do return wire
        rebuild #[receiver]
    | .contextualComposition _ first second _ _ _ => do
        unless tag == some "compose" do return wire
        rebuild #[first, second]
    | .callableRecipe _ _ _ body => rebuild #[body]
    | _ => pure wire
  if !formal.hasMVar && !formal.hasLevelMVar && !formal.hasFVar && !formal.hasLooseBVars then
    match actual.payload with
    | .ordinary .. => pure ()
    | _ => h.results.modify (·.insert formal actual)
  return actual

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
  let sourceJson := Json.mkObj [("ctor", "objectProduct"),
    ("args", Json.arr #[valueWire.json, valueWire.json])]
  let truthWire ← realize h trace "the computational equality's truth-value carrier" truth
  let (parameters, parameterWires) ← realizedParameters h trace parameterValues
  let invocation : Backend.PointInvocation := {
    operation := equality.id.raw, parameters,
    arrow := Json.mkObj [("ctor", toJson equality.id.raw), ("args", Json.arr parameters)],
    domain := domainWire.json, source := sourceJson, target := truthWire.json,
    argument := Json.arr #[first.json, second.json] }
  let payload ← combinedPayload arrow invocation.encode
    (#[first, second, domainWire, valueWire, truthWire] ++ parameterWires)
  let request : Wire := { form := .namedMorphism equality, payload }
  let (answer, backend) ← send h equality.id.raw request (completeRequest := true)
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
  let some (.property id route receiver) ← (trace.node? p : IO _)
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
  let (request, input) ← operationReceiver trace original route
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
  discard <| Semantic.validatePropertyResolutionComparisons state resolution (some receiver)
  let some classifier := state.classifier? property.classifier
    | throwError "the recorded property's classifier is not registered"
  -- Check the full selected domain without requiring an encoding of every intermediate image.
  let classifier ← classifierInstance classifier
  discard <| elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax input))) none
  call h id.raw (← computationalApexReceiver trace request)
    (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) resolution.comparisons

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
normalizing their presentation. Ordinary `mkDecideProof` remains available for a residue with
local hypotheses. The assembled proof is checked against the original `p` by Lean's kernel,
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
    throwStratum .noImplementation "this computational map requires a pointwise observation implementation"
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
partial def canonicalTerm : Expr → Expr
  | .mdata _ term => canonicalTerm term
  | .app fn arg => .app (canonicalTerm fn) (canonicalTerm arg)
  | .lam _ type body info => .lam .anonymous (canonicalTerm type) (canonicalTerm body) info
  | .forallE _ type body info => .forallE .anonymous (canonicalTerm type) (canonicalTerm body) info
  | .letE _ type value body nondep =>
      .letE .anonymous (canonicalTerm type) (canonicalTerm value) (canonicalTerm body) nondep
  | .proj type index term => .proj type index (canonicalTerm term)
  | term => term

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
  | .judged question _ expected _ => do
      let question ← instantiateQuestion question
      let table ← TermTable.new
      let roots ← encodeQuestion table question
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

/-- The operation schema has one encoder. Complete tie keys and the final snapshot
both use this same field traversal; typed terms use the unchanged proof-proposition quotient. -/
def encodeSnapshotNode (source : TermTable) (encode : Expr → TermElabM Nat)
    (node : Node) : TermElabM Json := do
  let encodeContext (context : CategoryContext) : TermElabM Json := do
    return Json.arr #[toJson (reprStr context.expression), toJson (← encode context.bundle)]
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
  | .method id route receiver =>
      pure (Json.arr #[toJson "method", toJson id.raw, toJson (route.map reprStr),
        toJson (← encode receiver)])
  | .methodWithLifts id route lifts receiver =>
      pure (Json.arr #[toJson "methodWithLifts", toJson id.raw, toJson (route.map reprStr),
        toJson (lifts.map (·.raw)), toJson (← encode receiver)])
  | .property id route receiver =>
      pure (Json.arr #[toJson "property", toJson id.raw, toJson (route.map reprStr),
        toJson (← encode receiver)])
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
      | .method id route receiver => pure (.method id route (← instantiateMVars receiver))
      | .methodWithLifts id route lifts receiver =>
          pure (.methodWithLifts id route lifts (← instantiateMVars receiver))
      | .property id route receiver => pure (.property id route (← instantiateMVars receiver))
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
