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
public import CasCatalogue.ElementData
public import CasCatalogue.QuestionIdentity
public import CasCatalogue.ComputationalData
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
   the operation's result form: the registered literal form of its result category. A registered
   limit is an operation on its diagram, sent in the forms of its objects and arrows; its answer
   is the cone of its shape, apex and legs, from which the kernel reconstructs the cone as
   Mathlib's standard constructor of the shape, deciding the commutation the legs must satisfy
   (CC-UNIV, CC-DECODE); an answer missing a leg, or whose legs do not commute, is malformed. No
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

structure Wire where
  form : Form
  payload : WirePayload
  /-- Accepted identifications used to change the wire presentation, in route order. -/
  presentationIsos : Array Expr := #[]
  /-- Full selected-object comparison from the fixed semantic receiver to actual returned data. -/
  objectIso : Option Expr := none

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
def closedElementDomain (state : RegistryState) : TermElabM Expr := do
  let some entry := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwStratum .noImplementation "the closed element singleton has no registered declaration"
  Semantic.object entry #[Syntax.mkNumLit "1"] none

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
  let portPython ← IO.FS.realPath ((← Backend.packageDir Backend.contractPackage) / "python")
  let path := match ← IO.getEnv "PYTHONPATH" with
    | some p => s!"{portPython}:{p}"
    | none => portPython.toString
  let child ← try
      IO.Process.spawn { toStdioConfig := Backend.Stdio, cmd := backend.command
                         args := backend.args, cwd := some root
                         env := #[("PYTHONPATH", some path)] }
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
def send (h : Harness) (operation : String) (input : Wire) : TermElabM (Json × String) := do
  let registrations := h.admitted.filter fun a =>
    a.registration.operation == operation && a.registration.input == input.formId &&
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
    ("backend", toJson registration.backend), ("session", toJson connection.identity),
    ("inputOwner", toJson input.owner?), ("request", input.json)]
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
def call (h : Harness) (operation : String) (input : Wire) (resultType : Expr) :
    TermElabM (Expr × Json) := do
  let (answer, backend) ← send h operation input
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
    (accepted? : Option Expr := none) :
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
    unless (← instantiateMVars m).isMVar do continue
    let t ← instantiateMVars (← inferType m)
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
  if let some (.object id params) ← (trace.node? value : IO _) then
    return Json.mkObj [("ctor", id.raw), ("args", Json.arr (← params.mapM (parameterData trace)))]
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
  if let .ok json ← Codec.encode value then return json
  let mut candidates : Array (ObjectEntry × Array Expr) := #[]
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
    if let some params := candidate then candidates := candidates.push (entry, params)
  let #[(entry, params)] := candidates
    | throwStratum .noImplementation m!"the exact functor parameter has no unique accepted data presentation"
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
  params.mapM (parameterData trace)

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

/-- Retain every residual object action, including its complete instantiated edge data. -/
def transportImage (trace : Trace) (w : Wire) (route : Array EdgeRef)
    (applications : Option (Array Expr) := none) : TermElabM Wire := do
  if let some retained := applications then
    unless retained.size == route.size do
      throwError "the retained route has incompatible ordered full applications"
  if route.isEmpty then return w
  let state ← registryState
  let some source := state.categories.find? (·.id == w.form.category)
    | throwError "the reconstructed source image has no accepted category"
  let mut expression := source.expression
  let mut result := w
  for index in [:route.size] do
    let step := route[index]!
    let some edge := (state.edgesFrom expression).find? (·.ref == step)
      | throwError "the reconstructed image route disagrees with its retained category"
    let some target := imageCategory? state edge.target
      | throwStratum .noImplementation m!"the transported image has no unique accepted target schema"
    let U ← match applications with
      | some retained => pure retained[index]!
      | none => Semantic.edgeFunctor state step
    let value ← Semantic.objOf U result.value
    let U ← instantiateMVars U
    if U.hasMVar || U.hasLevelMVar || U.hasFVar || U.hasLooseBVars then
      throwError "the retained structural edge application is not closed"
    let json := Json.mkObj [("ctor", "functorAction"),
      ("args", Json.arr #[← edgeDescriptor trace step U, result.json])]
    let objectIso ← mapObjectComparison U result.value result.objectIso
    result := { result with form := imageForm state step target, objectIso := objectIso, payload := forwardPayload result value json }
    expression := edge.target
  return result

partial def transport (trace : Trace) (w : Wire) (route : Array EdgeRef) : TermElabM Wire := do
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
  let decoded ← decodeFamily entry.declaration expected args fun type arg => do
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
  let diagramConstructor? := match (j.getObjValAs? String "ctor").toOption with
    | some "pair" => some ``CategoryTheory.Limits.pair
    | some "cospan" => some ``CategoryTheory.Limits.cospan
    | some "span" => some ``CategoryTheory.Limits.span
    | some "parallelPair" => some ``CategoryTheory.Limits.parallelPair
    | _ => none
  if let some constructor := diagramConstructor? then
    let .ok args := (j.getObjVal? "args").bind (·.getArr?)
      | return .error "a standard diagram has no ordered defining fields"
    return (← decodeFamily constructor type args (decodeValue trace category)).map fun
      (diagram, _) => (diagram, none)
  if let some result ← ConstructionData.decode type j fun expected data => do
      return (← decodeValue trace category expected data).map (·.1) then
    let form? := do
      guard ((j.getObjValAs? String "ctor").toOption == some "limitApex")
      let args ← (j.getObjVal? "args").toOption >>= (·.getArr?.toOption)
      let id ← args[0]? >>= (·.getStr?.toOption)
      let row ← state.limits.find? (·.id.raw == id)
      return Form.limitApex row
    return result.map (·, form?)
  if (j.getObjValAs? String "ctor").toOption.any (fun tag =>
      #["map", "compose", "presentation", "arrow", "arrowHom", "constructionLeg", "pointView", "operationPoint"].contains tag) then
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
      match ← decodeFamily entry.declaration type args (decodeValue trace category) with
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
    return (← decodeFamily entry.declaration
      (← inferType (← instantiateFresh entry.declaration)) args (decodeValue trace source)).map
      (fun (F, _) => (F, entry.source, entry.target))
  match tag, args with
  | "classifierForget", #[idJson, paramsJson] =>
      let .ok id := idJson.getStr? | return .error "a classifier edge has no registered id"
      let some entry := state.classifiers.find? (·.id.raw == id)
        | return .error "the classifier edge is not registered"
      let .ok params := paramsJson.getArr? | return .error "classifier declaration arguments are not ordered data"
      let .ok (classifier, _) ← decodeFamily entry.declaration
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
partial def decodeArrowData (trace : Trace) (category : NamedCategoryEntry) (json : Json) :
    TermElabM (Except String Expr) := do
  let state ← registryState
  let .ok tag := json.getObjValAs? String "ctor"
    | return .error "an untyped arrow graph requires complete source and target fields"
  let .ok args := (json.getObjVal? "args").bind (·.getArr?)
    | return .error "an arrow descriptor has no defining fields"
  if let some entry := state.morphisms.find? (·.id.raw == tag) then
    return (← decodeValue trace category
      (← inferType (← instantiateFresh entry.declaration)) json).map (·.1)
  match tag, args with
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
  | "arrow", #[sourceJson, targetJson, mapJson] =>
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
      let .ok (iso, _) ← decodeFamily entry.declaration expected params (decodeValue trace category)
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
      let .ok (operation, _) ← decodeFamily entry.declaration expected params (decodeValue trace category)
        | return .error "the terminal operation does not decode at its full declaration"
      let operation ← StructuredResult.checkReconstruction operation
      let operationType ← inferType operation
      let zeroClass ← elabTermAndSynthesize (← `(Zero $(← exprToSyntax operationType))) none
      unless (← trySynthInstance zeroClass).toOption.isSome do
        return .error "the terminal operation has no canonical zero representation"
      let rebuilt ← elabTermAndSynthesize (← `(0)) (some operationType)
      unless ← withTransparency .all <| isDefEq rebuilt operation do
        return .error "the canonical zero data does not represent this registered operation"
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
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparison, rebuilt]
      let point ← elabTermAndSynthesize
        (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax composite) 0)) none
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
      let some (.ok point) ← ElementData.decode sourceValue sourceJson sourceType sourceAnswer
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

/-- Decode a prescribed lift only with its complete original operation context. -/
partial def decodeLiftedAt (_trace : Trace) (_category : NamedCategoryEntry) (_expected : Expr)
    (_context : LiftReplayContext) (_json : Json) :
    TermElabM (Except String (Expr × Option Expr)) := do
  return .error "computational lifted data is opaque; it cannot be decoded as a mathematical object or comparison"

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

/-- Evaluate the recorded term `e`, the value of `what`, to a value of a form, through the
admitted registrations. -/
-- Closed element data comes from the formal operation trace, never from carrier matching.
partial def elementExpression (trace : Trace) (e : Expr) : TermElabM Json := do
  let state ← registryState
  let some node ← trace.node? e
    | throwStratum .noImplementation m!"the closed element has no retained construction"
  match node with
  | .elementNumeral n _ _ =>
      return Json.mkObj [("ctor", "numeral"), ("args", Json.arr #[toJson n])]
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      unless entry.generator.isSome do throwError "the retained object has no generator"
      let (_, infos, _) ← forallMetaTelescope (← getConstInfo entry.declaration).type
      let objectArity := (infos.filter (·.isExplicit)).size
      let index ← (params.extract objectArity params.size).mapM (parameterData trace)
      return Json.mkObj [("ctor", "generator"), ("args", Json.arr index)]
  | .operationApply id params operands _ _ =>
      let some entry := state.operations.find? (·.id == id) | unreachable!
      unless operands.size == entry.arity do
        throwError "the retained operation expression changed its declared arity"
      let parameters ← params.mapM (parameterData trace)
      let arguments ← operands.mapM (elementExpression trace)
      return Json.mkObj [("ctor", "operationExpression"),
        ("args", Json.arr #[toJson id.raw, Json.arr parameters, Json.arr arguments])]
  | .morphismTransport _ _ _ receiver =>
      unless ← withTransparency .all <| isDefEq (← inferType e) (← inferType receiver) do
        throwStratum .noImplementation "this element transport requires its actual typed action data"
      unless ← withTransparency .all <| isDefEq e receiver do
        throwStratum .noImplementation "this nonidentity element transport requires its actual action data"
      elementExpression trace receiver
  | _ => throwStratum .noImplementation m!"the closed element is not structural arithmetic data"

/-- Validate computational object fields without proving construction laws. In particular,
subobject data carries its inclusion at the declared endpoints but is not promoted to a Lean
`Mono` instance or identified with the formal construction. -/
partial def validateComputationalObject (_trace : Trace) (_category : NamedCategoryEntry)
    (fixed : Expr) (json : Json) : TermElabM (Except String Unit) := do
  ComputationalData.validatePort fixed (← inferType fixed) json

mutual

partial def realizedParameters (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array Json × Array Wire) := do
  let mut data := #[]
  let mut dependencies := #[]
  for parameter in parameters do
    if (← trace.node? parameter).isSome then
      let wire ← realize h trace "the retained callable parameter" parameter
      data := data.push wire.json
      dependencies := dependencies.push wire
    else
      data := data.push (← parameterData trace parameter)
  return (data, dependencies)

partial def realize (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let e ← instantiateMVars e
  let closed := !e.hasMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars
  if closed then
    if let some wire := (← h.results.get)[e]? then return wire
  let wire ← realizeFresh h trace what e
  if closed then
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
        a method of one)"
  match node with
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
      let args ← params.mapM fun p => do
        if (← trace.node? p).isSome then
          return (← realize h trace s!"a parameter of {id.raw} in {what}" p).json
        match ← Codec.encode p with
        | .ok json => pure json
        | .error message =>
            throwStratum .noImplementation m!"a parameter of {id.raw} in {what} has no \
              registered realization or structural encoding: {message}"
      return { form := .object entry, payload := .ordinary (e) (Json.mkObj [("ctor", id.raw), ("args", Json.arr args)]) }
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
      let args ← params.mapM fun parameter => do
        if (← trace.node? parameter).isSome then
          return (← realize h trace s!"a parameter of {id.raw}" parameter).json
        match ← Codec.encode parameter with
        | .ok json => pure json
        | .error message => throwStratum .noImplementation m!"{id.raw}: {message}"
      let request : Wire := { form := .namedMorphism entry, payload := .ordinary (e) (Json.mkObj [("ctor", id.raw), ("args", Json.arr args)]) }
      if h.computationOnly && h.admitted.any (fun registration =>
          registration.registration.operation == id.raw &&
          registration.registration.input == request.formId) then
        let (answer, backend) ← send h id.raw request
        match ← ComputationalData.validatePort e (← inferType e) answer with
        | .error message => malformed backend id.raw answer message
        | .ok () => pure ()
        let data ← receiveComputationalData h backend id.raw answer true
        return { form := .namedMorphism entry, payload := .computed e data }
      return request
  | .namedInclusion id categoryId params source target =>
      let some entry := state.inclusions.find? (·.id == id)
        | throwError "the retained inclusion is not a published row"
      unless entry.category == categoryId do
        throwError "the retained inclusion changed its registered category"
      unless ← withTransparency .all <| isDefEq (← inferType e)
          (← mkAppM ``Quiver.Hom #[source, target]) do
        throwError "the retained inclusion changed its full endpoint types"
      let parameters ← params.mapM (parameterData trace)
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      return { form := .canonicalMorphism category, payload := (.ordinary e
        (Json.mkObj [("ctor", toJson id.raw), ("args", Json.arr parameters)])) }
  | .admittedPoint id categoryId params original originalCategory originalSource originalTarget =>
      let some entry := state.objects.find? (·.id == id)
        | throwError "the admitted point owner is not registered"
      unless entry.category == categoryId && entry.admission.isSome do
        throwError "the admitted point changed its published owner or category"
      let datum ← realize h trace "the original admitted computational point" original
      unless datum.form.category == originalCategory do
        throwError "the admitted point changed its original computational category"
      let parameters ← params.mapM (parameterData trace)
      let source ← realize h trace "the admitted point original domain" originalSource
      let target ← realize h trace "the admitted point original codomain" originalTarget
      let some (_, selected) := Language.homEnds? (← inferType e)
        | throwError "the admitted point lost its full formal endpoints"
      discard <| Semantic.recordNamedObject selected (some trace)
      let selected ← realize h trace "the admitted point selected target" selected
      let json := Json.mkObj [("ctor", "admittedPoint"), ("args", Json.arr #[
        toJson id.raw, Json.arr parameters, source.json, target.json, selected.json, datum.json])]
      let payload ← combinedPayload e json #[datum, source, target, selected]
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the admitted point category is not registered"
      return { form := .canonicalMorphism category, payload }
  | .namedCallable address categoryId params =>
      let some (_, declaredCategory) := state.callable? address
        | throwError "the callable is not published by its registered owner"
      unless declaredCategory == categoryId do
        throwError "the callable changed its declared category"
      let some form := state.form? address
        | throwError "the callable has no published request form"
      let args ← params.mapM (parameterData trace)
      return { form, payload := .ordinary e (Json.mkObj [("ctor", toJson address), ("args", Json.arr args)]) }
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
      let .object sourceEntry := original.form
        | throwStratum .noImplementation "the original point has no exact selected element structure"
      let some sourceCategory := state.categories.find? (·.id == sourceEntry.category) | unreachable!
      let sourceValue ← (Language.recognize state source sourceCategory).run {}
      let some targetCategory := state.categories.find? (·.id == selected.form.category)
        | throwError "the selected point view category is not registered"
      let applicationArgs := (route.zip applications).map fun (edge, application) =>
        (edge, actualApplicationArguments application)
      let targetValue : Language.Value := .object target targetCategory none none
        (some (#[sourceValue], sourceValue, route, #[], applicationArgs))
      let sourceCarrier ← (Language.carrierObject sourceValue).run {}
      let targetCarrier ← (Language.carrierObject targetValue).run {}
      let .object originalCarrier _ _ _ _ := sourceCarrier
        | throwError "the original point carrier is not an accepted object view"
      let .object selectedCarrier _ _ _ _ := targetCarrier
        | throwError "the selected point carrier is not an accepted object view"
      unless ← withTransparency .all <| isDefEq originalCarrier selectedCarrier do
        throwStratum .noImplementation "the declared forward structural view changes the carrier"
      let actualHom ← whnfR (← inferType e)
      unless ← withTransparency .all <| isDefEq actualHom.getAppArgs.back! selectedCarrier do
        throwError "the forward point has a different selected carrier endpoint"
      let expression ← elementExpression trace argument
      let sourceAnswer := Json.mkObj [("ctor", "element"),
        ("args", Json.arr #[original.json, expression])]
      let pointType ← whnfR (← inferType point.value)
      let originalDomain := pointType.getAppArgs[pointType.getAppNumArgs - 2]!
      let some (.ok decoded) ← ElementData.decode sourceValue original.json originalCarrier sourceAnswer
        | throwError "the original point data does not reconstruct at its full selected structure"
      let constant ← withLocalDeclD `point originalDomain fun argument => mkLambdaFVars #[argument] decoded
      let reconstructed ← mkAppM ``TypeCat.ofHom #[constant]
      unless ← withTransparency .all <| isDefEq reconstructed point.value do
        let some _ ← Codec.conditionProof (← mkEq reconstructed point.value)
          | throwError "the original generalized point is not this independently reconstructed constant"
      let homType ← whnfR (← inferType e)
      let domain := homType.getAppArgs[homType.getAppNumArgs - 2]!
      unless ← withTransparency .all <| isDefEq domain originalDomain do
        throwError "the forward point view changed its original generalized domain"
      discard <| Semantic.recordNamedObject domain (some trace)
      let domainWire ← realize h trace "the exact generalized point domain" domain
      let json := Json.mkObj [("ctor", "pointView"),
        ("args", Json.arr #[targetJson, sourceAnswer, domainWire.json])]
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      let value ← StructuredResult.checkReconstruction (← mkExpectedTypeHint reconstructed (← inferType e))
      return { form := .canonicalMorphism sets, payload := .ordinary (e) (json) }
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
      let json ← match ← StructuredResult.projectData row result.diagram result.answer index with
        | .ok data => pure data
        | .error message => throwStratum .noImplementation message
      return { form := .canonicalMorphism category, payload := forwardPayload wire e json }
  | .arrowProjection receiver =>
      let wire ← realize h trace "the stored arrow object" receiver
      let some category := state.categories.find? (·.id == wire.form.category)
        | throwError "the stored arrow category is not registered"
      let .construct constructor #[.category base] := category.expression
        | throwStratum .invalid "the receiver is not a registered arrow construction"
      unless (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        throwStratum .invalid "the receiver uses a different registered construction"
      let baseCategory ← Semantic.namedCategoryFor state base
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
      return { form := .canonicalMorphism baseCategory, payload := forwardPayload wire e json }
  | .morphismIdentity categoryId object =>
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let endpoint ← realize h trace "the identity endpoint" object
      let value ← mkAppM ``CategoryTheory.CategoryStruct.id #[endpoint.value]
      unless ← isDefEq (← inferType value) (← inferType e) do
        throwError "the identity endpoint changed its fixed type"
      return { form := .canonicalMorphism category, payload := .ordinary (e) (Json.mkObj [("ctor", "identity"),
          ("args", Json.arr #[endpoint.json, endpoint.json])]) }
  | .productMediator categoryId presentation domain left right =>
      let some category := state.categories.find? (·.id == categoryId)
        | throwError "the formal product mediator category is not registered"
      unless ← withTransparency .all <| isDefEq domain (← closedElementDomain state) do
        throwStratum .noImplementation "this product mediator requires generalized pointwise computational data"
      let first ← realize h trace "the first product point" left
      let second ← realize h trace "the second product point" right
      let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
      let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
      unless ← withTransparency .all <| isDefEq (← inferType e)
          (← mkAppM ``Quiver.Hom #[domain, apex]) do
        throwError "the product point changed its independently fixed formal type"
      let payload ← combinedPayload e (Json.arr #[first.json, second.json]) #[first, second]
      return { form := .canonicalMorphism category, payload }
  | .morphismComposition categoryId first second source middle target =>
      let some category := state.categories.find? (·.id == categoryId) | unreachable!
      let callable ← match ← (trace.node? second : IO _) with
        | some (.namedMorphism id params) => pure (some (id.raw, params))
        | some (.namedCallable address _ params) => pure (some (address, params))
        | _ => pure none
      if let some (address, params) := callable then
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
        let domainWire ← realize h trace "the generalized point domain" source
        let sourceWire ← realize h trace "the applied operation source" middle
        let targetWire ← realize h trace "the applied operation target" target
        let arrow := Json.mkObj [("ctor", toJson address), ("args", Json.arr parameters)]
        let invocation : Backend.PointInvocation := {
          operation := address, parameters, arrow,
          domain := domainWire.json, source := sourceWire.json, target := targetWire.json,
          argument := argument.json }
        let requestData := invocation.encode
        let payload ← combinedPayload e requestData (#[argument, domainWire, sourceWire, targetWire] ++ parameterWires)
        let request : Wire := { form := sourceWire.form, payload }
        let (answer, backend) ← send h address request
        let data ← receiveComputationalData h backend address answer
        return { form := .canonicalMorphism category, payload := .computed e data }
      let a ← realize h trace "the first composed map" first
      let b ← realize h trace "the second composed map" second
      unless ← isDefEq (← inferType a.value) (← mkAppM ``Quiver.Hom #[source, middle]) do
        throwError "the first computed arrow changed its fixed endpoints"
      unless ← isDefEq (← inferType b.value) (← mkAppM ``Quiver.Hom #[middle, target]) do
        throwError "the second computed arrow changed its fixed endpoints"
      let value ← mkAppM ``CategoryTheory.CategoryStruct.comp #[a.value, b.value]
      let value ← StructuredResult.checkReconstruction value
      let json := Json.mkObj [("ctor", "compose"), ("args", Json.arr #[a.json, b.json])]
      let payload ← combinedPayload e json #[a, b]
      return { form := .canonicalMorphism category, payload }
  | .presentation id params inverse =>
      let some entry := state.presentations.find? (·.id == id) | unreachable!
      let args ← params.mapM fun parameter => do
        if (← trace.node? parameter).isSome then
          return (← realize h trace "a presentation parameter" parameter).json
        match ← Codec.encode parameter with
        | .ok json => pure json
        | .error message => throwStratum .noImplementation m!"{id.raw}: {message}"
      let some source := state.objects.find? (·.id == entry.source) | unreachable!
      return { form := .presentation entry source.category, payload := .ordinary (e) (Json.mkObj [("ctor", "presentation"), ("args", Json.arr #[
          toJson id.raw, Json.arr args, toJson inverse])]) }
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let args ← params.mapM fun parameter => do
        if (← trace.node? parameter).isSome then
          return (← realize h trace "a generator parameter" parameter).json
        match ← Codec.encode parameter with
        | .ok json => pure json
        | .error message => throwStratum .noImplementation m!"{id.raw}: {message}"
      return { form := .generator entry, payload := .ordinary (e) (Json.mkObj [("ctor", "generator"), ("args", Json.arr #[toJson id.raw, Json.arr args])]) }
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
      let operationType ← inferType operation
      let zeroClass ← elabTermAndSynthesize (← `(Zero $(← exprToSyntax operationType))) none
      unless (← trySynthInstance zeroClass).toOption.isSome do
        throwStratum .noImplementation m!"{id.raw}: the nullary map has no canonical zero data"
      let rebuilt ← elabTermAndSynthesize (← `(0)) (some operationType)
      unless ← withTransparency .all <| isDefEq rebuilt operation do
        throwStratum .noImplementation m!"{id.raw}: the nullary map requires another canonical data representation"
      let comparisonWire ← realize h trace "the accepted singleton comparison" comparison
      unless ← withTransparency .all <| isDefEq comparisonWire.value comparison do
        throwError "the terminal comparison changed its accepted map"
      let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[comparisonWire.value, rebuilt]
      let singleton ← closedElementDomain state
      let compositeType ← whnfR (← inferType composite)
      let compositeArgs := compositeType.getAppArgs
      unless compositeArgs.size >= 2 &&
          (← withTransparency .all <| isDefEq compositeArgs[compositeArgs.size - 2]! singleton) do
        throwError "the accepted terminal comparison has a different singleton source"
      let point ← elabTermAndSynthesize
        (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax composite) 0)) none
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
      let parameterData ← params.mapM fun parameter => do
        if (← trace.node? parameter).isSome then
          return (← realize h trace "a terminal operation parameter" parameter).json
        match ← Codec.encode parameter with
        | .ok data => pure data
        | .error message => throwStratum .noImplementation m!"{id.raw}: {message}"
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      return { form := .canonicalMorphism sets, payload := .ordinary (e) (Json.mkObj [("ctor", "operationPoint"), ("args", Json.arr #[
          toJson id.raw, Json.arr parameterData, comparisonWire.json, domainWire.json, selectedWire.json])]) }
  | .elementNumeral _ target selected | .operationApply _ _ _ target selected =>
      discard <| Semantic.recordNamedObject selected (some trace)
      let selectedWire ← realize h trace "the selected element structure" selected
      let .object entry := selectedWire.form
        | throwStratum .noImplementation m!"the selected element structure has no exact object descriptor"
      let some category := state.categories.find? (·.id == entry.category) | unreachable!
      let expression ← elementExpression trace e
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
      return { form := .element entry, payload := .ordinary (e) (answer) }
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
      let args ← params.mapM fun parameter => do
        if (← trace.node? parameter).isSome then
          return (← realize h trace "a presentation application parameter" parameter).json
        match ← Codec.encode parameter with
        | .ok json => pure json
        | .error message => throwStratum .noImplementation m!"{id.raw}: {message}"
      let request := { sourceWire with payload := (dataPayload sourceWire.value
        (Json.mkObj [("ctor", "presentationApply"),
          ("args", Json.arr #[Json.arr args, toJson inverse, sourceWire.json, targetWire.json, argumentWire.json])])
        (← sharedOwner sourceWire argumentWire)) }
      let (answer, backend) ← send h id.raw request
      let .object targetEntry := targetWire.form
        | throwError "the selected presentation target has no exact registered object form"
      let some category := state.categories.find? (·.id == targetEntry.category) | unreachable!
      let selected ← (Language.recognize state target category).run {}
      let expectedPoint ← elabTermAndSynthesize
        (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $(← exprToSyntax e) 0)) none
      let pointType ← inferType expectedPoint
      match ← ComputationalData.validatePort expectedPoint pointType answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw answer true
      return { form := .element targetEntry, payload := .computed e data }

  | .morphismTransport sourceCategory targetCategory route receiver =>
      let input ← realize h trace "the map before structural transport" receiver
      unless input.form.category == sourceCategory do
        throwError "the structural map has the wrong recorded source category"
      let mut value := input.value
      let mut json := input.json
      for step in route do
        let U ← Semantic.edgeFunctor state step
        value ← Semantic.mapOf U value
        json := Json.mkObj [("ctor", "map"), ("args", Json.arr #[
          ← edgeDescriptor trace step U, json])]
      let requested ← Semantic.mapOf (← Semantic.routeFunctor state route) receiver
      unless ← isDefEq requested e do
        throwError "the recorded map transport differs from the semantic request"
      let some form := state.graphLiterals.find? (·.category == targetCategory)
        | throwStratum .noImplementation m!"the map target category has no registered graph form"
      return { form := .graph form, payload := forwardPayload input e json }
  | .functor id params receiver =>
      let some entry := state.functor? id | unreachable!
      let input ← realize h trace s!"the source of {id.raw} in {what}" receiver
      let mut owner := input.owner?
      let mut args : Array Json := #[]
      for parameter in params do
        if (← trace.node? parameter).isSome then
          let parameterWire ← realize h trace s!"a parameter of {id.raw}" parameter
          owner ← mergeOwners owner parameterWire.owner?
          args := args.push parameterWire.json
        else
          match ← Codec.encode parameter with
          | .ok json => args := args.push json
          | .error message => throwStratum .noImplementation m!"{id.raw}: {message}"
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
      let request := { input with payload := dataPayload input.value (Json.mkObj [("ctor", id.raw),
        ("args", Json.arr args), ("receiver", input.json)]) owner }
      let (answer, backend) ← send h id.raw request
      let target ← Semantic.namedCategoryFor state entry.target
      match ← validateComputationalObject trace target e answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw answer true
      return { form := imageForm state (.functor id) target, payload := .computed e data }
  | .retainedRoute _ targetCategory route applications receiver =>
      let input ← realize h trace "the retained structural source" receiver
      let result ← transportImage trace input route (some applications)
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
      let (answer, backend) ← send h operation request
      let data ← receiveComputationalData h backend operation answer
      let some category := state.categories.find? (·.id == entry.category) | unreachable!
      return { form := .canonicalMorphism category, payload := .computed e data }
  | .arrow category morphism source target =>
      let some entry := state.categories.find? (·.id == category)
        | throwError "the recorded arrow category is not registered"
      let source ← realize h trace s!"the source of {what}" source
      let target ← realize h trace s!"the target of {what}" target
      let morphism ← realize h trace s!"the defining map of {what}" morphism
      let json := Json.mkObj [("ctor", "arrow"),
        ("args", Json.arr #[source.json, target.json, morphism.json])]
      return {
        form := .arrow entry
        payload := (← combinedPayload e json #[source, target, morphism]) }
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
              return { form := .canonicalMorphism category, payload := .ordinary (a) (Json.mkObj [("ctor", toJson tag),
                  ("args", Json.arr #[sourceWire.json, targetWire.json])]) }
        realize h trace s!"the diagram of {id.raw} in {what}" a
      let sourceDiagram ← mkAppM standard (wires.map (·.value))
      let sourceDiagramJson := Json.mkObj [("ctor", Codec.label standard),
        ("args", Json.arr (wires.map (·.json)))]
      let (sent, wires) ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
        | none => pure (sourceDiagram, wires)
        | some lift => do
          let U ← Semantic.edgeFunctor state lift.edge
          let mapped ← wires.mapM fun wire => do
            match wire.form with
            | .object _ => transport trace wire #[lift.edge]
            | .graph _ =>
              let value ← Semantic.mapOf U wire.value
              let some form := state.graphLiterals.find? (·.category == category.id)
                | throwStratum .noImplementation "the selected graph action has no declared target data form"
              let json := Json.mkObj [("ctor", "map"), ("args", Json.arr #[
                ← edgeDescriptor trace lift.edge U, wire.json])]
              pure { wire with form := .graph form, payload := forwardPayload wire value json }
            | _ => throwStratum .noImplementation m!"the diagram data has no accepted presentation along {lift.edge.label}"
          pure (← mkAppM standard (mapped.map (·.value)), mapped)
      let diagramJson := Json.mkObj [("ctor", Codec.label standard),
        ("args", Json.arr (wires.map (·.json)))]
      let input : Wire := {
        form := .diagrams category
        payload := (← combinedPayload sent diagramJson wires) }
      let formalLowerPresentation ← Semantic.limitPresentation row sent
      let plan ← match ← StructuredResult.dataPlan row sent formalLowerPresentation with
        | .error message => throwStratum .noImplementation m!"the formal construction has no computational data schema: {message}"
        | .ok plan => pure plan
      let inputRoles ← wires.mapM fun wire => do
        let ends := Language.homEnds? (← inferType wire.value)
        let endpointData ← match ends with
          | none => pure (none, none)
          | some (source, target) => do
            for endpoint in #[source, target] do
              if (← trace.node? endpoint).isNone then
                discard <| Semantic.recordNamedObject endpoint (some trace)
            let source ← realize h trace "the construction input map's retained source" source
            let target ← realize h trace "the construction input map's retained target" target
            pure (some source.json, some target.json)
        pure (wire.json, endpointData.1, endpointData.2)
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
      let (answer, backend) ← send h id.raw input
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
      let completed ← match ← StructuredResult.complete row formalDiagram formalDiagramJson
          packet formalPresentation (fun answer =>
            StructuredResult.validatePlannedData plan answer
              (fun port seen json => ComputationalData.validatePlannedPort plan port seen json
                externalDescriptor ComputationalData.endpointKeys)) with
        | .ok complete => pure complete
        | .error message => malformed backend id.raw answer message
      let form ← match lift?.bind (fun id => state.lifts.find? (·.id == id)) with
        | none => pure (.limitApex row)
        | some lift => do
          let some edge := state.structuralEdge? lift.edge | unreachable!
          let some source := state.categories.find? (·.expression.syntacticEq edge.source)
            | throwError "the creation lift has no registered source schema"
          pure (.createdApex row source.id)
      let scope ← computationalScope h backend answer
      return { form := form, payload := .construction completed scope }
  | .method id route receiver =>
      let input ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let input ← transport trace input route
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor
        | throwError "{id.raw} has no registered functor"
      let some target := state.category? functor.target
        | throwError "the result category of {id.raw} is not registered"
      let F ← registeredFunctorInstance functor
      let acceptedInput ← methodArgument method input.value
      let expected ← Semantic.objOf F acceptedInput
      let (json, backend) ← send h id.raw input
      match ← validateComputationalObject trace target expected json with
      | .error message => malformed backend id.raw json message
      | .ok () => pure ()
      let data ← receiveComputationalData h backend id.raw json true
      return { form := .functorImage functor target.id, payload := .computed e data }
  | .methodWithLifts id route lifts receiver =>
      let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let input ← transport trace original route
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor | unreachable!
      let some target := state.category? functor.target | unreachable!
      let F ← registeredFunctorInstance functor
      let acceptedInput ← methodArgument method input.value
      let expected ← Semantic.objOf F acceptedInput
      let (retainedBase, _) ← Semantic.applyRegisteredFunctor functor acceptedInput #[] (some trace)
      unless ← withTransparency .all <| isDefEq retainedBase expected do
        throwError "the prescribed base action changed its full retained method input"
      let (answer, backend) ← send h id.raw input
      match ← validateComputationalObject trace target expected answer with
      | .error message => malformed backend id.raw answer message
      | .ok () => pure ()
      let liftedJson := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
        answer, original.json, toJson (lifts.map (·.raw))])]
      let some sourceCategory := state.categories.find? (·.id == original.form.category)
        | throwError "the prescribed method has no independently retained source schema"
      let .construct arrowConstructor #[source] := sourceCategory.expression
        | throwError "the prescribed method receiver is not a complete Arrow"
      unless (state.constructors.find? (·.id == arrowConstructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        throwError "the prescribed method receiver uses a different constructor"
      let some constructor := state.constructors.find?
          (·.semantics == `CasCatalogue.Constructors.subobjects)
        | throwError "the prescribed method has no registered subobjects schema"
      let some category := state.categories.find?
          (·.expression.syntacticEq (.construct constructor.id #[source]))
        | throwError "the prescribed lift target has no registered full schema"
      let some checked ← LiftedSubobjectData.decode (← inferType e) sourceCategory
          receiver lifts retainedBase liftedJson
          (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
          (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
        | throwError "the prescribed method has no complete computational lift packet"
      let packet ← match checked with
        | .ok packet => pure packet
        | .error message => malformed backend id.raw liftedJson message
      unless ← withTransparency .all <| isDefEq packet.formalResult e do
        throwError "the independent prescribed lift changed its formal result"
      let scope ← computationalScope h backend answer
      let owner := match scope with
        | .portable => original.owner?
        | .owned backend session => some (backend, session)
      let owner ← mergeOwners original.owner? owner
      return { form := .subobject category, payload := match owner with
        | none => .computed e (.inline packet.data)
        | some (backend, session) => .computed e (.owned backend session packet.data) }
  | .property id _ _ =>
      throwError "the decision {id.raw} is not a value"

end

/-- Evaluate the recorded decision `p` to a three-valued answer (`Option Bool`), through the
admitted registration of its property on the form of its receiver, sent along the resolved
route. -/
def realizeDecision (h : Harness) (trace : Trace) (what : String) (p : Expr) :
    TermElabM (Expr × Json) := do
  let p ← instantiateMVars p
  let some (.property id route receiver) ← (trace.node? p : IO _)
    | throwStratum .noImplementation m!"nothing decides {what}: it is not a registered \
        property of a value the realized reading evaluates"
  let input ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
  let input ← transport trace input route
  call h id.raw input (mkApp (mkConst ``Option [0]) (mkConst ``Bool))

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
the one sanctioned runner (`Language.runProcedure`, LC-18), and the goal that remains is proved
by `of_decide_eq_true (Eq.refl true)` (`mkDecideProof`, on `Decidable` instances alone); the
proof so formed is checked by Lean's kernel, synchronously, within `decideBudget`
(`kernelAccepts`). With no evaluation, it is the proof by decision alone. `false` when an
evaluation fails or leaves several goals, when the remainder has no `Decidable` instance, or when
the kernel does not accept the proof within the budget. -/
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
    | [residue] => residue.withContext do residue.assign (← mkDecideProof (← residue.getDecl).type)
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

/-- Observe actual computational points through the published equality characteristic map.
The truth datum is never elaborated as a proposition or used as proof evidence. -/
def observeComputedPoints (h : Harness) (trace : Trace) (first second : Wire)
    (formal : Expr) : TermElabM Bool := do
  let state ← registryState
  let pointType ← inferType formal
  let some (domain, target) := Language.homEnds? pointType
    | throwStratum .noImplementation "the computational observation has no retained categorical point endpoints"
  unless ← withTransparency .all <| isDefEq domain (← closedElementDomain state) do
    throwStratum .noImplementation "this computational map requires a pointwise observation implementation"
  if ← ComputationalData.plainType target then
    let observe (wire : Wire) : TermElabM (Option Expr) := do
      match wire.payload with
      | .computed _ (.inline data) =>
        match ← Codec.decode target data with
        | .ok value => return some value
        | .error _ => return none
      | .ordinary value _ =>
        let action ← Language.functionOf value
        let point ← elabTerm (← `( (0 : Fin 1) )) none
        let value ← withTransparency .all <| whnf (mkApp action point)
        unless ← withTransparency .all <| isDefEq (← inferType value) target do
          return none
        return some value
      | _ => return none
    if let some a ← observe first then
      if let some b ← observe second then
        if let some answer ← Decide.decideProp (← mkEq a b) then return answer
  let some equality := state.morphisms.find? (·.id.raw == "mor.sets.equality")
    | throwStratum .noImplementation "the formal API has no released equality characteristic map"
  let arrow ← withTransparency .all <| mkAppM equality.declaration #[target]
  let some (source, truth) := Language.homEnds? (← inferType arrow)
    | throwError "the released equality map has no complete declared endpoints"
  for object in #[domain, target, truth] do
    discard <| Semantic.recordNamedObject object (some trace)
  let domainWire ← realize h trace "the computational equality's point domain" domain
  let valueWire ← realize h trace "the computational equality's selected carrier" target
  let sourceJson := Json.mkObj [("ctor", "objectProduct"),
    ("args", Json.arr #[valueWire.json, valueWire.json])]
  let truthWire ← realize h trace "the computational equality's truth-value carrier" truth
  let parameters := #[valueWire.json]
  let invocation : Backend.PointInvocation := {
    operation := equality.id.raw, parameters,
    arrow := Json.mkObj [("ctor", toJson equality.id.raw), ("args", Json.arr parameters)],
    domain := domainWire.json, source := sourceJson, target := truthWire.json,
    argument := Json.arr #[first.json, second.json] }
  let payload := dataPayload arrow invocation.encode (← sharedOwner first second)
  let request : Wire := { form := .namedMorphism equality, payload }
  let (answer, backend) ← send h equality.id.raw request
  match Backend.ComputationalValue.decode answer with
  | .ok (.inline (.bool truth)) => return truth
  | .ok _ => malformed backend equality.id.raw answer "the declared truth observation requires inline Boolean data"
  | .error message => malformed backend equality.id.raw answer message

def realizeClaim (h : Harness) (trace : Trace) (claim : Claim) : TermElabM ExecutionOutcome := do
  match claim with
  | .binding => return .internal "a binding entered execution"
  | .implemented value =>
      -- A decision is realized as one; anything else as a value.
      if ← isProp value then discard <| realizeDecision h trace "the decision" value
      else discard <| realize h trace "the value" value
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
      let a ← realize h trace left f
      let b ← realize h trace right g
      unless (← isDefEq (← inferType a.value) (← inferType f)) &&
          (← isDefEq (← inferType b.value) (← inferType g)) do
        throwStratum .malformed m!"the computed arrows changed the fixed comparison endpoints"
      if (match a.payload with | .computed .. => true | _ => false) ||
          (match b.payload with | .computed .. => true | _ => false) then
        return if ← observeComputedPoints h trace a b f then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      -- The retained formal maps fix the question; only the actual computational answer
      -- data is compared here. Using Wire.value would hide a well-formed wrong answer.
      let observe (wire : Wire) (formal : Expr) : TermElabM Expr := do
        let state ← registryState
        let some category := state.categories.find? (·.id == wire.form.category)
          | throwStratum .malformed "the computed map has no declared category"
        let .ok (actual, _) ← decodeValue trace category (← inferType formal) wire.json
          | throwStratum .noImplementation "the computational map has no independent observation decoder"
        return actual
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

/-- Exact structural serialization with shared subterms. Hash maps are only indexes:
equality is checked on expressions or complete node encodings, never on a digest. -/
structure TermTable where
  terms : IO.Ref (Std.HashMap Expr Nat)
  nodes : IO.Ref (Array Json)
  canonicalNodes : IO.Ref (Std.HashMap String Nat)

def TermTable.new : IO TermTable := do
  return { terms := ← IO.mkRef {}, nodes := ← IO.mkRef #[], canonicalNodes := ← IO.mkRef {} }

/-- Universe syntax is serialized without Lean's cached hash fields. -/
partial def encodeLevel : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ level => Json.arr #[toJson "succ", encodeLevel level]
  | .max left right => Json.arr #[toJson "max", encodeLevel left, encodeLevel right]
  | .imax left right => Json.arr #[toJson "imax", encodeLevel left, encodeLevel right]
  | .param name => Json.arr #[toJson "param", toJson (reprStr name)]
  | .mvar id => Json.arr #[toJson "unresolved", toJson (reprStr id)]

/-- Intern complete typed node descriptions. Context-sensitive expressions are never cached
inside the binder traversal; only their canonical node descriptions are shared. -/
def TermTable.intern (table : TermTable) (node : Json) : TermElabM Nat := do
  let description := node.compress
  if let some index := (← table.canonicalNodes.get)[description]? then return index
  let index := (← table.nodes.get).size
  table.nodes.modify (·.push node)
  table.canonicalNodes.modify (·.insert description index)
  return index

partial def TermTable.encode (table : TermTable) (term : Expr) : TermElabM Nat := do
  if let some index := (← table.terms.get)[term]? then return index
  let index ← QuestionIdentity.encode table.intern term
  table.terms.modify (·.insert term index)
  return index

def TermTable.finish (table : TermTable) (roots : Json) : IO String := do
  return (Json.mkObj [("roots", roots), ("terms", Json.arr (← table.nodes.get))]).compress

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

def termIdentity (term : Expr) : TermElabM String := do
  let table ← TermTable.new
  let root ← table.encode term
  table.finish (toJson root)

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

/-- Prepare the question against the current mathematical environment. A reader which has
cannot produce an interpretation record until its typed terms are complete. -/
def interpret (scope : Scope) (stx : Syntax) : TermElabM TypedQuestion := do
  let trace ← (Trace.new : IO _)
  let claim ← (Language.claim scope stx).run { trace := some trace }
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
  let nodes ← (← trace.get).toArray.mapM fun (term, node) => do
    let term ← instantiateMVars term
    let node : Node ← match node with
      | .object id parameters => pure (.object id (← parameters.mapM instantiateMVars))
      | .parameterTransport source sourceCategory targetCategory route receiver =>
          pure (.parameterTransport source sourceCategory targetCategory route (← instantiateMVars receiver))
      | .structureTransport sourceCategory targetCategory route receiver =>
          pure (.structureTransport sourceCategory targetCategory route (← instantiateMVars receiver))
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
      | .presentation id params inverse =>
          pure (.presentation id (← params.mapM instantiateMVars) inverse)
      | .generator id params => pure (.generator id (← params.mapM instantiateMVars))
      | .elementNumeral value target selected =>
          pure (.elementNumeral value (← instantiateMVars target) (← instantiateMVars selected))
      | .productMediator category presentation domain left right =>
          pure (.productMediator category (← instantiateMVars presentation)
            (← instantiateMVars domain) (← instantiateMVars left) (← instantiateMVars right))
      | .morphismComposition category first second source middle target =>
          pure (.morphismComposition category (← instantiateMVars first)
            (← instantiateMVars second) (← instantiateMVars source)
            (← instantiateMVars middle) (← instantiateMVars target))
      | .morphismIdentity category object =>
          pure (.morphismIdentity category (← instantiateMVars object))
      | .arrowProjection receiver =>
          pure (.arrowProjection (← instantiateMVars receiver))
      | .limitProjection receiver index =>
          pure (.limitProjection (← instantiateMVars receiver) (← instantiateMVars index))
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
  -- Sorting complete canonical term encodings makes the snapshot independent of hash-map
  -- layout. Shared term references then keep the complete record compact.
  let ordered ← nodes.mapM fun (term, node) => do
    return (← termIdentity term, term, node)
  let ordered := ordered.qsort fun a b => a.1 < b.1
  let table ← TermTable.new
  let operations ← ordered.mapM fun (_, term, node) => do
    let root ← table.encode term
    let operation ← match node with
      | .object id parameters =>
          pure (Json.arr #[toJson "object", toJson id.raw, toJson (← parameters.mapM table.encode)])
      | .parameterTransport source sourceCategory targetCategory route receiver =>
          pure (Json.arr #[toJson "parameterTransport", toJson source.raw,
            toJson sourceCategory.raw, toJson targetCategory.raw, toJson (route.map reprStr),
            toJson (← table.encode receiver)])
      | .structureTransport sourceCategory targetCategory route receiver =>
          pure (Json.arr #[toJson "structureTransport", toJson sourceCategory.raw,
            toJson targetCategory.raw, toJson (route.map reprStr), toJson (← table.encode receiver)])
      | .parameterEquivalence expected representative sources => do
          let keyed ← sources.mapM fun source => do
            let parameters ← source.params.mapM termIdentity
            return (source.source.raw ++ reprStr source.route ++ reprStr parameters, source)
          let sources := (keyed.qsort fun a b => a.1 < b.1).map (·.2)
          let data ← sources.mapM fun source => do
            return Json.arr #[toJson source.source.raw, toJson source.sourceCategory.raw,
              toJson source.targetCategory.raw, toJson (← source.params.mapM table.encode),
              toJson (source.route.map reprStr), toJson (← source.applications.mapM table.encode),
              toJson (source.carrierRoute.map reprStr),
              toJson (source.identifications.map Name.toString), toJson (← table.encode source.object),
              toJson (← table.encode source.image), toJson (← table.encode source.identity)]
          pure (Json.arr #[toJson "parameterEquivalence", toJson (← table.encode expected),
            toJson (← table.encode representative), Json.arr data])
      | .retainedRoute source target route applications receiver =>
          pure (Json.arr #[toJson "retainedRoute", toJson source.raw, toJson target.raw,
            toJson (route.map reprStr), toJson (← applications.mapM table.encode),
            toJson (← table.encode receiver)])
      | .namedMorphism id params =>
          pure (Json.arr #[toJson "namedMorphism", toJson id.raw, toJson (← params.mapM table.encode)])
      | .admittedPoint id category params original originalCategory source target =>
          pure (Json.arr #[toJson "admittedPoint", toJson id.raw, toJson category.raw,
            toJson (← params.mapM table.encode), toJson (← table.encode original),
            toJson originalCategory.raw, toJson (← table.encode source), toJson (← table.encode target)])
      | .namedInclusion id category params source target =>
          pure (Json.arr #[toJson "namedInclusion", toJson id.raw, toJson category.raw,
            toJson (← params.mapM table.encode), toJson (← table.encode source),
            toJson (← table.encode target)])
      | .callableRecipe category domain target body =>
          pure (Json.arr #[toJson "callableRecipe", toJson category.raw,
            toJson (← table.encode domain), toJson (← table.encode target),
            toJson (← table.encode body)])
      | .namedCallable address category params =>
          pure (Json.arr #[toJson "namedCallable", toJson address, toJson category.raw,
            toJson (← params.mapM table.encode)])
      | .presentation id params inverse =>
          pure (Json.arr #[toJson "presentation", toJson id.raw,
            toJson (← params.mapM table.encode), toJson inverse])
      | .generator id params =>
          pure (Json.arr #[toJson "generator", toJson id.raw, toJson (← params.mapM table.encode)])
      | .elementNumeral value target selected =>
          pure (Json.arr #[toJson "elementNumeral", toJson value,
            toJson (← table.encode target), toJson (← table.encode selected)])
      | .productMediator category presentation domain left right =>
          pure (Json.arr #[toJson "productMediator", toJson category.raw,
            toJson (← table.encode presentation), toJson (← table.encode domain),
            toJson (← table.encode left), toJson (← table.encode right)])
      | .morphismComposition category first second source middle target =>
          pure (Json.arr #[toJson "morphismComposition", toJson category.raw,
            toJson (← table.encode first), toJson (← table.encode second),
            toJson (← table.encode source), toJson (← table.encode middle),
            toJson (← table.encode target)])
      | .morphismIdentity category object =>
          pure (Json.arr #[toJson "morphismIdentity", toJson category.raw,
            toJson (← table.encode object)])
      | .arrowProjection receiver =>
          pure (Json.arr #[toJson "arrowProjection", toJson (← table.encode receiver)])
      | .limitProjection receiver index =>
          pure (Json.arr #[toJson "limitProjection", toJson (← table.encode receiver),
            toJson (← table.encode index)])
      | .pointView source target route applications argument =>
          pure (Json.arr #[toJson "pointView", toJson (← table.encode source),
            toJson (← table.encode target), toJson (route.map reprStr),
            toJson (← applications.mapM table.encode), toJson (← table.encode argument)])
      | .operationPoint id params comparison operation target selected =>
          pure (Json.arr #[toJson "operationPoint", toJson id.raw,
            toJson (← params.mapM table.encode), toJson (← table.encode comparison),
            toJson (← table.encode operation), toJson (← table.encode target),
            toJson (← table.encode selected)])
      | .operationApply id params operands target selected =>
          pure (Json.arr #[toJson "operationApply", toJson id.raw,
            toJson (← params.mapM table.encode), toJson (← operands.mapM table.encode),
            toJson (← table.encode target), toJson (← table.encode selected)])
      | .presentationApply id params inverse source target argument =>
          pure (Json.arr #[toJson "presentationApply", toJson id.raw,
            toJson (← params.mapM table.encode), toJson inverse, toJson (← table.encode source),
            toJson (← table.encode target), toJson (← table.encode argument)])
      | .morphismTransport sourceCategory targetCategory route receiver =>
          pure (Json.arr #[toJson "morphismTransport", toJson sourceCategory.raw,
            toJson targetCategory.raw, toJson (route.map reprStr), toJson (← table.encode receiver)])
      | .functor id params receiver =>
          pure (Json.arr #[toJson "functor", toJson id.raw,
            toJson (← params.mapM table.encode), toJson (← table.encode receiver)])
      | .binder id params domain body admitted =>
          pure (Json.arr #[toJson "binder", toJson id.raw, toJson (← params.mapM table.encode),
            toJson (← table.encode domain), toJson (← table.encode body),
            toJson (← table.encode admitted)])
      | .arrow category morphism source target =>
          pure (Json.arr #[toJson "arrow", toJson category.raw,
            toJson (← table.encode morphism), toJson (← table.encode source),
            toJson (← table.encode target)])
      | .literal form literal =>
          pure (Json.arr #[toJson "literal", toJson form.raw, toJson (← table.encode literal)])
      | .method id route receiver =>
          pure (Json.arr #[toJson "method", toJson id.raw, toJson (route.map reprStr),
            toJson (← table.encode receiver)])
      | .methodWithLifts id route lifts receiver =>
          pure (Json.arr #[toJson "methodWithLifts", toJson id.raw, toJson (route.map reprStr),
            toJson (lifts.map (·.raw)), toJson (← table.encode receiver)])
      | .property id route receiver =>
          pure (Json.arr #[toJson "property", toJson id.raw, toJson (route.map reprStr),
            toJson (← table.encode receiver)])
      | .limit id diagram lift =>
          pure (Json.arr #[toJson "limit", toJson id.raw, toJson (← table.encode diagram),
            toJson (lift.map (·.raw))])
    return Json.arr #[toJson root, operation]
  let tree ← table.finish (Json.arr operations)
  return { claim := claim
           trace := Std.HashMap.ofArray nodes
           mathematicalRevision := mathematicalRevision
           identity := (s!"{mathematicalRevision}:{identity}:operations:{tree}", shown) }

/-- Execute exactly the previously interpreted request. -/
def evaluate (h : Harness) (question : TypedQuestion) : TermElabM ExecutionOutcome := do
  let trace ← IO.mkRef question.trace
  unless h.computationOnly do
    if let some outcome ← discharge question.claim (some trace) then return outcome
  realizeClaim h trace question.claim

/-- Runtime failures cannot assert mathematical invalidity or semantic ambiguity. Those
judgements belong to interpretation; an unexpected semantic exception during evaluation is
an interpreter defect. -/
def executionFailure (e : Exception) : TermElabM ExecutionOutcome := do
  let reason ← e.toMessageData.toString
  return match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization => .gap reason
    | some .unavailable => .unavailable reason
    | some .malformed => .malformed reason
    | some .invalid | some .semanticAmbiguity | none => .internal reason

/-- Interpret before execution, retaining the same request through every later outcome.
Bindings are read without being counted as assertions. Incomplete interpretations fail visibly;
no operand list or truth value stands in for their question. -/
def runAsking (h : Harness) (scope : Scope) (stx : Syntax) :
    TermElabM (Outcome × Scope × Option (String × String)) := do
  if let some (x, t) ← letBinding? stx then
    let bind : TermElabM (Outcome × Scope × Option (String × String)) := do
      discard <| (Language.claim scope stx).run {}
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
