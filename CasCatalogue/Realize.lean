/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language
public import CasCatalogue.Admission
public import CasCatalogue.Codec
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
   statement is false mathematics and is invalid. Nothing is decided by evaluation outside the
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
structure Wire where
  form : Form
  value : Expr
  json : Json
  /-- For the apex of a limit computed by a registration: the cone (cocone) reconstructed from
  the answer, whose legs a later operation reads (CC-DECODE). -/
  universal : Option Expr := none

def Wire.formId (w : Wire) : String := w.form.id

/-- The admitted registrations of a run, their backend programs, and the live connections. -/
structure Harness where
  admitted : Array Admitted := #[]
  /-- The registrations not admitted, each with its reason. -/
  rejected : Array String := #[]
  backends : Array BackendProgram := #[]
  /-- The directory the programs run in: the manifest's. -/
  root : System.FilePath := "."
  connections : IO.Ref (Std.HashMap String (Except Backend.PortError Backend.Conn))

/-- A harness with no leaf installed. -/
def Harness.empty : IO Harness := return { connections := ← IO.mkRef {} }

/-- The harness of the manifest `manifest`, at the directory `root`. -/
def Harness.ofManifest (root : System.FilePath) (manifest : Manifest) : CoreM Harness := do
  let admission := (← registryState).admit manifest
  return { admitted := admission.admitted, rejected := admission.rejected
           backends := manifest.backends, root, connections := ← IO.mkRef {} }

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
    IO (Except Backend.PortError Backend.Conn) := do
  if let some connection := (← h.connections.get)[name]? then return connection
  let connection ← match h.backends.find? (·.name == name) with
    | some backend => start h.root backend
    | none => pure (.error (.unavailable name "not declared in the manifest"))
  h.connections.modify (·.insert name connection)
  return connection

/-- Stop every started backend. -/
def Harness.stop (h : Harness) : IO Unit := do
  let connections ← h.connections.get
  h.connections.set {}
  -- A backend is killed, not asked to exit: nothing it does is waited on or believed, and
  -- closing its input cannot be relied on while other references to the handle are alive.
  for (_, connection) in connections.toList do
    if let .ok c := connection then Backend.abort c.child

/-- Send the value `input` to the admitted registration of `operation` on its form, and read the
answer: untrusted JSON, with the backend that gave it. -/
def send (h : Harness) (operation : String) (input : Wire) : TermElabM (Json × String) := do
  let registrations := h.admitted.filter fun a =>
    a.registration.operation == operation && a.registration.input == input.formId
  let registration ← match registrations with
    | #[r] => pure r.registration
    | #[] => throwStratum .noImplementation m!"no admitted registration computes {operation} on \
        the form {input.formId}"
    | _ =>
        let backends := registrations.toList.map (·.registration.backend)
        throwStratum .ambiguousRealization m!"several admitted registrations compute \
          {operation} on the form {input.formId} ({backends}); which one is used is a choice \
          the kernel does not make"
  let connection ← match ← (h.connection registration.backend : IO _) with
    | .ok c => pure c
    | .error e => throwStratum .unavailable m!"{e.render}"
  match ← (Backend.call connection operation input.json : IO _) with
  | .ok answer => return (answer, registration.backend)
  | .error e => throwStratum e.stratum m!"{e.render}"

/-- The answer `answer` of `backend` to `operation` is not a value of the operation's result
form. -/
def malformed (backend operation : String) (answer : Json) (message : String) : TermElabM α :=
  throwStratum .malformed m!"the answer of {backend} to {operation} is not a value of its \
    result form: {message} (the answer was {answer.compress})"

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
an instance is synthesized; a proposition is decided by the kernel (`CasCatalogue.Decide`), and
one it does not decide rejects the answer; every other argument is the next value of `args`,
decoded by `decodeArg` at its type. The decoded arguments are returned with their forms, when
they are values of a registered form. Too few or too many values reject the answer. -/
def decodeFamily (declaration : Name) (expected : Expr) (args : Array Json)
    (decodeArg : Expr → Json → TermElabM (Except String (Expr × Option Form))) :
    TermElabM (Except String (Expr × Array (Expr × Option Form))) := do
  let c ← mkConstWithFreshMVarLevels declaration
  let (mvars, infos, type) ← forallMetaTelescopeReducing (← inferType c)
  unless ← isDefEq type expected do
    return .error s!"{declaration} does not form a value of {expected}"
  let mut remaining := args.toList
  let mut decoded : Array (Expr × Option Form) := #[]
  for (m, info) in mvars.zip infos do
    unless (← instantiateMVars m).isMVar do continue
    let t ← instantiateMVars (← inferType m)
    if info.isInstImplicit then
      match ← trySynthInstance t with
      | .some inst => discard <| isDefEq m inst
      | _ => return .error s!"no instance of {t} is found"
    else if ← isProp t then
      if t.hasMVar then return .error s!"the condition {t} is not determined by the answer"
      let some proof ← Decide.decisionProof t
        | return .error s!"the answer does not satisfy {t}, or the kernel does not decide it"
      discard <| isDefEq m proof
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

/-- Send the value `w`, the receiver of an operation, along the structural route `route` the
semantic reading resolved (CC-TRANSPORT): the value of `M(U(x))` is computed on `U(x)`, and
`U(x)` is what the catalogue's rows say it is. A named object refining another along a route that
begins `route` is that other object at the same parameters (`RegistryState.transport`); it is
elaborated and recorded like any named object. A value no row sends further is sent as it is.
Nothing but the catalogue's rows moves a value. -/
def transport (trace : Trace) (w : Wire) (route : Array EdgeRef) : TermElabM Wire := do
  let state ← registryState
  let .object entry := w.form | return w
  let (target, _) := state.transport entry route
  if target.id == entry.id then return w
  let some (.object _ params) ← (trace.node? w.value : IO _) | return w
  let value ← objectAt trace target params
  let args := (w.json.getObjVal? "args").toOption.getD (Json.arr #[])
  return { form := .object target, value
           json := Json.mkObj [("ctor", target.id.raw), ("args", args)] }

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
  let mut params : Array Expr := #[]
  for arg in args do
    match arg.getNat? with
    | .ok n => params := params.push (mkNatLit n)
    | .error _ =>
        match ← decodeObject trace arg with
        | .ok (_, value) => params := params.push value
        | .error message => return .error s!"a parameter of {id} is not decoded: {message}"
  try return .ok (entry, ← objectAt trace entry params)
  -- not a reading fallback: an object that does not elaborate at these parameters is rejected
  catch e => return .error s!"{id} at {params} is not an object: {← e.toMessageData.toString}"

/-- Decode `j` as a value of `type` in the category `category` (CC-DECODE): a morphism `a ⟶ b`
of the category by its graph, in its registered graph-literal form; a registered named object of
the category at its parameters; a literal of the category's registered literal form, denoted;
or, for any other type, a value of the structural codec. -/
partial def decodeValue (trace : Trace) (category : NamedCategoryEntry) (type : Expr) (j : Json) :
    TermElabM (Except String (Expr × Option Form)) := do
  let state ← registryState
  let type ← instantiateMVars type
  if (← whnfR type).isAppOf ``Quiver.Hom then
    let some form := state.graphLiterals.find? (·.category == category.id)
      | return .error s!"a morphism of {category.name} has no registered graph-literal form"
    return ← match ← decodeFamily form.denotation type #[j] fun t j' => do
        return (← Codec.decode t j').map (·, none) with
      | .ok (hom, _) => pure (.ok (hom, some (.graph form)))
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
      return .ok (value, some (.literal form))
  return (← Codec.decode type j).map (·, none)

/-- Evaluate the recorded term `e`, the value of `what`, to a value of a form, through the
admitted registrations. -/
partial def realize (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let state ← registryState
  let e ← instantiateMVars e
  let some node ← (trace.node? e : IO _)
    | throwStratum .noImplementation m!"nothing computes {what}: it is not formed by a \
        catalogue operation the realized reading evaluates (a named object at its parameters, \
        a method of one)"
  match node with
  | .object id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let args ← params.mapM fun p => do
        match ← Codec.nat? p with
        | some n => pure (toJson n)
        | none => return (← realize h trace s!"a parameter of {id.raw} in {what}" p).json
      return { form := .object entry, value := e
               json := Json.mkObj [("ctor", id.raw), ("args", Json.arr args)] }
  | .literal id literal =>
      let some form := state.form? id.raw
        | throwStratum .invalid m!"{id.raw} is not a registered literal form"
      match ← Codec.encode literal with
      | .ok json => return { form, value := e, json }
      | .error message =>
          throwStratum .noImplementation m!"{what} is not sent: the literal {literal} of \
            {id.raw} is not encoded ({message})"
  | .limit id D lift? =>
      let some row := state.limits.find? (·.id == id) | unreachable!
      let some category := state.categories.find? (·.id == row.category)
        | throwStratum .invalid m!"the category of {id.raw} is not registered"
      if let some lift := lift? then
        throwStratum .noImplementation m!"no registration computes {what}: its diagram is \
          returned along the lift {lift.raw}, and the realized reading does not send a diagram \
          along a lift"
      -- The diagram's data: the explicit arguments of its standard form, in their forms.
      let D ← instantiateMVars D
      let .const standard _ := D.getAppFn
        | throwStratum .noImplementation m!"nothing computes {what}: its diagram is not in a \
            standard form"
      let infos ← forallTelescopeReducing (← getConstInfo standard).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let data := (D.getAppArgs.zip infos).filterMap fun (a, i) =>
        if i.isExplicit then some a else none
      let wires ← data.mapM fun a => realize h trace s!"the diagram of {id.raw} in {what}" a
      let input : Wire :=
        { form := .diagrams category, value := D
          json := Json.mkObj [("ctor", Codec.label standard),
                              ("args", Json.arr (wires.map (·.json)))] }
      let (answer, backend) ← send h id.raw input
      -- The answer is the cone (cocone) of the shape, as the data of Mathlib's standard
      -- constructor: its apex, then its legs; the commutation it needs is decided by the kernel.
      let some constructor := standardCone row.shape row.colimit
        | throwStratum .invalid m!"the shape {row.shape} has no standard cone"
      let kind := if row.colimit then "cocone" else "cone"
      let shape := s!"a {kind} is \{\"ctor\": \"{kind}\", \"args\": [<apex>, <legs>…]}"
      let .ok name := answer.getObjValAs? String "ctor" | malformed backend id.raw answer shape
      unless name == kind do malformed backend id.raw answer shape
      let .ok args := (answer.getObjVal? "args").bind (·.getArr?)
        | malformed backend id.raw answer shape
      let expected ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone
        else ``CategoryTheory.Limits.Cone) #[D]
      let (cone, decoded) ← match ← decodeFamily constructor expected args
          (decodeValue trace category) with
        | .ok result => pure result
        | .error message => malformed backend id.raw answer message
      let some (apex, some form) := decoded[0]?
        | malformed backend id.raw answer s!"the apex is not a value of a registered form of \
            {category.name}"
      return { form, value := apex, json := args[0]!, universal := some cone }
  | .method id route receiver =>
      let input ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let input ← transport trace input route
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor
        | throwStratum .invalid m!"{id.raw} has no registered functor"
      let some target := state.category? functor.target
        | throwStratum .invalid m!"the result category of {id.raw} is not registered"
      let (form, type) ← resultForm state target.id m!"the result of {id.raw}"
      let (value, json) ← call h id.raw input type
      return { form := .literal form, value, json }
  | .property id _ _ =>
      throwStratum .invalid m!"the decision {id.raw} is not a value"

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
  match ← decideProp (← mkEq a b) with
  | some equal => return equal
  | none => throwError "the equality of {a} and {b} is not decided by the kernel: the form's \
      decidable equality does not compute"

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
def decideEvaluated (p : Expr) : TermElabM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  let evaluations := evaluationsOf (← registryState) p
  if ← evaluatedDecides evaluations p then return some true
  if ← evaluatedDecides evaluations (mkNot p) then return some false
  return none

/-- Discharge `claim` in Lean, generically (`decideEvaluated`): holds when its proposition is
decided true; invalid, as false mathematics, when it is decided false; `none` when Lean does not
decide it. -/
def discharge (claim : Claim) : TermElabM (Option Outcome) := do
  let refuted (what : String) : TermElabM (Option Outcome) :=
    throwStratum .invalid m!"{what} is refuted: Lean decides it false"
  match claim with
  | .settled outcome _ => return some outcome
  | .implemented _ => return none
  | .literal _ _ _ _ prop left right =>
      match ← decideEvaluated prop with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .homs _ _ _ prop left right =>
      match ← decideEvaluated prop with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .decision prop expected shown =>
      let some expected := expected | return none
      match ← decideEvaluated prop with
      | some decided => if decided == expected then return some .holds else refuted shown
      | none => return none

/-- Decide `claim` through the admitted registrations. -/
def realizeClaim (h : Harness) (trace : Trace) (claim : Claim) : TermElabM Outcome := do
  match claim with
  | .settled outcome _ => return outcome
  | .implemented value =>
      -- A decision is realized as one; anything else as a value.
      if ← isProp value then discard <| realizeDecision h trace "the decision" value
      else discard <| realize h trace "the value" value
      return .holds
  | .literal X _ form L _ left right =>
      let w ← realize h trace left X
      let .literal form' := w.form
        | throwStratum .noImplementation m!"{left} is not computed as a value of the literal \
            form {form.id.raw}"
      unless form'.id == form.id do
        throwStratum .invalid m!"{left} is computed in the form {form'.id.raw}, and compared in \
          {form.id.raw}"
      return if ← evaluatedEq w.value L then .holds
        else .wrong s!"{left} is not {right}: the registration answered {w.json.compress}"
  | .homs f g _ _ left right =>
      -- Both sides computed as values of one form, and compared there.
      let a ← realize h trace left f
      let b ← realize h trace right g
      unless a.formId == b.formId do
        throwStratum .invalid m!"{left} is computed in the form {a.formId}, and {right} in \
          {b.formId}"
      return if ← evaluatedEq a.value b.value then .holds
        else .wrong s!"{left} is not {right}: computed as {a.json.compress} and \
          {b.json.compress}"
  | .decision prop expected shown =>
      let (answer, json) ← realizeDecision h trace shown prop
      return if ← evaluatedEq answer (toExpr expected) then .holds
        else .wrong s!"{shown} is not the answer: the registration answered {json.compress}"

/-- The semantic question a claim asks, as a fingerprint of its elaborated proposition (and, for a
decision, the expected answer): what an admitted assertion means under this kernel, parser and
pin, compared across candidates by `scripts/check_question_permanence.py` (gov-meaning-permanence).
It is never the statement's text, its outcome, or whether it is provable. -/
def claimQuestion : Claim → TermElabM (String × String)
  | .settled outcome about => do
      let about ← about.mapM instantiateMVars
      let shown ← about.mapM fun e => return toString (← ppExpr e)
      return (s!"settled:{outcome.kind}:{(hash about).toNat}",
        s!"settled ({outcome.kind}) of: {", ".intercalate shown.toList}")
  | .implemented value => fingerprint "implemented" value
  | .literal _ _ _ _ prop .. => fingerprint "literal" prop
  | .homs _ _ _ prop .. => fingerprint "homs" prop
  | .decision prop expected _ => fingerprint s!"decision:{expected}" prop
where
  /-- The fingerprint, and the proposition as the acceptance author reads it to confirm the
  interpretation it records. -/
  fingerprint (kind : String) (e : Expr) : TermElabM (String × String) := do
    let e ← instantiateMVars e
    return (s!"{kind}:{(hash e).toNat}", s!"{kind}: {← ppExpr e}")

/-- Run a statement, within the `let` bindings `scope`: its semantic reading forms its claim; Lean
discharges the claim where it can; otherwise it is realized through the harness. A `let` binds its
term when its reading succeeds; its realized failure surfaces where it is used.

Every failure is an outcome (`Outcome.ofException`), whatever stage throws it: a stratum is
reported as itself, and an exception without one, exhausted heartbeats included, as an internal
error. Nothing is caught to be reinterpreted, and a failed statement leaves `scope` unchanged. -/
def runAsking (h : Harness) (scope : Scope) (stx : Syntax) :
    TermElabM (Outcome × Scope × Option (String × String)) := do
  -- The question is kept once read, whichever later stage fails (a gap is thrown while realizing).
  let asked ← IO.mkRef (none : Option (String × String))
  let attempt : TermElabM (Outcome × Scope × Option (String × String)) := do
    let trace ← (Trace.new : IO _)
    let claim ← (Language.claim scope stx).run { trace := some trace }
    let question ← claimQuestion claim
    asked.set (some question)
    if let some (x, t) ← letBinding? stx then return (.holds, scope.insert x t, some question)
    if let some outcome ← discharge claim then return (outcome, scope, some question)
    return (← realizeClaim h trace claim, scope, some question)
  tryCatchRuntimeEx attempt fun e => return (← Outcome.ofException e, scope, ← asked.get)

/-- `runAsking` without the question. -/
def run (h : Harness) (scope : Scope) (stx : Syntax) : TermElabM (Outcome × Scope) := do
  let (outcome, scope, _) ← runAsking h scope stx
  return (outcome, scope)

end Realize

end CasCatalogue
