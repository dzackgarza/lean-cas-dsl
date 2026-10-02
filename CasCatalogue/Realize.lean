/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language
public import CasCatalogue.Admission
public import CasCatalogue.Codec
public import CasCatalogue.StructuredResult
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
structure Wire where
  form : Form
  value : Expr
  json : Json
  /-- For the apex of a limit computed by a registration: the cone (cocone) reconstructed from
  the answer, whose legs a later operation reads (CC-DECODE). -/
  universal : Option Expr := none
  /-- Complete constructor response, including every defining map. -/
  universalJson : Option Json := none
  /-- The realized diagram at which the defining maps were decoded. -/
  universalDiagram : Option Expr := none

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
an instance is synthesized; a proposition is checked by the kernel (`CasCatalogue.Decide`), by
its `Decidable` instance or reflexivity when equality's sides are definitionally equal; a condition
neither check proves rejects the answer. Binder annotations never run their tactics. Every other
argument is the next value of `args`,
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
      -- Binder annotations such as autoParam carry elaboration instructions, not another
      -- mathematical condition. Decide their reduced proposition without running the tactic.
      let condition ← whnfR t
      if condition.hasMVar then
        return .error s!"the condition {condition} is not determined by the answer"
      let mut proof? ← Decide.decisionProof condition
      -- Reflexivity needs no Decidable instance and changes no commuting equation.
      -- The independently constructed proof is checked against the complete condition.
      if proof?.isNone then
        if let some (_, left, right) := condition.eq? then
          if ← isDefEq left right then
            let reflexive ← mkEqRefl left
            if ← Decide.kernelAccepts condition reflexive then proof? := some reflexive
      let some proof := proof?
        | return .error s!"the answer does not satisfy {condition}, or the kernel does not decide it"
      unless ← isDefEq m proof do
        return .error s!"the checked proof does not inhabit the constructor condition {t}"
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
  -- Retain the original construction and diagram through representation changes.
  -- These fields record its source maps; they do not assert a mapped universal cone.
  return { w with form := .object target, value := value
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
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      let input ← realize h trace s!"the structural parameter of {what}" receiver
      let .object entry := input.form
        | throwStratum .noImplementation m!"a structural parameter has no named-object presentation"
      unless entry.id == source && entry.category == sourceCategory do
        throwStratum .noImplementation m!"a structural parameter has a different source presentation"
      let output ← transport trace input route
      unless output.form.category == targetCategory &&
          (← withoutModifyingState (isDefEq output.value e)) do
        throwStratum .noImplementation m!"the registered parameter route has no target presentation"
      return { output with value := e }
  | .literal id literal =>
      let some form := state.form? id.raw
        | throwError "{id.raw} is not a registered literal form"
      match ← Codec.encode literal with
      | .ok json => return { form, value := e, json }
      | .error message =>
          throwStratum .noImplementation m!"{what} is not sent: the literal {literal} of \
            {id.raw} is not encoded ({message})"
  | .limit id D lift? =>
      let some row := state.limits.find? (·.id == id) | unreachable!
      let some category := state.categories.find? (·.id == row.category)
        | throwError "internal registry inconsistency: the category of {id.raw} is not registered"
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
      -- The diagram sent is the standard form at the realized values of its data (the apex of an
      -- earlier realized limit is its leaf's object, not the catalogue's presentation of it), its
      -- implicit arguments determined by them; its cone is decoded at that diagram.
      let sent ← mkAppM standard (wires.map (·.value))
      let input : Wire :=
        { form := .diagrams category, value := sent
          json := Json.mkObj [("ctor", Codec.label standard),
                              ("args", Json.arr (wires.map (·.json)))] }
      let (answer, backend) ← send h id.raw input
      -- The answer is the cone (cocone) of the shape, as the data of Mathlib's standard
      -- constructor: its apex, then its legs; the commutation it needs is decided by the kernel.
      let (result, decoded) ← match ← StructuredResult.decode row sent answer
          (fun constructor expected args =>
            decodeFamily constructor expected args (decodeValue trace category)) with
        | .ok result => pure result
        | .error message => malformed backend id.raw answer message
      let some (apex, some form) := decoded[0]?
        | malformed backend id.raw answer s!"the apex is not a value of a registered form of \
            {category.name}"
      let .ok args := (answer.getObjVal? "args").bind (·.getArr?)
        | malformed backend id.raw answer "the complete construction has no args array"
      return { form, value := apex, json := args[0]!, universal := some result.cone
               universalJson := some result.answer, universalDiagram := some result.diagram }
  | .method id route receiver =>
      let input ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
      let input ← transport trace input route
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor
        | throwError "{id.raw} has no registered functor"
      let some target := state.category? functor.target
        | throwError "the result category of {id.raw} is not registered"
      let (form, type) ← resultForm state target.id m!"the result of {id.raw}"
      let (value, json) ← call h id.raw input type
      return { form := .literal form, value, json }
  | .property id _ _ =>
      throwError "the decision {id.raw} is not a value"

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
def discharge (claim : Claim) : TermElabM (Option ExecutionOutcome) := do
  let refuted (what : String) : TermElabM (Option ExecutionOutcome) :=
    return some (.wrong s!"{what} is refuted: Lean decides it false")
  match claim with
  | .binding => return some (.internal "a binding entered execution")
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
  | .decision prop expected shown | .judged _ prop expected shown =>
      let some expected := expected | return none
      match ← decideEvaluated prop with
      | some decided => if decided == expected then return some .holds else refuted shown
      | none => return none

/-- Decide `claim` through the admitted registrations. -/
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
      let .literal form' := w.form
        | throwStratum .noImplementation m!"{left} is not computed as a value of the literal \
            form {form.id.raw}"
      unless form'.id == form.id do
        throwStratum .malformed m!"{left} is computed in the form {form'.id.raw}, and compared in \
          {form.id.raw}"
      return if ← evaluatedEq w.value L then .holds
        else .wrong s!"{left} is not {right}: the registration answered {w.json.compress}"
  | .homs f g _ _ left right =>
      -- Both sides computed as values of one form, and compared there.
      let a ← realize h trace left f
      let b ← realize h trace right g
      unless a.formId == b.formId do
        throwStratum .malformed m!"{left} is computed in the form {a.formId}, and {right} in \
          {b.formId}"
      return if ← evaluatedEq a.value b.value then .holds
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

partial def TermTable.encode (table : TermTable) (term : Expr) : TermElabM Nat := do
  if let some index := (← table.terms.get)[term]? then return index
  if term.hasMVar || term.hasLevelMVar then throwError "question contains unresolved typed terms"
  let node ← match term with
    | .mdata _ child =>
        let index ← table.encode child
        table.terms.modify (·.insert term index)
        return index
    | .bvar index => pure (Json.arr #[toJson "bvar", toJson index])
    | .fvar .. | .mvar .. => throwError "question contains an unclosed typed term"
    | .sort level => pure (Json.arr #[toJson "sort", encodeLevel level])
    | .const name levels =>
        pure (Json.arr #[toJson "const", toJson (reprStr name), toJson (levels.map encodeLevel)])
    | .app fn arg =>
        pure (Json.arr #[toJson "app", toJson (← table.encode fn), toJson (← table.encode arg)])
    | .lam _ type body info =>
        pure (Json.arr #[toJson "lam", toJson (← table.encode type),
          toJson (← table.encode body), toJson (reprStr info)])
    | .forallE _ type body info =>
        pure (Json.arr #[toJson "forall", toJson (← table.encode type),
          toJson (← table.encode body), toJson (reprStr info)])
    | .letE _ type value body nondep =>
        pure (Json.arr #[toJson "let", toJson (← table.encode type),
          toJson (← table.encode value), toJson (← table.encode body), toJson nondep])
    | .lit literal => pure (Json.arr #[toJson "literal", toJson (reprStr literal)])
    | .proj name index value =>
        pure (Json.arr #[toJson "proj", toJson (reprStr name), toJson index,
          toJson (← table.encode value)])
  let description := node.compress
  let index ← match (← table.canonicalNodes.get)[description]? with
    | some index => pure index
    | none => do
        let index := (← table.nodes.get).size
        table.nodes.modify (·.push node)
        table.canonicalNodes.modify (·.insert description index)
        pure index
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
      | .literal form literal => pure (.literal form (← instantiateMVars literal))
      | .method id route receiver => pure (.method id route (← instantiateMVars receiver))
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
      | .literal form literal =>
          pure (Json.arr #[toJson "literal", toJson form.raw, toJson (← table.encode literal)])
      | .method id route receiver =>
          pure (Json.arr #[toJson "method", toJson id.raw, toJson (route.map reprStr),
            toJson (← table.encode receiver)])
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
  if let some outcome ← discharge question.claim then return outcome
  realizeClaim h (← IO.mkRef question.trace) question.claim

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
    return ← tryCatchRuntimeEx bind fun e => return (← Outcome.ofException e, scope, none)
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
