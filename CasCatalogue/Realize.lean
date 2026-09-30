/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language
public import CasCatalogue.Admission
public import CasCatalogue.Codec
public import CasContract.Port
public import Mathlib.CategoryTheory.ConcreteCategory.Basic

@[expose] public section

/-!
# The realized reading (`specs/leaf-registration.md`)

A statement's semantic reading elaborates it into its claim (`Language.Claim`): a proposition of
the catalogue's mathematics, and the term it is about. This module decides the claim:

1. **Lean discharge first.** The proposition is decided in Lean, generically: `decide` by
   evaluation within a fixed heartbeat budget (`decideProp`; the `decideObligation` pattern, on
   `Decidable` instances alone, running no tactic). If Lean proves it, the statement holds and no
   leaf is consulted. If Lean refutes it, the statement is false mathematics and is invalid.
2. **Otherwise, realize.** The same term is evaluated bottom-up through the operations the
   semantic reading recorded (`CasCatalogue.Trace`): a named object at its parameters is its
   form, encoded by the kernel; an operation applied to a value of a form selects the admitted
   registration of that operation on that form (`CasCatalogue.Admission`), sends the encoded
   input over the port, and decodes the answer in the operation's result form: the registered
   literal form of its result category. No registration is a gap; two are a gap reported as
   ambiguous; a backend that cannot start is unavailable; a rejected answer is malformed.
3. **Comparison.** `assert X = L` holds when the decoded value equals `L`, by the decidable
   equality of the form's type, evaluated here. A decision is compared as a three-valued answer.
   Nothing a leaf returned is used as evidence of anything but its own answer.

The one decidability the kernel supplies itself is `decidableConcreteHomEq`: two morphisms of a
concrete category are equal iff their functions are, so their equality is decidable whenever
the function space's is (a finite domain with decidable equality on the codomain). It is what
makes the elements of a set, morphisms `1 → X`, compare in Lean.
-/

open Lean Meta Elab Term CategoryTheory

namespace CasCatalogue

/-- Equality of morphisms of a concrete category, decided on their functions
(`ConcreteCategory.coe_ext`). -/
instance decidableConcreteHomEq {C : Type _} [Category C] {FC : C → C → Type _}
    {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y : C} (f g : X ⟶ Y) [DecidableEq (CC X → CC Y)] : Decidable (f = g) :=
  decidable_of_iff (⇑(ConcreteCategory.hom f) = ⇑(ConcreteCategory.hom g))
    ⟨ConcreteCategory.coe_ext, fun h => h ▸ rfl⟩

namespace Realize

open Language

/-- The heartbeat budget of one decision by evaluation (in the units of `maxHeartbeats`). -/
def decideBudget : Nat := 20000

/-- The proposition `p` decided by evaluation, within `decideBudget`: `some true` when
`decide p` evaluates to `true`, `some false` when to `false`, `none` when `p` has no `Decidable`
instance, or its decision does not evaluate within the budget (a classical instance, a
computation beyond it). `Decidable` instances are the catalogue's and Mathlib's; the kernel runs
no proof search. -/
def decideProp (p : Expr) : MetaM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar then return none
  let attempt : MetaM (Option Expr) := do
    let decision ← mkDecide p
    some <$> (withTransparency .all <| whnf decision)
  let outcome ← withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|
      -- not a reading fallback: a proposition without a `Decidable` instance, or whose decision
      -- exceeds its budget, is not decided by Lean; the claim is then realized, unchanged
      tryCatchRuntimeEx attempt fun _ => pure none
  return match outcome with
    | some r => if r.isConstOf ``Bool.true then some true
        else if r.isConstOf ``Bool.false then some false
        else none
    | none => none

/-- The values the realized reading passes to and from a port: a closed value of a registered
literal form, or a registered named object at its parameters, each with its wire encoding. -/
inductive Wire
  | literal (form : LiteralEntry) (value : Expr) (json : Json)
  | object (entry : ObjectEntry) (json : Json)

def Wire.formId : Wire → String
  | .literal form .. => form.id.raw
  | .object entry _ => entry.id.raw

def Wire.json : Wire → Json
  | .literal _ _ json => json
  | .object _ json => json

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

/-- The harness of the manifest at `path`, or of the leaves package's manifest
(`leaves.json` at the root of `cas_leaves`, `Manifest`). No manifest is no leaf. A manifest that
does not read is reported and admits nothing. -/
def Harness.load (path? : Option System.FilePath := none) : CoreM Harness := do
  let path ← match path? with
    | some path => pure path
    | none => do pure ((← Backend.packageDir "cas_leaves") / manifestFile)
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
  for (_, connection) in (← h.connections.get).toList do
    if let .ok c := connection then Backend.stop c
  h.connections.set {}

/-- Call the admitted registration of `operation` on the value `input`, and decode the answer as
a value of `resultType`. -/
def call (h : Harness) (operation : String) (input : Wire) (resultType : Expr) :
    TermElabM (Expr × Json) := do
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
  let answer ← match ← (Backend.call connection operation input.json : IO _) with
    | .ok answer => pure answer
    | .error e => throwStratum e.stratum m!"{e.render}"
  match ← Codec.decode resultType answer with
  | .ok value => return (value, answer)
  | .error message =>
      throwStratum .malformed m!"the answer of {registration.backend} to {operation} is not a \
        value of its result form: {message} (the answer was {answer.compress})"

/-- The registered literal form of the category `category`: the result form of an operation
landing there. -/
def resultForm (state : RegistryState) (category : CategoryId) (what : MessageData) :
    TermElabM (LiteralEntry × Expr) := do
  let some form := state.literals.find? (·.category == category)
    | let name := (state.categories.find? (·.id == category)).map (·.name) |>.getD category.raw
      throwStratum .noImplementation m!"{what} is an object of {name}, which has no registered \
        literal form: nothing decodes it"
  return (form, ← mkConstWithFreshMVarLevels form.type)

/-- Evaluate the recorded term `e` to a value of a form, through the admitted registrations. -/
partial def realize (h : Harness) (trace : Trace) (e : Expr) : TermElabM Wire := do
  let state ← registryState
  let e ← instantiateMVars e
  let some node ← (trace.node? e : IO _)
    | throwStratum .noImplementation m!"nothing computes {e}: it is not formed by a catalogue \
        operation the realized reading evaluates (a literal form or a named object, a method or \
        a property of one)"
  match node with
  | .object id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      let args ← params.mapM fun p => do
        match ← Codec.nat? p with
        | some n => pure (toJson n)
        | none => return (← realize h trace p).json
      return .object entry (Json.mkObj [("ctor", id.raw), ("args", Json.arr args)])
  | .method id _ receiver =>
      let input ← realize h trace receiver
      let some method := state.methods.find? (·.id == id) | unreachable!
      let some functor := state.functor? method.functor
        | throwStratum .invalid m!"{id.raw} has no registered functor"
      let some target := state.category? functor.target
        | throwStratum .invalid m!"the result category of {id.raw} is not registered"
      let (form, type) ← resultForm state target.id m!"the result of {id.raw}"
      let (value, json) ← call h id.raw input type
      return .literal form value json
  | .property id _ _ =>
      throwStratum .invalid m!"the decision {id.raw} is not a value"
  | .limit id _ =>
      throwStratum .noImplementation m!"no registration computes the limit {id.raw}: the \
        realized reading sends no diagrams over the port"

/-- Evaluate the recorded decision `p` to a three-valued answer (`Option Bool`), through the
admitted registration of its property on the form of its receiver. -/
def realizeDecision (h : Harness) (trace : Trace) (p : Expr) : TermElabM (Expr × Json) := do
  let p ← instantiateMVars p
  let some (.property id _ receiver) ← (trace.node? p : IO _)
    | throwStratum .noImplementation m!"nothing decides {p}: it is not a registered property of \
        a value the realized reading evaluates"
  let input ← realize h trace receiver
  call h id.raw input (mkApp (mkConst ``Option [0]) (mkConst ``Bool))

/-- Whether two closed values of a type with decidable equality are equal, by evaluation. The
literal forms are registered with decidable equality; a decision is an `Option Bool`. -/
def evaluatedEq (a b : Expr) : MetaM Bool := do
  let decision ← withTransparency .all <| whnf (← mkDecide (← mkEq a b))
  if decision.isConstOf ``Bool.true then return true
  if decision.isConstOf ``Bool.false then return false
  throwError "the equality of {a} and {b} does not evaluate: the form's decidable equality is \
    not executable"

/-- Discharge `claim` in Lean, generically: holds when its proposition is decided true; invalid,
as false mathematics, when it is decided false; `none` when Lean does not decide it. -/
def discharge (claim : Claim) : TermElabM (Option Outcome) := do
  let refuted (what : String) : TermElabM (Option Outcome) :=
    throwStratum .invalid m!"{what} is refuted: Lean decides it false"
  match claim with
  | .settled outcome => return some outcome
  | .implemented _ => return none
  | .literal _ _ _ _ prop left right =>
      match ← decideProp prop with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .homs _ _ _ prop left right =>
      match ← decideProp prop with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .decision prop expected shown =>
      let some expected := expected | return none
      match ← decideProp prop with
      | some decided => if decided == expected then return some .holds else refuted shown
      | none => return none

/-- Decide `claim` through the admitted registrations. -/
def realizeClaim (h : Harness) (trace : Trace) (claim : Claim) : TermElabM Outcome := do
  match claim with
  | .settled outcome => return outcome
  | .implemented value =>
      -- A decision is realized as one; anything else as a value.
      if ← isProp value then discard <| realizeDecision h trace value
      else discard <| realize h trace value
      return .holds
  | .literal X _ form L _ left right =>
      let .literal form' value json ← realize h trace X
        | throwStratum .noImplementation m!"{left} is not computed as a value of the literal \
            form {form.id.raw}"
      unless form'.id == form.id do
        throwStratum .invalid m!"{left} is computed in the form {form'.id.raw}, and compared in \
          {form.id.raw}"
      return if ← evaluatedEq value L then .holds
        else .wrong s!"{left} is not {right}: the registration answered {json.compress}"
  | .homs _ _ category _ left right =>
      throwStratum .noImplementation m!"{left} = {right} is not decided by Lean, and the \
        morphisms of {category.name} have no registered literal form to compute in"
  | .decision prop expected shown =>
      let (answer, json) ← realizeDecision h trace prop
      return if ← evaluatedEq answer (toExpr expected) then .holds
        else .wrong s!"{shown} is not the answer: the registration answered {json.compress}"

/-- Run a statement, within the `let` bindings `scope`: its semantic reading forms its claim
(failing that, it is invalid whatever leaves are installed); Lean discharges the claim where it
can; otherwise it is realized through the harness. A `let` binds its term either way; its
realized failure surfaces where it is used. -/
def run (h : Harness) (scope : Scope) (stx : Syntax) : TermElabM (Outcome × Scope) := do
  let scope' := match ← letBinding? stx with
    | some (x, t) => scope.insert x t
    | none => scope
  let trace ← (Trace.new : IO _)
  let claim ← try (Language.claim scope stx).run { mode := .semantic, trace := some trace }
    -- not a reading fallback: it rethrows the semantic failure as invalidity
    catch e => throwError "not a valid statement: {e.toMessageData}"
  if (← letBinding? stx).isSome then return (.holds, scope')
  if let some outcome ← discharge claim then return (outcome, scope')
  let classify (e : Exception) : TermElabM Outcome := do
    match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization =>
        return .gap (← e.toMessageData.toString)
    | some .unavailable => return .unavailable (← e.toMessageData.toString)
    | some .malformed => return .malformed (← e.toMessageData.toString)
    | _ => throw e
  -- not a reading fallback: a realized failure is recorded as its stratum; the rest is rethrown
  let outcome ← try realizeClaim h trace claim catch e => classify e
  return (outcome, scope')

end Realize

end CasCatalogue
