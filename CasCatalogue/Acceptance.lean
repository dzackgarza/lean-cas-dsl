/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasContract.Failure
public import CasContract.Port
public import Lean.Elab.Command

public section

/-!
# Permanent acceptance assertions (`specs/architecture.md`, "Acceptance")

An assertion is a proposition in the mathematical language with the provenance of its expected
value:

* `#accept "id" from "source" : P := proof` states `P` about semantic values (`value%`,
  `ask%`, `eq%`), and the proof checks it. It is admitted as the theorem
  `CasAcceptance.Permanent.«id»`. If `P` cannot be elaborated because no realization computes a
  call in it (`NoImplementation`, or an ambiguous realization), the assertion is recorded as an
  implementation gap and the build continues. `#accept "id" from "source" realized : …` also
  asserts that an implementation exists, so a gap fails it.
* `#accept_backend "id" from "source" : (call) agrees value` runs `call`, a backend realization of
  type `RegistryState → IO (Except Backend.PortError τ)`, and asserts that its answer equals
  `value`: the result of a realization whose denotation another assertion proves. An unavailable
  backend is recorded, a malformed answer fails, and a different answer fails as a wrong answer.

The proposition, the value and the provenance are permanent: `scripts/check_acceptance_permanent.py`
refuses to modify or delete an admitted assertion (the text of an `#accept` up to its `:=`, or the
whole `#accept_backend`). The proof after `:=` is how the assertion is checked, and may change; it
proves the mathematics and is never established from a leaf's definitions.
`#acceptance_gaps` lists the assertions no realization computes yet.
-/

open Lean Elab Command Term Meta

namespace CasCatalogue.Acceptance

/-- How an admitted assertion stands in this build. -/
inductive Status
  | holds
  /-- No realization computes it: the failure, `NoImplementation` or an ambiguous realization. -/
  | gap (reason : String)
  /-- Its backend is not available here. -/
  | unavailable (reason : String)
  deriving Inhabited, Repr

/-- An admitted assertion: its id, provenance and status here, and what reruns it elsewhere: the
command and the namespace and `open`s it was elaborated in. -/
structure Record where
  id : String
  source : String
  status : Status
  command : Syntax := .missing
  «namespace» : Name := .anonymous
  openDecls : List OpenDecl := []
  deriving Inhabited

private initialize acceptanceExt : SimplePersistentEnvExtension Record (Array Record) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- The assertions admitted in the imported modules and this one. -/
def records (env : Environment) : Array Record := acceptanceExt.getState env

def recordAdmission (record : Record) : CommandElabM Unit := do
  if (records (← getEnv)).any (·.id == record.id) then
    throwError "the acceptance assertion {record.id} is already admitted"
  modifyEnv (acceptanceExt.addEntry · record)

/-- The outcome of running a backend realization against a value. -/
inductive BackendOutcome
  | agrees
  | disagrees (got expected : String)
  | portError (error : Backend.PortError)
  deriving Inhabited

def backendOutcome {τ : Type} [BEq τ] [Repr τ]
    (call : RegistryState → IO (Except Backend.PortError τ)) (value : τ) (state : RegistryState) :
    IO BackendOutcome := do
  match ← call state with
  | .ok got => return if got == value then .agrees else .disagrees (reprStr got) (reprStr value)
  | .error e => return .portError e

unsafe def evalBackendOutcomeUnsafe (e : Expr) : TermElabM (RegistryState → IO BackendOutcome) := do
  evalExpr (RegistryState → IO BackendOutcome)
    (← mkArrow (mkConst ``RegistryState) (mkApp (mkConst ``IO) (mkConst ``BackendOutcome))) e

@[implemented_by evalBackendOutcomeUnsafe]
opaque evalBackendOutcome (e : Expr) : TermElabM (RegistryState → IO BackendOutcome)

/-- The name of the theorem admitting the assertion `id`. -/
def theoremName (id : String) : Name := `CasAcceptance.Permanent ++ Name.mkSimple id

end CasCatalogue.Acceptance
