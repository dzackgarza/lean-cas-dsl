/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasContract.Failure
public import Lean.Elab.Command

public section

/-!
# Permanent acceptance assertions (`specs/architecture.md`, "Acceptance")

An assertion is a proposition in the mathematical language with the provenance of its expected
value. The suite's assertions are statements of the language in `tests/acceptance/*.cas`
(`CasCatalogue.TestSuite`), decided by Lean or through the admitted registrations
(`CasCatalogue.Realize`). Beside them, `#accept "id" from "source" : P := proof` states a
proposition `P` of the catalogue's mathematics and its proof, admitted as the theorem
`CasAcceptance.Permanent.«id»`. Nothing a leaf supplies enters either: an `#accept` is proved
in Lean about semantic values, and a statement compares a leaf's decoded answer with the
expected value and believes nothing else about it.

The proposition, the value and the provenance are permanent: `scripts/check_acceptance_permanent.py`
refuses to modify or delete an admitted assertion (the text of an `#accept` up to its `:=`). The
proof after `:=` is how the assertion is checked, and may change. `#acceptance_gaps` lists the
assertions that are not established here.
-/

open Lean Elab Command Term Meta

namespace CasCatalogue.Acceptance

/-- How an admitted assertion stands in this build. -/
inductive Status
  | holds
  /-- Its proposition cannot be formed here (a computation failure, by stratum). -/
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

/-- The name of the theorem admitting the assertion `id`. -/
def theoremName (id : String) : Name := `CasAcceptance.Permanent ++ Name.mkSimple id

end CasCatalogue.Acceptance
