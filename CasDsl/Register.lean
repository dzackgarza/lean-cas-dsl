/-
Elaboration-time registration helpers: the checked adders of
`Registry.lean` lifted into `CommandElabM`.

Load-bearing decision: registration failure is an ELABORATION error, not a
runtime one. A clash in the prelude therefore fails `lake build` — the
standard universe cannot ship half-registered, and a notebook can never
observe a registry that silently dropped or overwrote a declaration.

These are ordinary `CommandElabM` actions, used from `run_cmd` blocks (see
`CasDsl/Std.lean`); no new command syntax is introduced, so registrations
read as data and stay `#print`-able Lean values.
-/
import Lean
import CasDsl.Registry

namespace CasDsl

open Lean Elab Command

/-- Run one checked adder against the current environment, committing it on
success and reporting the registry's own message on a clash. -/
private def registerWith {α : Type}
    (adder : Environment → α → Except String Environment) (x : α)
    : CommandElabM Unit := do
  match adder (← getEnv) x with
  | .ok env => modifyEnv fun _ => env
  | .error msg => throwError msg

def registerCategory! (d : CatDecl) : CommandElabM Unit :=
  registerWith addCategoryChecked d

def registerMethod! (d : MethodDecl) : CommandElabM Unit :=
  registerWith addMethodChecked d

def registerRoute! (r : Route) : CommandElabM Unit :=
  registerWith addRouteChecked r

def registerProfileRule! (r : ProfileRule) : CommandElabM Unit :=
  registerWith addProfileRuleChecked r

def registerRepresentative! (r : Representative) : CommandElabM Unit :=
  registerWith addRepresentativeChecked r

end CasDsl
