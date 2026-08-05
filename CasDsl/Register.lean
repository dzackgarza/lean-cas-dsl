/-
Elaboration-time registration helpers: the checked adders of
`Registry.lean` lifted into `CommandElabM`, plus the SEMANTIC checks the
pure adders cannot perform (SPEC-REGISTRY-TYPE-PREPASS, invariant I1).

Load-bearing decision: registration failure is an ELABORATION error, not a
runtime one. A clash in the prelude therefore fails `lake build` — the
standard universe cannot ship half-registered, and a notebook can never
observe a registry that silently dropped or overwrote a declaration.

The semantic checks added here are the anti-lie layer: a category's
`telescope` names Mathlib classes, and a profile rule whose pattern names a
CONCRETE domain is admitted only when every telescope class synthesizes at
the domain's denoted type. A membership Lean cannot discharge fails the
build; family patterns (`polyOver anyDom`) are checked at resolution time,
where the receiver is concrete.

These are ordinary `CommandElabM` actions, used from `run_cmd` blocks (see
`CasDsl/Std.lean`); no new command syntax is introduced, so registrations
read as data and stay `#print`-able Lean values.
-/
import Lean
import CasDsl.Registry
import CasDsl.Mathlib.Denote
import CasDsl.Mathlib.Anchors

namespace CasDsl

open Lean Elab Command Meta

/-- Run one checked adder against the current environment, committing it on
success and reporting the registry's own message on a clash. -/
private def registerWith {α : Type}
    (adder : Environment → α → Except String Environment) (x : α)
    : CommandElabM Unit := do
  match adder (← getEnv) x with
  | .ok env => modifyEnv fun _ => env
  | .error msg => throwError msg

/-- The concrete domain a pattern names, when it names one. Family patterns
(`polyOver anyDom`, `anyMod`, …) have no single denoted type; their
memberships are judged at resolution time instead. -/
private def DomainPattern.concrete? : DomainPattern → Option Domain
  | .exact d => some d
  | .polyOver p => (concrete? p).map .poly
  | _ => none

private def PresPattern.concreteDomain? : PresPattern → Option Domain
  | .elemOf p => p.concrete?
  | .domainIs p => p.concrete?
  | .domainSetOf p => p.concrete?
  | _ => none

/-- Fully apply a class to a type — synthesizing the class's OWN instance
parameters (`UniqueFactorizationMonoid` needs `CancelCommMonoidWithZero`) —
then synthesize the membership itself. Failure at either step is the honest
report that the claimed mathematics does not hold at this type. -/
def synthMembership (cls : Name) (T : Expr) : MetaM Unit := do
  let mut e ← mkAppM cls #[T]
  let mut ty ← whnf (← inferType e)
  while ty.isForall do
    let .forallE _ bt _ bi := ty | break
    unless bi == .instImplicit do
      throwError "{cls} has a non-instance parameter this check cannot fill"
    e := mkApp e (← synthInstance bt)
    ty ← whnf (← inferType e)
  discard <| synthInstance e

def registerCategory! (d : CatDecl) : CommandElabM Unit := do
  for cls in d.telescope do
    unless isClass (← getEnv) cls do
      throwError "category '{d.name}' names '{cls}' in its telescope, but \
that is not a class in the current environment"
  registerWith addCategoryChecked d

def registerMethod! (d : MethodDecl) : CommandElabM Unit :=
  registerWith addMethodChecked d

def registerRoute! (r : Route) : CommandElabM Unit :=
  registerWith addRouteChecked r

def registerOpSig! (s : OpSig) : CommandElabM Unit :=
  registerWith addOpSigChecked s

def registerFunctor! (f : FunctorDecl) : CommandElabM Unit :=
  registerWith addFunctorChecked f

def registerProfileRule! (r : ProfileRule) : CommandElabM Unit := do
  -- the semantic check first, so a false membership never commits
  if let some cat := catDecl? (← getEnv) r.cat then
    if !cat.telescope.isEmpty then
      if let some d := r.pattern.concreteDomain? then
        liftTermElabM do
          let T ← d.denote
          for cls in cat.telescope do
            try synthMembership cls T
            catch _ =>
              throwError "this rule claims {d.render} inhabits \
'{r.cat}', but Lean cannot synthesize {cls} at its denoted type — the \
membership is not real mathematics, so it is refused"
  registerWith addProfileRuleChecked r

def registerCanonicalMap! (r : CanonicalMap) : CommandElabM Unit :=
  registerWith addCanonicalMapChecked r

def registerRepresentative! (r : Representative) : CommandElabM Unit :=
  registerWith addRepresentativeChecked r

end CasDsl
