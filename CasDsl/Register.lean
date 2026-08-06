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

def registerCategory! (d : CatDecl) : CommandElabM Unit := do
  if d.anchor == .anonymous then
    throwError "category '{d.name}' denotes nothing in Mathlib — a node \
must name the category it means (or the constant defining it), and a name \
with no mathematics behind it is not registrable"
  unless (← getEnv).contains d.anchor do
    throwError "category '{d.name}' anchors its meaning to '{d.anchor}', \
but that constant is not in the current environment"
  for cls in d.telescope ++ d.paramTelescope do
    unless isClass (← getEnv) cls do
      throwError "category '{d.name}' names '{cls}' in its telescope, but \
that is not a class in the current environment"
  -- an inclusion edge is the inclusion functor `child ↪ parent`; its
  -- object-level content — the instance implication — is discharged here,
  -- so the rendered `child ≤ parent` chain never claims what Lean cannot prove
  for p in d.parents do
    let some parent := catDecl? (← getEnv) p
      | throwError "category '{d.name}' names an unregistered parent '{p}'"
    unless parent.telescope.isEmpty do
      if d.telescope.isEmpty then
        throwError "the edge '{d.name}' ≤ '{p}' claims {parent.telescope} \
from a category with no telescope — an implication from nothing, which is \
not a theorem"
      match ← liftTermElabM (synthEdgeImplication d.telescope parent.telescope) with
      | none => pure ()
      | some cls =>
          throwError "the edge '{d.name}' ≤ '{p}' is not a theorem: Lean \
cannot derive {cls} from {d.telescope}"
    -- the ring-parameterized layer: the child must claim every class the
    -- parent claims — subset is the discharged implication here; a
    -- quantified two-type derivation is the catalogue's game
    for cls in parent.paramTelescope do
      unless d.paramTelescope.contains cls do
        throwError "the edge '{d.name}' ≤ '{p}' is not a theorem at the \
ring parameter: '{p}' claims {cls}, which '{d.name}' does not"
  registerWith addCategoryChecked d

def registerMethod! (d : MethodDecl) : CommandElabM Unit := do
  unless d.anchor == .anonymous do
    unless (← getEnv).contains d.anchor do
      throwError "method '{d.id}' anchors its meaning to '{d.anchor}', but \
no such constant exists — the anchor must be real Mathlib (or extension) \
mathematics"
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
