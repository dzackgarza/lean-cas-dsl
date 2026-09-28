/-
Elaboration-time registration helpers: the checked adders of
`Registry.lean` lifted into `CommandElabM`, plus the SEMANTIC checks the
pure adders cannot perform (SPEC-REGISTRY-TYPE-PREPASS, invariant I1).

Load-bearing decision: registration failure is an ELABORATION error, not a
runtime one. A clash in the prelude therefore fails `lake build` — the
standard universe cannot ship half-registered, and a notebook can never
observe a registry that silently dropped or overwrote a declaration.

The semantic checks added here are the anti-lie layer: a typing rule names a
registered `CasCatalogue` category and the Mathlib classes its claim needs, and
a rule whose pattern names a CONCRETE domain is admitted only when every class
synthesizes at the domain's denoted type. A typing Lean cannot discharge fails
the build.

These are ordinary `CommandElabM` actions, used from `run_cmd` blocks (see
`CasDsl/Std.lean`); no new command syntax is introduced, so registrations
read as data and stay `#print`-able Lean values.
-/
import Lean
import CasDsl.Registry
import CasDsl.Mathlib.Denote
import CasDsl.Mathlib.Anchors
import CasCatalogue.Standard

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
  | .finiteSetOver p => p.concrete?
  | _ => none

def registerMethod! (d : MethodDecl) : CommandElabM Unit := do
  unless d.anchor == .anonymous do
    unless (← getEnv).contains d.anchor do
      throwError "method '{d.id}' anchors its meaning to '{d.anchor}', but \
no such constant exists — the anchor must be real Mathlib (or extension) \
mathematics"
  registerWith addMethodChecked d

/-- A fused route claims to realize one semantic composite (CC-ROUTE): its method must be a
registered method row of the route's method name, and its steps a registered structural route from
some registered category to that method's owner. -/
def checkFusedRoute (r : Route) : CommandElabM Unit := do
  let some (methodId, steps) := r.realizes | return
  let state ← liftTermElabM CasCatalogue.registryState
  -- a property query (CC-PROP): the composite ends at the host of the property's classifier
  if let some property := state.properties.find? (·.id.raw == methodId) then
    unless property.name == r.method.toString do
      throwError "fused route for '{r.method}' claims to realize {methodId}, the property \
        `{property.name}`"
    let some classifier := state.classifier? property.classifier
      | throwError "fused route for '{r.method}': {methodId} has no registered classifier"
    let realized := state.categories.any fun c =>
      (state.routes c.expression classifier.host).any fun route =>
        route.refs.map (·.label) == steps
    unless realized do
      throwError "fused route for '{r.method}': {steps} is not a registered route to the host \
        of {methodId}'s classifier"
    return
  let some method := state.methods.find? (·.id.raw == methodId)
    | throwError "fused route for '{r.method}': no registered method {methodId}"
  unless method.name == r.method.toString do
    throwError "fused route for '{r.method}' claims to realize {methodId}, the method \
      `{method.name}`"
  let realized := state.categories.any fun c =>
    (state.routes c.expression method.owner).any fun route =>
      route.refs.map (·.label) == steps
  unless realized do
    throwError "fused route for '{r.method}': {steps} is not a registered route to the owner \
      of {methodId}"

def registerRoute! (r : Route) : CommandElabM Unit := do
  checkFusedRoute r
  registerWith addRouteChecked r

def registerOpSig! (s : OpSig) : CommandElabM Unit :=
  registerWith addOpSigChecked s

/-- Register a typing rule. Its category must be registered in `CasCatalogue`, and when the
pattern names a concrete domain, every class of the rule must synthesize at the domain's denoted
type: a typing Lean cannot discharge is not real mathematics, so it is refused. -/
def registerTypingRule! (r : TypingRule) : CommandElabM Unit := do
  let state ← liftTermElabM CasCatalogue.registryState
  unless state.categories.any (·.id.raw == r.category) do
    throwError "typing rule for {repr r.pattern}: no registered category {r.category}"
  for cls in r.classes do
    unless isClass (← getEnv) cls do
      throwError "typing rule for {repr r.pattern} names '{cls}', which is not a class"
  if let some d := r.pattern.concreteDomain? then
    liftTermElabM do
      let T ← d.denote
      for cls in r.classes do
        try synthMembership cls T
        catch _ =>
          throwError "this rule types {d.render} in {r.category}, but Lean cannot synthesize \
{cls} at its denoted type — the claim is not real mathematics, so it is refused"
  registerWith addTypingRuleChecked r

def registerCanonicalMap! (r : CanonicalMap) : CommandElabM Unit :=
  registerWith addCanonicalMapChecked r

def registerRepresentative! (r : Representative) : CommandElabM Unit :=
  registerWith addRepresentativeChecked r

end CasDsl
