/-
Runtime typing verification (SPEC-REGISTRY-TYPE-PREPASS, invariant I7): a typing rule over a
family of domains PROPOSES the category a value is constructed in; Mathlib DISPOSES, at the
concrete receiver. A disagreement surfaces as an error at the call, never as a silently granted
method.
-/
import CasDsl.Mathlib.Denote
import CasDsl.Registry

namespace CasDsl

open Lean Meta

/-- Run a `MetaM` check against a bare environment from `IO`. -/
def runSemanticCheck (env : Environment) (x : MetaM α) : IO α := do
  let ((a, _), _) ← (x.run).toIO
    { fileName := "<casdsl-semantics>", fileMap := default } { env }
  return a

/-- The domain a receiver's availability is judged at, when it has one.
Presentations without a single denoted type (finite sets, spans, cosets)
are judged by their category's structure alone. -/
private def receiverDomain? : Obj → Option Domain
  | .elem d _ => some d
  | .domainObj d => some d
  | .cyclicModule n => some (.mod n)
  | _ => none

/-- Verify a typing at a concrete receiver: every class of the rule must synthesize at the
receiver's denoted domain. `none` = verified (or nothing to judge: no classes, no denoted domain);
`some cls` = the class that failed. Registration already verifies rules over a concrete domain, so
this fires only for a family rule (`polyOver anyDom`) that does not hold at this member. -/
def verifyTyping (env : Environment) (classes : Array Name) (o : Obj) : IO (Option Name) := do
  let some d := receiverDomain? o | return none
  runSemanticCheck env do
    let T ← d.denote
    for cls in classes do
      try synthMembership cls T
      catch _ => return some cls
    return none

end CasDsl
