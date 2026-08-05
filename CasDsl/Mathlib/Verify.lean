/-
Runtime availability verification (SPEC-REGISTRY-TYPE-PREPASS, invariant
I7): the category walk PROPOSES a method's availability; Mathlib DISPOSES.

`verifyResolution` re-judges a resolution at the concrete receiver: every
telescope class of the category the method is DECLARED on must synthesize
at the receiver's denoted type. Registration already checks concrete
profile rules, so this firing means the walk and Mathlib disagree — a
family-pattern membership that does not actually hold, a corrupted
registry, or a Mathlib change. The disagreement surfaces as an error at the
call, never as a silently granted method.
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
  | _ => none

/-- `none` = verified (or not judgeable: empty telescope, no denoted type);
`some cls` = the class that failed to synthesize at the receiver. -/
def verifyResolution (env : Environment) (declaredOn : Name) (concrete : Obj)
    : IO (Option Name) := do
  let some cat := catDecl? env declaredOn | return none
  if cat.telescope.isEmpty then return none
  let some d := receiverDomain? concrete | return none
  runSemanticCheck env do
    let T ← d.denote
    for cls in cat.telescope do
      try synthMembership cls T
      catch _ => return some cls
    return none

end CasDsl
