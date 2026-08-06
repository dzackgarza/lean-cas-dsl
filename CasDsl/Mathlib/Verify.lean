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
  | .cyclicModule n => some (.mod n)
  | _ => none

/-- `none` = verified (or not judgeable: empty telescopes, no denoted
type); `some cls` = the class that failed to synthesize at the receiver.

The ENTRY category's telescopes are judged when they claim anything — with
every inclusion edge a registration-time theorem, the entry membership
grounds the whole displayed chain. A claimless entry (a family-pattern
category) falls back to the declaring category's telescopes, so the walk
still cannot grant what Mathlib refuses.

Two layers, one judgment: `telescope` classes synthesize at the member's
denoted carrier (`Countable ℚ`), `paramTelescope` classes at the entry's
ring parameter and the carrier together (`Module ℤ (ZMod n)`). -/
def verifyResolution (env : Environment) (entry : CatRef) (declaredOn : Name)
    (concrete : Obj) : IO (Option Name) := do
  let telescopesOf (n : Name) : Array Name × Array Name :=
    match catDecl? env n with
    | some d => (d.telescope, d.paramTelescope)
    | none => (#[], #[])
  let (etel, eptel) := telescopesOf entry.name
  let (tel, ptel) :=
    if etel.isEmpty && eptel.isEmpty then telescopesOf declaredOn
    else (etel, eptel)
  if tel.isEmpty && ptel.isEmpty then return none
  let some d := receiverDomain? concrete | return none
  runSemanticCheck env do
    let T ← d.denote
    for cls in tel do
      try synthMembership cls T
      catch _ => return some cls
    if !ptel.isEmpty then
      -- the entry's params ride inclusion edges unchanged, so they are the
      -- right instantiation even when the claim fell back to `declaredOn`
      if let some (ParamVal.dom pd) := entry.params[0]? then
        let P ← pd.denote
        for cls in ptel do
          try synthMembershipAt cls #[P, T]
          catch _ => return some cls
    return none

end CasDsl
