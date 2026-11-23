module

public import CasCompiler.ReadContext
public import CasCompiler.SourceLift
public import CasCompiler.SourceLimit
public import CasCompiler.SourceSubobject

public section

namespace CasCompiler
open Lean Meta Elab Term

/-- Projection syntax consumes the independently registered construction interface. -/
def readProjection (receiver : NativeSourceJudgement) (name : String)
    (arguments : Array (TSyntax `cas_term)) : TermElabM (Option NativeSourceJudgement) := do
  if let some value ← sourceLiftMember? receiver name then
    unless arguments.isEmpty do
      throwError "a selected lift projection takes no additional source arguments"
    return some value
  if let some value ← sourceSubobjectMember? receiver name then
    unless arguments.isEmpty do
      throwError "a selected subobject projection takes no additional source arguments"
    return some value
  -- `K.leg(j)`: a defining leg of a registered limit or colimit.
  if name == "leg" then
    if let #[index] := arguments then
      if let `(cas_term| $ordinal:num) := index then
        if let some leg ← sourceLimitLeg? receiver ordinal.getNat then return some leg
  return none

end CasCompiler
