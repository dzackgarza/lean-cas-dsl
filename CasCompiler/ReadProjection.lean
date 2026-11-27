module

public import CasCompiler.ReadContext
public import CasCompiler.SourceLift
public import CasCompiler.SourceLimit
public import CasCompiler.SourceSubobject

public section

namespace CasCompiler
open Lean Meta Elab Term


def readProjection (receiver : NativeSourceJudgement) (name : String)
    (arguments : Array (TSyntax `cas_term)) : SourceReadM (Option NativeSourceJudgement) := do
  if let some value ← sourceLiftMember? receiver name then
    unless arguments.isEmpty do
      liftM (m := TermElabM) <| throwError "a selected lift projection takes no additional source arguments"
    return some value
  if let some value ← sourceSubobjectMember? receiver name then
    unless arguments.isEmpty do
      liftM (m := TermElabM) <| throwError "a selected subobject projection takes no additional source arguments"
    return some value

  if name == "leg" then
    if let #[index] := arguments then
      if let `(cas_term| $ordinal:num) := index then
        if let some leg ← sourceLimitLeg? receiver ordinal.getNat then return some leg
  return none

end CasCompiler
