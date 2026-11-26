module

public import CasCompiler.ReadContext
public import CasCompiler.SourceTuple

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadTupleRules

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  match source with
  | `(cas_term| ($first:cas_term, $rest:cas_term,*)) => do
    let some expected := expected
      | liftM (m := TermElabM) <| throwError "a source tuple requires its independently declared domain"
    let value ← sourceTuple (#[first] ++ rest.getElems) expected fun component type => do
      let phase : String → SourceReadM Unit := fun event => do
        try
          let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
          liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj [
            ("heartbeats", toJson heartbeats),
            ("startByte", toJson (component.raw.getPos?.map (·.byteIdx))),
            ("stopByte", toJson (component.raw.getTailPos?.map (·.byteIdx))),
            ("tupleStartByte", toJson (source.raw.getPos?.map (·.byteIdx))),
            ("tupleStopByte", toJson (source.raw.getTailPos?.map (·.byteIdx)))])
        catch _ => pure ()
      phase "source.tuple.component.started"
      let value ← readExpression categoryOf component (some type)
      phase "source.tuple.component.finished"
      return value.value
    pure ⟨value, none⟩
  | `(cas_term| ($inner:cas_term)) =>
    readExpression categoryOf inner expected qualification expectedCategory
  | _ => throwReadRuleMismatch

end ReadTupleRules

end CasCompiler
