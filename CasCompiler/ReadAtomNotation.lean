module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadAtomNotation

open SourceReader

def ruleApplicable (context : ReadContext) :
    TermElabM (Except MessageData NativeSourceJudgement) := do
  let source := context.source
  let qualification := context.qualification
  let object := objectApplicable context
  if let some name := sourceAtomName? source then
    object name qualification #[]
  else throwReadRuleMismatch

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  match ← ruleApplicable context with
  | .ok value => pure value
  | .error message => throwError message

end ReadAtomNotation

end CasCompiler
