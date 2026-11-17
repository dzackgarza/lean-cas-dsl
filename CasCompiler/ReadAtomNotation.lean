module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadAtomNotation

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let source := context.source
  let qualification := context.qualification
  let object := object context
  if let some name := sourceAtomName? source then
    object name qualification #[]
  else throwReadRuleMismatch

end ReadAtomNotation

end CasCompiler
