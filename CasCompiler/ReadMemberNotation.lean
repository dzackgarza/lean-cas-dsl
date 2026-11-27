module

public import CasCompiler.ReadContext
public import CasCompiler.ReadMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadMemberNotation

open SourceReader

def ruleCompleting (context : ReadContext) (complete : ReadCompletion) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let source := context.source
  let member := memberCompleting context complete
  if source.raw.getKind == ``CasCatalogue.Language.casCallWith then do
    let arguments := source.raw[4].getSepArgs.map fun argument =>
      (⟨argument⟩ : TSyntax `cas_term)
    member ⟨source.raw[0]⟩ (source.raw[2].getId.toString (escape := false)) arguments
  else throwReadRuleMismatch

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  match ← ruleCompleting context (fun value => pure (.ok value)) with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end ReadMemberNotation

end CasCompiler
