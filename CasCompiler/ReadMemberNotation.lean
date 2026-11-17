module

public import CasCompiler.ReadContext
public import CasCompiler.ReadMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadMemberNotation

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let source := context.source
  let member := member context
  if source.raw.getKind == ``CasCatalogue.Language.casCallWith then do
    let arguments := source.raw[4].getSepArgs.map fun argument =>
      (⟨argument⟩ : TSyntax `cas_term)
    member ⟨source.raw[0]⟩ (source.raw[2].getId.toString (escape := false)) arguments
  else throwReadRuleMismatch

end ReadMemberNotation

end CasCompiler
