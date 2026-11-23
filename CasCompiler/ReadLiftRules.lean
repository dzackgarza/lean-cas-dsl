module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourcePresentation
public import CasCompiler.SourceLift

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadLiftRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let application := application context
  match source with
  | `(cas_term| map $point:cas_term along $name:ident) => do
    let selected ← sourcePresentation name.getId.toString false fun declaration =>
      application ⟨declaration, none⟩ #[] none
    return ⟨← application selected #[point] context.expected, none⟩
  | `(cas_term| map $point:cas_term back along $name:ident) => do
    let selected ← sourcePresentation name.getId.toString true fun declaration =>
      application ⟨declaration, none⟩ #[] none
    return ⟨← application selected #[point] context.expected, none⟩
  | `(cas_term| presentation($name:ident($arguments:cas_term,*))) =>
    sourcePresentation name.getId.toString false fun declaration =>
      application ⟨declaration, none⟩ arguments.getElems none
  | `(cas_term| inverse_presentation($name:ident($arguments:cas_term,*))) =>
    sourcePresentation name.getId.toString true fun declaration =>
      application ⟨declaration, none⟩ arguments.getElems none
  | `(cas_term| lift($receiver:cas_term) along $id:ident($arguments:cas_term,*)
      with $input:cas_term using $evidence:cas_term) => do
    let state ← CasCatalogue.semanticState
    let #[row] := state.lifts.filter
      (·.id.raw == id.getId.toString (escape := false))
      | throwError "selected source lifting requires one registered lift"
    discard <| checkedDeclaration row.evidence
    if let some computation := row.computation then discard <| checkedDeclaration computation
    checkEdgeDeclarations state row.edge
    CasCatalogue.validateLift state row
    let receiver ← readExpression categoryOf receiver none
    let selected ← application ⟨← mkConstWithFreshMVarLevels row.evidence, none⟩
      arguments.getElems none
    let input ← readExpression categoryOf input none
    let `(cas_term| proof($proof:term)) := evidence
      | throwError "a selected lift requires explicit native monicity evidence"
    let proof ← elabTermEnsuringType proof none
    sourceSelectedLift row receiver input selected proof
  | `(cas_term| factor($base:cas_term) through $lift:cas_term with $source:cas_term
      using $evidence:cas_term) => do
    let lift ← readExpression categoryOf lift none
    let base ← readExpression categoryOf base none
    let source ← readExpression categoryOf source none
    let `(cas_term| proof($proof:term)) := evidence
      | throwError "a source factor requires its explicit native equation"
    let proof ← elabTermEnsuringType proof none
    sourceLiftFactor lift base.value source.value proof
  | _ => throwReadRuleMismatch

end ReadLiftRules

end CasCompiler
