module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourceCell
public import CasCompiler.CategoricalPointFamily

public section

namespace CasCompiler.ReadCellRules

open Lean Meta Elab Term CasCatalogue

def component (context : ReadContext) (name : Ident)
    (parameters : Array (TSyntax `cas_term)) (receiver : TSyntax `cas_term)
    (constructors : Array Ident) (inverse : Bool) : SourceReadM NativeSourceJudgement := do
  let #[entry] := (← semanticState).cells.filter
      (·.id.raw == name.getId.toString (escape := false))
    | liftM (m := TermElabM) <| throwStratum .invalid "the selected source cell is not registered"
  let receiver ← context.readExpression context.categoryOf receiver none
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let application ← SourceReader.application context ⟨constant, none⟩ parameters none
  let mut cell ← nativeSourceCell entry application inverse
  for id in constructors.reverse do
    cell ← cell.construct ⟨id.getId.toString (escape := false)⟩
  let selected ← cell.selectedComponent receiver
  let value ← selectMorphism selected
    (fun selected expected => SourceReadM.select selected expected) (some cell.targetBundle)
  return ⟨value, selected.category⟩

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  match context.source with
  | `(cas_term| component($name:ident($parameters:cas_term,*), $receiver:cas_term,
      [$constructors:ident,*])) =>
    component context name parameters.getElems receiver constructors.getElems false
  | `(cas_term| inverse_component($name:ident($parameters:cas_term,*), $receiver:cas_term,
      [$constructors:ident,*])) =>
    component context name parameters.getElems receiver constructors.getElems true
  | _ => throwReadRuleMismatch

end CasCompiler.ReadCellRules
