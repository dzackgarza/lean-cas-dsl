module

public import CasCompiler.CategoricalPointFamily
public import CasCompiler.PublishedPorts
public import CasCompiler.SelectionScope

public section

namespace CasCompiler

open Lean Meta CasCatalogue



def CategoricalPointFamily.ofSelection? (selection : SourceSelection Expr) :
    MetaM (Option (CategoricalPointFamily × List Level × Array Expr)) := do
  let some application := selection.application | return none
  let .point family := application.family | return none
  unless selection.formalBindings.isEmpty &&
      application.universes.length == family.universeParams.length &&
      application.parameters.size == family.parameterCount &&
      application.arguments.size == (if family.invocation then 2 else 0) do
    throwError "the categorical point lost its complete original argument telescope"
  if let some request := selection.pointRequest then
    let .categorical original _ := request
      | throwError "the categorical point changed its original request kind"
    unless (SelectedApplicationFamily.point family).exactlyMatches (.point original) do
      throwError "the categorical point changed its original selected request family"
  return some (family, application.universes, application.parameters)



def categoricalPointSource? (context : OpenContext) (scope : SourceSelectionScope Expr)
    (expression : Expr) : MetaM (Option (SourceSelection Expr)) := do
  let some selected := scope.findAt? context expression.getAppFn | return none
  let selected ← selected.specialize expression.getAppArgs
  let some _ ← CategoricalPointFamily.ofSelection? selected | return none
  return some selected



def SourceActionFamily.ofSelection? (selection : SourceSelection Expr) :
    MetaM (Option (SourceActionFamily × List Level × Array Expr × Expr)) := do
  let some application := selection.application | return none
  let .objectAction family := application.family | return none
  unless selection.formalBindings.isEmpty &&
      application.universes.length == family.universeParams.length &&
      application.parameters.size == family.parameterCount do
    throwError "the object action lost its complete original argument telescope"
  let #[receiver] := application.arguments
    | throwError "the object action changed its exact original receiver slot"
  return some (family, application.universes, application.parameters, receiver)

end CasCompiler
