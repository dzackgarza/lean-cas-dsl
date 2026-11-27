module

public import CasCompiler.Surface
public import CasCompiler.SourceTuple
public import CasCompiler.Syntax

public section

namespace CasCompiler

open Lean Meta Elab Term

private inductive SourcePattern where
  | name (identifier : Ident)
  | tuple (source : Syntax) (components : Array SourcePattern)

private partial def sourcePattern (source : TSyntax `cas_term) : TermElabM SourcePattern :=
  match source with
  | `(cas_term| $name:ident) => return .name name
  | `(cas_term| ($first:cas_term, $rest:cas_term,*)) => do
    return .tuple source.raw (← (#[first] ++ rest.getElems).mapM sourcePattern)
  | `(cas_term| ($inner:cas_term)) => sourcePattern inner
  | _ => throwErrorAt source "a source binding pattern must contain names or tuple patterns"

private partial def patternNames (pattern : SourcePattern) : Array Ident :=
  match pattern with
  | .name name => #[name]
  | .tuple _ components => components.flatMap patternNames



private def componentValues (source : Syntax) (value : Expr) (count : Nat) :
    SourceReadM (Array Expr) := SourceReadM.withRef source do
  let phase : String → SourceReadM Unit := fun event => do
    try
      let scope ← get
      let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
      liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj [
        ("heartbeats", toJson heartbeats),
        ("contextBindings", toJson scope.context.bindings.size),
        ("formals", toJson scope.formals.size)])
    catch _ => pure ()
  phase "source.pattern.components.started"
  let components ← sourceComponentValues value count
  phase "source.pattern.components.finished"
  if let some values := components then return values
  phase "source.pattern.view.started"
  let originalType ← inferType value
  let type ← nativeTypeView originalType
  phase "source.pattern.view.finished"
  phase "source.pattern.select.started"
  let value ← if type.equal originalType then pure value else do
    let selected := (← SourceReadM.selection? value).getD { value }
    SourceReadM.select { selected with value } (some type)
  phase "source.pattern.select.finished"
  if let .forallE _ index _ _ := type then
    let index ← whnf index
    if index.isAppOfArity ``Fin 1 then


      return (← sourceFiniteIndices index.getAppArgs[0]! count).map (mkApp value)
  let (first, second) ←
    if type.isAppOfArity ``Prod 2 then pure (``Prod.fst, ``Prod.snd)
    else if type.isAppOfArity ``Sigma 2 then pure (``Sigma.fst, ``Sigma.snd)
    else if type.isAppOfArity ``PSigma 2 then pure (``PSigma.fst, ``PSigma.snd)
    else
      liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
        m!"source pattern binding is not implemented for domain {← inferType value}"
  unless count == 2 do
    liftM (m := TermElabM) <| throwError "a native pair pattern must have its declared pair of components"
  return #[← mkAppM first #[value], ← mkAppM second #[value]]




private partial def bindPattern (pattern : SourcePattern) (value : Expr)
    (body : SourceReadM Expr) : SourceReadM Expr := do
  match pattern with
  | .name name =>
    SourceReadM.withLet name.getId (← inferType value) value fun _ => body
  | .tuple source components =>
    let values ← componentValues source value components.size
    (components.zip values).foldr
      (fun (pattern, value) body => bindPattern pattern value body) body




opaque sourcePatternLambda (source : TSyntax `cas_term) (domain : Expr) (info : BinderInfo)
    (body : Expr → SourceReadM Expr) : SourceReadM Expr := do
  let pattern ← sourcePattern source
  let mut names := #[]
  for name in patternNames pattern do
    if names.contains name.getId then
      liftM (m := TermElabM) <| throwErrorAt name "a source tuple pattern repeats a bound name"
    names := names.push name.getId
  match pattern with
  | .name name =>
    SourceReadM.withLambda name.getId domain info body
  | .tuple _ _ =>
    SourceReadM.withLambda (← mkFreshUserName `argument) domain info fun parameter =>
      bindPattern pattern parameter (body parameter)

end CasCompiler
