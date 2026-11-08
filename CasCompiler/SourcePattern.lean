module

public import CasCompiler.Surface

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

-- Native pair projections apply only after exact registered-component lookup.
-- Reuse: Lean's Prod/Sigma/PSigma projections and the declared ObjectComponents maps.
private def componentValues (source : Syntax) (value : Expr) (count : Nat) :
    TermElabM (Array Expr) := withRef source do
  if let some values ← sourceComponentValues value count then return values
  let type ← whnf (← inferType value)
  let (first, second) ←
    if type.isAppOfArity ``Prod 2 then pure (``Prod.fst, ``Prod.snd)
    else if type.isAppOfArity ``Sigma 2 then pure (``Sigma.fst, ``Sigma.snd)
    else if type.isAppOfArity ``PSigma 2 then pure (``PSigma.fst, ``PSigma.snd)
    else
      CasCatalogue.throwUnsupportedSource
        m!"source pattern binding is not implemented for domain {← inferType value}"
  unless count == 2 do
    throwError "a native pair pattern must have its declared pair of components"
  return #[← mkAppM first #[value], ← mkAppM second #[value]]

-- Each pattern name is a native let at its actual projection. Close those lets in
-- order, including unused components, before closing the enclosing function binder.
-- Reuse: Lean.Meta.withLetDecl/mkLetFVars and metavariable-aware native abstraction.
private partial def bindPattern (pattern : SourcePattern) (value : Expr)
    (body : TermElabM Expr) : TermElabM Expr := do
  match pattern with
  | .name name =>
    withLetDecl name.getId (← inferType value) value fun binding => do
      mkLetFVars #[binding] (← body) (usedLetOnly := false) (generalizeNondepLet := false)
  | .tuple source components =>
    let values ← componentValues source value components.size
    (components.zip values).foldr
      (fun (pattern, value) body => bindPattern pattern value body) body

/-- Form a native lambda at its independently specified domain, with recursive source patterns.
Source: casPatternLambda and ObjectComponents. Native local declarations preserve lexical
shadowing, selected instance binders and captures; no source expression is replayed. -/
opaque sourcePatternLambda (source : TSyntax `cas_term) (domain : Expr) (info : BinderInfo)
    (body : Expr → TermElabM Expr) : TermElabM Expr := do
  let pattern ← sourcePattern source
  let mut names := #[]
  for name in patternNames pattern do
    if names.contains name.getId then
      throwErrorAt name "a source tuple pattern repeats a bound name"
    names := names.push name.getId
  match pattern with
  | .name name =>
    withLocalDecl name.getId info domain fun parameter => do
      mkLambdaFVars #[parameter] (← body parameter)
  | .tuple _ _ =>
    withLocalDecl (← mkFreshUserName `argument) info domain fun parameter => do
      mkLambdaFVars #[parameter] (← bindPattern pattern parameter (body parameter))

end CasCompiler
