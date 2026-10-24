module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/- The language preserves an original whole map through a supplied constrained
constructor. The fixture uses only the public set-map and record interfaces. -/
run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted set category is absent"
  let source := mkConst ``Nat
  let data : Value := .object source sets none none none
  let targetType ← elabTermAndSynthesize (← `({ n : Nat // n = n })) none
  let target : Value := .object targetType sets none none none
  let original ← elabTermAndSynthesize
    (← `(id (α := TypeCat.Hom Nat Nat) (TypeCat.ofHom (fun n : Nat => n)))) none
  unless (← inferType original).getAppFn.isConstOf ``TypeCat.Hom do
    throwError "the fixture no longer checks a bundled Hom presentation"
  let originalValue : Value := .morphism original source source sets (some (data, data))
  let proofSyntax ← `(by intro n; rfl)
  let trace ← Trace.new
  (show M Unit from do
    let result ← admitConstrainedPoint target originalValue #[proofSyntax]
    let (point, domain, endpoint, _, domainValue, targetValue) ← morphismContext result
    unless ← isDefEq domain source <&&> isDefEq endpoint targetType <&&>
        isDefEq (← semanticObject domainValue) source <&&>
        isDefEq (← semanticObject targetValue) targetType do
      throwError "the constrained map changed its full endpoints or retained objects"
    let some schema ← ConstrainedPoint.schema? targetType
      | throwError "the supplied constructor schema disappeared"
    unless ← isDefEq (← ConstrainedPoint.project schema (← functionOf point))
        (← functionOf original) do
      throwError "the constrained map changed its complete original function"
    let some (.constrainedPoint constructor category retainedDomain retainedData retainedTarget
        retainedOriginal) ← trace.node? point
      | throwError "the constrained map lost its computational reconstruction trace"
    unless constructor == schema.constructor && category == sets.id &&
        (← isDefEq retainedDomain source) && (← isDefEq retainedData source) &&
        (← isDefEq retainedTarget targetType) && retainedOriginal == original do
      throwError "the constrained map trace replaced an original input"

    let element ← admitConstrainedPoint target (.element original data) #[proofSyntax]
    let .element elementPoint elementTarget := element
      | throwError "a generalized element was changed into a map value"
    unless ← isDefEq (← functionOf elementPoint) (← functionOf point) <&&>
        isDefEq (← semanticObject elementTarget) targetType do
      throwError "the element and map paths changed their shared constrained function"

    let falseTargetType ← elabTermAndSynthesize (← `({ n : Nat // n = 0 })) none
    let falseTarget : Value := .object falseTargetType sets none none none
    let onePointProof ← `(Eq.refl (0 : Nat))
    let accepted ← parameterCompatible do
      discard <| admitConstrainedPoint falseTarget originalValue #[onePointProof]
      pure true
    unless !accepted do
      throwError "a single-point proof admitted a false whole-function condition"

    let wrong : Value := .morphism original source source sets
      (some (.object (mkConst ``Bool) sets none none none, data))
    let accepted ← parameterCompatible do
      discard <| admitConstrainedPoint target wrong #[proofSyntax]
      pure true
    unless !accepted do
      throwError "a constrained map accepted incompatible retained source metadata"
  ).run { trace := some trace }
