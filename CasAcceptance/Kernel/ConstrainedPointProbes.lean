module

import CasCatalogue.ConstrainedPoint
meta import CasCatalogue.ConstrainedPoint

open Lean Meta Elab Term CasCatalogue

/- Engineering checks of constructor introspection, full dependent endpoints and proof
checking. No computational implementation or permanent mathematical answer is used. -/
run_elab do
  let target ← elabTermAndSynthesize (← `({ n : Nat // n = n })) none
  let original ← elabTermAndSynthesize (← `(fun n : Nat => n)) none
  let proof ← elabTermAndSynthesize (← `(fun n : Nat => Eq.refl n)) none
  let result ← ConstrainedPoint.construct target original #[proof]
  unless result.schema.constructor == ``Subtype.mk &&
      (← isDefEq result.domain (mkConst ``Nat)) &&
      (← isDefEq result.schema.dataType (mkConst ``Nat)) &&
      (← isDefEq (← ConstrainedPoint.project result.schema result.value) original) do
    throwError "the constrained constructor changed its generalized domain or original data"

  let constantTarget ← elabTermAndSynthesize (← `({ n : Nat // n = 0 })) none
  let constant ← elabTermAndSynthesize (← `(fun _ : Nat => (0 : Nat))) none
  let constantProof ← elabTermAndSynthesize (← `(Eq.refl (0 : Nat))) none
  let constantResult ← ConstrainedPoint.construct constantTarget constant #[constantProof]
  unless ← isDefEq (← ConstrainedPoint.project constantResult.schema constantResult.value)
      constant do
    throwError "a constant proof replaced the original generalized point"

  let reject (action : MetaM Unit) : TermElabM Unit := do
    let rejected ← try action; pure false catch error =>
      if CasCatalogue.Exception.stratum? error == some .invalid then pure true else throw error
    unless rejected do throwError "an incompatible constrained point was admitted"
  let wrongData ← elabTermAndSynthesize (← `(fun b : Bool => b)) none
  reject do discard <| ConstrainedPoint.construct target wrongData #[proof]
  let wrongProof ← elabTermAndSynthesize (← `(True.intro)) none
  reject do discard <| ConstrainedPoint.construct target original #[wrongProof]
  reject do discard <| ConstrainedPoint.construct target original #[proof, proof]

  -- An infinite generalized obligation is not replaced by a proof at one sample point.
  reject do discard <| ConstrainedPoint.construct constantTarget original #[constantProof]

  -- Unknown proof obligations remain interpreter errors, distinct from a proved violation.
  let unknown ← try
    discard <| ConstrainedPoint.construct target original
    pure false
  catch error => pure ((CasCatalogue.Exception.stratum? error).isNone)
  unless unknown do throwError "an unresolved generalized proof acquired a semantic failure label"

  for typeSyntax in #[← `(Nat × Nat), ← `(List Nat), ← `(Nat → Nat)] do
    let type ← elabTermAndSynthesize typeSyntax none
    unless (← ConstrainedPoint.schema? type).isNone do
      throwError "a multi-data, recursive, or callable type acquired a constrained-record schema"
