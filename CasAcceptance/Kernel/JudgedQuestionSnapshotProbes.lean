/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.QuestionComparison
meta import CasCatalogue.QuestionComparison

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- These are inert claim-record controls, not mathematical acceptance assertions.
The displayed judgement and expected orientation are deliberately held fixed. -/
run_cmd liftTermElabM do
  let question : Question := .judgement "comparison" #[mkNatLit 0] #[] #[``Nat]
  let base := Claim.judged question (mkConst ``True) (some true) "first display"
  let relabeled := Claim.judged question (mkConst ``True) (some true) "other display"
  let changed := Claim.judged question (mkConst ``False) (some true) "first display"
  let (identity, _) ← claimQuestion base
  unless identity == (← claimQuestion relabeled).1 do
    throwError "display text changed a complete judged question"
  if identity == (← claimQuestion changed).1 then
    throwError "the serialized judged question omitted its actual execution proposition"
  if ← QuestionIdentity.equivalentClaim base changed then
    throwError "direct comparison omitted the judged execution proposition"
  let first ← elabTermAndSynthesize (← `((0 : Nat) = 0)) none
  let second ← elabTermAndSynthesize (← `((1 : Nat) = 1)) none
  let left := Claim.judged question first (some true) "same display"
  let right := Claim.judged question second (some true) "same display"
  if (← claimQuestion left).1 == (← claimQuestion right).1 then
    throwError "truth or provability replaced the complete judged execution proposition"
