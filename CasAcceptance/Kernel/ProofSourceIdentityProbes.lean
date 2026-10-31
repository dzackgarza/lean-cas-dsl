/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Engineering controls for exact source identity of explicit proof syntax. -/

open Lean Meta Elab Command Term CasCatalogue CasCatalogue.Language

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let first : TSyntax `term ← `(by trivial)
  let second : TSyntax `term ← `(True.intro)
  let value := Value.formalProof first.raw
  unless value.sameSource value do
    throwError "an exact explicit proof source is not reflexive"
  if value.sameSource (.formalProof second.raw) then
    throwError "different proof presentations were identified"
  let left := mkIdent (Lean.addMacroScope `ProofSource `h 11)
  let right := mkIdent (Lean.addMacroScope `ProofSource `h 12)
  unless left.getId.eraseMacroScopes == right.getId.eraseMacroScopes &&
      left.getId != right.getId do
    throwError "the lexical proof control has no distinct scopes"
  if (Value.formalProof left).sameSource (.formalProof right) then
    throwError "different lexical proof scopes were identified"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
      "PrimeResidues(5, proof(by decide))"
    | throwError "the proof-bearing source control did not parse"
  let original ← (eval {} parsed).run {}
  unless original.sameSource original do
    throwError "a complete proof-bearing constructor lost exact source identity"
  let witnesses := sourceParameterValues original
  unless witnesses.any (fun value => value matches .formalProof _) do
    throwError "the constructor control retained no explicit proof input"
  let repeated := collectSourceParameterValues [original, original] #[]
  unless repeated.size == witnesses.size &&
      (repeated.zip witnesses).all (fun (left, right) => left.sameSource right) do
    throwError "repeated exact constructor sources expanded their context"
  let retained := retainObjectContext original #[original]
  unless retained.sameSource original do
    throwError "retaining the exact constructor changed its complete source"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let expected ← elabTermAndSynthesize (← `(Invertible (1 : ℚ))) none
  if ← isProp expected then
    throwError "the inverse witness control is proposition-valued"
  let proof : TSyntax `term ← `(by infer_instance)
  let rejected ← try
      discard <| (typedParameter expected (.formalProof proof.raw)).run {}
      pure false
    catch error =>
      if Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do
    throwError "explicit proof syntax supplied Type-valued inverse data"
