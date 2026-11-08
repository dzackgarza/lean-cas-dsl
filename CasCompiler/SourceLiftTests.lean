module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Meta Elab Term CasCompiler

universe u₁ u₂ v₁ v₂

-- The native layout retains independent object and morphism universes at both boundaries.
example {C : Type u₁} {D : Type u₂} [CategoryTheory.Category.{v₁} C]
    [CategoryTheory.Category.{v₂} D] (U : CategoryTheory.Functor C D)
    (selected : CasCatalogue.MonoLift U) (X : C) (K : D)
    (i : K ⟶ U.obj X) (monicity : CategoryTheory.Mono i) : SourceLiftApplication U :=
  ⟨selected, X, K, i, monicity⟩

-- Reuse the original selected application and accepted MonoLift projection terms.
-- This checks native source translation, without deciding any acceptance question.
run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let mut observed := #[]
  let mut questions := #[]
  for item in file.items do
    if let `(cas_item| test $id:ident $_:str : assert $body:cas_term) := item then
      let text := id.getId.toString (escape := false)
      let native := if text.endsWith ".first_inverse_on_carrier" then
          some "CategoryTheory.CategoryStruct.comp alpha1 beta1 = CategoryTheory.CategoryStruct.id firstCarrier"
        else if text.endsWith ".first_inverse_on_scalar" then
          some "CategoryTheory.CategoryStruct.comp beta1 alpha1 = CategoryTheory.CategoryStruct.id scalarModule"
        else none
      if let some native := native then
        let .ok parsed := Parser.runParserCategory (← getEnv) `term native
          | throwError "the native composed-map proposition did not parse"
        let expected ← session.term ⟨parsed⟩
        let question ← file.withContext (session.readQuestion body)
        question.source.withOpen fun bindings expression => do
          let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
          unless ← isDefEq expression expected do
            throwError "the original inverse equation changed its complete native reading"
          checkWithKernel
            (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
        questions := questions.push text
      continue
    let `(cas_item| $statement:cas_stmt) := item | continue
    if let `(cas_stmt| assert $_:cas_term) := statement then continue
    let name ← match statement with
      | `(cas_stmt| let $name:ident := $_:cas_term) => pure name.getId
      | `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) => pure name.getId
      | _ => continue
    let .definition next value ← file.withContext (session.readStatement statement)
      | throwError "the original selected lift did not extend its source context"
    unless value.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
      throwError "the selected lift shortened its original ordered context"
    let expectedName := match name with
      | `X1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstObject"
      | `i1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstInclusion"
      | `alpha1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.alpha"
      | `beta1 => some "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.beta"
      | `unscaledRaw => some "(![(4 : ℚ), (-4 : ℚ)])"
      | _ => none
    if let some expectedName := expectedName then
      let .ok parsed := Parser.runParserCategory (← getEnv) `term expectedName
        | throwError "the owned lift projection did not parse"
      let expected ← session.term ⟨parsed⟩
      value.source.withOpen fun bindings expression => do
        let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
        unless ← isDefEq expression expected do
          throwError "the original lift projection {name} changed its selected native application"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
      observed := observed.push name
    session := next
    if name == `i0 then
      for (input, proof, detail) in #[
          ("i0", "True.intro", "explicit monicity evidence"),
          ("underlyingF",
            "CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono",
            "different original inclusion")] do
        let text := "lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with " ++
          input ++ " using proof(" ++ proof ++ ")"
        let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
          | throwError "the selected lift evidence control did not parse"
        let rejected ← withoutModifyingState do
          try
            discard <| session.read ⟨parsed⟩
            pure false
          catch error =>
            let message ← error.toMessageData.toString
            unless (message.splitOn detail).length > 1 do throw error
            pure true
        unless rejected do
          throwError "a selected lift accepted evidence for a different source input"
    if name == `unscaledRaw then break
  unless observed == #[`X1, `i1, `alpha1, `beta1, `unscaledRaw] && questions.size == 2 do
    throwError "the original lift context did not supply its projections, equations and raw point"
