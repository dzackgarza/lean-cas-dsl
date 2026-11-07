module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Modules.Operations
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Modules.Operations
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement

open Lean Meta Elab Term CasCompiler CasCatalogue

private def levels (name : String) : TermElabM (List Level) := do
  let entry ← selectCategory (← semanticState) name
  return (← checkedDeclaration entry.declaration).levelParams.map Level.param

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let cases : Array (String × String × List Level × Nat) := #[
    ("Rings", "·", [.zero], 1), ("Rings", "^", [.zero], 2),
    ("Modules", "•", [.param `u, .param `u], 2)]
  for (categoryName, operationName, universes, minimumBinders) in cases do
    let category ← session.categoryFamily Syntax.missing categoryName universes
    let routes ← SourceRoutes.forOperation category.expression operationName
    let families ← routes.operationFamilies session Syntax.missing #[] category
    unless families.size == 1 do throwError "the actual initial operation binding is not retained"
    for family in families do
      unless family.binding.name == operationName && family.route.steps.isEmpty &&
          family.source.expression.syntacticEq category.expression do
        throwError "whole-family preparation changed its source binding or route"
      family.term.source.withOpen fun _ expression => do
        lambdaTelescope expression fun parameters body => do
          unless parameters.size >= minimumBinders && parameters.all (·.isFVar) do
            throwError "whole-family preparation specialized a source object or parameter"
          unless !(body.hasExprMVar || body.hasLevelMVar) &&
              (← whnfR (← inferType body)).isAppOf ``Quiver.Hom do
            throwError "the prepared family is not the complete morphism before operands"
          for parameter in parameters do
            unless body.containsFVar parameter.fvarId! do
              throwError "whole-family preparation discarded an actual rigid source parameter"
  for (categoryName, operationName) in #[("Rings", "·"), ("Modules", "•")] do
    let category ← session.categoryFamily Syntax.missing categoryName (← levels categoryName)
    let routes ← SourceRoutes.forOperation category.expression operationName
    let rejected ← try
      discard <| routes.operationFamilies session Syntax.missing #[] category
      pure false
    catch _ => pure true
    unless rejected do
      throwError "operation preparation silently specialized an incompatible rigid universe"
  let commutative ← session.categoryFamily Syntax.missing "CommutativeRings" [.zero]
  let inherited ← SourceRoutes.forOperation commutative.expression "·"
  let some traces := inherited.language.grammar.finiteWords
    | throwError "the imported finite operation routes became infinite"
  unless !traces.isEmpty do throwError "the actual inherited operation route control is absent"
  let mut nonemptyRoute := false
  for trace in traces do
    let families ← inherited.operationFamilies session Syntax.missing trace commutative
    unless !families.isEmpty do throwError "an actual first-hit binding lost its whole family"
    for family in families do
      nonemptyRoute := nonemptyRoute || !family.route.steps.isEmpty
      family.term.source.withOpen fun _ expression => do
        lambdaTelescope expression fun parameters body => do
          unless !parameters.isEmpty && parameters.all (·.isFVar) &&
              body.getUsedConstants.contains family.binding.declaration &&
              (← whnfR (← inferType body)).isAppOf ``Quiver.Hom do
            throwError "an inherited operation lost its generic object or original declaration"
  unless nonemptyRoute do throwError "the operation control did not use its actual structural route"
  let inheritedFamilies ← traces.flatMapM fun trace =>
    inherited.operationFamilies session Syntax.missing trace commutative
  for left in inheritedFamilies do
    for right in inheritedFamilies do
      let some agreement ← session.operationConversion Syntax.missing left right
        | throwError "the actual whole multiplicative operation families lost conversion evidence"
      agreement.proof.source.withOpen fun context proof => do
        let goal ← agreement.proposition.source.inContext context
        unless ← isDefEq (← inferType proof) goal do
          throwError "the retained agreement proof has a different complete proposition"
        let left ← agreement.left.term.source.inContext context
        let right ← agreement.right.term.source.inContext context
        unless ← isDefEq goal (← mkEq left right) do
          throwError "the agreement proposition discarded its original whole families"
        checkWithKernel proof
  let rings ← session.categoryFamily Syntax.missing "Rings" [.zero]
  let additions ← SourceRoutes.forOperation rings.expression "+"
  let multiplications ← SourceRoutes.forOperation rings.expression "·"
  let #[addition] ← additions.operationFamilies session Syntax.missing #[] rings
    | throwError "the actual ring addition family is absent"
  let #[multiplication] ← multiplications.operationFamilies session Syntax.missing #[] rings
    | throwError "the actual ring multiplication family is absent"
  unless (← session.operationConversion Syntax.missing addition multiplication).isNone do
    throwError "different whole ring operations received conversion evidence"
  let modules ← session.categoryFamily Syntax.missing "Modules" (← levels "Modules")
  let state ← semanticState
  let some constructor := state.constructors.find? (·.functorialAction.isSome)
    | throwError "the source constructor family control is absent"
  let constructed ← session.unaryCategoryFamily Syntax.missing constructor.id modules
  unless constructed.expression.syntacticEq
      (.construct constructor.id #[.category modules.expression]) do
    throwError "the constructed family lost its actual symbolic argument"
  constructed.family.source.withOpen fun _ expression => do
    lambdaTelescope expression fun parameters body => do
      unless !parameters.isEmpty && parameters.all (·.isFVar) do
        throwError "the constructor family specialized the source category parameters"
      for parameter in parameters do
        unless body.containsFVar parameter.fvarId! do
          throwError "the constructor family discarded a rigid source argument"
