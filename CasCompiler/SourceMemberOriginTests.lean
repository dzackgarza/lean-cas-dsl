module

import CasCompiler.Read
import CasCompiler.SourceMember
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceMember
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

namespace CasCompiler.SourceMemberOriginTests

open Lean Meta Elab Term CasCatalogue CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original member-origin source did not parse"
  return ⟨source⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let source ← empty.defineTerm `Scalar (← empty.read (← sourceTerm "ℚ"))
  let some scalar := source.context.entries.back?
    | throwError "the original scalar lost its source binding"
  let selectedScalar ← source.read (← sourceTerm "Scalar")
  let some scalarCategory := selectedScalar.category
    | throwError "the original scalar lost its complete selected category"
  let space ← source.read (← sourceTerm "Scalar³")
  let source ← source.defineTerm `u
    (← source.read (← sourceTerm "(1, 0, 1)") (some space.source) space.selections)
  let source ← source.defineTerm `Scalar (← source.read (← sourceTerm "ℤ"))
  let some shadow := source.context.entries.back?
    | throwError "the scalar shadow lost its distinct source binding"
  let span ← source.read (← sourceTerm "span({u})")
  let #[field] := (← semanticState).objects.filter (·.id.raw == "obj.fields.rationals")
    | throwError "the independent rational-field registration is absent or ambiguous"
  let some refinement := field.refines
    | throwError "the independent rational field lost its registered base comparison"
  checkSelected span fun value => do
    let scope ← get
    let some original := scope.context.bindings.find? (·.id == scalar.id)
      | liftM (m := TermElabM) <|
          throwError "the selected span lost its original scalar occurrence"
    let some later := scope.context.bindings.find? (·.id == shadow.id)
      | liftM (m := TermElabM) <|
          throwError "the selected span lost its distinct shadow control"
    unless original.expression != later.expression do
      liftM (m := TermElabM) <|
        throwError "the scalar shadow reused the original source identity"
    let applications ← declaredApplications scope.context scope.selections
      ``CasCatalogue.Algebra.LinearAlgebra.span value
    if applications.isEmpty then
      liftM (m := TermElabM) <|
        throwError "the public span lost its original registered morphism"
    let mut found := false
    for applied in applications do
      for parameter in applied.getAppArgs do
        if let some (category, _) ← sourceObjectOrigin? parameter then
          if let some carrier := category.carrier then
            for comparison in carrier.comparisons do
              let some selected ← SourceReadM.selection? comparison | continue
              unless selected.reference.any
                  (·.exactlyMatches (.refinement field refinement)) do continue
              let some application := selected.originalApplication
                | liftM (m := TermElabM) <|
                    throwError "the member refinement lost its exact selected owner and declaration"
              unless application.getAppFn.isConstOf refinement.identification do
                liftM (m := TermElabM) <|
                  throwError "the member refinement lost its exact selected owner and declaration"
              let type ← whnfR (← inferType comparison)
              unless type.isAppOfArity ``CategoryTheory.Iso 4 do
                liftM (m := TermElabM) <|
                  throwError "the member refinement lost its complete native comparison type"
              let some (baseCategory, base) ← sourceObjectOrigin? type.getAppArgs[3]!
                | liftM (m := TermElabM) <|
                    throwError "the member comparison lost its original base's selected data"
              unless (← originatesAt scope.context scope.selections base original.expression false) &&
                  !(← originatesAt scope.context scope.selections base later.expression false) do
                liftM (m := TermElabM) <|
                  throwError "the member refinement changed its actual named base after shadowing"
              unless baseCategory.expression.syntacticEq scalarCategory.expression &&
                  baseCategory.bundle == (← scalarCategory.bundle.inContext scope.context) do
                liftM (m := TermElabM) <|
                  throwError "the member comparison changed the original base occurrence or category"
              checkOriginal #[comparison] fun native => checkWithKernel native[0]!
              found := true
    unless found do
      liftM (m := TermElabM) <|
        throwError "the span's selected field lost its original registered refinement comparison"
    checkOriginal #[value] fun native => checkWithKernel native[0]!



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let ring ← empty.read (← sourceTerm "ℚ in Rings")
  let some category := ring.category
    | throwError "the structured scalar control lost its selected category"
  let declared ← selectCategory (← semanticState) "Rings"
  unless category.expression.syntacticEq declared.expression do
    throwError "the structured scalar control did not select the registered ring"
  let source ← empty.defineTerm `Scalar ring
  let space ← source.read (← sourceTerm "Scalar³")
  let source ← source.defineTerm `u
    (← source.read (← sourceTerm "(1, 0, 1)") (some space.source) space.selections)
  let subset ← source.read (← sourceTerm "{u}")
  checkSelected subset fun value => do
    checkOriginal #[value] fun native => checkWithKernel native[0]!
    if (← sourceMorphismFrom? "span" (← inferType value)).isSome then
      liftM (m := TermElabM) <|
        throwError "a selected ring was replaced by a field from its equal carrier"




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let named ← empty.read (← sourceTerm "ℚ")
  checkSelected named fun value => do
    let bare ← liftM (m := TermElabM) <|
      elabTermAndSynthesize (← `(Set (Fin 2 → ℚ))) none
    let hidden ← mkAppM ``Function.const #[← inferType value, bare, value]
    checkOriginal #[bare, hidden] fun native => do
      checkWithKernel native[1]!
      unless ← isDefEq native[0]! native[1]! do
        throwError "the ignored source-object control changed its native type"
    if (← sourceMorphismFrom? "span" hidden).isSome then
      liftM (m := TermElabM) <|
        throwError "an unrelated type subterm supplied an unselected member structure"

end CasCompiler.SourceMemberOriginTests
