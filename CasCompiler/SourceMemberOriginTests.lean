module

import CasCompiler.Read
import CasCompiler.SourceMember
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceMember
meta import LeanCategories.Catalogue

namespace CasCompiler.SourceMemberOriginTests

open Lean Meta Elab Term CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original member-origin source did not parse"
  return ⟨source⟩

-- The original public span retains the named scalar it was formed over, including after
-- that name is shadowed. Its otherwise implicit field is supplied by the independently
-- registered refinement, with the complete comparison retained on the actual parameter.
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
    (← source.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let source ← source.defineTerm `Scalar (← source.read (← sourceTerm "ℤ"))
  let some shadow := source.context.entries.back?
    | throwError "the scalar shadow lost its distinct source binding"
  let span ← source.read (← sourceTerm "span({u})")
  let #[field] := (← semanticState).objects.filter (·.id.raw == "obj.fields.rationals")
    | throwError "the independent rational-field registration is absent or ambiguous"
  let some refinement := field.refines
    | throwError "the independent rational field lost its registered base comparison"
  span.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    let some original := bindings.find? (·.id == scalar.id)
      | throwError "the selected span lost its original scalar occurrence"
    let some later := bindings.find? (·.id == shadow.id)
      | throwError "the selected span lost its distinct shadow control"
    unless original.expression != later.expression do
      throwError "the scalar shadow reused the original source identity"
    let some applied := value.find? (·.getAppFn.isConstOf
        ``CasCatalogue.Algebra.LinearAlgebra.span)
      | throwError "the public span lost its original registered morphism"
    let mut found := false
    for parameter in applied.getAppArgs do
      if let some (category, _) ← sourceObjectOrigin? parameter then
        if let some carrier := category.carrier then
          for comparison in carrier.comparisons do
            if comparison.containsConst (· == refinement.identification) then
              unless comparison.containsFVar original.expression.fvarId! &&
                  !comparison.containsFVar later.expression.fvarId! do
                throwError "the member refinement changed its actual named base after shadowing"
              let type ← whnfR (← inferType comparison)
              unless type.isAppOfArity ``CategoryTheory.Iso 4 do
                throwError "the member refinement lost its complete native comparison type"
              let some (baseCategory, base) ← sourceObjectOrigin? type.getAppArgs[3]!
                | throwError "the member comparison lost its original base's selected data"
              unless base == original.expression &&
                  baseCategory.expression.syntacticEq scalarCategory.expression &&
                  baseCategory.bundle == (← scalarCategory.bundle.inContext context) do
                throwError "the member comparison changed the original base occurrence or category"
              checkWithKernel comparison
              found := true
    unless found do
      throwError "the span's selected field lost its original registered refinement comparison"
    checkWithKernel value

-- An explicitly selected ring keeps that structure. Its rational carrier does not license
-- substituting the independently registered field when the member requires a field.
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
    (← source.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let subset ← source.read (← sourceTerm "{u}")
  subset.source.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let value ← subset.source.inContext context
    checkWithKernel value
    if (← sourceMorphismFrom? "span" (← inferType value)).isSome then
      throwError "a selected ring was replaced by a field from its equal carrier"

-- A named rational object in an ignored native argument does not supply a field for a
-- separate bare carrier. This is the exact false-positive shape of the former subterm probe.
-- The native type is unchanged and no alternate interpretation or registry row is supplied.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let named ← empty.read (← sourceTerm "ℚ")
  named.source.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let named ← named.source.inContext context
    let bare ← elabTermAndSynthesize (← `(Set (Fin 2 → ℚ))) none
    let hidden ← mkAppM ``Function.const #[← inferType named, bare, named]
    checkWithKernel hidden
    unless ← isDefEq bare hidden do
      throwError "the ignored source-object control changed its native type"
    if (← sourceMorphismFrom? "span" hidden).isSome then
      throwError "an unrelated type subterm supplied an unselected member structure"

end CasCompiler.SourceMemberOriginTests
