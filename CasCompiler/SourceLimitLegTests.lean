module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/-- Read `text` after `let C := cokernel(to_dual(1))` (tests/acceptance/lattices.cas). -/
private def readAtCokernel (text : String) : TermElabM SourceTerm := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-leg.cas" "let C := cokernel(to_dual(1))\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the cokernel statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the cokernel did not extend its source context"
    session := next
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the leg did not parse"
  session.read ⟨source⟩

/- A universal construction supplies its defining maps (constitution C7): `C.leg(j)` is the leg of
the registered cocone at the object of its shape that the ordinal `j` names, the `j`-th constructor
of the shape's enumeration (the original reader's `constructionLeg`). The cokernel's shape is
`WalkingParallelPair`; its leg at `one` is the quotient map. An ordinal outside the shape is
invalid. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let leg ← readAtCokernel "C.leg(1)"
  unless leg.category.any (·.role == .morphism) do
    throwError "`C.leg(1)` did not read as a morphism"
  leg.source.withOpen fun _ value => do
    let value ← instantiateMVars value
    unless (value.find? (·.isConstOf ``CategoryTheory.Limits.Cocone.ι)).isSome &&
        (value.find? (·.isConstOf ``CategoryTheory.Limits.WalkingParallelPair.one)).isSome do
      throwError "`C.leg(1)` is not the cocone's leg at `one`: {value}"
  let failure ← try
      discard <| readAtCokernel "C.leg(2)"
      pure none
    catch error => pure (some error)
  match failure with
  | none => throwError "an ordinal outside the cokernel's shape was admitted"
  | some error =>
    unless CasCatalogue.Exception.stratum? error == some .invalid do throw error

/- The formation of a limit retains its selection (constitution C23): the binding of `C` carries
the row of the registered cokernel and its cocone. `C.leg(j)` is read from that selection, not from
the apex. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-leg.cas" "let C := cokernel(to_dual(1))\n"
  let mut session ← SourceSession.empty identities
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the cokernel statement did not parse"
    let .definition next _ ← file.withContext (session.readStatement statement)
      | throwError "the cokernel did not extend its source context"
    session := next
  let some entry := session.context.entries.back?
    | throwError "the cokernel added no declaration"
  let some category := session.categoryFor entry.id
    | throwError "the cokernel has no selected category"
  let some limit := category.limit
    | throwError "the binding of the cokernel did not retain its limit selection"
  unless limit.colimit do throwError "the retained selection is not a colimit"
  let state ← CasCatalogue.semanticState
  unless state.limits.any (fun row => row.id.raw == limit.row && row.colimit) do
    throwError "the retained selection names no registered colimit row: {limit.row}"

-- A binary product's published diagram is indexed by Discrete WalkingPair. The
-- ordinal chooses its existing left/right constructor, wrapped by the actual Discrete
-- constructor; the defining map still comes from the original retained cone.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "Fin(2) × Fin(3)"
    | throwError "the original product source did not parse"
  let product ← empty.read ⟨source⟩
  let some category := product.category
    | throwError "the original product lost its selected category"
  let some selection := category.limit
    | throwError "the original product lost its selected cone"
  let session ← empty.defineTerm `P product
  for (ordinal, constructor) in #[
      (0, ``CategoryTheory.Limits.WalkingPair.left),
      (1, ``CategoryTheory.Limits.WalkingPair.right)] do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term s!"P.leg({ordinal})"
      | throwError "the product leg source did not parse"
    let leg ← session.read ⟨source⟩
    unless leg.category.any (fun actual => actual.role == .morphism &&
        actual.expression.syntacticEq category.expression) do
      throwError "the product leg changed its original source category"
    leg.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let cone ← selection.cone.inContext context
      let projection ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
      let component ← mkAppM ``CategoryTheory.NatTrans.app #[projection]
      let index ← mkAppM ``CategoryTheory.Discrete.mk #[Lean.mkConst constructor]
      let expected := mkApp component index
      unless value.containsConst (· == ``CategoryTheory.Discrete.mk) &&
          value.containsConst (· == constructor) && (← isDefEq value expected) do
        throwError "the product leg changed the original cone or actual diagram index"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "P.leg(2)"
    | throwError "the invalid product leg source did not parse"
  let failure ← try
      discard <| session.read ⟨source⟩
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "the product admitted an ordinal outside its actual two-object shape"
  unless CasCatalogue.Exception.stratum? failure == some .invalid do throw failure

-- Equal definitions are distinct diagram inputs. In particular a module-valued
-- product's second leg must retain Y even though the first candidate X is convertible.
-- The Sets case checks the same retained cone interface without selecting another shape.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let readAt := fun (session : SourceSession) (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the retained-endpoint source did not parse"
    session.read ⟨source⟩
  for objectSource in #["RegularModule(ℤ)", "Fin(3)"] do
    let object ← readAt empty objectSource
    let session ← empty.defineTerm `X object
    let session ← session.defineTerm `Y object
    let product ← readAt session "X × Y"
    let some category := product.category
      | throwError "the equal-input product lost its selected category"
    let some selection := category.limit
      | throwError "the equal-input product lost its retained cone"
    let session ← session.defineTerm `P product
    let some first := session.context.entries.find? (·.userName == `X)
      | throwError "the first original diagram input is absent"
    let some second := session.context.entries.find? (·.userName == `Y)
      | throwError "the second original diagram input is absent"
    for (ordinal, constructor, selected) in #[
        (0, ``CategoryTheory.Limits.WalkingPair.left, first.id),
        (1, ``CategoryTheory.Limits.WalkingPair.right, second.id)] do
      let leg ← readAt session s!"P.leg({ordinal})"
      discard <| session.elaborate Syntax.missing fun context => do
        let some first := context.bindings.find? (·.id == first.id)
          | throwError "the first diagram input is outside its original context"
        let some second := context.bindings.find? (·.id == second.id)
          | throwError "the second diagram input is outside its original context"
        let some chosen := context.bindings.find? (·.id == selected)
          | throwError "the selected diagram input is outside its original context"
        unless first.expression != second.expression &&
            (← isDefEq first.expression second.expression) do
          throwError "the endpoint control lost its distinct equal-valued source bindings"
        let cone ← selection.cone.inContext context
        unless cone.containsFVar first.expression.fvarId! &&
            cone.containsFVar second.expression.fvarId! do
          throwError "product formation discarded one of its exact original diagram inputs"
        let projection ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
        let component ← mkAppM ``CategoryTheory.NatTrans.app #[projection]
        let index ← mkAppM ``CategoryTheory.Discrete.mk #[Lean.mkConst constructor]
        let expected := mkApp component index
        let value ← leg.source.inContext context
        let some (_, originalTarget) ← SourceReader.mapEnds expected
          | throwError "the original cone component lost its native endpoints"
        let some (_, actualTarget) ← SourceReader.mapEnds value
          | throwError "the retained product leg lost its native endpoints"
        -- This fixture reduces only the declared diagram projection; all actual
        -- context bindings remain opaque, so equal definitions cannot hide a swap.
        let preserveInputs := fun term =>
          withConfig (fun config => { config with zetaDelta := false }) <|
            withTransparency .all (whnf term)
        let originalTarget ← preserveInputs originalTarget
        let actualTarget ← preserveInputs actualTarget
        unless originalTarget == chosen.expression do
          throwError "the native product diagram changed its stated ordinal input"
        unless actualTarget == chosen.expression do
          throwError "the product leg replaced its actual diagram endpoint by an equal-valued input"
        unless ← isDefEq value expected do
          throwError "the product leg changed its exact retained cone component"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
        return value
