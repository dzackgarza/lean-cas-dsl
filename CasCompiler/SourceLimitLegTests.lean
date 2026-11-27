module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest


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






run_cmd Lean.Elab.Command.liftTermElabM do
  let leg ← readAtCokernel "C.leg(1)"
  unless leg.category.any (·.role == .morphism) do
    throwError "`C.leg(1)` did not read as a morphism"
  checkSelected leg fun value => do
    let some selected ← SourceReadM.selection? value
      | throwError "the cokernel leg lost its original typed selection"
    let some retained := selected.leg
      | throwError "the cokernel leg lost its original cone component"
    unless retained.value.containsConst (· == ``CategoryTheory.Limits.Cocone.ι) &&
        retained.index.isConstOf ``CategoryTheory.Limits.WalkingParallelPair.one do
      throwError "`C.leg(1)` is not the cocone's leg at `one`: {value}"
  let failure ← try
      discard <| readAtCokernel "C.leg(2)"
      pure none
    catch error => pure (some error)
  match failure with
  | none => throwError "an ordinal outside the cokernel's shape was admitted"
  | some error =>
    unless CasCatalogue.Exception.stratum? error == some .invalid do throw error




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
  checkSelected product fun value => do
    let some selected ← SourceReadM.selection? value
      | throwError "product formation lost its shared original construction anchor"
    let some retained := selected.limit
      | throwError "product formation lost its shared original construction anchor"
    unless retained.source.construction == selection.construction &&
        !selection.construction.isAnonymous do
      throwError "product formation changed its original construction identity"
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
    checkSelected leg fun value => do
      let scope ← get
      let cone ← selection.cone.inContext scope.context
      let projection ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
      let component ← mkAppM ``CategoryTheory.NatTrans.app #[projection]
      let index ← mkAppM ``CategoryTheory.Discrete.mk #[Lean.mkConst constructor]
      let expected := mkApp component index
      let some retained ← NativeLimitLegSelection.ofExpr? scope.context scope.selections value
        | throwError "the product leg lost its typed original receiver/index demand"
      unless retained.construction.source.construction == selection.construction &&
          retained.construction.source.cone.equal cone && retained.index.equal index do
        throwError "the product leg changed its construction, original cone or native index"
      unless retained.value.containsConst (· == ``CategoryTheory.Discrete.mk) &&
          retained.value.containsConst (· == constructor) do
        throwError "the product leg changed its original actual diagram index"
      checkOriginal #[value, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "the product leg changed the original cone component"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "P.leg(2)"
    | throwError "the invalid product leg source did not parse"
  let failure ← try
      discard <| session.read ⟨source⟩
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "the product admitted an ordinal outside its actual two-object shape"
  unless CasCatalogue.Exception.stratum? failure == some .invalid do throw failure




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
      discard <| session.elaborateScoped Syntax.missing do
        let value ← session.readTerm leg
        let scope ← get
        let context := scope.context
        let some first := context.bindings.find? (·.id == first.id)
          | throwError "the first diagram input is outside its original context"
        let some second := context.bindings.find? (·.id == second.id)
          | throwError "the second diagram input is outside its original context"
        let some chosen := context.bindings.find? (·.id == selected)
          | throwError "the selected diagram input is outside its original context"
        unless first.expression != second.expression do
          throwError "the endpoint control merged distinct source bindings"
        checkOriginal #[first.expression, second.expression] fun native => do
          unless ← isDefEq native[0]! native[1]! do
            throwError "the endpoint control lost its equal-valued source bindings"
        let cone ← selection.cone.inContext context
        for original in #[first.expression, second.expression] do
          unless (← visitNativeData (fun term =>
              originatesAt context scope.selections term original false) cone false) > 0 do
            throwError "product formation discarded one of its exact original diagram inputs"
        let projection ← mkAppM ``CategoryTheory.Limits.Cone.π #[cone]
        let component ← mkAppM ``CategoryTheory.NatTrans.app #[projection]
        let index ← mkAppM ``CategoryTheory.Discrete.mk #[Lean.mkConst constructor]
        let expected := mkApp component index
        let some (_, originalTarget) ← SourceReader.mapEnds expected
          | throwError "the original cone component lost its native endpoints"
        let some (_, actualTarget) ← SourceReader.mapEnds value
          | throwError "the retained product leg lost its native endpoints"


        let preserveInputs := fun term =>
          withConfig (fun config => { config with zetaDelta := false }) <|
            withTransparency .all (whnf term)
        let originalTarget ← preserveInputs originalTarget
        let actualTarget := (selectedEndpoint? context scope.selections actualTarget).getD actualTarget
        let actualTarget ← preserveInputs actualTarget
        unless ← originatesAt context scope.selections originalTarget chosen.expression false do
          throwError "the native product diagram changed its stated ordinal input"
        unless ← originatesAt context scope.selections actualTarget chosen.expression false do
          throwError "the product leg replaced its actual diagram endpoint by an equal-valued input"
        checkOriginal #[value, expected] fun native => do
          unless ← isDefEq native[0]! native[1]! do
            throwError "the product leg changed its exact retained cone component"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
            (← mkEq native[0]! native[1]!))
        return value



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let readAt := fun (session : SourceSession) (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the named-apex source did not parse"
    session.read ⟨source⟩
  let object ← readAt empty "cokernel(to_dual(1))"
  let some selection := object.category.bind (·.limit)
    | throwError "the named cokernel lost its retained cocone"
  let independent ← readAt empty "cokernel(to_dual(1))"
  let some independentSelection := independent.category.bind (·.limit)
    | throwError "the independent equal cokernel lost its original selection"
  unless selection.construction != independentSelection.construction do
    throwError "independent equal constructions shared a formation identity"
  unless selection.colimit do
    throwError "the named cokernel control changed its construction direction"
  let session ← empty.defineTerm `C object
  let session ← session.defineTerm `Cagain object
  for name in #[`C, `Cagain] do
    let leg ← readAt session s!"{name}.leg(1)"
    let mapped ← readAt session
      s!"map {name}.leg(1) along «fun.bil_wform.base_change»(ℤ, ℚ)"
    discard <| session.elaborateScoped Syntax.missing do
      let value ← session.readTerm leg
      let mapped ← session.readTerm mapped
      let scope ← get
      let context := scope.context
      let some original := session.context.entries.find? (·.userName == name)
        | throwError "the named apex has no original source binding"
      let some other := session.context.entries.find? (fun entry =>
          entry.userName == (if name == `C then `Cagain else `C))
        | throwError "the equal apex has no independent source binding"
      let some receiver := context.bindings.find? (·.id == original.id)
        | throwError "the named apex is outside its original source context"
      let some otherReceiver := context.bindings.find? (·.id == other.id)
        | throwError "the equal apex is outside its original source context"
      unless receiver.expression != otherReceiver.expression do
        throwError "the control merged its distinct apex bindings"
      checkOriginal #[receiver.expression, otherReceiver.expression] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "the control did not retain equal-valued apex definitions"
      let some retained ← NativeLimitLegSelection.ofExpr? context scope.selections value
        | throwError "the named leg lost its original receiver/index demand"
      unless retained.construction.source.construction == selection.construction &&
          retained.construction.receiver.equal receiver.expression &&
          !retained.construction.receiver.equal otherReceiver.expression &&
          retained.index.isConstOf ``CategoryTheory.Limits.WalkingParallelPair.one do
        throwError "the named leg replaced its receiver, shared construction or typed index"
      let some legData ← SourceReadM.selection? value
        | throwError "the named leg lost its original typed source selection"
      let some (.limit row) := legData.reference
        | throwError "the named leg lost its complete original limit row"
      unless row.id.raw == selection.row && row.declaration == selection.declaration &&
          legData.legOrdinal == some 1 do
        throwError "the named leg changed its original row, declaration or ordinal"
      let some (actualSource, actualTarget) ← SourceReader.mapEnds value
        | throwError "the named leg has no complete native endpoints"
      let actualTarget := (selectedEndpoint? context scope.selections actualTarget).getD actualTarget
      unless ← originatesAt context scope.selections actualTarget receiver.expression false do
        throwError "the named leg replaced its original apex with an equal-valued construction"
      let cone ← selection.cone.inContext context
      let projection ← mkAppM ``CategoryTheory.Limits.Cocone.ι #[cone]
      let component ← mkAppM ``CategoryTheory.NatTrans.app #[projection]
      let originalLeg := mkApp component (Lean.mkConst ``CategoryTheory.Limits.WalkingParallelPair.one)
      let some (originalSource, _) ← SourceReader.mapEnds originalLeg
        | throwError "the original native component lost its endpoints"
      let actualSource := (selectedEndpoint? context scope.selections actualSource).getD actualSource
      unless actualSource.equal originalSource do
        throwError "apex retention changed the original diagram endpoint"
      check value
      checkOriginal #[value, originalLeg] fun native => do
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      let some mapData ← SourceReadM.selection? mapped
        | throwError "the actual base-change map lost its selected source"
      let some application := mapData.application
        | throwError "the actual base-change map lost its complete native application"
      let .point family := application.family
        | throwError "the actual base-change map changed its selected point family"
      let .action (.functor id) := family.owner
        | throwError "the actual base-change map changed its original action owner"
      let image := mapData.value
      unless id.raw == "fun.bil_wform.base_change" &&
          image.getAppFn.isConstOf ``CategoryTheory.Functor.map do
        throwError "the actual base-change map changed its selected native action"
      let arguments := image.getAppArgs
      let some target := arguments[arguments.size - 2]?
        | throwError "the actual base-change map lost its target input"
      let target := (selectedEndpoint? context scope.selections target).getD target
      unless ← originatesAt context scope.selections target receiver.expression false do
        throwError "the actual map action discarded the selected original apex input"
      let some actualLeg := arguments.back?
        | throwError "the actual base-change map lost its original leg input"
      let some actualSelection ← NativeLimitLegSelection.ofExpr? context scope.selections actualLeg
        | throwError "the actual map argument lost its complete original leg selection"
      unless actualSelection.construction.source.construction == selection.construction &&
          actualSelection.construction.receiver.equal receiver.expression do
        throwError "the actual map argument replaced its original construction receiver"
      let some source := arguments[arguments.size - 3]?
        | throwError "the actual map action lost its source input"
      let some endpointData ← SourceReadM.selection? source
        | throwError "the actual map source lost its exact selected endpoint"
      let some endpoint := endpointData.endpoint
        | throwError "the actual map source is not its selected leg endpoint"
      unless endpoint.side == .source &&
          (← originatesAt context scope.selections actualLeg endpoint.arrow false) do
        throwError "the selected endpoint refers to a different leg occurrence"
      let some (legSource, legTarget) ← SourceReader.mapEnds actualLeg
        | throwError "the actual map action lost its leg's complete native endpoints"
      let legSource := (selectedEndpoint? context scope.selections legSource).getD legSource
      let legTarget := (selectedEndpoint? context scope.selections legTarget).getD legTarget
      unless legSource.equal originalSource &&
          (← originatesAt context scope.selections legTarget receiver.expression false) do
        throwError "the actual map action changed an original leg endpoint"
      check mapped
      checkOriginal #[actualLeg, originalLeg] fun native => do
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      return mapped
