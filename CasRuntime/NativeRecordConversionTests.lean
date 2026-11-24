module

import CasRuntime.Kernel
import LeanCategories.Foundation.Mathlib
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import LeanCategories.Foundation.Mathlib
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

namespace CasRuntime.NativeRecordConversionTests

open Lean Meta CasCompiler

-- Forgetting a functor's laws retains its one actual object action and the map that depends
-- on that action. The two projections of the original formal argument must share that input.
-- This uses only the existing native identity functor and requires no provider or value answer.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let declaration ← getConstInfo ``LeanCategories.Foundation.Mathlib.Sets
    let sets := mkConst declaration.name (declaration.levelParams.map fun _ => Level.zero)
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[sets]
    let category ← mkAppM ``CategoryTheory.Bundled.str #[sets]
    let functor ← mkAppOptM ``CategoryTheory.Functor.id #[some carrier, some category]
    let term ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let bound : Std.HashMap BindingId ValueBinding := {}
        let value ← kernel.run transaction context bound term
        let retained ← markValue kernel.marks value term
        let objectAction ← kernel.run transaction context bound (mkProj ``Prefunctor 0 retained)
        let mapAction ← kernel.run transaction context bound (mkProj ``Prefunctor 1 retained)
        let some consumed := mapAction.instantiations.find?
            (·.field.projection == ``CategoryTheory.Functor.map)
          | throwError "the native conversion lost the original functor's dependent map role"
        let some (some originalObject) := consumed.preceding[0]?
          | throwError "the native conversion lost the map's original object action"
        unless originalObject.value == objectAction.value &&
            originalObject.associationIds.toList.isPrefixOf objectAction.associationIds.toList do
          throwError "the native conversion rebuilt the original formal object-action occurrence"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "a native record conversion dispatched a provider"
      finally discard <| transaction.abort
      -- The same genuine functor source may name a descriptor with no native field data.
      -- Its source definition cannot replace those missing actual input projections.
      let missing ← CellTransaction.begin kernel.ledger
      try
        let program ← owners.identities.fresh .program
        let .ok payload := ValuePayload.descriptor .null #[]
          | throwError "the native conversion descriptor control is malformed"
        let descriptor ← missing.stage
          { program, occurrence := ← kernel.ledger.allocate,
            role := ← SourceLayout.ofTerm (← context.close functor), parameters := #[] }
          payload
        let marked ← markValue kernel.marks descriptor functor
        let unavailable ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[marked]
        let bound : Std.HashMap BindingId ValueBinding := {}
        let failure : Option Exception ← try
          discard <| kernel.run missing context bound unavailable
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "a native conversion fabricated a descriptor's unavailable fields"
        match CasCatalogue.Exception.stratum? failure with
        | some .noImplementation => pure ()
        | _ => throw failure
        -- A local alias must preserve the same unavailable actual field boundary.
        let sourceAlias := Expr.letE `value (← inferType marked) marked (.bvar 0) false
        let unavailableAlias ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[sourceAlias]
        let aliasFailure : Option Exception ← try
          discard <| kernel.run missing context bound unavailableAlias
          pure none
        catch error => pure (some error)
        let some aliasFailure := aliasFailure
          | throwError "a native conversion alias fabricated a descriptor's unavailable fields"
        match CasCatalogue.Exception.stratum? aliasFailure with
        | some .noImplementation => pure ()
        | _ => throw aliasFailure
        unless (← kernel.dispatches.get).isEmpty do
          throwError "a missing native conversion field dispatched a provider"
      finally discard <| missing.abort
    finally kernel.close
  finally setEnv original

-- Constant projection syntax and a nondependent native record conversion must retain the
-- same actual fields as Expr.proj. Equal source fields at different positions stay distinct;
-- a descriptor supplies none of them. Runtime class records have the same boundary, while
-- a formal class projection still reads its ordinary native definition.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let multiplicationType := mkApp (mkConst ``Mul [.zero]) (mkConst ``Nat)
    let multiplication ← synthInstance multiplicationType
    let leftAction := Expr.lam `left (mkConst ``Nat)
      (.lam `right (mkConst ``Nat) (.bvar 1) .default) .default
    let selectedMultiplication ← mkAppOptM ``Mul.mk
      #[some (mkConst ``Nat), some leftAction]
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let pair ← kernel.run transaction context {} pairTerm
        let graph ← transaction.view
        let .ok first := graph.project pair 0
          | throwError "the native projection control lost its first original field"
        let .ok second := graph.project pair 1
          | throwError "the native projection control lost its second original field"
        unless first.value != second.value do
          throwError "the native projection control merged equal original fields"
        let marked ← markValue kernel.marks pair pairTerm
        let markedType ← inferType marked
        for aliased in #[false, true] do
          let parent := if aliased then
              Expr.letE `value markedType marked (.bvar 0) false
            else marked
          for (projection, expected) in #[(``Prod.fst, first), (``Prod.snd, second)] do
            let term ← mkAppM projection #[parent]
            let selected ← kernel.run transaction context {} term
            unless selected.value == expected.value &&
                expected.associationIds.toList.isPrefixOf selected.associationIds.toList do
              throwError "a constant native projection replaced its original selected field"
          let swapped ← kernel.run transaction context {} (← mkAppM ``Prod.swap #[parent])
          let graph ← transaction.view
          for expected in #[second, first], index in [:2] do
            let .ok selected := graph.project swapped index
              | throwError "the nondependent native conversion lost a result field"
            unless selected.value == expected.value &&
                expected.associationIds.toList.isPrefixOf selected.associationIds.toList do
              throwError "a nondependent native conversion replaced an original selected field"
        let formal ← mkAppOptM ``Mul.mul #[some (mkConst ``Nat), some selectedMultiplication]
        let formalValue ← kernel.run transaction context {} formal
        unless formalValue.role.kind == .function do
          throwError "a formal class projection lost its native function field"
        let actual ← kernel.run transaction context {} selectedMultiplication
        let marked ← markValue kernel.marks actual selectedMultiplication
        let markedType ← inferType marked
        let projected ← kernel.run transaction context {} (mkProj ``Mul 0 marked)
        for aliased in #[false, true] do
          let parent := if aliased then
              Expr.letE `value markedType marked (.bvar 0) false
            else marked
          let term ← mkAppOptM ``Mul.mul #[some (mkConst ``Nat), some parent]
          let selected ← kernel.run transaction context {} term
          unless selected.value == projected.value do
            throwError "constant projection syntax rebuilt an actual class field"
        let actual ← kernel.run transaction context {} selectedMultiplication
        let marked ← markValue kernel.marks actual selectedMultiplication
        let markedType ← inferType marked
        let left ← markValue kernel.marks first (mkNatLit 7)
        let right ← markValue kernel.marks second (mkNatLit 7)
        for aliased in #[false, true] do
          let parent := if aliased then
              Expr.letE `value markedType marked (.bvar 0) false
            else marked
          let constant ← mkAppOptM ``Mul.mul
            #[some (mkConst ``Nat), some parent, some left, some right]
          let annotated := mkAppN
            (.mdata (KVMap.empty.setNat `control.inert 1) constant.getAppFn)
            constant.getAppArgs
          for term in #[constant, annotated, mkAppN (mkProj ``Mul 0 parent) #[left, right]] do
            let selected ← kernel.run transaction context {} term
            unless selected.value == first.value &&
                first.associationIds.toList.isPrefixOf selected.associationIds.toList do
              throwError "an applied class projection replaced its original argument"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the native projection controls dispatched a provider"
      finally discard <| transaction.abort
      for (source, operation, applied, annotated) in #[
          (pairTerm, ``Prod.fst, false, false), (pairTerm, ``Prod.swap, false, false),
          (multiplication, ``Mul.mul, false, false),
          (selectedMultiplication, ``Mul.mul, true, false),
          (selectedMultiplication, ``Mul.mul, true, true)] do
        for aliased in #[false, true] do
          let transaction ← CellTransaction.begin kernel.ledger
          try
            let program ← owners.identities.fresh .program
            let .ok payload := ValuePayload.descriptor .null #[]
              | throwError "the native projection descriptor control is malformed"
            let descriptor ← transaction.stage
              { program, occurrence := ← kernel.ledger.allocate,
                role := ← SourceLayout.ofTerm (← context.close source), parameters := #[] }
              payload
            let marked ← markValue kernel.marks descriptor source
            let markedType ← inferType marked
            let parent := if aliased then
                Expr.letE `value markedType marked (.bvar 0) false
              else marked
            let type ← whnf (← inferType source)
            let mut arguments := type.getAppArgs.push parent
            if applied then arguments := arguments ++ #[mkNatLit 7, mkNatLit 7]
            let term ← mkAppOptM operation (arguments.map some)
            let term := if annotated then
                mkAppN (.mdata (KVMap.empty.setNat `control.inert 1) term.getAppFn)
                  term.getAppArgs
              else term
            let failure : Option Exception ← try
              discard <| kernel.run transaction context {} term
              pure none
            catch error => pure (some error)
            let some failure := failure
              | throwError "the native selection {operation} fabricated a descriptor field"
            unless CasCatalogue.Exception.stratum? failure == some .noImplementation do
              throw failure
            unless (← kernel.dispatches.get).isEmpty do
              throwError "a missing native projection field dispatched a provider"
          finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original

-- The published total-module additive-group object action selects only the original
-- module's carrier and class fields. Check the symbolic paths before running that same
-- registered action, then compare its actual returned fields with those original inputs.
-- No provider data or expected additive-group value is constructed by this control.
set_option maxHeartbeats 2000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let scalarTerm := mkConst ``CasCatalogue.Algebra.NamedRings.ringIntegers
        let scalarValue ← kernel.run transaction context {} scalarTerm
        let scalarSource ← markValue kernel.marks scalarValue scalarTerm
        let moduleTerm ← mkAppM
          ``CasCatalogue.Modules.CatalogueRegistration.regularModule #[scalarSource]
        let moduleValue ← kernel.run transaction context {} moduleTerm
        let moduleSource ← markValue kernel.marks moduleValue moduleTerm
        let inclusionInfo ← getConstInfo
          ``CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
        let inclusion := mkApp
          (mkConst inclusionInfo.name (inclusionInfo.levelParams.map fun _ => Level.zero))
          scalarSource
        let inclusionPrefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[inclusion]
        let totalTerm ← mkAppM ``Prefunctor.obj #[inclusionPrefunctor, moduleSource]
        let totalValue ← kernel.run transaction context {} totalTerm
        let totalSource ← markValue kernel.marks totalValue totalTerm
        let some fibreField := totalValue.role.fields.find?
            (·.projection == ``CategoryTheory.Pseudofunctor.CoGrothendieck.fiber)
          | throwError "the native total module lost its original fibre field"
        let some fibreIndex := fibreField.wireIndex
          | throwError "the original module fibre became a proof field"
        let fibreValue ← IO.ofExcept <|
          ((← transaction.view).project totalValue fibreIndex).mapError IO.userError
        unless fibreValue.value == moduleValue.value &&
            moduleValue.associationIds.toList.isPrefixOf fibreValue.associationIds.toList do
          throwError "the native fibre inclusion replaced its actual original module"
        let actionInfo ← getConstInfo
          ``CasCatalogue.Modules.CatalogueRegistration.modulesAdditiveGroupDeclaration
        let action := mkConst actionInfo.name (actionInfo.levelParams.map fun _ => Level.zero)
        let actionPrefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[action]
        let objectAction ← mkAppM ``Prefunctor.obj #[actionPrefunctor]
        let functionLayout ← SourceLayout.ofTerm (← context.close objectAction)
        let (outputLayout, applicationLayout) ← ApplicationLayout.ofSource
          functionLayout context #[← context.close totalSource]
        let originalPaths : Array (Name × Array Name) := #[
          (``AddGrpCat.carrier,
            #[``CategoryTheory.Pseudofunctor.CoGrothendieck.fiber, ``ModuleCat.carrier]),
          (``AddGrpCat.str,
            #[``CategoryTheory.Pseudofunctor.CoGrothendieck.fiber,
              ``ModuleCat.isAddCommGroup, ``AddCommGroup.toAddGroup])]
        unless outputLayout.kind == .record &&
            (outputLayout.fields.filter (·.wireIndex.isSome)).size == originalPaths.size do
          throwError "the published additive-group object action changed its native field interface"
        for (projection, originalPath) in originalPaths do
          let some selected ← applicationLayout.inputProjectionAt #[projection]
            | throwError "the published native object field {projection} has no original input route"
          let .argument 0 := selected.target
            | throwError "the native object field {projection} selected a different formal input"
          unless selected.path == originalPath do
            throwError "the native object field {projection} changed its original input path: {selected.path}"
        -- Do not evaluate the expected input projections first: the actual object action must
        -- discover and preserve them through its ordinary complete input-result plan.
        let outputTerm := mkApp objectAction totalSource
        let outputValue ← kernel.run transaction context {} outputTerm
        let outputSource ← markValue kernel.marks outputValue outputTerm
        for (projection, originalPath) in originalPaths do
          let some field := outputValue.role.fields.find? (·.projection == projection)
            | throwError "the native additive-group output lost its selected field"
          let selectedValue ← kernel.run transaction context {}
            (← projectTerm outputSource field)
          let graph ← transaction.view
          let some originalValue ← IO.ofExcept <|
              (graph.projected? totalValue originalPath).mapError IO.userError
            | throwError "the native view did not publish its original input path {originalPath}"
          let some selectedBasis ← IO.ofExcept <|
              (graph.projectionBasis selectedValue totalValue originalPath).mapError IO.userError
            | throwError "the native view lost the selected field's exact original parent and path"
          unless selectedValue.value == originalValue.value &&
              originalValue.associationIds.toList.isPrefixOf selectedValue.associationIds.toList &&
              selectedBasis.value == originalValue.value &&
              selectedBasis.associationIds == originalValue.associationIds do
            throwError "the native additive-group view replaced an original field occurrence"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the complete native module view dispatched a provider"
      finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original

end CasRuntime.NativeRecordConversionTests
