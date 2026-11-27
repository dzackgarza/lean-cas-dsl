module

import CasCompiler.Program
import CasCompiler.Context
import CasRuntime.Environment
import CasRuntime.PreparedRequest
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import Mathlib.CategoryTheory.Limits.IsLimit
public meta import Lean.Elab.Command
meta import CasCompiler.Program
meta import CasCompiler.Context
meta import CasRuntime.Environment
meta import CasRuntime.PreparedRequest
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import Mathlib.CategoryTheory.Limits.IsLimit

open Lean Meta CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let programs ← SourceProgram.forTarget (.operation ⟨"op.rings.mul"⟩)
  unless programs.size == 2 do
    throwError "source intake must retain both published derivations"
  for program in programs do
    let source := program.source
    check source.correctness
    unless ← isDefEq (← inferType source.correctness) (← mkEq source.plan source.target) do
      throwError "source intake lost the checked whole-family equality"
    let owners ← liftM (m := IO) CasRuntime.OwnerRegistry.new
    let context ← ContextTelescope.capture #[]
    let universes := source.universeParams.map Level.param
    program.instantiate universes owners.identities context {} fun context selections selected => do
      context.withOriginalSources #[selected, source.plan] fun originals => do
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl originals[0]!)
          (← mkEq originals[0]! originals[1]!))
      unless context.bindings.size == source.prerequisites.size &&
          selections.size == source.prerequisites.size do
        throwError "the source program changed its complete original prerequisite table"
      for index in List.finRange source.prerequisites.size do
        let binding := context.bindings[index.val]!
        let some retained := selections[binding.id]?
          | throwError "the source program erased an original prerequisite selection"
        let some application := retained.application
          | throwError "the source program erased an original prerequisite family"
        unless application.family.exactlyMatches (.prerequisite program index) &&
            application.universes == universes && application.parameters.isEmpty &&
            retained.formalBindings.isEmpty &&
            selected.containsFVar binding.expression.fvarId! do
          throwError "the source program changed an original prerequisite selection"
    let previous ← program.withPrerequisites fun slots body => do
      unless slots.size == source.prerequisites.size do
        throwError "source intake changed the prerequisite arity"
      for slot in slots, expected in source.prerequisites, index in [:slots.size] do
        unless slot.index == index &&
            slot.source.reference == expected.reference do
          throwError "source intake changed an exact ordered prerequisite address"
        check slot.expression
      check body
      return slots.map (·.expression.fvarId!)
    program.withPrerequisites fun slots body => do
      for slot in slots do
        if previous.contains slot.expression.fvarId! then
          throwError "opening a source program reused a local identity"
      check body

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let family ← SourceFamily.forReference (.functor FunctorId.ringsMultiplicative)
  let universes := family.universeParams.map Level.param
  let native := family.source.family.instantiateLevelParams family.universeParams universes
  let owners ← liftM (m := IO) CasRuntime.OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let selected : SourceSelection Expr := {
    value := native, application := some {
      family := .registered family, universes, parameters := #[] } }
  SourceSelectionScope.withBinding owners.identities {} context selected fun context selections value => do
    let some binding := context.bindings.find? (·.expression == value)
      | throwError "the selected whole family lost its original typed binder"
    let request ← CasRuntime.PreparedRequest.forBoundary owners.identities program occurrence
      (.registered family) universes context #[] #[] #[] #[]
      (selections := selections) (selectionBinding := some binding.id)
    let source := request.source
    let some application := request.application
      | throwError "the selected whole family lost its original native application layout"
    for layout in #[source, application.result] do
      unless layout.selectionBinding == some binding.id do
        throwError "native input routing changed the original selected family binding"
      let some retained ← layout.selected? context
        | throwError "native input routing erased the original selected source family"
      unless retained.exactlyMatches Expr.equal selected do
        throwError "native input routing changed the complete selected source family"
    for original in #[source.source, application.result.source, application.resultTermFamily] do
      let original ← original.inContext context
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl original) (← mkEq original native))
    unless application.arguments.isEmpty do
      throwError "the nullary source family invented an application argument"
    let some (.projection route) ← application.inputProjectionThrough
        #[(#[``CategoryTheory.Cat.Hom.toFunctor, ``CategoryTheory.Functor.obj], 1)]
        #[``MonCat.carrier]
      | throwError "the selected family lost its native input carrier route"
    let .argument 0 := route.target
      | throwError "the selected family changed its original argument slot"
    unless route.path == #[``RingCat.carrier] do
      throwError "the selected family changed the original input carrier reference"
    let wrongNative ← mkAppM ``id #[native]
    unless !(wrongNative.equal native) &&
        (← isDefEq (← inferType wrongNative) (← inferType native)) do
      throwError "the wrong-family control requires a distinct body with the original native type"
    let wrong ← context.close wrongNative
    let rejected ← try
        discard <| ApplicationLayout.ofSource source context #[] (some wrong)
        pure false
      catch _ => pure true
    unless rejected do
      throwError "native input routing accepted a body other than the exact original declaration"

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← getConstInfo ``CategoryTheory.Limits.IsLimit
  let family := mkConst info.name (info.levelParams.map Level.param)
  forallTelescope (← inferType family) fun parameters _ => do
    let type := mkAppN family parameters
    withLocalDeclD `selectedLimit type fun selected => do
      let declarations := (← getLCtx).foldl (fun result decl => result.push decl) #[]
      let bindings := declarations.mapIdx fun index decl =>
        { id := ⟨"limit-layout", index⟩, role := .parameter,
          expression := mkFVar decl.fvarId : LocalBinding }
      let context ← ContextTelescope.capture bindings
      let layout ← SourceLayout.ofTerm (← context.close selected)
      unless layout.kind == .record do
        throwError "the selected limit witness lost its record layout"
      let some lift := layout.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.lift)
        | throwError "the selected limit witness lost its mediator field"
      unless lift.kind == .function && lift.wireIndex == some 0 do
        throwError "the mediator of a data-bearing subsingleton was erased"
      let callable ← lift.toLayout
      unless callable.address == #[lift.projection] &&
          callable.kind.actions.contains .apply do
        throwError "the mediator lost its projection address or application action"
      let some fac := layout.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.fac)
        | throwError "the selected limit witness lost its formal equation"
      unless fac.kind == .proof && fac.wireIndex.isNone &&
          fac.precedingDependencies.contains lift.sourceIndex do
        throwError "the formal equation lost its dependency on the retained mediator"
      fac.typeFamily.withOpen fun _ family => do
        lambdaTelescope family fun earlier type => do
          unless earlier.size == fac.sourceIndex &&
              type.containsFVar earlier[lift.sourceIndex]!.fvarId! do
            throwError "the field type lost its preceding-field parameterization"
      let some uniq := layout.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.uniq)
        | throwError "the selected limit witness lost its uniqueness law"
      uniq.typeFamily.withOpen fun _ family => do
        lambdaTelescope family fun earlier _ => do
          unless earlier.size == uniq.sourceIndex do
            throwError "the field type dropped an unused preceding formal slot"
      lift.source.withOpen fun _ expression => do
        unless (← whnf (← inferType expression)).isForall do
          throwError "the retained mediator lost its complete callable type"

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let function ← SourceLayout.ofTerm (← empty.close (mkConst ``Fin.last))
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"application-test", 0⟩, role := .parameter, expression := n }]
    let argument ← context.close n
    let result ← function.applyIn context #[argument]
    result.source.withOpen fun bindings expression => do
      let expected := mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) bindings[0]!.expression)
      unless ← isDefEq (← inferType expression) expected do
        throwError "callable application lost its dependent result type"

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let equivalence ← mkAppM ``Equiv.refl #[mkConst ``Nat]
  let layout ← SourceLayout.ofTerm (← context.close equivalence)
  unless layout.kind == .record && !layout.fields.isEmpty do
    throwError "the callable record lost its retained fields"
  let (result, application) ← ApplicationLayout.ofSource layout context
    #[← context.close (mkNatLit 1)]
  unless application.arguments.size == 1 &&
      application.arguments[0]?.map (·.wireIndex) == some (some 0) do
    throwError "native callable coercion lost its original argument position"
  result.source.withOpen fun _ expression => do
    unless ← isDefEq (← inferType expression) (mkConst ``Nat) do
      throwError "source application lost the record's accepted function coercion"




structure ChainedFieldsFixture where
  bound : Nat
  family : Fin bound → Type
  index : Fin bound
  value : family index

def chainedFieldsFixture : ChainedFieldsFixture := ⟨2, fun _ => Nat, 0, (5 : Nat)⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let layout ← SourceLayout.ofTerm (← context.close (mkConst ``chainedFieldsFixture))
  let some value := layout.fields.find? (·.projection == ``ChainedFieldsFixture.value)
    | throwError "the chained record lost its last field"
  unless value.precedingDependencies == #[0, 1, 2] do
    throwError "the field `value : family index` has preceding dependencies \
      {value.precedingDependencies}; its type names `family` and `index`, whose types name `bound`"




run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let source ← Elab.Term.elabTermAndSynthesize
    (← `(fun (n : Nat) =>
      (⟨(fun _ : Fin (Nat.succ n) => Nat × Nat),
        (⟨0, Nat.zero_lt_succ n⟩ : Fin (Nat.succ n)), ((7, 7) : Nat × Nat)⟩ :
        Σ p : Fin (Nat.succ n) → Type, Σ x : Fin (Nat.succ n), p x))) none
  let family ← forallTelescope (← inferType source) fun locals type =>
    mkLambdaFVars locals type (usedOnly := false) (usedLetOnly := false)
  let value ← mkAppOptM ``Sigma.mk #[
    some (mkConst ``Nat), some family, some (mkNatLit 0),
    some (mkApp source (mkNatLit 0))]
  let layout ← SourceLayout.ofTerm (← empty.close value)
  let some field := layout.fields.find? (·.projection == ``Sigma.snd)
    | throwError "the introduced-prefix control lost its original dependent field"
  let finalPath := #[``Sigma.snd, ``Sigma.snd]
  let shapePath := finalPath.push ``Prod.fst
  let fieldView ← field.dependencyView shapePath
  let orderedSource ← withLocalDeclD `unused (mkConst ``Nat) fun unused =>
    withLocalDeclD `n (mkConst ``Nat) fun n =>
      mkLambdaFVars #[unused, n] (mkApp source n) (usedOnly := false) (usedLetOnly := false)
  let (_, application) ← ApplicationLayout.ofSource
    (← SourceLayout.ofTerm (← empty.close orderedSource)) empty
    #[← empty.close (mkNatLit 0), ← empty.close (mkNatLit 0)]
  let finalDependencies ← application.dependenciesAt finalPath
  let shapeDependencies ← application.dependenciesAt shapePath
  unless finalDependencies.context.isEmpty && finalDependencies.arguments == #[1] &&
      shapeDependencies.context.isEmpty && shapeDependencies.arguments == #[1] &&
      fieldView.path == shapePath && fieldView.precedingDependencies == #[0] do
    throwError "introduced native prefixes lost their original dependencies: \
      final arguments={finalDependencies.arguments}, shape arguments={shapeDependencies.arguments}, \
      field prefix={fieldView.precedingDependencies}; expected #[1], #[1], #[0]"
  withLocalDeclD `unused (mkConst ``Nat) fun unused =>
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let context ← ContextTelescope.capture #[
        { id := ⟨"introduced-prefix-context", 0⟩, role := .parameter, expression := unused },
        { id := ⟨"introduced-prefix-context", 1⟩, role := .parameter, expression := n }]
      let capturedSource ← withLocalDeclD `ignored (mkConst ``Nat) fun ignored =>
        mkLambdaFVars #[ignored] (mkApp source n) (usedOnly := false) (usedLetOnly := false)
      let (_, application) ← ApplicationLayout.ofSource
        (← SourceLayout.ofTerm (← context.close capturedSource)) context #[← context.close (mkNatLit 0)]
      for path in #[finalPath, shapePath] do
        let dependencies ← application.dependenciesAt path
        unless dependencies.context == #[1] && dependencies.arguments.isEmpty do
          throwError "introduced native prefixes changed the original dependency planes: \
            context={dependencies.context}, arguments={dependencies.arguments}; expected #[1], #[]"



open CasRuntime in
run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `r (mkConst ``ChainedFieldsFixture) fun r => do
    let binding : LocalBinding := {
      id := ⟨"chained-runtime-prefix", 0⟩, role := .parameter, expression := r }
    let context ← ContextTelescope.capture #[binding]
    let layout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close r))
    let some callableField := layout.fields[1]?
      | throwError "the chained source lost its callable field layout"
    let some valueField := layout.fields[3]?
      | throwError "the chained source lost its final field layout"
    let owners ← liftM (m := IO) OwnerRegistry.new
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let mut fieldGraph := ValueGraph.empty owners.identities
    let mut fieldValues := #[]
    for prepared in layout.fields do
      let (next, value) ← liftM (m := IO) <| fieldGraph.stage owners.identities
        { program, occurrence, role := prepared.layout, parameters := #[none] }
        (.closure program #[])
      fieldGraph := next
      fieldValues := fieldValues.push value
    let retain (graph : ValueGraph) (fields : Array ValueBinding) :
        MetaM (ValueGraph × ValueBinding) := do
      let mut graph := graph
      let mut record ← liftM (m := IO) <|
        RecordPrefix.begin owners.identities program occurrence layout
          (parameters := some #[none])
      for field in fields do
        let (next, recordPrefix, _) ← liftM (m := IO) <| record.bind graph field
        graph := next
        record := recordPrefix
      let .ok payload := record.finish | throwError "the chained input record is incomplete"
      liftM (m := IO) <| graph.stage owners.identities
        { program, occurrence, role := layout.source, parameters := #[none] } payload
    let (graph, original) ← retain fieldGraph fieldValues
    let .ok parameter := RuntimeParameter.ofValue graph binding.id original
      | throwError "the original chained source record is outside its graph"
    let environment ← RuntimeEnvironment.capture owners.worker context #[parameter]
    let .ok callable := graph.project original 1
      | throwError "the dependent callable field is absent"
    let .ok value := graph.project original 3
      | throwError "the transitively dependent final field is absent"
    discard <| environment.checkResult graph callableField.layout callable
    discard <| environment.checkResult graph valueField.layout value
    discard <| environment.checkResult graph layout.source original
    let originalFields ← (Array.range 4).mapM fun index =>
      IO.ofExcept <| (graph.project original index).mapError IO.userError


    let (lazyGraph, lazyParent) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role := layout.source, parameters := #[none] } (.closure program #[])
    let .ok unresolvedParameter := RuntimeParameter.ofValue lazyGraph binding.id lazyParent
      | throwError "the lazy dependent source is outside its graph"
    let unresolved ← RuntimeEnvironment.capture owners.worker context #[unresolvedParameter]
    let beforeFailure : Option Exception ← try
      discard <| unresolved.checkResult lazyGraph valueField.layout value
      pure none
    catch error => pure (some error)
    let some beforeFailure := beforeFailure
      | throwError "an unpublished lazy source fabricated its dependent fields"
    unless (← beforeFailure.toMessageData.toString).startsWith
        "the runtime value has an unresolved consuming dependent reference" do throw beforeFailure
    let mut projectionGraph := lazyGraph
    for index in #[0, 1, 2] do
      let some prepared := layout.fields[index]?
        | throwError "the lazy dependent source lost a prefix field layout"
      let some baseline := originalFields[index]?
        | throwError "the lazy dependent source lost a captured prefix field"
      unless baseline.projectionAccesses.isEmpty do
        throwError "the captured baseline already carries a lazy projection access"
      let (next, _) ← projectionGraph.bindProjection owners.identities
        { program, occurrence, role := prepared.layout, parameters := #[none],
          access := some lazyParent, accessPath := #[prepared.field.projection] }
        baseline #[]
      projectionGraph := next
    let .ok retainedParameter := RuntimeParameter.ofValue projectionGraph binding.id lazyParent
      | throwError "the published lazy source is outside its graph"
    let retained ← RuntimeEnvironment.capture owners.worker context #[retainedParameter]
    discard <| retained.checkResult projectionGraph valueField.layout value
    for changed in #[0, 1, 2] do
      let some prepared := layout.fields[changed]?
        | throwError "the changed source lost a prefix field layout"
      let (graph, replacement) ← liftM (m := IO) <| graph.stage owners.identities
        { program, occurrence, role := prepared.layout, parameters := #[none] }
        (.closure program #[])


      let (mixedGraph, mixed) ← liftM (m := IO) <| graph.stage owners.identities
        { program, occurrence, role := layout.source, parameters := #[none] }
        (.product (originalFields.set! changed replacement))
      let mixedFailure : Option Exception ← try
        discard <| environment.checkResult mixedGraph layout.source mixed
        pure none
      catch error => pure (some error)
      let some mixedFailure := mixedFailure
        | throwError "the returned record accepted a changed actual prefix at {changed}"
      unless (← mixedFailure.toMessageData.toString).startsWith
          "the runtime value has a different consuming dependent reference" do throw mixedFailure
      let (graph, replaced) ← retain graph (originalFields.set! changed replacement)
      let .ok parameter := RuntimeParameter.ofValue graph binding.id replaced
        | throwError "the changed chained source record is outside its graph"
      let changedEnvironment ← RuntimeEnvironment.capture owners.worker context #[parameter]
      let failure : Option Exception ← try
        discard <| changedEnvironment.checkResult graph valueField.layout value
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "the dependent final field accepted a changed prefix at {changed}"
      unless (← failure.toMessageData.toString).startsWith
          "the runtime value has a different consuming dependent reference" do throw failure
    let missing ← RuntimeEnvironment.capture owners.worker context #[]
    let failure : Option Exception ← try
      discard <| missing.checkResult graph valueField.layout value
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "the dependent final field accepted a missing source record"
    unless missingValueOf failure binding.id do throw failure
