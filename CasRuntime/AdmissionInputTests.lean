module

import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
meta import LeanCategories.Catalogue.Semantics.Algebra.Units

namespace CasRuntime.AdmissionInputTests

open Lean Meta Elab Term CasCompiler CasCatalogue

private def readTerm (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let parsed ← match Parser.runParserCategory (← getEnv) `cas_term text with
    | .ok parsed => pure parsed
    | .error error => throwError "the admission control did not parse: {error}"
  session.read ⟨parsed⟩

private def admissionReference (context : OpenContext) (selections : SourceSelectionScope Expr)
    (expression : Expr) : MetaM (SelectedSourceAdmission Expr) := do
  let some selected := selections.findAt? context expression.getAppFn
    | throwError "the original units source lost its exact selected binding"
  let selected ← selected.specialize expression.getAppArgs
  let some admitted := selected.admission
    | throwError "the original units source lost its complete admission reference"
  unless admitted.entry.id.raw == "obj.sets.units" do
    throwError "the original units source selected another admission"
  return admitted

private def runAdmission (kernel : Kernel) (transaction : CellTransaction)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (selections : SourceSelectionScope Expr) (admitted : SelectedSourceAdmission Expr)
    (arguments : Array Expr) : MetaM ValueBinding := do
  let selected : SourceSelection Expr := {
    value := mkAppN admitted.family arguments
    admission := some { admitted with arguments } }
  SourceSelectionScope.withBinding kernel.ledger.owners.identities selections context selected
    fun context selections expression =>
      kernel.run transaction context bound expression (selections := selections)

private def retainedCode (kernel : Kernel) (transaction : CellTransaction)
    (context : OpenContext) (expression : Expr) (captures : Array ValueBinding := #[])
    (bound : Std.HashMap BindingId ValueBinding := {})
    (selections : SourceSelectionScope Expr := {}) : MetaM ValueBinding := do
  let source ← context.close expression
  let program ← kernel.ledger.owners.identities.fresh .program
  let closedSelections ← selections.close context
  kernel.codes.modify (·.insert program (.term source closedSelections))
  let environment ← RuntimeEnvironment.captureBound kernel.ledger.owners.worker
    context bound (← transaction.view) (selections := selections)
  transaction.stage (← environment.origin program (← kernel.ledger.allocate)
    (← SourceLayout.ofTerm source (selections := closedSelections))) (.closure program captures)

private def field (graph : ValueGraph) (value : ValueBinding) (projection : Name) :
    MetaM ValueBinding := do
  let some declared := value.role.fields.find? (·.projection == projection)
    | throwError "the native admission control lost field {projection}"
  let some index := declared.wireIndex
    | throwError "the native admission control selected a proof field"
  IO.ofExcept <| (graph.project value index).mapError IO.userError





run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let source ← SourceSession.empty owners.identities


      let admitted ← readTerm source
        "((3 in (ℚ in Rings)) in (view (ℚ in Rings) along «fun.rings.multiplicative_monoid»())ˣ)"
      admitted.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let selections ← admitted.selections.inContext context
        unless bindings.all (fun binding =>
            binding.role == .selectedStructure && selections.contains binding.id) do
          throwError "the admission control unexpectedly acquired external source bindings"
        let admission ← admissionReference context selections expression
        let arguments := admission.arguments
        let element := admission.element
        let evidence := element + 1
        let some evidenceSource := arguments[evidence]?
          | throwError "the complete admission lost its supplied evidence slot"
        unless arguments.size == evidence + 1 do
          throwError "the accepted units admission changed its complete source telescope"
        let family ← SourceLayout.ofTerm (← context.close admission.family)
          (selections := admitted.selections)
        let (result, application) ← ApplicationLayout.ofSource family context
          (← arguments.mapM context.close)
        let some evidenceArgument := application.arguments[evidence]?
          | throwError "the admission layout lost its supplied evidence argument"
        unless application.arguments.size == arguments.size &&
            evidenceArgument.wireIndex.isSome do
          throwError "the admission erased a data-bearing evidence argument"
        for (path, slot, selected) in #[
            (#[``Units.val], element, #[]),
            (#[``Units.inv], evidence, #[``Invertible.invOf])] do
          let some (.projection route) ← application.inputProjectionThrough #[] path
            | throwError "the admitted field lost its complete native input route"
          match route.target with
          | .argument index =>
            unless index == slot do
              throwError "the admitted field selected another formal argument"
          | .context _ => throwError "the admitted field replaced a formal input by context"
          unless route.path == selected do
            throwError "the admitted field changed its native evidence projection"
        unless (result.fields.filter (·.wireIndex.isSome)).size == 2 do
          throwError "the accepted units admission lost a computational result field"

        let producer ← CellTransaction.begin kernel.ledger
        let evidenceRole ← SourceLayout.ofTerm (← context.close evidenceSource)
          (selections := admitted.selections)
        let mut evidenceFields : Array ValueBinding := #[]
        for declared in evidenceRole.fields do
          if declared.wireIndex.isSome then
            evidenceFields := evidenceFields.push
              (← retainedCode kernel producer context (← declared.source.inContext context)
                (selections := selections))
        unless evidenceFields.size == 1 &&
            evidenceRole.fields.any (fun declared =>
              declared.projection == ``Invertible.invOf && declared.wireIndex == some 0) do
          throwError "the accepted evidence lost its native computational field"
        let program ← owners.identities.fresh .program
        let evidenceEnvironment ← RuntimeEnvironment.captureBound owners.worker context {}
          (← producer.view) (selections := selections)
        let evidenceValue ← producer.stage
          (← evidenceEnvironment.origin program (← kernel.ledger.allocate) evidenceRole)
          (.product evidenceFields)
        let mut values : Array ValueBinding := #[]
        for argument in arguments, index in [:arguments.size] do


          if ← isProof argument then
            throwError "the accepted units control changed its formal proof positions"
          values := values.push (← if index == evidence then pure evidenceValue
            else retainedCode kernel producer context argument (selections := selections))
        withApplicationInputs owners.identities context {} admission.family arguments
            (values.map some) fun context bound retained => do
            let retainedEvidence := retained[evidence]!
            let parentSource ← mkAppM ``Prod.mk #[retainedEvidence, mkNatLit 0]
            let evidenceParent ← retainedCode kernel producer context parentSource #[evidenceValue] bound
              (selections := selections)
            let .ok _ ← producer.commit
              | throwError "the admission inputs could not publish their original references"

            let consumer ← CellTransaction.begin kernel.ledger
            try
              let value ← runAdmission kernel consumer context bound selections admission retained
              let graph ← consumer.view
              let some node := graph.find value.value
                | throwError "the admitted result is outside its graph"
              let some fields := node.payload.data.storedFields?
                | throwError "the complete admission returned no native record fields"
              unless fields.size == 2 do
                throwError "the complete admission changed its mandatory native field arity"
              let some originalValue := values[element]?
                | throwError "the admission control lost its retained original element"
              let some originalInverse := evidenceFields[0]?
                | throwError "the admission control lost its retained original evidence field"
              let selectedValue ← field graph value ``Units.val
              let selectedInverse ← field graph value ``Units.inv
              unless selectedValue.value == originalValue.value &&
                  originalValue.associationIds.toList.isPrefixOf selectedValue.associationIds.toList &&
                  selectedInverse.value == originalInverse.value &&
                  originalInverse.associationIds.toList.isPrefixOf selectedInverse.associationIds.toList do
                throwError "the admitted record changed its original element or supplied inverse field"
              let .ok (some baseline) :=
                  graph.projectionBasis selectedInverse evidenceValue #[``Invertible.invOf]
                | throwError "the admitted inverse lost its exact evidence-field access"
              unless baseline.value == originalInverse.value &&
                  baseline.associationIds == originalInverse.associationIds do
                throwError "the admitted inverse acquired another evidence baseline"
              unless (← kernel.dispatches.get).isEmpty do
                throwError "the complete native admission dispatched a mathematical operation"
              let .ok _ ← consumer.commit
                | throwError "the complete admission could not publish its native result"
            finally discard <| consumer.abort



            let projected ← CellTransaction.begin kernel.ledger
            try
              withBoundValue owners.identities context bound parentSource evidenceParent fun context bound parent => do
                let marked := retained.set! evidence (mkProj ``Prod 0 parent)
                let value ← runAdmission kernel projected context bound selections admission marked
                let graph ← projected.view
                let .ok (some actualEvidence) := graph.projected? evidenceParent #[``Prod.fst]
                  | throwError "used projected admission evidence did not demand its actual parent"
                unless actualEvidence.value == evidenceValue.value do
                  throwError "used projected admission evidence fabricated a replacement h"
                let selectedInverse ← field graph value ``Units.inv
                let some originalInverse := evidenceFields[0]?
                  | throwError "the projected evidence control lost its original inverse field"
                let .ok (some baseline) := graph.projectionBasis selectedInverse evidenceParent
                    #[``Prod.fst, ``Invertible.invOf]
                  | throwError "used admission evidence lost its complete original parent/path"
                unless baseline.value == originalInverse.value &&
                    selectedInverse.value == originalInverse.value do
                  throwError "used admission evidence replaced its original selected field"
                unless (← kernel.dispatches.get).isEmpty do
                  throwError "native projected admission evidence dispatched a mathematical operation"
                let .ok _ ← projected.commit
                  | throwError "the projected admission evidence could not publish"
            finally discard <| projected.abort



            let absent ← CellTransaction.begin kernel.ledger
            try
              let .ok payload := ValuePayload.descriptor .null #[]
                | throwError "the absent-field evidence control has an invalid descriptor"
              let graph ← absent.view
              let environment ← RuntimeEnvironment.captureBound owners.worker context bound graph
                (selections := selections)
              let role ← SourceLayout.ofTerm (← context.close retained[evidence]!)
                (selections := ← selections.close context)
              let missing ← absent.stage
                (← environment.origin program (← kernel.ledger.allocate) role) payload
              SourceSelectionScope.withBinding owners.identities selections context
                  { value := evidenceSource } fun context selections emptySource => do
                withBoundValue owners.identities context bound emptySource missing
                    (fun context bound retainedMissing => do
                      let marked := retained.set! evidence retainedMissing
                      let failure : Option Exception ← try
                          discard <| runAdmission kernel absent context bound selections admission marked
                          pure none
                        catch error => pure (some error)
                      let some failure := failure
                        | throwError "the admission fabricated its absent computational evidence field"
                      unless CasCatalogue.Exception.stratum? failure == some .noImplementation do
                        throw failure
                      unless (← kernel.dispatches.get).isEmpty do
                        throwError "absent admission data triggered an unrelated mathematical dispatch"
                    ) (declaredType := some (← inferType retained[evidence]!))
            finally discard <| absent.abort



            let absentParent ← CellTransaction.begin kernel.ledger
            try
              let .ok payload := ValuePayload.descriptor .null #[]
                | throwError "the projected absent-field control has an invalid descriptor"
              let graph ← absentParent.view
              let environment ← RuntimeEnvironment.captureBound owners.worker context bound graph
                (selections := selections)
              let role ← SourceLayout.ofTerm (← context.close retained[evidence]!)
                (selections := ← selections.close context)
              let missing ← absentParent.stage
                (← environment.origin program (← kernel.ledger.allocate) role) payload
              SourceSelectionScope.withBinding owners.identities selections context
                  { value := evidenceSource } fun context selections emptySource => do
                withBoundValue owners.identities context bound emptySource missing
                    (fun context bound retainedMissing => do
                      let parentSource ← mkAppM ``Prod.mk #[retainedMissing, mkNatLit 0]
                      let parentValue ← retainedCode kernel absentParent context parentSource #[missing] bound
                        (selections := selections)
                      withBoundValue owners.identities context bound parentSource parentValue fun context bound parent => do
                        let marked := retained.set! evidence (mkProj ``Prod 0 parent)
                        let failure : Option Exception ← try
                          discard <| runAdmission kernel absentParent context bound selections admission marked
                          pure none
                        catch error => pure (some error)
                        let some failure := failure
                          | throwError "used projected evidence fabricated its absent native field"
                        unless CasCatalogue.Exception.stratum? failure == some .noImplementation do
                          throw failure
                        unless (← kernel.dispatches.get).isEmpty do
                          throwError "missing projected admission data dispatched an unrelated operation"
                    ) (declaredType := some (← inferType retained[evidence]!))
            finally discard <| absentParent.abort
    finally kernel.close
  finally setEnv original



run_cmd Lean.Elab.Command.liftTermElabM do
  let function ← elabTermAndSynthesize (← `(fun (n : Nat) (p : Fin n) => p.val)) none
  forallTelescope (← inferType function) fun locals _ => do
    let bindings := locals.mapIdx fun index expression =>
      ({ id := ⟨"admission-input-type-prefix", index⟩, role := .parameter, expression } : LocalBinding)
    let context ← ContextTelescope.capture bindings
    let (_, application) ← ApplicationLayout.ofSource
      (← SourceLayout.ofTerm (← context.close function)) context
      (← locals.mapM fun argument => context.close argument)
    let some required ← application.inputResultArguments (bindings.map (·.id))
      | throwError "the native dependent field lost its complete source coverage"
    unless required == #[0, 1] do
      throwError "source coverage erased the selected input's transitive type parameter"





run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let context ← ContextTelescope.capture #[]
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let pairSource ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 11]
      let pair ← retainedCode kernel producer context pairSource
      let first ← retainedCode kernel producer context (mkNatLit 7)
      let identitySource ← elabTermAndSynthesize
        (← `(fun (x : Nat) (_h : Nat) => x)) none
      let incompleteSource ← elabTermAndSynthesize
        (← `(fun (p : Nat × Nat) (_h : Nat) => (p.1, Nat.succ p.2))) none
      let identity ← retainedCode kernel producer context identitySource
      let incomplete ← retainedCode kernel producer context incompleteSource
      let .ok _ ← producer.commit
        | throwError "the missing-input controls could not publish their native sources"
      withBoundValue owners.identities context {} pairSource pair fun context bound parent => do
        let absentSource ← context.close (mkProj ``Prod 0 parent)

        let completed ← CellTransaction.begin kernel.ledger
        try
          let graph ← completed.view
          let parameters ← bound.toArray.mapM fun (id, value) =>
            IO.ofExcept <| (RuntimeParameter.ofValue graph id value).mapError IO.userError
          let .ok firstArgument := RuntimeArgument.ofValue graph 0 first
            | throwError "the identity control lost its supplied first argument"
          let request ← PreparedRequest.forApplication owners.identities program
            (← kernel.ledger.allocate) context identity
            #[← context.close (mkNatLit 7), absentSource] #[firstArgument] parameters (some graph)
          let some missingRole := request.roles.arguments[1]?
            | throwError "the unused computational argument disappeared from the telescope"
          unless missingRole.wireIndex == some 1 do
            throwError "unused data were relabeled as a formal proof"
          let failure : Option Exception ← try
            discard <| request.admitInputs graph
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "ordinary input admission accepted an absent computational argument"
          unless failure.toMessageData.hasTag
              (· == `CasRuntime.InputRoleMap.missingArgument) do throw failure
          let resolverCalls ← IO.mkRef 0
          let executorCalls ← IO.mkRef 0
          let response ← Execute.run
            (fun _ _ => do
              executorCalls.modify (· + 1)
              throwError "the complete identity reached its ordinary executor")
            (PFunctor.FreeM.lift (P := OperationalSignature) request) completed
            (some (fun _ => do
              resolverCalls.modify (· + 1)
              throwError "the complete identity forced unused projected evidence"))
          unless response.root.value == first.value &&
              first.associationIds.toList.isPrefixOf response.root.associationIds.toList &&
              (← resolverCalls.get) == 0 && (← executorCalls.get) == 0 do
            throwError "source-fixed identity changed its input or demanded unused evidence"
          let graph ← completed.view
          let .ok none := graph.projected? pair #[``Prod.fst]
            | throwError "unused projected evidence acquired an actual field value"
          let some application := request.origin.application
            | throwError "the completed identity lost its complete formal application"
          unless application.arguments.size == 2 && (application.arguments[1]?.bind id).isNone do
            throwError "the completed identity manufactured its unused computational argument"
          let .ok published ← completed.commit
            | throwError "the sealed identity completion could not publish"
          let some receipt := published.receipt request.occurrence
            | throwError "the sealed identity completion lost its receipt"
          unless !(receipt.association.inputs.lookup published.graph missingRole.role.id).isOk &&
              !(receipt.association.inputs.arguments published.graph).isOk do
            throwError "the fixed completion exposed omitted data as an ordinary complete input map"
        finally discard <| completed.abort

        let refused ← CellTransaction.begin kernel.ledger
        try
          let graph ← refused.view
          let parameters ← bound.toArray.mapM fun (id, value) =>
            IO.ofExcept <| (RuntimeParameter.ofValue graph id value).mapError IO.userError
          let .ok pairArgument := RuntimeArgument.ofValue graph 0 pair
            | throwError "the incomplete control lost its supplied record"
          let request ← PreparedRequest.forApplication owners.identities program
            (← kernel.ledger.allocate) context incomplete
            #[← context.close pairSource, absentSource] #[pairArgument] parameters (some graph)
          unless (← request.inputResultPlan graph).isNone do
            throwError "an unknown result field acquired complete input coverage"
          let resolverCalls ← IO.mkRef 0
          let executorCalls ← IO.mkRef 0
          let failure : Option Exception ← try
            discard <| Execute.run
              (fun _ _ => do
                executorCalls.modify (· + 1)
                throwError "incomplete inputs reached an ordinary executor")
              (PFunctor.FreeM.lift (P := OperationalSignature) request) refused
              (some (fun _ => do
                resolverCalls.modify (· + 1)
                throwError "incomplete inputs forced a partial input-result route"))
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "an incomplete result bypassed total input admission before effects"
          unless failure.toMessageData.hasTag
              (· == `CasRuntime.InputRoleMap.missingArgument) do throw failure
          unless (← resolverCalls.get) == 0 && (← executorCalls.get) == 0 do
            throwError "an incomplete result bypassed total input admission before effects"
          unless ((← SessionSnapshot.current).receipt request.occurrence).isNone do
            throwError "the incomplete result published a completion"
        finally discard <| refused.abort
    finally kernel.close
  finally setEnv original




run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let owners ← OwnerRegistry.new
    let source ← SourceSession.empty owners.identities
    let inverse ← readTerm source
      "(((3 in (ℚ in Rings)) in (view (ℚ in Rings) along «fun.rings.multiplicative_monoid»())ˣ))⁻¹"
    inverse.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      context.withOriginalSources #[expression] fun originals => do
        let letIds := (← getLCtx).foldl (fun ids declaration =>
          if declaration.isLet then ids.push declaration.fvarId else ids) #[]
        let expression ← zetaDeltaFVars originals[0]! letIds
        unless (expression.find? (·.isConstOf ``CasCatalogue.Algebra.Units.groupInverse)).isSome do
          throwError "the selected inverse lost its accepted operation declaration"
  finally setEnv original

end CasRuntime.AdmissionInputTests
