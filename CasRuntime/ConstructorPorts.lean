module

public import CasCompiler.ConstructorPorts
public import CasRuntime.PreparedRequest
public import CasRuntime.ResultCodec

public section

namespace CasRuntime

open Lean Meta CasCompiler

/-- The original constructor's actual data ports, admitted in native dependency order.
Proof slots stay present and empty. The current port has no runtime association until its
complete packet has passed that port's own native interface and dependency checks. -/
structure ConstructorPortPrefix (scope : RoleScope) where
  private mk ::
  plan : ConstructorPorts
  environment : RuntimeEnvironment
  private parameters : Array RuntimeParameter
  values : Array (Option ValueBinding)
  nextIndex : Nat

private def ConstructorPortPrefix.skipProofs (nativePrefix : ConstructorPortPrefix scope) :
    ConstructorPortPrefix scope := Id.run do
  let mut nextIndex := nativePrefix.nextIndex
  while nextIndex < nativePrefix.plan.ports.size do
    let some port := nativePrefix.plan.ports[nextIndex]? | break
    if port.argument.wireIndex.isSome then break
    nextIndex := nextIndex + 1
  return { nativePrefix with nextIndex }

/-- Open the already accepted formal constructor scope over the exact request inputs.
No native object/arrow is reconstructed from the answer packet. -/
opaque ConstructorPortPrefix.prepare (request : PreparedRequest) (graph : ValueGraph)
    (plan : ConstructorPorts) (marks : Array ValueBinding := #[]) :
    MetaM (ConstructorPortPrefix request.roles.scope) := do
  unless plan.originalContext.exactlyMatches request.environment.context do
    throwError "the constructor ports changed their original prepared request context"
  unless request.environment.values.size == plan.originalContext.entries.size do
    throwError "the constructor ports lost the complete original context value table"
  let mut parameters := #[]
  for entry in plan.originalContext.entries, value in request.environment.values do
    if let some value := value then
      parameters := parameters.push (← IO.ofExcept <|
        (RuntimeParameter.ofValue graph entry.id value).mapError IO.userError)
  let mut sourceMarks := request.environment.sourceMarks
  for term in #[plan.interface.presentation, plan.interface.diagram] ++
      plan.interface.standardization.toArray ++ plan.interface.dataConstructor.toArray do
    let retained ← IO.ofExcept <| (captureSourceMarks marks term).mapError IO.userError
    sourceMarks ← IO.ofExcept <| (mergeSourceMarks sourceMarks retained).mapError IO.userError
  let environment ← plan.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    RuntimeEnvironment.capture request.program.worker context parameters
      sourceMarks (some graph)
  return (⟨plan, environment, parameters, Array.replicate plan.ports.size none, 0⟩ :
    ConstructorPortPrefix request.roles.scope).skipProofs

def ConstructorPortPrefix.current? (nativePrefix : ConstructorPortPrefix scope) :
    Option ConstructorPort :=
  nativePrefix.plan.ports[nativePrefix.nextIndex]?

/-- The current native port is an original constructor binder, with only earlier actual
ports supplying its dependent type. It is not a fabricated projection from a reply shape. -/
opaque ConstructorPortPrefix.origin (nativePrefix : ConstructorPortPrefix scope)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM ValueOrigin := do
  request.requirePreparation scope
  let some port := nativePrefix.current?
    | throwError "the complete constructor has no remaining computational data port"
  let environment ← nativePrefix.environment.withSourceMarks #[] (some graph)
  environment.origin request.program request.occurrence port.argument.source

/-- Admit the actual stored port before assigning its original formal BindingId. All later
ports read this exact node/view through the ordinary complete runtime context machinery. -/
opaque ConstructorPortPrefix.bind (nativePrefix : ConstructorPortPrefix scope)
    (graph : ValueGraph) (value : ValueBinding) : MetaM (ConstructorPortPrefix scope) := do
  let some port := nativePrefix.current?
    | throwError "a constructor reply supplied an extra computational data port"
  unless port.argument.sourceIndex == nativePrefix.nextIndex && port.argument.wireIndex.isSome do
    throwError "the constructor reply changed its original native port order"
  let candidate ← nativePrefix.environment.checkResult graph port.argument.source value
  let parameter ← IO.ofExcept <|
    (RuntimeParameter.ofValue graph port.binding candidate.root).mapError IO.userError
  let parameters := nativePrefix.parameters.push parameter
  let environment ← nativePrefix.plan.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    RuntimeEnvironment.capture nativePrefix.environment.worker context parameters
      nativePrefix.environment.sourceMarks (some graph)
  return ({ nativePrefix with
    environment := environment
    parameters := parameters
    values := nativePrefix.values.set! nativePrefix.nextIndex (some candidate.root),
    nextIndex := nativePrefix.nextIndex + 1 }).skipProofs

/-- Finish only the complete original native telescope. Proof entries remain explicit empty
positions; callers project to the public non-Prop port order only after this check. -/
opaque ConstructorPortPrefix.finish (nativePrefix : ConstructorPortPrefix scope) :
    Except String (Array (Option ValueBinding)) := do
  let nativePrefix := nativePrefix.skipProofs
  unless nativePrefix.nextIndex == nativePrefix.plan.ports.size do
    throw "the constructor reply omitted a required dependent data port"
  for port in nativePrefix.plan.ports, value in nativePrefix.values do
    unless port.argument.wireIndex.isSome == value.isSome do
      throw "the constructor reply changed its original computational/proof port table"
  return nativePrefix.values

/-- A map port uses this port's exact original Hom binder and the already admitted
constructor prefix. Its endpoints are actual earlier ports or original request suppliers. -/
opaque ConstructorPortPrefix.mapCodec (nativePrefix : ConstructorPortPrefix scope)
    (graph : ValueGraph) (source target : ValueBinding) (marks : Array ValueBinding := #[])
    (operands : Array (ValueBinding × ValueBinding × ValueBinding) := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none) : MetaM PreparedMapResult := do
  let some port := nativePrefix.current?
    | throwError "the complete constructor has no remaining native map port"
  PreparedMapResult.forSource nativePrefix.environment port.argument.source graph source target
    marks none none none operands checkSymbolic

/-- Select only the original supplier named by the accepted constructor's native projection
route. This returns its retained parent and remaining native path; it performs no field
evaluation, association or endpoint equality search. Port admission remains with the prefix. -/
opaque _root_.CasCompiler.ConstructorPorts.projectionSupplier? (plan : ConstructorPorts)
    (environment : RuntimeEnvironment) (values : Array (Option ValueBinding))
    (path : Array Name) : MetaM (Option (ValueBinding × Array Name)) := do
  unless values.size == plan.ports.size do
    throwError "constructor projection requires the complete original native port table"
  let some selected ← plan.projectionAt path | return none
  let value ← match selected.target with
    | .argument index =>
      let some original := values[index]?
        | throwError "a constructor projection selected an undeclared native port"
      pure original
    | .context id =>
      IO.ofExcept <| (environment.lookup id).mapError IO.userError
  let some value := value
    | throwError "a constructor projection has no actual original supplier"
  return some (value, selected.path)

/-- Reopen only the exact complete table already materialized at this request's original
native port positions. Proof slots remain empty, and each computational view is admitted
again through the same dependency-ordered prefix without allocating graph nodes. -/
opaque ConstructorPortPrefix.ofValues (request : PreparedRequest) (graph : ValueGraph)
    (plan : ConstructorPorts) (values : Array (Option ValueBinding))
    (marks : Array ValueBinding := #[]) :
    MetaM (ConstructorPortPrefix request.roles.scope) := do
  unless values.size == plan.ports.size do
    throwError "constructor transport requires its complete native/proof port table"
  let mut nativePrefix ← ConstructorPortPrefix.prepare request graph plan marks
  for port in plan.ports, value in values do
    match port.argument.wireIndex, value with
    | none, none => pure ()
    | some _, some value =>
      unless nativePrefix.nextIndex == port.argument.sourceIndex do
        throwError "constructor transport changed its original dependent port order"
      unless value.role.address == port.argument.source.address &&
          value.role.source.context.exactlyMatches port.argument.source.source.context &&
          value.role.source.expression.equal port.argument.source.source.expression &&
          value.role.source.type.equal port.argument.source.source.type do
        throwError "constructor transport changed an original admitted port view"
      nativePrefix ← nativePrefix.bind graph value
    | _, _ => throwError "constructor transport changed a native computational/proof slot"
  discard <| IO.ofExcept <| nativePrefix.finish.mapError IO.userError
  return nativePrefix

/-- Present the accepted constructor's exact selected port as its native result field.
Both producing and consuming interfaces are checked; the immutable origin remains in its
complete original telescope, and no returned data is converted into a mathematical term. -/
opaque ConstructorPortPrefix.transportProjection (nativePrefix : ConstructorPortPrefix scope)
    (request : PreparedRequest) (path : Array Name) (draft : CellDraft) :
    MetaM (CellDraft × ValueBinding) := do
  request.requirePreparation scope
  let values ← IO.ofExcept <| nativePrefix.finish.mapError IO.userError
  let transport ← nativePrefix.plan.projectionTransport request.source path
  let some (parent, remaining) ← nativePrefix.plan.projectionSupplier?
      nativePrefix.environment values path
    | throwError "the accepted constructor lost its original result-field supplier"
  let some (selected, #[]) ← IO.ofExcept <|
      (draft.view.projectionFrontier parent remaining).mapError IO.userError
    | throwError "constructor transport requires the original stored field selection"
  let original ← nativePrefix.environment.checkResult draft.view transport.source selected
  unless original.root.value == selected.value &&
      original.root.associationIds == selected.associationIds do
    throwError "constructor transport changed its original selected port baseline"
  let (draft, value) ← draft.bindTelescopeTransport transport nativePrefix.environment.values
    nativePrefix.environment.sourceMarks original.root
  let candidate ← request.environment.checkResult draft.view transport.target value
  return (draft, candidate.root)
end CasRuntime
