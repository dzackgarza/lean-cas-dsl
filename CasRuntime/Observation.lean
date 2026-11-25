module

public import CasCompiler.Program
public import CasCompiler.Roles
public import CasCompiler.ContextSnapshot
public import CasRuntime.Environment

@[expose] public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasTools

inductive PreparedAction
  | primitive (boundary : ProgramBoundary) (universeArguments : List Level)
  | project (operand : ValueBinding) (field : FieldLayout)
  | apply (callable : ValueBinding) (arguments : Array ClosedTerm)
      (values : Array (Option ValueBinding))

/-- Inert source and request observations, prepared before the request is emitted.
The descriptor owns only immutable JSON and strings, never an elaborator or renderer action. -/
structure ObservationDescriptor where
  private mk ::
  native : Json
  readable : Json
  selection : Option Json
  sourceSnapshot : Option Json

namespace Observation

def identityJson {kind : IdentityKind} (id : RuntimeId kind) : Json :=
  Json.mkObj [("worker", toJson id.worker), ("serial", toJson id.serial)]

def namesJson (names : Array Name) : Json := Json.arr (names.map NativeExpression.nameJson)

/-- Preserve the original source plane and exact native projection path. -/
def inputProjectionJson (projection : InputProjection) : Json :=
  let target := match projection.target with
    | .argument index => Json.mkObj [("argument", toJson index)]
    | .context binding => Json.mkObj [("context", ContextSnapshot.bindingJson binding)]
  Json.mkObj [("target", target), ("path", namesJson projection.path)]

/-- Display names supplement, rather than replace, the exact native source address. -/
def readableInputProjectionJson (projection : InputProjection) : Json :=
  (inputProjectionJson projection).setObjVal! "displayPath"
    (toJson (projection.path.map (·.toString (escape := false))))

def referenceJson (reference : ComputationRef) : Json :=
  let (kind, id) := match reference with
    | .operation id => ("operation", id.raw)
    | .functor id => ("functor", id.raw)
    | .method id => ("method", id.raw)
    | .construction id => ("construction", id.raw)
    | .morphism id => ("morphism", id.raw)
  Json.mkObj [("kind", toJson kind), ("id", toJson id)]

def prerequisiteJson (source : CheckedComputationPrerequisite) :
    StateM NativeExpression.Builder Json := do
  return Json.mkObj [("reference", referenceJson source.reference),
    ("declaration", NativeExpression.nameJson source.declaration),
    ("family", toJson (← NativeExpression.Builder.add source.family)),
    ("familyType", toJson (← NativeExpression.Builder.add source.familyType))]

def programJson (program : SourceProgram) : StateM NativeExpression.Builder Json := do
  let source := program.source
  let entry := source.entry
  let prerequisites ← source.prerequisites.mapM prerequisiteJson
  return Json.mkObj [
    ("entry", Json.mkObj [("id", toJson entry.id.raw),
      ("target", referenceJson entry.target),
      ("prerequisites", toJson (entry.prerequisites.map referenceJson)),
      ("plan", NativeExpression.nameJson entry.plan),
      ("correctness", NativeExpression.nameJson entry.correctness)]),
    ("universeParams", namesJson source.universeParams.toArray),
    ("targetDeclaration", NativeExpression.nameJson source.targetDeclaration),
    ("target", toJson (← NativeExpression.Builder.add source.target)),
    ("familyType", toJson (← NativeExpression.Builder.add source.familyType)),
    ("prerequisites", toJson prerequisites),
    ("template", toJson (← NativeExpression.Builder.add source.template)),
    ("plan", toJson (← NativeExpression.Builder.add source.plan)),
    ("correctness", toJson (← NativeExpression.Builder.add source.correctness))]

def boundaryJson (boundary : ProgramBoundary) : StateM NativeExpression.Builder Json := do
  match boundary with
  | .registered family =>
    return Json.mkObj [("kind", toJson "registered"),
      ("source", ← prerequisiteJson family.source),
      ("universeParams", namesJson family.universeParams.toArray)]
  | .target program =>
    return Json.mkObj [("kind", toJson "target"), ("program", ← programJson program)]
  | .prerequisite program index =>
    return Json.mkObj [("kind", toJson "prerequisite"),
      ("program", ← programJson program), ("index", toJson index.val)]
  | .lift family =>
    return Json.mkObj [("kind", toJson "lift"), ("lift", toJson family.lift.raw),
      ("port", toJson family.port.name),
      ("universeParams", namesJson family.universeParams.toArray),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("familyType", toJson (← NativeExpression.Builder.add family.familyType))]

  | .presentation family =>
    return Json.mkObj [("kind", toJson "presentation"),
      ("entry", toJson (reprStr family.entry)),
      ("declaration", NativeExpression.nameJson family.entry.declaration),
      ("source", toJson (reprStr family.source)), ("target", toJson (reprStr family.target)),
      ("category", toJson (reprStr family.category)),
      ("universeParams", namesJson family.universeParams.toArray),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("familyType", toJson (← NativeExpression.Builder.add family.familyType)),
      ("forwardPath", namesJson family.forwardPath), ("inversePath", namesJson family.inversePath)]
  | .routedMethod family =>
    let returning ← family.returns.mapM fun returned => do
      return Json.mkObj [
        ("route", Json.mkObj [("source", toJson (reprStr returned.route.source)),
          ("target", toJson (reprStr returned.route.target)),
          ("refs", toJson (reprStr returned.route.refs))]),
        ("rows", toJson (returned.rows.map fun row => row.id.raw)),
        ("category", toJson (reprStr returned.category)),
        ("categoryFamily", toJson (← NativeExpression.Builder.add returned.categoryFamily)),
        ("resultFamily", toJson (← NativeExpression.Builder.add returned.resultFamily)),
        ("actions", toJson (← returned.actions.mapM NativeExpression.Builder.add)),
        ("evidences", toJson (← returned.evidences.mapM NativeExpression.Builder.add)),
        ("agreement", toJson (← returned.agreement.mapM NativeExpression.Builder.add))]
    return Json.mkObj [("kind", toJson "routedMethod"),
      ("entry", toJson (reprStr family.entry)), ("functor", toJson (reprStr family.functor)),
      ("route", Json.mkObj [("source", toJson (reprStr family.route.source)),
        ("target", toJson (reprStr family.route.target)),
        ("refs", toJson (reprStr family.route.refs))]),
      ("universeParams", namesJson family.universeParams.toArray),
      ("parameterCount", toJson family.parameterCount),
      ("categoryFamily", toJson (← NativeExpression.Builder.add family.categoryFamily)),
      ("functorFamily", toJson (← NativeExpression.Builder.add family.functorFamily)),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("actions", toJson (← family.actions.mapM NativeExpression.Builder.add)),
      ("return", toJson returning)]
  | .property family =>
    return Json.mkObj [("kind", toJson "property"),
      ("entry", toJson (reprStr family.entry)), ("classifier", toJson (reprStr family.classifier)),
      ("route", Json.mkObj [("source", toJson (reprStr family.route.source)),
        ("target", toJson (reprStr family.route.target)),
        ("refs", toJson (reprStr family.route.refs))]),
      ("universeParams", namesJson family.universeParams.toArray),
      ("parameterCount", toJson family.parameterCount),
      ("categoryFamily", toJson (← NativeExpression.Builder.add family.categoryFamily)),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("actions", toJson (← family.actions.mapM NativeExpression.Builder.add))]
  | .application family =>
    let owner := match family.owner with
      | .morphism entry => Json.mkObj [("kind", toJson "morphism"), ("entry", toJson (reprStr entry))]
      | .application entry => Json.mkObj [("kind", toJson "application"), ("entry", toJson (reprStr entry))]
    return Json.mkObj [("kind", toJson "application"), ("owner", owner),
      ("operation", toJson family.operation),
      ("declaration", NativeExpression.nameJson family.declaration),
      ("category", toJson (reprStr family.category)),
      ("universeParams", namesJson family.universeParams.toArray),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("familyType", toJson (← NativeExpression.Builder.add family.familyType)),
      ("path", namesJson family.path)]
  | .point family =>
    let owner := match family.owner with
      | .named (.morphism entry) =>
        Json.mkObj [("kind", toJson "morphism"), ("entry", toJson (reprStr entry))]
      | .named (.application entry) =>
        Json.mkObj [("kind", toJson "application"), ("entry", toJson (reprStr entry))]
      | .component entry constructors inverse =>
        Json.mkObj [("kind", toJson "component"), ("entry", toJson (reprStr entry)),
          ("constructors", toJson (constructors.map (·.raw))), ("inverse", toJson inverse)]
      | .cartesian entry =>
        Json.mkObj [("kind", toJson "cartesian"), ("entry", toJson (reprStr entry))]
      | .binder entry =>
        Json.mkObj [("kind", toJson "binder"), ("entry", toJson (reprStr entry))]
      | .action edge =>
        Json.mkObj [("kind", toJson "action"), ("edge", edgeImageDescriptor edge)]
    return Json.mkObj [("kind", toJson "point"), ("owner", owner),
      ("operation", toJson family.operation), ("whole", toJson family.whole),
      ("invocation", toJson family.invocation),
      ("declaration", NativeExpression.nameJson family.declaration),
      ("universeParams", namesJson family.universeParams.toArray),
      ("parameterCount", toJson family.parameterCount),
      ("category", toJson (reprStr family.category)),
      ("categoryFamily", toJson (← NativeExpression.Builder.add family.categoryFamily)),
      ("arrowFamily", toJson (← NativeExpression.Builder.add family.arrowFamily)),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("familyType", toJson (← NativeExpression.Builder.add family.familyType))]
  | .objectAction family =>
    return Json.mkObj [("kind", toJson "objectAction"),
      ("edge", edgeImageDescriptor family.edge), ("operation", toJson family.operation),
      ("declaration", NativeExpression.nameJson family.declaration),
      ("universeParams", namesJson family.universeParams.toArray),
      ("parameterCount", toJson family.parameterCount),
      ("category", toJson (reprStr family.category)),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("familyType", toJson (← NativeExpression.Builder.add family.familyType))]
  | .limit family owner =>
    return Json.mkObj [("kind", toJson "limit"), ("entry", toJson (reprStr family.entry)),
      ("declaration", NativeExpression.nameJson family.entry.declaration),
      ("universeParams", namesJson family.universeParams.toArray),
      ("parameterCount", toJson family.parameterCount),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("owner", ← ContextSnapshot.closedTermJson owner)]
  | .limitUniversal family owner =>
    return Json.mkObj [("kind", toJson "limitUniversal"),
      ("entry", toJson (reprStr family.presentation.entry)),
      ("operation", toJson family.operation),
      ("projection", NativeExpression.nameJson family.projection),
      ("declaration", NativeExpression.nameJson family.presentation.entry.declaration),
      ("universeParams", namesJson family.universeParams.toArray),
      ("parameterCount", toJson family.parameterCount),
      ("family", toJson (← NativeExpression.Builder.add family.family)),
      ("owner", ← ContextSnapshot.closedTermJson owner)]
  | .creation family =>
    return Json.mkObj [("kind", toJson "creation"),
      ("lift", toJson family.family.entry.id.raw),
      ("target", toJson family.target.entry.id.raw),
      ("construction", NativeExpression.nameJson family.construction),
      ("requestFamily", ← ContextSnapshot.closedTermJson family.requestFamily),
      ("owner", ← ContextSnapshot.closedTermJson family.owner)]

def fieldJson (field : FieldLayout) : StateM NativeExpression.Builder Json := do
  return Json.mkObj [("address", namesJson field.address),
    ("projection", NativeExpression.nameJson field.projection),
    ("sourceIndex", toJson field.sourceIndex), ("wireIndex", toJson field.wireIndex),
    ("precedingDependencies", toJson field.precedingDependencies),
    ("source", ← ContextSnapshot.closedTermJson field.source),
    ("typeFamily", ← ContextSnapshot.closedTermJson field.typeFamily),
    ("kind", toJson (reprStr field.kind)),
    ("actions", toJson (field.kind.actions.map reprStr))]

def layoutJson (layout : SourceLayout) : StateM NativeExpression.Builder Json := do
  let fields ← layout.fields.mapM fieldJson
  return Json.mkObj [("address", namesJson layout.address),
    ("source", ← ContextSnapshot.closedTermJson layout.source),
    ("kind", toJson (reprStr layout.kind)),
    ("actions", toJson (layout.kind.actions.map reprStr)),
    ("fields", toJson fields), ("contextDependencies", toJson layout.contextDependencies),
    ("inputProjection", toJson (layout.inputProjection.map inputProjectionJson))]

def recordJson (record : RecordLayout) : StateM NativeExpression.Builder Json := do
  let fields ← record.fields.mapM fun prepared => do
    return Json.mkObj [("field", ← fieldJson prepared.field),
      ("layout", ← layoutJson prepared.layout)]
  return Json.mkObj [("source", ← layoutJson record.source), ("fields", toJson fields)]

def applicationJson (application : ApplicationLayout) : StateM NativeExpression.Builder Json := do
  let arguments ← application.arguments.mapM fun argument => do
    return Json.mkObj [("sourceIndex", toJson argument.sourceIndex),
      ("wireIndex", toJson argument.wireIndex), ("binderInfo", toJson argument.binderInfo),
      ("precedingDependencies", toJson argument.precedingDependencies),
      ("source", ← layoutJson argument.source),
      ("typeFamily", ← ContextSnapshot.closedTermJson argument.typeFamily)]
  return Json.mkObj [("arguments", toJson arguments),
    ("resultDependencies", toJson application.resultDependencies),
    ("resultTypeFamily", ← ContextSnapshot.closedTermJson application.resultTypeFamily),
    ("resultTermFamily", ← ContextSnapshot.closedTermJson application.resultTermFamily),
    ("result", ← layoutJson application.result),
    ("resultContextDependencies", toJson application.resultContextDependencies)]

/-- References name the actual node and ordered association chain. They contain no payload. -/
def valueIdentityJson (value : ValueBinding) : Json :=
  Json.mkObj [("value", identityJson value.value),
    ("associations", toJson (value.associationIds.map identityJson))]

def sourceMarksJson (marks : Array (Nat × ValueBinding)) : Json :=
  toJson (marks.map fun (key, value) =>
    Json.mkObj [("key", toJson key), ("reference", valueIdentityJson value)])

def valueReferenceJson (value : ValueBinding) : StateM NativeExpression.Builder Json := do
  let markedTypeRoles ← value.markedTypeRoles.mapM layoutJson
  let result := (valueIdentityJson value).setObjVal! "role" (← layoutJson value.role)
  let result := result.setObjVal! "sourceMarks" (sourceMarksJson value.sourceMarks)
  let result := result.setObjVal! "sourceDependencies"
    (toJson (value.sourceDependencies.map valueIdentityJson))
  return result.setObjVal! "markedTypeRoles" (toJson markedTypeRoles)

def actualArgumentJson (argument : RuntimeArgument) (marks : Array (Nat × ValueBinding)) : Json :=
  Json.mkObj [("sourceIndex", toJson argument.index),
    ("reference", valueIdentityJson argument.value),
    ("marks", sourceMarksJson marks)]

def valuesJson (values : Array (Option ValueBinding)) : StateM NativeExpression.Builder Json := do
  return toJson (← values.mapM fun value => value.mapM valueReferenceJson)

/-- Preserve the selected field and application associations of this actual reference.
Their ordered operands remain references to the existing graph, not copied returned values. -/
def valueJson (value : ValueBinding) : StateM NativeExpression.Builder Json := do
  let fields ← value.instantiations.mapM fun field => do
    let association := field.association
    let view ← field.view.mapM fun view => do
      return Json.mkObj [("path", namesJson view.path),
        ("typeFamily", ← ContextSnapshot.closedTermJson view.typeFamily),
        ("precedingDependencies", toJson view.precedingDependencies)]
    return Json.mkObj [("id", identityJson field.id),
      ("association", Json.mkObj [("id", identityJson association.id),
        ("program", identityJson association.program),
        ("occurrence", identityJson association.occurrence),
        ("layout", ← recordJson association.layout)]),
      ("field", ← fieldJson field.field), ("preceding", ← valuesJson field.preceding),
      ("dependencyView", toJson view)]
  let applications ← value.applications.mapM fun application => do
    let association := application.association
    return Json.mkObj [("association", Json.mkObj [("id", identityJson association.id),
        ("program", identityJson association.program),
        ("occurrence", identityJson association.occurrence),
        ("layout", ← applicationJson association.layout),
        ("path", namesJson association.path), ("dependencies", toJson association.dependencies),
        ("contextDependencies", toJson association.contextDependencies)]),
      ("parameters", ← valuesJson application.parameters),
      ("applicationParameters", ← valuesJson application.applicationParameters),
      ("arguments", ← valuesJson application.arguments),
      ("callable", toJson (← application.callable.mapM valueReferenceJson)),
      ("access", toJson (← application.access.mapM valueReferenceJson))]
  let projections ← value.projectionAccesses.mapM fun (parent, path) => do
    return Json.mkObj [("parent", ← valueReferenceJson parent), ("path", namesJson path)]
  return Json.mkObj [("reference", ← valueReferenceJson value),
    ("fields", toJson fields), ("applications", toJson applications),
    ("projections", toJson projections)]

def applicationOriginJson (origin : ApplicationOrigin) : StateM NativeExpression.Builder Json := do
  return Json.mkObj [("layout", ← applicationJson origin.layout),
    ("parameters", ← valuesJson origin.parameters), ("arguments", ← valuesJson origin.arguments),
    ("path", namesJson origin.path), ("dependencies", toJson origin.dependencies),
    ("contextDependencies", toJson origin.contextDependencies),
    ("callable", toJson (← origin.callable.mapM valueJson))]

def originJson (origin : ValueOrigin) : StateM NativeExpression.Builder Json := do
  return Json.mkObj [("occurrence", identityJson origin.occurrence),
    ("program", identityJson origin.program), ("role", ← layoutJson origin.role),
    ("parameters", ← valuesJson origin.parameters),
    ("application", toJson (← origin.application.mapM applicationOriginJson)),
    ("access", toJson (← origin.access.mapM valueJson)),
    ("accessPath", namesJson origin.accessPath),
    ("sourceMarks", sourceMarksJson origin.sourceMarks),
    ("sourceDependencies", toJson (origin.sourceDependencies.map valueIdentityJson))]

def roleScopeJson (scope : RoleScope) : Json :=
  Json.mkObj [("program", identityJson scope.program),
    ("occurrence", identityJson scope.occurrence), ("preparation", identityJson scope.preparation)]

def roleIdJson (role : RoleId) : Json :=
  let address := match role.address with
    | .context binding => Json.mkObj [("context", ContextSnapshot.bindingJson binding)]
    | .argument position => Json.mkObj [("argument", toJson position)]
    | .result path => Json.mkObj [("result", namesJson path)]
    | .capture position => Json.mkObj [("capture", toJson position)]
  Json.mkObj [("scope", roleScopeJson role.scope), ("address", address)]

def roleJson (role : ComputationalRole) : StateM NativeExpression.Builder Json := do
  return Json.mkObj [("id", roleIdJson role.id),
    ("source", ← ContextSnapshot.closedTermJson role.source),
    ("typeFamily", ← ContextSnapshot.closedTermJson role.typeFamily),
    ("dependencies", toJson (role.dependencies.map roleIdJson))]

def rolesJson (roles : RoleTelescope) : StateM NativeExpression.Builder Json := do
  let context ← roles.context.mapM roleJson
  let arguments ← roles.arguments.mapM fun argument => do
    return Json.mkObj [("role", ← roleJson argument.role),
      ("wireIndex", toJson argument.wireIndex)]
  let results ← roles.results.mapM fun result => do
    return Json.mkObj [("role", ← roleJson result.role), ("layout", ← layoutJson result.layout),
      ("wirePath", toJson result.wirePath)]
  let captures ← roles.captures.mapM fun capture => do
    return Json.mkObj [("role", ← roleJson capture.role), ("layout", ← layoutJson capture.layout)]
  return Json.mkObj [("scope", roleScopeJson roles.scope), ("source", ← layoutJson roles.source),
    ("context", toJson context), ("arguments", toJson arguments),
    ("results", toJson results), ("captures", toJson captures)]

def environmentJson (environment : RuntimeEnvironment) : StateM NativeExpression.Builder Json := do
  let values ← environment.values.mapM fun value => value.mapM valueJson
  return Json.mkObj [("worker", toJson environment.worker),
    ("context", ← ContextSnapshot.contextJson environment.context),
    ("instances", ContextSnapshot.instancesJson environment.context), ("values", toJson values),
    ("sourceMarks", sourceMarksJson environment.sourceMarks)]

def actionJson (action : PreparedAction) : StateM NativeExpression.Builder Json := do
  match action with
  | .primitive boundary arguments =>
    return Json.mkObj [("kind", toJson "primitive"),
      ("boundary", ← boundaryJson boundary), ("universeArguments", toJson arguments)]
  | .project operand field =>
    return Json.mkObj [("kind", toJson "project"),
      ("operand", ← valueJson operand), ("field", ← fieldJson field)]
  | .apply callable arguments values =>
    return Json.mkObj [("kind", toJson "apply"), ("callable", ← valueJson callable),
      ("arguments", toJson (← arguments.mapM ContextSnapshot.closedTermJson)),
      ("values", ← valuesJson values)]

/-- Readability is prepared while the original native contexts may be opened.
Later observation reads only the strings returned here. -/
def readableTerm (term : ClosedTerm) : MetaM Json :=
  term.withOpen fun bindings expression => do
    let type := term.type.instantiateRev (bindings.map (·.expression))
    return Json.mkObj [("expression", toJson (← ppExpr expression).pretty),
      ("type", toJson (← ppExpr type).pretty)]

/-- Add the retained source address without reopening or rendering the term a second time. -/
def readableLayout (layout : SourceLayout) : MetaM Json := do
  let source ← readableTerm layout.source
  return source.setObjVal! "inputProjection"
    (toJson (layout.inputProjection.map readableInputProjectionJson))

def readableContext (context : ContextTelescope) : MetaM Json :=
  context.withOpen fun bindings => do
    let entries ← bindings.mapM fun binding => do
      let declaration ← getFVarLocalDecl binding.expression
      let value ← (declaration.value? true).mapM fun value => return (← ppExpr value).pretty
      return Json.mkObj [("id", ContextSnapshot.bindingJson binding.id),
        ("name", toJson (declaration.userName.toString (escape := false))),
        ("type", toJson (← ppExpr declaration.type).pretty), ("value", toJson value)]
    return toJson entries

def readableRole (role : ComputationalRole) (layout : Option SourceLayout := none) :
    MetaM Json := do
  let mut source ← readableTerm role.source
  if let some layout := layout then
    source := source.setObjVal! "inputProjection"
      (toJson (layout.inputProjection.map readableInputProjectionJson))
  return Json.mkObj [("id", roleIdJson role.id), ("source", source),
    ("typeFamily", ← readableTerm role.typeFamily)]

def readableApplication (application : ApplicationLayout) : MetaM Json := do
  let arguments ← application.arguments.mapM fun argument => do
    return Json.mkObj [("sourceIndex", toJson argument.sourceIndex),
      ("wireIndex", toJson argument.wireIndex),
      ("source", ← readableLayout argument.source),
      ("typeFamily", ← readableTerm argument.typeFamily)]
  return Json.mkObj [("arguments", toJson arguments),
    ("resultTypeFamily", ← readableTerm application.resultTypeFamily),
    ("resultTermFamily", ← readableTerm application.resultTermFamily),
    ("result", ← readableLayout application.result)]

end Observation

/-- Prepare the reached native request after its complete provenance has been fixed.
Reuse the exact native expression graph and closed-source serializer; no canonical quotient,
source reconstruction, provider call or completed payload copy enters the observation. -/
opaque ObservationDescriptor.prepare
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (scope : Array ValueBinding) (outputs : Array SourceLayout)
    (record : Option RecordLayout) (environment : RuntimeEnvironment) (origin : ValueOrigin)
    (application : Option ApplicationLayout) (roles : RoleTelescope)
    (actualArguments : Array RuntimeArgument := #[]) :
    MetaM ObservationDescriptor := do
  let actualArguments ← actualArguments.mapM fun argument => do
    let some declared := roles.arguments[argument.index]?
      | throwError "an observed actual argument is outside its prepared source telescope"
    let .ok marks := argument.sourceMarks declared.role.source
      | throwError "the source observation lost a retained occurrence mark"
    return Observation.actualArgumentJson argument marks
  let build : StateM NativeExpression.Builder (Json × Array Nat) := do
    let action ← Observation.actionJson action
    let sourceDocument ← Observation.layoutJson source
    let scope ← scope.mapM Observation.valueJson
    let outputs ← outputs.mapM Observation.layoutJson
    let record ← record.mapM Observation.recordJson
    let environment ← Observation.environmentJson environment
    let origin ← Observation.originJson origin
    let application ← application.mapM Observation.applicationJson
    let roles ← Observation.rolesJson roles
    let request := Json.mkObj [
      ("program", Observation.identityJson program),
      ("occurrence", Observation.identityJson occurrence),
      ("action", action), ("source", sourceDocument), ("scope", toJson scope),
      ("outputs", toJson outputs), ("record", toJson record), ("environment", environment),
      ("origin", origin), ("application", toJson application), ("roles", roles),
      ("actualArguments", toJson actualArguments)]
    let expression ← NativeExpression.Builder.add source.source.expression
    let type ← NativeExpression.Builder.add source.source.type
    return (request, #[expression, type])
  let ((request, roots), builder) := build.run {}
  let native := Json.mkObj [("request", request), ("nativeExpressions", builder.finish roots)]
  let context ← Observation.readableContext environment.context
  let arguments ← roles.arguments.mapM fun argument => Observation.readableRole argument.role
  let results ← roles.results.mapM fun result =>
    Observation.readableRole result.role (some result.layout)
  let captures ← roles.captures.mapM fun capture =>
    Observation.readableRole capture.role (some capture.layout)
  let sourceText ← Observation.readableLayout source
  let applicationText ← application.mapM Observation.readableApplication
  let readable := Json.mkObj [("source", sourceText),
    ("context", context), ("arguments", toJson arguments),
    ("results", toJson results), ("captures", toJson captures),
    ("application", toJson applicationText),
    ("sourceMarks", Observation.sourceMarksJson environment.sourceMarks),
    ("sourceDependencies", toJson (origin.sourceDependencies.map Observation.valueIdentityJson))]
  return ⟨native, readable, none, none⟩

/-- Updating a supplied source selection does not reopen or re-render the native descriptor. -/
opaque ObservationDescriptor.withSelection (descriptor : ObservationDescriptor)
    (selection : Option Name) : ObservationDescriptor :=
  { descriptor with selection := selection.map NativeExpression.nameJson }

/-- Attach the source document prepared by the authorized frontend handoff. -/
opaque ObservationDescriptor.withSourceSnapshot (descriptor : ObservationDescriptor)
    (sourceSnapshot : Option Json) : ObservationDescriptor :=
  { descriptor with sourceSnapshot }

def ObservationDescriptor.toJson (descriptor : ObservationDescriptor) : Json :=
  Json.mkObj [("native", descriptor.native), ("readable", descriptor.readable),
    ("selection", Lean.toJson descriptor.selection),
    ("sourceSnapshot", Lean.toJson descriptor.sourceSnapshot)]

end CasRuntime
