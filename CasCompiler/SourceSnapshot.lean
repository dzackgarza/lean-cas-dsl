module

public import CasCompiler.Elaborate
public import CasCompiler.ContextSnapshot
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SelectionData
import all CasCompiler.SelectionData
public import CasTools.InterfaceDocument

@[expose] public section

namespace CasCompiler.SourceSnapshot

open Lean CasTools CasCatalogue ContextSnapshot

-- Registry rows reuse InterfaceDocument's codecs, derived from the actual independent
-- records. A rigid family's native expressions are complete closed functions; their
-- nested graphs retain every binder and universe without reopening or interpreting them.
local instance : ToJson Name := ⟨NativeExpression.nameJson⟩
local instance : ToJson BindingId := ⟨bindingJson⟩
local instance : ToJson Expr := ⟨fun expression => NativeExpression.encode #[expression]⟩
-- A prerequisite ordinal retains the bound supplied by its original whole program.
-- The finite type's proof is determined by that checked value and bound.
local instance {bound : Nat} : ToJson (Fin bound) :=
  ⟨fun index => Json.mkObj [("value", toJson index.val), ("bound", toJson bound)]⟩

deriving instance ToJson for Sum

deriving instance ToJson for StructuralEdge, Route
deriving instance ToJson for ComputationRef, ComputationDerivationId, ComputationDerivationEntry
deriving instance ToJson for CheckedComputationPrerequisite, CheckedComputationDerivation
deriving instance ToJson for SourceNamedEntry, SelectedConstructorInterface, SelectedSourceReference
deriving instance ToJson for SourceCategoryRole, NativePowerObject
deriving instance ToJson for LimitInterface, LimitCreationInterface
deriving instance ToJson for NativeSourceCarrierSelection, NativeSourceLimitSelection
deriving instance ToJson for NativeSourceCategory, NativeSourceElementOwner, NativeSourceTypeOrigin
deriving instance ToJson for NativeSourcePointOrigin, NativeRouteFunctor, NativeSourceCell
deriving instance ToJson for NativeSourceCellComponent, NativeSourceCartesian
deriving instance ToJson for LiftPort, LiftFamily, PresentationFamily
deriving instance ToJson for SourceActionFamily
deriving instance ToJson for RoutedMethodReturn, RoutedMethodFamily, PropertyFamily
deriving instance ToJson for PointFamilyOwner, PointFamily, NativePointRequest
deriving instance ToJson for CategoricalPointOwner, CategoricalPointFamily, CategoricalPointRequest
deriving instance ToJson for LimitFamily, LimitUniversalFamily, CreationFamily
deriving instance ToJson for NativeLimitSelection, SelectedLimitOwner, NativeLimitLegSelection
deriving instance ToJson for SourceProgram, SourceFamily
deriving instance ToJson for SelectedApplicationFamily, SelectedSourceApplication
deriving instance ToJson for SelectedSourceAdmission, SelectedSourcePointRequest, SelectedSourceField
deriving instance ToJson for SelectedEndpointSide, SelectedSourceEndpoint, SourceSelection

/-- Every native payload is encoded in its retained complete telescope. The derived record
codec also retains all original registry rows, whole rigid families, formal slots and routes;
it cannot silently omit a field when the typed selection owner grows. -/
def selectionJson (selection : SourceSelection ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  return toJson (← selection.mapM closedTermJson)

/-- Stable binding identities order the complete source side table. No expression, type,
carrier or available implementation is consulted to reconstruct a selection. -/
def selectionsJson (selections : SourceSelectionScope ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  let entries := selections.toArray.qsort fun left right =>
    if left.1.session == right.1.session then left.1.serial < right.1.serial
    else left.1.session < right.1.session
  let rows ← entries.mapM fun (binding, selection) => do
    return Json.mkObj [("binding", bindingJson binding),
      ("selection", ← selectionJson selection)]
  return Json.arr rows

/-- Original source positions; no reconstructed or pretty-printed source is substituted. -/
def spanJson (span : SourceSpan) : Json :=
  Json.mkObj [("file", toJson span.fileName),
    ("startByte", toJson (span.start.map (·.byteIdx))),
    ("stopByte", toJson (span.stop.map (·.byteIdx)))]

def ringVariablesJson (rings : Array SourceRingVariable) :
    StateM NativeExpression.Builder Json := do
  let rows ← rings.mapM fun ring => do
    let carrier ← closedTermJson ring.carrier
    return Json.mkObj [("name", toJson (ring.name.toString (escape := false))),
      ("nativeName", NativeExpression.nameJson ring.name),
      ("carrier", carrier), ("index", toJson ring.index),
      ("selections", ← selectionsJson ring.selections)]
  return toJson rows

def carrierJson (carrier : SourceCarrierSelection) : StateM NativeExpression.Builder Json := do
  let actions ← carrier.actions.mapM closedTermJson
  let comparisons ← carrier.comparisons.mapM closedTermJson
  return Json.mkObj [("refs", toJson (reprStr carrier.refs)),
    ("target", toJson (reprStr carrier.target)),
    ("identifications", Json.arr (carrier.identifications.map NativeExpression.nameJson)),
    ("actions", toJson actions), ("comparisons", toJson comparisons)]

/-- The accepted interface is retained as supplied, including its dependent constructor and
optional standardization. It is not reconstructed from the selected apex or cone. -/
def limitInterfaceJson (interface : LimitInterface ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  let presentation ← closedTermJson interface.presentation
  let diagram ← closedTermJson interface.diagram
  let standardization ← interface.standardization.mapM closedTermJson
  let dataConstructor ← interface.dataConstructor.mapM closedTermJson
  return Json.mkObj [("presentation", presentation), ("diagram", diagram),
    ("standardization", toJson standardization), ("dataConstructor", toJson dataConstructor)]

/-- Exact native creation inputs and full fixed result family, in the original source context. -/
def creationJson (creation : LimitCreationInterface ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  return Json.mkObj [
    ("lift", toJson creation.lift.raw),
    ("declaration", NativeExpression.nameJson creation.declaration),
    ("edge", toJson creation.edge),
    ("evidence", ← closedTermJson creation.evidence),
    ("createsLimit", ← closedTermJson creation.createsLimit),
    ("functor", ← closedTermJson creation.functor),
    ("diagram", ← closedTermJson creation.diagram),
    ("targetCone", ← closedTermJson creation.targetCone),
    ("targetUniversal", ← closedTermJson creation.targetUniversal),
    ("standardization", ← closedTermJson creation.standardization),
    ("standardizedCone", ← closedTermJson creation.standardizedCone),
    ("standardizedUniversal", ← closedTermJson creation.standardizedUniversal),
    ("requestFamily", ← closedTermJson creation.requestFamily),
    ("result", ← closedTermJson creation.result)]

/-- Source and target presentations stay distinct for a created limit. All fields are the
already checked retained data; serializing them neither elaborates nor executes mathematics. -/
def limitJson (limit : SourceLimitSelection) : StateM NativeExpression.Builder Json := do
  let cone ← closedTermJson limit.cone
  let presentation ← closedTermJson limit.presentation
  let diagram ← closedTermJson limit.diagram
  let interface ← limitInterfaceJson limit.interface
  let ownerFamily ← limit.ownerFamily.mapM closedTermJson
  let creation ← limit.creation.mapM creationJson
  let creationFamily ← limit.creationFamily.mapM closedTermJson
  return Json.mkObj [("row", toJson limit.row),
    ("construction", NativeExpression.nameJson limit.construction),
    ("declaration", NativeExpression.nameJson limit.declaration),
    ("displayDeclaration", toJson (limit.declaration.toString (escape := false))),
    ("nativeDeclaration", NativeExpression.nameJson limit.declaration),
    ("colimit", toJson limit.colimit), ("cone", cone),
    ("presentation", presentation), ("diagram", diagram), ("interface", interface),
    ("ownerFamily", toJson ownerFamily), ("creation", toJson creation),
    ("creationFamily", toJson creationFamily), ("creationInputs", toJson limit.creationInputs),
    ("category", toJson (reprStr limit.category)), ("bundle", ← closedTermJson limit.bundle)]

def categoryJson (category : SourceCategoryBinding) : StateM NativeExpression.Builder Json := do
  let bundle ← closedTermJson category.bundle
  let carrier ← category.carrier.mapM carrierJson
  let limit ← category.limit.mapM limitJson
  let fields := [("role", toJson <| match category.role with
      | .object => "object" | .morphism => "morphism"),
    ("expression", toJson (reprStr category.expression)),
    ("bundle", bundle), ("carrier", toJson carrier)]
  return Json.mkObj (fields ++ limit.toList.map ("limit", ·))

def bindingSpan (session : SourceContextObservation) (id : BindingId) : Option Json := do
  let index ← session.context.entries.findIdx? (·.id == id)
  spanJson <$> session.spans[index]?

/-- Prepare an inert exact source document at the existing source handoff.
Categories and declaration spans are aligned with the retained context by stable identity.
This pure encoder does not reopen terms, infer types, print expressions, select providers or
read a mutable environment. Callers retain its result for later observation. -/
def snapshot (session : SourceContextObservation) (term : SourceTerm)
    (definedBinding : Option ContextEntry := none) : Json := Id.run do
  let build : StateM NativeExpression.Builder (List (String × Json) × Array Nat) := do
    let native ← closedTermJson term.source
    let context ← contextJson term.source.context
    let expression ← NativeExpression.Builder.add term.source.expression
    let type ← NativeExpression.Builder.add term.source.type
    let categories ← term.source.context.entries.mapM fun entry =>
      (session.categoryFor entry.id).mapM categoryJson
    let rings ← term.source.context.entries.mapM fun entry => do
      let rings ← ringVariablesJson (session.ringsFor entry.id)
      return Json.mkObj [("id", bindingJson entry.id), ("variables", rings)]
    let resultBinding ← definedBinding.mapM fun entry => do
      let category ← (session.categoryFor entry.id).mapM categoryJson
      let rings ← ringVariablesJson (session.ringsFor entry.id)
      return Json.mkObj [("id", bindingJson entry.id),
        ("name", toJson (entry.userName.toString (escape := false))),
        ("nativeName", NativeExpression.nameJson entry.userName),
        ("span", toJson (bindingSpan session entry.id)),
        ("category", toJson category), ("ringVariables", rings)]
    let category ← term.category.mapM categoryJson
    let selections ← selectionsJson term.selections
    let sessionSelections ← selectionsJson session.selections
    pure ([("native", native), ("context", context),
      ("instances", instancesJson term.source.context),
      ("categories", toJson categories), ("category", toJson category),
      ("ringVariables", toJson rings),
      ("selections", selections), ("sessionSelections", sessionSelections),
      ("resultBinding", toJson resultBinding),
      ("file", toJson term.span.fileName),
      ("startByte", toJson (term.span.start.map (·.byteIdx))),
      ("stopByte", toJson (term.span.stop.map (·.byteIdx))),
      ("bindingSpans", toJson <| term.source.context.entries.map fun entry => Json.mkObj [
        ("id", bindingJson entry.id), ("span", toJson (bindingSpan session entry.id))])],
      #[expression, type])
  let ((fields, roots), builder) := build.run {}
  return Json.mkObj (fields ++ [("nativeExpressions", builder.finish roots)])

end CasCompiler.SourceSnapshot
