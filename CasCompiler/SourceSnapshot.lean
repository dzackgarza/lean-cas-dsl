module

public import CasCompiler.Elaborate
public import CasCompiler.ContextSnapshot
import all CasCompiler.ContextSnapshot
import all CasTools.NativeExpression
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SelectionData
import all CasCompiler.SelectionData
public import CasTools.InterfaceDocument

@[expose] public section

namespace CasCompiler.SourceSnapshot

open Lean CasTools CasCatalogue ContextSnapshot

local instance : ToJson Name := ⟨NativeExpression.nameJson⟩
local instance : ToJson BindingId := ⟨bindingJson⟩
local instance : ToJson Expr := ⟨fun expression => NativeExpression.encode #[expression]⟩

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

private abbrev ClosedSelection := SourceSelection ClosedTerm
private abbrev ClosedSelections := SourceSelectionScope ClosedTerm

private def selectionJsonWith (encodeTerm : ClosedTerm → StateM NativeExpression.Builder Json)
    (selection : SourceSelection ClosedTerm) : StateM NativeExpression.Builder Json := do
  return toJson (← selection.mapM encodeTerm)

private def selectionJsonReference (selection : SourceSelection ClosedTerm) :
    StateM NativeExpression.Builder Json :=
  selectionJsonWith closedTermJsonReference selection

private unsafe def selectionJsonCached (selection : SourceSelection ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  letI : TypeName ClosedSelection := TypeName.mk ClosedSelection ``ClosedSelection
  NativeExpression.Builder.memoSnapshot ``selectionJsonReference selection (selectionJsonWith closedTermJson selection)

@[implemented_by selectionJsonCached]
opaque selectionJson (selection : SourceSelection ClosedTerm) : StateM NativeExpression.Builder Json :=
  selectionJsonReference selection

private def selectionsJsonWith
    (encodeSelection : SourceSelection ClosedTerm → StateM NativeExpression.Builder Json)
    (selections : SourceSelectionScope ClosedTerm) : StateM NativeExpression.Builder Json := do
  let entries := selections.toArray.qsort fun left right =>
    if left.1.session == right.1.session then left.1.serial < right.1.serial
    else left.1.session < right.1.session
  let rows ← entries.mapM fun (binding, selection) => do
    return Json.mkObj [("binding", bindingJson binding),
      ("selection", ← encodeSelection selection)]
  return Json.arr rows

private def selectionsJsonReference (selections : SourceSelectionScope ClosedTerm) :
    StateM NativeExpression.Builder Json :=
  selectionsJsonWith selectionJsonReference selections

private unsafe def selectionsJsonCached (selections : SourceSelectionScope ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  letI : TypeName ClosedSelections := TypeName.mk ClosedSelections ``ClosedSelections
  NativeExpression.Builder.memoSnapshot ``selectionsJsonReference selections (selectionsJsonWith selectionJson selections)

@[implemented_by selectionsJsonCached]
opaque selectionsJson (selections : SourceSelectionScope ClosedTerm) : StateM NativeExpression.Builder Json :=
  selectionsJsonReference selections

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

def limitInterfaceJson (interface : LimitInterface ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  let presentation ← closedTermJson interface.presentation
  let diagram ← closedTermJson interface.diagram
  let standardization ← interface.standardization.mapM closedTermJson
  let dataConstructor ← interface.dataConstructor.mapM closedTermJson
  return Json.mkObj [("presentation", presentation), ("diagram", diagram),
    ("standardization", toJson standardization), ("dataConstructor", toJson dataConstructor)]

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
