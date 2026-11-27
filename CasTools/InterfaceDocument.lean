module

public import LeanCategories.Catalogue.Registry.Snapshot
public import CasCompiler.SourceTypeOrigin
public import CasTools.NativeExpression
public meta import CasTools.NativeExpression
public import CasContract.Registration
public import CasContract.Port
public import Mathlib.CategoryTheory.Limits.Creates
public import Lean.Elab.Command

@[expose] public section

namespace CasTools.InterfaceExport

open Lean Meta Elab Command CasCatalogue CasCompiler




local instance : ToJson Name := ⟨NativeExpression.nameJson⟩
deriving instance ToJson for ParameterMorphismId, ParameterKindId, VarianceId
deriving instance ToJson for FibrationId, MethodId, PropertyId, LiftId, LimitId
deriving instance ToJson for AdjunctionId, ObjectId, LiteralId, PowerObjectId
deriving instance ToJson for InclusionId, OperationId, MorphismId
deriving instance ToJson for NaturalTransformationId, PortId, OpaquePortId
deriving instance ToJson for BinderId, ConstructionId
deriving instance ToJson for CategoryFamilySchema, CategoryFamilyTransportSemantics
deriving instance ToJson for FibrationVariance, MethodShape, LiftKind
deriving instance ToJson for InclusionParameterization, ConstructorArgKind



instance {source target : CategoryExpr} : ToJson (FunctorExpr source target) :=
  ⟨fun expression => NativeExpression.encode #[toExpr expression]⟩

deriving instance ToJson for FibrationEntry, MethodEntry, LiftEntry, LimitEntry
deriving instance ToJson for AdjunctionEntry, ObjectRefinement, ObjectFunctorPresentation
deriving instance ToJson for ObjectComponents, ObjectEntry, LiteralEntry, NumeralEntry
deriving instance ToJson for GraphLiteralEntry, SubsetLiteralEntry, BinderEntry
deriving instance ToJson for InclusionEntry, OperationRefinement, OperationEntry
deriving instance ToJson for PowerObjectEntry, MorphismEntry, CellEntry, PropertyEntry
deriving instance ToJson for ConstructorEntry, NamedCategoryEntry, CategoryFamilyEntry
deriving instance ToJson for ClassifierEntry, FunctorEntry, PresentationComparisonEntry
deriving instance ToJson for ConstructionEntry, StructuralPortEntry, OpaqueCategoryEntry
deriving instance ToJson for SemanticEntry



def rowDeclarations (row : SemanticEntry) : Array Name :=
  row.declarations ++ match row with
    | .object object => object.generator.toArray ++ object.application.toArray ++
      object.constants.toArray ++ object.inclusion.toArray ++ object.admission.toArray ++
      object.refines.toArray.map (·.identification)
    | _ => #[]




def dataInterfaces : Array Name :=
  #[``BackendProgram, ``PreferredRoute, ``Registration, ``Manifest,
    ``Backend.ObjectField, ``Backend.MorphismEndpoint, ``Backend.TypedMap,
    ``Backend.LiftImages, ``Backend.LiftInput, ``Backend.LiftFactorInput,
    ``Backend.CartesianMap, ``Backend.ConstructionField,
    ``CategoryTheory.LiftableCone, ``CategoryTheory.LiftsToLimit,
    ``Backend.CategoryParameter,
    ``Backend.ConstructedCategory, ``Backend.StructuredProjectionAction,
    ``Backend.FunctorParameter, ``Backend.CellComponent, ``Backend.ConstructedCellComponent,
    ``Backend.CoreObject, ``Backend.CoreIso, ``Backend.ConstructionInvocation,
    ``Backend.AdmittedPoint, ``Backend.ConstrainedPoint, ``Backend.PointInvocation,
    ``Backend.PresentationInvocation, ``Backend.ComputationalValue,
    ``Backend.InputPathStep, ``Backend.DeferredCall, ``Backend.DeferredData,
    ``Backend.PortError, ``Backend.Ready, ``Backend.ReadyV2]

def uniqueNames (names : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut result := #[]
  for name in names do
    unless seen.contains name do
      seen := seen.insert name
      result := result.push name
  return result



def declarationMembers (name : Name) : MetaM (Array Name) := do
  let env ← getEnv
  match ← getConstInfo name with
  | .inductInfo info =>
    let labels := (getStructureInfo? env name).map (·.fieldNames) |>.getD #[]
    let fields ← labels.mapM fun label => do
      let some projection := getProjFnForField? env name label
        | throwError "public structure {name} has no native projection for {label}"
      return projection
    return #[name] ++ info.ctors.toArray ++ fields
  | _ => return #[name]

def declarationDocument (info : ConstantInfo) : MetaM Json := do
  let env ← getEnv
  let fields ← match getStructureInfo? env info.name with
    | none => pure #[]
    | some structureInfo => structureInfo.fieldNames.mapM fun label => do
      let some name := getProjFnForField? env info.name label
        | throwError "public structure {info.name} has no native projection for {label}"
      let field ← getConstInfo name
      return Json.mkObj [("label", toJson label.toString),
        ("name", NativeExpression.nameJson name),
        ("signature", toJson (← ppExpr field.type).pretty),
        ("documentation", toJson (← findDocString? env name))]
  return Json.mkObj [("name", NativeExpression.nameJson info.name),
    ("displayName", toJson (info.name.toString (escape := false))),
    ("universeParameters", Json.arr (info.levelParams.toArray.map NativeExpression.nameJson)),
    ("signature", toJson (← ppExpr info.type).pretty),
    ("documentation", toJson (← findDocString? env info.name)),
    ("fields", Json.arr fields)]




def prepare : MetaM Json := do
  let snapshot ← RegistrySnapshot.snapshot
  match snapshot.validateDerived #[] with
  | .error message => throwError "invalid public registry snapshot: {message}"
  | .ok () => pure ()
  let entries := snapshot.entries.qsort (fun a b => a.stableId < b.stableId)
  let names := uniqueNames (entries.flatMap rowDeclarations ++ dataInterfaces)
  let names := uniqueNames ((← names.mapM declarationMembers).flatten)
  let declarations ← names.mapM getConstInfo
  let documents ← withOptions (fun options =>
      options.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
    declarations.mapM declarationDocument
  let origins := semanticRowsByModule (← getEnv)
  let mut rows := #[]
  let mut identities : Std.HashSet (String × String) := {}
  for row in entries do
    let entry := toJson row
    let .ok variants := entry.getObj?
      | throwError "public row {row.stableId} lost its native constructor"
    let [(kind, _)] := variants.toList
      | throwError "public row {row.stableId} has no unique native constructor"
    let identity := (kind, row.stableId)
    if identities.contains identity then
      throwError "public registry repeats the typed identity {kind}:{row.stableId}"
    identities := identities.insert identity
    let modules := origins.filterMap fun (name, rows) =>
      if rows.any (fun other => if other.stableId == row.stableId then
          (toJson other).compress == entry.compress else false) then some name else none
    unless modules.size == 1 do
      throwError "public row {row.stableId} has no unique registered module"
    rows := rows.push <| Json.mkObj [
      ("id", toJson row.stableId), ("kind", toJson kind), ("entry", entry),
      ("module", NativeExpression.nameJson modules[0]!),
      ("declarations", Json.arr ((rowDeclarations row).map NativeExpression.nameJson))]
  return Json.mkObj [("schema", toJson "cas-language-interface/1"),
    ("leanVersion", toJson Lean.versionString), ("registry", Json.arr rows),
    ("dataInterfaces", Json.arr (dataInterfaces.map NativeExpression.nameJson)),
    ("declarations", Json.arr documents),
    ("native", NativeExpression.encodeWithDeclarations #[] declarations)]



def help (document : Json) : Except String String := do
  let rows ← document.getObjValAs? (Array Json) "registry"
  let declarations ← document.getObjValAs? (Array Json) "declarations"
  let mut result := "# Selected language and interfaces\n\n" ++
    "Generated from the checked registry and native declarations in this export. " ++
    "The adjacent JSON retains every registered field and the complete native expression graph.\n\n" ++
    "Use committed inspection to obtain the selected instance, remaining parameters, " ++
    "candidate routes and availability. A registered signature does not assert that a " ++
    "computation is installed or that returned data satisfy its mathematical laws.\n\n" ++
    "The data-only wire protocol and preferred-route registration rules are documented in " ++
    "[kernel-service.md](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/main/api/kernel-service.md) " ++
    "and [manifest.md](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/main/api/manifest.md).\n\n" ++
    "## Registered language\n\n" ++
    "| Surface | Kind | Stable identifier |\n| --- | --- | --- |\n"
  for row in rows do
    let id ← row.getObjValAs? String "id"
    let variants ← (← row.getObjVal? "entry").getObj?
    let [(kind, fields)] := variants.toList
      | throw "a public registry row must retain one native constructor"
    let arguments ← fields.getObj?
    let [(_, payload)] := arguments.toList
      | throw "a public registry constructor must retain its complete row record"
    let surface := (payload.getObjValAs? String "name").toOption.filter (! ·.isEmpty)
      |>.orElse (fun _ => (payload.getObjValAs? String "token").toOption)
      |>.getD ""
    result := result ++ "| " ++ surface.replace "|" "\\|" ++ " | " ++ kind ++
      " | `" ++ id ++ "` |\n"
  result := result ++ "\n"
  for row in rows do
    let id ← row.getObjValAs? String "id"
    let entry ← row.getObjVal? "entry"
    result := result ++ "### " ++ id ++ "\n\n```json\n" ++ entry.pretty ++ "\n```\n\n"
  result := result ++ "## Native interfaces, laws and choices\n\n"
  for declaration in declarations do
    let name ← declaration.getObjValAs? String "displayName"
    let signature ← declaration.getObjValAs? String "signature"
    let documentation ← declaration.getObjValAs? (Option String) "documentation"
    result := result ++ "### " ++ name ++ "\n\n```lean\n" ++ signature ++ "\n```\n\n"
    if let some text := documentation then result := result ++ text ++ "\n\n"
  return result

end CasTools.InterfaceExport
