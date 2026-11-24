module

public import CasCompiler.Elaborate
public import CasCompiler.ContextSnapshot

@[expose] public section

namespace CasCompiler.SourceSnapshot

open Lean CasTools ContextSnapshot

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
      ("carrier", carrier), ("index", toJson ring.index)]
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

/-- Source and target presentations stay distinct for a created limit. All fields are the
already checked retained data; serializing them neither elaborates nor executes mathematics. -/
def limitJson (limit : SourceLimitSelection) : StateM NativeExpression.Builder Json := do
  let cone ← closedTermJson limit.cone
  let presentation ← closedTermJson limit.presentation
  let diagram ← closedTermJson limit.diagram
  let interface ← limitInterfaceJson limit.interface
  return Json.mkObj [("row", toJson limit.row),
    ("declaration", NativeExpression.nameJson limit.declaration),
    ("displayDeclaration", toJson (limit.declaration.toString (escape := false))),
    ("nativeDeclaration", NativeExpression.nameJson limit.declaration),
    ("colimit", toJson limit.colimit), ("cone", cone),
    ("presentation", presentation), ("diagram", diagram), ("interface", interface),
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
    pure ([("native", native), ("context", context),
      ("instances", instancesJson term.source.context),
      ("categories", toJson categories), ("category", toJson category),
      ("ringVariables", toJson rings),
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
