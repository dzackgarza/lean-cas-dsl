module

public import CasCompiler.Parse
public import CasCompiler.Read
public import CasCatalogue.QuestionIdentity
public import CasTools.NativeExpression
public import Lean.Elab.Command

@[expose] public section

namespace CasTools.QuestionExport

open Lean Meta Elab Term Command CasCompiler CasCatalogue.Language

structure Location where
  id : String
  file : String
  sourceLine : Nat
  source : String
  deriving Inhabited, ToJson

structure Reading where
  id : String
  file : String
  sourceLine : Nat
  source : String
  provenance : String
  /-- The canonical typed reading in the fixed mathematical source environment. -/
  question : String
  /-- NativeExpression graph document for the exact whole closed proposition. -/
  proposition : String
  prettyProposition : String
  /-- Complete native source terms, binding identities, selections and original spans.
  Expression indices refer to this snapshot's `nativeExpressions` node table. -/
  sourceContext : Json
  deriving Inhabited, ToJson

structure Failure where
  id : String
  file : String
  sourceLine : Nat
  source : String
  stage : String
  kind : String
  detail : String
  cause : Option Location
  deriving Inhabited, ToJson

structure Observation where
  readings : Array Reading := #[]
  failures : Array Failure := #[]

private def bindingJson (id : BindingId) : Json :=
  Json.mkObj [("session", toJson id.session), ("serial", toJson id.serial)]

private def contextJson (context : ContextTelescope) : StateM NativeExpression.Builder Json := do
  let entries ← context.entries.mapM fun entry => do
    let type ← NativeExpression.Builder.add entry.type
    let value ← entry.value.mapM NativeExpression.Builder.add
    return Json.mkObj [
      ("id", bindingJson entry.id), ("name", toJson (entry.userName.toString (escape := false))),
      ("nativeName", NativeExpression.nameJson entry.userName),
      ("role", toJson <| match entry.role with
        | .parameter => "parameter" | .definition => "definition" | .hypothesis => "hypothesis"
        | .instance => "instance" | .selectedStructure => "selectedStructure" | .result => "result"),
      ("binderInfo", toJson (reprStr entry.binderInfo)),
      ("nativeBinderInfo", toJson entry.binderInfo),
      ("kind", toJson (reprStr entry.kind)), ("type", toJson type),
      ("value", toJson value), ("nondep", toJson entry.nondep)]
  return toJson entries

-- NativeExpression retains every constructor and metadata value in a shared node table.
-- The ordered closed telescope supplies each de Bruijn scope.
private def closedTermJson (term : ClosedTerm) : StateM NativeExpression.Builder Json := do
  let context ← contextJson term.context
  let expression ← NativeExpression.Builder.add term.expression
  let type ← NativeExpression.Builder.add term.type
  return Json.mkObj [
    ("context", context),
    ("instances", toJson <| term.context.instances.map fun selected => Json.mkObj [
      ("class", toJson (selected.className.toString (escape := false))),
      ("nativeClass", NativeExpression.nameJson selected.className),
      ("binding", bindingJson selected.binding)]),
    ("universeParams", Json.arr (term.universeParams.map NativeExpression.nameJson)),
    ("expression", toJson expression), ("type", toJson type)]

private def carrierJson (carrier : SourceCarrierSelection) : StateM NativeExpression.Builder Json := do
  let actions ← carrier.actions.mapM closedTermJson
  let comparisons ← carrier.comparisons.mapM closedTermJson
  return Json.mkObj [("refs", toJson (reprStr carrier.refs)),
    ("target", toJson (reprStr carrier.target)),
    ("identifications", Json.arr (carrier.identifications.map NativeExpression.nameJson)),
    ("actions", toJson actions), ("comparisons", toJson comparisons)]

private def categoryJson (category : SourceCategoryBinding) : StateM NativeExpression.Builder Json := do
  let bundle ← closedTermJson category.bundle
  let carrier ← category.carrier.mapM carrierJson
  return Json.mkObj [("role", toJson <| match category.role with
      | .object => "object" | .morphism => "morphism"),
    ("expression", toJson (reprStr category.expression)),
    ("bundle", bundle), ("carrier", toJson carrier)]

private def snapshot (session : SourceSession) (term : SourceTerm) : Json := Id.run do
  let build : StateM NativeExpression.Builder (List (String × Json) × Array Nat) := do
    let native ← closedTermJson term.source
    let context ← contextJson term.source.context
    let categories ← term.source.context.entries.mapM fun entry =>
      (session.categoryFor entry.id).mapM categoryJson
    let category ← term.category.mapM categoryJson
    let expression ← NativeExpression.Builder.add term.source.expression
    let type ← NativeExpression.Builder.add term.source.type
    pure ([("native", native), ("context", context),
      ("instances", toJson <| term.source.context.instances.map fun selected => Json.mkObj [
        ("class", toJson (selected.className.toString (escape := false))),
        ("nativeClass", NativeExpression.nameJson selected.className),
        ("binding", bindingJson selected.binding)]),
      ("categories", toJson categories), ("category", toJson category),
      ("file", toJson term.span.fileName),
      ("startByte", toJson (term.span.start.map (·.byteIdx))),
      ("stopByte", toJson (term.span.stop.map (·.byteIdx)))], #[expression, type])
  let ((fields, roots), builder) := build.run {}
  return Json.mkObj (fields ++ [("nativeExpressions", builder.finish roots)])

private def location (file : SourceFile) (id : String) (stx : Syntax) : TermElabM Location := do
  let some start := stx.getPos? | throwError "an original source item has no start position"
  let some stop := stx.getTailPos? | throwError "an original source item has no end position"
  return ⟨id, file.context.fileName, (file.context.fileMap.toPosition start).line,
    ({ str := file.context.inputString, startPos := start, stopPos := stop } :
      Substring.Raw).toString⟩

private def bindingName? (stx : TSyntax `cas_stmt) : Option Ident :=
  match stx with
  | `(cas_stmt| let $name:ident := $_:cas_term)
  | `(cas_stmt| let $name:ident : $_:cas_term := $_:cas_term)
  | `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term)
  | `(cas_stmt| let $name:ident($_:ident, $_:ident,*) := $_:cas_term) => some name
  | _ => none

private def failure (where_ : Location) (stage : String) (error : Exception) :
    TermElabM Failure := do
  let kind := if CasCatalogue.Exception.isSemanticAmbiguity error then "ambiguous"
    else if CasCatalogue.Exception.isUnsupportedSource error then "unsupported"
    else if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then "interrupted"
    else match error with | .internal .. => "internal" | .error .. => "invalid"
  return ⟨where_.id, where_.file, where_.sourceLine, where_.source, stage, kind,
    ← error.toMessageData.toString, none⟩

private def blocked (where_ : Location) (stage : String) (cause : Failure) : Failure :=
  ⟨where_.id, where_.file, where_.sourceLine, where_.source, stage, cause.kind, cause.detail,
    some ⟨cause.id, cause.file, cause.sourceLine, cause.source⟩⟩

private def unread (where_ : Location) (provenance : String) : Reading :=
  ⟨where_.id, where_.file, where_.sourceLine, where_.source, provenance, "", "", "", Json.null⟩

private def canonicalCategory (table : CasCatalogue.Realize.TermTable)
    (category : SourceCategoryBinding) : TermElabM Json := do
  let bundle ← category.bundle.withOpen fun bindings value =>
    mkLambdaFVars (bindings.map (·.expression)) value
      (usedLetOnly := false) (generalizeNondepLet := false)
  let carrier ← category.carrier.mapM fun carrier => do
    let encode := fun (term : ClosedTerm) => do
      let value ← term.withOpen fun bindings value =>
        mkLambdaFVars (bindings.map (·.expression)) value
          (usedLetOnly := false) (generalizeNondepLet := false)
      table.encode value
    let actions ← carrier.actions.mapM encode
    let comparisons ← carrier.comparisons.mapM encode
    return Json.mkObj [("refs", toJson (reprStr carrier.refs)),
      ("target", toJson (reprStr carrier.target)),
      ("identifications", toJson (carrier.identifications.map (·.toString (escape := false)))),
      ("actions", toJson actions), ("comparisons", toJson comparisons)]
  return Json.mkObj [("role", toJson <| match category.role with
      | .object => "object" | .morphism => "morphism"),
    ("expression", toJson (reprStr category.expression)),
    ("bundle", toJson (← table.encode bundle)),
    ("carrier", toJson carrier)]

private def reading (session : SourceSession) (where_ : Location) (provenance : String)
    (term : SourceTerm) : TermElabM Reading := do
  let proposition ← term.source.withOpen fun bindings expression => do
    unless ← isProp expression do throwError "an exported question must be a proposition"
    -- Retain unused parameters, hypotheses and lets; do not generalize a let into a parameter.
    -- Reuse: Lean.Meta.mkForallFVars at v4.33.0, with its explicit retention controls.
    mkForallFVars (bindings.map (·.expression)) expression
      (usedLetOnly := false) (generalizeNondepLet := false)
  -- Reuse the existing typed canonical serializer. It erases only native metadata,
  -- binder spelling and proofs of the same proposition; the unquotiented snapshot stays below.
  -- Source: CasCatalogue/QuestionIdentity.lean, QuestionIdentity.encode and TermTable.
  let table ← CasCatalogue.Realize.TermTable.new
  let root ← table.encode proposition
  let categories ← term.source.context.entries.mapM fun entry =>
    (session.categoryFor entry.id).mapM (canonicalCategory table)
  let category ← term.category.mapM (canonicalCategory table)
  let instances ← term.source.context.instances.mapM fun selected => do
    let some index := term.source.context.entries.findIdx? (·.id == selected.binding)
      | throwError "an exported instance is outside its actual source telescope"
    return Json.mkObj [("class", toJson (selected.className.toString (escape := false))),
      ("binding", toJson index)]
  let question ← table.finish <| Json.mkObj [("proposition", toJson root),
    ("roles", toJson (term.source.context.entries.map (reprStr ·.role))),
    ("instances", toJson instances), ("categories", toJson categories),
    ("category", toJson category)]
  return ⟨where_.id, where_.file, where_.sourceLine, where_.source, provenance,
    question, (NativeExpression.encode #[proposition]).compress,
    (← ppExpr proposition).pretty, snapshot session term⟩

/-- Observe each original item through the native source session. A failed definition blocks
the remaining file scope; a failed question leaves the preceding scope available. Native
saved-state restoration discards failed elaboration state without replaying source bindings.
Source: T029 complete-reading boundary and Lean.Elab.Term.saveState/restore. -/
opaque observeFile (file : SourceFile) (initial : SourceSession) : TermElabM Observation :=
  file.withContext do
    let mut session := initial
    let mut observation : Observation := {}
    let mut rootFailure : Option Failure := none
    for item in file.items do
      let (identity, provenance, statement) ← match item with
        | `(cas_item| test $id:ident $label:str : $statement:cas_stmt) =>
          pure (some (id.getId.toString (escape := false)), label.getString, statement)
        | `(cas_item| $statement:cas_stmt) => pure (none, "", statement)
        | _ => throwError "an original source item changed its syntax category"
      let name := bindingName? statement
      if identity.isSome && name.isSome then
        throwError "a labeled export item must be a question"
      if identity.isNone && name.isNone then
        throwError "question export requires each assertion's original identity"
      let id ← match identity, name with
        | some id, _ => pure id
        | none, some name => pure (name.getId.toString (escape := false))
        | none, none => throwError "the source item has no question or binding identity"
      let where_ ← location file id item
      let stage := if name.isSome then "binding" else "interpretation"
      if let some cause := rootFailure then
        observation := { observation with
          failures := observation.failures.push (blocked where_ stage cause) }
        if identity.isSome then
          observation := { observation with
            readings := observation.readings.push (unread where_ provenance) }
        continue
      let saved ← saveState
      let result : Except Failure (SourceSession ⊕ Reading) ← try
        let formed ← session.readStatement statement
        match formed with
        | .definition next _ => pure (.ok (Sum.inl next))
        | .question term | .implemented term | .settled term =>
          pure (.ok (Sum.inr (← reading session where_ provenance term)))
      catch error =>
        saved.restore
        pure (.error (← failure where_ stage error))
      match result with
      | .ok (.inl next) => session := next
      | .ok (.inr row) =>
        observation := { observation with readings := observation.readings.push row }
      | .error error =>
        observation := { observation with failures := observation.failures.push error }
        if name.isSome then rootFailure := some error
        else observation := { observation with
          readings := observation.readings.push (unread where_ provenance) }
    return observation

end CasTools.QuestionExport
