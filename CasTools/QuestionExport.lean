module

public import CasCompiler.Parse
public import CasCompiler.Read
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
  question : String
  proposition : String
  prettyProposition : String
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

private def contextJson (context : ContextTelescope) : Json :=
  toJson <| context.entries.map fun entry => Json.mkObj [
    ("id", bindingJson entry.id), ("name", toJson (entry.userName.toString (escape := false))),
    ("role", toJson <| match entry.role with
      | .parameter => "parameter" | .definition => "definition" | .hypothesis => "hypothesis"
      | .instance => "instance" | .selectedStructure => "selectedStructure" | .result => "result"),
    ("binderInfo", toJson (reprStr entry.binderInfo)),
    ("kind", toJson (reprStr entry.kind)), ("type", toJson (reprStr entry.type)),
    ("value", toJson (entry.value.map reprStr)), ("nondep", toJson entry.nondep)]

-- Native Repr preserves every Expr constructor and MData value. The ordered closed
-- telescope supplies each de Bruijn scope. No native term, proof or dictionary is reduced.
-- Reference: Lean/Expr.lean deriving Repr; CasCompiler/Context.lean closeOver/withOpen.
private def closedTermJson (term : ClosedTerm) : Json :=
  Json.mkObj [
    ("context", contextJson term.context),
    ("instances", toJson <| term.context.instances.map fun selected => Json.mkObj [
      ("class", toJson (selected.className.toString (escape := false))),
      ("binding", bindingJson selected.binding)]),
    ("universeParams", toJson (term.universeParams.map (·.toString (escape := false)))),
    ("expression", toJson (reprStr term.expression)), ("type", toJson (reprStr term.type))]

private def categoryJson (category : SourceCategoryBinding) : Json :=
  Json.mkObj [("role", toJson <| match category.role with
      | .object => "object" | .morphism => "morphism"),
    ("expression", toJson (reprStr category.expression)),
    ("bundle", closedTermJson category.bundle)]

private def snapshot (session : SourceSession) (term : SourceTerm) : Json :=
  Json.mkObj [("native", closedTermJson term.source),
    ("context", contextJson term.source.context),
    ("instances", toJson <| term.source.context.instances.map fun selected => Json.mkObj [
      ("class", toJson (selected.className.toString (escape := false))),
      ("binding", bindingJson selected.binding)]),
    ("categories", toJson <| term.source.context.entries.map fun entry =>
      (session.categoryFor entry.id).map categoryJson),
    ("category", toJson (term.category.map categoryJson)),
    ("file", toJson term.span.fileName),
    ("startByte", toJson (term.span.start.map (·.byteIdx))),
    ("stopByte", toJson (term.span.stop.map (·.byteIdx)))]

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
  ⟨where_.id, where_.file, where_.sourceLine, where_.source, provenance, "", "", ""⟩

private def reading (session : SourceSession) (where_ : Location) (provenance : String)
    (term : SourceTerm) : MetaM Reading := do
  let proposition ← term.source.withOpen fun bindings expression => do
    unless ← isProp expression do throwError "an exported question must be a proposition"
    -- Retain unused parameters, hypotheses and lets; do not generalize a let into a parameter.
    -- Reuse: Lean.Meta.mkForallFVars at v4.33.0, with its explicit retention controls.
    mkForallFVars (bindings.map (·.expression)) expression
      (usedLetOnly := false) (generalizeNondepLet := false)
  return ⟨where_.id, where_.file, where_.sourceLine, where_.source, provenance,
    (snapshot session term).compress, reprStr proposition, (← ppExpr proposition).pretty⟩

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
      let result ← try
        let formed ← session.readStatement statement
        match formed with
        | .definition next _ => pure (.ok (Sum.inl next))
        | .question term => pure (.ok (Sum.inr (← reading session where_ provenance term)))
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
