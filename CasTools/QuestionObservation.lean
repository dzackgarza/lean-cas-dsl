module

public import CasCompiler.Parse
public import CasCompiler.Read
public import CasCatalogue.QuestionIdentity
public import CasCompiler.SourceSnapshot
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
  /-- NativeExpression graph document for the exact whole closed proposition or the ordered
  closed terms of a settled typing conjunction. -/
  proposition : String
  prettyProposition : String
  /-- Complete native source terms, binding identities, selections and original spans.
  Expression indices refer to this snapshot's `nativeExpressions` node table. A settled
  conjunction retains one complete snapshot per ordered conjunct. -/
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

/-- The retained telescope already supplies the exact de Bruijn scopes. Close it directly
instead of reopening fresh locals and abstracting them again for each category field.
Reuse: ContextTelescope.capture and Lean.MetavarContext.MkBinding.mkBinding at v4.33.0;
its non-let domains use headBeta, with every let retained and no eta reduction. -/
private def closedLambda (term : ClosedTerm) : Expr :=
  term.context.entries.foldr (init := term.expression) fun entry body =>
    match entry.value with
    | none => .lam entry.userName entry.type.headBeta body entry.binderInfo
    | some value => .letE entry.userName entry.type value body entry.nondep

private def canonicalCategory (remap : CasCatalogue.Realize.TermRemap)
    (category : SourceCategoryBinding) : TermElabM Json := do
  let bundle := closedLambda category.bundle
  let carrier ← category.carrier.mapM fun carrier => do
    let encode := fun (term : ClosedTerm) => remap.encodeTerm (closedLambda term)
    let actions ← carrier.actions.mapM encode
    let comparisons ← carrier.comparisons.mapM encode
    return Json.mkObj [("refs", toJson (reprStr carrier.refs)),
      ("target", toJson (reprStr carrier.target)),
      ("identifications", toJson (carrier.identifications.map (·.toString (escape := false)))),
      ("actions", toJson actions), ("comparisons", toJson comparisons)]
  return Json.mkObj [("role", toJson <| match category.role with
      | .object => "object" | .morphism => "morphism"),
    ("expression", toJson (reprStr category.expression)),
    ("bundle", toJson (← remap.encodeTerm bundle)),
    ("carrier", toJson carrier)]

/-- A question is its proposition. A settled typing question retains every term read at its
declared type, in conjunct order. Singleton identity and snapshot formats remain unchanged.
Source: SourceStatement.settled and settledJudgements? in CasCompiler/ReadSession.lean. -/
private def reading (shared : CasCatalogue.Realize.TermTable) (session : SourceSession)
    (where_ : Location) (provenance : String)
    (terms : Array SourceTerm) (settled : Bool) : TermElabM Reading := do
  if terms.isEmpty then throwError "an exported question must retain its source terms"
  unless settled || terms.size == 1 do
    throwError "a proposition question must retain exactly one source term"
  -- Reuse the existing typed canonical serializer. It erases only native metadata,
  -- binder spelling and proofs of the same proposition; the unquotiented snapshot stays below.
  -- Source: CasCatalogue/QuestionIdentity.lean, QuestionIdentity.encode and TermTable.
  let table ← CasCatalogue.Realize.TermTable.new
  let remap ← CasCatalogue.Realize.TermRemap.new shared table
  let retained ← terms.mapM fun term => do
    let proposition ← term.source.withOpen fun bindings expression => do
      -- Retain unused parameters, hypotheses and lets; do not generalize a let into a parameter.
      -- Reuse: Lean.Meta.mkForallFVars at v4.33.0, with its explicit retention controls.
      if settled then
        let typed ← mkExpectedTypeHint expression (← inferType expression)
        return ← mkLambdaFVars (bindings.map (·.expression)) typed
          (usedLetOnly := false) (generalizeNondepLet := false)
      unless ← isProp expression do throwError "an exported question must be a proposition"
      mkForallFVars (bindings.map (·.expression)) expression
        (usedLetOnly := false) (generalizeNondepLet := false)
    let root ← remap.encodeTerm proposition
    let categories ← term.source.context.entries.mapM fun entry =>
      (session.categoryFor entry.id).mapM (canonicalCategory remap)
    let category ← term.category.mapM (canonicalCategory remap)
    let instances ← term.source.context.instances.mapM fun selected => do
      let some index := term.source.context.entries.findIdx? (·.id == selected.binding)
        | throwError "an exported instance is outside its actual source telescope"
      return Json.mkObj [("class", toJson (selected.className.toString (escape := false))),
        ("binding", toJson index)]
    return (proposition, [("proposition", toJson root),
      ("roles", toJson (term.source.context.entries.map (reprStr ·.role))),
      ("instances", toJson instances), ("categories", toJson categories),
      ("category", toJson category)])
  -- A settled reading is marked; a proposition keeps its existing identity document.
  let judgement := if settled then [("judgement", toJson "settled")] else []
  let roots := match retained with
    | #[(_, fields)] => fields
    | _ => [("conjuncts", toJson (retained.map fun (_, fields) => Json.mkObj fields))]
  let question ← table.finish <| Json.mkObj (judgement ++ roots)
  let propositions := retained.map (·.1)
  let shown ← propositions.mapM fun proposition => return (← ppExpr proposition).pretty
  let sourceContext := match terms with
    | #[term] => SourceSnapshot.snapshot session term none
    | _ => Json.mkObj [
        ("conjuncts", toJson (terms.map fun term => SourceSnapshot.snapshot session term none))]
  return ⟨where_.id, where_.file, where_.sourceLine, where_.source, provenance,
    question, (NativeExpression.encode propositions).compress,
    " and ".intercalate shown.toList, sourceContext⟩

/-- Observe each original item through the native source session. A failed definition blocks
the remaining file scope; a failed question leaves the preceding scope available. Native
saved-state restoration discards failed elaboration state without replaying source bindings.
Source: T029 complete-reading boundary and Lean.Elab.Term.saveState/restore. -/
opaque observeFile (file : SourceFile) (initial : SourceSession) : TermElabM Observation :=
  file.withContext do
    let mut session := initial
    let mut observation : Observation := {}
    let mut rootFailure : Option Failure := none
    -- Retained closed categories recur in later questions. Encode their typed syntax once;
    -- TermRemap reproduces each reading's original independent table and insertion order.
    let mut shared ← CasCatalogue.Realize.TermTable.new
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
        | .question term | .implemented term =>
          pure (.ok (Sum.inr (← reading shared session where_ provenance #[term] false)))
        | .settled terms =>
          pure (.ok (Sum.inr (← reading shared session where_ provenance terms true)))
      catch error =>
        saved.restore
        pure (.error (← failure where_ stage error))
      match result with
      | .ok (.inl next) => session := next
      | .ok (.inr row) =>
        observation := { observation with readings := observation.readings.push row }
      | .error error =>
        -- Encoding refs are outside Lean's saved state; discard them after its rollback.
        shared ← CasCatalogue.Realize.TermTable.new
        observation := { observation with failures := observation.failures.push error }
        if name.isSome then rootFailure := some error
        else observation := { observation with
          readings := observation.readings.push (unread where_ provenance) }
    return observation

end CasTools.QuestionExport
