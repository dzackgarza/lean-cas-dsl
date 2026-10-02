/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantic
public import CasCatalogue.Admission

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.StructuredResult

/-- The complete decoded construction. The cone retains its defining maps; its diagram and
wire answer are retained separately from the apex's presentation. -/
structure Result where
  diagram : Expr
  cone : Expr
  apex : Expr
  answer : Json

/-- Check the shape's complete constructor envelope before decoding any dependent fields.
The constructor decoder checks all fields, including the defining maps and their equations. -/
def decode (row : LimitEntry) (diagram : Expr) (answer : Json)
    (decodeConstructor : Name → Expr → Array Json →
      TermElabM (Except String (Expr × Array (Expr × Option Form)))) :
    TermElabM (Except String (Result × Array (Expr × Option Form))) := do
  let kind := if row.colimit then "cocone" else "cone"
  let .ok name := answer.getObjValAs? String "ctor"
    | return .error s!"expected a {kind} constructor"
  unless name == kind do return .error s!"expected {kind}, received {name}"
  let .ok args := (answer.getObjVal? "args").bind (·.getArr?)
    | return .error s!"the {kind} has no args array"
  let some constructor := standardCone row.shape row.colimit
    | return .error s!"no standard constructor for {row.shape} {kind}"
  let expected ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone
    else ``CategoryTheory.Limits.Cone) #[diagram]
  match ← decodeConstructor constructor expected args with
  | .error message => return .error message
  | .ok (cone, fields) =>
      let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt) #[cone]
      return .ok ({ diagram, cone, apex := ← instantiateMVars apex, answer }, fields)

/-- Execute a registered creation lift using an independently available upstream presentation.
An untrusted cone supplies no universal-property evidence: only a definitional identification
with the accepted presentation permits using its `IsLimit`. No leaf proof is consulted. -/
def lift (state : RegistryState) (entry : LiftEntry) (sourceDiagram : Expr)
    (result : Result) (presentation : Expr) : TermElabM (Except String Result) := do
  let presentation ← instantiateMVars presentation
  let decodedCone ← instantiateMVars result.cone
  if presentation.hasMVar || presentation.hasLevelMVar || decodedCone.hasMVar ||
      decodedCone.hasLevelMVar then
    return .error s!"{entry.id.raw}: universal-property reconstruction requires closed terms"
  let U ← state.edgeFunctor entry.edge
  let expectedDiagram ← withTransparency .all <| mkFunctorComp sourceDiagram U
  unless ← isDefEq result.diagram expectedDiagram do
    return .error s!"{entry.id.raw}: the decoded cone is over a different diagram"
  let acceptedCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  unless ← isDefEq acceptedCone decodedCone do
    return .error s!"{entry.id.raw}: no independent universal-property reconstruction is \
      available for the decoded cone"
  let evidence ← instantiateFresh entry.evidence
  let lifted ← elabTermAndSynthesize (← `(@CasCatalogue.liftedLimitCone _ _ _ _ _ _
    $(← exprToSyntax U) $(← exprToSyntax evidence) _ $(← exprToSyntax presentation))) none
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[lifted]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  return .ok { result with diagram := sourceDiagram, cone := ← instantiateMVars cone
                           apex := ← instantiateMVars apex }

end CasCatalogue.StructuredResult
