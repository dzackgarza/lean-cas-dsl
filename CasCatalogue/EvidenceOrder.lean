/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.QuestionIdentity

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.EvidenceOrder

/-- The local parameters relevant to the typed identity quotient. Proof implementations
contribute their propositions, never the variables used only to construct the proof.
Nested binders are opened before type inspection, and exact shared subterms are visited once. -/
partial def collectParameters (ambient : LocalContext) (visited : IO.Ref ExprSet)
    (parameters : IO.Ref FVarIdSet) (term : Expr) : TermElabM Unit := do
  let term := (← instantiateMVars term).consumeMData
  if term.hasMVar || term.hasLevelMVar then
    throwError "an evidence ordering key contains an unresolved typed term"
  unless term.hasFVar do return
  if (← visited.get).contains term then return
  visited.modify (·.insert term)
  if ← isProof term then
    collectParameters ambient visited parameters (← inferType term)
    return
  match term with
  | .fvar id =>
      -- Inner binders belong to the expression, not its surrounding parameter telescope.
      let some declaration := ambient.find? id | return
      parameters.modify (·.insert id)
      collectParameters ambient visited parameters declaration.type
      if let some value := declaration.value? (allowNondep := true) then
        collectParameters ambient visited parameters value
  | .app function argument =>
      collectParameters ambient visited parameters function
      collectParameters ambient visited parameters argument
  | .lam name type body info | .forallE name type body info =>
      collectParameters ambient visited parameters type
      withLocalDecl name info type fun variable =>
        collectParameters ambient visited parameters (body.instantiate1 variable)
  | .letE name type value body _ =>
      collectParameters ambient visited parameters type
      collectParameters ambient visited parameters value
      withLetDecl name type value fun variable =>
        collectParameters ambient visited parameters (body.instantiate1 variable)
  | .proj _ _ value => collectParameters ambient visited parameters value
  | _ => pure ()

/-- One common ordered dependent telescope for an entire collection being ordered.
Every field uses these same slots; distinct local parameters cannot become separate
copies of `fun x => x`. This is private ordering evidence, not a closed question. -/
structure Context where
  parameters : Array FVarId
  binders : QuestionIdentity.BinderContext

def Context.ofTerms (terms : Array Expr) : TermElabM Context := do
  let ambient ← getLCtx
  let visited ← IO.mkRef ({} : ExprSet)
  let required ← IO.mkRef ({} : FVarIdSet)
  for term in terms do collectParameters ambient visited required term
  let required ← required.get
  let parameters := ambient.getFVarIds.filter required.contains
  let mut prefix : Array Expr := #[]
  let mut binders : QuestionIdentity.BinderContext := #[]
  for parameter in parameters do
    let declaration := ambient.get! parameter
    let type ← instantiateMVars declaration.type
    let value ← (declaration.value? (allowNondep := true)).mapM instantiateMVars
    binders := binders.push (type.abstract prefix, value.map (·.abstract prefix))
    prefix := prefix.push (.fvar parameter)
  return { parameters, binders }

/-- Encode a field in the common typed context. The existing encoder still rejects
unaccounted data variables; proof-local variables contribute their exact propositions. -/
def Context.encode (context : Context) (table : Realize.TermTable) (term : Expr) :
    TermElabM Nat := do
  let term ← instantiateMVars term
  QuestionIdentity.encodeInContext table.intern table.terms table.contextualTerms
    (term.abstract (context.parameters.map Expr.fvar)) term context.parameters context.binders

/-- BinderContext is a cache key, not serialized evidence. Root every complete local
type, binder kind, and let value explicitly, each in its already established prefix. -/
def Context.encodeBinders (context : Context) (table : Realize.TermTable) :
    TermElabM Json := do
  let ambient ← getLCtx
  let mut records : Array Json := #[]
  for index in [:context.parameters.size] do
    let declaration := ambient.get! context.parameters[index]!
    let prefix : Context := {
      parameters := context.parameters.extract 0 index
      binders := context.binders.extract 0 index }
    let type ← prefix.encode table declaration.type
    let value ← match declaration.value? (allowNondep := true) with
      | none => pure (Json.arr #[toJson "local"])
      | some value =>
          let nondependent := !declaration.isLet
          pure (Json.arr #[toJson "let", toJson nondependent,
            toJson (← prefix.encode table value)])
    records := records.push (Json.arr #[toJson (reprStr declaration.binderInfo), toJson type, value])
  return Json.arr records

/-- Each complete key has its own deterministic term-table insertion order. Shared
context slots and all record roots are retained; no data reduction or expression repr
participates. Final QuestionIdentity closure checks are intentionally unchanged. -/
def Context.key (context : Context)
    (record : (Expr → TermElabM Nat) → TermElabM Json) : TermElabM String := do
  let table ← Realize.TermTable.new
  let binders ← context.encodeBinders table
  let root ← record (context.encode table)
  table.finish (Json.arr #[binders, root])

end CasCatalogue.EvidenceOrder
