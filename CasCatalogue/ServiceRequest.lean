/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Language
public import CasCatalogue.Admission
public import CasCatalogue.ComputationalData
public import CasCatalogue.DirectConstruction
public import CasCatalogue.StructuredResult
public import CasCatalogue.DataOwnership

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.ServiceRequest

/-- Closed point invocations use the singleton domain selected by the registry. -/
def closedElementDomain : TermElabM Expr := do
  let object ← Language.oneObject.run {}
  (Language.semanticObject object).run {}

/-- The original formal point fixes its result interface before any reply. A
generalized map keeps its full Hom type; a closed point uses the already selected
global point. This is shared with the ordinary operation observer. -/
def pointResultValue (point : Expr) : TermElabM Expr := do
  let some (domain, target) := Language.homEnds? (← inferType point)
    | throwError "the requested point result lost its complete categorical endpoints"
  unless ← withTransparency .all <| isDefEq domain (← closedElementDomain) do
    return point
  let action ← Language.functionOf point
  let value := mkApp action (← Language.globalPoint.run {})
  unless ← withTransparency .all <| isDefEq (← inferType value) target do
    throwError "the requested point result changed its declared target"
  return value

/-- A typed operand supplied by the runtime. `handle` identifies its exact retained
Wire occurrence; this module neither owns nor reconstructs backend/session data. -/
structure Operand where
  value : Expr
  data : Json
  handle : Nat
  form : Option Form := none
  context : Option CategoryContext := none
  /-- Suppliers are attached to exact opaque occurrences relative to `data`. -/
  ownership : DataOwnership.Table := #[]

def Operand.fragment (operand : Operand) : DataOwnership.Data :=
  { json := operand.data, ownership := operand.ownership }

/-- Position existing scopes at their respective array indices. Equal JSON at
different indices never identifies or merges its suppliers. -/
def arrayOwnership (tables : Array DataOwnership.Table) : DataOwnership.Table := Id.run do
  let mut ownership : DataOwnership.Table := #[]
  for index in [:tables.size] do
    ownership := ownership ++ DataOwnership.prefix #[.index index] tables[index]!
  return ownership

/-- Scope the ordered fields of an existing public constructor envelope. -/
def argsOwnership (tables : Array DataOwnership.Table) : DataOwnership.Table :=
  DataOwnership.prefix #[.field "args"] (arrayOwnership tables)

def operandArrayOwnership (operands : Array Operand) : DataOwnership.Table :=
  arrayOwnership (operands.map (·.ownership))

/-- The published dependent telescope with its explicit computational operands.
The caller closes remaining formal obligations after the full receiver is bound. -/
structure Declaration where
  application : DirectConstruction.Application
  operands : Array Operand

/-- Every callback resolves references at the requested typed data role. It must
preserve the exact retained Wire and reject proofs, backend selectors and types.
No callback may turn a validator's fresh placeholder into a mathematical input. -/
structure Decoder where
  argument : Expr → Json → TermElabM Operand
  object : Json → TermElabM Operand
  arrow : Json → TermElabM Operand
  /-- `true` selects the source; `false` selects the target, matching the retained callable API. -/
  endpoint : Operand → Bool → TermElabM Operand
  project : Operand → String → Option Nat → TermElabM Operand
  condition : Expr → TermElabM Expr
  declaration : Name → Array Json → TermElabM Declaration

/-- A public data descriptor's already checked formal value and resolved typed
operands. Runtime ownership comes exclusively from the exact operand handles. -/
structure DataPrepared where
  value : Expr
  data : Json
  dependencies : Array Operand := #[]
  form : Option Form := none
  context : Option CategoryContext := none
  ownership : DataOwnership.Table := #[]

def DataPrepared.fragment (prepared : DataPrepared) : DataOwnership.Data :=
  { json := prepared.data, ownership := prepared.ownership }

/-- Object and whole-map actions reuse the ordinary executable image boundary.
Other published request families use the same admitted dispatch and completion. -/
inductive ActionPlan where
  | object (action : Expr) (original : Operand)
      (parameters : Array Json) (dependencies : Array Operand)
  | wholeMap (action : Expr) (source target : CategoryContext) (original : Operand)
      (descriptor : Json) (parameters : Array Json) (dependencies : Array Operand)
      (imageSource imageTarget : Operand)

/-- Preparation fixes meaning solely from the published declaration and typed
operands. Completion validates computational shape only. The enclosing caller's
formal expression is retained separately when a completed packet is reused. -/
structure Prepared where
  requestValue : Expr
  request : Json
  result : Expr
  /-- Exact complete declaration application selected before any execution.
  A proof-bearing derivation may specialize only this family occurrence. -/
  familyApplication : Option Expr := none
  resultForm : Form
  dependencies : Array Operand
  /-- Suppliers at the exact positions of the assembled public `request`. -/
  requestOwnership : DataOwnership.Table := #[]
  resultContext : Option CategoryContext := none
  objectResult : Bool := false
  callableResult : Bool := false
  /-- This preparer's completion validates a datum at the selected closed-point
  target, rather than a whole callable. Runtime reuse retains that exact role. -/
  pointResult : Bool := false
  action : Option ActionPlan := none
  /-- Existing semantic execution can own method/property routing and prescribed
  lifts. The runtime seeds this private trace with the exact retained operands. -/
  trace : Option Trace := none
  decisionResult : Bool := false
  constructionInputs : Option (Expr × ComputationalData.InterfaceObjects) := none
  /-- Relative scopes in the same order as `constructionInputs`' data operands. -/
  constructionInputOwnership : Array DataOwnership.Table := #[]
  /-- Structured replies expose their already declared port roles before scoped
  references are replaced. The callback checks a reference at a formal data field. -/
  validateTemplate : Option ((Expr → Json → TermElabM Unit) → Json → TermElabM Unit) := none
  complete : Json → TermElabM (Except String (Option StructuredResult.Result))

def Prepared.fragment (prepared : Prepared) : DataOwnership.Data :=
  { json := prepared.request, ownership := prepared.requestOwnership }

/-- Compose in the actual selected category dictionary, including constructed
categories without a global typeclass instance. -/
def compose (context : CategoryContext) (domain source target first second : Expr) :
    TermElabM Expr := do
  CategoryContext.checkMorphism context first domain source
  CategoryContext.checkMorphism context second source target
  let carrier ← CategoryContext.carrier context
  let dictionary ← CategoryContext.dictionary context
  let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some dictionary]
  let result ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
    #[some carrier, some categoryStructure, some domain, some source, some target, some first, some second]
  let result ← instantiateMVars result
  CategoryContext.checkMorphism context result domain target
  return result

/-- Reuse existing addresses for a complete derived context without inventing a
new named category or discarding its selected bundle. -/
def formFor (state : RegistryState) (context : CategoryContext)
    (origin : Form) (morphism : Bool := false) : Form :=
  match CategoryContext.named? state context.expression with
  | some category => if morphism then .canonicalMorphism category else .diagrams category
  | none => .contextual context.expression origin

end CasCatalogue.ServiceRequest
