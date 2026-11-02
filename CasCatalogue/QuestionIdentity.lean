/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import Lean
public import CasCatalogue.Trace

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.QuestionIdentity

partial def level : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ l => Json.arr #[toJson "succ", level l]
  | .max a b => Json.arr #[toJson "max", level a, level b]
  | .imax a b => Json.arr #[toJson "imax", level a, level b]
  | .param n => Json.arr #[toJson "param", toJson (reprStr n)]
  | .mvar _ => Json.arr #[toJson "unresolved"]

abbrev BinderContext := Array (Expr × Option Expr)

/-- Compare typed terms directly, independently of the serialized DAG. Bound variables
are related by paired local declarations; proof implementations are compared through
their proposition types. This does not use JSON, node interning, hashes as identities,
definitional reduction of data, or the serializer's contextual cache. -/
partial def compareInContext (cache : IO.Ref (Std.HashMap (Expr × Expr) Bool))
    (left right : Expr) (binders : Array (FVarId × FVarId)) : TermElabM Bool := do
  let left := left.consumeMData
  let right := right.consumeMData
  if let some result := (← cache.get)[(left, right)]? then return result
  let leftProof ← isProof left
  let rightProof ← isProof right
  let result ← if leftProof || rightProof then do
      unless leftProof && rightProof do return false
      compareInContext cache (← inferType left) (← inferType right) binders
    else match left, right with
    | .fvar a, .fvar b => pure (binders.contains (a, b))
    | .sort a, .sort b => pure (a == b)
    | .const a ls, .const b ms => pure (a == b && ls == ms)
    | .lit a, .lit b => pure (a == b)
    | .app f x, .app g y =>
        -- A producer's allocation ordinal is an execution address. Its complete
        -- selected descriptor and typed fields occur in the remaining applications
        -- and are still compared. Accepted operation-binding strings are unchanged.
        if f.isConstOf ``Trace.producerResult && g.isConstOf ``Trace.producerResult then
          compareInContext cache f g binders
        else
          compareInContext cache f g binders <&&> compareInContext cache x y binders
    | .lam _ a body info, .lam _ b other otherInfo => do
        unless info == otherInfo && (← compareInContext cache a b binders) do return false
        withLocalDecl .anonymous info a fun x =>
          withLocalDecl .anonymous otherInfo b fun y =>
            compareInContext cache (body.instantiate1 x) (other.instantiate1 y)
              (binders.push (x.fvarId!, y.fvarId!))
    | .forallE _ a body info, .forallE _ b other otherInfo => do
        unless info == otherInfo && (← compareInContext cache a b binders) do return false
        withLocalDecl .anonymous info a fun x =>
          withLocalDecl .anonymous otherInfo b fun y =>
            compareInContext cache (body.instantiate1 x) (other.instantiate1 y)
              (binders.push (x.fvarId!, y.fvarId!))
    | .letE _ a value body nondep, .letE _ b otherValue other otherNondep => do
        unless nondep == otherNondep && (← compareInContext cache a b binders) &&
            (← compareInContext cache value otherValue binders) do return false
        withLetDecl .anonymous a value fun x =>
          withLetDecl .anonymous b otherValue fun y =>
            compareInContext cache (body.instantiate1 x) (other.instantiate1 y)
              (binders.push (x.fvarId!, y.fvarId!))
    | .proj name index value, .proj other otherIndex otherValue =>
        if name != other || index != otherIndex then pure false
        else compareInContext cache value otherValue binders
    | _, _ => pure false
  cache.modify (·.insert (left, right) result)
  return result

/-- Independent structural comparison for the identity quotient implemented by
`encode`: metadata and binder spelling are ignored, proofs retain their exact
propositions, and all computational declarations, parameters and dictionaries
remain significant. A revision label alone is not a term comparison. Cross-revision
admission still requires independently assessed declarations and accepted inputs. -/
def equivalent (left right : Expr) : TermElabM Bool := do
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  for term in #[left, right] do
    if term.hasMVar || term.hasLevelMVar || term.hasFVar || term.hasLooseBVars then
      throwError "question comparison requires complete closed typed terms"
    unless ← isTypeCorrect term do
      throwError "question comparison received an ill-typed expression"
  compareInContext (← IO.mkRef {}) left right #[]

/-- Encode the unopened syntax alongside its locally opened form. The unopened expression and
its ordered binder types and let values identify a contextual subterm across fresh local IDs;
the opened form is used only where Lean must inspect a proof or create another local binder. -/
partial def encodeInContext (intern : Json → TermElabM Nat)
    (closed : IO.Ref (Std.HashMap Expr Nat))
    (contextual : IO.Ref (Std.HashMap (Expr × BinderContext) Nat))
    (raw opened : Expr) (bound : Array FVarId) (context : BinderContext) : TermElabM Nat := do
  let raw ← instantiateMVars raw
  let opened ← instantiateMVars opened
  if opened.hasMVar || opened.hasLevelMVar then
    throwError "question contains unresolved typed terms"
  let independent := !raw.hasFVar && !raw.hasLooseBVars
  if independent then
    if let some index := (← closed.get)[raw]? then return index
  else
    if let some index := (← contextual.get)[(raw, context)]? then return index
  let index ← if ← isProof opened then
    let type ← instantiateMVars (← inferType opened)
    let rawType := type.abstract (bound.map Expr.fvar)
    intern <| Json.arr #[toJson "proof",
      toJson (← encodeInContext intern closed contextual rawType type bound context)]
  else match raw, opened with
  | .mdata _ child, .mdata _ openedChild =>
      encodeInContext intern closed contextual child openedChild bound context
  | .bvar index, .fvar id =>
      if index < bound.size && bound[bound.size - 1 - index]! == id then
        intern <| Json.arr #[toJson "bvar", toJson index]
      else
        throwError "question contains a bound variable outside its typed context"
  | .bvar _, _ => throwError "question contains a bound variable outside its typed context"
  | .fvar _, _ => throwError "question contains an unclosed typed term"
  | .mvar _, _ => throwError "question contains unresolved typed terms"
  | .sort l, .sort _ => intern <| Json.arr #[toJson "sort", level l]
  | .const name levels, .const .. =>
      intern <| Json.arr #[toJson "const", toJson (reprStr name), toJson (levels.map level)]
  | .app fn arg, .app openedFn openedArg =>
      let (arg, openedArg) := if fn.isConstOf ``Trace.producerResult then
          (mkRawNatLit 0, mkRawNatLit 0)
        else (arg, openedArg)
      intern <| Json.arr #[toJson "app",
        toJson (← encodeInContext intern closed contextual fn openedFn bound context),
        toJson (← encodeInContext intern closed contextual arg openedArg bound context)]
  | .lam _ type body info, .lam _ openedType openedBody _ =>
      let domain ← encodeInContext intern closed contextual type openedType bound context
      withLocalDecl .anonymous info openedType fun binder => do
        let body ← encodeInContext intern closed contextual body
          (openedBody.instantiate1 binder) (bound.push binder.fvarId!)
          (context.push (type, none))
        return ← intern <| Json.arr #[toJson "lam", toJson domain, toJson body,
          toJson (reprStr info)]
  | .forallE _ type body info, .forallE _ openedType openedBody _ =>
      let domain ← encodeInContext intern closed contextual type openedType bound context
      withLocalDecl .anonymous info openedType fun binder => do
        let body ← encodeInContext intern closed contextual body
          (openedBody.instantiate1 binder) (bound.push binder.fvarId!)
          (context.push (type, none))
        return ← intern <| Json.arr #[toJson "forall", toJson domain, toJson body,
          toJson (reprStr info)]
  | .letE _ type value body nondep, .letE _ openedType openedValue openedBody _ =>
      let domain ← encodeInContext intern closed contextual type openedType bound context
      let valueNode ← encodeInContext intern closed contextual value openedValue bound context
      withLetDecl .anonymous openedType openedValue fun binder => do
        let body ← encodeInContext intern closed contextual body
          (openedBody.instantiate1 binder) (bound.push binder.fvarId!)
          (context.push (type, some value))
        return ← intern <| Json.arr #[toJson "let", toJson domain, toJson valueNode,
          toJson body, toJson nondep]
  | .lit literal, .lit _ => intern <| Json.arr #[toJson "literal", toJson (reprStr literal)]
  | .proj name index value, .proj _ _ openedValue =>
      intern <| Json.arr #[toJson "proj", toJson (reprStr name), toJson index,
        toJson (← encodeInContext intern closed contextual value openedValue bound context)]
  | _, _ => throwError "question changed shape while opening its typed binders"
  if independent then
    closed.modify (·.insert raw index)
  else
    contextual.modify (·.insert (raw, context) index)
  return index

/-- Serialize typed syntax, quotienting only metadata, binder spelling and proofs of the
same proposition. No reduction of data, propositions, relations, or selected dictionaries
is performed; a dependent proof token retains its proposition with de Bruijn indices. -/
def encode (intern : Json → TermElabM Nat)
    (closed : IO.Ref (Std.HashMap Expr Nat))
    (contextual : IO.Ref (Std.HashMap (Expr × BinderContext) Nat))
    (term : Expr) : TermElabM Nat :=
  encodeInContext intern closed contextual term term #[] #[]

/-- The method snapshot retains complete selected typed invocations, separately
from runtime ownership and packets. This is only an encoding: independent
comparison inspects every corresponding typed field directly. -/
def encodeMethodApplication (encode : Expr → TermElabM Nat)
    (application : MethodApplication) : TermElabM Json := do
  let context (value : CategoryContext) : TermElabM Json := do
    return Json.arr #[toJson (reprStr value.expression), toJson (← encode value.bundle)]
  let lifts ← application.lifts.mapM fun lift => do
    return Json.arr #[toJson lift.id.raw, toJson (← encode lift.evidence),
      toJson (← encode lift.action), toJson (← encode lift.receiver),
      toJson (← encode lift.input), toJson (← encode lift.result)]
  return Json.arr #[← context application.sourceContext,
    toJson (← application.routeApplications.mapM encode),
    toJson (← application.routeReceivers.mapM encode),
    toJson (← encode application.image), toJson (← encode application.application),
    toJson (← encode application.input), toJson (← encode application.baseResult),
    ← context application.baseContext, toJson (← encode application.result),
    ← context application.resultContext, Json.arr lifts]

/-- Preserve the existing primary order and resolve every tie by a complete canonical
record key. Equal records retain their multiplicity. The complete key is constructed only
for colliding primary keys; these strings order serialization, never decide semantic equality. -/
def orderByCompleteKey {α : Type} (records : Array (String × α))
    (fullKey : α → TermElabM String) : TermElabM (Array α) := do
  let sortGroup (group : Array α) : TermElabM (Array α) := do
    if group.size < 2 then return group
    let keyed ← group.mapM fun value => return (← fullKey value, value)
    return (keyed.qsort fun left right => left.1 < right.1).map (·.2)
  let mut result : Array α := #[]
  let mut group : Array α := #[]
  let mut key := ""
  for (primary, value) in records.qsort (fun left right => left.1 < right.1) do
    if !group.isEmpty && key != primary then
      result := result ++ (← sortGroup group)
      group := #[]
    key := primary
    group := group.push value
  return result ++ (← sortGroup group)

end CasCatalogue.QuestionIdentity

namespace CasCatalogue.Realize

open Lean Meta Elab Term

/-- Exact structural serialization with shared subterms. Hash maps are only indexes:
equality is checked on expressions or complete node encodings, never on a digest. -/
structure TermTable where
  terms : IO.Ref (Std.HashMap Expr Nat)
  contextualTerms : IO.Ref (Std.HashMap (Expr × QuestionIdentity.BinderContext) Nat)
  nodes : IO.Ref (Array Json)
  canonicalNodes : IO.Ref (Std.HashMap String Nat)

def TermTable.new : IO TermTable := do
  let terms ← IO.mkRef ({} : Std.HashMap Expr Nat)
  let contextualTerms ← IO.mkRef ({} : Std.HashMap
    (Expr × QuestionIdentity.BinderContext) Nat)
  let nodes ← IO.mkRef (#[] : Array Json)
  let canonicalNodes ← IO.mkRef ({} : Std.HashMap String Nat)
  return { terms, contextualTerms, nodes, canonicalNodes }

/-- Universe syntax is serialized without Lean's cached hash fields. -/
partial def encodeLevel : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ level => Json.arr #[toJson "succ", encodeLevel level]
  | .max left right => Json.arr #[toJson "max", encodeLevel left, encodeLevel right]
  | .imax left right => Json.arr #[toJson "imax", encodeLevel left, encodeLevel right]
  | .param name => Json.arr #[toJson "param", toJson (reprStr name)]
  | .mvar id => Json.arr #[toJson "unresolved", toJson (reprStr id)]

/-- Intern complete typed node descriptions. Context-sensitive expressions are never cached
inside the binder traversal; only their canonical node descriptions are shared. -/
def TermTable.intern (table : TermTable) (node : Json) : TermElabM Nat := do
  let description := node.compress
  if let some index := (← table.canonicalNodes.get)[description]? then return index
  let index := (← table.nodes.get).size
  table.nodes.modify (·.push node)
  table.canonicalNodes.modify (·.insert description index)
  return index

partial def TermTable.encode (table : TermTable) (term : Expr) : TermElabM Nat := do
  QuestionIdentity.encode table.intern table.terms table.contextualTerms term

def TermTable.finish (table : TermTable) (roots : Json) : IO String := do
  return (Json.mkObj [("roots", roots), ("terms", Json.arr (← table.nodes.get))]).compress

/-- Rebuild roots from an already encoded term DAG. Child indices are rewritten through the
target table, so visiting roots in a new order produces exactly the table that direct encoding
in that order would produce, without traversing the Lean expressions again. -/
structure TermRemap where
  source : TermTable
  target : TermTable
  mapped : IO.Ref (Std.HashMap Nat Nat)

def TermRemap.new (source target : TermTable) : IO TermRemap := do
  return { source, target, mapped := ← IO.mkRef {} }

partial def TermRemap.encode (remap : TermRemap) (root : Nat) : TermElabM Nat := do
  if let some mapped := (← remap.mapped.get)[root]? then return mapped
  let some node := (← remap.source.nodes.get)[root]?
    | throwError "a term identity DAG refers outside its node table"
  let child (value : Json) : TermElabM Nat := do
    let .ok index := value.getNat?
      | throwError "a term identity DAG has a nonnumeric child"
    remap.encode index
  let rebuilt ← match node with
    | .arr #[.str "proof", type] =>
        pure (Json.arr #[toJson "proof", toJson (← child type)])
    | .arr #[.str "app", fn, arg] =>
        pure (Json.arr #[toJson "app", toJson (← child fn), toJson (← child arg)])
    | .arr #[.str "lam", domain, body, info] =>
        pure (Json.arr #[toJson "lam", toJson (← child domain),
          toJson (← child body), info])
    | .arr #[.str "forall", domain, body, info] =>
        pure (Json.arr #[toJson "forall", toJson (← child domain),
          toJson (← child body), info])
    | .arr #[.str "let", domain, value, body, nondep] =>
        pure (Json.arr #[toJson "let", toJson (← child domain),
          toJson (← child value), toJson (← child body), nondep])
    | .arr #[.str "proj", name, index, value] =>
        pure (Json.arr #[toJson "proj", name, index, toJson (← child value)])
    | .arr #[.str "bvar", _] | .arr #[.str "sort", _] |
        .arr #[.str "const", _, _] | .arr #[.str "literal", _] => pure node
    | _ => throwError "a term identity DAG contains an unknown node"
  let mapped ← remap.target.intern rebuilt
  remap.mapped.modify (·.insert root mapped)
  return mapped

/-- Encode a term once in the source DAG, then reproduce its nodes in the target's current
insertion order. Closed source terms already encountered by another root require no Lean-term
traversal. -/
def TermRemap.encodeTerm (remap : TermRemap) (term : Expr) : TermElabM Nat := do
  let root ← if let some root := (← remap.source.terms.get)[term]? then pure root
    else remap.source.encode term
  remap.encode root

/-- The legacy standalone serialization of one root, recovered from a shared encoded DAG. -/
def TermTable.rootIdentity (source : TermTable) (root : Nat) : TermElabM String := do
  let target ← TermTable.new
  let remap ← TermRemap.new source target
  let root ← remap.encode root
  target.finish (toJson root)

def termIdentity (term : Expr) : TermElabM String := do
  let table ← TermTable.new
  let root ← table.encode term
  table.finish (toJson root)

end CasCatalogue.Realize
