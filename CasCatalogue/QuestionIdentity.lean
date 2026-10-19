/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import Lean

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

end CasCatalogue.QuestionIdentity
