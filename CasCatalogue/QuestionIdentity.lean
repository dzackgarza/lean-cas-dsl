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

/-- Serialize typed syntax, quotienting only metadata, binder spelling and proofs of the
same proposition. The original expression is never rewritten. Local declarations are opened
before type inspection: a dependent proof token retains its proposition with de Bruijn indices.
No reduction of data, propositions, relations, or selected dictionaries is performed. -/
partial def encode (intern : Json → TermElabM Nat) (term : Expr)
    (bound : Array FVarId := #[]) : TermElabM Nat := do
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then
    throwError "question contains unresolved typed terms"
  if ← isProof term then
    return ← intern <| Json.arr #[toJson "proof", toJson (← encode intern (← inferType term) bound)]
  match term with
  | .mdata _ child => encode intern child bound
  | .bvar _ => throwError "question contains a bound variable outside its typed context"
  | .fvar id =>
      for position in [:bound.size] do
        if bound[position]! == id then
          return ← intern <| Json.arr #[toJson "bvar", toJson (bound.size - 1 - position)]
      throwError "question contains an unclosed typed term"
  | .mvar _ => throwError "question contains unresolved typed terms"
  | .sort l => return ← intern <| Json.arr #[toJson "sort", level l]
  | .const name levels =>
      return ← intern <| Json.arr #[toJson "const", toJson (reprStr name), toJson (levels.map level)]
  | .app fn arg =>
      return ← intern <| Json.arr #[toJson "app", toJson (← encode intern fn bound), toJson (← encode intern arg bound)]
  | .lam _ type body info =>
      let domain ← encode intern type bound
      withLocalDecl .anonymous info type fun binder => do
        let body ← encode intern (body.instantiate1 binder) (bound.push binder.fvarId!)
        return ← intern <| Json.arr #[toJson "lam", toJson domain, toJson body, toJson (reprStr info)]
  | .forallE _ type body info =>
      let domain ← encode intern type bound
      withLocalDecl .anonymous info type fun binder => do
        let body ← encode intern (body.instantiate1 binder) (bound.push binder.fvarId!)
        return ← intern <| Json.arr #[toJson "forall", toJson domain, toJson body, toJson (reprStr info)]
  | .letE _ type value body nondep =>
      let domain ← encode intern type bound
      let valueNode ← encode intern value bound
      withLetDecl .anonymous type value fun binder => do
        let body ← encode intern (body.instantiate1 binder) (bound.push binder.fvarId!)
        return ← intern <| Json.arr #[toJson "let", toJson domain, toJson valueNode, toJson body, toJson nondep]
  | .lit literal => return ← intern <| Json.arr #[toJson "literal", toJson (reprStr literal)]
  | .proj name index value =>
      return ← intern <| Json.arr #[toJson "proj", toJson (reprStr name), toJson index, toJson (← encode intern value bound)]

end CasCatalogue.QuestionIdentity
