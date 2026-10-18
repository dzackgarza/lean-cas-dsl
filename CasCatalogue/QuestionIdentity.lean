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

/- Serialize typed syntax, quotienting only metadata, binder spelling and proofs of the
same proposition. The original expression is never rewritten. Local declarations are opened
before type inspection: a dependent proof token retains its proposition with de Bruijn indices.
No reduction of data, propositions, relations, or selected dictionaries is performed.
Only closed subterms are memoized; local and bound terms retain their current binder context. -/
/-- `isProofQuickApp` walks an application back to its head. Once an application is known
not to be a proof, its function cannot be a proof either: applying a proof-valued function
still produces a proof. Carry that fact down only the function spine. -/
partial def encodeWithKnownNonProof (intern : Json → TermElabM Nat)
    (closed : IO.Ref (Std.HashMap Expr Nat)) (term : Expr)
    (bound : Array FVarId) (knownNonProof : Bool) : TermElabM Nat := do
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then
    throwError "question contains unresolved typed terms"
  let reusable := !term.hasFVar && !term.hasLooseBVars
  if reusable then
    if let some index := (← closed.get)[term]? then return index
  let index ← if !knownNonProof && (← isProof term) then
    intern <| Json.arr #[toJson "proof", toJson
      (← encodeWithKnownNonProof intern closed (← inferType term) bound false)]
  else match term with
  | .mdata _ child => encodeWithKnownNonProof intern closed child bound knownNonProof
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
      return ← intern <| Json.arr #[toJson "app",
        toJson (← encodeWithKnownNonProof intern closed fn bound true),
        toJson (← encodeWithKnownNonProof intern closed arg bound false)]
  | .lam _ type body info =>
      let domain ← encodeWithKnownNonProof intern closed type bound false
      withLocalDecl .anonymous info type fun binder => do
        let body ← encodeWithKnownNonProof intern closed (body.instantiate1 binder)
          (bound.push binder.fvarId!) false
        return ← intern <| Json.arr #[toJson "lam", toJson domain, toJson body, toJson (reprStr info)]
  | .forallE _ type body info =>
      let domain ← encodeWithKnownNonProof intern closed type bound false
      withLocalDecl .anonymous info type fun binder => do
        let body ← encodeWithKnownNonProof intern closed (body.instantiate1 binder)
          (bound.push binder.fvarId!) false
        return ← intern <| Json.arr #[toJson "forall", toJson domain, toJson body, toJson (reprStr info)]
  | .letE _ type value body nondep =>
      let domain ← encodeWithKnownNonProof intern closed type bound false
      let valueNode ← encodeWithKnownNonProof intern closed value bound false
      withLetDecl .anonymous type value fun binder => do
        let body ← encodeWithKnownNonProof intern closed (body.instantiate1 binder)
          (bound.push binder.fvarId!) false
        return ← intern <| Json.arr #[toJson "let", toJson domain, toJson valueNode, toJson body, toJson nondep]
  | .lit literal => return ← intern <| Json.arr #[toJson "literal", toJson (reprStr literal)]
  | .proj name index value =>
      return ← intern <| Json.arr #[toJson "proj", toJson (reprStr name), toJson index,
        toJson (← encodeWithKnownNonProof intern closed value bound false)]
  if reusable then closed.modify (·.insert term index)
  return index

partial def encode (intern : Json → TermElabM Nat)
    (closed : IO.Ref (Std.HashMap Expr Nat)) (term : Expr)
    (bound : Array FVarId := #[]) : TermElabM Nat :=
  encodeWithKnownNonProof intern closed term bound false

end CasCatalogue.QuestionIdentity
