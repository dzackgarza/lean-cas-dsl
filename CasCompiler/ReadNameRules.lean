module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed
public import CasCompiler.ReadMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadNameRules

open SourceReader

def ruleApplicable (context : ReadContext) :
    TermElabM (Except MessageData NativeSourceJudgement) := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let registered := registeredApplicable context
  let member := member context
  -- `m(X)` for a registered method or property `m` is `X.m()`. The rule applies when the name
  -- names no object, map, construction or limit shape, so no kind takes priority.
  let registeredOrMember := fun (name : TSyntax `ident) (arguments : Array (TSyntax `cas_term)) => do
    let state ← CasCatalogue.semanticState
    let spelling := name.getId.toString (escape := false)
    let memberName := state.methods.any (·.name == spelling) ||
      state.properties.any (·.name == spelling)
    let otherKind := state.objects.any (·.name == spelling) ||
      state.morphisms.any (·.name == spelling) ||
      state.constructions.any (·.name == spelling) ||
      state.limits.any (·.shape == spelling)
    match memberName && !otherKind, arguments with
    | true, #[receiver] => return .ok (← member receiver spelling #[])
    | _, _ => registered name arguments
  match source with
  | `(cas_term| $name:ident) =>
    if let some declaration := (← getLCtx).findFromUserName? name.getId then
      return .ok ⟨mkFVar declaration.fvarId, ← categoryOf declaration.fvarId⟩
    else if let some generator ← (sourceDifferentialOf? name.getId).filterM fun generator =>
        return ((← getLCtx).findFromUserName? generator).isSome then
      -- `dv` for a bound variable `v` is its differential `d(v)` (public language contract).
      return .ok (← readExpression categoryOf
        (← `(cas_term| $(mkIdentFrom name `d):ident($(mkIdentFrom name generator):ident)))
        expected qualification
        expectedCategory)
    else if name.getId == `false then return .ok ⟨mkConst ``False, none⟩
    else if name.getId == `true then return .ok ⟨mkConst ``True, none⟩
    else registered name #[]
  | `(cas_term| $name:ident($arguments:cas_term,*)) =>
    if ((← getLCtx).findFromUserName? name.getId).isSome then
      registered name arguments.getElems
    else if let .str receiver field := name.getId then do
      if !receiver.isAnonymous &&
          ((← getLCtx).findFromUserName? receiver).isSome then
        return .ok (← member (← `(cas_term| $(mkIdentFrom name receiver):ident)) field arguments.getElems)
      else
        -- `ℤ.is_finite()` lexes as one identifier. When the whole dotted name is not
        -- registered, the receiver is a term of the language read before the member.
        let state ← CasCatalogue.semanticState
        let spelling := name.getId.toString (escape := false)
        let named := state.objects.any (·.name == spelling) ||
          state.morphisms.any (·.name == spelling)
        let parsed := Parser.runParserCategory (← getEnv) `cas_term
          (receiver.toString (escape := false))
        match named || receiver.isAnonymous, parsed with
        | false, .ok source => return .ok (← member ⟨source⟩ field arguments.getElems)
        | _, _ => registeredOrMember name arguments.getElems
    else registeredOrMember name arguments.getElems
  | _ => throwReadRuleMismatch

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  match ← ruleApplicable context with
  | .ok value => pure value
  | .error message => throwError message

end ReadNameRules

end CasCompiler
