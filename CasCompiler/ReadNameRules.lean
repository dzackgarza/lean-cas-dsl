module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed
public import CasCompiler.ReadMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadNameRules

open SourceReader

def ruleCompleting (context : ReadContext) (complete : ReadCompletion) :
    SourceReadM (Except MessageData NativeSourceJudgement) := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let registered := registeredCompleting context complete
  let member := memberCompleting context complete


  let registeredOrMember : TSyntax `ident → Array (TSyntax `cas_term) →
      SourceReadM (Except MessageData NativeSourceJudgement) := fun name arguments => do
    let state ← CasCatalogue.semanticState
    let spelling := name.getId.toString (escape := false)
    let memberName := state.methods.any (·.name == spelling) ||
      state.properties.any (·.name == spelling)
    let otherKind := state.objects.any (·.name == spelling) ||
      state.morphisms.any (·.name == spelling) ||
      state.constructions.any (·.name == spelling) ||
      state.limits.any (·.shape == spelling)
    match memberName && !otherKind, arguments with
    | true, #[receiver] => member receiver spelling #[]
    | _, _ => registered name arguments
  match source with
  | `(cas_term| $name:ident) =>
    if let some declaration := (← liftM (m := MetaM) getLCtx).findFromUserName? name.getId then
      complete ⟨mkFVar declaration.fvarId, ← categoryOf declaration.fvarId⟩
    else if let some generator ← (sourceDifferentialOf? name.getId).filterM fun generator =>
        return ((← liftM (m := MetaM) getLCtx).findFromUserName? generator).isSome then

      return .ok (← readExpression categoryOf
        (← liftM (m := TermElabM) `(cas_term| $(mkIdentFrom name `d):ident($(mkIdentFrom name generator):ident)))
        expected qualification
        expectedCategory)
    else if name.getId == `false then complete ⟨mkConst ``False, none⟩
    else if name.getId == `true then complete ⟨mkConst ``True, none⟩
    else registered name #[]
  | `(cas_term| $name:ident($arguments:cas_term,*)) =>
    if ((← liftM (m := MetaM) getLCtx).findFromUserName? name.getId).isSome then
      registered name arguments.getElems
    else if let .str receiver field := name.getId then do
      if !receiver.isAnonymous &&
          ((← liftM (m := MetaM) getLCtx).findFromUserName? receiver).isSome then
        member (← liftM (m := TermElabM) `(cas_term| $(mkIdentFrom name receiver):ident)) field arguments.getElems
      else


        let state ← CasCatalogue.semanticState
        let spelling := name.getId.toString (escape := false)
        let named := state.objects.any (·.name == spelling) ||
          state.morphisms.any (·.name == spelling)
        let parsed := Parser.runParserCategory (← liftM (m := MetaM) getEnv) `cas_term
          (receiver.toString (escape := false))
        match named || receiver.isAnonymous, parsed with
        | false, .ok source => member ⟨source⟩ field arguments.getElems
        | _, _ => registeredOrMember name arguments.getElems
    else registeredOrMember name arguments.getElems
  | _ => throwReadRuleMismatch

def ruleApplicable (context : ReadContext) :
    SourceReadM (Except MessageData NativeSourceJudgement) :=
  ruleCompleting context (checkReadJudgementApplicable { context with qualification := none })

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  match ← ruleApplicable context with
  | .ok value => pure value
  | .error message => liftM (m := TermElabM) <| throwError message

end ReadNameRules

end CasCompiler
