module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed
public import CasCompiler.ReadMember

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadNameRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let registered := registered context
  let member := member context
  match source with
  | `(cas_term| $name:ident) =>
    if let some declaration := (← getLCtx).findFromUserName? name.getId then
      pure ⟨mkFVar declaration.fvarId, ← categoryOf declaration.fvarId⟩
    else if let some generator ← (sourceDifferentialOf? name.getId).filterM fun generator =>
        return ((← getLCtx).findFromUserName? generator).isSome then
      -- `dv` for a bound variable `v` is its differential `d(v)` (public language contract).
      readExpression categoryOf
        (← `(cas_term| $(mkIdentFrom name `d):ident($(mkIdentFrom name generator):ident)))
        expected qualification
        expectedCategory
    else if name.getId == `false then pure ⟨mkConst ``False, none⟩
    else if name.getId == `true then pure ⟨mkConst ``True, none⟩
    else registered name #[]
  | `(cas_term| $name:ident($arguments:cas_term,*)) =>
    if ((← getLCtx).findFromUserName? name.getId).isSome then
      registered name arguments.getElems
    else if let .str receiver field := name.getId then do
      if !receiver.isAnonymous &&
          ((← getLCtx).findFromUserName? receiver).isSome then
        member (← `(cas_term| $(mkIdentFrom name receiver):ident)) field arguments.getElems
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
        | false, .ok source => member ⟨source⟩ field arguments.getElems
        | _, _ => registered name arguments.getElems
    else registered name arguments.getElems
  | _ => throwReadRuleMismatch

end ReadNameRules

end CasCompiler
