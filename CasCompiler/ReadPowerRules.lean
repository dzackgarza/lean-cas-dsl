module

public import CasCompiler.ReadContext
public import CasCompiler.ReadNamed
public import CasCompiler.ReadOperation
public import CasCompiler.SourceDivision
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadPowerRules

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let qualification := context.qualification
  let expectedCategory := context.expectedCategory
  let elementOperation := elementOperation context
  let registered := registered context
  let notationObject := notationObject context
  let objectPower := objectPower context
  match source with
  | `(cas_term| $base:cas_term²) => do
    if let some object ← objectPower base (← liftM (m := TermElabM) `(cas_term| 2)) then return object
    readExpression categoryOf (← liftM (m := TermElabM) `(cas_term| $base:cas_term ^ 2)) expected qualification
      expectedCategory
  | `(cas_term| $base:cas_term³) => do
    if let some object ← objectPower base (← liftM (m := TermElabM) `(cas_term| 3)) then return object
    readExpression categoryOf (← liftM (m := TermElabM) `(cas_term| $base:cas_term ^ 3)) expected qualification
      expectedCategory
  | `(cas_term| √$operand:cas_term) =>

    registered (mkIdentFrom source `sqrt) #[operand]
  | `(cas_term| 𝒫($operand:cas_term)) =>
    registered (mkIdentFrom source (.mkSimple "𝒫")) #[operand]
  | `(cas_term| 2 ^ $power:cas_term) => do

    if power.raw.isOfKind ``CasCatalogue.Language.casAtom || power.raw.isIdent then
      let object ← readExpression categoryOf power none
      if object.category.any (·.role == .object) then
        return ← registered (mkIdentFrom source (.mkSimple "𝒫")) #[power]
    elementOperation "^" #[← liftM (m := TermElabM) `(cas_term| 2)] #[power] #[] none
  | `(cas_term| $base:cas_term ^ $power:cas_term) => do
    if let some object ← objectPower base power then return object
    elementOperation "^" #[base] #[power] #[] none
  | `(cas_term| $left:cas_term / $right:cas_term) => do

    let identifier := fun (term : TSyntax `cas_term) => match term with
      | `(cas_term| $name:ident) => some name.getId
      | _ => none
    if identifier left == some `d then
      if let some generator := (identifier right).bind sourceDifferentialOf? then
        if let some declaration := (← liftM (m := MetaM) getLCtx).findFromUserName? generator then
          let some morphism ← sourceMorphismFrom? "derivative" declaration.type
            | liftM (m := TermElabM) <| throwError "the ring of {generator} has no registered derivative"
          return ⟨morphism, none⟩

    if let some atom := sourceAtomName? left then
      if let some object ← notationObject s!"{atom}/" #[right] then return object

    let mut hints := #[]
    for operand in #[left, right] do
      if let `(cas_term| $identifier:ident) := operand then
        if ((← liftM (m := MetaM) getLCtx).findFromUserName? identifier.getId).isSome then
          hints := hints.push (← inferType (← readExpression categoryOf operand none).value)
    let some domain := (← liftM (m := MetaM) <| expected.mapM instantiateMVars).orElse fun _ => hints[0]?
      | liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource "source division requires the set of its operands"
    let owners ← sourceOperationDomains categoryOf domain none (#[domain] ++ hints)
    let value ← sourceDivision owners left right fun operand => do
      return (← readExpression categoryOf operand (some domain)).value
    return ⟨value, none⟩
  | _ => throwReadRuleMismatch

end ReadPowerRules

end CasCompiler
