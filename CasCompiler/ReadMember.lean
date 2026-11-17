module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourceMethod
public import CasCompiler.SourceMember
public import CasCompiler.SourceSubset
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def member (context : ReadContext) :
    TSyntax `cas_term → String → Array (TSyntax `cas_term) → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  let qualification := context.qualification
  let application := application context
  fun (receiver : TSyntax `cas_term) (name : String)
      (arguments : Array (TSyntax `cas_term)) => do
    let readArguments : Option (Expr → TermElabM Expr) := if arguments.isEmpty then none
      else some fun type => do
        if let #[argument] := arguments then
          return (← readExpression categoryOf argument (some type)).value
        sourceTuple arguments type fun source type => do
          return (← readExpression categoryOf source (some type)).value
    -- A numeral receiver is read at the declared source of the registered method. A
    -- number-system atom (`ℤ.is_finite()`) names an object and is not a numeral receiver.
    if sourceNumeric receiver.raw && !receiver.raw.isOfKind ``CasCatalogue.Language.casAtom then
      let read := fun (type : Expr) => do
        return (← readExpression categoryOf receiver (some type)).value
      let some value ← sourceElementMember? name none read readArguments
        | throwError "no registered morphism {name} accepts this numeral"
      return (⟨value, none⟩ : NativeSourceJudgement)
    let receiver ← readExpression categoryOf receiver none
    if let some value ← context.project receiver name arguments then return value
    -- `f.image()` is the image of the whole map, as `f(X)` (PowerObjectEntry.image).
    if name == "image" && arguments.isEmpty then
      if let some (domain, codomain) ← mapEnds receiver.value then
        return (⟨← sourceImageOf (← sourcePowerObjectAt codomain) domain receiver.value expected,
          none⟩ : NativeSourceJudgement)
    -- A method of objects on a subset is its extent's method (`Fs.cardinality()`).
    let object ← match ← sourceExtent? receiver with
      | some extent => pure extent
      | none => pure receiver
    let method ← sourceMethod object name
    let family ← sourceMemberFamily object name qualification
    let family ← match method, family with
      | some _, some _ =>
        CasCatalogue.throwSemanticAmbiguity
          "a method and a member family both accept this selected receiver"
      | some method, none => pure method
      | none, some family => pure family
      | none, none => do
        if arguments.isEmpty then
          if let some property ← sourceProperty object name then return property
        let some value ← sourceElementMember? name (some receiver) (fun _ => pure receiver.value)
            readArguments
          | throwError "no declared member family accepts this complete selected receiver"
        return (⟨value, none⟩ : NativeSourceJudgement)
    if arguments.isEmpty then return family
    if arguments.size == 1 then
      return (⟨← application family arguments expected, none⟩ : NativeSourceJudgement)
    let function ← sourceFunction family
    let argument ← mkFreshExprMVar none
    discard <| elabAppArgs function #[] #[Arg.expr argument] expected false false
    let type ← instantiateMVars (← inferType argument)
    let argument ← sourceTuple arguments type fun source type => do
      return (← readExpression categoryOf source (some type)).value
    return (⟨← elabAppArgs function #[] #[Arg.expr argument] expected false false, none⟩ :
      NativeSourceJudgement)

end SourceReader

end CasCompiler
