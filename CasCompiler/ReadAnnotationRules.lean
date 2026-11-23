module

public import CasCompiler.ReadContext
public import CasCompiler.ReadAdmission
public import CasCompiler.ReadOperation
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def annotated (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  let admitted := admitted context
  let elementOperation := elementOperation context
  fun (body domain : TSyntax `cas_term) => do
    let domain ← sourceCarrier (← readExpression categoryOf domain none)
    discard <| getLevel domain.value
    let typeOrigin ← sourceTypeOrigin? domain.value
    let originalReference ← sourceObjectReference? domain.value
    let typedReference ← match typeOrigin with
      | some original => sourceObjectReference? original.object
      | none => pure none
    let head := reprStr domain.value.consumeMData.getAppFn.constName?
    let typeHead := reprStr (typeOrigin.map fun original => original.type.consumeMData.getAppFn.constName?)
    let originalRef := reprStr (originalReference.map fun original => (original.1.raw, original.2.toString))
    let typedRef := reprStr (typedReference.map fun original => (original.1.raw, original.2.toString))
    logInfo m!"admission target: head={head}; typed={typeOrigin.isSome}; typeHead={typeHead}; original={originalRef}; typedObject={typedRef}"
    if let some entry ← sourceAdmissionDomain? domain.value then
      let identifier := body.raw.isIdent && ((← getLCtx).findFromUserName? body.raw.getId).isSome
      let typed ← if identifier then do
          let value ← readExpression categoryOf body none
          isDefEq (← inferType value.value) domain.value
        else pure false
      unless typed do
        let value ← admitted entry body domain.value
        return (⟨← mkExpectedTypeHint value domain.value, none⟩ : NativeSourceJudgement)
    -- A relation's annotation selects its operand structure, not its truth-value result.
    -- Reuse the same whole-family operation preparation as other element operations.
    match body with
    | `(cas_term| $left:cas_term ≤ $right:cas_term) =>
      return ← elementOperation "≤" #[left, right] #[] #[] (some domain.value)
    | `(cas_term| $left:cas_term < $right:cas_term) =>
      return ← elementOperation "<" #[left, right] #[] #[] (some domain.value)
    | _ => pure ()
    if let some expected := expected then checkRegisteredDomains domain.value expected
    readExpression categoryOf body (some domain.value)

end SourceReader

namespace ReadAnnotationRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let annotated := SourceReader.annotated context
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  match source with
  | `(cas_term| $body:cas_term in $domain:cas_term using ($evidence:cas_term,*)) => do
    let domain ← sourceCarrier (← readExpression categoryOf domain none)
    discard <| getLevel domain.value
    SourceReader.constrained context body domain.value evidence.getElems
  | `(cas_term| $body:cas_term in $category:ident / $base:cas_term) => do
    -- `X in C/Y`: X read in the registered category family C at its base parameter Y.
    let state ← CasCatalogue.semanticState
    let name := category.getId.toString (escape := false)
    -- The family registered as `C/` (`Schemes/`, beside `Schemes`), else `C` itself.
    let some entry := (state.categories.find? (·.name == name ++ "/")).orElse fun _ =>
        state.categories.find? (·.name == name)
      | annotated body (← `(cas_term| $category:ident / $base:cas_term))
    let name := entry.name
    discard <| checkedDeclaration entry.declaration
    let family ← mkConstWithFreshMVarLevels entry.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let some parameter := parameters.back?
      | throwError "the category {name} has no base parameter"
    let base ← readExpression categoryOf base (some (← instantiateMVars (← inferType parameter)))
    unless ← isDefEq parameter base.value do
      throwError "the base is not an object of the base category of {name}"
    -- An object already selected elsewhere is in C through C's registered refinement of its
    -- object family, at the same parameters (`ℂ[x₀, …]` as a ℂ-algebra).
    let object ← readExpression categoryOf body none
    let judgement ← if object.category.any (·.expression.syntacticEq entry.expression) then
        pure object
      else do
        let value ← zetaReduce (← instantiateMVars object.value)
        let some original := state.objects.find? fun row =>
            value.consumeMData.getAppFn.isConstOf row.declaration
          | throwError "the value does not name a registered object"
        let rows := state.objects.filter fun row =>
          row.category == entry.id && (row.refines.any (·.base == original.id) ||
            original.refines.any (·.base == row.id))
        let #[refinement] := rows
          | CasCatalogue.throwStratum .invalid m!"{original.name} has no registered object in {name}"
        let arguments ← sourceExplicitArguments value.consumeMData
        let (bundle, refined) ← registeredExpressions (.inl refinement) entry
          fun function expected =>
            elabAppArgs function #[] (arguments.map Arg.expr) expected false false
        pure (⟨refined, some ⟨.object, entry.expression, bundle, none, none⟩⟩ : NativeSourceJudgement)
    let some selected := judgement.category
      | throwError "the source value has no selected category"
    unless ← isDefEq (mkAppN family parameters) selected.bundle do
      CasCatalogue.throwStratum .invalid m!"the value is not an object of {name} over this base"
    return judgement
  | `(cas_term| $body:cas_term in $category:ident) => do
    if ((← getLCtx).findFromUserName? category.getId).isSome then
      annotated body (← `(cas_term| $category:ident))
    else
      readExpression categoryOf body expected (some (category.getId.toString (escape := false)))
  | `(cas_term| $body:cas_term in $domain:cas_term) =>
    annotated body domain
  | _ => throwReadRuleMismatch

end ReadAnnotationRules

end CasCompiler
