module

public import CasCompiler.ReadContext
public import CasCompiler.PublishedSource
public import CasCompiler.ReadApplication
public import CasCompiler.SourceLimit
public import CasCompiler.SourceConstruction
public import CasCompiler.SourceRing
public import CasCompiler.SourceMember
public import CasCompiler.SourceAdmission

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def objectApplicable (context : ReadContext) :
    String → Option String → Array (TSyntax `cas_term) →
      SourceReadM (Except MessageData NativeSourceJudgement) :=
  let expected := context.expected
  let application := application context
  fun (name : String) (category : Option String)
      (arguments : Array (TSyntax `cas_term)) => do
    let selected ← selectObjectApplicable name category expected
    let (entry, categoryEntry) ← match selected with
      | .ok selected => pure selected
      | .error message => return .error message
    let (bundle, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
      application ⟨function, none⟩ arguments expected
    return .ok (⟨value, some ⟨.object, categoryEntry.expression, bundle,
      ← objectCarrierSelection entry bundle value, none⟩⟩ : NativeSourceJudgement)

def object (context : ReadContext) :
    String → Option String → Array (TSyntax `cas_term) → SourceReadM NativeSourceJudgement :=
  fun name category arguments => do
    match ← objectApplicable context name category arguments with
    | .ok value => pure value
    | .error message => liftM (m := TermElabM) <| throwError message

def registeredCompleting (context : ReadContext) (complete : ReadCompletion) :
    Ident → Array (TSyntax `cas_term) → SourceReadM (Except MessageData NativeSourceJudgement) :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  let qualification := context.qualification
  let application := applicationApplicable context
  fun (name : Ident) (arguments : Array (TSyntax `cas_term)) => do
    if let some declaration := (← liftM (m := MetaM) getLCtx).findFromUserName? name.getId then
      let selected ← categoryOf declaration.fvarId
      return ← applicationResultCompleting context ⟨mkFVar declaration.fvarId, selected⟩
        arguments expected complete

    let spelling := name.getId.toString (escape := false)
    if !arguments.isEmpty && (← CasCatalogue.semanticState).limits.any (·.shape == spelling) then
      let maps ← arguments.mapM (readExpression categoryOf · none)
      if let some limit ← sourceNamedLimit spelling maps then return ← complete limit
    if name.getId == `id then
      let #[argument] := arguments
        | liftM (m := TermElabM) <| throwError "source identity requires one object"
      let object ← readExpression categoryOf argument none
      let object ← if object.category.isSome then pure object
        else sourceSetJudgement .object object.value
      let some category := object.category
        | liftM (m := TermElabM) <| throwError "source identity requires its complete selected category"
      unless category.role == .object do liftM (m := TermElabM) <| throwError "source identity requires an object"
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
      let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
      let structureValue ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some carrier, some instanceValue]
      let function ← mkAppOptM ``CategoryTheory.CategoryStruct.id
        #[some carrier, some structureValue]
      let value ← elabAppArgs function #[] #[Arg.expr object.value] expected false false
      return ← complete ⟨value, some { category with role := .morphism, carrier := none, limit := none }⟩
    let spelling := name.getId.toString (escape := false)
    let (spelling, arguments) ← do
      let state ← CasCatalogue.semanticState
      let some (base, number) := CasCatalogue.Language.subscripted? spelling
        | pure (spelling, arguments)
      if state.objects.any (·.name == spelling) || state.morphisms.any (·.name == spelling) ||
          !state.objects.any (·.name == base) then
        pure (spelling, arguments)
      else


        let literal : TSyntax `num := ⟨Syntax.mkNumLit (toString number)⟩
        let leading ← liftM (m := TermElabM) `(cas_term| $literal:num)
        pure (base, #[leading] ++ arguments)
    let readNamed : SourceNamedEntry → SourceReadM (Except MessageData NativeSourceJudgement) := fun selected => do
     match selected with
     | .construction entry => do
       let some receiver := arguments.back?
         | liftM (m := TermElabM) <| throwError "a source construction requires its actual receiver"
       let receiver ← readExpression categoryOf receiver none
       return ← complete (← sourceConstruction entry receiver
         ((arguments.pop).map fun parameter type => do
           return (← readExpression categoryOf parameter (some type)).value))
     | .registered entry categoryEntry => do
       let declaration := match entry with
         | .inl entry => entry.declaration
         | .inr entry => entry.declaration
       let parameterCount ← liftM (m := MetaM) <| withoutModifyingState do
         let info ← checkedDeclaration declaration
         let (_, binders, _) ← forallMetaTelescopeReducing info.type
         pure (binders.filter (·.isExplicit)).size


       if let (.inr row, #[argument]) := (entry, arguments) then
         if parameterCount > 0 && !sourceNumeric argument.raw then
           let element ← readExpression categoryOf argument none
           let type ← liftM (m := MetaM) <| instantiateMVars (← inferType element.value)
           let parameterMatches ← liftM (m := MetaM) <| withoutModifyingState do
             let info ← checkedDeclaration declaration
             let (parameters, binders, _) ← forallMetaTelescopeReducing info.type
             let some (first, _) := (parameters.zip binders).find? (·.2.isExplicit)
               | throwError "the named map lost its declaration parameter"
             isDefEq type (← inferType first)


           let indexing := element.category.any (·.role == .object)
           unless indexing || parameterMatches do
             let some morphism ← sourceMorphismFrom? row.name type (some row)
               | return .error m!"the named map {row.name} does not leave the set of its argument"
             let function ← sourceSetFunction morphism
             return ← complete ⟨← elabAppArgs function #[] #[Arg.expr element.value] none false false, none⟩
       if arguments.size < parameterCount then
         return .error m!"the registered source declaration requires {parameterCount} explicit parameters"
       let formed ← PublishedSource.namedApplicable entry categoryEntry
         (fun selected expected => SourceReadM.select selected expected) fun function expected =>
           application ⟨function, none⟩ (arguments.take parameterCount) expected
       let (bundle, value) ← match formed with
         | .ok value => pure value
         | .error message => return .error message
       let role := match entry with
         | .inl _ => SourceCategoryRole.object
         | .inr _ => SourceCategoryRole.morphism
       let carrier ← match entry with
         | .inl object => objectCarrierSelection object bundle value
         | .inr _ => pure none
       let result : NativeSourceJudgement :=
         ⟨value, some ⟨role, categoryEntry.expression, bundle, carrier, none⟩⟩


       if role == .morphism && parameterCount == arguments.size then
         if let some expected := expected then
           let expected ← liftM (m := MetaM) <| instantiateMVars expected
           let type ← whnfR (← inferType value)
           if !expected.isSort && type.isAppOfArity ``Quiver.Hom 4 &&
               !(← whnfR expected).isAppOfArity ``Quiver.Hom 4 then
             let source ← declaredEndpoint type.getAppArgs[2]!
             if (← synthInstance? (← mkAppM ``Unique #[source])).isSome then
               return ← complete ⟨← sourcePointValue value (some expected), none⟩
       if parameterCount < arguments.size then
         return ← applicationResultCompleting context result (arguments.drop parameterCount) expected complete
       return ← complete result
    let selection ← selectNamedApplicable spelling qualification expected
    let candidates ← match selection with
      | .ok selected => pure selected
      | .error message => return .error message
    SourceReadM.chooseApplicable (candidates.map readNamed)
      m!"no registered reading of source name {spelling} accepts its actual arguments"
      m!"source name {spelling} requires a category qualification"



def registeredApplicable (context : ReadContext) :
    Ident → Array (TSyntax `cas_term) → SourceReadM (Except MessageData NativeSourceJudgement) :=
  registeredCompleting context
    (checkReadJudgementApplicable { context with qualification := none })


def registered (context : ReadContext) :
    Ident → Array (TSyntax `cas_term) → SourceReadM NativeSourceJudgement :=
  fun name arguments => do
    match ← registeredApplicable context name arguments with
    | .ok value => pure value
    | .error message => liftM (m := TermElabM) <| throwError message

def notationObject (context : ReadContext) :
    String → Array (TSyntax `cas_term) → SourceReadM (Option NativeSourceJudgement) :=
  let application := application context
  fun (form : String) (arguments : Array (TSyntax `cas_term)) => do
    let state ← CasCatalogue.semanticState
    let rows := state.objects.filter (·.notations.contains form)
    let #[entry] := rows
      | if rows.isEmpty then return none
        else liftM (m := TermElabM) <| CasCatalogue.throwSemanticAmbiguity s!"several objects declare the notation {form}"
    let #[categoryEntry] := state.categories.filter (·.id == entry.category)
      | liftM (m := TermElabM) <| throwError "the notation object requires one complete category"
    let (bundle, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
      application ⟨function, none⟩ arguments expected
    return some (⟨value, some ⟨.object, categoryEntry.expression, bundle,
      ← objectCarrierSelection entry bundle value, none⟩⟩ : NativeSourceJudgement)

def objectPower (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → SourceReadM (Option NativeSourceJudgement) :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let notationObject := notationObject context
  let registered := registered context
  fun (base power : TSyntax `cas_term) => do
    let `(cas_term| $_:num) := power | return none
    if let `(cas_term| ($inner:cas_term)) := base then
      if let `(cas_term| $atom:cas_term / $modulus:cas_term) := inner then
        if let some name := sourceAtomName? atom then
          if let some object ← notationObject s!"({name}/)^" #[modulus, power] then
            return some object
    let named := base.raw.isOfKind ``CasCatalogue.Language.casAtom || base.raw.isIdent ||
      (match base with
        | `(cas_term| $_:ident) => true
        | `(cas_term| $_:ident($_:cas_term,*)) => true
        | `(cas_term| ($_:cas_term)) => true
        | _ => false)
    unless named do return none
    let object ← readExpression categoryOf base none
    unless object.category.any (·.role == .object) do return none
    return some (← registered (mkIdentFrom source `Vec) #[base, power])

def relatedObject (context : ReadContext) :
    TSyntax `cas_term → (String → String) → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (base : TSyntax `cas_term) (derived : String → String) => do
    let base ← readExpression categoryOf base none
    let state ← CasCatalogue.semanticState
    let (original, entries) ← registeredSourceDomain base.value
    let #[entry] := entries
      | liftM (m := TermElabM) <| throwError "the derived object is formed of one registered object"
    let rows := state.objects.filter (·.name == derived entry.name)
    let #[target] := rows
      | liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource s!"no registered object {derived entry.name}"
    let #[category] := state.categories.filter (·.id == target.category)
      | liftM (m := TermElabM) <| throwError "the derived object requires one complete category"
    let arguments ← sourceExplicitArguments original
    let (bundle, value) ← registeredExpressions (.inl target) category fun function expected =>
      elabAppArgs function #[] (arguments.map Arg.expr) expected false false
    return (⟨value, some ⟨.object, category.expression, bundle,
      ← objectCarrierSelection target bundle value, none⟩⟩ : NativeSourceJudgement)

end SourceReader

end CasCompiler
