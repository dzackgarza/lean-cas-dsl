module

public import CasCompiler.ReadContext
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

def object (context : ReadContext) :
    String → Option String → Array (TSyntax `cas_term) → TermElabM NativeSourceJudgement :=
  let expected := context.expected
  let application := application context
  fun (name : String) (category : Option String)
      (arguments : Array (TSyntax `cas_term)) => do
    let (entry, categoryEntry) ← selectObject name category expected
    let (bundle, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
      application ⟨function, none⟩ arguments expected
    return (⟨value, some ⟨.object, categoryEntry.expression, bundle,
      ← objectCarrierSelection entry bundle value, none⟩⟩ : NativeSourceJudgement)

def registered (context : ReadContext) :
    Ident → Array (TSyntax `cas_term) → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let expected := context.expected
  let qualification := context.qualification
  let application := application context
  fun (name : Ident) (arguments : Array (TSyntax `cas_term)) => do
    if let some declaration := (← getLCtx).findFromUserName? name.getId then
      let selected ← categoryOf declaration.fvarId
      return ← applicationResult context ⟨mkFVar declaration.fvarId, selected⟩
        arguments expected
    -- `pullback(f, g)`: a registered universal construction named by its shape.
    let spelling := name.getId.toString (escape := false)
    if !arguments.isEmpty && (← CasCatalogue.semanticState).limits.any (·.shape == spelling) then
      let maps ← arguments.mapM (readExpression categoryOf · none)
      if let some limit ← sourceNamedLimit spelling maps then return limit
    if name.getId == `id then
      let #[argument] := arguments
        | throwError "source identity requires one object"
      let object ← readExpression categoryOf argument none
      let object ← if object.category.isSome then pure object
        else sourceSetJudgement .object object.value
      let some category := object.category
        | throwError "source identity requires its complete selected category"
      unless category.role == .object do throwError "source identity requires an object"
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
      let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
      let structureValue ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some carrier, some instanceValue]
      let function ← mkAppOptM ``CategoryTheory.CategoryStruct.id
        #[some carrier, some structureValue]
      let value ← elabAppArgs function #[] #[Arg.expr object.value] expected false false
      return ⟨value, some { category with role := .morphism, carrier := none, limit := none }⟩
    let spelling := name.getId.toString (escape := false)
    let (spelling, arguments) ← do
      let state ← CasCatalogue.semanticState
      let some (base, number) := CasCatalogue.Language.subscripted? spelling
        | pure (spelling, arguments)
      if state.objects.any (·.name == spelling) || state.morphisms.any (·.name == spelling) ||
          !state.objects.any (·.name == base) then
        pure (spelling, arguments)
      else
        -- The documented leading parameter enters the same dependent application once.
        -- Exact lexical and registered spellings have already retained their own identity.
        let literal : TSyntax `num := ⟨Syntax.mkNumLit (toString number)⟩
        let leading ← `(cas_term| $literal:num)
        pure (base, #[leading] ++ arguments)
    let readNamed := fun (selected : SourceNamedEntry) => do
     match selected with
     | .construction entry => do
       let some receiver := arguments.back?
         | throwError "a source construction requires its actual receiver"
       let receiver ← readExpression categoryOf receiver none
       sourceConstruction entry receiver
         ((arguments.pop).map fun parameter type => do
           return (← readExpression categoryOf parameter (some type)).value)
     | .registered entry categoryEntry => do
       let declaration := match entry with
         | .inl entry => entry.declaration
         | .inr entry => entry.declaration
       let parameterCount ← withoutModifyingState do
         let info ← checkedDeclaration declaration
         let (_, binders, _) ← forallMetaTelescopeReducing info.type
         pure (binders.filter (·.isExplicit)).size
       -- `d(f)`: a named map applied to one element whose set fixes its declaration parameters,
       -- rather than one source argument per parameter (`rev(3, 2)`).
       if let (.inr row, #[argument]) := (entry, arguments) then
         if parameterCount > 0 && !sourceNumeric argument.raw then
           let element ← readExpression categoryOf argument none
           let type ← instantiateMVars (← inferType element.value)
           let parameterType ← withoutModifyingState do
             let info ← checkedDeclaration declaration
             let (parameters, binders, _) ← forallMetaTelescopeReducing info.type
             let some (first, _) := (parameters.zip binders).find? (·.2.isExplicit)
               | throwError "the named map lost its declaration parameter"
             instantiateMVars (← inferType first)
           -- An object argument instead indexes a family of global elements
           -- (`dimension(ℚ[x, y])`): it is read at the declared parameter type below.
           let indexing := element.category.any (·.role == .object)
           unless indexing || (← withoutModifyingState (isDefEq type parameterType)) do
             let some morphism ← sourceMorphismFrom? row.name type
               | throwError "the named map {row.name} does not leave the set of its argument"
             let function ← sourceSetFunction morphism
             return ⟨← elabAppArgs function #[] #[Arg.expr element.value] expected false false, none⟩
       let (bundle, value) ← registeredExpressions entry categoryEntry fun function expected =>
         application ⟨function, none⟩ (arguments.take parameterCount) expected
       let role := match entry with
         | .inl _ => SourceCategoryRole.object
         | .inr _ => SourceCategoryRole.morphism
       let carrier ← match entry with
         | .inl object => objectCarrierSelection object bundle value
         | .inr _ => pure none
       let result : NativeSourceJudgement :=
         ⟨value, some ⟨role, categoryEntry.expression, bundle, carrier, none⟩⟩
       -- A named global element `1 ⟶ X` (`i`, `π`) read where an element of a set is expected
       -- is its value at the terminal point.
       if role == .morphism && parameterCount == arguments.size then
         if let some expected := expected then
           let expected ← instantiateMVars expected
           let type ← whnfR (← inferType value)
           if !expected.isSort && type.isAppOfArity ``Quiver.Hom 4 &&
               !(← whnfR expected).isAppOfArity ``Quiver.Hom 4 then
             let source ← declaredEndpoint type.getAppArgs[2]!
             if (← synthInstance? (← mkAppM ``Unique #[source])).isSome then
               return ⟨← sourcePointValue value (some expected), none⟩
       if parameterCount < arguments.size then
         return ← applicationResult context result (arguments.drop parameterCount) expected
       return result
    let candidates ← selectNamed spelling qualification expected
    if let #[selected] := candidates then return ← readNamed selected
    -- Kinds sharing a name: the reading is the one candidate that accepts the arguments.
    let mut accepted := #[]
    for selected in candidates do
      let reads ← withoutModifyingState do
        try discard <| readNamed selected; pure true
        catch error => do
          CasCatalogue.keepTrialAmbiguity error
          pure false
      if reads then accepted := accepted.push selected
    let #[selected] := accepted
      | CasCatalogue.throwSemanticAmbiguity m!"source name {spelling} requires a category qualification"
    readNamed selected

def notationObject (context : ReadContext) :
    String → Array (TSyntax `cas_term) → TermElabM (Option NativeSourceJudgement) :=
  let application := application context
  fun (form : String) (arguments : Array (TSyntax `cas_term)) => do
    let state ← CasCatalogue.semanticState
    let rows := state.objects.filter (·.notations.contains form)
    let #[entry] := rows
      | if rows.isEmpty then return none
        else CasCatalogue.throwSemanticAmbiguity s!"several objects declare the notation {form}"
    let #[categoryEntry] := state.categories.filter (·.id == entry.category)
      | throwError "the notation object requires one complete category"
    let (bundle, value) ← registeredExpressions (.inl entry) categoryEntry fun function expected =>
      application ⟨function, none⟩ arguments expected
    return some (⟨value, some ⟨.object, categoryEntry.expression, bundle,
      ← objectCarrierSelection entry bundle value, none⟩⟩ : NativeSourceJudgement)

def objectPower (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → TermElabM (Option NativeSourceJudgement) :=
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
        | `(cas_term| $_:ident($_:cas_term,*)) => true
        | `(cas_term| ($_:cas_term)) => true
        | _ => false)
    unless named do return none
    let object ← readExpression categoryOf base none
    unless object.category.any (·.role == .object) do return none
    return some (← registered (mkIdentFrom source `Vec) #[base, power])

def relatedObject (context : ReadContext) :
    TSyntax `cas_term → (String → String) → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (base : TSyntax `cas_term) (derived : String → String) => do
    let base ← readExpression categoryOf base none
    let state ← CasCatalogue.semanticState
    -- A definition names the object its value is.
    let base := { base with value := ← zetaReduce (← instantiateMVars base.value) }
    let head := base.value.consumeMData.getAppFn
    let some entry := state.objects.find? fun entry => head.isConstOf entry.declaration
      | throwError "the derived object is formed of a registered object"
    let rows := state.objects.filter (·.name == derived entry.name)
    let #[target] := rows
      | CasCatalogue.throwUnsupportedSource s!"no registered object {derived entry.name}"
    let #[category] := state.categories.filter (·.id == target.category)
      | throwError "the derived object requires one complete category"
    let arguments ← sourceExplicitArguments (← instantiateMVars base.value.consumeMData)
    let (bundle, value) ← registeredExpressions (.inl target) category fun function expected =>
      elabAppArgs function #[] (arguments.map Arg.expr) expected false false
    return (⟨value, some ⟨.object, category.expression, bundle,
      ← objectCarrierSelection target bundle value, none⟩⟩ : NativeSourceJudgement)

end SourceReader

end CasCompiler
