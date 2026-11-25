module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourceLimit
public import CasCompiler.SourceConstruction
public import CasCompiler.SourceRing
public import CasCompiler.SourceMember
public import CasCompiler.SourceAdmission
import CasCompiler.FamilyConversion

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

/-- Category syntax names an accepted row, unless its head is a lexical binding.
An unmatched category form remains an ordinary source domain; a selected row's errors propagate. -/
partial def categoryEntry? (source : TSyntax `cas_term) :
    TermElabM (Option (CasCatalogue.NamedCategoryEntry × Array (TSyntax `cas_term))) := do
  if let `(cas_term| ($inner:cas_term)) := source then return ← categoryEntry? inner
  let (name, arguments, over) ← match source with
    | `(cas_term| $name:ident) => pure (name, #[], false)
    | `(cas_term| $name:ident($arguments:cas_term,*)) =>
      pure (name, arguments.getElems, false)
    | `(cas_term| $name:ident / $base:cas_term) => pure (name, #[base], true)
    | _ => return none
  if ((← getLCtx).findFromUserName? name.getId).isSome then return none
  let state ← CasCatalogue.semanticState
  let spelling := name.getId.toString (escape := false)
  let names := if over then #[spelling ++ "/", spelling] else #[spelling]
  let some selected := names.find? fun name => state.categories.any (·.name == name)
    | return none
  return some (← selectCategory state selected, arguments)

/-- Apply the selected category family through the shared dependent source application reader. -/
def category (context : ReadContext) (entry : CasCatalogue.NamedCategoryEntry)
    (arguments : Array (TSyntax `cas_term)) : TermElabM Expr := do
  discard <| checkedDeclaration entry.declaration
  let family ← mkConstWithFreshMVarLevels entry.declaration
  let bundle ← application context ⟨family, none⟩ arguments none
  discard <| categoryIdentity bundle
  return bundle

private structure FormedObjectCandidate where
  value : Expr
  bundle : Expr
  carrier : Option NativeSourceCarrierSelection
  parameters : Array Expr
  levels : List Level

private def FormedObjectCandidate.fields (image : FormedObjectCandidate) : Array Expr :=
  #[image.bundle, image.value] ++ (image.carrier.map (·.comparisons) |>.getD #[])

private def FormedObjectCandidate.instantiate (image : FormedObjectCandidate) :
    TermElabM FormedObjectCandidate := do
  return { image with
    value := ← instantiateMVars image.value
    bundle := ← instantiateMVars image.bundle
    parameters := ← image.parameters.mapM instantiateMVars
    levels := ← image.levels.mapM instantiateLevelMVars
    carrier := ← image.carrier.mapM fun carrier => do
      return { carrier with
        actions := ← carrier.actions.mapM instantiateMVars
        comparisons := ← carrier.comparisons.mapM instantiateMVars } }

-- The callback forms this row at its own native telescope. No parameters are recovered from
-- another row or from a flattened carrier. Prefixes consume only the authored presentation.
private def formObjectCandidate (candidate : SourceObjectCandidate)
    (elaborate : Expr → Option Expr → TermElabM Expr) : TermElabM FormedObjectCandidate := do
  let (bundle, original) ← registeredExpressions (.inl candidate.entry) candidate.category elaborate
  let native ← sourceDomain (← instantiateMVars original)
  let .const declaration levels := native.getAppFn
    | throwError "the source object lost its complete native declaration application"
  unless declaration == candidate.entry.declaration do
    throwError "the source object changed its selected declaration"
  let carrier ← objectCarrierSelection candidate.entry bundle original
  if candidate.prefixLength == 0 then
    return ⟨original, bundle, carrier, native.getAppArgs, levels⟩
  let some carrier := carrier
    | throwError "the selected source prefix lost its authored carrier comparison"
  unless candidate.prefixLength < carrier.actions.size &&
      carrier.refs.size == carrier.actions.size do
    throwError "the selected source prefix is not an intermediate authored boundary"
  let mut value := original
  let mut imageBundle := bundle
  for action in carrier.actions.extract 0 candidate.prefixLength do
    let (_, target) ← CasCatalogue.functorCategoryBundles action
    value ← functorObject action value target
    imageBundle := target
  -- The image contains the consumed actions and original row/arguments. The existing carrier
  -- selection retains the unconsumed actions and the complete original comparison.
  let remaining := { carrier with
    refs := carrier.refs.extract candidate.prefixLength carrier.refs.size
    actions := carrier.actions.extract candidate.prefixLength carrier.actions.size }
  return ⟨value, imageBundle, some remaining, native.getAppArgs, levels⟩

-- Compare complete constructors at their own rigid native telescopes. Universes are renamed
-- by their declaration binder order; this never specializes a parameter or maps base carriers
-- backwards into a structure. Unequal telescope types require an independently supplied relation.
private def objectCandidateFamily (candidate : SourceObjectCandidate) (universes : List Name) :
    TermElabM (Array Expr) := do
  let info ← checkedDeclaration candidate.entry.declaration
  unless info.levelParams.length == universes.length do
    CasCatalogue.throwSemanticAmbiguity
      "the source constructors require a comparison of their complete universe families"
  let declaration := Lean.mkConst candidate.entry.declaration (universes.map Level.param)
  forallTelescopeReducing (← inferType declaration) fun parameters _ => do
    let image ← formObjectCandidate candidate fun _ _ => pure (mkAppN declaration parameters)
    image.fields.mapM fun field => do
      let field ← instantiateMVars field
      if field.hasMVar || field.hasLevelMVar then
        throwError "the complete source constructor family has undetermined parameters"
      mkLambdaFVars parameters field

private def readObjectCandidates (context : ReadContext)
    (candidates : Array SourceObjectCandidate) (arguments : Array (TSyntax `cas_term)) :
    TermElabM NativeSourceJudgement := do
  let some firstCandidate := candidates[0]?
    | throwError "the named source object has no selected candidate"
  let parameterCount ← withoutModifyingState do
    let info ← checkedDeclaration firstCandidate.entry.declaration
    let (_, binders, _) ← forallMetaTelescopeReducing info.type
    pure (binders.filter (·.isExplicit)).size
  let sourceArguments := arguments.take parameterCount
  let application := application context
  -- Read every matched row with the original syntax and its own declared parameter types.
  -- Errors are not a signal to retry a different mathematical interpretation.
  let images ← candidates.mapM fun candidate => do
    unless candidate.target.expression.syntacticEq firstCandidate.target.expression do
      CasCatalogue.throwSemanticAmbiguity "the source name has different target categories"
    let count ← withoutModifyingState do
      let info ← checkedDeclaration candidate.entry.declaration
      let (_, binders, _) ← forallMetaTelescopeReducing info.type
      pure (binders.filter (·.isExplicit)).size
    unless count == parameterCount do
      CasCatalogue.throwSemanticAmbiguity
        "the source constructors have different written telescopes"
    let image ← formObjectCandidate candidate fun function expected =>
      application ⟨function, none⟩ sourceArguments expected
    if parameterCount == arguments.size then
      if let some expected := context.expected then
        unless ← isDefEq (← inferType image.value) expected do
          throwError "the source constructor has a different complete parameter category"
    image.instantiate
  let some first := images[0]?
    | throwError "the source constructor did not form its original arguments"
  let mut carrier := first.carrier
  if images.size > 1 then
    let info ← checkedDeclaration firstCandidate.entry.declaration
    let universes ← info.levelParams.mapM fun _ => mkFreshUserName `objectUniverse
    let families ← candidates.mapM (objectCandidateFamily · universes)
    let some firstFamily := families[0]?
      | throwError "the source constructor lost its complete family"
    -- Existing comparison data may establish the exact whole-family equality. An arbitrary
    -- carrier isomorphism is not such evidence; sourceFamilyConversion checks the actual type.
    let supplied := images.flatMap (fun image => image.carrier.toArray.flatMap (·.comparisons)) ++
      context.expectedCategory.toArray.flatMap (fun category =>
        category.carrier.toArray.flatMap (·.comparisons))
    -- PreferredRoute selects a forward binding route from an already selected receiver.
    -- It cannot select a refining constructor from a base carrier. That existing selection
    -- remains in sourceStructuralView; explicit named-category selection was handled above.
    let mut agreements := #[]
    for other in images.drop 1, family in families.drop 1 do
      unless first.parameters.size == other.parameters.size && first.levels == other.levels &&
          (first.parameters.zip other.parameters).all (fun (left, right) => left.equal right) do
        CasCatalogue.throwSemanticAmbiguity
          "the source constructors selected different original native arguments"
      unless firstFamily.size == family.size do
        CasCatalogue.throwSemanticAmbiguity
          "the source constructors have different complete comparison data"
      for left in firstFamily, right in family,
          actualLeft in first.fields, actualRight in other.fields do
        let some proof ← sourceFamilyConversion left right supplied
          | CasCatalogue.throwSemanticAmbiguity
              "the complete source constructor families require their supplied agreement"
        let mut proof := proof.instantiateLevelParams universes first.levels
        for parameter in first.parameters do proof ← mkAppM ``congrFun #[proof, parameter]
        proof ← mkExpectedTypeHint (← instantiateMVars proof) (← mkEq actualLeft actualRight)
        checkWithKernel proof
        agreements := agreements.push proof
    -- These are comparisons of the complete named constructor families. Requiring their
    -- residual functors to agree on unrelated objects of the whole target category would add
    -- a stronger obligation. Keep the carrier selected by the chosen authored presentation.
    carrier := some (match first.carrier with
      | some selected => { selected with comparisons := selected.comparisons ++ agreements }
      | none => ⟨#[], firstCandidate.target.expression, #[], #[], agreements⟩)
  let result : NativeSourceJudgement := ⟨first.value,
    some ⟨.object, firstCandidate.target.expression, first.bundle, carrier, none⟩⟩
  if parameterCount < arguments.size then
    return ⟨← application result (arguments.drop parameterCount) context.expected, none⟩
  return result



def object (context : ReadContext) :
    String → Option String → Array (TSyntax `cas_term) → TermElabM NativeSourceJudgement :=
  fun name category arguments => do
    readObjectCandidates context
      (← sourceObjectCandidates name category context.expected) arguments

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
      let value ← application ⟨mkFVar declaration.fvarId, selected⟩ arguments expected
      return ⟨value, if arguments.isEmpty then selected else none⟩
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
     | .objects candidates => readObjectCandidates context candidates arguments
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
         return ⟨← application result (arguments.drop parameterCount) expected, none⟩
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
