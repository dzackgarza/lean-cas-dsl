module

public import CasCompiler.Surface
public import CasCompiler.FamilyConversion
public import LeanCategories.Catalogue.Constructors

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

-- Check the public constructor at its whole rigid category, before any receiver or
-- category parameters are supplied. Its native FullSubcategory contains the actual
-- monomorphism Arrow; no carrier shape selects a mathematical interface.
private def checkSubobjectConstructor (entry : ConstructorEntry) : MetaM Unit := do
  unless entry.signature == #[.category] do
    throwError "the selected subobject constructor changed its complete signature"
  let info ← checkedDeclaration entry.semantics
  let universes ← info.levelParams.mapM fun _ => mkFreshUserName `subobjectUniverse
  let family := Lean.mkConst entry.semantics (universes.map Level.param)
  let agreement ← forallTelescopeReducing (← inferType family) fun parameters _ => do
    let #[category] := parameters
      | throwError "the selected subobject constructor has additional native parameters"
    let expected ← applyConstructorInterface ``CasCatalogue.Constructors.subobjects
      #[category] #[category]
    let some proof ← withTransparency .all <|
        sourceFamilyConversion (mkAppN family parameters) expected #[]
      | throwError "the selected subobject constructor is not its complete native family"
    mkLambdaFVars parameters proof (usedOnly := false) (usedLetOnly := false)
  checkWithKernel agreement

/-- The domain and inclusion of the actual selected Subobjects object.
Reuse: Constructors.subobjects, FullSubcategory.obj and the native Arrow fields.
The whole accepted constructor is checked before specializing the selected complete bundle;
both projections remain rooted in this receiver, including after source aliasing. -/
def sourceSubobjectMember? (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  unless name == "obj" || name == "hom" do return none
  let some selected := receiver.category | return none
  unless selected.role == .object do return none
  let .construct id #[.category base] := selected.expression | return none
  let state ← semanticState
  let some constructor := state.constructor? id
    | throwError "the selected subobject constructor is absent"
  unless constructor.semantics == ``CasCatalogue.Constructors.subobjects do return none
  checkSubobjectConstructor constructor
  -- Specialize the selected base category's complete family against the supplied
  -- constructed bundle. Do not expand native structure parameters or any bound input.
  let family ← nativeCategoryFamily state base (fun _ => mkFreshLevelMVar)
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let bundle := mkAppN family parameters
  let expected ← applyConstructorInterface constructor.semantics #[bundle] #[bundle]
  unless ← isDefEq expected selected.bundle do
    throwError "the selected subobject has different complete native category parameters"
  let bundle ← instantiateMVars bundle
  if bundle.hasMVar || bundle.hasLevelMVar then
    throwError "the selected subobject requires its complete original category parameters"
  unless ← isDefEq (← inferType receiver.value)
      (← mkAppM ``CategoryTheory.Bundled.α #[selected.bundle]) do
    throwError "the selected subobject value does not inhabit its complete native category"
  -- mkProjection preserves the parent expression. The existing projection lowering
  -- therefore consumes the actual retained K, not another evaluation of its definition.
  let arrow ← mkProjection receiver.value `obj
  let value ← mkProjection arrow (if name == "obj" then `left else `hom)
  check value
  let role := if name == "obj" then SourceCategoryRole.object else .morphism
  return some ⟨value, some ⟨role, base, bundle, none, none⟩⟩

end CasCompiler
