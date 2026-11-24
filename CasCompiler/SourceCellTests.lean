module

import CasCompiler.Read
import CasCompiler.SourceCell
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.ConstructorRegistration
import LeanCategories.Catalogue.Semantics.Algebra.PortComparison
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceCell
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.ConstructorRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.PortComparison

open Lean Meta Elab Term CasCompiler CasCatalogue

private def readCellSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original cell component syntax did not parse"
  session.read ⟨parsed⟩

private def nativeCellType (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the original cell receiver type did not parse"
  return ⟨parsed⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeCellType "Type")
  for (id, inverse) in #[(NaturalTransformationId.listUnit, false),
      (NaturalTransformationId.listJoin, false), (NaturalTransformationId.listReverse, false),
      (NaturalTransformationId.listReverse, true)] do
    let spelling := if inverse then "inverse_component" else "component"
    let component ← readCellSource session s!"{spelling}(«{id.raw}»(), X, [])"
    let some selected := component.category
      | throwError "a public cell component lost its actual target category"
    unless selected.role == .morphism && selected.expression.syntacticEq Foundation.Sets do
      throwError "a public cell component changed its declared morphism role or target"
    component.source.withOpen fun bindings value => do
      let .mdata data _ := value
        | throwError "a public cell component lost its retained source selection"
      unless data.getString `CasCompiler.source.id == id.raw &&
          data.getBool `CasCompiler.source.cell.inverse == inverse &&
          data.getString `CasCompiler.source.cell.constructors == "[]" do
        throwError "a public cell component lost its exact row, direction or constructor path"
      let #[entry] := (← semanticState).cells.filter (·.id == id)
        | throwError "the independent list cell was not retained"
      let declaration := Lean.mkConst entry.declaration [.zero]
      let transformation ← if entry.invertible then
          mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[declaration]
        else pure declaration
      let expected ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, bindings[0]!.expression]
      unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a public cell component replaced its actual declared action or receiver"
      let some retained ← sourceCellComponent? value
        | throwError "a public cell component lost its complete original interface"
      unless retained.cell.entry.id == entry.id && retained.cell.inverse == inverse &&
          retained.receiver == bindings[0]!.expression && retained.cell.constructors.isEmpty do
        throwError "a public cell component changed its actual retained source inputs"
      let some original ← sourceApplication? entry.declaration value
        | throwError "a public cell component lost the actual declaration application"
      unless original.consumeMData.getAppFn.isConstOf entry.declaration do
        throwError "a public cell component substituted another declaration"
      checkWithKernel value
  let failed ← try
    discard <| readCellSource session "inverse_component(«cell.sets.list.unit»(), X, [])"
    pure false
  catch error =>
    unless CasCatalogue.Exception.stratum? error == some .invalid do throw error
    pure true
  unless failed do throwError "a public noninvertible cell acquired an inverse"
  let failed ← try
    discard <| readCellSource session "component(«missing.cell»(), X, [])"
    pure false
  catch error =>
    unless CasCatalogue.Exception.stratum? error == some .invalid do throw error
    pure true
  unless failed do throwError "an unregistered source cell acquired a meaning"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `f (← nativeCellType "CategoryTheory.Arrow (Type)")
  for inverse in #[false, true] do
    let spelling := if inverse then "inverse_component" else "component"
    let component ← readCellSource session
      s!"{spelling}(«cell.sets.list.reverse»(), f, [«ctor.arrow»])"
    let some category := component.category
      | throwError "a constructed component lost its selected target category"
    unless category.expression.syntacticEq
        (.construct ConstructorId.arrow #[.category Foundation.Sets]) do
      throwError "a constructed component changed its original target constructor"
    component.source.withOpen fun bindings value => do
      unless value.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a constructed component replaced its original arrow receiver"
      let .mdata data _ := value
        | throwError "a constructed component lost its exact original constructor path"
      unless data.getString `CasCompiler.source.cell.constructors == "[\"ctor.arrow\"]" &&
          data.getBool `CasCompiler.source.cell.inverse == inverse do
        throwError "a constructed component changed its path or orientation"
      let some retained ← sourceCellComponent? value
        | throwError "a constructed component lost its complete original interface"
      unless retained.cell.constructors == #[ConstructorId.arrow] &&
          retained.receiver == bindings[0]!.expression && retained.cell.isomorphism.isSome do
        throwError "a constructed component replaced its actual constructor, receiver or comparison"
      checkWithKernel value
  let failed ← try
    discard <| readCellSource session "component(«cell.sets.list.join»(), f, [«ctor.arrow»])"
    pure false
  catch error =>
    unless CasCatalogue.Exception.stratum? error == some .invalid do throw error
    pure true
  unless failed do throwError "an isomorphism-only constructor acquired a noninvertible action"

-- The registered ring diamond has nonempty composite routes of different lengths.
-- Mapping it must retain both complete route-expansion comparisons, including all
-- declared constructor composition actions, without identifying the source routes.
run_cmd Lean.Elab.Command.liftTermElabM do
  let #[entry] := (← semanticState).cells.filter (·.id.raw == "cmp.rings.carrier")
    | throwError "the original independent ring comparison is absent"
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let original ← nativeSourceCell entry constant
  let constructed ← original.construct ConstructorId.arrow
  unless constructed.left.actions.size == entry.left.size &&
      constructed.right.actions.size == entry.right.size &&
      constructed.left.actions.size != constructed.right.actions.size do
    throwError "the constructor collapsed two independently declared comparison routes"
  let some constructor := (← semanticState).constructor? ConstructorId.arrow
    | throwError "the original arrow constructor is absent"
  let some composition := constructor.compositionComparison
    | throwError "the original arrow constructor lost its composition comparison"
  unless constructed.transformation.getUsedConstants.contains composition do
    throwError "the constructed ring component omitted its declared route expansions"
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[constructed.sourceBundle]
  withLocalDeclD `f carrier fun receiver => do
    let component ← constructed.component ⟨receiver, none⟩
    unless component.value.containsFVar receiver.fvarId! do
      throwError "the constructed ring component replaced its actual receiver"
    check component.value
