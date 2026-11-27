module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the construction source did not parse"
  return ⟨source⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← `(Nat))
  let object ← session.read (← sourceTerm "Fin(n)")
  let session ← session.defineTerm `X object
  let session ← session.assume `unused (← `(Nat))
  let some category := object.category
    | throwError "the actual finite family has no selected source category"
  for (name, declaration) in #[
      ("Aut", ``CasCatalogue.Algebra.Automorphisms.automorphismsConstruction),
      ("End", ``CasCatalogue.Algebra.Automorphisms.endomorphismsConstruction)] do
    for text in #[s!"{name}(X)", s!"view X along {name}()"] do
      let result ← session.read (← sourceTerm text)
      let some selected := result.category
        | throwError "the construction lost its complete target category"
      unless selected.role == .object do
        throwError "the construction result changed its native object role"
      checkSelected result fun value => do
        let scope ← get
        let bindings ← authoredBindings
        let context := scope.context
        let bundle ← category.bundle.inContext context
        let functor ← mkAppM declaration #[bundle]
        let input ← mkAppM ``CategoryTheory.Core.mk #[bindings[1]!.expression]
        let (_, target) ← functorCategoryBundles functor
        let expected ← functorObject functor input target
        unless bindings.size == 3 do
          throwError "the construction changed its original authored context"
        checkOriginal #[value, expected] fun native => do
          unless ← isDefEq native[0]! native[1]! do
            throwError "the construction changed its actual source category or receiver"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
            (← mkEq native[0]! native[1]!))

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok source := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native construction input did not parse"
  return ⟨source⟩

private def expectRefusal (message : String) (action : TermElabM SourceTerm) : TermElabM Unit := do
  let refused ← try
    discard action
    pure false
  catch error =>
    if ((← error.toMessageData.toString).splitOn message).length > 1 then pure true
    else throw error
  unless refused do throwError "the source accepted an incompatible construction input"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `G (← nativeTerm "GrpCat.{0}")
  let category ← session.namedCategory Syntax.missing "Groups" [.zero] #[]
  let object ← session.term (← nativeTerm "G")
  let object ← object.inCategory category.expression category.value
  let session ← session.defineTerm `X object
  let result ← session.read (← sourceTerm "Aut(X)")
  checkSelected result fun value => do
    let scope ← get
    let bindings ← authoredBindings
    let bundle ← category.value.source.inContext scope.context
    let functor ← mkAppM ``CasCatalogue.Algebra.Automorphisms.automorphismsConstruction #[bundle]
    let input ← mkAppM ``CategoryTheory.Core.mk #[bindings[1]!.expression]
    let (_, target) ← functorCategoryBundles functor
    let expected ← functorObject functor input target
    checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "Aut used a carrier category instead of the original group category"
  let session ← session.defineTerm `answer result
  let session ← session.assume `X (← `(Type))
  let retained ← session.read (← sourceTerm "answer")
  checkSelected retained fun value => do
    let bindings ← authoredBindings
    unless value == bindings[2]!.expression do
      throwError "the constructed object was replayed after receiver shadowing"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← `(Type))
  let session ← session.assume `Y (← `(Type))
  let session ← session.assume `iso (← nativeTerm "X ≅ Y")
  let sets ← session.namedCategory Syntax.missing "Sets" [.zero] #[]
  let core ← session.unaryCategory Syntax.missing ConstructorId.core sets
  let arrow ← session.term (← nativeTerm
    "CategoryTheory.CoreHom.mk (X := CategoryTheory.Core.mk X) (Y := CategoryTheory.Core.mk Y) iso")
  let arrow ← arrow.inCategory core.expression core.value .morphism
  let session ← session.defineTerm `e arrow
  let result ← session.read (← sourceTerm "map e along Aut()")
  unless result.category.any (·.role == .morphism) do
    throwError "the construction map changed its morphism role"
  checkSelected result fun value => do
    let scope ← get
    let bindings ← authoredBindings
    let bundle ← sets.value.source.inContext scope.context
    let functor ← mkAppM ``CasCatalogue.Algebra.Automorphisms.automorphismsConstruction #[bundle]
    let expected ← mkAppM ``CategoryTheory.Functor.map #[functor, bindings[3]!.expression]
    checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "the construction map changed its retained complete core morphism"
  let session ← session.assume `f (← nativeTerm "X ⟶ Y")
  let arrow ← session.term (← nativeTerm "f")
  let arrow ← arrow.inCategory sets.expression sets.value .morphism
  let session ← session.defineTerm `plain arrow
  expectRefusal "different complete selected source category"
    (session.read (← sourceTerm "map plain along Aut()"))

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let sets ← empty.namedCategory Syntax.missing "Sets" [.zero] #[]
  let functor ← empty.term (← nativeTerm
    "CasCatalogue.Foundation.CatalogueRegistration.setsIdentity.{0}.toFunctor")
  let session ← empty.defineTerm `U functor
  let session ← session.assume `P (← nativeTerm
    "CasCatalogue.Algebra.Automorphisms.Registration.pointedSetsCategory.{0}")
  let category ← session.constant Syntax.missing
    ``CasCatalogue.Algebra.Automorphisms.Registration.pointedSetsCategory [.zero]
  let object ← session.term (← nativeTerm "P")
  let object ← object.inCategory CasCatalogue.Algebra.Automorphisms.Registration.PointedSets category
  let session ← session.defineTerm `point object
  let result ← session.read (← sourceTerm "Stab(U, point)")
  checkSelected result fun value => do
    let scope ← get
    let bindings ← authoredBindings
    let bundle ← sets.value.source.inContext scope.context
    let functor ← mkAppM ``CasCatalogue.Algebra.Automorphisms.stabilizersConstruction
      #[bundle, bindings[0]!.expression]
    let input ← mkAppM ``CategoryTheory.Core.mk #[bindings[2]!.expression]
    let (_, target) ← functorCategoryBundles functor
    let expected ← functorObject functor input target
    checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "the parameterized construction changed its actual functor or pointed object"
    let #[applied] ← declaredApplications scope.context scope.selections
        ``CasCatalogue.Algebra.Automorphisms.stabilizersConstruction value
      | throwError "the construction lost its one complete original functor application"
    unless applied.isAppOfArity ``CasCatalogue.Algebra.Automorphisms.stabilizersConstruction 2 &&
        (← originatesAt scope.context scope.selections applied.getAppArgs[1]!
          bindings[0]!.expression) do
      throwError "the construction did not retain its exact supplied functor argument"
  expectRefusal "requires its actual declaration parameter"
    (session.read (← sourceTerm "Stab(point)"))
