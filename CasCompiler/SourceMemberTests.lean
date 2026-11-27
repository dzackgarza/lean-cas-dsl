module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | liftM (m := MetaM) <| throwError "the native member parameter did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | liftM (m := MetaM) <| throwError "the source member did not parse"
  return ⟨parsed⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "CommRingCat.{0}")
  let session ← session.assume `W (← nativeTerm "ModuleCat.{0} R")
  let session ← session.assume `X
    (← nativeTerm "LeanCategories.Modules.Bilinear.Valued.BilinModuleCat R W")
  let ringType ← session.term (← nativeTerm "(R : Type)")
  let valueType ← session.term (← nativeTerm "(W : Type)")
  let category ← session.namedCategory Syntax.missing "Bil" [.zero] #[ringType, valueType]
  let object ← session.term (← nativeTerm "X")
  let object ← object.inCategory category.expression category.value
  let session ← session.defineTerm `A object
  let session ← session.assume `x (← nativeTerm "(A.carrier : Type)")
  let session ← session.assume `y (← nativeTerm "(A.carrier : Type)")
  let functionType ← session.term (← nativeTerm "∀ (_ : A.carrier) (_ : A.carrier), A.carrier")
  let mapCoercion ← session.term (← nativeTerm
    "CoeFun (TypeCat.Hom (A.carrier × A.carrier) W) (fun _ => (A.carrier × A.carrier) → W)")
  let session ← session.assume `unrelatedRing (← nativeTerm "CommRing (R : Type)") .instImplicit
  let session ← session.assumeTerm `unrelatedMapCall mapCoercion .instImplicit
  let result ← session.read (← sourceTerm "A.pairing(x, y)")
  SourceTest.checkSelected result fun value => do
    let bindings ← SourceTest.authoredBindings
    let declaration := ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.pairing
    let family ← mkAppM declaration
      #[bindings[0]!.expression, bindings[1]!.expression, bindings[3]!.expression]
    let pair ← mkAppM ``Prod.mk #[bindings[4]!.expression, bindings[5]!.expression]
    let function ← mkAppM ``TypeCat.Hom.hom #[family]
    let function ← mkAppM ``TypeCat.Fun.toFun #[function]
    let expected := mkApp function pair
    let scope ← get
    let applications ← SourceTest.declaredApplications scope.context scope.selections
      declaration value
    let actual ← applications.anyM fun application => do
      unless application.isAppOfArity declaration 3 do return false
      for index in #[0, 1, 2], binding in #[0, 1, 3] do
        unless ← SourceTest.originatesAt scope.context scope.selections
            application.getAppArgs[index]! bindings[binding]!.expression false do return false
      return true
    unless actual &&
        (← SourceTest.visitNativeData
          (fun expression => pure (expression.equal bindings[6]!.expression)) value false) == 0 &&
        (← SourceTest.visitNativeData
          (fun expression => pure (expression.equal bindings[7]!.expression)) value false) == 0 do
      liftM (m := MetaM) <| throwError "member application changed its original bundled parameters or dictionary"
    SourceTest.checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        liftM (m := MetaM) <| throwError "member application differs from its complete selected source map"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
  let parenthesized ← session.read (← sourceTerm "(A).pairing(x, y)")
  SourceTest.checkSelected parenthesized fun value => do
    let expected ← session.readTerm result
    SourceTest.checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        liftM (m := MetaM) <| throwError "a parenthesized member receiver changed its declared application"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
  let shadowed ← session.assumeTerm `A.pairing functionType
  let localCall ← shadowed.read (← sourceTerm "A.pairing(x, y)")
  SourceTest.checkSelected localCall fun value => do
    let bindings ← SourceTest.authoredBindings
    let expected := mkApp2 bindings[8]!.expression bindings[4]!.expression bindings[5]!.expression
    let native ← SourceTest.selectedValue value
    let scope ← get
    unless ← SourceTest.originatesAt scope.context scope.selections
        native.getAppFn bindings[8]!.expression false do
      liftM (m := MetaM) <| throwError "a member call displaced an exact local callable binding"
    SourceTest.checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        liftM (m := MetaM) <| throwError "a member call displaced an exact local callable binding"
  let session ← session.defineTerm `result result
  let session ← session.assume `A (← nativeTerm "Type")
  let retained ← session.read (← sourceTerm "result")
  SourceTest.checkSelected retained fun value => do
    let bindings ← SourceTest.authoredBindings
    let scope ← get
    unless ← SourceTest.originatesAt scope.context scope.selections
        value bindings[8]!.expression false do
      liftM (m := MetaM) <| throwError "member application was reconstructed after its receiver name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← empty.read (← sourceTerm "Fin(3)")
  let session ← empty.defineTerm `B object
  let rejected ← try
    discard <| session.read (← sourceTerm "B.pairing(0, 0)")
    pure false
  catch error =>
    unless error.toMessageData.hasTag (· == `CasCompiler.SourceReader.memberReceiver) do throw error
    pure true
  unless rejected do liftM (m := MetaM) <| throwError "a member family inferred a structure from an unrelated set"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "CommRingCat.{0}")
  let session ← session.assume `W (← nativeTerm "ModuleCat.{0} R")
  let session ← session.assume `X
    (← nativeTerm "LeanCategories.Modules.Bilinear.Valued.BilinModuleCat R W")
  let session ← session.assume `Y
    (← nativeTerm "LeanCategories.Modules.Bilinear.Valued.BilinModuleCat R W")
  let ringType ← session.term (← nativeTerm "(R : Type)")
  let valueType ← session.term (← nativeTerm "(W : Type)")
  let category ← session.namedCategory Syntax.missing "Bil" [.zero] #[ringType, valueType]
  let first ← session.term (← nativeTerm "X")
  let first ← first.inCategory category.expression category.value
  let session ← session.defineTerm `A first
  let second ← session.term (← nativeTerm "Y")
  let second ← second.inCategory category.expression category.value
  let session ← session.defineTerm `B second
  let session ← session.assume `f (← nativeTerm "A ⟶ B")
  let arrow ← session.term (← nativeTerm "f")
  let arrow ← arrow.inCategory category.expression category.value .morphism
  let session ← session.defineTerm `g arrow
  let session ← session.assume `x (← nativeTerm "A.carrier")
  let expected ← session.term (← nativeTerm
    "LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.underlyingMap g x")
  for source in #["g(x)", "(g)(x)"] do
    let result ← session.read (← sourceTerm source)
    SourceTest.checkSelected result fun value => do
      let bindings ← SourceTest.authoredBindings
      let expected ← expected.source.inContext (← get).context
      unless (← SourceTest.visitNativeData
          (fun expression => pure (expression.equal bindings[7]!.expression)) value false) > 0 &&
          (← SourceTest.visitNativeData
            (fun expression => pure (expression.equal bindings[8]!.expression)) value false) > 0 do
        liftM (m := MetaM) <| throwError "a selected source arrow changed its arbitrary native function or operand"
      SourceTest.checkOriginal #[value, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          liftM (m := MetaM) <| throwError "a selected source arrow changed its arbitrary native function or operand"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
