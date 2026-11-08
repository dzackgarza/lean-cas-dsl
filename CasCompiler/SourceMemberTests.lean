module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native member parameter did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source member did not parse"
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
  let session ← session.assume `unrelatedRing (← nativeTerm "CommRing (R : Type)") .instImplicit
  let result ← session.read (← sourceTerm "A.pairing(x, y)")
  result.source.withOpen fun bindings value => do
    let declaration := ``CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.pairing
    let family ← mkAppM declaration
      #[bindings[0]!.expression, bindings[1]!.expression, bindings[3]!.expression]
    let pair ← mkAppM ``Prod.mk #[bindings[4]!.expression, bindings[5]!.expression]
    let function ← mkAppM ``TypeCat.Hom.hom #[family]
    let function ← mkAppM ``TypeCat.Fun.toFun #[function]
    let expected := mkApp function pair
    unless ← isDefEq value expected do
      throwError "member application differs from its complete selected source map"
    unless !value.containsFVar bindings[6]!.expression.fvarId! &&
        (value.find? fun expression => expression.isAppOfArity declaration 3 &&
          expression.getAppArgs[0]! == bindings[0]!.expression &&
          expression.getAppArgs[1]! == bindings[1]!.expression &&
          expression.getAppArgs[2]! == bindings[3]!.expression).isSome do
      throwError "member application changed its original bundled parameters or dictionary"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let parenthesized ← session.read (← sourceTerm "(A).pairing(x, y)")
  parenthesized.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    let expected ← result.source.inContext context
    unless ← isDefEq value expected do
      throwError "a parenthesized member receiver changed its declared application"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let shadowed ← session.assumeTerm `A.pairing functionType
  let localCall ← shadowed.read (← sourceTerm "A.pairing(x, y)")
  localCall.source.withOpen fun bindings value => do
    let expected := mkApp2 bindings[7]!.expression bindings[4]!.expression bindings[5]!.expression
    unless value.getAppFn == bindings[7]!.expression && (← isDefEq value expected) do
      throwError "a member call displaced an exact local callable binding"
  let session ← session.defineTerm `result result
  let session ← session.assume `A (← nativeTerm "Type")
  let retained ← session.read (← sourceTerm "result")
  retained.source.withOpen fun bindings value => do
    unless value == bindings[7]!.expression do
      throwError "member application was reconstructed after its receiver name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← empty.read (← sourceTerm "Fin(3)")
  let session ← empty.defineTerm `B object
  let rejected ← try
    discard <| session.read (← sourceTerm "B.pairing(0, 0)")
    pure false
  catch error =>
    let message ← error.toMessageData.toString
    if !message.startsWith "no declared member family accepts this complete selected receiver"
      then throw error
    pure true
  unless rejected do throwError "a member family inferred a structure from an unrelated set"
