module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Algebra.Fields
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Algebra.Fields
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native inherited point control did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the inherited source point did not parse"
  return ⟨parsed⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "CommRingCat.{0}")
  let object ← session.term (← nativeTerm "R")
  let category ← session.namedCategory Syntax.missing "CommutativeRings" [.zero] #[]
  let object ← object.inCategory category.expression category.value
  let session ← session.defineTerm `S object
  let type ← session.term (← nativeTerm "(S : Type)")
  let expected ← session.term (← nativeTerm
    "TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Algebra.NamedRings.ringNumeral (CasCatalogue.Algebra.Algebras.commutativeRingsRings.toFunctor.obj S) 4)) default")
  let session ← session.assume `unrelatedNumeral (← nativeTerm "OfNat (S : Type) 4") .instImplicit
  let point ← session.read (← sourceTerm "4") (some type.source)
  point.source.withOpen fun bindings expression => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    unless expression.containsFVar bindings[1]!.expression.fvarId! &&
        !expression.containsFVar bindings[2]!.expression.fvarId! &&
        (← isDefEq expression expected) do
      throwError "the inherited numeral changed its selected scalar or declared point map"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
