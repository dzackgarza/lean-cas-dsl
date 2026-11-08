module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native action parameter did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source action did not parse"
  return ⟨parsed⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let session ← session.assume `V (← nativeTerm "ModuleCat.{0} R")
  let ring ← session.term (← nativeTerm "R")
  let rings ← session.namedCategory Syntax.missing "Rings" [.zero] #[]
  let ring ← ring.inCategory rings.expression rings.value
  let session ← session.defineTerm `S ring
  let scalar ← session.read (← sourceTerm "S")
  let modules ← session.namedCategory Syntax.missing "Modules" [.zero, .zero] #[scalar]
  let moduleObject ← session.term (← nativeTerm "V")
  let moduleObject ← moduleObject.inCategory modules.expression modules.value
  let session ← session.defineTerm `M moduleObject
  let session ← session.assume `r (← nativeTerm "S")
  let session ← session.assume `v (← nativeTerm "M")
  let expected ← session.term (← nativeTerm
    "TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Modules.Operations.scalarAction S M)) (r, v)")
  let mapCoercion ← session.term (← nativeTerm
    "CoeFun (TypeCat.Hom (S × M) M) (fun _ => (S × M) → M)")
  let session ← session.assume `customAction (← nativeTerm "SMul S M") .instImplicit
  let session ← session.assumeTerm `customMapCall mapCoercion .instImplicit
  for source in #["r • v", "r * v", "r v"] do
    let term ← session.read (← sourceTerm source)
    term.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let expected ← expected.source.inContext context
      unless ← isDefEq expression expected do
        throwError "a source action changed its actual ring, module or declared action"
      unless expression.containsFVar bindings[4]!.expression.fvarId! &&
          expression.containsFVar bindings[5]!.expression.fvarId! &&
          !expression.containsFVar bindings[6]!.expression.fvarId! &&
          !expression.containsFVar bindings[7]!.expression.fvarId! do
        throwError "a source action lost its operands or used an unrelated local instance"
      checkWithKernel
        (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let ring ← session.term (← nativeTerm "R")
  let rings ← session.namedCategory Syntax.missing "Rings" [.zero] #[]
  let ring ← ring.inCategory rings.expression rings.value
  let session ← session.defineTerm `S ring
  let moduleObject ← session.read (← sourceTerm "RegularModule(S)")
  let session ← session.defineTerm `M moduleObject
  let session ← session.assume `v (← nativeTerm "M")
  let expected ← session.term (← nativeTerm
    "TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Modules.Operations.scalarAction S M)) ((2 : S), v)")
  for source in #["2 • v", "2 * v", "2 v"] do
    let term ← session.read (← sourceTerm source)
    term.source.withOpen fun bindings expression => do
      let context ← ContextTelescope.capture bindings
      let expected ← expected.source.inContext context
      unless expression.containsConst (· == ``CasCatalogue.Modules.Operations.scalarAction) &&
          (← isDefEq expression expected) do
        throwError "a source action identified scalar and module roles from their coincident carriers"
      checkWithKernel
        (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
