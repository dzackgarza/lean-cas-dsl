module

import CasCompiler.Read
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest

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
    checkSelected term fun expression => do
      let scope ← get
      let bindings ← authoredBindings
      let expected ← expected.source.inContext scope.context
      checkOriginal #[expression, expected, bindings[4]!.expression, bindings[5]!.expression,
          bindings[6]!.expression, bindings[7]!.expression] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a source action changed its actual ring, module or declared action"
        unless native[0]!.containsFVar native[2]!.fvarId! &&
            native[0]!.containsFVar native[3]!.fvarId! &&
            !native[0]!.containsFVar native[4]!.fvarId! &&
            !native[0]!.containsFVar native[5]!.fvarId! do
          throwError "a source action lost its operands or used an unrelated local instance"
        checkWithKernel
          (← mkExpectedTypeHint (← mkEqRefl native[0]!) (← mkEq native[0]! native[1]!))

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
    "TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Modules.Operations.scalarAction S M)) (TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Algebra.NamedRings.ringNumeral S 2)) default, v)")
  for source in #["2 • v", "2 * v", "2 v"] do
    let term ← session.read (← sourceTerm source)
    checkSelected term fun expression => do
      let scope ← get
      let expected ← expected.source.inContext scope.context
      checkOriginal #[expression, expected] fun native => do
        unless native[0]!.containsConst (· == ``CasCatalogue.Modules.Operations.scalarAction) &&
            (← isDefEq native[0]! native[1]!) do
          throwError "source action {source} changed its generic scalar or module role"
        checkWithKernel
          (← mkExpectedTypeHint (← mkEqRefl native[0]!) (← mkEq native[0]! native[1]!))




  for (source, operation) in #[
      ("v · v", "op.monoids.mul"), ("v • v", "op.modules.scalar_action")] do
    let term ← session.read (← sourceTerm source)
    let #[entry] := (← semanticState).operations.filter (·.id.raw == operation)
      | throwError "the explicit operation control lost its independent original row"
    checkSelected term fun expression => do
      let count ← visitNativeData (fun actual => do
        let some selected ← SourceReadM.selection? actual | return false
        return selected.reference.any (·.exactlyMatches (.operation entry))) expression
      unless count > 0 do
        liftM (m := TermElabM) <|
          throwError "the explicit operation control changed its original selected family"
      checkOriginal #[expression] fun native => check native[0]!

  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| session.read (← sourceTerm "v v")
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "juxtaposition selected one of two admitted original operations"
  unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
