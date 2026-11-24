module

import CasCompiler.Read
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source did not parse"
  return ⟨source⟩

/- `span` names a registered morphism of sets and a registered object of module subobjects.
Of the two, only the morphism accepts a finite set of vectors of ℚ³ (the object needs a module
whose carrier the argument does not determine), so `span({u₁, u₂})` reads as that morphism
(tests/acceptance/linear_algebra.cas). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let space ← empty.read (← sourceTerm "ℚ³")
  let session ← empty.defineTerm `u₁ (← empty.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let session ← session.defineTerm `u₂ (← session.read (← sourceTerm "(0, 1, 1)") (some space.source))
  let span ← session.read (← sourceTerm "span({u₁, u₂})")
  span.source.withOpen fun _ value => do
    unless ((← instantiateMVars value).find?
        (·.isConstOf ``CasCatalogue.Algebra.LinearAlgebra.span)).isSome do
      throwError "the span is not the registered span of sets: {value}"

/- The span is a subset of the same set of vectors of ℚ³, so a tuple of numerals is read in it
as its elements are: `(1, 1, 2) ∈ span({u₁, u₂})` (tests/acceptance/linear_algebra.cas). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let space ← empty.read (← sourceTerm "ℚ³")
  let session ← empty.defineTerm `u₁ (← empty.read (← sourceTerm "(1, 0, 1)") (some space.source))
  let session ← session.defineTerm `u₂ (← session.read (← sourceTerm "(0, 1, 1)") (some space.source))
  discard <| session.read (← sourceTerm "(1, 1, 2) ∈ span({u₁, u₂})")

/- The native application helper distinguishes equal-arity declarations by their complete
argument types. These are ordinary native declarations, not downstream catalogue rows.
The public source-reader controls above still exercise the independently owned span. -/
open CategoryTheory

def nativeTrialObject (n : Nat) (_ : Nat) : Type := Fin n

def nativeTrialMap (_ _ : Fin 2) : Fin 2 ⟶ Fin 2 :=
  TypeCat.ofHom fun value => value

private def nativeTrialSession : TermElabM SourceSession := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assumeTerm `n (← empty.read (← sourceTerm "ℕ"))
  session.assumeTerm `i (← session.read (← sourceTerm "Fin(2)"))

private def nativeTrialFailure (read : TermElabM α) : TermElabM Exception := withoutModifyingState do
  let result ← try
      discard <| read
      pure none
    catch error => pure (some error)
  let some error := result | throwError "the negative native applicability control succeeded"
  return error

run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← nativeTrialSession
  session.context.withOpen fun bindings => do
    let natural := bindings[0]!.expression
    let finite := bindings[1]!.expression
    for (declaration, arguments, applicable) in
        #[(``nativeTrialObject, #[natural, natural], true),
          (``nativeTrialMap, #[finite, finite], true),
          (``nativeTrialObject, #[finite, finite], false),
          (``nativeTrialMap, #[natural, natural], false)] do
      let result ← withoutModifyingState do
        elabSourceApplicationApplicable (← mkConstWithFreshMVarLevels declaration)
          (Array.replicate arguments.size Syntax.missing) none fun index _ => do
            let some value := arguments[index]?
              | throwError "the native applicability control lost an actual argument"
            return .ok value
      match result with
      | .ok (value, actual) =>
        unless applicable && actual == arguments &&
            value.consumeMData.getAppFn.isConstOf declaration do
          throwError "the native applicability helper changed or accepted incompatible arguments"
      | .error _ =>
        if applicable then throwError "the native applicability helper rejected its actual domain"

/- Controlled dispatcher coverage: both independently registered span rows receive complete
native operands through the ReadContext callback, and each distinct operand choice is checked first.
This is not a public-source ambiguity fixture: genuine public ambiguity remains covered by
SourceDivisionTests and SourceViewTests without changing their original inputs. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let field ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.Fields.rationals)) none
  let ring ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.NamedRings.ringRationals)) none
  let moduleObject ← elabTermAndSynthesize (← `(ModuleCat.of ℚ (Fin 2 → ℚ))) none
  let subset ← elabTermAndSynthesize (← `((∅ : Set (Fin 2 → ℚ)))) none
  let operands := #[#[field, ring], #[mkNatLit 2, moduleObject], #[subset]]
  let source ← sourceTerm "span(0, 1, 2)"
  let `(cas_term| $name:ident($arguments:cas_term,*)) := source
    | throwError "the controlled span lost its original application syntax"
  let reads ← liftM (m := IO) <| IO.mkRef (#[] : Array Nat)
  let contextFor : Array (Array Expr) → ReadContext := fun operands =>
    ⟨(fun _ => pure none), source, none, none, none,
      readProjection, fun _ argument expected _ _ => do
        let some expected := expected
          | throwError "the controlled span operand lost its declared parameter type"
        let `(cas_term| $index:num) := argument
          | throwError "the controlled span lost an operand position"
        reads.modify (·.push index.getNat)
        let some choices := operands[index.getNat]?
          | throwError "the controlled span requested an absent operand"
        let matching ← choices.filterM fun value => do
          withoutModifyingState <| isDefEq (← inferType value) expected
        if matching.isEmpty then
          return .error m!"the supplied operand has another native type"
        let #[value] := matching
          | throwError "the controlled span requires one supplied operand at its native type"
        unless ← isDefEq (← inferType value) expected do
          throwError "the controlled span changed its original native parameter"
        return .ok ⟨value, none⟩⟩
  let context := contextFor operands
  let candidates ← selectNamed "span" none none
  unless candidates.size == 2 do
    throwError "the controlled span requires its two independently registered source kinds"
  for candidate in candidates do
    let .registered entry _ := candidate
      | throwError "the controlled span acquired a different registered kind"
    let (declaration, selectedOperands) : Name × Array (Array Expr) := match entry with
      | .inl entry => (entry.declaration, #[#[ring], #[moduleObject], #[subset]])
      | .inr entry => (entry.declaration, #[#[field], #[mkNatLit 2], #[subset]])
    withoutModifyingState do
      reads.set #[]
      let value ← SourceReader.registered (contextFor selectedOperands)
        name arguments.getElems
      let value ← instantiateMVars value.value
      unless value.containsConst (· == declaration) &&
          !value.hasMVar && !value.hasLevelMVar do
        throwError "a controlled span candidate did not retain its actual native declaration"
      check value
      -- Only the accepted row reaches its final original operand. Retaining its
      -- native state must not elaborate that successful source occurrence again.
      unless ((← reads.get).filter (· == 2)).size == 1 do
        throwError "the selected named reading replayed its original source operand"
  let ambiguous ← nativeTrialFailure <|
    SourceReader.registered context name arguments.getElems
  unless CasCatalogue.Exception.isSemanticAmbiguity ambiguous do
    throwError "two applicable native candidates were not retained as an ambiguity"
  let mismatchContext : ReadContext := { context with
    read := fun _ _ _ _ _ => pure (.error m!"controlled native parameter mismatch") }
  let inapplicable ← nativeTrialFailure <|
    SourceReader.registered mismatchContext name arguments.getElems
  unless CasCatalogue.Exception.stratum? inapplicable == some .invalid &&
      !CasCatalogue.Exception.isSemanticAmbiguity inapplicable do
    throwError "zero applicable native candidates did not preserve invalid source"

/- Recursive operand failures belong to the matched source expression, not to candidate
applicability. This includes the original unknown-name stratum and internal exceptions. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← nativeTrialSession
  for source in #["span(unregistered_native_trial_operand)",
      "span(span(unregistered_native_trial_operand))"] do
    let missing ← nativeTrialFailure <| session.read (← sourceTerm source)
    unless CasCatalogue.Exception.stratum? missing == some .invalid &&
        CasCatalogue.Exception.isUnknownSourceName missing "unregistered_native_trial_operand" do
      throwError "the named trial replaced its operand's original unknown-name failure"
  let original ← nativeTrialFailure <| session.read
    (← sourceTerm "id(Fin(2), Fin(3))")
  let nested ← nativeTrialFailure <| session.read
    (← sourceTerm "span(id(Fin(2), Fin(3)))")
  unless (← original.toMessageData.toString) == (← nested.toMessageData.toString) do
    throwError "the native trial replaced a matched operand's original construction failure"

run_cmd Lean.Elab.Command.liftTermElabM do
  let nativeTrialInternal ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.nativeTrialInternal
  let source ← sourceTerm "span(Fin(2))"
  let `(cas_term| $name:ident($arguments:cas_term,*)) := source
    | throwError "the native trial control lost its source application"
  let context : ReadContext := ⟨(fun _ => pure none), source, none, none, none,
    readProjection, fun _ _ _ _ _ => throw (Exception.internal nativeTrialInternal)⟩
  let internal ← nativeTrialFailure <|
    SourceReader.registered context name arguments.getElems
  match internal with
  | .internal id _ =>
    unless id == nativeTrialInternal do
      throwError "the native trial changed the original internal exception"
  | _ => throwError "the native trial swallowed a matched operand's internal exception"
