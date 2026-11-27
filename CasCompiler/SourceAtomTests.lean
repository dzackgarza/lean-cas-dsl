module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Algebra.Calculus
import LeanCategories.Catalogue.Semantics.Algebra.Fields
import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Algebra.Calculus
meta import LeanCategories.Catalogue.Semantics.Algebra.Fields
meta import LeanCategories.Catalogue.Semantics.Algebra.Semirings

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let cases : Array (String × String × Option String) := #[
    ("ℕ", "ℕ", none), ("ℤ", "ℤ", none), ("ℚ", "ℚ", none),
    ("ℝ", "ℝ", none), ("ℂ", "ℂ", none), ("ℕ⁺", "ℕ⁺", none),
    ("ℙ", "ℙ", none), ("C^∞", "C^∞", none), ("«C^∞»", "C^∞", none),
    ("ℤ in Rings", "ℤ", some "Rings"), ("ℚ in Fields", "ℚ", some "Fields"),
    ("((ℤ)) in Rings", "ℤ", some "Rings"),
    ("(Fin(3)) in FiniteSets", "Fin", some "FiniteSets")]
  for (text, name, qualification) in cases do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "a registered source atom did not parse"
    let (entry, selected) ← selectObject name qualification
    let term ← session.read ⟨stx⟩
    checkSelected term fun value => do
      let some selection ← SourceReadM.selection? value
        | liftM (m := TermElabM) <| throwError "a registered source object lost its selected reference"
      let some reference := selection.reference
        | liftM (m := TermElabM) <| throwError "a registered source object lost its complete registry row"
      unless reference.exactlyMatches (.named (.registered (.inl entry) selected)) do
        liftM (m := TermElabM) <| throwError "a registered source object changed its exact selected reference"
      let some application := selection.originalApplication
        | liftM (m := TermElabM) <| throwError "an atomic source lost its complete original application"
      unless application.getAppFn.constName? == some entry.declaration do
        liftM (m := TermElabM) <| throwError "an atomic source changed its independently registered declaration"
    let some category := term.category
      | throwError "an atomic source lost its selected category bundle"
    unless category.expression.syntacticEq selected.expression do
      throwError "an atomic source changed its selected category"
    checkSelected term fun _ => do
      let scope ← get
      let bundle ← category.bundle.inContext scope.context
      checkOriginal #[bundle] fun native => do
        unless native[0]!.getAppFn.constName? == some selected.declaration do
          throwError "an atomic source reconstructed a different native category bundle"
    let bound ← session.defineTerm `X term
    let .ok retainedSyntax := Parser.runParserCategory (← getEnv) `cas_term "X"
      | throwError "the source reference alias did not parse"
    let retained ← bound.read ⟨retainedSyntax⟩
    let some originalAlias := bound.context.entries.find? (·.userName == `X)
      | throwError "the source reference alias lost its original declaration"
    checkSelected retained fun value => do
      let scope ← get
      let some original := scope.context.bindings.find? (·.id == originalAlias.id)
        | liftM (m := TermElabM) <| throwError "the source reference alias lost its exact native binding"
      let some (originalEntry, originalCategory) ←
          sourceObjectSelection? scope.context scope.selections value
        | liftM (m := TermElabM) <| throwError "a native source alias lost its original object reference"
      unless (SelectedSourceReference.named (.registered (.inl originalEntry) originalCategory)).exactlyMatches
          (.named (.registered (.inl entry) selected)) && value == original.expression do
        liftM (m := TermElabM) <| throwError "a native source alias changed its selected object or binding"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  for (text, native) in #[
      ("Fin₂₃", ← `(CasCatalogue.Foundation.Objects.fin 23)),
      ("Fin₀", ← `(CasCatalogue.Foundation.Objects.fin 0)),
      ("Fin₂ in FiniteSets", ← `(CasCatalogue.Foundation.FiniteObjects.finiteFin 2))] do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the subscripted object did not parse"
    let value ← session.read ⟨source⟩
    let expected ← session.term native
    checkSelected value fun expression => do
      let expected ← expected.source.inContext (← get).context
      checkOriginal #[expression, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a subscripted object changed its actual declaration or leading parameter"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!) (← mkEq native[0]! native[1]!))
  let session ← session.assume `Fin₂₃ (← `(Nat → Type))
  let session ← session.assume `n (← `(Nat))
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term "Fin₂₃(n)"
    | throwError "the local subscripted callable did not parse"
  let value ← session.read ⟨source⟩
  checkSelected value fun expression => do
    let scope ← get
    let #[function, argument] ← authoredBindings
      | liftM (m := TermElabM) <| throwError "the local callable control lost its original authored binders"
    unless expression == mkApp function.expression argument.expression do
      liftM (m := TermElabM) <| throwError "a subscripted spelling replaced its exact local callable binding"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← `(Nat))
  for (text, declaration) in #[
      ("FinOrder(n)", ``CasCatalogue.Foundation.FiniteOrders.ordinary),
      ("ReverseFinOrder(n)", ``CasCatalogue.Foundation.FiniteOrders.reverse)] do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the explicitly named structure did not parse"
    let result ← session.read ⟨source⟩
    let some category := result.category
      | throwError "the explicitly named structure lost its selected category"
    unless category.expression.syntacticEq (.atom CategoryId.linearOrders) do
      throwError "the explicitly named structure changed its registered category"
    checkSelected result fun value => do
      let scope ← get
      let #[parameter] ← authoredBindings
        | liftM (m := TermElabM) <| throwError "the named structure lost its original authored parameter"
      let expected ← mkAppM declaration #[parameter.expression]
      checkOriginal #[value, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "the explicit structure name changed its original dependent declaration"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!) (← mkEq native[0]! native[1]!))
