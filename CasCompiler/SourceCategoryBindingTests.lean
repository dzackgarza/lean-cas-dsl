module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Meta Elab Term CasCompiler

private def readSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the categorical source binding did not parse"
  session.read ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let refined ← readSource empty "Fin(3) in FiniteSets"
  let first ← empty.defineTerm `X refined
  let same ← readSource first "X in FiniteSets"
  unless same.source.expression == mkBVar 0 do
    throwError "source qualification replaced the retained object by its definition"
  let aliased ← first.defineTerm `Y same
  let plain ← readSource aliased "Fin(3)"
  let shadowed ← aliased.defineTerm `X plain
  let retained ← readSource shadowed "Y in FiniteSets"
  unless retained.source.expression == mkBVar 1 do
    throwError "a shadowed source definition changed its earlier selected category"
  let plain ← readSource shadowed "X in Sets"
  unless plain.source.expression == mkBVar 0 do
    throwError "source qualification lost the actual latest lexical binding"
  let failure : Option Exception ← try
    discard <| readSource shadowed "X in Rings"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "qualification changed a retained category without a supplied source action"
  unless (← failure.toMessageData.toString).startsWith
      "the retained source value has a different selected category" do throw failure

private def nativeSource (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native categorical parameter did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let scalars ← empty.assume `R (← nativeSource "RingCat.{0}")
  let module ← readSource scalars "RegularModule(R)"
  let modules ← scalars.defineTerm `M module
  let originalRing ← modules.term (← nativeSource "R")
  let shadowed ← modules.defineTerm `R originalRing
  let retained ← readSource shadowed "(M in Modules)"
  let some category := retained.category
    | throwError "the parameterized source object lost its selected category"
  retained.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    let bundle ← category.bundle.inContext context
    unless value == bindings[1]!.expression &&
        bundle.containsFVar bindings[0]!.expression.fvarId! &&
        !bundle.containsFVar bindings[2]!.expression.fvarId! do
      throwError "a category bundle replaced its original scalar with a shadowing alias"
  let functions ← shadowed.define `f (← nativeSource "fun (N : ModuleCat.{0} R) => N")
  let nested ← readSource functions "f(M in Modules)"
  nested.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[1]!.expression.fvarId! &&
        value.containsFVar bindings[3]!.expression.fvarId! do
      throwError "a qualified dependent argument lost its actual source bindings"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.define `poly (← nativeSource "fun {A : Type} (x : A) => x")
  let retained ← readSource session "poly"
  unless retained.source.expression == mkBVar 0 do
    throwError "reading a callable name specialized its unapplied native family"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for (source, declaration) in #[
      ("ℤ", ``CasCatalogue.Algebra.NamedRings.ringIntegers),
      ("ℚ", ``CasCatalogue.Algebra.NamedRings.ringRationals)] do
    let module ← readSource empty s!"RegularModule({source})"
    let some category := module.category
      | throwError "a declaration-directed parameter lost the module category"
    module.source.withOpen fun _ value => do
      let expected ← mkAppM ``CasCatalogue.Modules.CatalogueRegistration.regularModule
        #[Lean.mkConst declaration]
      unless (← isDefEq value expected) && value.containsConst (· == declaration) do
        throwError "a source parameter changed its independently declared ring"
    category.bundle.withOpen fun _ bundle => do
      unless bundle.containsConst (· == declaration) do
        throwError "a module category lost its actual registered scalar parameter"
    let bound ← empty.defineTerm `M module
    let image ← readSource bound s!"view M along «fun.modules.fibre_inclusion»({source})"
    image.source.withOpen fun bindings value => do
      let functor := mkApp
        (Lean.mkConst ``CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
          [.zero, .zero]) (Lean.mkConst declaration)
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a source view changed its independently typed scalar or actual module"
  let set ← readSource empty "ℚ"
  let bound ← empty.defineTerm `Q set
  for source in #["RegularModule(Q)", "RegularModule(ℚ in Sets)"] do
    let failure : Option Exception ← try
      discard <| readSource bound source
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "a declared parameter type replaced an existing source category"
    unless (← failure.toMessageData.toString).startsWith
        "the source expression does not have its independently declared parameter type" do
      throw failure

private def rejectedQualification (session : SourceSession) (text errorPrefix : String) :
    TermElabM Unit := do
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| readSource session text
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "the explicit qualification incorrectly admitted {text}"
  unless (← failure.toMessageData.toString).startsWith errorPrefix do throw failure

-- The original B0 product is refined as its already selected Sets object. Its retained
-- presentation remains the original Sets cone, including when every factor has a named
-- finite refinement of its own. Later aliases still expose that same cone's defining legs.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for text in #["Fin(2) × ℤ/3", "Fin(2) × Fin(3)"] do
    let original ← readSource empty text
    let qualified ← readSource empty s!"({text}) in FiniteSets"
    let some originalCategory := original.category
      | throwError "the original product lost its selected category"
    let some originalLimit := originalCategory.limit
      | throwError "the original product lost its selected cone"
    let some refinedCategory := qualified.category
      | throwError "the explicitly refined product lost its selected category"
    let some refinedLimit := refinedCategory.limit
      | throwError "the explicit refinement discarded the original product cone"
    unless originalCategory.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets) &&
        refinedCategory.expression.syntacticEq
          (.classifierTotal CasCatalogue.ClassifierId.setsFinite) &&
        originalLimit.row == refinedLimit.row &&
        originalLimit.declaration == refinedLimit.declaration &&
        originalLimit.colimit == refinedLimit.colimit do
      throwError "the explicit refinement selected a different universal presentation"
    qualified.source.withOpen fun bindings _ => do
      let context ← ContextTelescope.capture bindings
      unless (← originalLimit.cone.inContext context) == (← refinedLimit.cone.inContext context) do
        throwError "the whole product qualification changed its actual original cone"
    let bound ← empty.defineTerm `P original
    let some originalEntry := bound.context.entries.back?
      | throwError "the product did not retain its source binding"
    let refined ← readSource bound "P in FiniteSets"
    refined.source.withOpen fun bindings expression => do
      let some base := bindings.find? (·.id == originalEntry.id)
        | throwError "the product's original source binding is absent"
      let constructor ← whnfR expression
      unless constructor.isAppOfArity ``CategoryTheory.ObjectProperty.FullSubcategory.mk 5 &&
          constructor.getAppArgs[3]! == base.expression do
        throwError "the property constructor replaced its actual original product"
    let bound ← bound.defineTerm `K refined
    let bound ← bound.defineTerm `KAgain (← readSource bound "K")
    let retained ← readSource bound "KAgain in FiniteSets"
    unless retained.source.expression == mkBVar 0 do
      throwError "repeating a property qualification replaced its retained alias"
    let originalLeg ← readSource bound "P.leg(0)"
    let refinedLeg ← readSource bound "KAgain.leg(0)"
    unless originalLeg.category.any (fun category => category.role == .morphism &&
        category.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets)) &&
        refinedLeg.category.any (fun category => category.role == .morphism &&
          category.expression.syntacticEq (.atom CasCatalogue.CategoryId.sets)) do
      throwError "a refined product's original leg acquired the refinement category"
    refinedLeg.source.withOpen fun bindings value => do
      let expected ← originalLeg.source.inContext (← ContextTelescope.capture bindings)
      unless ← isDefEq value expected do
        throwError "the aliased refined product replaced its original defining leg"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let .ok question := Parser.runParserCategory (← getEnv) `cas_term
    "|(Fin(2) × ℤ/3) in FiniteSets| = 6"
    | throwError "the original finite-product question did not parse"
  discard <| empty.readQuestion ⟨question⟩
  -- Existing directly qualified source rows remain their actual authored declarations.
  let named ← readSource empty "Fin(3) in FiniteSets"
  unless named.source.expression.containsConst
      (· == ``CasCatalogue.Foundation.FiniteObjects.finiteFin) do
    throwError "generic refinement displaced the explicitly named finite-set row"
  let counted ← readSource empty "ℕ in CountableSets"
  unless counted.category.any (·.expression.syntacticEq
      (.classifierTotal CasCatalogue.ClassifierId.setsCountable)) do
    throwError "the declared countability classifier did not admit its original set"
  let rings ← empty.defineTerm `R (← readSource empty "ZMod(3) in Rings")
  rejectedQualification rings "R in FiniteSets"
    "the explicit refinement has a different selected base category"
  -- Nat already has Encodable data in Lean; this syntax still cannot choose that data.
  rejectedQualification empty "ℕ in EnumeratedSets"
    "explicit refinement requires a proof-only property classifier"

-- A supplied proof instance may refine an arbitrary actual set. Equal-looking lexical
-- aliases retain their own occurrences as the constructor's data, and mere fibre
-- inhabitation cannot authorize a chosen enumeration.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let source ← empty.assume `rawX (← nativeSource "Type")
  let sets ← source.namedCategory Syntax.missing "Sets" [.zero] #[]
  let actual ← source.term (← nativeSource "rawX")
  let actual ← actual.inCategory sets.expression sets.value
  let source ← source.defineTerm `X actual
  rejectedQualification source "X in FiniteSets"
    "not a valid call: the explicit property is not established for the original object"
  let finite ← source.assume `finiteX (← nativeSource "Finite X") .instImplicit
  let same ← readSource finite "X"
  let finite ← finite.defineTerm `XAgain same
  let some first := finite.context.entries.find? (·.userName == `X)
    | throwError "the original abstract set binding is absent"
  let some second := finite.context.entries.find? (·.userName == `XAgain)
    | throwError "the abstract set alias is absent"
  for (name, selected, other) in #[("X", first.id, second.id), ("XAgain", second.id, first.id)] do
    let refined ← readSource finite s!"{name} in FiniteSets"
    refined.source.withOpen fun bindings expression => do
      let some selected := bindings.find? (·.id == selected)
        | throwError "the actual abstract set is outside the original context"
      let some other := bindings.find? (·.id == other)
        | throwError "the other abstract set alias is outside the original context"
      let constructor ← whnfR expression
      unless constructor.isAppOfArity ``CategoryTheory.ObjectProperty.FullSubcategory.mk 5 do
        throwError "the abstract refinement is not the native property constructor"
      let data := constructor.getAppArgs[3]!
      unless data == selected.expression && !data.containsFVar other.expression.fvarId! do
        throwError "proof-only refinement replaced its exact original source occurrence"
  let countable ← source.assume `countableX (← nativeSource "Countable X") .instImplicit
  discard <| readSource countable "X in CountableSets"
  let existence ← countable.assume `enumerationExists (← nativeSource
    "CasCatalogue.Classifier.Holds LeanCategories.Foundation.enumeratedSets X")
  rejectedQualification existence "X in EnumeratedSets"
    "explicit refinement requires a proof-only property classifier"
