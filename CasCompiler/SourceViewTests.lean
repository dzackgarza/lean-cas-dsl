module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.SourceConstrainedPoint
import CasCompiler.SourceAdmission
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.Fields
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.SourceConstrainedPoint
meta import CasCompiler.SourceAdmission
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.Fields
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def readSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | liftM (m := MetaM) <| throwError "the explicit source view did not parse"
  session.read ⟨stx⟩

private def nativeSource (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | liftM (m := MetaM) <| throwError "the native view parameter did not parse"
  return ⟨stx⟩

private def reference (term : SourceTerm) (expected : SelectedSourceReference) :
    TermElabM Unit :=
  SourceTest.checkSelected term fun value => do
    let some selected ← SourceReadM.selection? value
      | liftM (m := MetaM) <| throwError "the source view lost its selected reference"
    let references := selected.reference.toArray ++ selected.observation.toArray ++
      (selected.application.toArray.flatMap fun application => match application.family with
        | .objectAction family => family.references
        | .point family => family.references
        | _ => #[])
    unless references.any (fun actual =>
        SourceSelection.exactlyMatches Expr.equal
          { value, reference := some actual } { value, reference := some expected }) do
      liftM (m := MetaM) <| throwError "the source view changed its selected reference or declaration"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← readSource empty "Fin(3)"
  let session ← empty.defineTerm `X object
  let some entry := (← semanticState).functor? FunctorId.setsList
    | liftM (m := MetaM) <| throwError "the actual list functor is absent from the source"
  unless !entry.structural do liftM (m := MetaM) <| throwError "the source list functor changed its declared role"
  for text in #["view X along «fun.sets.list»", "view X along «fun.sets.list»()"] do
    let image ← readSource session text
    reference image (.functor entry)
    let some category := image.category
      | liftM (m := MetaM) <| throwError "the source image lost its complete target category"
    unless category.expression.syntacticEq entry.target do
      liftM (m := MetaM) <| throwError "the source image changed its declared target"
    SourceTest.checkSelected image fun value => do
      let bindings ← SourceTest.authoredBindings
      let functor := Lean.mkConst entry.declaration [.zero]
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) && (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) do
        liftM (m := MetaM) <| throwError "the explicit view changed its actual declared action or retained object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let scalars ← empty.assume `R (← nativeSource "RingCat.{0}")
  let module ← readSource scalars "RegularModule(R)"
  let modules ← scalars.defineTerm `M module
  let image ← readSource modules "view M along «fun.modules.fibre_inclusion»(R)"
  let some entry := (← semanticState).functor? FunctorId.modulesFibreInclusion
    | liftM (m := MetaM) <| throwError "the source fibre inclusion is absent"
  reference image (.functor entry)
  SourceTest.checkSelected image fun value => do
    let bindings ← SourceTest.authoredBindings
    let functor := mkApp (Lean.mkConst entry.declaration [.zero, .zero]) bindings[0]!.expression
    let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
    let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[1]!.expression]
    unless (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) && ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[1]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "the source view lost its chosen scalar or actual module"
  let bound ← modules.defineTerm `A image
  let ring ← bound.term (← nativeSource "R")
  let shadowed ← bound.defineTerm `R ring
  let underlying ← readSource shadowed "view A along «fun.modules.underlying»()"
  let some forget := (← semanticState).functor? FunctorId.modulesUnderlying
    | liftM (m := MetaM) <| throwError "the source underlying-set functor is absent"
  reference underlying (.functor forget)
  SourceTest.checkSelected underlying fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[2]!.expression)) value false) > 0) &&
        !((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[3]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "a later view replaced its retained object after scalar shadowing"
  let unrelated ← shadowed.assume `S (← nativeSource "RingCat.{0}")
  let failure : Option Exception ← try
    discard <| readSource unrelated "view M along «fun.modules.fibre_inclusion»(S)"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "a source view accepted an unrelated scalar at its complete native boundary"
  unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReader.actionNativeSource) do throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for (receiver, id) in #[
      ("Fin(3) in FiniteSets", ClassifierId.setsFinite),
      ("ℚ in Fields", ClassifierId.commutativeRingsField)] do
    let object ← readSource empty receiver
    let session ← empty.defineTerm `X object
    let image ← readSource session s!"view X along «{id.raw}»()"
    let some entry := (← semanticState).classifier? id
      | liftM (m := MetaM) <| throwError "the selected source classifier is absent"
    reference image (.classifierForget entry)
    let some category := image.category
      | liftM (m := MetaM) <| throwError "the classifier view lost its actual target category"
    unless category.expression.syntacticEq entry.host do
      liftM (m := MetaM) <| throwError "the classifier view changed its independently declared host"
    SourceTest.checkSelected image fun value => do
      let bindings ← SourceTest.authoredBindings
      let functor ← classifierForgetInstance entry
      let context := (← get).context
      let some source := object.category
        | liftM (m := MetaM) <| throwError "the classifier input lost its selected source category"
      let (domain, _) ← functorCategoryBundles functor
      unless ← isDefEq domain (← source.bundle.inContext context) do
        liftM (m := MetaM) <| throwError "the independent classifier projection has a different source bundle"
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) && (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) do
        liftM (m := MetaM) <| throwError "the classifier view changed its actual declared projection or bound object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `X (← nativeSource "Type")
  let image ← readSource parameters "view X along «fun.sets.list»"
  let some entry := (← semanticState).functor? FunctorId.setsList
    | liftM (m := MetaM) <| throwError "the explicitly selected source context is absent"
  reference image (.functor entry)
  SourceTest.checkSelected image fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "the explicit source context replaced its actual formal object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let functions ← domains.assume `f (← nativeSource "TypeCat.Hom A B")
  let image ← readSource functions "map f along «fun.sets.list»()"
  let some entry := (← semanticState).functor? FunctorId.setsList
    | liftM (m := MetaM) <| throwError "the actual map action is absent from the source"
  reference image (.functor entry)
  let some category := image.category
    | liftM (m := MetaM) <| throwError "the source map action lost its selected target category"
  unless category.role == .morphism && category.expression.syntacticEq entry.target do
    liftM (m := MetaM) <| throwError "the source map action changed its categorical role or target"
  SourceTest.checkSelected image fun value => do
    let bindings ← SourceTest.authoredBindings
    let expected ← mkAppM ``CategoryTheory.Functor.map
      #[Lean.mkConst entry.declaration [.zero], bindings[2]!.expression]
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[2]!.expression)) value false) > 0) && (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) do
      liftM (m := MetaM) <| throwError "the source map action changed the actual declared functor or input arrow"
  let bound ← functions.defineTerm `mapped image
  let repeated ← readSource bound "map mapped along «fun.sets.list»()"
  SourceTest.checkSelected repeated fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[3]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "successive map action replaced the actual bound arrow"
  let failure : Option Exception ← try
    discard <| readSource bound "view mapped along «fun.sets.list»()"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "an object action accepted a source arrow"
  unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReader.actionRole) do throw failure
  let arguments ← bound.assume `xs (← nativeSource "List A")
  let applied ← readSource arguments "mapped(xs)"
  SourceTest.checkSelected applied fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[3]!.expression)) value false) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[4]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "a mapped callable lost its actual binding or later argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.assume `R (← nativeSource "CommRingCat.{0}")
  let rings ← rings.assume `S (← nativeSource "CommRingCat.{0}")
  let arrows ← rings.assume `f (← nativeSource "CommRingCat.Hom R S")
  let image ← readSource arrows "map f along «fun.commutative_rings.ring»()"
  let bound ← arrows.defineTerm `q image
  let some selected := image.category
    | liftM (m := MetaM) <| throwError "the mapped ring arrow lost its selected category"
  unless selected.role == .morphism do
    liftM (m := MetaM) <| throwError "the mapped ring arrow lost its morphism role"
  let failure : Option Exception ← try
    discard <| readSource bound "map q along «fun.commutative_rings.ring»()"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "a mapped arrow changed its selected source category"
  unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReader.actionSymbolicSource) do
    throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let domains ← domains.assume `C (← nativeSource "Type")
  let arrows ← domains.assume `f (← nativeSource "TypeCat.Hom A B")
  let arrows ← arrows.assume `g (← nativeSource "TypeCat.Hom B C")
  let f ← readSource arrows "map f along «fun.sets.list»()"
  let bound ← arrows.defineTerm `fL f
  let g ← readSource bound "map g along «fun.sets.list»()"
  let bound ← bound.defineTerm `gL g
  let composite ← readSource bound "gL ∘ fL"
  let some category := composite.category
    | liftM (m := MetaM) <| throwError "source composition lost its selected category"
  unless category.role == .morphism do
    liftM (m := MetaM) <| throwError "source composition lost its morphism role"
  SourceTest.checkSelected composite fun value => do
    let bindings ← SourceTest.authoredBindings
    let expected ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[bindings[5]!.expression, bindings[6]!.expression]
    unless (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) && ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[5]!.expression)) value false) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[6]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "source composition changed its actual arrow occurrences or order"
  let rejected ← try
    discard <| readSource bound "fL ∘ gL"
    pure false
  catch _ => pure true
  unless rejected do liftM (m := MetaM) <| throwError "source composition accepted different middle objects"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.assume `R (← nativeSource "CommRingCat.{0}")
  let coefficients ← readSource rings "integerCoefficients(R)"
  let #[entry] := (← semanticState).morphisms.filter (·.name == "integerCoefficients")
    | liftM (m := MetaM) <| throwError "the actual named morphism reference is not unique"
  let #[owner] := (← semanticState).categories.filter (·.id == entry.category)
    | liftM (m := MetaM) <| throwError "a named morphism lost its selected source reference"
  reference coefficients (.named (.registered (.inr entry) owner))
  let some category := coefficients.category
    | liftM (m := MetaM) <| throwError "the named morphism lost its selected category"
  unless category.role == .morphism do
    liftM (m := MetaM) <| throwError "the named morphism lost its categorical role"
  SourceTest.checkSelected coefficients fun value => do
    let bindings ← SourceTest.authoredBindings
    let expected ← mkAppM ``CasCatalogue.Algebra.NamedCommutativeRings.integerCoefficients
      #[bindings[0]!.expression]
    unless (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) && ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "the named morphism changed its registered declaration or actual ring"
  let bound ← rings.defineTerm `q coefficients
  let mapped ← readSource bound "map q along «fun.commutative_rings.ring»()"
  SourceTest.checkSelected mapped fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[1]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "a named morphism was replayed during a later functor action"
  let dimensions ← empty.assume `n (← nativeSource "Nat")
  let reversal ← readSource dimensions "rev(n)"
  let some category := reversal.category
    | liftM (m := MetaM) <| throwError "a parameterized named morphism lost its category"
  unless category.role == .morphism do
    liftM (m := MetaM) <| throwError "a parameterized named morphism lost its categorical role"
  SourceTest.checkSelected reversal fun value => do
    let bindings ← SourceTest.authoredBindings
    let expected ← mkAppM ``CasCatalogue.Foundation.Morphisms.finRev
      #[bindings[0]!.expression]
    unless (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) do
      liftM (m := MetaM) <| throwError "a parameterized named morphism changed its declared action"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let point ← readSource empty "rev(3,2)"
  SourceTest.checkSelected point fun value => do
    unless (← SourceTest.visitNativeData (fun expression =>
        pure (expression.isConstOf ``CasCatalogue.Foundation.Morphisms.finPoint)) value) > 0 do
      liftM (m := MetaM) <| throwError "a source point numeral omitted its independent declared point"
  let #[entry] := (← semanticState).numerals.filter
      (·.declaration == ``CasCatalogue.Foundation.Morphisms.finPoint)
    | liftM (m := MetaM) <| throwError "the actual point numeral reference is not unique"
  SourceTest.checkSelected point fun value => do
    let selected ← SourceTest.visitNativeData (fun expression => do
      let some selected ← SourceReadM.selection? expression | return false
      return selected.reference.any fun actual =>
        SourceSelection.exactlyMatches Expr.equal
          { value := expression, reference := some actual }
          { value := expression, reference := some (.numeral entry) }) value
    unless selected > 0 do
      liftM (m := MetaM) <| throwError "a source point numeral lost its exact selected reference"
  let rejected ← try
    discard <| readSource empty "rev(3,3)"
    pure false
  catch _ => pure true
  unless rejected do liftM (m := MetaM) <| throwError "a source point numeral bypassed its declared domain obligation"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for domain in #["Int", "CasCatalogue.Foundation.Objects.integers",
      "CasCatalogue.Foundation.Objects.integersMod 3", "Rat",
      "CasCatalogue.Algebra.NamedRings.rationals"] do
    let functions ← empty.define `f (← nativeSource s!"fun (x : {domain}) => x")
    let value ← readSource functions "f(3)"
    SourceTest.checkSelected value fun expression => do
      unless (← SourceTest.visitNativeData (fun value =>
          pure (value.isConstOf ``CasCatalogue.Algebra.NamedRings.ringNumeral)) expression) > 0 &&
          (← SourceTest.visitNativeData (fun value =>
            pure (value.isConstOf ``CasCatalogue.Foundation.Morphisms.finPoint)) expression) == 0 do
        liftM (m := MetaM) <| throwError "a source numeral changed its actual registered scalar refinement"
  let scalars ← readSource empty "ℚ in Rings"
  let rings ← empty.defineTerm `R scalars
  let functions ← rings.define `f (← nativeSource
    "fun (x : CasCatalogue.Algebra.NamedRings.underlying R) => x")
  let value ← readSource functions "f(3)"
  SourceTest.checkSelected value fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.NamedRings.ringNumeral)) value) > 0) do
      liftM (m := MetaM) <| throwError "a source numeral replaced the actual selected scalar object"
  let dictionaries ← empty.assume `customRationalNumeral
    (← nativeSource "OfNat Rat 3") .instImplicit
  let functions ← dictionaries.define `f (← nativeSource "fun (x : Rat) => x")
  let value ← readSource functions "f(3)"
  SourceTest.checkSelected value fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.NamedRings.ringNumeral)) value) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.NamedRings.ringRationals)) value) > 0) &&
        !((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "a source rational point changed its declared ring or used a host numeral instance"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let instances ← empty.assume `customNumeral
    (← nativeSource "OfNat (CasCatalogue.Foundation.Objects.fin 3) 2") .instImplicit
  let value ← readSource instances "rev(3,2)"
  SourceTest.checkSelected value fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Foundation.Morphisms.finPoint)) value) > 0) &&
        !((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "a host numeral instance changed the independent source point"
  let dimensions ← empty.assume `n (← nativeSource "Nat")
  let hypotheses ← dimensions.assume `h (← nativeSource "2 < n")
  let functions ← hypotheses.define `f
    (← nativeSource "fun (x : CasCatalogue.Foundation.Objects.fin n) => x")
  let value ← readSource functions "f(2 in Fin(n) using (proof(h)))"
  SourceTest.checkSelected value fun value => do
    let bindings ← SourceTest.authoredBindings
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[1]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "a source point lost its actual dimension or formal domain premise"
  for source in #[
      "f(2 in Fin(n) using (proof(True.intro)))",
      "f(2 in Fin(n) using (proof(h), proof(h)))",
      "f(2 in Fin(n) using (h))"] do
    let rejected ← try
      discard <| readSource functions source
      pure false
    catch _ => pure true
    unless rejected do liftM (m := MetaM) <| throwError "source point evidence bypassed its declared proof boundary"
  let modular ← empty.define `f
    (← nativeSource "fun (x : CasCatalogue.Foundation.Objects.integersMod 3) => x")
  let rejected ← try
    discard <| readSource modular "f(2 in Fin(3) using (proof(by decide)))"
    pure false
  catch _ => pure true
  unless rejected do liftM (m := MetaM) <| throwError "explicit point evidence changed the consuming source domain"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let scalars ← readSource empty "ZMod(3) in Rings"
  let rings ← empty.defineTerm `R scalars
  let functions ← rings.define `f (← nativeSource
    "fun (x : CasCatalogue.Foundation.Objects.fin (let chosen := R; 3)) => x")
  let rejected ← try
    discard <| readSource functions "f(3)"
    pure false
  catch _ => pure true
  unless rejected do
    liftM (m := MetaM) <| throwError "a scalar in a dimension expression replaced the selected finite domain"




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | liftM (m := MetaM) <| throwError "the structural view control did not parse"
    session.read ⟨stx⟩
  let units ← read "(Sym(3) in Groups)ˣ"
  SourceTest.checkSelected units fun expression => do
    unless (← SourceTest.visitNativeData (fun value =>
        pure (value.isConstOf ``CasCatalogue.Algebra.Ports.groupsMonoid)) expression) > 0 do
      liftM (m := MetaM) <| throwError "a group was not viewed along its structural monoid route"
  let rejected ← try
    discard <| read "(Mat₂(ℚ) in Rings)ˣ"
    pure false
  catch error => pure (CasCatalogue.Exception.isSemanticAmbiguity error)
  unless rejected do liftM (m := MetaM) <| throwError "competing structural views were read without a selection"




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let expected ← elabTermAndSynthesize (← `(
    CasCatalogue.Algebra.Ports.ringsMultiplicative.toFunctor.obj
      CasCatalogue.Algebra.NamedRings.ringRationals)) none
  for text in #["ℚˣ", "(ℚ)ˣ"] do
    let units ← readSource empty text
    SourceTest.checkSelected units fun expression => do
      let (original, _) ← registeredSourceDomain expression
      unless original.isAppOfArity ``CasCatalogue.Algebra.Units.units 1 do
        liftM (m := MetaM) <| throwError "the bare units source lost its declared object and parameter"
      let parameter := original.getAppArgs[0]!
      unless (← (← get).context.withOriginalSources #[parameter, expected] fun originals => isDefEq originals[0]! originals[1]!) && ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.Ports.ringsMultiplicative)) parameter) > 0) do
        liftM (m := MetaM) <| throwError "the bare units source changed its complete declared monoid"
      unless ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.NamedRings.ringRationalsIdentification)) parameter) > 0) do
        liftM (m := MetaM) <| throwError "the bare units source erased its named base identification"
  let rationals ← readSource empty "ℚ"
  let bound ← empty.defineTerm `Q rationals
  for text in #["Qˣ", "(ℚ in Sets)ˣ"] do
    let failure : Option Exception ← try
      discard <| readSource bound text
      pure none
    catch error => pure (some error)
    let some failure := failure
      | liftM (m := MetaM) <| throwError "parameter reading acquired a new refinement of an already selected source"
    unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReader.declaredParameterType) do
      throw failure




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for (text, admission) in #[
      ("(t ↦ t) in C", "obj.sets.continuous_maps"),
      ("[1,2;3,4] in (view (Mat₂(ℚ) in Rings) along «fun.rings.multiplicative_monoid»())ˣ",
        "obj.sets.units")] do
    let admitted ← readSource empty text
    SourceTest.checkSelected admitted fun expression => do
      let reference ← SourceTest.visitNativeData (fun value => do
        let some selected ← SourceReadM.selection? value | return false
        return selected.admission.any (·.entry.id.raw == admission)) expression
      unless reference > 0 do
        liftM (m := MetaM) <| throwError "the typed admission lost its independently registered constructor"
  let sine ← readSource empty "sin"
  let functions ← empty.defineTerm `f sine
  let admitted ← readSource functions "f in C"
  SourceTest.checkSelected admitted fun expression => do
    let bindings ← SourceTest.authoredBindings
    unless bindings.size == 1 && ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) expression false) > 0) do
      liftM (m := MetaM) <| throwError "function admission replaced the original selected map"
  let finiteIdentity ← readSource empty "id(Fin(2))"
  let finiteFunctions ← empty.defineTerm `f finiteIdentity
  let failure : Option Exception ← try
    discard <| readSource finiteFunctions "f in C"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "function admission changed the selected map's actual endpoints"
  unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReader.declaredParameterType) do
    throw failure



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let domains ← domains.assume `C (← nativeSource "Type")
  let functions ← domains.assume `rawF (← nativeSource "A → B")
  let functions ← functions.assume `rawG (← nativeSource "B → C")


  let first ← readSource functions "(x ↦ rawF(x)) in (A → B)"
  let arrows ← functions.defineTerm `f first
  let second ← readSource arrows "(x ↦ rawG(x)) in (B → C)"
  let arrows ← arrows.defineTerm `g second
  let supplied ← readSource arrows "f"
  let arrows ← arrows.defineTerm `fAgain supplied
  for text in #["f", "g", "fAgain"] do
    let selected ← readSource arrows text
    unless selected.category.any (·.role == .morphism) do
      liftM (m := MetaM) <| throwError "the public source fixture did not select its native map category"
  let retained := fun (session : SourceSession) (bindings : Array LocalBinding)
      (name : Name) => (do
    let some entry := session.context.entries.find? (·.userName == name)
      | liftM (m := MetaM) <| throwError "the generalized application fixture lost its named source entry"
    let some binding := bindings.find? (·.id == entry.id)
      | liftM (m := MetaM) <| throwError "the generalized application fixture lost its exact source binding"
    pure binding.expression : MetaM Expr)
  for (text, native, used, unused) in #[
      ("g(f)", "CategoryTheory.CategoryStruct.comp f g", `f, `fAgain),
      ("g(fAgain)", "CategoryTheory.CategoryStruct.comp fAgain g", `fAgain, `f)] do
    let composed ← readSource arrows text
    let expected ← arrows.term (← nativeSource native)
    let some category := composed.category
      | liftM (m := MetaM) <| throwError "generalized application lost its morphism category"
    unless category.role == .morphism &&
        category.expression.syntacticEq (.atom CategoryId.sets) do
      liftM (m := MetaM) <| throwError "generalized application changed its complete source role"
    SourceTest.checkSelected composed fun value => do
      let bindings ← SourceTest.authoredBindings
      let expected ← expected.source.inContext (← get).context
      let original ← retained arrows bindings used
      let other ← retained arrows bindings unused
      let later ← retained arrows bindings `g
      unless (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) && ((← SourceTest.visitNativeData (fun expression => pure (expression == mkFVar original.fvarId!)) value false) > 0) &&
          ((← SourceTest.visitNativeData (fun expression => pure (expression == mkFVar later.fvarId!)) value false) > 0) && !((← SourceTest.visitNativeData (fun expression => pure (expression == mkFVar other.fvarId!)) value false) > 0) do
        liftM (m := MetaM) <| throwError "generalized application substituted an equal native arrow binding"
  let failure : Option Exception ← try
    discard <| readSource arrows "f(g)"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "generalized application ignored the actual intermediate native object"
  unless (← failure.toMessageData.toString).startsWith
      "Application type mismatch: The " do
    throw failure
  let nested ← arrows.assume `rawH (← nativeSource "B → B")
  let middle ← readSource nested "(x ↦ rawH(x)) in (B → B)"
  let nested ← nested.defineTerm `h middle
  let composed ← readSource nested "g(h(f))"
  let expected ← nested.term (← nativeSource
    "CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp f h) g")
  SourceTest.checkSelected composed fun value => do
    let bindings ← SourceTest.authoredBindings
    let expected ← expected.source.inContext (← get).context
    unless ← (← get).context.withOriginalSources #[value, expected] (fun originals => isDefEq originals[0]! originals[1]!) do
      liftM (m := MetaM) <| throwError "nested generalized application changed its complete native composite"
    for name in #[`f, `g, `h] do
      unless ((← SourceTest.visitNativeData (fun expression => do pure (expression.equal (← retained nested bindings name))) value false) > 0) do
        liftM (m := MetaM) <| throwError "nested generalized application lost an original complete map"
  let failure : Option Exception ← try
    discard <| readSource nested "g(h(g))"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | liftM (m := MetaM) <| throwError "nested generalized application changed its actual intermediate object"
  unless (← failure.toMessageData.toString).startsWith
      "Application type mismatch: The " do
    throw failure
  let consumers ← arrows.assume `rawConsumeMap
    (← nativeSource "TypeCat.Hom A B → C")
  let consumers ← consumers.assume `rawConsumeFunction
    (← nativeSource "(A → B) → C")
  let consumers ← consumers.define `nativeFunctions (← nativeSource "A → B")
  let mapConsumer ← readSource consumers "(m ↦ rawConsumeMap(m)) in ((A → B) → C)"
  let consumers ← consumers.defineTerm `consumeMap mapConsumer
  let functionConsumer ← readSource consumers
    "(m ↦ rawConsumeFunction(m)) in (nativeFunctions → C)"
  let consumers ← consumers.defineTerm `consumeFunction functionConsumer
  for (text, native) in #[
      ("consumeMap(f)", "consumeMap.hom.toFun f"),
      ("consumeFunction(f)", "consumeFunction.hom.toFun f.hom.toFun")] do
    let applied ← readSource consumers text
    let expected ← consumers.term (← nativeSource native)
    SourceTest.checkSelected applied fun value => do
      let bindings ← SourceTest.authoredBindings
      let expected ← expected.source.inContext (← get).context
      unless (← (← get).context.withOriginalSources #[value, expected] fun originals => isDefEq originals[0]! originals[1]!) &&
          ((← SourceTest.visitNativeData (fun expression => do pure (expression.equal (← retained consumers bindings `f))) value false) > 0) do
        liftM (m := MetaM) <| throwError "a map-valued native parameter was changed into generalized composition"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let direct ← empty.assume `n (← nativeSource "Nat")
  let direct ← direct.assume `k (← nativeSource "Nat")
  let direct ← direct.assume `h (← nativeSource "k < n")
  let point ← withCurrHeartbeats <| readSource direct "k in Fin(n) using (proof(h))"
  let original ← direct.term (← nativeSource "(⟨k, h⟩ : Fin n)")
  SourceTest.checkSelected point fun value => do
    let bindings ← SourceTest.authoredBindings
    let original ← original.source.inContext (← get).context
    unless ← (← get).context.withOriginalSources #[value, original] (fun originals => isDefEq originals[0]! originals[1]!) do
      liftM (m := MetaM) <| throwError "the direct constrained datum changed its original native constructor"
    for index in [0:3] do
      unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[index]!.expression)) value false) > 0) do
        liftM (m := MetaM) <| throwError "the direct constrained datum lost an original parameter or proof"
  let generalized ← empty.assume `D (← nativeSource "Type")
  let generalized ← generalized.assume `n (← nativeSource "Nat")
  let generalized ← generalized.assume `rawF (← nativeSource "D → Nat")
  let generalized ← generalized.assume `h (← nativeSource "∀ d, rawF d < n")
  let mapped ← withCurrHeartbeats <| readSource generalized "rawF in Fin(n) using (proof(h))"
  unless mapped.category.any (·.role == .morphism) do
    liftM (m := MetaM) <| throwError "the generalized constrained datum lost its selected native map role"
  let original ← generalized.term (← nativeSource
    "TypeCat.ofHom (fun d : D => (⟨rawF d, h d⟩ : Fin n))")
  SourceTest.checkSelected mapped fun value => do
    let bindings ← SourceTest.authoredBindings
    let original ← original.source.inContext (← get).context
    unless ← (← get).context.withOriginalSources #[value, original] (fun originals => isDefEq originals[0]! originals[1]!) do
      liftM (m := MetaM) <| throwError "the generalized constrained datum changed its original native map"
    for index in [0:4] do
      unless ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[index]!.expression)) value false) > 0) do
        liftM (m := MetaM) <| throwError "the generalized constrained datum lost an original domain, map or proof"

private def originalReaderFailure {α : Type} (action : TermElabM α) :
    TermElabM Exception := do
  let failure : Option Exception ← try
    discard <| withCurrHeartbeats <| withoutModifyingState action
    pure none
  catch failure => pure (some failure)
  let some failure := failure | liftM (m := MetaM) <| throwError "the negative reader control unexpectedly succeeded"
  pure failure



run_cmd Lean.Elab.Command.liftTermElabM do
  let originalDataFailure ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.originalConstrainedDataFailure
  let target := mkApp (mkConst ``Fin) (mkNatLit 3)
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let mapCalls ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let unexpectedMap : SourceReadM NativeSourceJudgement := do
    liftM (m := IO) <| mapCalls.modify (· + 1)
    liftM (m := MetaM) <| throwError "the failed direct datum was retried as a map"
  let validProof ← nativeSource "by decide"
  let failedData : Expr → SourceReadM (Except MessageData Expr) := fun _ =>
    throw (Exception.internal originalDataFailure)
  let failure ← originalReaderFailure <| empty.elaborateJudgementsScoped Syntax.missing do
    return #[← sourceConstrainedPointApplicable target #[validProof] failedData unexpectedMap]
  match failure with
  | .internal id _ =>
    unless id == originalDataFailure do
      liftM (m := MetaM) <| throwError "the constrained datum changed its original internal exception"
  | _ => liftM (m := MetaM) <| throwError "the constrained datum replaced its reader's original internal exception"
  unless (← mapCalls.get) == 0 do
    liftM (m := MetaM) <| throwError "the failed constrained datum invoked another interpretation"
  let wrongProof ← nativeSource "True.intro"
  discard <| originalReaderFailure <| empty.elaborateJudgementsScoped Syntax.missing do
    return #[← sourceConstrainedPointApplicable target #[wrongProof]
      (fun _ => pure (.ok (mkNatLit 0))) unexpectedMap]
  unless (← mapCalls.get) == 0 do
    liftM (m := MetaM) <| throwError "a failed constrained proof invoked another interpretation"

private def nativeBinderArgument (value expected : Expr) :
    SourceReadM (Except MessageData Expr) := do
  unless ← liftM (m := MetaM) <| isDefEq (← inferType value) expected do
    return .error "the test argument has another native type"
  return .ok value



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let integral ← withCurrHeartbeats <| readSource empty "∫_{0}^{1} t dt"
  SourceTest.checkSelected integral fun value => do
    check value
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.Calculus.integral)) value) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.Calculus.admitContinuous)) value) > 0) do
      liftM (m := MetaM) <| throwError "a binder returned its point argument instead of the original admitted operation"
  let functions ← empty.define `g
    (← nativeSource "fun n : Nat => ((1 : Real) / 2) ^ n")
  let selected ← withCurrHeartbeats <| readSource functions "∑_{n ∈ ℕ} g(n)"
  SourceTest.checkSelected selected fun value => do
    let bindings ← SourceTest.authoredBindings
    check value
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.Series.realSeriesSum)) value) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf ``CasCatalogue.Algebra.Series.admit)) value) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression.equal bindings[0]!.expression)) value false) > 0) do
      liftM (m := MetaM) <| throwError "the selected binder changed its original operation, family or map admission"
    let reference ← SourceTest.visitNativeData (fun expression => do
      let some selected ← SourceReadM.selection? expression | return false
      return selected.reference.any fun
        | .binder entry => entry.id.raw == "bind.sets.real_series"
        | _ => false) value
    unless reference > 0 do
      liftM (m := MetaM) <| throwError "the selected binder lost its original registered row"



run_cmd Lean.Elab.Command.liftTermElabM do
  let originalDataFailure ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.originalBinderDataFailure
  unless ((← semanticState).binders.filter (·.token == "∑")).size > 1 do
    liftM (m := MetaM) <| throwError "the binder failure control requires the original overloaded family"
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let missing ← originalReaderFailure <|
    readSource empty "∑_{n ∈ ℕ} unregistered_binder_body"
  unless CasCatalogue.Exception.stratum? missing == some .invalid &&
      CasCatalogue.Exception.isUnknownSourceName missing "unregistered_binder_body" do
    liftM (m := MetaM) <| throwError "the binder replaced its body's original unknown-name failure"
  let index := nativeBinderArgument (mkConst ``Nat)
  let failedBody : Expr → SourceReadM Expr := fun _ =>
    throw (Exception.internal originalDataFailure)
  let bodyFailure ← originalReaderFailure <| empty.elaborateScoped Syntax.missing <| sourceBinder "∑" #[index] `n failedBody
  match bodyFailure with
  | .internal id _ =>
    unless id == originalDataFailure do
      liftM (m := MetaM) <| throwError "the binder changed its original body exception"
  | _ => liftM (m := MetaM) <| throwError "the binder swallowed its original body exception"
  let failedArgument : Expr → SourceReadM (Except MessageData Expr) := fun _ =>
    throw (Exception.internal originalDataFailure)
  let argumentFailure ← originalReaderFailure <| empty.elaborateScoped Syntax.missing <|
    sourceBinder "∑" #[failedArgument] `n failedBody
  match argumentFailure with
  | .internal id _ =>
    unless id == originalDataFailure do
      liftM (m := MetaM) <| throwError "the binder changed its original argument exception"
  | _ => liftM (m := MetaM) <| throwError "the binder swallowed its original argument exception"
  let mismatch : Expr → SourceReadM (Except MessageData Expr) := fun _ =>
    pure (.error "the supplied argument has another native type")
  let absent ← originalReaderFailure <| empty.elaborateScoped Syntax.missing <| sourceBinder "∑" #[mismatch] `n failedBody
  unless CasCatalogue.Exception.stratum? absent == some .invalid &&
      !CasCatalogue.Exception.isSemanticAmbiguity absent do
    liftM (m := MetaM) <| throwError "zero applicable binder rows were reported as ambiguity"
  let family ← elabTermAndSynthesize (← nativeSource "fun _ : Nat => (1 : Real)") none
  let bodies ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let admissionFailure ← originalReaderFailure <| empty.elaborateScoped Syntax.missing <| sourceBinder "∑" #[index] `n fun n => do
    liftM (m := IO) <| bodies.modify (· + 1)
    pure (mkApp family n)
  unless (← bodies.get) == 1 &&
      CasCatalogue.Exception.stratum? admissionFailure == some .invalid do
    liftM (m := MetaM) <| throwError "a selected binder admission failure retried another body interpretation"




run_cmd Lean.Elab.Command.liftTermElabM do
  let rows := (← semanticState).binders.filter (·.token == "∑")
  unless rows.size > 1 do liftM (m := MetaM) <| throwError "the binder retention control requires the actual overloads"
  let some selectedIndex := rows.findIdx? (·.id.raw == "bind.sets.real_series")
    | liftM (m := MetaM) <| throwError "the binder retention control lost the original real-series row"
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeSource "Nat")
  let hypotheses ← parameters.assume `h (← nativeSource "n = n")
  let session ← hypotheses.define `g
    (← nativeSource "fun n : Nat => ((1 : Real) / 2) ^ n")
  let identity ← elabTermAndSynthesize (← nativeSource "fun x : Real => x") none
  let identityType ← inferType identity
  let argumentReads ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let declarations ← liftM (m := IO) <| IO.mkRef (#[] : Array (Nat × Name))
  let index : Expr → SourceReadM (Except MessageData Expr) := fun expected => do
    liftM (m := IO) <| argumentReads.modify (· + 1)
    nativeBinderArgument (mkConst ``Nat) expected
  let retained ← withCurrHeartbeats <| session.elaborateScoped Syntax.missing do
    let bindings ← SourceTest.authoredBindings
    let #[outer, _, family] := bindings
      | liftM (m := MetaM) <| throwError "the binder retention control changed its original source scope"
    let value ← sourceBinder "∑" #[index] `n fun parameter => do
      unless parameter.isFVar && parameter.fvarId! != outer.expression.fvarId! do
        liftM (m := MetaM) <| throwError "the bound variable replaced an earlier same-named source parameter"
      let ordinal ← liftM (m := IO) argumentReads.get
      let name ← liftM (m := TermElabM) <| mkAuxDeclName (.num `binderBodyOccurrence ordinal)
      liftM (m := TermElabM) <| addDecl (.defnDecl {
        name := name
        levelParams := []
        type := identityType
        value := identity
        hints := .abbrev
        safety := .safe })



      liftM (m := TermElabM) <| setReducibilityStatus name .reducible
      liftM (m := IO) <| declarations.modify (·.push (ordinal, name))
      pure (mkApp (mkConst name) (mkApp family.expression parameter))
    unless (← liftM (m := IO) argumentReads.get) == rows.size do
      liftM (m := MetaM) <| throwError "binder selection replayed an original argument or bound body"
    let created ← liftM (m := IO) declarations.get
    let some (_, selectedName) := created.find? (·.1 == selectedIndex + 1)
      | liftM (m := MetaM) <| throwError "the original selected binder body was not retained"
    unless ((← SourceTest.visitNativeData (fun expression => pure (expression.isConstOf selectedName)) value) > 0) &&
        ((← SourceTest.visitNativeData (fun expression => pure (expression == mkFVar family.expression.fvarId!)) value false) > 0) &&
        !((← SourceTest.visitNativeData (fun expression => pure (expression == mkFVar outer.expression.fvarId!)) value false) > 0) do
      liftM (m := MetaM) <| throwError "binder selection replaced its checked body or captured source occurrence"
    let environment := (← liftM (m := MetaM) getEnv).setExporting false
    for (ordinal, name) in created do
      unless environment.contains name == (ordinal == selectedIndex + 1) do
        liftM (m := MetaM) <| throwError "binder selection lost the selected native state or kept a rejected state"
    check value
    return value
  SourceTest.checkSelected retained fun value => do
    let scope ← get
    let original ← ContextTelescope.capture
      (scope.context.bindings.take session.context.entries.size)
    unless original.telescope.exactlyMatches session.context do
      liftM (m := MetaM) <| throwError "binder selection shortened its complete context or changed stable binding identities"
    let before ← SourceTest.authoredEntries session.context session.selections
    let after ← SourceTest.authoredEntries retained.source.context retained.selections
    unless before.map (·.id) == after.map (·.id) do
      liftM (m := MetaM) <| throwError "binder selection changed its complete original authored telescope"
    checkWithKernel value



run_cmd Lean.Elab.Command.liftTermElabM do
  let originalFailure ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.originalBinderStateFailure
  let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let failure : Option Exception ← try
    discard <| withCurrHeartbeats <| empty.elaborateScoped Syntax.missing <| sourceBinder "∑"
      #[nativeBinderArgument (mkConst ``Nat)] `n fun _ => do
        let name ← liftM (m := TermElabM) <| mkAuxDeclName `failedBinderBody
        liftM (m := TermElabM) <| addDecl (.defnDecl {
          name := name
          levelParams := []
          type := Lean.mkConst ``Nat
          value := mkNatLit 1
          hints := .abbrev
          safety := .safe })
        liftM (m := IO) <| introduced.set (some name)
        throw (Exception.internal originalFailure)
    pure none
  catch error => pure (some error)
  let some (.internal actual _) := failure
    | liftM (m := MetaM) <| throwError "a binder state failure lost its original native exception"
  unless actual == originalFailure do
    liftM (m := MetaM) <| throwError "a binder state failure was replaced by another exception"
  let some name ← introduced.get
    | liftM (m := MetaM) <| throwError "the binder state control never reached its original body"
  unless !((← getEnv).setExporting false).contains name do
    liftM (m := MetaM) <| throwError "a failed binder row left its speculative native declaration behind"
