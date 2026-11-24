module

import CasCompiler.Read
import CasCompiler.SourceConstrainedPoint
import CasCompiler.SourceAdmission
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.Fields
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
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
    | throwError "the explicit source view did not parse"
  session.read ⟨stx⟩

private def nativeSource (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native view parameter did not parse"
  return ⟨stx⟩

private def reference (term : SourceTerm) (kind : Name) (id : String)
    (declaration : Name) : MetaM Unit := do
  let .mdata data _ := term.source.expression
    | throwError "the source view lost its selected reference"
  unless data.getName `CasCompiler.source.kind == kind &&
      data.getString `CasCompiler.source.id == id &&
      data.getName `CasCompiler.source.declaration == declaration do
    throwError "the source view changed its selected reference or declaration"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← readSource empty "Fin(3)"
  let session ← empty.defineTerm `X object
  let some entry := (← semanticState).functor? FunctorId.setsList
    | throwError "the actual list functor is absent from the source"
  unless !entry.structural do throwError "the source list functor changed its declared role"
  for text in #["view X along «fun.sets.list»", "view X along «fun.sets.list»()"] do
    let image ← readSource session text
    reference image ``EdgeRef.functor entry.id.raw entry.declaration
    let some category := image.category
      | throwError "the source image lost its complete target category"
    unless category.expression.syntacticEq entry.target do
      throwError "the source image changed its declared target"
    image.source.withOpen fun bindings value => do
      let functor := Lean.mkConst entry.declaration [.zero]
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless value.containsFVar bindings[0]!.expression.fvarId! && (← isDefEq value expected) do
        throwError "the explicit view changed its actual declared action or retained object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let scalars ← empty.assume `R (← nativeSource "RingCat.{0}")
  let module ← readSource scalars "RegularModule(R)"
  let modules ← scalars.defineTerm `M module
  let image ← readSource modules "view M along «fun.modules.fibre_inclusion»(R)"
  let some entry := (← semanticState).functor? FunctorId.modulesFibreInclusion
    | throwError "the source fibre inclusion is absent"
  reference image ``EdgeRef.functor entry.id.raw entry.declaration
  image.source.withOpen fun bindings value => do
    let functor := mkApp (Lean.mkConst entry.declaration [.zero, .zero]) bindings[0]!.expression
    let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
    let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[1]!.expression]
    unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! &&
        value.containsFVar bindings[1]!.expression.fvarId! do
      throwError "the source view lost its chosen scalar or actual module"
  let bound ← modules.defineTerm `A image
  let ring ← bound.term (← nativeSource "R")
  let shadowed ← bound.defineTerm `R ring
  let underlying ← readSource shadowed "view A along «fun.modules.underlying»()"
  let some forget := (← semanticState).functor? FunctorId.modulesUnderlying
    | throwError "the source underlying-set functor is absent"
  reference underlying ``EdgeRef.functor forget.id.raw forget.declaration
  underlying.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[2]!.expression.fvarId! &&
        !value.containsFVar bindings[3]!.expression.fvarId! do
      throwError "a later view replaced its retained object after scalar shadowing"
  let unrelated ← shadowed.assume `S (← nativeSource "RingCat.{0}")
  let failure : Option Exception ← try
    discard <| readSource unrelated "view M along «fun.modules.fibre_inclusion»(S)"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a source view accepted an unrelated scalar at its complete native boundary"
  unless (← failure.toMessageData.toString).startsWith
      "the selected source action has a different complete native source category" do throw failure

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
      | throwError "the selected source classifier is absent"
    reference image ``EdgeRef.classifierForget entry.id.raw entry.declaration
    let some category := image.category
      | throwError "the classifier view lost its actual target category"
    unless category.expression.syntacticEq entry.host do
      throwError "the classifier view changed its independently declared host"
    image.source.withOpen fun bindings value => do
      let functor ← classifierForgetInstance entry
      let context ← ContextTelescope.capture bindings
      let some source := object.category
        | throwError "the classifier input lost its selected source category"
      let (domain, _) ← functorCategoryBundles functor
      unless ← isDefEq domain (← source.bundle.inContext context) do
        throwError "the independent classifier projection has a different source bundle"
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let expected ← mkAppM ``Prefunctor.obj #[prefunctor, bindings[0]!.expression]
      unless value.containsFVar bindings[0]!.expression.fvarId! && (← isDefEq value expected) do
        throwError "the classifier view changed its actual declared projection or bound object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `X (← nativeSource "Type")
  let image ← readSource parameters "view X along «fun.sets.list»"
  let some entry := (← semanticState).functor? FunctorId.setsList
    | throwError "the explicitly selected source context is absent"
  reference image ``EdgeRef.functor entry.id.raw entry.declaration
  image.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "the explicit source context replaced its actual formal object"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let functions ← domains.assume `f (← nativeSource "TypeCat.Hom A B")
  let image ← readSource functions "map f along «fun.sets.list»()"
  let some entry := (← semanticState).functor? FunctorId.setsList
    | throwError "the actual map action is absent from the source"
  reference image ``EdgeRef.functor entry.id.raw entry.declaration
  let some category := image.category
    | throwError "the source map action lost its selected target category"
  unless category.role == .morphism && category.expression.syntacticEq entry.target do
    throwError "the source map action changed its categorical role or target"
  image.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CategoryTheory.Functor.map
      #[Lean.mkConst entry.declaration [.zero], bindings[2]!.expression]
    unless value.containsFVar bindings[2]!.expression.fvarId! && (← isDefEq value expected) do
      throwError "the source map action changed the actual declared functor or input arrow"
  let bound ← functions.defineTerm `mapped image
  let repeated ← readSource bound "map mapped along «fun.sets.list»()"
  repeated.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[3]!.expression.fvarId! do
      throwError "successive map action replaced the actual bound arrow"
  let failure : Option Exception ← try
    discard <| readSource bound "view mapped along «fun.sets.list»()"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "an object action accepted a source arrow"
  unless (← failure.toMessageData.toString).startsWith
      "the source functor action has a different object or morphism role" do throw failure
  let arguments ← bound.assume `xs (← nativeSource "List A")
  let applied ← readSource arguments "mapped(xs)"
  applied.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[3]!.expression.fvarId! &&
        value.containsFVar bindings[4]!.expression.fvarId! do
      throwError "a mapped callable lost its actual binding or later argument"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.assume `R (← nativeSource "CommRingCat.{0}")
  let rings ← rings.assume `S (← nativeSource "CommRingCat.{0}")
  let arrows ← rings.assume `f (← nativeSource "CommRingCat.Hom R S")
  let image ← readSource arrows "map f along «fun.commutative_rings.ring»()"
  let bound ← arrows.defineTerm `q image
  let some selected := image.category
    | throwError "the mapped ring arrow lost its selected category"
  unless selected.role == .morphism do
    throwError "the mapped ring arrow lost its morphism role"
  let failure : Option Exception ← try
    discard <| readSource bound "map q along «fun.commutative_rings.ring»()"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a mapped arrow changed its selected source category"
  unless (← failure.toMessageData.toString).startsWith
      "the selected source action has a different complete symbolic source category" do
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
    | throwError "source composition lost its selected category"
  unless category.role == .morphism do
    throwError "source composition lost its morphism role"
  composite.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CategoryTheory.CategoryStruct.comp
      #[bindings[5]!.expression, bindings[6]!.expression]
    unless (← isDefEq value expected) && value.containsFVar bindings[5]!.expression.fvarId! &&
        value.containsFVar bindings[6]!.expression.fvarId! do
      throwError "source composition changed its actual arrow occurrences or order"
  let rejected ← try
    discard <| readSource bound "fL ∘ gL"
    pure false
  catch _ => pure true
  unless rejected do throwError "source composition accepted different middle objects"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.assume `R (← nativeSource "CommRingCat.{0}")
  let coefficients ← readSource rings "integerCoefficients(R)"
  let #[entry] := (← semanticState).morphisms.filter (·.name == "integerCoefficients")
    | throwError "the actual named morphism reference is not unique"
  let .mdata data _ := coefficients.source.expression
    | throwError "a named morphism lost its selected source reference"
  unless data.getName `CasCompiler.source.kind == ``MorphismEntry &&
      data.getString `CasCompiler.source.id == entry.id.raw &&
      data.getName `CasCompiler.source.declaration == entry.declaration do
    throwError "a named morphism changed its exact selected source reference"
  let some category := coefficients.category
    | throwError "the named morphism lost its selected category"
  unless category.role == .morphism do
    throwError "the named morphism lost its categorical role"
  coefficients.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CasCatalogue.Algebra.NamedCommutativeRings.integerCoefficients
      #[bindings[0]!.expression]
    unless (← isDefEq value expected) && value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "the named morphism changed its registered declaration or actual ring"
  let bound ← rings.defineTerm `q coefficients
  let mapped ← readSource bound "map q along «fun.commutative_rings.ring»()"
  mapped.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[1]!.expression.fvarId! do
      throwError "a named morphism was replayed during a later functor action"
  let dimensions ← empty.assume `n (← nativeSource "Nat")
  let reversal ← readSource dimensions "rev(n)"
  let some category := reversal.category
    | throwError "a parameterized named morphism lost its category"
  unless category.role == .morphism do
    throwError "a parameterized named morphism lost its categorical role"
  reversal.source.withOpen fun bindings value => do
    let expected ← mkAppM ``CasCatalogue.Foundation.Morphisms.finRev
      #[bindings[0]!.expression]
    unless (← isDefEq value expected) do
      throwError "a parameterized named morphism changed its declared action"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let point ← readSource empty "rev(3,2)"
  unless point.source.expression.containsConst
      (· == ``CasCatalogue.Foundation.Morphisms.finPoint) do
    throwError "a source point numeral omitted its independent declared point"
  let #[entry] := (← semanticState).numerals.filter
      (·.declaration == ``CasCatalogue.Foundation.Morphisms.finPoint)
    | throwError "the actual point numeral reference is not unique"
  let selected := point.source.expression.find? fun value =>
    match value with
    | .mdata data _ => data.getName `CasCompiler.source.kind == ``NumeralEntry &&
        data.getString `CasCompiler.source.id == entry.id.raw &&
        data.getName `CasCompiler.source.declaration == entry.declaration
    | _ => false
  unless selected.isSome do throwError "a source point numeral lost its exact selected reference"
  let rejected ← try
    discard <| readSource empty "rev(3,3)"
    pure false
  catch _ => pure true
  unless rejected do throwError "a source point numeral bypassed its declared domain obligation"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for domain in #["Int", "CasCatalogue.Foundation.Objects.integers",
      "CasCatalogue.Foundation.Objects.integersMod 3", "Rat",
      "CasCatalogue.Algebra.NamedRings.rationals"] do
    let functions ← empty.define `f (← nativeSource s!"fun (x : {domain}) => x")
    let value ← readSource functions "f(3)"
    unless value.source.expression.containsConst
        (· == ``CasCatalogue.Algebra.NamedRings.ringNumeral) &&
        !value.source.expression.containsConst
          (· == ``CasCatalogue.Foundation.Morphisms.finPoint) do
      throwError "a source numeral changed its actual registered scalar refinement"
  let scalars ← readSource empty "ℚ in Rings"
  let rings ← empty.defineTerm `R scalars
  let functions ← rings.define `f (← nativeSource
    "fun (x : CasCatalogue.Algebra.NamedRings.underlying R) => x")
  let value ← readSource functions "f(3)"
  value.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[0]!.expression.fvarId! &&
        value.containsConst (· == ``CasCatalogue.Algebra.NamedRings.ringNumeral) do
      throwError "a source numeral replaced the actual selected scalar object"
  let dictionaries ← empty.assume `customRationalNumeral
    (← nativeSource "OfNat Rat 3") .instImplicit
  let functions ← dictionaries.define `f (← nativeSource "fun (x : Rat) => x")
  let value ← readSource functions "f(3)"
  value.source.withOpen fun bindings value => do
    unless value.containsConst (· == ``CasCatalogue.Algebra.NamedRings.ringNumeral) &&
        value.containsConst (· == ``CasCatalogue.Algebra.NamedRings.ringRationals) &&
        !value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "a source rational point changed its declared ring or used a host numeral instance"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let instances ← empty.assume `customNumeral
    (← nativeSource "OfNat (CasCatalogue.Foundation.Objects.fin 3) 2") .instImplicit
  let value ← readSource instances "rev(3,2)"
  value.source.withOpen fun bindings value => do
    unless value.containsConst (· == ``CasCatalogue.Foundation.Morphisms.finPoint) &&
        !value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "a host numeral instance changed the independent source point"
  let dimensions ← empty.assume `n (← nativeSource "Nat")
  let hypotheses ← dimensions.assume `h (← nativeSource "2 < n")
  let functions ← hypotheses.define `f
    (← nativeSource "fun (x : CasCatalogue.Foundation.Objects.fin n) => x")
  let value ← readSource functions "f(2 in Fin(n) using (proof(h)))"
  value.source.withOpen fun bindings value => do
    unless value.containsFVar bindings[0]!.expression.fvarId! &&
        value.containsFVar bindings[1]!.expression.fvarId! do
      throwError "a source point lost its actual dimension or formal domain premise"
  for source in #[
      "f(2 in Fin(n) using (proof(True.intro)))",
      "f(2 in Fin(n) using (proof(h), proof(h)))",
      "f(2 in Fin(n) using (h))"] do
    let rejected ← try
      discard <| readSource functions source
      pure false
    catch _ => pure true
    unless rejected do throwError "source point evidence bypassed its declared proof boundary"
  let modular ← empty.define `f
    (← nativeSource "fun (x : CasCatalogue.Foundation.Objects.integersMod 3) => x")
  let rejected ← try
    discard <| readSource modular "f(2 in Fin(3) using (proof(by decide)))"
    pure false
  catch _ => pure true
  unless rejected do throwError "explicit point evidence changed the consuming source domain"

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
    throwError "a scalar in a dimension expression replaced the selected finite domain"

/- An object read where another category's object is expected is viewed along the structural
route: a group as the monoid whose units are formed. Competing routes with different whole
functors (a ring's multiplicative and additive monoids) are an unresolved reading. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the structural view control did not parse"
    session.read ⟨stx⟩
  let units ← read "(Sym(3) in Groups)ˣ"
  let viewed ← units.source.withOpen fun _ expression => do
    return (← instantiateMVars expression).containsConst
      (· == ``CasCatalogue.Algebra.Ports.groupsMonoid)
  let rejected ← try
    discard <| read "(Mat₂(ℚ) in Rings)ˣ"
    pure false
  catch error => pure (CasCatalogue.Exception.isSemanticAmbiguity error)
  unless viewed do throwError "a group was not viewed along its structural monoid route"
  unless rejected do throwError "competing structural views were read without a selection"

/- Bare named constants keep their declared refinement's carrier prefix when the parameter
category has no row of that name. The resulting complete monoid is the one already supplied
by the catalogue; existing bindings and explicit Sets qualifications remain fixed. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let expected ← elabTermAndSynthesize (← `(
    CasCatalogue.Algebra.Ports.ringsMultiplicative.toFunctor.obj
      CasCatalogue.Algebra.NamedRings.ringRationals)) none
  for text in #["ℚˣ", "(ℚ)ˣ"] do
    let units ← readSource empty text
    units.source.withOpen fun _ expression => do
      let original ← sourceDomain expression
      unless original.isAppOfArity ``CasCatalogue.Algebra.Units.units 1 do
        throwError "the bare units source lost its declared object and parameter"
      let parameter := original.getAppArgs[0]!
      unless (← isDefEq parameter expected) && parameter.containsConst
          (· == ``CasCatalogue.Algebra.Ports.ringsMultiplicative) do
        throwError "the bare units source changed its complete declared monoid"
      unless parameter.containsConst
          (· == ``CasCatalogue.Algebra.NamedRings.ringRationalsIdentification) do
        throwError "the bare units source erased its named base identification"
  let rationals ← readSource empty "ℚ"
  let bound ← empty.defineTerm `Q rationals
  for text in #["Qˣ", "(ℚ in Sets)ˣ"] do
    let failure : Option Exception ← try
      discard <| readSource bound text
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "parameter reading acquired a new refinement of an already selected source"
    unless (← failure.toMessageData.toString).startsWith
        "the source expression does not have its independently declared parameter type" do
      throw failure

/- Admission data are read once at the existing admission declaration's data-field type.
Lambda and matrix syntax need that type, while an already selected map retains its source
binding when its carrier function is supplied to the same boundary. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for (text, admission) in #[
      ("(t ↦ t) in C", "obj.sets.continuous_maps"),
      ("[1,2;3,4] in (view (Mat₂(ℚ) in Rings) along «fun.rings.multiplicative_monoid»())ˣ",
        "obj.sets.units")] do
    let admitted ← readSource empty text
    admitted.source.withOpen fun _ expression => do
      let reference := expression.find? fun expression => match expression with
        | .mdata data _ => data.getName `CasCompiler.source.kind == ``ObjectEntry.admission &&
            data.getString `CasCompiler.source.id == admission
        | _ => false
      unless reference.isSome do
        throwError "the typed admission lost its independently registered constructor"
  let sine ← readSource empty "sin"
  let functions ← empty.defineTerm `f sine
  let admitted ← readSource functions "f in C"
  admitted.source.withOpen fun bindings expression => do
    unless bindings.size == 1 && expression.containsFVar bindings[0]!.expression.fvarId! do
      throwError "function admission replaced the original selected map"
  let finiteIdentity ← readSource empty "id(Fin(2))"
  let finiteFunctions ← empty.defineTerm `f finiteIdentity
  let failure : Option Exception ← try
    discard <| readSource finiteFunctions "f in C"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "function admission changed the selected map's actual endpoints"
  unless (← failure.toMessageData.toString).startsWith
      "the source expression does not have its independently declared parameter type" do
    throw failure

/- A supplied whole map is a generalized point at its original source. The selected later
map composes with that actual arrow, while a map-valued native parameter remains a value. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let domains ← empty.assume `A (← nativeSource "Type")
  let domains ← domains.assume `B (← nativeSource "Type")
  let domains ← domains.assume `C (← nativeSource "Type")
  let functions ← domains.assume `rawF (← nativeSource "A → B")
  let functions ← functions.assume `rawG (← nativeSource "B → C")
  -- Public lambda formation supplies each selected Sets morphism; native assumptions
  -- alone intentionally carry no source category in SourceSession.assume.
  let first ← readSource functions "(x ↦ rawF(x)) in (A → B)"
  let arrows ← functions.defineTerm `f first
  let second ← readSource arrows "(x ↦ rawG(x)) in (B → C)"
  let arrows ← arrows.defineTerm `g second
  let supplied ← readSource arrows "f"
  let arrows ← arrows.defineTerm `fAgain supplied
  for text in #["f", "g", "fAgain"] do
    let selected ← readSource arrows text
    unless selected.category.any (·.role == .morphism) do
      throwError "the public source fixture did not select its native map category"
  let retained := fun (session : SourceSession) (bindings : Array LocalBinding)
      (name : Name) => (do
    let some entry := session.context.entries.find? (·.userName == name)
      | throwError "the generalized application fixture lost its named source entry"
    let some binding := bindings.find? (·.id == entry.id)
      | throwError "the generalized application fixture lost its exact source binding"
    pure binding.expression : MetaM Expr)
  for (text, native, used, unused) in #[
      ("g(f)", "CategoryTheory.CategoryStruct.comp f g", `f, `fAgain),
      ("g(fAgain)", "CategoryTheory.CategoryStruct.comp fAgain g", `fAgain, `f)] do
    let composed ← readSource arrows text
    let expected ← arrows.term (← nativeSource native)
    let some category := composed.category
      | throwError "generalized application lost its morphism category"
    unless category.role == .morphism &&
        category.expression.syntacticEq (.atom CategoryId.sets) do
      throwError "generalized application changed its complete source role"
    composed.source.withOpen fun bindings value => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      let original ← retained arrows bindings used
      let other ← retained arrows bindings unused
      let later ← retained arrows bindings `g
      unless (← isDefEq value expected) && value.containsFVar original.fvarId! &&
          value.containsFVar later.fvarId! && !value.containsFVar other.fvarId! do
        throwError "generalized application substituted an equal native arrow binding"
  let failure : Option Exception ← try
    discard <| readSource arrows "f(g)"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "generalized application ignored the actual intermediate native object"
  unless (← failure.toMessageData.toString).startsWith
      "Application type mismatch: The " do
    throw failure
  let nested ← arrows.assume `rawH (← nativeSource "B → B")
  let middle ← readSource nested "(x ↦ rawH(x)) in (B → B)"
  let nested ← nested.defineTerm `h middle
  let composed ← readSource nested "g(h(f))"
  let expected ← nested.term (← nativeSource
    "CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp f h) g")
  composed.source.withOpen fun bindings value => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq value expected do
      throwError "nested generalized application changed its complete native composite"
    for name in #[`f, `g, `h] do
      unless value.containsFVar (← retained nested bindings name).fvarId! do
        throwError "nested generalized application lost an original complete map"
  let failure : Option Exception ← try
    discard <| readSource nested "g(h(g))"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "nested generalized application changed its actual intermediate object"
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
    applied.source.withOpen fun bindings value => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless (← isDefEq value expected) &&
          value.containsFVar (← retained consumers bindings `f).fvarId! do
        throwError "a map-valued native parameter was changed into generalized composition"

/- A direct datum and a generalized datum retain their actual constructor fields and proofs.
Only their own native type comparison distinguishes the two readings. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let direct ← empty.assume `n (← nativeSource "Nat")
  let direct ← direct.assume `k (← nativeSource "Nat")
  let direct ← direct.assume `h (← nativeSource "k < n")
  let point ← withCurrHeartbeats <| readSource direct "k in Fin(n) using (proof(h))"
  let original ← direct.term (← nativeSource "(⟨k, h⟩ : Fin n)")
  point.source.withOpen fun bindings value => do
    let original ← original.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq value original do
      throwError "the direct constrained datum changed its original native constructor"
    for index in [0:3] do
      unless value.containsFVar bindings[index]!.expression.fvarId! do
        throwError "the direct constrained datum lost an original parameter or proof"
  let generalized ← empty.assume `D (← nativeSource "Type")
  let generalized ← generalized.assume `n (← nativeSource "Nat")
  let generalized ← generalized.assume `rawF (← nativeSource "D → Nat")
  let generalized ← generalized.assume `h (← nativeSource "∀ d, rawF d < n")
  let mapped ← withCurrHeartbeats <| readSource generalized "rawF in Fin(n) using (proof(h))"
  unless mapped.category.any (·.role == .morphism) do
    throwError "the generalized constrained datum lost its selected native map role"
  let original ← generalized.term (← nativeSource
    "TypeCat.ofHom (fun d : D => (⟨rawF d, h d⟩ : Fin n))")
  mapped.source.withOpen fun bindings value => do
    let original ← original.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq value original do
      throwError "the generalized constrained datum changed its original native map"
    for index in [0:4] do
      unless value.containsFVar bindings[index]!.expression.fvarId! do
        throwError "the generalized constrained datum lost an original domain, map or proof"

private def originalReaderFailure {α : Type} (action : TermElabM α) :
    TermElabM Exception := do
  let failure : Option Exception ← try
    discard <| withCurrHeartbeats <| withoutModifyingState action
    pure none
  catch failure => pure (some failure)
  let some failure := failure | throwError "the negative reader control unexpectedly succeeded"
  pure failure

/- A reader failure is not evidence that the same datum is a map. Proof failure is checked
only after choosing the direct datum and cannot invoke the generalized reader either. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalDataFailure ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.originalConstrainedDataFailure
  let target := mkApp (mkConst ``Fin) (mkNatLit 3)
  let mapCalls ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let unexpectedMap : TermElabM NativeSourceJudgement := do
    mapCalls.modify (· + 1)
    throwError "the failed direct datum was retried as a map"
  let validProof ← nativeSource "by decide"
  let failedData : Expr → TermElabM (Except MessageData Expr) := fun _ =>
    throw (Exception.internal originalDataFailure)
  let failure ← originalReaderFailure <| sourceConstrainedPointApplicable target
    #[validProof] failedData unexpectedMap
  match failure with
  | .internal id _ =>
    unless id == originalDataFailure do
      throwError "the constrained datum changed its original internal exception"
  | _ => throwError "the constrained datum replaced its reader's original internal exception"
  unless (← mapCalls.get) == 0 do
    throwError "the failed constrained datum invoked another interpretation"
  let wrongProof ← nativeSource "True.intro"
  discard <| originalReaderFailure <| sourceConstrainedPointApplicable target #[wrongProof]
    (fun _ => pure (.ok (mkNatLit 0))) unexpectedMap
  unless (← mapCalls.get) == 0 do
    throwError "a failed constrained proof invoked another interpretation"

private def nativeBinderArgument (value expected : Expr) :
    TermElabM (Except MessageData Expr) := do
  unless ← isDefEq (← inferType value) expected do
    return .error "the test argument has another native type"
  return .ok value

/- Use the existing real/complex/power-series rows. Their original data-field types select
the real geometric family; the existing catalogue evidence establishes its admission. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let integral ← withCurrHeartbeats <| readSource empty "∫_{0}^{1} t dt"
  integral.source.withOpen fun _ value => do
    check value
    unless value.containsConst (· == ``CasCatalogue.Algebra.Calculus.integral) &&
        value.containsConst (· == ``CasCatalogue.Algebra.Calculus.admitContinuous) do
      throwError "a binder returned its point argument instead of the original admitted operation"
  let functions ← empty.define `g
    (← nativeSource "fun n : Nat => ((1 : Real) / 2) ^ n")
  let selected ← withCurrHeartbeats <| readSource functions "∑_{n ∈ ℕ} g(n)"
  selected.source.withOpen fun bindings value => do
    check value
    unless value.containsConst (· == ``CasCatalogue.Algebra.Series.realSeriesSum) &&
        value.containsConst (· == ``CasCatalogue.Algebra.Series.admit) &&
        value.containsFVar bindings[0]!.expression.fvarId! do
      throwError "the selected binder changed its original operation, family or map admission"
    let reference := value.find? fun expression => match expression with
      | .mdata data _ => data.getName `CasCompiler.source.kind == ``BinderEntry &&
          data.getString `CasCompiler.source.id == "bind.sets.real_series"
      | _ => false
    unless reference.isSome do
      throwError "the selected binder lost its original registered row"

/- In the same actual overloaded family, failed argument/body reads and selected admission
evidence are errors. Only an explicit own-type mismatch can remove a candidate. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalDataFailure ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.originalBinderDataFailure
  unless ((← semanticState).binders.filter (·.token == "∑")).size > 1 do
    throwError "the binder failure control requires the original overloaded family"
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let missing ← originalReaderFailure <|
    readSource empty "∑_{n ∈ ℕ} unregistered_binder_body"
  unless CasCatalogue.Exception.stratum? missing == some .invalid &&
      CasCatalogue.Exception.isUnknownSourceName missing "unregistered_binder_body" do
    throwError "the binder replaced its body's original unknown-name failure"
  let index := nativeBinderArgument (mkConst ``Nat)
  let failedBody : Expr → TermElabM Expr := fun _ =>
    throw (Exception.internal originalDataFailure)
  let bodyFailure ← originalReaderFailure <| sourceBinder "∑" #[index] `n failedBody
  match bodyFailure with
  | .internal id _ =>
    unless id == originalDataFailure do
      throwError "the binder changed its original body exception"
  | _ => throwError "the binder swallowed its original body exception"
  let failedArgument : Expr → TermElabM (Except MessageData Expr) := fun _ =>
    throw (Exception.internal originalDataFailure)
  let argumentFailure ← originalReaderFailure <|
    sourceBinder "∑" #[failedArgument] `n failedBody
  match argumentFailure with
  | .internal id _ =>
    unless id == originalDataFailure do
      throwError "the binder changed its original argument exception"
  | _ => throwError "the binder swallowed its original argument exception"
  let mismatch : Expr → TermElabM (Except MessageData Expr) := fun _ =>
    pure (.error "the supplied argument has another native type")
  let absent ← originalReaderFailure <| sourceBinder "∑" #[mismatch] `n failedBody
  unless CasCatalogue.Exception.stratum? absent == some .invalid &&
      !CasCatalogue.Exception.isSemanticAmbiguity absent do
    throwError "zero applicable binder rows were reported as ambiguity"
  let family ← elabTermAndSynthesize (← nativeSource "fun _ : Nat => (1 : Real)") none
  let bodies ← liftM (m := IO) <| IO.mkRef (0 : Nat)
  let admissionFailure ← originalReaderFailure <| sourceBinder "∑" #[index] `n fun n => do
    bodies.modify (· + 1)
    pure (mkApp family n)
  unless (← bodies.get) == 1 &&
      CasCatalogue.Exception.stratum? admissionFailure == some .invalid do
    throwError "a selected binder admission failure retried another body interpretation"

/- Overload selection keeps the original checked body occurrence and its native state.
The declarations below are checked aliases of the identity function, not new binder rows;
their distinct names expose a replay even though every candidate has the same value. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let rows := (← semanticState).binders.filter (·.token == "∑")
  unless rows.size > 1 do throwError "the binder retention control requires the actual overloads"
  let some selectedIndex := rows.findIdx? (·.id.raw == "bind.sets.real_series")
    | throwError "the binder retention control lost the original real-series row"
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
  let index : Expr → TermElabM (Except MessageData Expr) := fun expected => do
    argumentReads.modify (· + 1)
    nativeBinderArgument (mkConst ``Nat) expected
  let retained ← withCurrHeartbeats <| session.context.withOpen fun bindings => do
    let #[outer, _, family] := bindings
      | throwError "the binder retention control changed its original source scope"
    let context ← ContextTelescope.capture bindings
    let value ← sourceBinder "∑" #[index] `n fun parameter => do
      unless parameter.isFVar && parameter.fvarId! != outer.expression.fvarId! do
        throwError "the bound variable replaced an earlier same-named source parameter"
      let ordinal ← argumentReads.get
      let name ← mkAuxDeclName (.num `binderBodyOccurrence ordinal)
      addDecl (.defnDecl { name, levelParams := [], type := identityType,
        value := identity, hints := .abbrev, safety := .safe })
      declarations.modify (·.push (ordinal, name))
      pure (mkApp (mkConst name) (mkApp family.expression parameter))
    unless (← argumentReads.get) == rows.size do
      throwError "binder selection replayed an original argument or bound body"
    let created ← declarations.get
    let some (_, selectedName) := created.find? (·.1 == selectedIndex + 1)
      | throwError "the original selected binder body was not retained"
    unless value.containsConst (· == selectedName) &&
        value.containsFVar family.expression.fvarId! &&
        !value.containsFVar outer.expression.fvarId! do
      throwError "binder selection replaced its checked body or captured source occurrence"
    let environment := (← getEnv).setExporting false
    for (ordinal, name) in created do
      unless environment.contains name == (ordinal == selectedIndex + 1) do
        throwError "binder selection lost the selected native state or kept a rejected state"
    check value
    context.close value
  unless retained.context.exactlyMatches session.context do
    throwError "binder selection shortened its complete context or changed stable binding identities"
  retained.withOpen fun _ value => checkWithKernel value

/- Native exceptions restore a speculative row's state and retain the original exception.
The public source failure controls above continue to check the same error classifications. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalFailure ← liftM (m := IO) <|
    registerInternalExceptionId `CasCompiler.tests.originalBinderStateFailure
  let introduced ← liftM (m := IO) <| IO.mkRef (none : Option Name)
  let failure : Option Exception ← try
    discard <| withCurrHeartbeats <| sourceBinder "∑"
      #[nativeBinderArgument (mkConst ``Nat)] `n fun _ => do
        let name ← mkAuxDeclName `failedBinderBody
        addDecl (.defnDecl { name, levelParams := [], type := mkConst ``Nat,
          value := mkNatLit 1, hints := .abbrev, safety := .safe })
        introduced.set (some name)
        throw (Exception.internal originalFailure)
    pure none
  catch error => pure (some error)
  let some (.internal actual _) := failure
    | throwError "a binder state failure lost its original native exception"
  unless actual == originalFailure do
    throwError "a binder state failure was replaced by another exception"
  let some name ← introduced.get
    | throwError "the binder state control never reached its original body"
  unless !((← getEnv).setExporting false).contains name do
    throwError "a failed binder row left its speculative native declaration behind"
