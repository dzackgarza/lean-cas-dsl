module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.Resolve
import CasCompiler.RoutedMethodFamily
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.Resolve
meta import CasCompiler.RoutedMethodFamily
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction

open Lean Meta Elab Term CasCompiler CasCatalogue

private def kernelSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the ordinary subobject source did not parse"
  session.read ⟨stx⟩

private def kernelNative (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the ordinary subobject native parameter did not parse"
  return ⟨stx⟩

private def expectKernelFailure (action : TermElabM Unit) (errorPrefix : String) :
    TermElabM Unit := do
  let failure : Option Exception ← withoutModifyingState do
    try
      action
      pure none
    catch error => pure (some error)
  let some failure := failure | throwError "the ordinary subobject control was admitted"
  unless (← failure.toMessageData.toString).startsWith errorPrefix do throw failure

-- Check the actual source occurrence and native field path, not just definitional equality
-- of a newly evaluated kernel with the expected mathematical object.
private def checkKernelProjection (term : SourceTerm) (root : BindingId)
    (field : Name) (base : ClosedTerm) : MetaM Unit := do
  let some category := term.category
    | throwError "the ordinary subobject projection lost its selected category"
  let role := if field == ``CategoryTheory.Comma.left then SourceCategoryRole.object else .morphism
  unless category.role == role && category.expression.syntacticEq Modules.Modules do
    throwError "the ordinary subobject projection changed its original base category or role"
  let some selected ← term.source.inputProjectionAt #[] (term.source.context.entries.map (·.id))
    | throwError "the ordinary subobject projection is not rooted in a retained input"
  let .context selectedRoot := selected.target
    | throwError "the ordinary subobject projection selected an argument instead of its binding"
  unless selectedRoot == root &&
      selected.path == #[``CategoryTheory.ObjectProperty.FullSubcategory.obj, field] do
    throwError "the ordinary subobject projection selected a different occurrence or native field"
  term.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    let some original := bindings.find? (·.id == root)
      | throwError "the ordinary subobject projection lost its retained source binding"
    let arrow ← mkProjection original.expression `obj
    let expected ← mkProjection arrow (if field == ``CategoryTheory.Comma.left then `left else `hom)
    unless (← isDefEq value expected) &&
        (← isDefEq (← category.bundle.inContext context) (← base.inContext context)) do
      throwError "the ordinary subobject projection changed its complete native source"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))

-- The unchanged kernel prefix of each existing file is read through its complete
-- projection and zero-composite questions. This focused frontend check stops at
-- restricted; the complete original RX08 files remain separate required consumers.
private def checkOrdinaryKernel (path : String) : TermElabM Unit := do
  let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let mut session ← SourceSession.empty identities
  let mut questions : Array String := #[]
  let mut projections : Array Name := #[]
  for item in file.items do
    if let `(cas_item| test $id:ident $_:str : assert $body:cas_term) := item then
      let question ← try file.withContext (session.readQuestion body)
        catch error => throwError "original kernel question {id.getId}: {error.toMessageData}"
      unless question.source.context.entries.map (·.id) == session.context.entries.map (·.id) do
        throwError "the original kernel question lost its complete source context"
      question.source.withOpen fun _ expression => do
        unless ← isProp expression do throwError "the original kernel question is not a proposition"
        check expression
      questions := questions.push (id.getId.toString (escape := false))
      continue
    let `(cas_item| $statement:cas_stmt) := item | continue
    let name ← match statement with
      | `(cas_stmt| let $name:ident := $_:cas_term) => pure name.getId
      | `(cas_stmt| let $name:ident($_:cas_term) := $_:cas_term) => pure name.getId
      | _ => continue
    if name == `restricted then break
    let checked ← try file.withContext (session.readStatement statement)
      catch error => throwError "original kernel binding {name}: {error.toMessageData}"
    let .definition next value := checked
      | throwError "an original kernel definition changed its statement kind"
    if name == `K then
      let some original := session.context.entries.find? (·.userName == `projection)
        | throwError "the original module map is absent"
      let some category := value.category
        | throwError "the ordinary kernel lost its selected result category"
      unless category.expression.syntacticEq Modules.Bilinear.Valued.Kernels.SubobjectsModules do
        throwError "the ordinary kernel acquired a different source result family"
      value.source.withOpen fun bindings expression => do
        let some projection := bindings.find? (·.id == original.id)
          | throwError "the ordinary kernel lost its original module map"
        let declaration ← mkConstWithFreshMVarLevels
          ``CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelDeclaration
        let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
        unless ← expandSourceStructures parameters do
          throwError "the published kernel functor has inconsistent native parameters"
        let family := mkAppN declaration parameters
        let (domain, target) ← functorCategoryBundles family
        let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[projection.expression]
        unless ← isDefEq (← inferType arrow) (← mkAppM ``CategoryTheory.Bundled.α #[domain]) do
          throwError "the published kernel functor has a different complete native input"
        let family ← instantiateMVars family
        if family.hasMVar || family.hasLevelMVar then
          throwError "the published kernel functor lost an actual native parameter"
        let expected ← functorObject family arrow (← instantiateMVars target)
        unless expression.containsFVar projection.expression.fvarId! &&
            (← isDefEq expression expected) do
          throwError "the ordinary kernel replaced its actual input or published functor"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
    if name == `kernelObject || name == `kernelInclusion then
      let some original := session.context.entries.find? (·.userName == `K)
        | throwError "the original kernel result is absent"
      let some projection := session.context.entries.find? (·.userName == `projection)
        | throwError "the original module map is absent"
      let some base := session.categoryFor projection.id
        | throwError "the original module map lost its selected category"
      checkKernelProjection value original.id
        (if name == `kernelObject then ``CategoryTheory.Comma.left else ``CategoryTheory.Comma.hom)
        base.bundle
      projections := projections.push name
    session := next
  unless projections == #[`kernelObject, `kernelInclusion] && questions.size == 3 &&
      questions[0]!.endsWith ".full_projection" &&
      questions[1]!.endsWith ".kernel_dimension" &&
      questions[2]!.endsWith ".kernel_zero_composite" do
    throwError "the original kernel consumer lost a projection or complete source question"
  let some projection := session.context.entries.find? (·.userName == `projection)
    | throwError "the original module map is absent after its continuation"
  let some base := session.categoryFor projection.id
    | throwError "the original module category is absent after its continuation"
  session ← session.defineTerm `KAgain (← kernelSource session "K")
  let some selectedAlias := session.context.entries.back?
    | throwError "the original kernel alias did not bind"
  for (name, field) in #[
      ("obj", ``CategoryTheory.Comma.left), ("hom", ``CategoryTheory.Comma.hom)] do
    checkKernelProjection (← kernelSource session s!"KAgain.{name}()") selectedAlias.id field base.bundle

run_cmd Lean.Elab.Command.liftTermElabM do
  checkOrdinaryKernel
    "tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/rx08-ordinary-kernel.cas"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkOrdinaryKernel
    "tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/clarifications/rx08-ordinary-module-kernel.cas.proposal"

-- Equal definitions do not identify the selected category parameters. The same raw
-- subobject can be explicitly typed in either convertible complete category; each
-- projection must preserve the category that its source actually selected.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← kernelNative "RingCat.{0}")
  let session ← session.define `RFirst (← kernelNative "R")
  let session ← session.define `RSecond (← kernelNative "R")
  let firstRing ← session.term (← kernelNative "RFirst")
  let secondRing ← session.term (← kernelNative "RSecond")
  let first ← session.namedCategory Syntax.missing "Modules" [.zero, .zero] #[firstRing]
  let second ← session.namedCategory Syntax.missing "Modules" [.zero, .zero] #[secondRing]
  let firstSubobjects ← session.unaryCategory Syntax.missing ConstructorId.subobjects first
  let secondSubobjects ← session.unaryCategory Syntax.missing ConstructorId.subobjects second
  let type ← session.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← firstSubobjects.value.source.inContext context]
  let session ← session.assumeTerm `raw type
  let raw ← session.term (← kernelNative "raw")
  let firstValue ← raw.inCategory firstSubobjects.expression firstSubobjects.value
  let secondValue ← raw.inCategory secondSubobjects.expression secondSubobjects.value
  let session ← session.defineTerm `KFirst firstValue
  let session ← session.defineTerm `KSecond secondValue
  for (name, ring, other, base) in #[
      ("KFirst", `RFirst, `RSecond, first.value.source),
      ("KSecond", `RSecond, `RFirst, second.value.source)] do
    let some original := session.context.entries.find? (·.userName == Name.mkSimple name)
      | throwError "the typed subobject did not retain its original source binding"
    let some chosen := session.context.entries.find? (·.userName == ring)
      | throwError "the typed subobject lost its chosen category parameter"
    let some unrelated := session.context.entries.find? (·.userName == other)
      | throwError "the category control lost its distinct equal definition"
    for (member, field) in #[
        ("obj", ``CategoryTheory.Comma.left), ("hom", ``CategoryTheory.Comma.hom)] do
      let projected ← kernelSource session s!"{name}.{member}()"
      checkKernelProjection projected original.id field base
      let some category := projected.category
        | throwError "the projection lost its actual complete category"
      projected.source.withOpen fun bindings _ => do
        let context ← ContextTelescope.capture bindings
        let some chosen := bindings.find? (·.id == chosen.id)
          | throwError "the actual category parameter is outside the original context"
        let some unrelated := bindings.find? (·.id == unrelated.id)
          | throwError "the distinct category parameter is outside the original context"
        let bundle ← category.bundle.inContext context
        unless bundle.containsFVar chosen.expression.fvarId! &&
            !bundle.containsFVar unrelated.expression.fvarId! do
          throwError "the projection replaced its actual selected category parameter"
  expectKernelFailure (discard <| kernelSource session "raw.obj()")
    "no declared member family accepts this complete selected receiver"
  expectKernelFailure (discard <| kernelSource session "raw.hom()")
    "no declared member family accepts this complete selected receiver"
  expectKernelFailure (discard <| kernelSource session "KFirst.obj(0)")
    "a selected subobject projection takes no additional source arguments"

-- The empty-return case is not an inherited-return bypass. A real nonidentity route
-- still requires actual lifting data, and a forged empty route is not first-hit source data.
run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  let some method := state.methods.find? (·.id.raw == "meth.kernel")
    | throwError "the published kernel method is absent"
  let query ← SourceRoutes.forMethod Modules.Bilinear.Valued.Kernels.ArrowsBilin "kernel"
  let some routes ← query.finiteRoutes
    | throwError "the original formed-arrow route lost its finite selected comparison"
  let some route := routes.find? (fun route =>
      !route.refs.isEmpty && route.target.syntacticEq method.owner)
    | throwError "the formed-arrow control no longer has its declared inherited route"
  expectKernelFailure (do
      let _ ← RoutedMethodFamily.forRoute route method
      pure ())
    "source method lifting requires its actual selected return data"
  expectKernelFailure
    (do
      let _ ← RoutedMethodFamily.forRoute { route with steps := #[] } method
      pure ())
    "the selected method route is not a complete first-hit source route"
