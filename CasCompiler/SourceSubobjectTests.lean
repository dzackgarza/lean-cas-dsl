module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import CasCompiler.RoutedMethodFamily
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.RoutedMethodFamily
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

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



private def checkKernelProjection (term : SourceTerm) (root : BindingId)
    (field : Name) (base : ClosedTerm) : TermElabM Unit := do
  let some category := term.category
    | throwError "the ordinary subobject projection lost its selected category"
  let role := if field == ``CategoryTheory.Comma.left then SourceCategoryRole.object else .morphism
  unless category.role == role && category.expression.syntacticEq Modules.Modules do
    throwError "the ordinary subobject projection changed its original base category or role"
  checkSelected term fun expression => do
    let scope ← get
    let value ← selectedValue expression
    let source ← ClosedTerm.close scope.context value
    let some selected ← source.inputProjectionAt #[] (scope.context.bindings.map (·.id))
      | throwError "the ordinary subobject projection is not rooted in a retained input"
    let .context selectedRoot := selected.target
      | throwError "the ordinary subobject projection selected an argument instead of its binding"
    unless selectedRoot == root &&
        selected.path == #[``CategoryTheory.ObjectProperty.FullSubcategory.obj, field] do
      throwError "the ordinary subobject projection selected a different occurrence or native field"
    let some original := scope.context.bindings.find? (·.id == root)
      | throwError "the ordinary subobject projection lost its retained source binding"
    let arrow ← mkProjection original.expression `obj
    let expected ← mkProjection arrow (if field == ``CategoryTheory.Comma.left then `left else `hom)
    checkOriginal #[value, expected, ← category.bundle.inContext scope.context,
        ← base.inContext scope.context] fun native => do
      unless (← isDefEq native[0]! native[1]!) && (← isDefEq native[2]! native[3]!) do
        throwError "the ordinary subobject projection changed its complete native source"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))




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
      unless (question.source.context.entries.take session.context.entries.size).map (·.id) ==
          session.context.entries.map (·.id) do
        throwError "the original kernel question lost its complete source context"
      checkSelected question fun expression => do
        checkOriginal #[expression] fun native => do
          unless ← isProp native[0]! do throwError "the original kernel question is not a proposition"
          check native[0]!
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
      checkSelected value fun expression => do
        let scope ← get
        let some projection := scope.context.bindings.find? (·.id == original.id)
          | throwError "the ordinary kernel lost its original module map"
        unless (← visitNativeData (fun term =>
            originatesAt scope.context scope.selections term projection.expression false)
            expression false) > 0 do
          throwError "the ordinary kernel replaced its actual input"
        checkOriginal #[expression, projection.expression] fun native => do
          let declaration ← mkConstWithFreshMVarLevels
            ``CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelDeclaration
          let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
          unless ← expandSourceStructures parameters do
            throwError "the published kernel functor has inconsistent native parameters"
          let family := mkAppN declaration parameters
          let (domain, target) ← functorCategoryBundles family
          let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[native[1]!]
          unless ← isDefEq (← inferType arrow) (← mkAppM ``CategoryTheory.Bundled.α #[domain]) do
            throwError "the published kernel functor has a different complete native input"
          let family ← instantiateMVars family
          if family.hasMVar || family.hasLevelMVar then
            throwError "the published kernel functor lost an actual native parameter"
          let expected ← functorObject family arrow (← instantiateMVars target)
          unless ← isDefEq native[0]! expected do
            throwError "the ordinary kernel replaced its published functor"
          checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
            (← mkEq native[0]! expected))
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
  let type ← session.elaborateScoped Syntax.missing do
    mkAppM ``CategoryTheory.Bundled.α #[← session.readTerm firstSubobjects.value]
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
      checkSelected projected fun _ => do
        let scope ← get
        let some chosen := scope.context.bindings.find? (·.id == chosen.id)
          | throwError "the actual category parameter is outside the original context"
        let some unrelated := scope.context.bindings.find? (·.id == unrelated.id)
          | throwError "the distinct category parameter is outside the original context"
        let bundle ← category.bundle.inContext scope.context
        unless (← visitNativeData (fun term =>
            originatesAt scope.context scope.selections term chosen.expression false) bundle false) > 0 &&
            (← visitNativeData (fun term =>
            originatesAt scope.context scope.selections term unrelated.expression false) bundle false) == 0 do
          throwError "the projection replaced its actual selected category parameter"
  expectKernelFailure (discard <| kernelSource session "raw.obj()")
    "no declared member family accepts this complete selected receiver"
  expectKernelFailure (discard <| kernelSource session "raw.hom()")
    "no declared member family accepts this complete selected receiver"
  expectKernelFailure (discard <| kernelSource session "KFirst.obj(0)")
    "a selected subobject projection takes no additional source arguments"



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

  let some first := route.steps[0]?
    | throwError "the original inherited route lost its first structural edge"
  unless !(first.source.syntacticEq first.target) do
    throwError "the original inherited-route control lost its distinct first endpoints"
  let changed : StructuralEdge := {
    source := first.source
    target := first.source
    expression := .identity first.source
    ref := first.ref }
  let forged := { route with steps := route.steps.set! 0 changed }
  unless forged.refs == route.refs && forged.source.syntacticEq route.source &&
      forged.target.syntacticEq route.target do
    throwError "the intermediate-edge control changed the route's original outer interface"
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| RoutedMethodFamily.forRoute forged method
      return none
    catch failure => return some failure
  let some failure := failure
    | throwError "the source method accepted a substituted intermediate structural edge"
  unless failure.toMessageData.hasTag (· == `CasCompiler.RoutedMethodFamily.invalidRoute) do
    throw failure
