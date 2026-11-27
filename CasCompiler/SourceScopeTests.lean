module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Language
open CasCompiler.SourceTest

private def readScopedStatement (session : SourceSession) (text : String) :
    TermElabM SourceStatement := do
  let file ← SourceFile.parse "scoped-declarations.cas" text
  let #[item] := file.items
    | throwError "the scoped declaration control changed its public statement count"
  let `(cas_item| $statement:cas_stmt) := item
    | throwError "the scoped declaration control changed its public syntax"
  file.withContext <| session.readStatement statement



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let environment ← getEnv
  let .assumption rings ← readScopedStatement empty "let R ∈ CommutativeRings"
    | throwError "the abstract category declaration did not introduce a local assumption"
  let #[ring] ← authoredEntries rings.context rings.selections
    | throwError "the abstract declaration changed the original source telescope"
  let category ← selectCategory (← semanticState) "CommutativeRings"
  let some selected := rings.categoryFor ring.id
    | throwError "the abstract ring lost its selected category"
  unless ring.role == .parameter && ring.value.isNone && selected.role == .object &&
      selected.expression.syntacticEq category.expression do
    throwError "the abstract declaration acquired a concrete value or changed its category"
  let .assumption elements ← readScopedStatement rings "let x ∈ R"
    | throwError "the dependent abstract element did not remain a local parameter"
  let some element := elements.context.entries.back?
    | throwError "the dependent abstract element has no retained source binding"
  unless element.role == .parameter && element.value.isNone do
    throwError "the hypothetical element acquired an invented definition"
  let .definition uniform one ← readScopedStatement elements "let one := 1 in R"
    | throwError "the abstract ring did not expose its declared uniform numeral"
  checkSelected one fun expression => do
    let scope ← get
    let some actualRing := scope.context.bindings.find? (·.id == ring.id)
      | throwError "the uniform numeral lost its original abstract ring"
    let some selected ← SourceReadM.selection? expression
      | throwError "the uniform numeral lost its exact selected native binder"
    let some (.numeral row) := selected.reference
      | throwError "the uniform numeral lost its complete original numeral row"
    let some application := selected.originalApplication
      | throwError "the uniform numeral lost its complete original application"
    unless row.id.raw == "num.rings" && application.getAppFn.isConstOf row.declaration &&
        (← application.getAppArgs.anyM fun argument =>
          originatesAt scope.context scope.selections argument actualRing.expression false) do
      throwError "the uniform numeral replaced its abstract input or selected family"
    check expression
  let .assumption assumptions ← readScopedStatement uniform "assume h : x = one"
    | throwError "the public hypothesis did not extend the actual local scope"
  let some hypothesis := assumptions.context.entries.back?
    | throwError "the public hypothesis has no retained source binding"
  unless hypothesis.role == .hypothesis && hypothesis.value.isNone do
    throwError "a local hypothesis became a proved definition"
  let .proved proposition evidence ← readScopedStatement assumptions
      "assert x = one using (proof(h))"
    | throwError "the explicit proof did not retain its original proposition and evidence"
  discard <| assumptions.elaborateScoped Syntax.missing do
    let expression ← assumptions.readTerm evidence
    let proposition ← assumptions.readTerm proposition
    let scope ← get
    let some actualHypothesis := scope.context.bindings.find? (·.id == hypothesis.id)
      | throwError "the source proof lost its actual local hypothesis"
    let some actualRing := scope.context.bindings.find? (·.id == ring.id)
      | throwError "the source proof lost its original abstract ring"
    let some actualElement := scope.context.bindings.find? (·.id == element.id)
      | throwError "the source proof lost its original abstract element"
    unless ← originatesAt scope.context scope.selections expression actualHypothesis.expression false do
      throwError "the explicit proof replaced its original source hypothesis"
    let dependent ← visitNativeData (fun term =>
      originatesAt scope.context scope.selections term actualRing.expression false)
      (← inferType actualElement.expression) false
    unless dependent > 0 do
      throwError "the dependent element replaced its original source ring"
    checkOriginal #[expression, proposition] fun native => do
      checkWithKernel (← mkExpectedTypeHint native[0]! native[1]!)
    return expression
  let conclusion ← assumptions.conclusion #[proposition] (some evidence)
  unless conclusion.context.context.exactlyMatches assumptions.context &&
      conclusion.proof.isSome && conclusion.inspectAssumptions != "No local assumptions." do
    throwError "the proved statement lost its original local assumptions"
  let .inspection observed ← readScopedStatement assumptions "inspect assumptions"
    | throwError "explicit assumption inspection did not return a frozen context"
  unless observed.context.exactlyMatches assumptions.context &&
      observed.assumptionsText == conclusion.inspectAssumptions do
    throwError "explicit inspection changed the actual retained assumptions"
  for name in #[`R, `x, `one, `h] do
    unless (← getEnv).contains name == environment.contains name do
      throwError "a public local declaration introduced a global declaration"
  let bad ← SourceFile.parse "wrong-scoped-proof.cas"
    "assert x = one using (proof(True.intro))"
  let #[item] := bad.items | throwError "the wrong-proof control did not parse one statement"
  let `(cas_item| $statement:cas_stmt) := item
    | throwError "the wrong-proof control changed its syntax"
  let failure : Option Exception ← try
    discard <| bad.withContext <| assumptions.readStatement statement
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "a different proposition justified a scoped assertion"
  unless failure.toMessageData.hasTag (· == `CasCompiler.sourceFormalProof.typeMismatch) do
    throw failure



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let .assumption scalars ← readScopedStatement empty "let S ∈ Rings"
    | throwError "the parameterized-category control lost its abstract scalar"
  let #[scalar] ← authoredEntries scalars.context scalars.selections
    | throwError "the scalar declaration changed its original telescope"
  let some scalarCategory := scalars.categoryFor scalar.id
    | throwError "the scalar lost its originally selected category"
  let .assumption modules ← readScopedStatement scalars "let M ∈ Modules(S)"
    | throwError "the parameterized abstract category did not introduce a local object"
  let some moduleEntry := modules.context.entries.back?
    | throwError "the abstract module lost its original binding"
  let some selected := modules.categoryFor moduleEntry.id
    | throwError "the abstract module lost its complete selected category"
  let expectedCategory ← selectCategory (← semanticState) "Modules"
  unless moduleEntry.role == .parameter && moduleEntry.value.isNone &&
      selected.role == .object && selected.expression.syntacticEq expectedCategory.expression do
    throwError "the module became a concrete object or changed its category family"
  discard <| modules.elaborateScoped Syntax.missing do
    let scope ← get
    let context := scope.context
    let some original := context.bindings.find? (·.id == scalar.id)
      | throwError "the complete module category lost its original scalar binding"
    let some object := context.bindings.find? (·.id == moduleEntry.id)
      | throwError "the complete module category lost its original object binding"
    let bundle ← selected.bundle.inContext context
    let expected ← sourceReferenceAt (.category expectedCategory) bundle bundle
    unless scope.selections.toList.any (fun (_, retained) =>
        retained.exactlyMatches Expr.equal expected) do
      throwError "the abstract module changed its complete original category row"
    unless bundle.getAppFn.isConstOf expectedCategory.declaration &&
        bundle.getAppArgs.size == 1 do
      throwError "the abstract module changed the complete declared category application"
    let some (actualCategory, actualScalar) ← sourceObjectOrigin? bundle.getAppArgs[0]!
      | throwError "the parameterized category discarded its explicit source parameter"
    unless (← originatesAt context scope.selections actualScalar original.expression) &&
        actualCategory.role == .object &&
        actualCategory.expression.syntacticEq scalarCategory.expression &&
        actualCategory.bundle.equal (← scalarCategory.bundle.inContext context) do
      throwError "the parameterized category replaced its original scalar or selected category"
    let expectedType ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
    checkWithKernel (← mkExpectedTypeHint object.expression expectedType)
    return bundle



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let .definition concrete value ← readScopedStatement empty
      "let Q := ℚ ∈ CommutativeRings"
    | throwError "the Unicode concrete declaration did not remain a definition"
  let some entry := concrete.context.entries.back?
    | throwError "the concrete declaration lost its original source binding"
  let some category := concrete.categoryFor entry.id
    | throwError "the concrete declaration lost its selected category"
  let expectedCategory ← selectCategory (← semanticState) "CommutativeRings"
  unless entry.role == .definition && entry.value.isSome &&
      category.expression.syntacticEq expectedCategory.expression do
    throwError "the concrete declaration became a hypothetical object"
  let .definition _ expected ← readScopedStatement empty
      "let expected := ℚ in CommutativeRings"
    | throwError "the established concrete qualification did not read"
  discard <| empty.elaborateScoped Syntax.missing do
    let expression ← empty.readTerm value
    let expected ← empty.readTerm expected
    checkOriginal #[expression, expected] fun native => do
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
    return expression


  for text in #["(ℚ ∈ CommutativeRings)", "((ℚ ∈ (CommutativeRings)))"] do
    let file ← SourceFile.parse "parenthesized-category.cas"
      s!"-- original qualification\nlet Q := {text}\n"
    let #[item] := file.items
      | throwError "the parenthesized qualification changed its statement count"
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the parenthesized qualification changed its public statement"
    let `(cas_stmt| let $_:ident := $body:cas_term) := statement
      | throwError "the parenthesized qualification lost its original body"
    let .definition bounded actual ← file.withContext <| empty.readStatement statement
      | throwError "the parenthesized Unicode qualification did not remain a definition"
    let some bound := bounded.context.entries.back?
      | throwError "the parenthesized declaration lost its original binding"
    let some selected := bounded.categoryFor bound.id
      | throwError "the parenthesized declaration lost its selected category"
    unless bound.role == .definition && bound.value == some actual.source.expression &&
        selected.role == .object &&
        selected.expression.syntacticEq expectedCategory.expression do
      throwError "parentheses changed the concrete value or its selected category"
    unless actual.span.fileName == "parenthesized-category.cas" &&
        actual.span.start.isSome && actual.span.stop.isSome &&
        actual.span.start == body.raw.getPos? && actual.span.stop == body.raw.getTailPos? do
      throwError "category qualification discarded the original outer parentheses span"
    discard <| empty.elaborateScoped Syntax.missing do
      let expression ← empty.readTerm actual
      let original ← empty.readTerm value
      let expected ← empty.readTerm expected
      let scope ← get
      let some (actualRow, actualCategory) ←
          sourceObjectSelection? scope.context scope.selections expression
        | throwError "parentheses lost the rational ring's complete selected row"
      let some (originalRow, originalCategory) ←
          sourceObjectSelection? scope.context scope.selections original
        | throwError "the original rational ring lost its complete selected row"
      unless (sourceReference (.named (.registered (.inl actualRow) actualCategory)) expression).exactlyMatches
          Expr.equal (sourceReference (.named (.registered (.inl originalRow) originalCategory)) expression) &&
          actualRow.declaration == ``CasCatalogue.Algebra.NamedCommutativeRings.rationals do
        throwError "parentheses replaced the actual rational ring or its complete category"
      checkOriginal #[expression, original, expected,
          ← selected.bundle.inContext scope.context, ← category.bundle.inContext scope.context] fun native => do
        unless (← isDefEq native[0]! native[1]!) &&
            native[0]!.containsConst (· == ``CasCatalogue.Algebra.NamedCommutativeRings.rationals) &&
            (← isDefEq native[3]! native[4]!) do
          throwError "parentheses changed the original native rational ring or category"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[2]!))
      return expression
  let .definition subsets _ ← readScopedStatement concrete
      "let CommutativeRings := {1, 2} in 𝒫(ℤ)"
    | throwError "the membership domain did not define its original subset"
  let .definition membership proposition ← readScopedStatement subsets
      "let member := 1 ∈ CommutativeRings"
    | throwError "ordinary membership was reinterpreted as category qualification"
  proposition.source.withOpen fun _ expression => do
    unless ← isProp expression do
      throwError "a membership proposition became a category-qualified value"
  let some member := membership.context.entries.back?
    | throwError "the membership proposition lost its definition"
  unless member.role == .definition && member.value.isSome do
    throwError "the membership proposition was promoted to a hypothesis"
  let some subset := subsets.context.entries.back?
    | throwError "the shadowing membership domain lost its original binding"
  for text in #["(1 ∈ CommutativeRings)", "((1 ∈ (CommutativeRings)))"] do
    let file ← SourceFile.parse "parenthesized-membership.cas" s!"let member := {text}\n"
    let #[item] := file.items
      | throwError "the parenthesized membership changed its statement count"
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the parenthesized membership changed its public statement"
    let `(cas_stmt| let $_:ident := $body:cas_term) := statement
      | throwError "the parenthesized membership lost its original body"
    let .definition _ actual ← file.withContext <| subsets.readStatement statement
      | throwError "parentheses reinterpreted ordinary membership as category qualification"
    unless actual.span.fileName == "parenthesized-membership.cas" &&
        actual.span.start.isSome && actual.span.stop.isSome &&
        actual.span.start == body.raw.getPos? && actual.span.stop == body.raw.getTailPos? do
      throwError "ordinary membership discarded the original outer parentheses span"
    discard <| subsets.elaborateScoped Syntax.missing do
      let expression ← subsets.readTerm actual
      let proposition ← subsets.readTerm proposition
      let scope ← get
      let some originalSubset := scope.context.bindings.find? (·.id == subset.id)
        | throwError "parenthesized membership lost its actual shadowing domain"
      let usesSubset ← visitNativeData (fun term =>
        originatesAt scope.context scope.selections term originalSubset.expression false) expression false
      unless (← isProp expression) && usesSubset > 0 do
        throwError "parentheses changed membership in the original same-name local subset"
      checkOriginal #[expression, proposition] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "parentheses changed the original native membership proposition"
      return expression



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let .definition outer _ ← readScopedStatement empty "let outside := Fin(3)"
    | throwError "the outer source control did not define its original object"
  let .contextBlock children ← readScopedStatement outer
      "context do\n  let X ∈ Sets\n  let x in X\n  assume h : x = x\n  \
       test scoped.local \"local hypothesis\": assert x = x using (proof(h))\nend"
    | throwError "the public context block did not retain its typed children"
  unless children.size == 4 do throwError "the block lost an original child statement"
  let hypothesisItem? : Option (TSyntax `cas_item × SourceStatement) := children[2]?
  let some (_, innerStatement) := hypothesisItem?
    | throwError "the block lost its actual local hypothesis scope"
  let .assumption inner := innerStatement
    | throwError "the block lost its actual local hypothesis scope"
  let questionItem? : Option (TSyntax `cas_item × SourceStatement) := children[3]?
  let some (question, proofStatement) := questionItem?
    | throwError "the block lost its actual conditional conclusion"
  let .proved proposition evidence := proofStatement
    | throwError "the block lost its actual conditional conclusion"
  let `(cas_item| test $identity:ident $label:str : $_:cas_stmt) := question
    | throwError "the block discarded the original question label"
  unless identity.getId == `scoped.local && label.getString == "local hypothesis" do
    throwError "the block changed its original question identity"
  let conclusion ← inner.conclusion #[proposition] (some evidence)
  let outerEntries ← authoredEntries outer.context outer.selections
  let innerEntries ← authoredEntries conclusion.context.context inner.selections
  unless outerEntries.size == 1 && innerEntries.size == 4 &&
      (innerEntries[3]?).map (·.role) == some .hypothesis do
    throwError "scope exit discarded local assumptions or leaked a local binding"
  let file ← SourceFile.parse "outside-scope.cas" "let escaped := x"
  let #[item] := file.items | throwError "the scope-exit control did not parse"
  let `(cas_item| $statement:cas_stmt) := item
    | throwError "the scope-exit control changed its source syntax"
  let failure : Option Exception ← try
    discard <| file.withContext <| outer.readStatement statement
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "a local element escaped its source scope"
  unless CasCatalogue.Exception.isUnknownSourceName failure "x" do throw failure
