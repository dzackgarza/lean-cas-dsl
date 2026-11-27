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

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-rings.cas"
    "let p(x) := x² - 2x + 1 in ℤ[x]\nassert x ∈ ℤ[x]\nlet q := x · x in ℚ[x]\n\
     assert p(1) = 0\nassert q(√2) = 2\n"
  let mut session ← SourceSession.empty identities
  let mut formed := #[]
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the ring statement control changed its parsed category"
    let statement ← file.withContext (session.readStatement statement)
    if let .definition next _ := statement then session := next
    formed := formed.push statement
  let generator := ``CasCatalogue.Algebra.Polynomials.generator
  let evaluation := ``CasCatalogue.Algebra.Polynomials.evaluation
  for index in [3, 4] do
    let some (SourceStatement.question term) := formed[index]?
      | throwError "a polynomial evaluation is not a question"
    checkSelected term fun expression =>
      checkOriginal #[expression] fun original => do
        unless original[0]!.containsConst (· == evaluation) do
          throwError "a polynomial value was not applied by its registered evaluation"
  for statement in formed.extract 0 3 do
    let term ← match statement with
      | .assumption _ | .proved .. | .inspection _ | .contextBlock _ =>
        throwError "this original source control contains no scoped declaration or explicit proof"
      | .definition _ value | .question value | .implemented value => pure value
      | .settled values =>
        let #[value] := values
          | throwError "an individual ring typing judgement did not retain exactly one term"
        pure value
    checkSelected term fun expression =>
      checkOriginal #[expression] fun original => do
        unless original[0]!.containsConst (· == generator) do
          throwError "a ring variable was not read as the registered generator"
  unless formed[1]? matches some (SourceStatement.settled _) do
    throwError "membership of the ring's variable was not settled by its reading"
  let free ← SourceFile.parse "source-free-variable.cas" "let r := x · x\n"
  let rejected ← try
    let some (item : TSyntax `cas_item) := free.items[0]?
      | throwError "the free-variable control is absent"
    let `(cas_item| $statement:cas_stmt) := item | throwError "the control did not parse"
    discard <| free.withContext ((← SourceSession.empty identities).readStatement statement)
    pure false
  catch _ => pure true
  unless rejected do throwError "a variable with no written ring was read"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-coercions.cas" "let n := 3 in ℕ\nlet m := n in ℤ\nlet p := n in ℚ[x]\n"
  let mut session ← SourceSession.empty identities
  let mut values := #[]
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the coercion control changed its parsed category"
    let .definition next value ← file.withContext (session.readStatement statement)
      | throwError "a coercion control is not a definition"
    session := next
    values := values.push value
  let uses := fun (index : Nat) (declaration : Name) (failure : String) => do
    let some value := values[index]? | throwError "a coercion control was not read"
    checkSelected value fun expression =>
      checkOriginal #[expression] fun original => do
        unless original[0]!.containsConst (· == declaration) do throwError failure
  uses 1 ``CasCatalogue.Algebra.NumberSystems.naturalsIntegers
    "a natural was not read in ℤ through the registered inclusion"
  uses 2 ``CasCatalogue.Algebra.Polynomials.coefficients
    "a natural was not read in ℚ[x] through the registered constants"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let path := "tests/acceptance/b0-required-positives.cas.proposed"
  let file ← SourceFile.parse path (← IO.FS.readFile path)
  let mut found := false
  for item in file.items do
    let `(cas_item| test $id:ident $_:str : $statement:cas_stmt) := item
      | continue
    unless id.getId.toString == "units.rationals.three_inverse" do continue
    if found then throwError "the original unit assertion is repeated"
    let .question proposition ← file.withContext (session.readStatement statement)
      | throwError "the complete original unit assertion did not remain a question"
    checkSelected proposition fun expression =>
      checkOriginal #[expression] fun original => do
        unless original[0]!.isAppOfArity ``Eq 3 do
          throwError "the original unit equality was not retained"
    found := true
  unless found do throwError "the complete original unit assertion is absent"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let read := fun (session : SourceSession) (text : String) => do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the units parameter control did not parse"
    session.read ⟨parsed⟩
  let first ← read empty "view (ℚ in Rings) along «fun.rings.multiplicative_monoid»()"
  let session ← empty.defineTerm `MFirst first
  let second ← read session "view (ℚ in Rings) along «fun.rings.multiplicative_monoid»()"
  let session ← session.defineTerm `MSecond second
  for (name, otherName, text) in #[
      (`MFirst, `MSecond, "3 in MFirstˣ"),
      (`MSecond, `MFirst, "3 in MSecondˣ")] do
    let selected ← read session name.toString
    let some selectedCategory := selected.category
      | throwError "the units parameter lost its selected category"
    let some selectedCarrier := selectedCategory.carrier
      | throwError "the units parameter lost its declared base comparison"
    let admitted ← read session text
    checkSelected admitted fun expression => do
      let scope ← get
      let context := scope.context
      let selections := scope.selections
      let findNamed := fun name => context.bindings.findM? fun binding =>
        return (← binding.expression.fvarId!.getUserName) == name
      let some original ← findNamed name
        | liftM (m := TermElabM) <| throwError "the units parameter lost its original binding"
      let some other ← findNamed otherName
        | liftM (m := TermElabM) <| throwError "the units parameter lost its distinct equal binding"
      unless original.expression != other.expression do
        liftM (m := TermElabM) <| throwError "the units parameter control does not have distinct equal native objects"
      checkOriginal #[original.expression, other.expression] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "the units parameter control does not have distinct equal native objects"
      let some selected ← SourceReadM.selection? expression
        | liftM (m := TermElabM) <| throwError "the units value lost its original selected binding"
      let some admission := selected.admission
        | liftM (m := TermElabM) <| throwError "the units value lost its original registered admission"
      let count ← liftM (m := MetaM) <| forallTelescope (← inferType admission.family)
        fun parameters _ => pure parameters.size
      unless admission.entry.id.raw == "obj.sets.units" &&
          admission.entry.admission == some ``CasCatalogue.Algebra.Units.admit &&
          admission.element == 1 && admission.arguments.size == count do
        liftM (m := TermElabM) <| throwError "the units admission changed its complete native argument positions"
      let parameter := admission.arguments[0]!
      let some parameterSelection ← SourceReadM.selection? parameter
        | liftM (m := TermElabM) <| throwError "the units admission lost its original selected parameter"
      let some category := parameterSelection.category
        | liftM (m := TermElabM) <| throwError "the units admission lost its complete selected category"
      unless parameterSelection.value == original.expression &&
          parameterSelection.value != other.expression do
        liftM (m := TermElabM) <| throwError "the units admission replaced its original parameter by an equal object"
      unless category.role == .object &&
          category.expression.syntacticEq selectedCategory.expression &&
          category.bundle == (← selectedCategory.bundle.inContext context) do
        liftM (m := TermElabM) <| throwError "the units admission changed its complete selected category"
      let some carrier := category.carrier
        | liftM (m := TermElabM) <| throwError "the units admission discarded its selected carrier"
      unless carrier.refs == selectedCarrier.refs &&
          carrier.target.syntacticEq selectedCarrier.target &&
          carrier.identifications == selectedCarrier.identifications &&
          carrier.actions == (← selectedCarrier.actions.mapM (·.inContext context)) &&
          carrier.comparisons == (← selectedCarrier.comparisons.mapM (·.inContext context)) do
        liftM (m := TermElabM) <| throwError "the units admission changed its actual carrier or base comparison"
      let datum := admission.arguments[admission.element]!
      let some datumSelection ← SourceReadM.selection? datum
        | liftM (m := TermElabM) <| throwError "the units datum lost its original selected point"
      let some point := datumSelection.pointOrigin
        | liftM (m := TermElabM) <| throwError "the units datum lost its transported source point"
      unless (point.target.find? (· == parameter)).isSome do
        liftM (m := TermElabM) <| throwError "the numeral point replaced its original selected carrier target"
      let comparisons ← carrier.comparisons.filterM fun comparison =>
        return (← whnfR (← inferType comparison)).isAppOfArity ``CategoryTheory.Iso 4
      let #[comparison] := comparisons
        | liftM (m := TermElabM) <| throwError "the units control lost its exact supplied carrier comparison"
      checkOriginal #[point.point, comparison] fun native => do
        unless native[0]!.containsConst
            (· == ``CasCatalogue.Algebra.NamedRings.ringNumeral) do
          throwError "the named rational base lost its declared numeral point"
        unless (native[0]!.find? fun term =>
            term.getAppFn.isConstOf ``CategoryTheory.Iso.symm &&
              term.getAppArgs.back? == some native[1]!).isSome do
          throwError "the numeral point did not use the supplied inverse carrier comparison"

      let .fvar parameterId := parameter
        | liftM (m := TermElabM) <| throwError "the units parameter lost its exact source binder"
      let some parameterBinding := context.bindings.find? (·.expression.fvarId! == parameterId)
        | liftM (m := TermElabM) <| throwError "the units parameter lost its original source identity"
      let forged := { parameterSelection with value := other.expression }
      let failure : Option Exception ← liftM (m := TermElabM) do
        try
          discard <| selections.merge
            (({} : SourceSelectionScope Expr).insert parameterBinding.id forged)
          pure none
        catch error => pure (some error)
      let some failure := failure
        | liftM (m := TermElabM) <| throwError "object provenance accepted a different equal source occurrence"
      unless (← failure.toMessageData.toString) ==
          "one source binding has incompatible retained selections" do
        liftM (m := TermElabM) <| throw failure


  for (name, otherName) in #[ (`MFirst, `MSecond), (`MSecond, `MFirst) ] do
    let equation ← read session s!"(3 in {name.toString}ˣ)⁻¹ = 1/3"
    checkSelected equation fun root => do
      let scope ← get
      let context := scope.context
      let selections := scope.selections
      let some original ← context.bindings.findM? fun binding =>
          return (← binding.expression.fvarId!.getUserName) == name
        | liftM (m := TermElabM) <| throwError "the quotient lost its original Monoid binding"
      let some other ← context.bindings.findM? fun binding =>
          return (← binding.expression.fvarId!.getUserName) == otherName
        | liftM (m := TermElabM) <| throwError "the quotient lost its distinct equal Monoid binding"
      let inspected ← visitNativeData (fun expression => do
        unless expression.isAppOfArity ``Eq 3 do return false
        let result := expression.getAppArgs[2]!
        let #[division] ← declaredApplications context selections
            ``CasCatalogue.Algebra.Units.divide result
          | liftM (m := TermElabM) <| throwError "the quotient lost its independently declared division"
        unless division.isAppOfArity ``CasCatalogue.Algebra.Units.divide 1 do
          liftM (m := TermElabM) <| throwError "the quotient changed its complete division parameter"
        let parameter := division.getAppArgs[0]!
        let hasOriginal ← visitNativeData (fun actual => pure (actual == original.expression)) parameter
        let hasOther ← visitNativeData (fun actual => pure (actual == other.expression)) parameter
        unless hasOriginal > 0 && hasOther == 0 do
          liftM (m := TermElabM) <| throwError "division replaced its original Monoid by an equal binding"
        let groups ← visitNativeData (fun group => do
          unless group.isAppOfArity ``CasCatalogue.Algebra.Units.groupUnits 1 do return false
          let groupParameter := group.getAppArgs[0]!
          unless (← originatesAt context selections groupParameter original.expression) &&
              !(← originatesAt context selections groupParameter other.expression) do
            liftM (m := TermElabM) <| throwError "the quotient group changed its actual original Monoid argument"
          let comparisons ← visitNativeData (fun comparison => do
            unless comparison.isAppOfArity ``CasCatalogue.Algebra.Units.unitsIdentification 1 do
              return false
            unless comparison.getAppArgs[0]! == groupParameter do
              liftM (m := TermElabM) <| throwError "division changed the original parameter of its carrier comparison"
            return true) result
          unless comparisons > 0 do
            liftM (m := TermElabM) <| throwError "division lost its supplied group-carrier comparison"

          let nativeTarget ← inferType expression.getAppArgs[1]!
          let originalTarget ← sourceDomain nativeTarget
          unless originalTarget.isAppOfArity ``CasCatalogue.Algebra.Units.units 1 do
            liftM (m := TermElabM) <| throwError "the inverse result lost its authored native units domain"
          unless originalTarget.getAppArgs[0]! == groupParameter do
            liftM (m := TermElabM) <| throwError "the native units domain changed its actual admission parameter"
          unless (← sourceObjectReference? context selections nativeTarget).isNone do
            liftM (m := TermElabM) <| throwError "the native units control retained a surface object reference"
          let some selectedAdmission ← sourceAdmissionDomain? nativeTarget
            | liftM (m := TermElabM) <| throwError "the exact native units domain did not select its declared admission"
          unless selectedAdmission.id.raw == "obj.sets.units" &&
              selectedAdmission.declaration == ``CasCatalogue.Algebra.Units.units &&
              selectedAdmission.admission == some ``CasCatalogue.Algebra.Units.admit do
            liftM (m := TermElabM) <| throwError "the native units domain selected another admission row"
          return true) parameter
        unless groups > 0 do
          liftM (m := TermElabM) <| throwError "division lost the declared group of the original units set"
        return true) root
      unless inspected == 1 do
        liftM (m := TermElabM) <| throwError "the original units division did not remain an equality"


  let some firstCategory := first.category
    | throwError "the missing-comparison control lost its selected category"
  let some firstCarrier := firstCategory.carrier
    | throwError "the missing-comparison control lost its original carrier route"
  let categoryTerm ← empty.elaborateScoped Syntax.missing do
    discard <| empty.readTerm first
    firstCategory.bundle.inContext (← get).context
  let withoutComparison ← first.inCategory firstCategory.expression categoryTerm
    firstCategory.role
    (some { firstCarrier with comparisons := #[], identifications := #[] })
    firstCategory.limit
  let unpresented ← session.defineTerm `MWithoutComparison withoutComparison
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| read unpresented "3 in MWithoutComparisonˣ"
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "a Monoid numeral was inferred without its supplied base comparison"
  unless (← failure.toMessageData.toString) ==
      "no declared source point numeral was admitted in the supplied domain" do throw failure
  let failure : Option Exception ← withoutModifyingState do
    try
      discard <| read session "0 in MFirstˣ"
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "units admission accepted zero without its prescribed evidence"
  let message ← failure.toMessageData.toString
  unless CasCatalogue.Exception.stratum? failure == some .invalid &&
      (message.splitOn "not established by the evidence of").length > 1 do
    throw failure

private def numeralAbsenceFailure (action : TermElabM α) : TermElabM Exception := do
  let failure : Option Exception ← withoutModifyingState do
    try
      discard action
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "a rejected numeral reading was reported as absence or success"
  return failure



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let context ← ContextTelescope.capture #[]
  let initial : SourceReadScope := { identities, context, selections := {} }
  let noCategory : FVarId → TermElabM (Option NativeSourceCategory) := fun _ => pure none
  let originalLiteral : SourceReadM Unit := do
    unless (← sourceNumeral? noCategory 4 (mkConst ``Nat)) == some (mkNatLit 4) do
      liftM (m := TermElabM) <| throwError "the optional numeral producer changed the native natural literal"
  originalLiteral.runK initial fun _ _ => pure ()
  let evidence : Term ← `(term| rfl)
  let rejected ← numeralAbsenceFailure <|
    (sourceNumeral? noCategory 4 (mkConst ``Nat) #[evidence]).runK initial fun _ _ => pure ()
  unless (← rejected.toMessageData.toString) ==
      "a natural parameter literal has no domain obligations" do throw rejected

  let empty ← SourceSession.empty identities
  let native : String → TermElabM Term := fun text => do
    let .ok parsed := Parser.runParserCategory (← getEnv) `term text
      | throwError "the native numeral absence control did not parse"
    return ⟨parsed⟩
  let session ← empty.assume `M (← native "MonCat.{0}")
  let object ← session.term (← native "M")
  let #[category] := (← semanticState).categories.filter (·.id == CategoryId.monoids)
    | throwError "the numeral absence control lost its independently registered Monoid category"
  let bundle ← session.constant Syntax.missing category.declaration [.zero]
  let object ← object.inCategory category.expression bundle
  let session ← session.defineTerm `S object
  let type ← session.term (← native "(S : Type)")
  session.withTerm type fun context selections target => do
    let some selectedEntry := session.context.entries.find? (·.userName == `S)
      | throwError "the numeral absence control lost its original selected Monoid"
    let some selectedBinding := context.bindings.find? (·.id == selectedEntry.id)
      | throwError "the numeral absence control lost its exact selected Monoid binder"
    let some selected := session.categoryFor selectedBinding.id
      | throwError "the numeral absence control lost its actual category selection"
    unless selected.carrier.isNone && selected.limit.isNone do
      throwError "the absence control acquired a supplied carrier comparison or limit"
    let bundle ← selected.bundle.inContext context
    let categoryOf : FVarId → TermElabM (Option NativeSourceCategory) := fun id =>
      pure (if id == selectedBinding.expression.fvarId! then
        some (⟨selected.role, selected.expression, bundle, none, none⟩ : NativeSourceCategory)
      else none)
    let scope : SourceReadScope := { identities, context, selections }
    let absent : SourceReadM Unit := do
      unless (← sourceNumeral? categoryOf 4 target).isNone do
        liftM (m := TermElabM) <| throwError "the selected Monoid acquired an undeclared numeral"
    absent.runK scope fun _ _ => pure ()
    let failure ← numeralAbsenceFailure <|
      (sourceNumeral categoryOf 4 target).runK scope fun _ _ => pure ()
    unless (← failure.toMessageData.toString) ==
        "no declared source point numeral was admitted in the supplied domain" do throw failure
  let source : TSyntax `cas_term ← `(cas_term| 4)
  let failure ← numeralAbsenceFailure <|
    session.read source (some type.source) type.selections
  unless (← failure.toMessageData.toString) ==
      "no declared source point numeral was admitted in the supplied domain" do throw failure




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let context ← ContextTelescope.capture #[]
  let initial : SourceReadScope := { identities, context, selections := {} }
  let noCategory : FVarId → TermElabM (Option NativeSourceCategory) := fun _ => pure none
  let evidence : Term ← `(term| rfl)
  let observed : IO.Ref (Option Exception) ← IO.mkRef none
  let included := sourceIncludedNumeral (mkConst ``Int) fun source =>
    SourceReadM.tryCatch (sourceNumeral? noCategory 4 source #[evidence]) fun error => do
      observed.set (some error)
      liftM (m := TermElabM) <| throw error
  let failure ← numeralAbsenceFailure <|
    included.runK initial fun _ _ => pure ()
  let some original ← observed.get
    | throwError "the inclusion error control did not reach an original numeral producer"
  unless (← failure.toMessageData.toString) == (← original.toMessageData.toString) &&
      CasCatalogue.Exception.stratum? failure == CasCatalogue.Exception.stratum? original do
    throwError "inclusion search replaced a rejected chosen numeral interpretation"
