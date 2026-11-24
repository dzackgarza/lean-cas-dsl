module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

/- `R[x]` reads the polynomial object, and its variable `x` is the registered generator: as a
free variable of a term that writes the ring, and as the bound variable of `x ↦ e in R[x]`. -/

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
    let evaluated ← term.source.withOpen fun _ expression => do
      return (← instantiateMVars expression).containsConst (· == evaluation)
    unless evaluated do throwError "a polynomial value was not applied by its registered evaluation"
  for statement in formed.extract 0 3 do
    let term ← match statement with
      | .definition _ value | .question value | .implemented value => pure value
      | .settled values =>
        let #[value] := values
          | throwError "an individual ring typing judgement did not retain exactly one term"
        pure value
    let uses ← term.source.withOpen fun _ expression => do
      return (← instantiateMVars expression).containsConst (· == generator)
    unless uses do throwError "a ring variable was not read as the registered generator"
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

/- An element of a named set read in a larger one goes through the registered maps between them:
inclusions (`ℕ ⊆ ℤ`) and the target's constants (`ℚ ↪ ℚ[x]`). -/
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
  let uses := fun (index : Nat) (declaration : Name) => do
    let some value := values[index]? | throwError "a coercion control was not read"
    value.source.withOpen fun _ expression => do
      return (← instantiateMVars expression).containsConst (· == declaration)
  unless ← uses 1 ``CasCatalogue.Algebra.NumberSystems.naturalsIntegers do
    throwError "a natural was not read in ℤ through the registered inclusion"
  unless ← uses 2 ``CasCatalogue.Algebra.Polynomials.coefficients do
    throwError "a natural was not read in ℚ[x] through the registered constants"

-- Read the complete unchanged B0 unit assertion through its original source positions.
-- This checks source formation only; the full public consumer still owes its computation.
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
    proposition.source.withOpen fun _ expression => do
      unless expression.isAppOfArity ``Eq 3 do
        throwError "the original unit equality was not retained"
    found := true
  unless found do throwError "the complete original unit assertion is absent"

-- Equal native monoids retain their separately selected source occurrences and complete
-- carrier comparisons when they become parameters of the declared units admission.
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
    admitted.source.withOpen fun bindings expression => do
      let findNamed := fun name => bindings.findM? fun binding =>
        return (← binding.expression.fvarId!.getUserName) == name
      let some original ← findNamed name
        | throwError "the units parameter lost its original binding"
      let some other ← findNamed otherName
        | throwError "the units parameter lost its distinct equal binding"
      unless original.expression != other.expression &&
          (← isDefEq original.expression other.expression) do
        throwError "the units parameter control does not have distinct equal native objects"
      let some reference := expression.find? fun term =>
          match term with
          | .mdata data _ => data.getName `CasCompiler.source.kind ==
                ``CasCatalogue.ObjectEntry.admission &&
              data.getString `CasCompiler.source.id == "obj.sets.units"
          | _ => false
        | throwError "the units value lost its original registered admission"
      let .mdata data body := reference
        | throwError "the units admission has no source reference"
      unless data.getName `CasCompiler.source.declaration ==
          ``CasCatalogue.Algebra.Units.admit &&
          data.getNat `CasCompiler.source.element == 1 &&
          body.getAppArgs.size == data.getNat `CasCompiler.source.admissionArguments do
        throwError "the units admission changed its complete native argument positions"
      let parameter := body.getAppArgs[0]!
      let some (category, object) ← sourceObjectOrigin? parameter
        | throwError "the units admission lost its original selected parameter"
      unless object == original.expression && object != other.expression do
        throwError "the units admission replaced its original parameter by an equal object"
      let context ← ContextTelescope.capture bindings
      unless category.role == .object &&
          category.expression.syntacticEq selectedCategory.expression &&
          category.bundle == (← selectedCategory.bundle.inContext context) do
        throwError "the units admission changed its complete selected category"
      let some carrier := category.carrier
        | throwError "the units admission discarded its selected carrier"
      unless carrier.refs == selectedCarrier.refs &&
          carrier.target.syntacticEq selectedCarrier.target &&
          carrier.identifications == selectedCarrier.identifications &&
          carrier.actions == (← selectedCarrier.actions.mapM (·.inContext context)) &&
          carrier.comparisons == (← selectedCarrier.comparisons.mapM (·.inContext context)) do
        throwError "the units admission changed its actual carrier or base comparison"
      let datum := body.getAppArgs[data.getNat `CasCompiler.source.element]!
      let some point ← sourcePointOrigin? datum
        | throwError "the units datum lost its transported source point"
      unless (point.target.find? (· == parameter)).isSome do
        throwError "the numeral point replaced its original selected carrier target"
      unless point.point.containsConst
          (· == ``CasCatalogue.Algebra.NamedRings.ringNumeral) do
        throwError "the named rational base lost its declared numeral point"
      let comparisons ← carrier.comparisons.filterM fun comparison =>
        return (← whnfR (← inferType comparison)).isAppOfArity ``CategoryTheory.Iso 4
      let #[comparison] := comparisons
        | throwError "the units control lost its exact supplied carrier comparison"
      unless (point.point.find? fun term =>
          term.getAppFn.isConstOf ``CategoryTheory.Iso.symm &&
            term.getAppArgs.back? == some comparison).isSome do
        throwError "the numeral point did not use the supplied inverse carrier comparison"
      -- Replacing only the typed owner field by an equal-valued different source is invalid.
      let .mdata mark fields := parameter
        | throwError "the units parameter lost its typed object wrapper"
      unless fields.isAppOfArity ``Function.const 4 do
        throwError "the units parameter lost its complete category field"
      let ownerField := fields.getAppArgs[2]!
      unless ownerField.isAppOfArity ``Function.const 4 do
        throwError "the units parameter lost its original object field"
      let wrongOwner := mkAppN ownerField.getAppFn
        (ownerField.getAppArgs.set! 3 other.expression)
      let forged := Expr.mdata mark
        (mkAppN fields.getAppFn (fields.getAppArgs.set! 2 wrongOwner))
      let failure : Option Exception ← withoutModifyingState do
        try
          discard <| sourceObjectOrigin? forged
          pure none
        catch error => pure (some error)
      let some failure := failure
        | throwError "object provenance accepted a different equal source occurrence"
      unless (← failure.toMessageData.toString) ==
          "the source object provenance changed its original parameter" do throw failure
  -- The same native Monoid without its supplied base comparison cannot acquire
  -- a numeral from the convertible rational carrier or a stronger structural owner.
  let some firstCategory := first.category
    | throwError "the missing-comparison control lost its selected category"
  let some firstCarrier := firstCategory.carrier
    | throwError "the missing-comparison control lost its original carrier route"
  let withoutComparison := { first with category := some { firstCategory with
    carrier := some { firstCarrier with comparisons := #[], identifications := #[] } } }
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
