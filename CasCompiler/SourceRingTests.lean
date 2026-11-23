module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceSnapshot
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceSnapshot
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

/- A written polynomial variable remains source data when the value never uses it.
The original definition keeps its own convention after an alias and a shadowing definition. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-unused-ring-variable.cas"
    "let p := 1 in ℚ[x]\nlet pAlias := p\nlet p := 2 in ℚ[y]\nassert pAlias = pAlias\n"
  let mut session ← SourceSession.empty identities
  let mut definitions : Array (ContextEntry × SourceTerm × Json) := #[]
  let mut question : Option SourceTerm := none
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the unused ring variable control changed its parsed category"
    match ← file.withContext (session.readStatement statement) with
    | .definition next value =>
      let some entry := next.context.entries.back?
        | throwError "the ring definition lost its source binding"
      let prepared := SourceSnapshot.snapshot next value (some entry)
      definitions := definitions.push (entry, value, prepared)
      session := next
    | .question value => question := some value
    | _ => throwError "the unused ring variable control changed its statement kind"
  let #[(original, value, prepared), (_, _, _), (shadow, _, _)] := definitions
    | throwError "the ring control did not retain its three definitions"
  unless value.source.context.entries.isEmpty &&
      !value.source.expression.containsConst (· == ``CasCatalogue.Algebra.Polynomials.generator) do
    throwError "the supposedly unused generator entered the original native term or context"
  let #[written] := session.ringsFor original.id
    | throwError "the reader lost the original written polynomial variable"
  unless written.name == `x && original.id != shadow.id && original.userName == shadow.userName do
    throwError "the public reader did not preserve the intended variable and shadowed binding"
  let result := prepared.getObjValD "resultBinding"
  let .ok #[ring] := result.getObjValAs? (Array Json) "ringVariables"
    | throwError "the definition snapshot omitted its unused written variable"
  unless result.getObjValD "id" == ContextSnapshot.bindingJson original.id &&
      ring.getObjValD "name" == toJson "x" &&
      ring.getObjValD "nativeName" == CasTools.NativeExpression.nameJson `x &&
      (ring.getObjVal? "index").toOption == some Json.null do
    throwError "the definition snapshot changed the original ring variable or binding"
  let .ok nodes := CasTools.NativeExpression.decodeNodes (prepared.getObjValD "nativeExpressions")
    | throwError "the ring snapshot lost its native expression graph"
  let carrier := ring.getObjValD "carrier"
  let .ok expression := carrier.getObjValAs? Nat "expression"
    | throwError "the written variable lost its complete native carrier"
  let .ok type := carrier.getObjValAs? Nat "type"
    | throwError "the written variable lost its carrier type"
  unless nodes[expression]? == some written.carrier.expression &&
      nodes[type]? == some written.carrier.type do
    throwError "the ring snapshot replaced the reader's actual carrier or its type"
  unless SourceSnapshot.snapshot session value (some original) == prepared do
    throwError "later aliasing or shadowing changed the original prepared source snapshot"
  let some asked := question | throwError "the alias question was not read"
  let observed := SourceSnapshot.snapshot session asked none
  let .ok rings := observed.getObjValAs? (Array Json) "ringVariables"
    | throwError "the later source snapshot lost its binding-indexed ring conventions"
  for (entry, expected) in #[(original, "x"), (shadow, "y")] do
    let some row := rings.find? (·.getObjValD "id" == ContextSnapshot.bindingJson entry.id)
      | throwError "the later snapshot omitted a shadowed source binding"
    let .ok #[ring] := row.getObjValAs? (Array Json) "variables"
      | throwError "the later snapshot omitted a binding's written variable"
    unless ring.getObjValD "name" == toJson expected do
      throwError "the later snapshot paired a written variable with the other shadowed binding"
