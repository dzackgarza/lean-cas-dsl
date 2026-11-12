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
    let term := match statement with
      | .definition _ value | .question value | .implemented value | .settled value => value
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
