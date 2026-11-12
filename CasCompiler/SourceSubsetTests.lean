module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

/- Power-object forms read through the registered power object of `Sets`: the subset-literal
denotation, membership, transpose, image and extent; typing questions settle at reading. -/

private def statements (session : SourceSession) (text : String) :
    TermElabM (Array SourceStatement × SourceSession) := do
  let file ← SourceFile.parse "source-subsets.cas" text
  let mut session := session
  let mut formed := #[]
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "the source statement control changed its parsed category"
    let statement ← file.withContext (session.readStatement statement)
    if let .definition next _ := statement then session := next
    formed := formed.push statement
  return (formed, session)

private def denotes (term : SourceTerm) (declarations : Array Name) : MetaM Bool :=
  term.source.withOpen fun _ expression => do
    let expression ← instantiateMVars expression
    return declarations.all fun declaration => expression.containsConst (· == declaration)

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let (formed, _) ← statements empty
    "let A := {1, 2, 3} in 𝒫(ℤ)\nlet B := {3, 4} in 2^ℤ\n\
     assert 2 ∈ A\nassert 4 ∉ A\nassert A ∪ B = {1, 2, 3, 4}\nassert A ⊆ A ∪ B\n\
     let S := {n ∈ ℤ | n² ≤ 4}\nlet E := {2n | n ∈ ℕ}\n\
     assert S in 𝒫(ℤ)\nassert -3 ∈ ℤ\nassert |A| = 3\n"
  let literal := ``CasCatalogue.Foundation.FiniteSubsetLiterals.literal
  let powerSets : Name := `CasCatalogue.Foundation.PowerSets
  let expectations : Array (Nat × Array Name) := #[
    (0, #[literal]), (1, #[literal]),
    (2, #[powerSets ++ `member]),
    (3, #[``Not, powerSets ++ `member]),
    (4, #[powerSets ++ `union, literal]),
    (5, #[powerSets ++ `subset, powerSets ++ `union]),
    (6, #[powerSets ++ `transpose, ``CasCatalogue.Foundation.PowerSets.le]),
    (7, #[powerSets ++ `image]),
    (10, #[powerSets ++ `extent])]
  for (index, declarations) in expectations do
    let some statement := formed[index]? | throwError "a subset statement was not formed"
    let term := match statement with
      | .definition _ value | .question value | .implemented value | .settled value => value
    unless ← denotes term declarations do
      throwError "subset statement {index} lost its registered power-object declaration"
  for index in [2, 3, 4, 5, 10] do
    unless formed[index]? matches some (SourceStatement.question _) do
      throwError "subset statement {index} is not a proposition"
  for index in [8, 9] do
    unless formed[index]? matches some (SourceStatement.settled _) do
      throwError "typing statement {index} was not settled by its reading"
  for source in #["let C := {1, 2}", "let D := {x ∈ ℤ | x}"] do
    let rejected ← try
      discard <| statements empty source
      pure false
    catch _ => pure true
    unless rejected do throwError "an untyped subset form was admitted: {source}"
