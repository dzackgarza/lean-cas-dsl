module

import CasCompiler.Surface
public meta import Lean.Elab.Command
meta import CasCompiler.Surface

namespace CasCompiler.SourceArgumentIdentityTests

open Lean Meta

-- Native target positions determine formal slots, including reordered parameters. Equal
-- definitions do not make their independently supplied input occurrences interchangeable.
-- These controls perform source matching only; no provider or mathematical value is run.
run_cmd Lean.Elab.Command.liftTermElabM do
  let typeSort := mkSort (.succ .zero)
  let product := mkConst ``Prod [.zero, .zero]
  withLetDecl `First typeSort (mkConst ``Nat) fun first => do
    withLetDecl `Second typeSort (mkConst ``Nat) fun second => do
      unless ← isDefEq first second do
        throwError "the distinct-source control lost its convertible native definitions"
      let formal ← mkFreshExprMVar typeSort
      let rejected ← alignSourceArguments? ``Prod #[formal]
        (mkApp2 product formal formal) (mkApp2 product first second)
      unless rejected.isNone && (← instantiateMVars formal).isMVar do
        throwError "repeated formal accepted different equal source inputs or leaked its failed match"

      let left ← mkFreshExprMVar typeSort
      let right ← mkFreshExprMVar typeSort
      let some retained ← alignSourceArguments? ``Prod #[left, right]
          (mkApp2 product right left) (mkApp2 product first second)
        | throwError "native target positions did not specialize reordered formals"
      unless retained == #[some second, some first] do
        throwError "native target matching replaced the original reordered source arguments"

    let formal ← mkFreshExprMVar typeSort
    let some retained ← alignSourceArguments? ``Prod #[formal]
        (mkApp2 product formal formal) (mkApp2 product first first)
      | throwError "one repeated original source input was rejected"
    unless retained == #[some first] do
      throwError "the repeated original input lost its actual source expression"

    withLetDecl `Alias typeSort first fun aliasType => do
      let formal ← mkFreshExprMVar typeSort
      let some retained ← alignSourceArguments? ``Prod #[formal]
          (mkApp2 product formal formal) (mkApp2 product aliasType first)
        | throwError "an explicit native alias lost its original input witness"
      unless retained == #[some aliasType] do
        throwError "the alias control replaced its original supplied expression"

    -- A retained-value marker is an admission boundary even when its body is the same
    -- native input. The matcher cannot turn two such marks into an alias by erasing them.
    let markedFirst := Expr.mdata
      (KVMap.empty.setNat `CasCompiler.lower.value 1) first
    let markedSecond := Expr.mdata
      (KVMap.empty.setNat `CasCompiler.lower.value 2) first
    let formal ← mkFreshExprMVar typeSort
    let rejected ← alignSourceArguments? ``Prod #[formal]
      (mkApp2 product formal formal) (mkApp2 product markedFirst markedSecond)
    unless rejected.isNone && (← instantiateMVars formal).isMVar do
      throwError "repeated formal erased conflicting retained-value boundaries"

-- A projected alias keeps the exact original parent and native field path. Equal sibling
-- fields do not establish that path; only the actual supplied projection does.
run_cmd Lean.Elab.Command.liftTermElabM do
  let natural := mkConst ``Nat
  let pair := mkApp2 (mkConst ``Prod [.zero, .zero]) natural natural
  let pairValue ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
  withLetDecl `pair pair pairValue fun input => do
    let selected := mkProj ``Prod 0 input
    withLetDecl `selected natural selected fun selectedAlias => do
      let formal ← mkFreshExprMVar natural
      let equality := mkConst ``Eq [.succ .zero]
      let some retained ← alignSourceArguments? ``Eq #[formal]
          (mkApp3 equality natural formal formal)
          (mkApp3 equality natural selectedAlias selected)
        | throwError "an exact native projection alias lost its original parent/path"
      unless retained == #[some selectedAlias] do
        throwError "native projection alignment changed its supplied alias expression"
      let other := mkProj ``Prod 1 input
      unless ← isDefEq selected other do
        throwError "the sibling-field control lost its convertible native fields"
      let formal ← mkFreshExprMVar natural
      let rejected ← alignSourceArguments? ``Eq #[formal]
        (mkApp3 equality natural formal formal) (mkApp3 equality natural selected other)
      unless rejected.isNone && (← instantiateMVars formal).isMVar do
        throwError "repeated formal accepted another native input field"

-- The complete native constructor telescope includes dependent arguments and proof-only
-- positions. Actual data is retained, while repeated proofs use native proof irrelevance.
run_cmd Lean.Elab.Command.liftTermElabM do
  let natural := mkConst ``Nat
  let family ← withLocalDeclD `n natural fun n =>
    mkLambdaFVars #[n] (mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) n))
  withLocalDeclD `n natural fun n => do
    withLocalDeclD `point (mkApp family n) fun point => do
      let formalNumber ← mkFreshExprMVar natural
      let formalPoint ← mkFreshExprMVar (mkApp family formalNumber)
      let declared ← mkAppOptM ``Sigma.mk
        #[some natural, some family, some formalNumber, some formalPoint]
      let original ← mkAppOptM ``Sigma.mk
        #[some natural, some family, some n, some point]
      let some retained ← alignSourceArguments? ``Sigma.mk #[formalNumber, formalPoint]
          declared original
        | throwError "complete native dependent parameters did not specialize"
      unless retained == #[some n, some point] do
        throwError "native specialization changed an original dependent argument"
  withLocalDeclD `h (mkConst ``True) fun first => do
    withLocalDeclD `k (mkConst ``True) fun second => do
      let formal ← mkFreshExprMVar (mkConst ``True)
      let constructor := mkConst ``And.intro
      let declared := mkApp4 constructor (mkConst ``True) (mkConst ``True) formal formal
      let original := mkApp4 constructor (mkConst ``True) (mkConst ``True) first second
      unless (← alignSourceArguments? ``And.intro #[formal] declared original).isSome do
        throwError "native proof-only repetition was treated as a computational source choice"

end CasCompiler.SourceArgumentIdentityTests
