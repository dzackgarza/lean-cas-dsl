module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData
public import Lean.Meta.Structure

public section

namespace CasCompiler

open Lean Meta


def selectedField (selection projection : Name) (owner value : Expr) : SourceSelection Expr :=
  { value, field := some ⟨selection, projection, owner, false⟩ }


def selectedFieldAt (selection projection : Name) (owner value : Expr) :
    MetaM (SourceSelection Expr) := do
  unless !selection.isAnonymous && !projection.isAnonymous do
    throwError "an owned source field requires its original selection and projection"
  check owner
  check value
  return selectedField selection projection owner value



def selectRecordActions [Monad m] [MonadLiftT MetaM m] (selection : Name)
    (record : SourceSelection Expr)
    (select : SourceSelection Expr → Option Expr → m Expr) : m Expr := do
  liftM (m := MetaM) do
    unless !selection.isAnonymous do
      throwError "a selected interface requires its original construction identity"
    let type ← whnf (← inferType record.value)
    let .const owner _ := type.getAppFn
      | throwError "a selected interface must be a record"
    let some info := getStructureInfo? (← getEnv) owner
      | throwError "a selected interface must have declared fields"
    for field in info.fieldNames, index in [:info.fieldNames.size] do
      unless (info.getProjFn? index).isSome do
        throwError "a selected interface lost its projection"
      check (← mkProjection record.value field)
  select record none

end CasCompiler
