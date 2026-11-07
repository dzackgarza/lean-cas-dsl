module

import CasRuntime.Literal
public meta import Lean.Elab.Command
meta import CasRuntime.Literal

open Lean Meta Elab Term CasCompiler CasRuntime

private def literalSource (term : Term) : TermElabM SourceLayout := do
  let context ← ContextTelescope.capture #[]
  SourceLayout.ofTerm (← context.close (← elabTermAndSynthesize term none))

private def reject (source : SourceLayout) (packet : Json) (expected : String) : MetaM Unit := do
  let failure : Option Exception ← try
    discard <| ScalarLiteral.check source packet
    pure none
  catch error => pure (some error)
  let some failure := failure | throwError "a scalar packet violated its source representation"
  unless (← failure.toMessageData.toString).startsWith expected do throw failure

run_cmd Lean.Elab.Command.liftTermElabM do
  let natural ← literalSource (← `((7 : Nat)))
  let integer ← literalSource (← `((-7 : Int)))
  let rational ← literalSource (← `(((1 : Rat) / 2)))
  let finite ← literalSource (← `((Fin.last 3)))
  let dependent ← literalSource (← `((⟨3, Fin.last 3⟩ : Σ n : Nat, Fin (n + 1))))
  let list ← literalSource (← `(([1, 2] : List Nat)))
  let boolean ← literalSource (← `((true : Bool)))
  let valid : Array (SourceLayout × Json) := #[
    (natural, toJson (0 : Nat)), (integer, toJson (-19 : Int)),
    (rational, .arr #[toJson (-2 : Int), toJson (3 : Nat)]),
    (rational, .arr #[toJson (0 : Int), toJson (1 : Nat)]),
    (finite, toJson (0 : Nat)), (finite, toJson (3 : Nat)),
    (dependent, .arr #[toJson (3 : Nat), toJson (3 : Nat)]),
    (list, .arr #[toJson (3 : Nat), toJson (4 : Nat)]),
    (boolean, Json.mkObj [("ctor", .str "false"), ("args", .arr #[])])]
  for (source, packet) in valid do
    unless (← ScalarLiteral.check source packet) == .checked do
      throwError "the native scalar representation was not checked"
  reject natural (.str "7") "a scalar literal requires a natural JSON number"
  reject integer (.arr #[]) "a scalar literal requires an integer JSON number"
  for packet in #[Json.arr #[toJson (1 : Int), toJson (0 : Nat)],
      .arr #[toJson (2 : Int), toJson (4 : Nat)],
      .arr #[toJson (0 : Int), toJson (2 : Nat)]] do
    reject rational packet "a scalar literal violates its declared representation constraint"
  reject finite (toJson (4 : Nat))
    "a scalar literal violates its declared representation constraint"
  reject dependent (.arr #[toJson (3 : Nat), toJson (4 : Nat)])
    "a scalar literal violates its declared representation constraint"
  reject list (.arr #[.str "3"]) "a scalar literal requires a natural JSON number"
  let function ← literalSource (← `((Nat.succ)))
  let type ← literalSource (← `((Nat)))
  for source in #[function, type] do
    unless (← ScalarLiteral.check source .null) == .notScalar do
      throwError "scalar validation reconstructed a callable or type-valued result"
  let native := CasCatalogue.Backend.ComputationalValue.encode (.opaque "actual-token")
  unless (← ScalarLiteral.check natural native) == .notScalar do
    throwError "scalar validation interpreted a native export as a literal"
