/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Elab Command Term
open CasCatalogue CasCatalogue.Realize

/- Engineering regression: a term recovered from a shared identity DAG must have exactly the
same standalone serialization as direct encoding, including binders and proof quotienting. -/
run_cmd liftTermElabM do
  let term ← elabTermAndSynthesize (← `(fun (n : Nat) (_h : n = n) => n)) none
  let distractor ← elabTermAndSynthesize (← `(Nat.succ 3)) none
  let expected ← termIdentity term
  let source ← TermTable.new
  discard <| source.encode distractor
  let sourceRoot ← source.encode term
  let target ← TermTable.new
  let remap ← TermRemap.new source target
  let targetRoot ← remap.encode sourceRoot
  let actual ← target.finish (toJson targetRoot)
  unless actual == expected do
    throwError "remapping a shared identity DAG changed the standalone term identity"
  let direct ← TermTable.new
  let directTerm ← direct.encode term
  let directDistractor ← direct.encode distractor
  let expectedTable ← direct.finish (Json.arr #[toJson directTerm, toJson directDistractor])
  let reordered ← TermTable.new
  let reorder ← TermRemap.new source reordered
  let reorderedTerm ← reorder.encode sourceRoot
  let sourceDistractor ← source.encode distractor
  let reorderedDistractor ← reorder.encode sourceDistractor
  let actualTable ← reordered.finish
    (Json.arr #[toJson reorderedTerm, toJson reorderedDistractor])
  unless actualTable == expectedTable do
    throwError "remapping identity roots changed direct-encoding insertion order"
