/-
The `sage-categories` leaf probes as notebook specimens (`cc-probe-corpus`). Each specimen runs
through the public DSL surface only: `let … in …` ascriptions, method calls and `assert`.

## The ring diamond (CC-RESOLVE, CC-COHERE; #53 §9)

A ring reaches sets along its multiplicative port `Ring → Mon → Semigrp → Magma → Set` and along
its additive port `Ring → AddGrp → Grp → Mon → …`. The two routes carry different operations, so
`is_commutative` stays ambiguous (asserted in `Abelian.lean`); at `Set` they are identified by the
registered comparison `cmp.rings.carrier`, so `cardinality` resolves and is computed by the
registered table actions along the route.
-/
import CasDsl

namespace CasDslTests.ProbeCorpus

open Lean Elab Command
open CasDsl

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

let R := ZZ/4 in Rings
let F := ZZ/5 in Rings

assert R.cardinality() = 4
assert F.cardinality() = 5
assert R.cardinality() ≠ 5

run_cmd do
  let env ← getEnv
  -- the two ports are one route to `Set` only by the registered comparison, which the audit names
  match ← Semantic.explain env "cat.rings" none (.domainObj (.mod 4)) "cardinality" with
  | .ok text =>
      for needle in ["identified:  the other routes by [cmp.rings.carrier]",
          "composed Lean-native actions"] do
        unless contains text needle do
          throwError s!"the audit of R.cardinality() does not mention {needle}:\n{text}"
  | .error e => throwError s!"the audit of R.cardinality() failed: {e}"
  -- …and they stay distinct where they carry different operations
  match ← runEval env (.method (.ref `R) `is_commutative #[]) with
  | .error e =>
      unless contains e.render "ambiguous" && contains e.render "fun.rings.additive_group" &&
          contains e.render "fun.rings.multiplicative_monoid" do
        throwError s!"R.is_commutative() did not report both ports: {e.render}"
  | .ok v => throwError s!"R.is_commutative() was answered ({v.render}) without choosing a port"

end CasDslTests.ProbeCorpus
