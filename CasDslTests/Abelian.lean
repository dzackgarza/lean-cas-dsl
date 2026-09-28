/-
#53 §12 through the notebook surface: commutativity and abelianness
(`cc-dsl-migration`).

`G.is_abelian()` is a property query on a point of `Groups`. It resolves, by
the registry's one resolver, to the commutativity classifier of magmas pulled
back along the multiplicative route `Groups → Monoids → Semigroups → Magmas`,
and is answered by the registered decision procedure of that classifier on
the route's image. Asserted here:

1. `is_abelian` introduces no predicate of its own: its route ends at the
   classifier `clf.magmas.commutative`, and it agrees with `is_commutative`;
2. the audit (`#explain_route`) names that owner and the route;
3. on rings the additive and the multiplicative commutativity are distinct
   routes: `R.is_commutative()` is an ambiguity listing both ports;
4. the Boolean is a decision procedure's answer (the audit names the decider,
   and a false answer is a refutation, `Dihedral(3)`);
5. a group-specific backend call is a fused realization of the same composite,
   selected explicitly and never silently substituted.
-/
import CasDsl

namespace CasDslTests.Abelian

open Lean Elab Command
open CasDsl

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

let G := ZZ/3 in Groups
let H := Dihedral(3) in Groups
let R := ZZ/4 in Rings

private def answer (env : Environment) (x : Name) (m : Name) :
    IO (Except String String) := do
  match ← runEval env (.method (.ref x) m #[]) with
  | .ok d => return .ok d.render
  | .error e => return .error e.render

run_cmd do
  let env ← getEnv
  -- (1), (4): decided values, the refutation included; `is_abelian` and `is_commutative` agree
  for (x, m, expected) in [(`G, `is_abelian, "true"), (`H, `is_abelian, "false"),
      (`G, `is_commutative, "true"), (`H, `is_commutative, "false")] do
    match ← answer env x m with
    | .ok v =>
        unless v == expected do throwError s!"{x}.{m}() = {v}, expected {expected}"
    | .error e => throwError s!"{x}.{m}() failed: {e}"
  -- (1), (2), (4): the owner is the commutativity classifier of magmas, reached along the
  -- multiplicative route, answered by a decision procedure
  match ← Semantic.explain env "cat.groups" none (.dihedralGroup 3) "is_abelian" with
  | .ok text =>
      for needle in ["prop.is_abelian", "clf.magmas.commutative",
          "cat.groups --fun.groups.monoid--> cat.monoids --fun.monoids.semigroup--> \
cat.semigroups --forget[clf.magmas.associative]--> cat.magmas",
          "dec.magmas.commutative.table", "decision procedure"] do
        unless contains text needle do
          throwError s!"the audit of H.is_abelian() does not mention {needle}:\n{text}"
  | .error e => throwError s!"the audit of H.is_abelian() failed: {e}"
  -- (3): additive and multiplicative commutativity of a ring are two routes, not one
  match ← answer env `R `is_commutative with
  | .error e =>
      unless contains e "ambiguous" && contains e "fun.rings.multiplicative_monoid" &&
          contains e "fun.rings.additive_group" do
        throwError s!"R.is_commutative() did not report both ports: {e}"
  | .ok v => throwError s!"R.is_commutative() was answered ({v}) without choosing a port"
  -- `is_abelian` is an alias on groups only: a ring does not answer it
  match ← answer env `R `is_abelian with
  | .error _ => pure ()
  | .ok v => throwError s!"R.is_abelian() was answered ({v}); the alias belongs to groups"

#explain_route H.is_abelian()

/-! (5): the fused Sage realization, selected explicitly. Where Sage is installed it answers the
same Booleans; where it is not, the failure is its absence — never the Lean decision in its
place. -/

run_cmd do
  let env ← getEnv
  let ctx : EvalCtx := { env, realization? := some `sage, notes := ← IO.mkRef #[],
                         annotations := ← IO.mkRef #[] }
  for (x, expected) in [(`G, "true"), (`H, "false")] do
    match ← (eval ctx (.method (.ref x) `is_abelian #[])).run with
    | .ok d =>
        unless d.render == expected do
          throwError s!"Sage's {x}.is_abelian() = {d.render}, expected {expected}"
    | .error (.exec (.backendUnavailable b _)) =>
        unless b == `sage do throwError s!"the Sage realization ran on {b}"
    | .error e => throwError s!"the Sage realization of {x}.is_abelian() failed: {e.render}"

end CasDslTests.Abelian
