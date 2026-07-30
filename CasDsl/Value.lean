/-
Core data model of the CAS: presentations and values.

Everything here is first-order, serializable data — these types are stored
in persistent env extensions (bindings, routes, representative
presentations), so they contain no closures and no host handles. An opaque
backend handle is never a semantic value (anti-drift: backend results are
reflected into these Lean values or the call fails honestly).
-/
import Lean

namespace CasDsl

/-- A presentation of a mathematical domain (a "parent" in CAS speak). -/
inductive Domain where
  | nat
  | int
  | rat
  /-- `ℝ`, spelled `ℝ`, `R` or `RR`. An ASCRIPTION DOMAIN TAG in this slice
  (SPEC.md's `in ℝ → ℝ`): it names the domain a function is declared over and
  carries no analysis semantics — there are no `Value`s presenting it, and
  every operation that would need them fails honestly. -/
  | real
  /-- `ℤ/n`. -/
  | mod (n : Nat)
  /-- Univariate polynomials `coeff[x]`. -/
  | poly (coeff : Domain)
  /-- Square `n × n` matrices over `entry` (square-only in this slice). -/
  | matrix (n : Nat) (entry : Domain)
  /-- `src → tgt`, the domain a function binding is ascribed to. -/
  | funcs (src tgt : Domain)
  deriving BEq, Repr, Hashable, Inhabited

/-- Cardinality values the slice can express. -/
inductive Cardinality where
  | finite (n : Nat)
  | countablyInfinite
  deriving BEq, Repr, Hashable, Inhabited

/-- A trusted CAS value. Backend results reflect into these; small values
are materialized eagerly in this slice (a choice, not a permanent semantic
requirement — see DESIGN.md §Large computations). -/
inductive Value where
  | int (z : Int)
  | rat (q : Rat)
  /-- Element of `ℤ/n`; `v` is normalized `< n` on construction. -/
  | mod (n : Nat) (v : Nat)
  /-- Coefficients ascending by degree, no trailing zeros. -/
  | poly (coeff : Domain) (coeffs : Array Value)
  | mat (n : Nat) (entry : Domain) (rows : Array (Array Value))
  /-- Unit convention and factor order belong to the backend that produced
  it; only this neutral shape is semantic. -/
  | factorization (unit : Value) (factors : Array (Value × Nat)) (dom : Domain)
  /-- An ideal presented by generators (e.g. an annihilator in `ℤ`). -/
  | idealV (gens : Array Value) (ring : Domain)
  | cardinal (c : Cardinality)
  | bool (b : Bool)
  /-- `binder ↦ body` in `src → tgt`. The body is the exact polynomial the
  binder generates, so the identities SPEC.md asserts about functions
  (`h(-t) = h(t)`, `(f ∘ g)(t) = t⁶`) are decided by the polynomial engine
  rather than sampled. The binder is a BOUND NAME, not data: equality
  compares domains and bodies (`Native.valueEq`). -/
  | func (src tgt : Domain) (binder : Lean.Name) (body : Value)
  deriving BEq, Repr, Inhabited

/-- Presentation of a set object. Semantic sets are not replaced by ordered
lists merely because indexing exists; the presentation records the
registered enumeration choice implicitly (first/step order for
progressions, literal order for finite sets, a registered convention for
`domainSet`). -/
inductive SetPresentation where
  | finite (dom : Domain) (elems : Array Value)
  /-- `{a, b, ...}` / `{a, ..., z}`: first, step, optional inclusive last. -/
  | arithProg (dom : Domain) (first step : Value) (last? : Option Value)
  /-- The underlying set of a domain (`ℤ` used as a set). -/
  | domainSet (d : Domain)
  deriving BEq, Repr, Inhabited

/-- The thing a notebook binding names: an object with a presentation.
Category memberships are NOT stored here — the profile is computed
(`Std.profileOf`), keeping presentation and category judgment separate. -/
inductive Obj where
  | elem (dom : Domain) (v : Value)
  | domainObj (d : Domain)
  | setObj (s : SetPresentation)
  /-- Module fixture: the ℤ-module ℤ/n (plan: inheritance demo without a
  premature Macaulay2/Singular bridge). -/
  | cyclicModule (n : Nat)
  deriving BEq, Repr, Inhabited

namespace Domain

/-- Mathematician-facing rendering. -/
partial def render : Domain → String
  | .nat => "ℕ"
  | .int => "ℤ"
  | .rat => "ℚ"
  | .real => "ℝ"
  | .mod n => s!"ℤ/{n}"
  | .poly c => s!"{c.render}[x]"
  | .matrix n e => s!"Mat{subscript n}({e.render})"
  | .funcs s t => s!"{s.render} → {t.render}"
where
  subscript (n : Nat) : String :=
    let digits := "₀₁₂₃₄₅₆₇₈₉"
    String.ofList <| (toString n).toList.map fun c =>
      if c.isDigit then digits.toList[c.toNat - '0'.toNat]! else c

instance : ToString Domain := ⟨render⟩

end Domain

namespace Value

/-- Normalize an integer mod `n` into `Value.mod`. -/
def mkMod (n : Nat) (z : Int) : Value :=
  if n == 0 then .int z else .mod n (z.emod n).toNat

/-- Zero in whatever domain the coefficient presents. `ℤ/n`'s zero counts:
a normal form that stripped only ℤ and ℚ zeros would leave `t + 7` over ℤ/5
one degree too long, and two equal polynomials comparing unequal. -/
private def isZeroCoeff : Value → Bool
  | .int z => z == 0
  | .rat q => q == 0
  | .mod _ v => v == 0
  | _ => false

/-- Strip trailing zero coefficients (the zero polynomial is `#[]`). -/
def mkPoly (coeff : Domain) (coeffs : Array Value) : Value := Id.run do
  let mut cs := coeffs
  while cs.size > 0 && isZeroCoeff cs[cs.size - 1]! do
    cs := cs.pop
  return .poly coeff cs

partial def render : Value → String
  | .int z => toString z
  | .rat q => if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"
  | .mod _ v => toString v
  | .poly _ coeffs => renderPoly "x" coeffs
  | .mat _ _ rows =>
      let r := rows.toList.map fun row =>
        ", ".intercalate (row.toList.map render)
      "[" ++ "; ".intercalate r ++ "]"
  | .factorization unit factors _ =>
      let fs := factors.toList.map fun (f, m) =>
        let base := match f with
          | .poly _ cs =>
              if (cs.filter (· != .int 0)).size > 1 ∨ cs.size > 2 then
                s!"({renderPoly "x" cs})"
              else renderPoly "x" cs
          | v => v.render
        if m == 1 then base else s!"{base}^{m}"
      let core := " * ".intercalate fs
      match unit with
      | .int 1 => if fs.isEmpty then "1" else core
      | .rat q => if q == 1 then core else s!"{render (.rat q)} * {core}"
      | u => if fs.isEmpty then u.render else s!"{u.render} * {core}"
  | .idealV gens _ =>
      "(" ++ ", ".intercalate (gens.toList.map render) ++ ")"
  | .cardinal (.finite n) => toString n
  | .cardinal .countablyInfinite => "ℵ₀"
  | .bool b => toString b
  | .func _ _ binder body =>
      -- the body is written back in the mathematician's own binder, not in
      -- the `x` a bare polynomial renders with
      let t := toString binder
      let b := match body with
        | .poly _ cs => renderPoly t cs
        | v => v.render
      s!"{t} ↦ {b}"
where
  renderPoly (x : String) (coeffs : Array Value) : String := Id.run do
    if coeffs.isEmpty then return "0"
    let mut terms : List String := []
    for i in [0:coeffs.size] do
      let c := coeffs[i]!
      let cs := c.render
      if cs == "0" then continue
      let term :=
        if i == 0 then cs
        else
          let p := if i == 1 then x else s!"{x}^{i}"
          if cs == "1" then p
          else if cs == "-1" then s!"-{p}"
          else if cs.contains '/' then s!"({cs}){p}"
          else s!"{cs}{p}"
      terms := term :: terms
    if terms.isEmpty then return "0"
    -- terms is highest-degree first; join with signs
    let mut out := ""
    for t in terms do
      if out.isEmpty then out := t
      else if t.startsWith "-" then out := out ++ " - " ++ (t.drop 1)
      else out := out ++ " + " ++ t
    return out

instance : ToString Value := ⟨render⟩

end Value

namespace SetPresentation

def render : SetPresentation → String
  | .finite _ elems =>
      "{" ++ ", ".intercalate (elems.toList.map (·.render)) ++ "}"
  | .arithProg _ first step none =>
      let second := match first, step with
        | .int a, .int d => Value.int (a + d) |>.render
        | _, _ => "…"
      s!"\{{first.render}, {second}, ...}"
  | .arithProg _ first step (some last) =>
      let second := match first, step with
        | .int a, .int d => Value.int (a + d) |>.render
        | _, _ => "…"
      s!"\{{first.render}, {second}, ..., {last.render}}"
  | .domainSet d => d.render

instance : ToString SetPresentation := ⟨render⟩

end SetPresentation

namespace Obj

def render : Obj → String
  | .elem _ v => v.render
  | .domainObj d => d.render
  | .setObj s => s.render
  | .cyclicModule n => s!"ℤ/{n} as ℤ-module"

/-- The presentation string used in capability gaps and diagnostics. -/
def presentation : Obj → String
  | .elem d v => s!"{v.render} ∈ {d.render}"
  | .domainObj d => d.render
  | .setObj s => s.render
  | .cyclicModule n => s!"ℤ/{n} as ℤ-module"

instance : ToString Obj := ⟨render⟩

end Obj

end CasDsl
