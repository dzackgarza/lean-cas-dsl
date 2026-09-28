/-
The semantic bridge: notebook values as points of the `CasCatalogue` registry
(`specs/computational-core.md` §8, plan node `cc-dsl-migration`).

A semantic point is a pair (registered category, presentation). The category is
fixed by the ascription that made the point (`let F := ℤ/4 in Modules(ℤ)`); the
presentation only selects a realization (CC-SEP). A method call on a point is
resolved by `CasCatalogue.RegistryState.resolveMethod` — the one resolver — and
executed by the registered actions along the resolved route, starting from the
realizer the presentation encodes into:

* when a registered action also realizes the method itself, the whole composite
  runs in Lean (`Trust.leanChecked`);
* otherwise the route's image is decoded back into a presentation and the
  method runs on it through a registered backend route (a trusted backend
  answer, `ExecError` when the backend is unreachable).

The codecs below are the only presentation-dependent code: `encode` sends a
presentation to a handle of a registered realizer of the point's category, and
the decoders send handles back. Neither decides a category.
-/
import Lean
import CasDsl.Value
import CasDsl.Mathlib.Verify
import CasCatalogue.Resolve
import CasCatalogue.Standard

namespace CasDsl.Semantic

open Lean Meta
open CasCatalogue CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Cardinality
open CasCatalogue.Foundation.Subsets

/-! ## Surface categories -/

/-- The registered category a surface category spelling names, with its base ring for a module
fibre. `Modules(R)` and `Mod(R)` are the fibre `Mod_R` of the module fibration. -/
def surfaceCategory? (head : Name) (base : Option Domain) : Option (String × Option Domain) :=
  match head, base with
  | `Modules, some b | `Mod, some b => some ("cat.modules_r", some b)
  | _, _ => none

/-! ## Codecs -/

/-- A presentation encoded as a handle of a registered realizer: the realizer's id, its
denotation (applied to the realizer's parameters) and the handle. -/
structure Encoded where
  realizer : String
  denotation : Expr
  handle : Expr

/-- Encode a presentation of an object of `category` (over `base`) into a realizer registered for
that category. `none`: no registered realizer of this category realizes the presentation. -/
def encode (category : String) (base : Option Domain) (pres : Obj) : Option Encoded :=
  match category, base, pres with
  -- ℤ/n as a cyclic ℤ-module
  | "cat.modules_r", some .int, .domainObj (.mod n) =>
      some ⟨"rz.modules.cyclic_int", mkConst ``CasCatalogue.Modules.Finite.cyclicDenotation,
        mkNatLit n⟩
  -- ℤᵏ, free
  | "cat.modules_r", some .int, .domainObj (.vector k .int) =>
      some ⟨"rz.modules.int_free", mkConst ``CasCatalogue.Modules.Actions.freeModuleDenotation,
        mkNatLit k⟩
  -- (ℤ/n)ᵏ, free over ℤ/n
  | "cat.modules_r", some (.mod n), .domainObj (.vector k (.mod m)) =>
      if n == m then
        some ⟨"rz.modules.zmod_free",
          mkApp (mkConst ``CasCatalogue.Modules.Finite.freeDenotation) (mkNatLit n), mkNatLit k⟩
      else none
  | _, _, _ => none

/-- The finite set `{0, …, n-1}` of residues, as the notebook presents `ℤ/n`'s elements. -/
def residues (n : Nat) : Obj :=
  .setObj (.finite (.mod n) ((Array.range n).map fun i => Value.mkMod n (Int.ofNat i)))

/-- A presented set, as a notebook presentation. -/
def decodeSet : SetHandle → Obj
  | .intPow n => .setObj (.domainSet (.vector n .int))
  | .finite n => .setObj (.finite .nat ((Array.range n).map fun i => .int (Int.ofNat i)))
  | .zmod 0 => .setObj (.domainSet .int)
  | .zmod n => residues n
  | .zmodPow n k => .setObj (.domainSet (.vector k (.mod n)))

/-- A presented subset, as a notebook presentation. -/
def decodeSubset : SubsetHandle → Obj
  | .whole X => decodeSet X

/-- A cardinal handle, as a notebook value. -/
def decodeCardinal : CardinalHandle → Value
  | .finite n => .cardinal (.finite n)
  | .aleph0 => .cardinal .countablyInfinite

/-! ## Evaluation of closed handle terms -/

unsafe def evalObjUnsafe (e : Expr) : MetaM Obj := evalExpr Obj (mkConst ``Obj) e
@[implemented_by evalObjUnsafe] opaque evalObj (e : Expr) : MetaM Obj

unsafe def evalValueUnsafe (e : Expr) : MetaM Value := evalExpr Value (mkConst ``Value) e
@[implemented_by evalValueUnsafe] opaque evalValue (e : Expr) : MetaM Value

/-- Decode a closed handle term into a presentation, by its handle type. -/
def decodeImage (image : Expr) : MetaM (Option Obj) := do
  let type ← whnf (← inferType image)
  if type.isConstOf ``SetHandle then
    return some (← evalObj (mkApp (mkConst ``decodeSet) image))
  if type.isConstOf ``SubsetHandle then
    return some (← evalObj (mkApp (mkConst ``decodeSubset) image))
  return none

/-- Decode a closed result term into a notebook value, by its handle type. -/
def decodeResult (value : Expr) : MetaM (Option Value) := do
  let type ← whnf (← inferType value)
  if type.isConstOf ``CardinalHandle then
    return some (← evalValue (mkApp (mkConst ``decodeCardinal) value))
  return none

/-! ## Calls -/

/-- What resolving a method call on a semantic point produced: the resolved composite, and its
Lean-native realization where the registered actions provide one. -/
structure Plan where
  /-- The resolution, rendered. -/
  route : String
  /-- The composite's key (CC-ROUTE): the method's id and the labels of the route's steps. -/
  method : String
  steps : Array String
  /-- The value of the composite computed by registered actions, when they realize the method
  itself (and the call has no arguments). -/
  value? : Option Value
  /-- The route's image `U(x)`, decoded, for a method realized by a backend on the image. -/
  image? : Option Obj
  deriving Inhabited

/-- The registered category of a point, by id. -/
def categoryExpr (state : RegistryState) (category : String) : Except String CategoryExpr :=
  match state.categories.find? (·.id.raw == category) with
  | some entry => .ok entry.expression
  | none => .error s!"no registered category {category}"

/-- Resolve `pres.method` for a point of `category` and run the route's registered actions from
the presentation's realizer (CC-TRANSPORT: execution receives `U(x)`, never `x`). Errors are
rendered resolution errors or codec failures. -/
def call (env : Environment) (category : String) (base : Option Domain) (pres : Obj)
    (method : String) (withArguments : Bool) : IO (Except String Plan) :=
  runSemanticCheck env <| tryCatch body fun e => return .error (← e.toMessageData.toString)
where
  body : MetaM (Except String Plan) := do
    let state ← registryState
    let expression ← match categoryExpr state category with
      | .ok e => pure e
      | .error e => return .error e
    let resolution ← match state.resolveMethod expression method with
      | .ok r => pure r
      | .error e => return .error (e.render state)
    let some encoded := encode category base pres
      | return .error s!"no registered realizer of {category} realizes {pres.presentation} \
          (CC-SEP)"
    let (image, value?) ← realizedCall state resolution encoded.denotation encoded.handle
    let value? ← if withArguments then pure none else
      match value? with
      | some value => decodeResult value
      | none => pure none
    return .ok { route := state.renderResolution resolution
                 method := resolution.method.id.raw
                 steps := resolution.route.refs.map (·.label)
                 value?, image? := ← decodeImage image }

/-- `#explain_route` for a semantic point: the resolved route and the realizations of it — the
receiver's realizer, whether registered actions realize the whole composite, and every registered
fused implementation of the same composite (CC-ROUTE). Nothing is executed. -/
def explain (env : Environment) (category : String) (base : Option Domain) (pres : Obj)
    (method : String) : IO (Except String String) :=
  runSemanticCheck env <| tryCatch body fun e => return .error (← e.toMessageData.toString)
where
  body : MetaM (Except String String) := do
    let state ← registryState
    let expression ← match categoryExpr state category with
      | .ok e => pure e
      | .error e => return .error e
    let resolution ← match state.resolveMethod expression method with
      | .ok r => pure r
      | .error e => return .error (e.render state)
    let some encoded := encode category base pres
      | return .error s!"no registered realizer of {category} realizes {pres.presentation}"
    let (_, value?) ← realizedCall state resolution encoded.denotation encoded.handle
    let fused := state.implementations.filter fun e =>
      e.method == resolution.method.id && e.route == resolution.route.refs
    let key := some (resolution.method.id.raw, resolution.route.refs.map (·.label))
    let fusedRoutes := (routesFor env (Name.mkSimple method)).filter fun r => r.realizes == key
    let lines := #[s!"{method} on {pres.presentation} (a point of {category}, realized by \
        {encoded.realizer})",
      s!"  route:       {state.renderRoute resolution.route}",
      s!"  method:      {resolution.method.id.raw} = {resolution.method.functor.raw}",
      s!"  realization: " ++ (if value?.isSome then
          "composed Lean-native actions (Lean-checked computation)"
        else "the route's registered actions, then a backend route on the image")] ++
      fused.map (fun e => s!"  realization: {e.id.raw} by {e.backend} ({e.trust.label})") ++
      fusedRoutes.map fun r =>
        s!"  realization: fused route {r.backend} {repr r.opId} on the receiver (trusted \
          backend assertion){if r.pattern.accepts pres then "" else " — not for this presentation"}"
    return .ok ("\n".intercalate lines.toList)

/-- The membership judgment of an ascription to a registered category: some registered realizer
of the category realizes the presentation. -/
def realizes (category : String) (base : Option Domain) (pres : Obj) : Bool :=
  (encode category base pres).isSome

end CasDsl.Semantic
