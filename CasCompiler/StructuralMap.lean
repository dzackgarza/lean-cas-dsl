module

public import CasCompiler.Layout
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

public section

namespace CasCompiler

open Lean Meta

/-- A structural map written in the original native Hom interface. It retains the actual
category/dictionary and ordered operands; the wire descriptor supplies no executable code. -/
structure NativeStructuralMap where
  private mk ::
  value : Expr
  tag : String
  source : Expr
  target : Expr
  operands : Array Expr
  dictionary : Expr

private def originalHom? (value : Expr) : MetaM (Option Expr) := do
  let type ← inferType value
  if type.isAppOfArity ``Quiver.Hom 4 then return some type
  let type ← whnfR type
  return if type.isAppOfArity ``Quiver.Hom 4 then some type else none

/-- Inspect only an explicitly selected class parent, then return its exact field without
reducing that field. This is the same native constructor boundary used by Lower.field. -/
private def originalClassField? (context : OpenContext) (inputs : Array BindingId)
    (value : Expr) : MetaM (Option Expr) := do
  let some projection ← SourceProjection.ofExpr? value | return none
  unless projection.info.fromClass do return none
  let parent ← context.inputProjectionSource projection.parent inputs
  unless parent.getAppFn.isConstOf projection.info.ctorName do return none
  let some selected ← projectCore? parent projection.info.i | return none
  return some (selected.betaRev
    (value.getAppArgs.extract (projection.info.numParams + 1) value.getAppNumArgs).reverse
    (preserveMData := true))

private def numeralField? (context : OpenContext) (inputs : Array BindingId)
    (value : Expr) : MetaM (Option Expr) := do
  unless value.isAppOfArity ``OfNat.ofNat 3 do return some value
  let some index := value.getAppArgs[1]!.rawNatLit? | return none
  unless index == 0 || index == 1 do return none
  originalClassField? context inputs value

/-- The original Hom supplies the exact Category parent. Instance inference is only for its
zero structure; the supplied map must be the unchanged native field of that structure.
In particular, a group's literal 1 is accepted only when it is that actual zero-map field. -/
private def originalZero? (context : OpenContext) (inputs : Array BindingId)
    (value type : Expr) : MetaM (Option Expr) := do
  let some value ← numeralField? context inputs value | return none
  unless value.isAppOfArity ``Zero.zero 2 || value.isAppOfArity ``One.one 2 do return none
  if value.isAppOfArity ``Zero.zero 2 then
    let instanceValue := value.getAppArgs[1]!
    if instanceValue.isAppOfArity ``CategoryTheory.Limits.HasZeroMorphisms.zero 5 then
      return some instanceValue
  let quiver := type.getAppArgs[1]!.consumeMData
  let structureValue ← if quiver.isAppOfArity ``CategoryTheory.CategoryStruct.toQuiver 2 then
      pure (some quiver.getAppArgs[1]!)
    else if let .proj owner 0 parent := quiver then
      pure (if owner == ``CategoryTheory.CategoryStruct then some parent else none)
    else pure none
  let some structureValue := structureValue | return none
  let structureValue := structureValue.consumeMData
  let category ← if structureValue.isAppOfArity ``CategoryTheory.Category.toCategoryStruct 2 then
      pure (some structureValue.getAppArgs[1]!)
    else if let .proj owner 0 parent := structureValue then
      pure (if owner == ``CategoryTheory.Category then some parent else none)
    else pure none
  let some category := category | return none
  let fields := type.getAppArgs
  let classType ← mkAppOptM ``CategoryTheory.Limits.HasZeroMorphisms
    #[some fields[0]!, some category]
  let some zeros := (← trySynthInstance classType).toOption | return none
  let zeroInstance ← mkAppOptM ``CategoryTheory.Limits.HasZeroMorphisms.zero
    #[some fields[0]!, some category, some zeros, some fields[2]!, some fields[3]!]
  let canonical ← mkAppOptM ``Zero.zero #[some type, some zeroInstance]
  let some original ← originalClassField? context inputs canonical | return none
  let some original ← numeralField? context inputs original | return none
  unless original.equal value do return none
  return some zeroInstance

/-- Recognize native identity, composition and the exact original categorical-zero field.
No declaration is unfolded to discover a map, and no map body, matcher or recursor executes.
Only an OfNat/class parent can expose its constructor before the unchanged field is read. -/
opaque NativeStructuralMap.ofExpr? (context : OpenContext) (value : Expr)
    (inputs : Array BindingId := #[]) : MetaM (Option NativeStructuralMap) := do
  let .const _ _ := value.getAppFn | return none
  if value.isAppOfArity ``CategoryTheory.CategoryStruct.id 3 then
    check value
    let args := value.getAppArgs
    return some ⟨value, "identity", args[2]!, args[2]!, #[args[2]!, args[2]!], args[1]!⟩
  if value.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 then
    check value
    let args := value.getAppArgs
    return some ⟨value, "compose", args[2]!, args[4]!, #[args[5]!, args[6]!], args[1]!⟩
  unless value.isAppOfArity ``Zero.zero 2 || value.isAppOfArity ``One.one 2 ||
      value.isAppOfArity ``OfNat.ofNat 3 do return none
  let some type ← originalHom? value | return none
  let some dictionary ← originalZero? context inputs value type | return none
  check value
  return some ⟨value, "zero", type.getAppArgs[2]!, type.getAppArgs[3]!,
    #[type.getAppArgs[2]!, type.getAppArgs[3]!], dictionary⟩

end CasCompiler
