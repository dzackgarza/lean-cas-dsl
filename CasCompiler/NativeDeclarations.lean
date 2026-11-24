module

public import Lean.AddDecl
public import Lean.Meta.Basic

@[expose] public section

namespace CasCompiler

open Lean Meta

/-- Exact native declarations used by a captured source, excluding imported declarations.
The constructor is private: entries come from the checked native environment, not from
source syntax, a backend response, or an invented axiom. -/
structure NativeDeclarations where
  private mk ::
  constants : Array ConstantInfo

private def sameConstantVal (left right : ConstantVal) : Bool :=
  left.name == right.name && left.levelParams == right.levelParams &&
    left.type.equal right.type

/-- Native declaration identity includes the whole checked payload, not just its name/type. -/
opaque nativeConstantExactlyMatches (left right : ConstantInfo) : Bool :=
  sameConstantVal left.toConstantVal right.toConstantVal && match left, right with
  | .axiomInfo left, .axiomInfo right => left.isUnsafe == right.isUnsafe
  | .defnInfo left, .defnInfo right =>
    left.value.equal right.value && left.hints == right.hints &&
      left.safety == right.safety && left.all == right.all
  | .thmInfo left, .thmInfo right =>
    left.value.equal right.value && left.all == right.all
  | .opaqueInfo left, .opaqueInfo right =>
    left.value.equal right.value && left.isUnsafe == right.isUnsafe && left.all == right.all
  | .inductInfo left, .inductInfo right =>
    left.numParams == right.numParams && left.numIndices == right.numIndices &&
      left.all == right.all && left.ctors == right.ctors && left.numNested == right.numNested &&
      left.isRec == right.isRec && left.isUnsafe == right.isUnsafe &&
      left.isReflexive == right.isReflexive
  | .ctorInfo left, .ctorInfo right =>
    left.induct == right.induct && left.cidx == right.cidx &&
      left.numParams == right.numParams && left.numFields == right.numFields &&
      left.isUnsafe == right.isUnsafe
  | .recInfo left, .recInfo right =>
    left.all == right.all && left.numParams == right.numParams &&
      left.numIndices == right.numIndices && left.numMotives == right.numMotives &&
      left.numMinors == right.numMinors && left.k == right.k &&
      left.isUnsafe == right.isUnsafe && left.rules.length == right.rules.length &&
      (left.rules.zip right.rules).all fun (left, right) =>
        left.ctor == right.ctor && left.nfields == right.nfields && left.rhs.equal right.rhs
  | .quotInfo left, .quotInfo right =>
    match left.kind, right.kind with
    | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
    | _, _ => false
  | _, _ => false

def NativeDeclarations.exactlyMatches (left right : NativeDeclarations) : Bool :=
  left.constants.size == right.constants.size &&
    (left.constants.zip right.constants).all fun (left, right) =>
      nativeConstantExactlyMatches left right

private structure CaptureState where
  visited : NameSet := {}
  constants : Array ConstantInfo := #[]

private partial def captureConstant (environment : Environment) (name : Name) :
    StateT CaptureState MetaM Unit := do
  if environment.isImportedConst name || (← get).visited.contains name then return
  let some info := environment.find? name
    | throwError "a retained native source refers to missing declaration {name}"
  modify fun state => { state with visited := state.visited.insert name }
  let mut expressions := #[info.type]
  if let some value := info.value? (allowOpaque := true) then
    expressions := expressions.push value
  match info with
  | .inductInfo declaration =>
    for name in declaration.all ++ declaration.ctors do captureConstant environment name
  | .ctorInfo declaration => captureConstant environment declaration.induct
  | .recInfo declaration =>
    for name in declaration.all do captureConstant environment name
    for rule in declaration.rules do
      captureConstant environment rule.ctor
      expressions := expressions.push rule.rhs
  | _ => pure ()
  for expression in expressions do
    for dependency in expression.getUsedConstants do captureConstant environment dependency
  modify fun state => { state with constants := state.constants.push info }

/-- Freeze the reachable current-module declaration graph in dependency order. Imported
mathematics stays in its original module environment and is never copied or unfolded. -/
opaque NativeDeclarations.capture (expressions : Array Expr) : MetaM NativeDeclarations := do
  let environment := (← getEnv).setExporting false
  let action : StateT CaptureState MetaM Unit := do
    for expression in expressions do
      for name in expression.getUsedConstants do captureConstant environment name
  let (_, state) ← action.run {}
  return ⟨state.constants⟩

private def replayable? : ConstantInfo → Option Declaration
  | .defnInfo declaration =>
    if declaration.safety == .safe then some (.defnDecl declaration) else none
  | .thmInfo declaration => some (.thmDecl declaration)
  | .opaqueInfo declaration =>
    if declaration.isUnsafe then none else some (.opaqueDecl declaration)
  | _ => none

/-- Reattach exact checked value declarations to the current environment. Existing names
must carry identical native payloads. Ambient axioms, inductive families and unsafe
declarations must already be present: this operation never invents or publishes them.
Native addDecl checks every restored definition/proof, preserving the current environment's
runtime extensions. Additions remain available after the caller's inspection finishes. -/
opaque NativeDeclarations.ensure (declarations : NativeDeclarations) : MetaM Unit := do
  for original in declarations.constants do
    match ((← getEnv).setExporting false).find? original.name with
    | some current =>
      unless nativeConstantExactlyMatches original current do
        throwError "a retained source declaration {original.name} has a different native meaning"
    | none =>
      unless (replayable? original).isSome do
        throwError "a retained source requires its original ambient declaration {original.name}"
  for original in declarations.constants do
    if ((← getEnv).setExporting false).contains original.name then continue
    let some declaration := replayable? original
      | throwError "a retained source declaration lost its checked replay form"
    addDecl declaration
    let current ← getConstInfo original.name
    unless nativeConstantExactlyMatches original current do
      throwError "native checking changed a retained source declaration {original.name}"

end CasCompiler
