/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Decide
public import CasCatalogue.EquationData
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Defs

@[expose] public section

/-!
# The generic structural codec (`specs/leaf-registration.md`, "Forms are formal")

The kernel owns each form's wire encoding, and it is one codec over every inductive type, derived
from the type's definition in the environment. It has no per-type code:

* a natural number or an integer is a JSON number;
* a list is a JSON array;
* a quotient `Quot r` is a representative: the encoding of a value of the carrier, and decodes
  as the class of the value read (a `Multiset` is a list; a `Finset` is a list, its `nodup`
  decided);
* a record (an inductive type with one constructor and no indices: a pair, `Fin n`, a subtype)
  is the JSON array of its data fields, and is the field itself when it has exactly one (a
  point of `Fin n` is its number, a pair is `[x, y]`);
* any other constructor application is `{"ctor": <constructor name>, "args": [<fields>]}`, the
  constructor spelled by its short name within its type (`finite`, `aleph0`), with its data
  fields.

A proof field is never on the wire (`k < n` of a point of `Fin n`). Decoding establishes it by
the kernel's decision (`CasCatalogue.Decide`), from the data fields before it, or rejects the
value: what a leaf sends is data, and whether it satisfies the form's conditions is decided here.

Decoding is total: JSON becomes a closed value of the expected type, driven by that type's
inductive definition, or it is rejected with the reason. A type the codec does not handle (a
quotient, a field that is a type) is rejected by name; nothing special-cases it.
-/

open Lean Meta

namespace CasCatalogue.Codec

/-- The wire spelling of a constructor: its name within its type. -/
def label (ctor : Name) : String :=
  match ctor with
  | .str _ s => s
  | n => n.toString

/-- The natural number a closed term is. -/
def nat? (e : Expr) : MetaM (Option Nat) := (evalNat e).run

/-- Synthesize at the actual carrier beneath accepted projection definitions. This changes
only definitional presentation, never supplies a new instance. -/
def dataInstance (type : Expr) : MetaM (Option Expr) := do
  if let some value := (← trySynthInstance type).toOption then return some value
  let args ← type.getAppArgs.mapM fun arg => withTransparency .all <| whnf arg
  let normalized := mkAppN type.getAppFn args
  return (← trySynthInstance normalized).toOption

/-- Enumerate a finite domain from its independently synthesized `Fintype` instance. -/
def finiteDomain (type : Expr) : MetaM (Option (Array Expr)) := do
  let instanceType ← mkAppM ``Fintype #[type]
  let some finiteInstance ← dataInstance instanceType | return none
  let values ← mkAppOptM ``Fintype.elems #[some type, some finiteInstance]
  let representation ← withTransparency .all <| whnf (← mkAppM ``Finset.val #[values])
  let some ``Quot.mk := representation.getAppFn.constName? | return none
  let some list := representation.getAppArgs[2]? | return none
  let mut values ← withTransparency .all <| whnf list
  let mut result := #[]
  repeat
    match values.getAppFn.constName?, values.getAppArgs with
    | some ``List.nil, _ => return some result
    | some ``List.cons, #[_, value, rest] =>
        result := result.push value
        values ← withTransparency .all <| whnf rest
    | _, _ => return none

/-- Whether `info` has one constructor and no indices: its values go on the wire without a
constructor label. -/
def isUnlabelled (info : InductiveVal) : Bool := info.ctors.length == 1 && info.numIndices == 0

/-- The number of data (non-proof) fields of the constructor `ctor`. -/
def dataFieldCount (ctor : ConstructorVal) : MetaM Nat :=
  forallTelescopeReducing ctor.type fun xs _ => do
    let fields := xs.extract ctor.numParams (ctor.numParams + ctor.numFields)
    fields.foldlM (init := 0) fun n x => return if ← isProp (← inferType x) then n else n + 1

/-- Structural proof assembly from decision, reflexivity, function extensionality and
constructor congruence. No tactic or leaf proof participates; the final proof is kernel-checked. -/
partial def conditionProofAux (condition : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let condition ← whnfR (← instantiateMVars condition)
  let originalCondition := condition
  if let some (_, left, right) := condition.eq? then
    if ← withReducible <| isDefEq left right then return some (← mkEqRefl left)
    let leftHead ← withTransparency .all <| whnf left
    let rightHead ← withTransparency .all <| whnf right
    if let some name := leftHead.getAppFn.constName? then
      if let some (.ctorInfo ctor) := (← getEnv).find? name then
        if ctor.numFields == 1 && leftHead.getAppNumArgs == rightHead.getAppNumArgs &&
            rightHead.getAppFn.constName? == some name then
          let parameters := leftHead.getAppArgs.pop
          if ← (parameters.zip rightHead.getAppArgs.pop).allM fun (a, b) =>
              withTransparency .all <| isDefEq a b then
            if let some proof ← conditionProofAux
                (← mkEq leftHead.appArg! rightHead.appArg!) (fuel - 1) then
              return some (← mkCongrArg (mkAppN leftHead.getAppFn parameters) proof)
    -- Primitive quotient constructors are not ordinary inductive constructor metadata.
    -- Equal representatives suffice only after the complete selected type and relation agree.
    if leftHead.isAppOf ``Quot.mk && rightHead.isAppOf ``Quot.mk &&
        leftHead.getAppNumArgs == rightHead.getAppNumArgs then
      let parameters := leftHead.getAppArgs.pop
      if ← (parameters.zip rightHead.getAppArgs.pop).allM fun (a, b) =>
          withTransparency .all <| isDefEq a b then
        if let some proof ← conditionProofAux
            (← mkEq leftHead.appArg! rightHead.appArg!) (fuel - 1) then
          return some (← mkCongrArg (mkAppN leftHead.getAppFn parameters)
            (mkExpectedPropHint proof (← mkEq leftHead.appArg! rightHead.appArg!)))
    -- Preserve the original bundled type while selecting its accepted extensionality instance.
    -- Normalizing its carrier first can hide the registered FunLike instance head.
    let bundled ← withoutModifyingState do
      let ext ← mkConstWithFreshMVarLevels ``DFunLike.ext'
      let (args, _, result) ← forallMetaTelescope (← inferType ext)
      unless ← isDefEq result condition do return none
      for arg in args.pop do
        if (← instantiateMVars arg).isMVar then
          let argType ← instantiateMVars (← inferType arg)
          if (← isClass? argType).isSome then
            if let some value ← dataInstance argType then
              discard <| isDefEq arg value
      let some hypothesis := args.back? | return none
      let goal ← instantiateMVars (← inferType hypothesis)
      if goal.hasMVar then return none
      let some proof ← conditionProofAux goal (fuel - 1) | return none
      unless ← isDefEq hypothesis (mkExpectedPropHint proof goal) do return none
      let value ← instantiateMVars (mkAppN ext args)
      if value.hasMVar || value.hasLevelMVar then return none
      return some value
    if let some proof := bundled then return some proof
  let condition ← Meta.transform condition (pre := fun term => do
    if term.isSort || (← isProof term) then return .done term
    -- Keep the selected dictionary itself intact, while normalizing its type arguments
    -- consistently with the carrier occurrences outside the dictionary application.
    if (← isClass? (← inferType term)).isSome then return .continue
    if (← whnf (← inferType term)).isSort && !(← isProp term) then
      let normalized ← withTransparency .all <|
        reduce term (explicitOnly := false) (skipTypes := false)
      let aligned ← Meta.transform normalized (post := fun expression => do
        match expression with
        | .lam name domain body info =>
          let domain ← withTransparency .all <|
            reduce domain (explicitOnly := false) (skipTypes := false)
          return .done (.lam name domain body info)
        | .forallE name domain body info =>
          let domain ← withTransparency .all <|
            reduce domain (explicitOnly := false) (skipTypes := false)
          return .done (.forallE name domain body info)
        | _ => return .done expression)
      return .done aligned
    return .continue)
  let condition ← match condition with
    | .forallE name domain body info => do
        let normalized ← withTransparency .all <|
          reduce domain (explicitOnly := false) (skipTypes := false)
        -- Preserve the proposition's instance heads while normalizing its carrier everywhere.
        -- Unfolding membership itself to List.Mem hides the decidability instance; leaving
        -- its implicit carrier at an accepted apex projection hides DecidableEq instead.
        let body := body.replace fun term => if term == domain then some normalized else none
        pure (Expr.forallE name normalized body info)
    | other => pure other
  if let some proof ← Decide.decisionProof condition then return some proof
  -- A checked negative decision ends unsuccessful proof assembly before metadata traversal.
  if let some negative ← Decide.decisionProof (mkNot condition) then
    let negative ← instantiateMVars (mkExpectedPropHint negative (mkNot originalCondition))
    if !negative.hasMVar && !negative.hasLevelMVar && !negative.hasFVar &&
        !negative.hasLooseBVars && (← Decide.kernelAccepts (mkNot originalCondition) negative) then
      return none
  if originalCondition.eq?.isSome then
    if let some proof ← EquationData.prove originalCondition fun normalized =>
        conditionProofAux normalized (fuel - 1) then return some proof
  if let some (_, left, right) := condition.eq? then
    if ← isDefEq left right then return some (← mkEqRefl left)
    let type ← whnfR (← inferType left)
    if type.isForall then
      let pointwise ← forallTelescope type fun xs _ => do
        let proposition ← mkEq (mkAppN left xs) (mkAppN right xs)
        mkForallFVars xs proposition
      if let some proof ← conditionProofAux pointwise (fuel - 1) then
        let proof ← forallTelescope type fun xs _ => do
          let mut applied := mkAppN proof xs
          for x in xs.reverse do
            applied ← mkFunExt (← mkLambdaFVars #[x] applied)
          pure applied
        return some proof
    -- Bundled functions may have several law fields. Extensionality identifies their
    -- complete values from the actual function field, with proof irrelevance for the laws.
    let bundled ← withoutModifyingState do
      let ext ← mkConstWithFreshMVarLevels ``DFunLike.ext'
      let (args, _, result) ← forallMetaTelescope (← inferType ext)
      unless ← isDefEq result condition do return none
      for arg in args.pop do
        if (← instantiateMVars arg).isMVar then
          let argType ← instantiateMVars (← inferType arg)
          if (← isClass? argType).isSome then
            if let some value ← dataInstance argType then
              discard <| isDefEq arg value
      let some hypothesis := args.back? | return none
      let goal ← instantiateMVars (← inferType hypothesis)
      if goal.hasMVar then return none
      let some proof ← conditionProofAux goal (fuel - 1) | return none
      unless ← isDefEq hypothesis proof do return none
      let value ← instantiateMVars (mkAppN ext args)
      if value.hasMVar || value.hasLevelMVar then return none
      return some value
    if let some proof := bundled then return some proof
    let left ← withTransparency .all <| whnf left
    let right ← withTransparency .all <| whnf right
    if ← isDefEq left.getAppFn right.getAppFn then
      if let some name := left.getAppFn.constName? then
        if let some (.ctorInfo ctor) := (← getEnv).find? name then
          if ctor.numFields == 1 && left.getAppNumArgs == right.getAppNumArgs then
            let constructorArgs := left.getAppArgs.pop
            let otherConstructorArgs := right.getAppArgs.pop
            if ← (constructorArgs.zip otherConstructorArgs).allM fun (a, b) => isDefEq a b then
              if let some proof ← conditionProofAux
                  (← mkEq left.appArg! right.appArg!) (fuel - 1) then
                return some (← mkCongrArg (mkAppN left.getAppFn constructorArgs) proof)
  if let .forallE name domain body _ := condition then
    let domain ← withTransparency .all <| whnf domain
    let some typeName := domain.getAppFn.constName? | return none
    let some (.inductInfo info) := (← getEnv).find? typeName | return none
    if info.numIndices != 0 || info.isRec then return none
    return ← withLocalDeclD name domain fun x => do
      let body := body.instantiate1 x
      let cases ← mkConstWithFreshMVarLevels (typeName ++ `casesOn)
      let (args, _, result) ← forallMetaTelescopeReducing (← inferType cases)
      -- Assign the major premise before solving the motive at the resulting proposition.
      let mut major := false
      for arg in args do
        if (← instantiateMVars arg).isMVar then
          if ← withoutModifyingState (isDefEq (← inferType arg) domain) then
            discard <| isDefEq (← inferType arg) domain
            discard <| isDefEq arg x
            major := true
            break
      unless major do return none
      -- Fix the dependent motive explicitly. Unifying only `motive x` may choose a constant
      -- motive retaining `x`, which leaves constructor branches unreduced.
      for arg in args do
        unless (← instantiateMVars arg).isMVar do continue
        let motiveType ← whnfR (← inferType arg)
        if let .forallE _ input output _ := motiveType then
          if output.isSort && (← withoutModifyingState (isDefEq input domain)) then
            discard <| isDefEq arg (← mkLambdaFVars #[x] body)
      unless ← isDefEq result body do return none
      for arg in args do
        unless (← instantiateMVars arg).isMVar do continue
        let type ← instantiateMVars (← inferType arg)
        let some proof ← conditionProofAux type (fuel - 1) | return none
        unless ← isDefEq arg proof do return none
      return some (← mkLambdaFVars #[x] (← instantiateMVars (mkAppN cases args)))
  return none

/-- A closed constructor condition discharged structurally and independently checked by Lean. -/
def conditionProof (condition : Expr) : MetaM (Option Expr) := do
  let attempt : MetaM (Option Expr) := do
    let some proof ← conditionProofAux condition 32 | return none
    if ← Decide.kernelAccepts condition proof then
      let sealed := mkExpectedPropHint proof condition
      if ← Decide.kernelAccepts condition sealed then return some sealed
    return none
  attempt

/-- Encode the closed value `e`. -/
partial def encode (e : Expr) : MetaM (Except String Json) := do
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars then
    return .error "the codec only encodes closed values"
  let type ← whnf (← inferType e)
  if let .forallE _ domain _ _ := type then
    let some inputs ← finiteDomain domain
      | return .error "a function field has no computable finite domain"
    let mut graph := #[]
    for input in inputs do
      match ← encode input, ← encode (mkApp e input) with
      | .ok x, .ok y => graph := graph.push (Json.arr #[x, y])
      | .error message, _ | _, .error message => return .error message
    return .ok (Json.arr graph)
  if type.isConstOf ``Nat then
    return match ← nat? e with
      | some n => .ok (toJson n)
      | none => .error s!"the natural number {e} is not a closed literal"
  if type.isConstOf ``Int then
    let e ← whnf e
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Int.ofNat, #[n] =>
        return match ← nat? n with
          | some n => .ok (toJson (Int.ofNat n))
          | none => .error s!"the integer {e} is not a closed literal"
    | some ``Int.negSucc, #[n] =>
        return match ← nat? n with
          | some n => .ok (toJson (Int.negSucc n))
          | none => .error s!"the integer {e} is not a closed literal"
    | _, _ => return .error s!"the integer {e} is not a closed literal"
  if type.isAppOf ``List then
    let mut items : Array Json := #[]
    let mut rest ← whnf e
    repeat
      match rest.getAppFn.constName?, rest.getAppArgs with
      | some ``List.nil, _ => break
      | some ``List.cons, #[_, x, xs] =>
          match ← encode x with
          | .ok j => items := items.push j
          | .error m => return .error m
          rest ← whnf xs
      | _, _ => return .error s!"the list {rest} is not a closed literal"
    return .ok (Json.arr items)
  if type.isAppOf ``Quot then
    let e ← whnf e
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Quot.mk, #[_, _, a] => return ← encode a
    | _, _ => return .error s!"the class {e} is not a closed literal"
  let e ← whnf e
  let .const c _ := e.getAppFn
    | return .error s!"{e} is not a constructor application"
  let some (.ctorInfo ctor) := (← getEnv).find? c
    | return .error s!"{e} is not a constructor application ({c} is not a constructor)"
  let some (.inductInfo info) := (← getEnv).find? ctor.induct
    | return .error s!"{ctor.induct} is not an inductive type the codec handles"
  let fields := e.getAppArgs.extract ctor.numParams (ctor.numParams + ctor.numFields)
  let mut args : Array Json := #[]
  for field in fields do
    -- A proof field is not on the wire: decoding decides it.
    if ← isProof field then continue
    if ← isType field then
      return .error s!"the constructor {c} has a type field: it is not a data type the codec \
        encodes"
    match ← encode field with
    | .ok j => args := args.push j
    | .error m => return .error m
  if isUnlabelled info then
    return .ok (if args.size == 1 then args[0]! else Json.arr args)
  return .ok (Json.mkObj [("ctor", label c), ("args", Json.arr args)])

mutual

/-- Decode `j` as a closed value of the type `type`. The value is read at the type asked for:
when that type unfolds to the inductive type driving the decoding (`Multiset ℤ` to a quotient,
`ZMod 3` to `Fin 3`), the value carries the asked type as its expected-type hint, so that what
is later decided or synthesized about it (`Multiset.Nodup`, decidable equality) is stated at that
type. -/
partial def decode (type : Expr) (j : Json)
    (point? : Option (Expr → Json → MetaM (Option (Except String Expr))) := none) :
    MetaM (Except String Expr) := do
  let asked ← instantiateMVars type
  let decoded ← if let some point := point? then do
      if let some result ← point asked j then pure result else decodeAt asked j point?
    else decodeAt asked j point?
  match decoded with
  | .ok value =>
      let value ← instantiateMVars value
      if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
        return .error "the answer does not determine a closed value"
      unless ← isDefEq (← inferType value) asked do
        return .error s!"the decoded value does not inhabit {asked}"
      if (← whnf asked) == asked then return .ok value
      else return .ok (← mkExpectedTypeHint value asked)
  | .error message => return .error message

/-- Decode `j` at `type`, driven by the inductive type `type` unfolds to. -/
partial def decodeAt (type : Expr) (j : Json)
    (point? : Option (Expr → Json → MetaM (Option (Except String Expr))) := none) :
    MetaM (Except String Expr) := do
  let type ← whnf (← instantiateMVars type)
  if let .forallE name domain body binderInfo := type then
    if body.hasLooseBVars then
      return .error "a dependent function field has no structural wire form"
    let some inputs ← finiteDomain domain
      | return .error "a function field has no computable finite domain"
    let .ok graph := j.getArr? | return .error "a finite function is an array of input/output pairs"
    unless graph.size == inputs.size do return .error "a finite function graph is not total"
    let mut entries : Array (Expr × Expr) := #[]
    for pair in graph do
      let .ok pair := pair.getArr? | return .error "a function graph entry is not a pair"
      unless pair.size == 2 do return .error "a function graph entry is not a pair"
      match ← decode domain pair[0]! point?, ← decode body pair[1]! point? with
      | .ok x, .ok y => entries := entries.push (x, y)
      | .error message, _ | _, .error message => return .error message
    for input in inputs do
      let mut matchCount := 0
      for (key, _) in entries do
        if (← Decide.decisionProof (← mkEq input key)).isSome then matchCount := matchCount + 1
      unless matchCount == 1 do return .error "a function graph omits or repeats a domain element"
    return ← withLocalDecl name binderInfo domain fun x => do
      if entries.isEmpty then
        let impossible ← mkForallFVars #[x] (mkConst ``False)
        let some proof ← conditionProof impossible
          | return .error "the kernel does not establish that the function domain is empty"
        let value ← mkAppOptM ``False.elim #[some body, some (mkApp proof x)]
        return .ok (← mkLambdaFVars #[x] value)
      let (_, fallback) := entries.back!
      let mut value := fallback
      for (key, output) in entries.reverse do
        value ← mkAppM ``ite #[← mkEq x key, output, value]
      return .ok (← mkLambdaFVars #[x] value)
  if type.isConstOf ``Nat then
    return match j.getNat? with
      | .ok n => .ok (mkNatLit n)
      | .error _ => .error s!"{j.compress} is not a natural number"
  if type.isConstOf ``Int then
    return match j.getInt? with
      | .ok n =>
          if n ≥ 0 then .ok (mkApp (mkConst ``Int.ofNat) (mkNatLit n.toNat))
          else .ok (mkApp (mkConst ``Int.negSucc) (mkNatLit (-n - 1).toNat))
      | .error _ => .error s!"{j.compress} is not an integer"
  if type.isAppOf ``List then
    let element := type.appArg!
    let .ok items := j.getArr? | return .error s!"{j.compress} is not a list"
    let mut decoded : Array Expr := #[]
    for item in items do
      match ← decode element item point? with
      | .ok v => decoded := decoded.push v
      | .error m => return .error m
    let mut list ← mkAppOptM ``List.nil #[some element]
    for v in decoded.reverse do list ← mkAppM ``List.cons #[v, list]
    return .ok list
  if type.isAppOf ``Quot then
    let #[carrier, relation] := type.getAppArgs
      | return .error s!"{type} is not a quotient the codec handles"
    let .const _ levels := type.getAppFn | unreachable!
    return (← decode carrier j point?).map fun a => mkAppN (mkConst ``Quot.mk levels) #[carrier, relation, a]
  let .const typeName levels := type.getAppFn
    | return .error s!"{type} is not an inductive type the codec handles"
  let some (.inductInfo info) := (← getEnv).find? typeName
    | return .error s!"{typeName} is not an inductive type the codec handles"
  -- The constructor and its data fields' encodings: a record's from the array (or the single
  -- field itself), any other type's from `{"ctor", "args"}`.
  let (ctor, args) ← if isUnlabelled info then do
      let ctor ← getConstInfoCtor info.ctors[0]!
      let count ← dataFieldCount ctor
      if count == 1 then pure (ctor, #[j])
      else match j.getArr? with
        | .ok args => pure (ctor, args)
        | .error _ => return .error s!"{j.compress} is not a {typeName}: its {count} fields are \
            an array"
    else do
      let .ok name := j.getObjValAs? String "ctor"
        | return .error s!"{j.compress} is not a constructor application of {typeName} \
            (no `ctor` field)"
      let .ok args := (j.getObjVal? "args").bind (·.getArr?)
        | return .error s!"{j.compress} is not a constructor application of {typeName} \
            (no `args` array)"
      let some ctor := info.ctors.find? fun c => label c == name || c.toString == name
        | return .error s!"{typeName} has no constructor {name} (its constructors are \
            {info.ctors.map label})"
      pure (← getConstInfoCtor ctor, args)
  let count ← dataFieldCount ctor
  unless args.size == count do
    return .error s!"the constructor {label ctor.name} of {typeName} takes {count} values, not \
      {args.size}"
  let mut value := mkAppN (mkConst ctor.name levels) (type.getAppArgs.extract 0 info.numParams)
  let mut remaining := args.toList
  for _ in [0:ctor.numFields] do
    let .forallE fieldName fieldType _ _ ← whnf (← inferType value)
      | return .error s!"the constructor {label ctor.name} of {typeName} has fewer fields than \
          {args.size}"
    if ← isProp fieldType then
      -- The condition the data must satisfy, decided by the kernel.
      let some proof ← conditionProof fieldType
        | return .error s!"the kernel does not establish condition {fieldName} of \
            constructor {label ctor.name}"
      value := mkApp value proof
      continue
    if (← whnf fieldType).isSort then
      return .error s!"a field of the constructor {label ctor.name} of {typeName} is a type: it \
        is not a data type the codec decodes"
    let arg :: rest := remaining | unreachable!
    remaining := rest
    match ← decode fieldType arg point? with
    | .ok v => value := mkApp value v
    | .error m => return .error m
  return .ok value

end

end CasCatalogue.Codec
