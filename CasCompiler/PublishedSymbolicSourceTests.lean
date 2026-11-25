module

import CasCompiler.PublishedSource
import CasCompiler.CategoricalPointSource
import LeanCategories.Catalogue.Semantics.Algebra.Ports
import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasCompiler.PublishedSource
meta import CasCompiler.CategoricalPointSource
meta import LeanCategories.Catalogue.Semantics.Algebra.Ports
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

namespace CasCompiler.PublishedSymbolicSourceTests

open Lean Meta Elab Term CasCatalogue

private def symbolicContext (bindings : Array LocalBinding) : MetaM PublishedSourceContext := do
  let unavailable : {α : Type} → MetaM α := fun {_} =>
    throwError "a symbolic interface control attempted to execute or recover a runtime input"
  return {
    scope := ← ContextTelescope.capture bindings
    retained := fun _ => pure none
    literal := fun _ _ => pure none
    bind := pure
    rebind := fun _ value => pure value
    methodParameters := fun _ _ _ => unavailable
    checkInput := fun expected actual => do
      checkRegisteredDomains expected actual
      unless ← isDefEq expected actual do throwError "the original source input changed"
    admitMethod := fun _ _ _ => unavailable
    admitProperty := fun _ _ _ => unavailable
    admitPoint := fun _ _ => unavailable
    projection := fun _ _ => unavailable }

-- A nested source map follows the supplied native RingCat→MonCat action back into
-- RingCat. Its actual native arrow is rejected at the outer MonCat interface.
run_cmd Lean.Elab.Command.liftTermElabM do
  let family ← CategoricalPointFamily.forOwner (.action (.functor FunctorId.ringsMultiplicative))
  let descriptor := Json.mkObj [("ctor", toJson FunctorId.ringsMultiplicative.raw),
    ("args", .arr #[])]
  for levels in #[family.universeParams.map (fun _ => Level.zero),
      family.universeParams.map Level.param] do
    let type ← inferType (family.arrowFamily.instantiateLevelParams family.universeParams levels)
    forallTelescopeReducing type fun parameters _ => do
      let bindings := parameters.mapIdx fun index expression =>
        ({ id := ⟨"symbolic-source-route", index⟩, role := .parameter, expression } : LocalBinding)
      let context ← symbolicContext bindings
      let (expected, _) ← family.arrowAt levels parameters
      let sourceArrow := parameters[family.declarationParameterCount + 2]!
      let (_, target) ← categoricalPointEndpoints sourceArrow
      let operands := #[PublishedSource.NativeSymbolicOperand.value sourceArrow,
        .mapData (.value target) (.value target)]
      PublishedSource.validateSymbolic context expected "compose" operands none #[descriptor]
      let rejected ← try
          PublishedSource.validateSymbolic context expected "compose" operands none
          pure false
        catch _ => pure true
      unless rejected do throwError "a nested source arrow used the outer target category"
      PublishedSource.validateSymbolic context expected "identity"
        #[.objectData (.inline 0)] none #[descriptor]
      PublishedSource.validateSymbolic context expected "compose"
        #[.mapData (.inline 0) (.inline 1), .mapData (.inline 1) (.inline 2)]
        none #[descriptor]
      checkWithKernel (← mkLambdaFVars parameters expected
        (usedOnly := false) (usedLetOnly := false))

-- Two independently supplied category dictionaries on the same object carrier
-- remain separate. Carrier equality cannot authorize their identity or composition.
run_cmd Lean.Elab.Command.liftTermElabM do
  let carrierLevel := Level.param `symbolicCarrier
  withLocalDeclD `C (mkSort (.succ carrierLevel)) fun carrier => do
    let declaration ← getConstInfo ``CategoryTheory.Category
    let categoryType := mkApp (mkConst ``CategoryTheory.Category
      (declaration.levelParams.map (fun _ => carrierLevel))) carrier
    check categoryType
    withLocalDeclD `firstCategory categoryType fun firstCategory => do
      withLocalDeclD `secondCategory categoryType fun secondCategory => do
        withLocalDeclD `X carrier fun object => do
          let firstStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
            #[some carrier, some firstCategory]
          let secondStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
            #[some carrier, some secondCategory]
          let expected ← mkAppOptM ``CategoryTheory.CategoryStruct.id
            #[some carrier, some firstStructure, some object]
          let other ← mkAppOptM ``CategoryTheory.CategoryStruct.id
            #[some carrier, some secondStructure, some object]
          let expressions := #[carrier, firstCategory, secondCategory, object]
          let bindings := expressions.mapIdx fun index expression =>
            ({ id := ⟨"symbolic-category-dictionaries", index⟩, role := .parameter, expression } : LocalBinding)
          let context ← symbolicContext bindings
          PublishedSource.validateSymbolic context expected "compose"
            #[.value expected, .value expected] none
          let rejected ← try
              PublishedSource.validateSymbolic context expected "compose"
                #[.value other, .value other] none
              pure false
            catch _ => pure true
          unless rejected do
            throwError "a different complete category dictionary passed by carrier equality"

-- The same inline intermediate position keeps constraints from every symbolic node.
-- Independently valid leaves cannot relabel distinct native objects as one composition boundary.
run_cmd Lean.Elab.Command.liftTermElabM do
  let carrierLevel := Level.param `sharedSymbolicCarrier
  withLocalDeclD `C (mkSort (.succ carrierLevel)) fun carrier => do
    let declaration ← getConstInfo ``CategoryTheory.Category
    let categoryType := mkApp (mkConst ``CategoryTheory.Category
      (declaration.levelParams.map (fun _ => carrierLevel))) carrier
    withLocalDeclD `category categoryType fun category => do
      withLocalDeclD `B carrier fun first => do
        withLocalDeclD `C carrier fun second => do
          let expressions := #[carrier, category, first, second]
          let bindings := expressions.mapIdx fun index expression =>
            ({ id := ⟨"shared-symbolic-position", index⟩, role := .parameter, expression } : LocalBinding)
          let context ← symbolicContext bindings
          let structureValue ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
            #[some carrier, some category]
          let expected ← mkAppOptM ``CategoryTheory.CategoryStruct.id
            #[some carrier, some structureValue, some first]
          let node := fun object => ({
            expected, tag := "identity", operands := #[.objectData (.value object)],
            descriptor := none, framed := some (.inline 0, .inline 0)
              } : PublishedSource.NativeSymbolicNode)
          let compare : Expr → Expr → TermElabM Unit := fun left right => do
            unless ← isDefEq left right do
              throwError "the shared symbolic position has different original endpoints"
          PublishedSource.validateSymbolicBatch context #[node first, node first] compare
          let rejected ← try
              PublishedSource.validateSymbolicBatch context #[node first, node second] compare
              pure false
            catch _ => pure true
          unless rejected do
            throwError "independent symbolic nodes forgot their shared endpoint constraint"
          checkWithKernel (← mkLambdaFVars expressions expected
            (usedOnly := false) (usedLetOnly := false))


-- Opaque positions are data ports of the accepted native declaration. The finite binder's
-- third port depends on its first; replay must retain that complete dependency with rigid
-- locals, while the same original parameter positions may appear throughout one tree.
run_cmd Lean.Elab.Command.liftTermElabM do
  let slot := fun (index : Nat) => Json.mkObj [("ctor", .str "nativeParameterTest"),
    ("args", .arr #[toJson index])]
  let position? : Json → MetaM (Option Nat) := fun packet => do
    unless (packet.getObjValAs? String "ctor").toOption == some "nativeParameterTest" do
      return none
    let #[value] ← ofExcept <| (packet.getObjVal? "args").bind Json.getArr?
      | throwError "the parameter test lost its original position"
    let index ← ofExcept <| value.getNat?
    unless packet == slot index do throwError "the parameter test changed its original fields"
    return some index
  let compare : Expr → Expr → TermElabM Unit := fun first second => do
    checkRegisteredDomains first second
    unless ← isDefEq first second do
      throwError "the opaque parameter changed a shared native endpoint"
  for identifier in #["bind.sets.finite_sum", "bind.sets.finite_product"] do
    let #[entry] := (← semanticState).binders.filter (·.id.raw == identifier)
      | throwError "the original dependent binder is absent"
    let family ← CategoricalPointFamily.forOwner (.binder entry)
    let levels := family.universeParams.map Level.param
    forallTelescopeReducing
        (← inferType (family.arrowFamily.instantiateLevelParams family.universeParams levels))
        fun parameters _ => do
      let bindings := parameters.mapIdx fun index expression =>
        ({ id := ⟨"opaque-dependent-native-parameters", index⟩, role := .parameter,
           expression } : LocalBinding)
      let context ← symbolicContext bindings
      let (expected, _) ← family.arrowAt levels parameters
      let node := fun (positions : Array Nat) => ({
        expected, tag := identifier, operands := #[],
        descriptor := some (Json.mkObj [("ctor", toJson identifier),
          ("args", .arr (positions.map slot))]),
        framed := some (.inline 0, .inline 1) } : PublishedSource.NativeSymbolicNode)
      let original := node #[0, 1, 2]
      PublishedSource.validateSymbolicBatch context #[original, original] compare
        (parameterCount := 3) (parameterPosition? := position?)
      let reject := fun changed count => do
        let rejected ← try
            PublishedSource.validateSymbolicBatch context #[original, changed] compare
              (parameterCount := count) (parameterPosition? := position?)
            pure false
          catch _ => pure true
        unless rejected do throwError "distinct opaque positions erased a native dependency"
      -- The same actual third port cannot be assigned to a different source object.
      reject (node #[3, 1, 2]) 4
      -- Two independently valid third ports still cannot identify different source objects.
      reject (node #[3, 1, 4]) 5
      -- Reusing an object parameter as an arrow is not licensed by packet identity.
      reject (node #[0, 1, 1]) 3
      let outside ← try
          PublishedSource.validateSymbolicBatch context #[original] compare
          pure false
        catch _ => pure true
      unless outside do throwError "ordinary symbolic reading admitted an unscoped opaque parameter"

-- Polymorphic source cells use the same transient binder entrance at both a concrete and a
-- truly rigid universe. A second original object position cannot be unified with the first.
run_cmd Lean.Elab.Command.liftTermElabM do
  let #[entry] := (← semanticState).cells.filter (·.id == NaturalTransformationId.listReverse)
    | throwError "the original polymorphic comparison is absent"
  let family ← CategoricalPointFamily.forOwner (.component entry #[] false)
  let slot := fun (index : Nat) => Json.mkObj [("ctor", .str "nativeParameterTest"),
    ("args", .arr #[toJson index])]
  let position? : Json → MetaM (Option Nat) := fun packet => do
    if packet == slot 0 then return some 0
    if packet == slot 1 then return some 1
    return none
  for levels in #[family.universeParams.map (fun _ => Level.zero),
      family.universeParams.map Level.param] do
    forallTelescopeReducing
        (← inferType (family.arrowFamily.instantiateLevelParams family.universeParams levels))
        fun parameters _ => do
      let bindings := parameters.mapIdx fun index expression =>
        ({ id := ⟨"opaque-rigid-cell-parameter", index⟩, role := .parameter,
           expression } : LocalBinding)
      let context ← symbolicContext bindings
      let (expected, _) ← family.arrowAt levels parameters
      let node := fun position => ({
        expected, tag := "cellComponent", operands := #[],
        descriptor := some (({
          cell := entry.id.raw, parameters := #[], receiver := slot position, inverse := false
          } : CasCatalogue.Backend.CellComponent).encode),
        framed := some (.inline 0, .inline 1) } : PublishedSource.NativeSymbolicNode)
      let compare : Expr → Expr → TermElabM Unit := fun first second => do
        unless ← isDefEq first second do throwError "the original cell object changed"
      PublishedSource.validateSymbolicBatch context #[node 0, node 0] compare
        (parameterCount := 1) (parameterPosition? := position?)
      let rejected ← try
          PublishedSource.validateSymbolicBatch context #[node 0, node 1] compare
            (parameterCount := 2) (parameterPosition? := position?)
          pure false
        catch _ => pure true
      unless rejected do throwError "rigid opaque object positions were merged by their native type"


-- A parameterized functor and its nested source-category view share one original opaque
-- ring position. The native module family still has its full rigid universe telescope.
run_cmd Lean.Elab.Command.liftTermElabM do
  let edge := EdgeRef.functor FunctorId.modulesFibreInclusion
  let family ← CategoricalPointFamily.forOwner (.action edge)
  let slot := fun (index : Nat) => Json.mkObj [("ctor", .str "nativeParameterTest"),
    ("args", .arr #[toJson index])]
  let position? : Json → MetaM (Option Nat) := fun packet => do
    if packet == slot 0 then return some 0
    if packet == slot 1 then return some 1
    return none
  for levels in #[family.universeParams.map (fun _ => Level.zero),
      family.universeParams.map Level.param] do
    forallTelescopeReducing
        (← inferType (family.arrowFamily.instantiateLevelParams family.universeParams levels))
        fun parameters _ => do
      let bindings := parameters.mapIdx fun index expression =>
        ({ id := ⟨"opaque-native-action-parameter", index⟩, role := .parameter,
           expression } : LocalBinding)
      let context ← symbolicContext bindings
      let (expected, _) ← family.arrowAt levels parameters
      let descriptor := fun position => routedActionDescriptor edge #[slot position]
      let original : PublishedSource.NativeSymbolicNode := {
        expected, tag := "map", operands := #[.mapData (.inline 0) (.inline 1)],
        descriptor := some (descriptor 0), framed := some (.inline 2, .inline 3) }
      let sourceNode := fun position => ({
        expected, tag := "identity", operands := #[.objectData (.inline 0)],
        descriptor := none, framed := some (.inline 0, .inline 0),
        inputActions := #[descriptor position] } : PublishedSource.NativeSymbolicNode)
      let compare : Expr → Expr → TermElabM Unit := fun first second => do
        checkRegisteredDomains first second
        unless ← isDefEq first second do throwError "the original action parameter changed"
      PublishedSource.validateSymbolicBatch context #[original, sourceNode 0] compare
        (parameterCount := 1) (parameterPosition? := position?)
      let rejected ← try
          PublishedSource.validateSymbolicBatch context #[original, sourceNode 1] compare
            (parameterCount := 2) (parameterPosition? := position?)
          pure false
        catch _ => pure true
      unless rejected do throwError "a nested source action selected an independent opaque ring"

end CasCompiler.PublishedSymbolicSourceTests
