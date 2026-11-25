module

public import CasCompiler.CreationInterface
public import CasCompiler.SourceReference
public import CasCompiler.Layout
public import LeanCategories.Catalogue.Registry.Semantic

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The fixed native creation family of one accepted lift. The original evidence parameters
are followed by the actual source diagram, mapped cone and its data-bearing IsLimit interface.
The result is Mathlib's existing LiftsToLimit; no new mathematical computation is defined. -/
structure CreationFamily where
  private mk ::
  entry : LiftEntry
  universeParams : List Name
  parameterCount : Nat
  evidenceFamily : Expr
  evidenceType : Expr
  family : Expr
  familyType : Expr

private def creationResolved (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars then
    throwError "the selected creation requires all original native parameters"
  check value
  return value

/-- The instance is the selected evidence's own field at D, never an instance search. -/
private def creationInstance (evidence diagram : Expr) : MetaM Expr := do
  let type ← whnfR (← inferType evidence)
  unless type.isAppOfArity ``CategoryTheory.CreatesLimitsOfShape 7 do
    throwError "the selected creation evidence has another native interface"
  mkAppOptM ``CategoryTheory.CreatesLimitsOfShape.CreatesLimit
    ((type.getAppArgs.map some) ++ #[some evidence, some diagram])

/-- Exact native argument order in Creates.lean: C, its category, D, its category, J,
its category, K, F, the selected CreatesLimit, the target cone, and its IsLimit data. -/
private def creationArguments (diagram functor instance_ cone universal : Expr) :
    Array (Option Expr) :=
  #[none, none, none, none, none, none, some diagram, some functor, some instance_,
    some cone, some universal]

/-- Read the complete evidence family under rigid universes before specializing any actual
diagram or result. Reuse: CreatesLimitsOfShape.CreatesLimit and liftsToLimitOfCreates at the
pinned native source; layout retains LiftableCone.validLift and LiftsToLimit.makesLimit. -/
opaque CreationFamily.forLift (entry : LiftEntry) : MetaM CreationFamily := withLCtx {} #[] do
  let .createsLimits _ := entry.kind
    | throwError "a native creation family requires an accepted creates-limits lift"
  let information ← checkedDeclaration entry.evidence
  let evidenceFamily := mkConst entry.evidence (information.levelParams.map Level.param)
  discard <| checkedDeclaration ``CategoryTheory.liftsToLimitOfCreates
  forallTelescope information.type fun parameters result => do
    let result ← whnfR result
    let #[source, sourceInstance, _, _, shape, shapeInstance, functor] :=
        result.getAppArgs
      | throwError "the creation evidence changed its complete native family"
    unless result.isAppOfArity ``CategoryTheory.CreatesLimitsOfShape 7 do
      throwError "the creation evidence is not CreatesLimitsOfShape"
    let diagramType ← mkAppOptM ``CategoryTheory.Functor
      #[some shape, some shapeInstance, some source, some sourceInstance]
    withLocalDeclD `diagram diagramType fun diagram => do
      let evidence := mkAppN evidenceFamily parameters
      let instance_ ← creationInstance evidence diagram
      let image ← mkAppM ``CategoryTheory.Functor.comp #[diagram, functor]
      let coneType ← mkAppM ``CategoryTheory.Limits.Cone #[image]
      withLocalDeclD `cone coneType fun cone => do
        let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
        withLocalDeclD `universal universalType fun universal => do
          let value ← mkAppOptM ``CategoryTheory.liftsToLimitOfCreates
            (creationArguments diagram functor instance_ cone universal)
          let family ← mkLambdaFVars (parameters ++ #[diagram, cone, universal]) value
            (usedOnly := false) (usedLetOnly := false)
          check family
          if family.hasMVar || family.hasLevelMVar then
            throwError "the whole native creation family has unresolved parameters"
          return ⟨entry, information.levelParams, parameters.size, evidenceFamily,
            information.type, family, ← inferType family⟩

/-- Resolve only the explicit accepted lift identity before preparing its complete native family. -/
opaque CreationFamily.forId (id : LiftId) : MetaM CreationFamily := do
  let state ← semanticState
  let #[entry] := state.lifts.filter (·.id == id)
    | throwError "the selected creation lost its unique original lift registration"
  CreationFamily.forLift entry

/-- Read this exact declared evidence at the chosen native functor and source diagram.
Only ordinary whole-type applicability is tested; no provider or result data participates. -/
opaque CreationFamily.evidenceAt? (family : CreationFamily) (functor diagram : Expr) :
    MetaM (Option Expr) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  let head := family.evidenceFamily.instantiateLevelParams family.universeParams levels
  let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType head)
  let type ← whnfR type
  unless type.isAppOfArity ``CategoryTheory.CreatesLimitsOfShape 7 do
    throwError "the creation evidence lost its prepared native interface"
  let diagramType ← whnfR (← inferType diagram)
  unless diagramType.isAppOfArity ``CategoryTheory.Functor 4 do
    throwError "the selected creation diagram has no complete native functor interface"
  let expected ← mkAppOptM ``CategoryTheory.CreatesLimitsOfShape
    #[some diagramType.getAppArgs[2]!, some diagramType.getAppArgs[3]!, none, none,
      some diagramType.getAppArgs[0]!, some diagramType.getAppArgs[1]!, some functor]
  unless ← isDefEq type expected do return none
  return some (← creationResolved (mkAppN head parameters))

/-- Apply the exact prepared native family to its original evidence argument positions.
The supplied IsLimit remains a data input, independently of the cone and of proof fields. -/
opaque CreationFamily.atEvidence (family : CreationFamily)
    (evidence diagram cone universal : Expr) : MetaM Expr := do
  let evidence ← creationResolved evidence
  let .const declaration levels := evidence.consumeMData.getAppFn
    | throwError "the selected creation lost its original evidence declaration"
  unless declaration == family.entry.evidence &&
      evidence.getAppNumArgs == family.parameterCount &&
      levels.length == family.universeParams.length do
    throwError "the selected creation changed its complete evidence application"
  let function := family.family.instantiateLevelParams family.universeParams levels
  creationResolved (mkAppN function (evidence.getAppArgs ++ #[diagram, cone, universal]))

/-- Elaborate only the original declaration's explicit argument positions. Type comparison
checks applicability; the resulting application keeps each actual source expression at that
same slot, rather than substituting a diagram projection found by type conversion. -/
private def creationApplication? (declaration : Name) (arguments : Array Expr)
    (checkResult : Expr → MetaM Bool) : MetaM (Option Expr) := do
  discard <| checkedDeclaration declaration
  let function ← mkConstWithFreshMVarLevels declaration
  let (parameters, binders, result) ← forallMetaTelescopeReducing (← inferType function)
  unless (binders.filter (·.isExplicit)).size == arguments.size do return none
  let mut actual := parameters
  let mut argumentIndex := 0
  for parameter in parameters, binder in binders, index in [:parameters.size] do
    if binder.isExplicit then
      let some argument := arguments[argumentIndex]?
        | throwError "the source construction lost an explicit original argument"
      unless ← isDefEq (← inferType parameter) (← inferType argument) do return none
      unless ← isDefEq parameter argument do return none
      actual := actual.set! index argument
      argumentIndex := argumentIndex + 1
  unless ← checkResult (← instantiateMVars result) do return none
  return some (← creationResolved (mkAppN function actual))

private def creationRestoreBinders : List BinderInfo → Expr → MetaM Expr
  | [], value => pure value
  | info :: rest, .lam name type body _ => do
    return .lam name type (← creationRestoreBinders rest body) info
  | _, _ => throwError "the creation source telescope lost an original binder"

/-- Specialize only the diagram constructor parameters fixed by its original full Functor
type. The remaining original slots, including implicit data and proofs, stay in native order.
Metavariable identity records declared source indices; no actual expression selects a supplier. -/
opaque CreationFamily.sourceTelescope (diagram : Expr) : MetaM (Expr × Array Nat) :=
    withNewMCtxDepth do
  let .const declaration levels := diagram.consumeMData.getAppFn
    | throwError "the created source diagram lost its original constructor"
  discard <| checkedDeclaration declaration
  let constructor := mkConst declaration levels
  let (parameters, binders, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless parameters.size == diagram.getAppNumArgs do
    throwError "the created source diagram changed its complete original argument telescope"
  unless ← isDefEq result (← inferType diagram) do
    throwError "the source diagram constructor changed its complete native category or shape"
  let applied ← instantiateMVars (mkAppN constructor parameters)
  let abstracted ← abstractMVars applied
  let mut positions : Array Nat := #[]
  let mut annotations : Array BinderInfo := #[]
  let mut previous : Option Nat := none
  for parameter in abstracted.mvars do
    let some index := parameters.findIdx? (· == parameter)
      | throwError "the creation source telescope introduced an undeclared parameter"
    if let some earlier := previous then
      unless earlier < index do
        throwError "the creation source telescope changed original binder order"
    let some binder := binders[index]?
      | throwError "the creation source telescope lost an original binder annotation"
    positions := positions.push index
    annotations := annotations.push binder
    previous := some index
  let family ← creationRestoreBinders annotations.toList abstracted.expr
  let family ← creationResolved family
  return (family, positions)

private def creationDiagramCategory (bundle result : Expr) : MetaM Bool := do
  let result ← whnfR result
  unless result.isAppOfArity ``CategoryTheory.Functor 4 do return false
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let instance_ ← mkAppM ``CategoryTheory.Bundled.str #[bundle]
  (isDefEq result.getAppArgs[2]! carrier) <&&>
    (isDefEq result.getAppArgs[3]! instance_)

/-- Read the diagram constructor from the accepted standardization's original target.
No shape string, native enumeration order or result-apex recognition chooses a diagram. -/
opaque CreationFamily.diagramAt? (entry : LimitEntry) (bundle : Expr)
    (arguments : Array Expr) : MetaM (Option Expr) := do
  let some name := entry.standardization
    | throwError "the selected creation requires its declared diagram constructor standardization"
  let information ← checkedDeclaration name
  let constructor ← forallTelescope information.type fun _ result => do
    let result ← whnfR result
    unless result.isAppOfArity ``CategoryTheory.Iso 4 do
      throwError "the declared diagram standardization is not a complete native isomorphism"
    let .const constructor _ := result.getAppArgs[3]!.consumeMData.getAppFn
      | throwError "the declared diagram standardization has no native constructor target"
    return constructor
  creationApplication? constructor arguments (creationDiagramCategory bundle)

/-- The target presentation receives the actual mapped source arguments at its original
explicit positions; the standardization later checks the complete mapped diagram. -/
opaque CreationFamily.presentationAt? (entry : LimitEntry) (bundle : Expr)
    (arguments : Array Expr) : MetaM (Option Expr) := do
  unless !entry.colimit do
    throwError "a creates-limits witness cannot supply a colimit creation"
  creationApplication? entry.declaration arguments fun result => do
    let result ← whnfR result
    unless result.isAppOf ``CategoryTheory.Limits.LimitCone do
      throwError "the target creation presentation has another native result family"
    let some diagram := result.getAppArgs.back?
      | throwError "the target creation presentation lost its complete diagram"
    creationDiagramCategory bundle (← inferType diagram)

/-- Build the accepted native transport as source, preserving both original data inputs.
These expressions describe the fixed provider action; they are not computed port values. -/
private def creationStandardizedInputs (standardization cone universal : Expr) :
    MetaM (Expr × Expr) := do
  let inverse ← mkAppM ``CategoryTheory.Iso.inv #[standardization]
  let postcompose ← mkAppM ``CategoryTheory.Limits.Cone.postcompose #[inverse]
  let standardizedCone ← mkAppM ``CategoryTheory.Functor.obj #[postcompose, cone]
  let equivalence ← mkAppM ``CategoryTheory.Limits.IsLimit.postcomposeInvEquiv
    #[standardization, cone]
  let inverseEquivalence ← mkAppM ``Equiv.symm #[equivalence]
  let standardizedUniversal ← mkAppM ``Equiv.toFun #[inverseEquivalence, universal]
  let expectedUniversal ← mkAppM ``CategoryTheory.Limits.IsLimit #[standardizedCone]
  unless ← isDefEq (← inferType standardizedUniversal) expectedUniversal do
    throwError "the creation changed its exact standardized universal interface"
  return (standardizedCone, standardizedUniversal)

/-- One fixed source-derived request on the original target data. The selected evidence,
source diagram and comparison remain captured in their original context. In particular no
runtime source evaluation is needed to invent the standardized cone or its universal data.
The complete native output is LiftsToLimit, including validLift and makesLimit. -/
opaque CreationFamily.requestAt (family : CreationFamily)
    (evidence functor diagram : Expr) (target : NativeLimitInterface) : MetaM Expr := do
  let some standardization := target.standardization
    | throwError "the selected creation requires its declared diagram standardization"
  let image ← mkAppM ``CategoryTheory.Functor.comp #[diagram, functor]
  let expectedComparison ← mkAppM ``CategoryTheory.Iso #[image, target.diagram]
  unless ← isDefEq (← inferType standardization) expectedComparison do
    throwError "the creation changed its original mapped-diagram comparison"
  let coneType ← mkAppM ``CategoryTheory.Limits.Cone #[target.diagram]
  withLocalDeclD `targetCone coneType fun cone => do
    let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
    withLocalDeclD `targetUniversal universalType fun universal => do
      let (standardizedCone, standardizedUniversal) ←
        creationStandardizedInputs standardization cone universal
      let result ← family.atEvidence evidence diagram standardizedCone standardizedUniversal
      let request ← mkLambdaFVars #[cone, universal] result
        (usedOnly := false) (usedLetOnly := false)
      creationResolved request

/-- Complete rigid signature for publication of the existing standardized creation action.
The comparison is an explicit native context slot in this schema. A selected runtime request
captures its already accepted comparison with requestAt; providers do not choose this slot. -/
opaque CreationFamily.standardizedTemplate (family : CreationFamily) : MetaM Expr :=
    withLCtx {} #[] do
  lambdaTelescope family.family fun original _ => do
    unless original.size == family.parameterCount + 3 do
      throwError "the creation template lost its complete original native telescope"
    let parameters := original.extract 0 family.parameterCount
    let diagram := original[family.parameterCount]!
    let evidence := mkAppN family.evidenceFamily parameters
    let evidenceType ← whnfR (← inferType evidence)
    let #[_, _, target, targetInstance, shape, shapeInstance, functor] :=
        evidenceType.getAppArgs
      | throwError "the creation template lost its complete native category interface"
    let targetDiagramType ← mkAppOptM ``CategoryTheory.Functor
      #[some shape, some shapeInstance, some target, some targetInstance]
    let image ← mkAppM ``CategoryTheory.Functor.comp #[diagram, functor]
    withLocalDeclD `targetDiagram targetDiagramType fun targetDiagram => do
      let comparisonType ← mkAppM ``CategoryTheory.Iso #[image, targetDiagram]
      withLocalDeclD `standardization comparisonType fun standardization => do
        let coneType ← mkAppM ``CategoryTheory.Limits.Cone #[targetDiagram]
        withLocalDeclD `targetCone coneType fun cone => do
          let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
          withLocalDeclD `targetUniversal universalType fun universal => do
            let (standardizedCone, standardizedUniversal) ←
              creationStandardizedInputs standardization cone universal
            let result ← family.atEvidence evidence diagram standardizedCone standardizedUniversal
            let template ← mkLambdaFVars
              (parameters ++ #[diagram, targetDiagram, standardization, cone, universal]) result
              (usedOnly := false) (usedLetOnly := false)
            if template.hasFVar then
              throwError "the complete creation template retained an undeclared native input"
            creationResolved template

/-- Prepare the existing selected standardization and creation actions without evaluating them.
The target cone and its universal interface are projected independently from the same exact
original presentation. Neither returned cone data nor an equal native type selects the latter. -/
opaque CreationFamily.interfaceAt (family : CreationFamily) (evidence functor diagram : Expr)
    (target : NativeLimitInterface) : MetaM NativeLimitCreationInterface := do
  let some standardization := target.standardization
    | throwError "the selected creation requires its declared diagram standardization"
  let targetCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[target.presentation]
  let targetUniversal ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[target.presentation]
  let image ← mkAppM ``CategoryTheory.Functor.comp #[diagram, functor]
  let expectedComparison ← mkAppM ``CategoryTheory.Iso #[image, target.diagram]
  unless ← isDefEq (← inferType standardization) expectedComparison do
    throwError "the creation changed its original mapped-diagram comparison"
  let (standardizedCone, standardizedUniversal) ←
    creationStandardizedInputs standardization targetCone targetUniversal
  let createsLimit ← creationInstance evidence diagram
  let requestFamily ← family.requestAt evidence functor diagram target
  let result ← creationResolved (mkAppN requestFamily #[targetCone, targetUniversal])
  return {
    lift := family.entry.id
    declaration := family.entry.evidence
    edge := family.entry.edge
    evidence, createsLimit, functor, diagram, targetCone, targetUniversal, standardization,
    standardizedCone, standardizedUniversal, requestFamily, result }

/-- Keep the original source presentation's native liftLimit spelling while retaining the
complete liftsToLimitOfCreates result beside it. This is the same fixed accepted selection. -/
opaque NativeLimitCreationInterface.presentation (selected : NativeLimitCreationInterface) :
    MetaM Expr := do
  let arguments := creationArguments selected.diagram selected.functor selected.createsLimit
    selected.standardizedCone selected.standardizedUniversal
  let cone ← mkAppOptM ``CategoryTheory.liftLimit arguments
  let universal ← mkAppOptM ``CategoryTheory.liftedLimitIsLimit arguments
  creationResolved (← mkAppM ``CategoryTheory.Limits.LimitCone.mk #[cone, universal])

end CasCompiler
