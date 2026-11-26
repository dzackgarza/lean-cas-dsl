module

public import CasCompiler.SelectionData

public section

namespace CasCompiler

open Lean CasCatalogue CasCatalogue.Backend

private def sameArray (equal : α → α → Bool) (left right : Array α) : Bool :=
  left.size == right.size && (left.zip right).all (fun (a, b) => equal a b)

private def sameOption (equal : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some left, some right => equal left right
  | _, _ => false

/-- Registry records contain closed declared syntax and have complete derived representations.
This comparison validates an already identical binding ID; it never searches for an owner. -/
private def sameStatic [Repr α] (left right : α) : Bool :=
  reprStr left == reprStr right

private def sameRoute (left right : Route) : Bool :=
  sameStatic left.source right.source && sameStatic left.target right.target &&
    sameArray (fun (a b : StructuralEdge) =>
      sameStatic a.source b.source && sameStatic a.target b.target &&
        reprStr a.expression == reprStr b.expression && sameStatic a.ref b.ref)
      left.steps right.steps

/-- Compare the complete originally selected route, including each ordered native edge. -/
def _root_.CasCatalogue.Route.exactlyMatches (left right : Route) : Bool :=
  sameRoute left right

private def sameNamed : SourceNamedEntry → SourceNamedEntry → Bool
  | .registered left leftCategory, .registered right rightCategory =>
      sameStatic left right && sameStatic leftCategory rightCategory
  | .construction left, .construction right => sameStatic left right
  | _, _ => false

private def sameReference : SelectedSourceReference → SelectedSourceReference → Bool
  | .named left, .named right => sameNamed left right
  | .category left, .category right => sameStatic left right
  | .operation left, .operation right => sameStatic left right
  | .method left leftFunctor, .method right rightFunctor =>
    sameStatic left right && sameStatic leftFunctor rightFunctor
  | .functor left, .functor right => sameStatic left right
  | .classifier left, .classifier right => sameStatic left right
  | .constructor left, .constructor right => sameStatic left right
  | .cell left, .cell right => sameStatic left right
  | .binder left, .binder right => sameStatic left right
  | .lift left, .lift right => sameStatic left right
  | .presentation left, .presentation right => sameStatic left right
  | .literal left, .literal right => sameStatic left right
  | .numeral left, .numeral right => sameStatic left right
  | .subset left, .subset right => sameStatic left right
  | .graph left, .graph right => sameStatic left right
  | .generator left, .generator right => sameStatic left right
  | .components left, .components right => sameStatic left right
  | .limit left, .limit right => sameStatic left right
  | .classifierForget left, .classifierForget right => sameStatic left right
  | .constructorInterface left leftField, .constructorInterface right rightField =>
      sameStatic left right && leftField == rightField
  | .refinement left leftRefinement, .refinement right rightRefinement =>
      sameStatic left right && sameStatic leftRefinement rightRefinement
  | _, _ => false

/-- Compare every field of the two already supplied accepted registry references. -/
def SelectedSourceReference.exactlyMatches (left right : SelectedSourceReference) : Bool :=
  sameReference left right

private def samePrerequisite (left right : CheckedComputationPrerequisite) : Bool :=
  sameStatic left.reference right.reference &&
    left.declaration == right.declaration &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType

private def sameProgram (left right : SourceProgram) : Bool :=
  sameStatic left.source.entry right.source.entry &&
    left.source.universeParams == right.source.universeParams &&
    left.source.targetDeclaration == right.source.targetDeclaration &&
    left.source.target.equal right.source.target &&
    left.source.familyType.equal right.source.familyType &&
    sameArray samePrerequisite left.source.prerequisites right.source.prerequisites &&
    left.source.template.equal right.source.template &&
    left.source.plan.equal right.source.plan &&
    left.source.correctness.equal right.source.correctness &&
    sameReference left.targetReference right.targetReference &&
    sameArray sameReference left.prerequisiteReferences right.prerequisiteReferences

private def samePointOwner : PointFamilyOwner → PointFamilyOwner → Bool
  | .morphism left, .morphism right => sameStatic left right
  | .application left, .application right => sameStatic left right
  | _, _ => false

private def samePointFamily (left right : PointFamily) : Bool :=
  samePointOwner left.owner right.owner &&
    left.declaration == right.declaration &&
    sameStatic left.category right.category &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType &&
    left.universeParams == right.universeParams &&
    left.path == right.path

private def sameFamily (left right : SourceFamily) : Bool :=
  samePrerequisite left.source right.source &&
    left.universeParams == right.universeParams &&
    sameReference left.selectedReference right.selectedReference &&
    sameOption samePointFamily left.pointFamily right.pointFamily

private def sameLift (left right : LiftFamily) : Bool :=
  left.lift == right.lift &&
    sameStatic left.entry right.entry &&
    left.port == right.port &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType &&
    left.universeParams == right.universeParams

private def samePresentation (left right : PresentationFamily) : Bool :=
  sameStatic left.entry right.entry &&
    sameStatic left.source right.source &&
    sameStatic left.target right.target &&
    sameStatic left.category right.category &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType &&
    left.universeParams == right.universeParams &&
    left.forwardPath == right.forwardPath &&
    left.inversePath == right.inversePath

private def sameActionFamily (left right : SourceActionFamily) : Bool :=
  sameStatic left.edge right.edge &&
    left.declaration == right.declaration &&
    left.universeParams == right.universeParams &&
    left.parameterCount == right.parameterCount &&
    sameStatic left.category right.category &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType &&
    sameArray sameReference left.references right.references


private def sameMethodReturn (left right : RoutedMethodReturn) : Bool :=
  sameRoute left.route right.route &&
    sameArray sameStatic left.rows right.rows &&
    sameArray Expr.equal left.actions right.actions &&
    sameArray sameActionFamily left.actionFamilies right.actionFamilies &&
    sameOption Expr.equal left.agreement right.agreement &&
    sameArray Expr.equal left.evidences right.evidences &&
    sameStatic left.category right.category &&
    left.categoryFamily.equal right.categoryFamily &&
    left.resultFamily.equal right.resultFamily

private def sameMethod (left right : RoutedMethodFamily) : Bool :=
  sameStatic left.entry right.entry &&
    sameRoute left.route right.route &&
    sameStatic left.functor right.functor &&
    left.categoryFamily.equal right.categoryFamily &&
    left.functorFamily.equal right.functorFamily &&
    left.family.equal right.family &&
    sameArray Expr.equal left.actions right.actions &&
    sameArray sameActionFamily left.actionFamilies right.actionFamilies &&
    sameArray (sameOption sameStatic) left.receiverViews right.receiverViews &&
    left.universeParams == right.universeParams &&
    left.parameterCount == right.parameterCount &&
    sameOption sameMethodReturn left.returns right.returns

private def sameProperty (left right : PropertyFamily) : Bool :=
  sameStatic left.entry right.entry &&
    sameStatic left.classifier right.classifier &&
    sameRoute left.route right.route &&
    left.categoryFamily.equal right.categoryFamily &&
    left.family.equal right.family &&
    sameArray Expr.equal left.actions right.actions &&
    sameArray sameActionFamily left.actionFamilies right.actionFamilies &&
    sameArray (sameOption sameStatic) left.receiverViews right.receiverViews &&
    left.universeParams == right.universeParams &&
    left.parameterCount == right.parameterCount

private def sameCategoricalOwner : CategoricalPointOwner → CategoricalPointOwner → Bool
  | .named left, .named right => samePointOwner left right
  | .component left leftConstructors leftInverse, .component right rightConstructors rightInverse =>
      sameStatic left right && leftConstructors == rightConstructors && leftInverse == rightInverse
  | .cartesian left, .cartesian right => sameStatic left right
  | .binder left, .binder right => sameStatic left right
  | .action left, .action right => sameStatic left right
  | _, _ => false

private def sameRouteFunctor (termEqual : α → α → Bool) (left right : NativeRouteFunctor α) : Bool :=
  termEqual left.functor right.functor &&
    termEqual left.target right.target &&
    sameArray termEqual left.actions right.actions

private def sameCell (termEqual : α → α → Bool) (left right : NativeSourceCell α) : Bool :=
  sameStatic left.entry right.entry &&
    termEqual left.application right.application &&
    left.inverse == right.inverse &&
    left.constructors == right.constructors &&
    sameStatic left.source right.source &&
    termEqual left.sourceBundle right.sourceBundle &&
    sameStatic left.target right.target &&
    termEqual left.targetBundle right.targetBundle &&
    sameRouteFunctor termEqual left.left right.left &&
    sameRouteFunctor termEqual left.right right.right &&
    termEqual left.transformation right.transformation &&
    sameOption termEqual left.isomorphism right.isomorphism &&
    sameArray sameReference left.references right.references

private def sameComponent (termEqual : α → α → Bool) (left right : NativeSourceCellComponent α) : Bool :=
  sameCell termEqual left.cell right.cell &&
    termEqual left.receiver right.receiver &&
    termEqual left.value right.value

private def sameCartesian (termEqual : α → α → Bool) (left right : NativeSourceCartesian α) : Bool :=
  sameStatic left.entry right.entry &&
    termEqual left.application right.application &&
    termEqual left.realization right.realization &&
    termEqual left.baseMap right.baseMap &&
    termEqual left.receiver right.receiver &&
    termEqual left.totalBundle right.totalBundle &&
    termEqual left.arrow right.arrow

private def sameCategoricalFamily (left right : CategoricalPointFamily) : Bool :=
  sameCategoricalOwner left.owner right.owner &&
    left.declaration == right.declaration &&
    left.universeParams == right.universeParams &&
    left.declarationParameterCount == right.declarationParameterCount &&
    left.parameterCount == right.parameterCount &&
    sameStatic left.category right.category &&
    left.categoryFamily.equal right.categoryFamily &&
    left.arrowFamily.equal right.arrowFamily &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType &&
    left.whole == right.whole &&
    left.invocation == right.invocation &&
    sameArray sameReference left.references right.references &&
    sameOption (sameComponent Expr.equal) left.componentTemplate right.componentTemplate &&
    sameOption (sameCartesian Expr.equal) left.cartesianTemplate right.cartesianTemplate

private def sameLimitFamily (left right : LimitFamily) : Bool :=
  sameStatic left.entry right.entry &&
    sameStatic left.category right.category &&
    left.universeParams == right.universeParams &&
    left.parameterCount == right.parameterCount &&
    left.presentationFamily.equal right.presentationFamily &&
    left.diagramFamily.equal right.diagramFamily &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType

private def sameUniversalFamily (left right : LimitUniversalFamily) : Bool :=
  sameLimitFamily left.presentation right.presentation &&
    left.projection == right.projection &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType

private def sameCreationFamily (left right : CreationFamily) : Bool :=
  sameStatic left.entry right.entry &&
    left.universeParams == right.universeParams &&
    left.parameterCount == right.parameterCount &&
    left.evidenceFamily.equal right.evidenceFamily &&
    left.evidenceType.equal right.evidenceType &&
    left.family.equal right.family &&
    left.familyType.equal right.familyType

private def sameApplicationFamily : SelectedApplicationFamily → SelectedApplicationFamily → Bool
  | .registered left, .registered right => sameFamily left right
  | .target left, .target right => sameProgram left right
  | .prerequisite left leftIndex, .prerequisite right rightIndex =>
      sameProgram left right && leftIndex.val == rightIndex.val
  | .lift left, .lift right => sameLift left right
  | .presentation left, .presentation right => samePresentation left right
  | .routedMethod left, .routedMethod right => sameMethod left right
  | .property left, .property right => sameProperty left right
  | .application left, .application right => samePointFamily left right
  | .point left, .point right => sameCategoricalFamily left right
  | .objectAction left, .objectAction right => sameActionFamily left right
  | .limit left, .limit right => sameLimitFamily left right
  | .limitUniversal left, .limitUniversal right => sameUniversalFamily left right
  | .creation left leftTarget, .creation right rightTarget =>
      sameCreationFamily left right && sameLimitFamily leftTarget rightTarget
  | _, _ => false

private def sameCarrier (termEqual : α → α → Bool) (left right : NativeSourceCarrierSelection α) : Bool :=
  sameStatic left.refs right.refs &&
    sameStatic left.target right.target &&
    left.identifications == right.identifications &&
    sameArray termEqual left.actions right.actions &&
    sameArray termEqual left.comparisons right.comparisons

private def sameInterface (termEqual : α → α → Bool) (left right : LimitInterface α) : Bool :=
  termEqual left.presentation right.presentation &&
    termEqual left.diagram right.diagram &&
    sameOption termEqual left.standardization right.standardization &&
    sameOption termEqual left.dataConstructor right.dataConstructor

private def sameCreation (termEqual : α → α → Bool) (left right : LimitCreationInterface α) : Bool :=
  left.lift == right.lift &&
    left.declaration == right.declaration &&
    sameStatic left.edge right.edge &&
    sameArray termEqual left.terms right.terms

private def sameSourceLimit (termEqual : α → α → Bool) (left right : NativeSourceLimitSelection α) : Bool :=
  left.row == right.row &&
    left.declaration == right.declaration &&
    termEqual left.cone right.cone &&
    left.colimit == right.colimit &&
    sameStatic left.category right.category &&
    termEqual left.bundle right.bundle &&
    termEqual left.presentation right.presentation &&
    termEqual left.diagram right.diagram &&
    sameInterface termEqual left.interface right.interface &&
    left.construction == right.construction &&
    sameOption termEqual left.ownerFamily right.ownerFamily &&
    sameOption (sameCreation termEqual) left.creation right.creation &&
    sameOption termEqual left.creationFamily right.creationFamily &&
    left.creationInputs == right.creationInputs

private def sameCategory (termEqual : α → α → Bool) (left right : NativeSourceCategory α) : Bool :=
  left.role == right.role &&
    sameStatic left.expression right.expression &&
    termEqual left.bundle right.bundle &&
    sameOption (sameCarrier termEqual) left.carrier right.carrier &&
    sameOption (sameSourceLimit termEqual) left.limit right.limit

private def sameElementOwner (termEqual : α → α → Bool) (left right : NativeSourceElementOwner α) : Bool :=
  sameCategory termEqual left.category right.category &&
    termEqual left.value right.value &&
    termEqual left.evidence right.evidence

private def sameTypeOrigin (termEqual : α → α → Bool) (left right : NativeSourceTypeOrigin α) : Bool :=
  sameCategory termEqual left.category right.category &&
    termEqual left.object right.object &&
    termEqual left.type right.type

private def samePointOrigin (termEqual : α → α → Bool) (left right : NativeSourcePointOrigin α) : Bool :=
  termEqual left.point right.point &&
    termEqual left.domain right.domain &&
    termEqual left.target right.target

private def samePowerObject (termEqual : α → α → Bool)
    (left right : NativePowerObject α) : Bool :=
  sameStatic left.row right.row &&
    sameStatic left.object right.object &&
    sameStatic left.category right.category &&
    termEqual left.base right.base

private def sameNamedRequest (termEqual : α → α → Bool) (left right : NativePointRequest α) : Bool :=
  termEqual left.arrow right.arrow &&
    termEqual left.domain right.domain &&
    termEqual left.source right.source &&
    termEqual left.target right.target &&
    termEqual left.point right.point

private def sameCategoricalRequest (termEqual : α → α → Bool) (left right : CategoricalPointRequest α) : Bool :=
  termEqual left.arrow right.arrow &&
    termEqual left.domain right.domain &&
    termEqual left.source right.source &&
    termEqual left.target right.target &&
    termEqual left.point right.point

private def sameLimit (termEqual : α → α → Bool) (left right : NativeLimitSelection α) : Bool :=
  sameSourceLimit termEqual left.source right.source &&
    termEqual left.receiver right.receiver

private def sameLeg (termEqual : α → α → Bool) (left right : NativeLimitLegSelection α) : Bool :=
  sameLimit termEqual left.construction right.construction &&
    termEqual left.index right.index &&
    termEqual left.value right.value

private def sameSelectedLimitOwner (termEqual : α → α → Bool)
    (left right : SelectedLimitOwner α) : Bool :=
  sameLimit termEqual left.selection right.selection &&
    left.formalBindings == right.formalBindings

private def sameApplication (termEqual : α → α → Bool) (left right : SelectedSourceApplication α) : Bool :=
  sameApplicationFamily left.family right.family &&
    left.universes == right.universes &&
    sameArray termEqual left.parameters right.parameters &&
    sameArray termEqual left.arguments right.arguments &&
    sameOption termEqual left.owner right.owner &&
    sameOption (sameSelectedLimitOwner termEqual) left.ownerSelection right.ownerSelection

private def sameAdmission (termEqual : α → α → Bool) (left right : SelectedSourceAdmission α) : Bool :=
  sameStatic left.entry right.entry &&
    termEqual left.family right.family &&
    sameArray termEqual left.arguments right.arguments &&
    left.element == right.element

private def samePointRequest (termEqual : α → α → Bool) :
    SelectedSourcePointRequest α → SelectedSourcePointRequest α → Bool
  | .named leftFamily left, .named rightFamily right =>
      samePointFamily leftFamily rightFamily && sameNamedRequest termEqual left right
  | .categorical leftFamily left, .categorical rightFamily right =>
      sameCategoricalFamily leftFamily rightFamily && sameCategoricalRequest termEqual left right
  | _, _ => false

private def sameField (termEqual : α → α → Bool) (left right : SelectedSourceField α) : Bool :=
  left.selection == right.selection &&
    left.projection == right.projection &&
    termEqual left.owner right.owner &&
    left.deferredCone == right.deferredCone

private def sameEndpoint (termEqual : α → α → Bool) (left right : SelectedSourceEndpoint α) : Bool :=
  termEqual left.arrow right.arrow &&
    left.side == right.side &&
    termEqual left.value right.value

/-- Compare the complete already-selected rigid family, including its checked native data. -/
def SelectedApplicationFamily.exactlyMatches (left right : SelectedApplicationFamily) : Bool :=
  sameApplicationFamily left right

/-- Compare a point request's selected owner and every original operand. -/
def SelectedSourcePointRequest.exactlyMatches (termEqual : α → α → Bool)
    (left right : SelectedSourcePointRequest α) : Bool :=
  samePointRequest termEqual left right

/-- Compare all retained data at the same native binding identity. Native fields are
compared by the supplied exact representation equality, never by definitional equality. -/
def SourceSelection.exactlyMatches (termEqual : α → α → Bool)
    (left right : SourceSelection α) : Bool :=
  termEqual left.value right.value &&
    left.formalBindings == right.formalBindings &&
    sameStatic left.carrierRoutes right.carrierRoutes &&
    sameOption sameStatic left.preferredRoute right.preferredRoute &&
    sameStatic left.operationRefinements right.operationRefinements &&
    sameArray (fun (reference, route) (otherReference, otherRoute) =>
      sameReference reference otherReference && sameStatic route otherRoute)
      left.alternatives right.alternatives &&
    sameOption sameReference left.reference right.reference &&
    sameOption sameReference left.observation right.observation &&
    sameOption termEqual left.originalApplication right.originalApplication &&
    sameOption (sameApplication termEqual) left.application right.application &&
    sameOption (fun (family, target) (otherFamily, otherTarget) =>
      sameCreationFamily family otherFamily && sameLimitFamily target otherTarget)
      left.creationOwner right.creationOwner &&
    sameOption (sameAdmission termEqual) left.admission right.admission &&
    sameOption (fun (a, b) (c, d) => termEqual a c && termEqual b d)
      left.presentationEndpoints right.presentationEndpoints &&
    sameOption (sameArray (sameArray termEqual)) left.routedInputs right.routedInputs &&
    left.legOrdinal == right.legOrdinal &&
    left.recordSelection == right.recordSelection &&
    sameOption termEqual left.recordOwner right.recordOwner &&
    sameOption (sameCategory termEqual) left.category right.category &&
    sameOption (sameTypeOrigin termEqual) left.typeOrigin right.typeOrigin &&
    sameOption (sameElementOwner termEqual) left.elementOwner right.elementOwner &&
    sameOption (samePointOrigin termEqual) left.pointOrigin right.pointOrigin &&
    sameOption (samePointRequest termEqual) left.pointRequest right.pointRequest &&
    sameOption termEqual left.isoOrigin right.isoOrigin &&
    sameOption (sameField termEqual) left.field right.field &&
    sameOption (sameEndpoint termEqual) left.endpoint right.endpoint &&
    sameOption sameLimitFamily left.limitFamily right.limitFamily &&
    sameOption (sameLimit termEqual) left.limit right.limit &&
    sameOption (sameLeg termEqual) left.leg right.leg &&
    sameOption (sameCell termEqual) left.cellFamily right.cellFamily &&
    sameOption (sameComponent termEqual) left.cell right.cell &&
    sameOption (sameCartesian termEqual) left.cartesian right.cartesian &&
    sameOption (samePowerObject termEqual) left.powerObject right.powerObject

/-- Equality of complete selection tables, indexed only by stable native binding IDs. -/
def SourceSelectionScope.exactlyMatches (termEqual : α → α → Bool)
    (left right : SourceSelectionScope α) : Bool :=
  left.size == right.size && left.toList.all fun (binding, selection) =>
    match right[binding]? with
    | some other => selection.exactlyMatches termEqual other
    | none => false

end CasCompiler
