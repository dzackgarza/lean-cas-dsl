module

public import CasCompiler.Layout
public import CasCompiler.LimitInterface

public section

namespace CasCompiler

open Lean Meta

/-- One original argument of an accepted dependent data constructor. Native and wire
positions remain distinct, and proof slots keep their binding identity without a payload. -/
structure ConstructorPort where
  private mk ::
  binding : BindingId
  argument : ArgumentLayout

/-- The complete source telescope of one already accepted data constructor. These formal
locals describe its ports; no returned data is substituted into the native constructor. -/
structure ConstructorPorts where
  private mk ::
  interface : LimitInterface ClosedTerm
  originalContext : ContextTelescope
  context : ContextTelescope
  contextInputs : Array BindingId
  ports : Array ConstructorPort
  application : ApplicationLayout

/-- Prepare every remaining native argument in its original order, including proof and
implicit positions. Reuse: the accepted LimitInterface.dataConstructor, ContextTelescope,
ApplicationLayout.ofSource and its original argument type families. The caller supplies
fresh source identities from the current preparation; the compiler owns no runtime graph. -/
opaque ConstructorPorts.prepare (interface : LimitInterface ClosedTerm)
    (freshBinding : MetaM BindingId) : MetaM ConstructorPorts := do
  let some constructor := interface.dataConstructor
    | throwError "the accepted construction has no complete native data constructor"
  constructor.withOpen fun originalBindings expression => do
    let originalContext ← ContextTelescope.capture originalBindings
    -- All parts of the accepted interface must remain in this exact original source scope.
    discard <| interface.presentation.inContext originalContext
    discard <| interface.diagram.inContext originalContext
    if let some standardization := interface.standardization then
      discard <| standardization.inContext originalContext
    forallTelescope (← inferType expression) fun arguments _ => do
      let mut bindings := originalBindings
      let mut portBindings := #[]
      for argument in arguments do
        let id ← freshBinding
        let proof ← isProof argument
        let declaration ← getFVarLocalDecl argument
        let role := if proof then BindingRole.hypothesis
          else if declaration.binderInfo == .instImplicit then .instance
          else .parameter
        bindings := bindings.push { id, role, expression := argument }
        portBindings := portBindings.push id
      let context ← ContextTelescope.capture bindings
      let function ← SourceLayout.ofTerm (← context.close expression)
      let sources ← arguments.mapM context.close
      let (_, application) ← ApplicationLayout.ofSource function context sources
      unless application.arguments.size == portBindings.size do
        throwError "the accepted constructor changed its complete native port telescope"
      let ports := portBindings.zipWith (fun binding argument =>
        (⟨binding, argument⟩ : ConstructorPort)) application.arguments
      let mut contextInputs := #[]
      for binding in bindings do
        unless ← isProof binding.expression do contextInputs := contextInputs.push binding.id
      return ⟨interface, originalContext.telescope, context.telescope, contextInputs,
        ports, application⟩

/-- Follow only a source-authored native result projection back to its original constructor
argument/context position. Matcher-defined components remain delayed; no ordinal is guessed. -/
def ConstructorPorts.projectionAt (ports : ConstructorPorts) (path : Array Name) :
    MetaM (Option InputProjection) :=
  ports.application.inputProjectionAt path ports.contextInputs

end CasCompiler
