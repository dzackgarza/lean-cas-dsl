module

public import CasCompiler.SelectionScope
public import LeanCategories.Catalogue.Registry.Entry

public section

namespace CasCompiler

open Lean Meta CasCatalogue


def SelectedSourceReference.declaration : SelectedSourceReference → Option Name
  | .named (.registered (.inl entry) _) => some entry.declaration
  | .named (.registered (.inr entry) _) => some entry.declaration
  | .named (.construction entry) => some entry.declaration
  | .category entry => some entry.declaration
  | .operation entry => some entry.declaration
  | .method _ nativeFunctor => some nativeFunctor.declaration
  | .functor entry => some entry.declaration
  | .classifier entry | .classifierForget entry => some entry.declaration
  | .constructor entry => some entry.semantics
  | .cell entry => some entry.declaration
  | .binder entry => some entry.operation
  | .lift entry => some entry.evidence
  | .presentation entry => some entry.declaration
  | .literal entry => some entry.denotation
  | .numeral entry => some entry.declaration
  | .subset entry => some entry.denotation
  | .graph entry => some entry.denotation
  | .generator entry => entry.generator
  | .components entry => entry.components.map (·.projection)
  | .limit entry => some entry.declaration
  | .constructorInterface entry field =>
    match field with
    | .functorialAction => entry.functorialAction
    | .comparisonAction => entry.comparisonAction
    | .identityComparison => entry.identityComparison
    | .compositionComparison => entry.compositionComparison
  | .refinement _ nativeRefinement => some nativeRefinement.identification


def SelectedSourceReference.computation? : SelectedSourceReference → Option ComputationRef
  | .named (.registered (.inr entry) _) => some (.morphism entry.id)
  | .named (.construction entry) => some (.construction entry.id)
  | .operation entry => some (.operation entry.id)
  | .method entry _ => some (.method entry.id)
  | .functor entry => some (.functor entry.id)
  | _ => none



def SelectedSourceReference.forComputation (reference : ComputationRef) :
    MetaM SelectedSourceReference := do
  let state ← semanticState
  match reference with
  | .operation id =>
    let #[entry] := state.operations.filter (·.id == id)
      | throwError "the accepted operation address has no unique original row"
    return .operation entry
  | .method id =>
    let #[entry] := state.methods.filter (·.id == id)
      | throwError "the accepted method address has no unique original row"
    let #[nativeFunctor] := state.functors.filter (·.id == entry.functor)
      | throwError "the accepted method lost its unique original functor row"
    return .method entry nativeFunctor
  | .functor id =>
    let #[entry] := state.functors.filter (·.id == id)
      | throwError "the accepted functor address has no unique original row"
    return .functor entry
  | .construction id =>
    let #[entry] := state.constructions.filter (·.id == id)
      | throwError "the accepted construction address has no unique original row"
    return .named (.construction entry)
  | .morphism id =>
    let #[entry] := state.morphisms.filter (·.id == id)
      | throwError "the accepted morphism address has no unique original row"
    let #[categoryRow] := state.categories.filter (·.id == entry.category)
      | throwError "the accepted morphism lost its original complete category row"
    return .named (.registered (.inr entry) categoryRow)


def SelectedSourceReference.descriptor? : SelectedSourceReference → Option (Name × String)
  | .named (.registered (.inl entry) _) => some (entry.declaration, entry.id.raw)
  | .category entry => some (entry.declaration, entry.id.raw)
  | .classifier entry => some (entry.declaration, entry.id.raw)
  | .constructor entry => some (entry.semantics, entry.id.raw)
  | .cell entry => some (entry.declaration, entry.id.raw)
  | .presentation entry => some (entry.declaration, entry.id.raw)
  | .literal entry => some (entry.denotation, entry.id.raw)
  | .graph entry => some (entry.denotation, entry.id.raw)
  | _ => none


def SelectedSourceReference.element? : SelectedSourceReference → Option (Name × String)
  | .numeral entry => some (entry.declaration, entry.id.raw)
  | .subset entry => some (entry.denotation, entry.id.raw)
  | .limit entry => some (entry.declaration, entry.id.raw)
  | .generator entry => entry.generator.map (fun declaration => (declaration, entry.id.raw ++ "#generator"))
  | _ => none

def SelectedSourceReference.nativeInterface? : SelectedSourceReference → Option Name
  | .constructorInterface entry field => (SelectedSourceReference.constructorInterface entry field).declaration
  | .refinement _ nativeRefinement => some nativeRefinement.identification
  | _ => none


def sourceReference (reference : SelectedSourceReference) (value : Expr) : SourceSelection Expr :=
  { value, reference := some reference }


def sourceDerivedReference (reference : SelectedSourceReference) (value : Expr) :
    SourceSelection Expr :=
  { value, observation := some reference }


def retainSourceApplication (selection : SourceSelection Expr) (application : Expr) :
    MetaM (SourceSelection Expr) := do
  let some reference := selection.reference
    | throwError "the source application has no original selected row"
  let some declaration := reference.declaration
    | throwError "the selected row has no declared native application"
  let application ← instantiateMVars application
  unless application.consumeMData.getAppFn.isConstOf declaration do
    throwError "the source application changed its selected original declaration"
  return { selection with originalApplication := some application }




private partial def sourceApplicationHead (application : Expr) : Expr :=
  let arguments := application.getAppArgs
  match application.getAppFn with
  | .mdata _ body => sourceApplicationHead (mkAppN body arguments)
  | .letE _ _ value body _ =>
    sourceApplicationHead (mkAppN (body.instantiate1 value) arguments)
  | .lam .. =>
    if arguments.isEmpty then application else sourceApplicationHead application.headBeta
  | _ => application



def sourceApplication? (declaration : Name) (selection : SourceSelection Expr) :
    MetaM (Option Expr) := do
  let some application := selection.originalApplication | return none
  let application := sourceApplicationHead application
  unless selection.reference.bind (·.declaration) == some declaration &&
      application.consumeMData.getAppFn.isConstOf declaration do
    throwError "the retained source application changed its selected original declaration \
      (expected {declaration}, retained {(selection.reference.bind (·.declaration)).getD .anonymous}, \
      head {application.getAppFn})"
  return some application

def sourceReferenceAt (reference : SelectedSourceReference) (application value : Expr) :
    MetaM (SourceSelection Expr) :=
  retainSourceApplication (sourceReference reference value) application



def sourceObjectSelection? (context : OpenContext) (scope : SourceSelectionScope Expr)
    (value : Expr) : MetaM (Option (ObjectEntry × NamedCategoryEntry)) := do
  let rec visit (fuel : Nat) (value : Expr) :
      MetaM (Option (ObjectEntry × NamedCategoryEntry)) := do
    match fuel with
    | 0 => throwError "the selected object reference has cyclic binding provenance"
    | fuel + 1 =>
      let some template := scope.findAt? context value.getAppFn | return none
      unless template.formalBindings.size == value.getAppNumArgs do return none
      let selected ← template.specialize value.getAppArgs
      match selected.reference with
      | some (.named (.registered (.inl entry) category)) => return some (entry, category)
      | _ =>
        if let some endpoint := selected.endpoint then return ← visit fuel endpoint.value
        return none
  visit (context.bindings.size + 1) value


def sourceObjectReference? (context : OpenContext) (scope : SourceSelectionScope Expr)
    (value : Expr) : MetaM (Option (ObjectId × Name)) := do
  return (← sourceObjectSelection? context scope value).map fun (entry, _) =>
    (entry.id, entry.declaration)

end CasCompiler
