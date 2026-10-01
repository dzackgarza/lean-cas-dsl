/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve

@[expose] public section

/-!
# Composing registered cells (`cell%`, CC-CALC)

`cell% c at (x) in "cat.id"` elaborates a composite `c` of registered cells and takes its component
at the object `x` of the registered category `cat.id`. The grammar of `c`:

* `"cell.id"`: a registered cell; `c⁻¹`: the inverse of a registered invertible cell;
* `c ≫ d`: vertical composition (`c`'s target composite must be `d`'s source composite);
* `"fun.id" ◁ c`, `c ▷ "fun.id"`: whiskering by a registered functor;
* `c ◫ d`: horizontal composition.

Every operation is Mathlib's (`≫`, `Functor.whiskerLeft`, `Functor.whiskerRight`,
`NatTrans.hcomp`, `Iso.inv`), applied to the registered declarations, so the composite is a
checked Mathlib natural transformation between the composites of registered functors, and its
component at `x` is a morphism of the catalogue's mathematics (`NatTrans.app`). Nothing here is
computed: what a cell does to data is a statement of the language, decided by
`CasCatalogue.Realize`.
-/

open Lean Meta Elab Term Command

namespace CasCatalogue

declare_syntax_cat casCell
syntax str : casCell
syntax:max "(" casCell ")" : casCell
syntax:80 casCell:80 "⁻¹" : casCell
syntax:70 str " ◁ " casCell:71 : casCell
syntax:70 casCell:70 " ▷ " str : casCell
syntax:65 casCell:65 " ◫ " casCell:66 : casCell
syntax:60 casCell:60 " ≫ " casCell:61 : casCell

syntax (name := cellCall) "cell% " casCell " at " "(" term ")" " in " str : term

/-- A composite cell: the Mathlib natural transformation, its inverse when it is invertible, and
the registered functors whose composites are its source and target. -/
structure CellTerm where
  nat : Expr
  inv? : Option Expr
  left : Array EdgeRef
  right : Array EdgeRef

/-- The registered functor named `raw`, as a Mathlib functor. -/
def registeredFunctorNamed (state : RegistryState) (raw : String) : MetaM (FunctorId × Expr) := do
  let some entry := state.functor? ⟨raw⟩ | throwError "no registered functor {raw}"
  return (entry.id, ← registeredFunctorInstance entry)

/-- A composite of registered functors, rendered; the empty composite is the identity. -/
def renderComposite (steps : Array EdgeRef) : String :=
  if steps.isEmpty then "𝟙" else renderSteps steps

/-- Elaborate a composite of registered cells. -/
partial def elabCellTerm (state : RegistryState) : Syntax → MetaM CellTerm
  | `(casCell| $s:str) => do
      let some entry := state.cells.find? (·.id.raw == s.getString)
        | throwError "no registered cell {s.getString}"
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (args, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
      let value := mkAppN declaration args
      if entry.invertible then
        return { nat := ← mkAppHere ``CategoryTheory.Iso.hom #[value]
                 inv? := some (← mkAppHere ``CategoryTheory.Iso.inv #[value])
                 left := entry.left, right := entry.right }
      else
        return { nat := value, inv? := none, left := entry.left, right := entry.right }
  | `(casCell| ($c)) => elabCellTerm state c
  | `(casCell| $c⁻¹) => do
      let t ← elabCellTerm state c
      let some inv := t.inv? | throwError "the cell is not registered invertible"
      return { nat := inv, inv? := some t.nat, left := t.right, right := t.left }
  | `(casCell| $c ≫ $d) => do
      let s ← elabCellTerm state c
      let t ← elabCellTerm state d
      unless s.right == t.left do
        throwError "vertical composition: the target {renderComposite s.right} of the first cell \
          is not the source {renderComposite t.left} of the second"
      let nat ← mkAppHere ``CategoryTheory.CategoryStruct.comp #[s.nat, t.nat]
      let inv? ← match s.inv?, t.inv? with
        | some i, some j => some <$> mkAppHere ``CategoryTheory.CategoryStruct.comp #[j, i]
        | _, _ => pure none
      return { nat, inv?, left := s.left, right := t.right }
  | `(casCell| $f:str ◁ $c) => do
      let (id, F) ← registeredFunctorNamed state f.getString
      let t ← elabCellTerm state c
      let whisker (α : Expr) := mkAppHere ``CategoryTheory.Functor.whiskerLeft #[F, α]
      return { nat := ← whisker t.nat, inv? := ← t.inv?.mapM whisker
               left := #[.functor id] ++ t.left, right := #[.functor id] ++ t.right }
  | `(casCell| $c ▷ $f:str) => do
      let (id, F) ← registeredFunctorNamed state f.getString
      let t ← elabCellTerm state c
      let whisker (α : Expr) := mkAppHere ``CategoryTheory.Functor.whiskerRight #[α, F]
      return { nat := ← whisker t.nat, inv? := ← t.inv?.mapM whisker
               left := t.left.push (.functor id), right := t.right.push (.functor id) }
  | `(casCell| $c ◫ $d) => do
      let s ← elabCellTerm state c
      let t ← elabCellTerm state d
      let nat ← mkAppHere ``CategoryTheory.NatTrans.hcomp #[s.nat, t.nat]
      return { nat, inv? := none, left := s.left ++ t.left, right := s.right ++ t.right }
  | _ => throwUnsupportedSyntax

/-- Elaborate `cell% c at (x) in "cat.id"`: the component of the composite cell at the object `x`
of the registered category, elaborated as an object of it. -/
def elabCellCall (cell : Syntax) (receiver : Term) (category : String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let t ← elabCellTerm state cell
  let x ← elabTermEnsuringType receiver (← categoryCarrierInstance categoryEntry)
  synthesizeSyntheticMVarsNoPostponing
  -- Elaborated at the current depth, so that the cell's universe levels are assigned by `x`'s
  -- category (as `Semantic.objOf`).
  let component ← elabTermAndSynthesize (← `(CategoryTheory.NatTrans.app
    $(← exprToSyntax t.nat) $(← exprToSyntax (← instantiateMVars x)))) none
  instantiateMVars component

end CasCatalogue
