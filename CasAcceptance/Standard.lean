module

public import LeanCategories.Catalogue.Semantics
public import CasCatalogue.Registry
public meta import LeanCategories.Catalogue.Semantics
public meta import CasCatalogue.Registry

@[expose] public section

/-!
# The exported registry manifest's integrity

Which rows exist is `lean-categories`' alone: `normalized_registry` refuses every module outside
it, and `SemanticProjectionProbes` checks that every semantic row was written in
`LeanCategories.Catalogue`. No list of those rows is kept here; a downstream copy of them would be
a mirror that every upstream row invalidates. What the export must itself guarantee is that a
stable id names one row of its kind.
-/

namespace CasCatalogue.Catalogue.Standard

open CasCatalogue

/-- The ids that occur more than once in `ids`. -/
def duplicates (ids : Array String) : Array String :=
  ids.foldl (init := #[]) fun out id =>
    if (ids.filter (· == id)).size > 1 && !out.contains id then out.push id else out

/-- Each stable id of `kind` names one row. -/
def validateStableIds (kind : String) (ids : Array String) : Except String Unit :=
  match duplicates ids with
  | #[] => .ok ()
  | repeated => .error s!"standard manifest {kind}: stable ids name several rows: {repeated}"

/-- Validate every row kind emitted by the standard registry manifest. -/
def validateStandardManifest (manifest : RegistryManifest) : Except String Unit := do
  validateStableIds "categories" (manifest.categories.map (·.id))
  validateStableIds "category families" (manifest.categoryFamilies.map (·.id))
  validateStableIds "classifiers" (manifest.classifiers.map (·.id))
  validateStableIds "functors" (manifest.functors.map (·.id))
  validateStableIds "constructors" (manifest.constructors.map (·.id))
  validateStableIds "fibrations" (manifest.fibrations.map (·.id))
  validateStableIds "methods" (manifest.methods.map (·.id))
  validateStableIds "properties" (manifest.properties.map (·.id))
  validateStableIds "lifts" (manifest.lifts.map (·.id))
  validateStableIds "cells" (manifest.cells.map (·.id))
  validateStableIds "limits" (manifest.limits.map (·.id))
  validateStableIds "adjunctions" (manifest.adjunctions.map (·.id))
  validateStableIds "opaque categories" (manifest.opaqueCategories.map (·.id))
  validateStableIds "opaque ports"
    (manifest.opaqueCategories.flatMap (fun category => category.ports.map (·.id)))

-- A repeated stable id fails the standard contract; distinct ones pass.
#guard duplicates #["cat.sets", "cat.groups", "cat.sets"] == #["cat.sets"]
#guard (validateStableIds "categories" #["cat.sets", "cat.sets"]).isOk == false
#guard (validateStableIds "categories" #["cat.sets", "cat.groups"]).isOk

end CasCatalogue.Catalogue.Standard
