/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasTools.ExportJson
public import CasAcceptance.Standard
public import Lean.Data.Json
public import Lean.CoreM

public meta import CasTools.ExportJson

@[expose] public section

/-!
# Registry export (`lean-categories-export`)

Emits JSON from the Lean registry. The executable reloads the module that owns
the private persistent extension `LeanCategories.registryExt` from
`CasCatalogue.Catalogue.Registry.Extension`, then calls the checked manifest
path `CasCatalogue.checkedRegistryManifest`.

Does **not** read external semantic-seed artifacts.
-/

open Lean Elab Command

namespace CasCatalogue.Tools.ExportFull
open LeanCategories

open LeanCategories CasCatalogue
open Tools

/-- Reload the compiled registry extension; this is the exporter data source. -/
def readRegistryManifest : IO CasCatalogue.RegistryManifest := do
  let appDir ← IO.appDir
  let buildOleanRoot := appDir.parent.get! / "lib" / "lean"
  let workspaceRoot := appDir.parent.get!.parent.get!.parent.get!
  let packagesDir := workspaceRoot / ".lake" / "packages"
  let packageOleanRoots ← (← packagesDir.readDir).toList.mapM fun entry =>
    pure (entry.path / ".lake" / "build" / "lib" / "lean")
  Lean.initSearchPath (← Lean.findSysroot) (buildOleanRoot :: packageOleanRoots)
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules
    #[{ module := `CasAcceptance.Standard }] {}
    (loadExts := true)
  let result ← Lean.Core.CoreM.toIO CasCatalogue.checkedRegistryManifestDTO
    { fileName := "", options := {}, fileMap := default } { env }
  pure result.1

def loadRegisteredManifest : IO Json := do
  return toJson (← readRegistryManifest)

/-- Validate Lean-authored registry JSON: `j`, parsed back from the emitted text, is exactly the
checked registry state's JSON. -/
def validate (expected : CasCatalogue.RegistryManifest) (j : Json) : Except String Unit := do
  CasCatalogue.Catalogue.Standard.validateStandardManifest expected
  unless j == toJson expected do
    throw "exported registry manifest does not match the checked registry state"
  pure ()

def run : IO UInt32 := do
  let expected ← readRegistryManifest
  let manifest := toJson expected
  match Json.parse manifest.compress with
  | .error e =>
      IO.eprintln s!"JSON parse failed: {e}"
      return 1
  | .ok j =>
      match validate expected j with
      | .error e =>
          IO.eprintln e
          return 1
      | .ok () =>
          IO.println manifest.compress
          pure 0

def main : IO UInt32 :=
  run

end CasCatalogue.Tools.ExportFull
