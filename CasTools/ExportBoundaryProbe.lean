/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasTools.ExportJson

@[expose] public section

/-! External compile probes for the checked registry export boundary. -/

example : True := by
  fail_if_success
    let _ := CasCatalogue.registryExt.addEntry
    trivial
  fail_if_success
    let _ := CasCatalogue.Tools.snapshotManifestJson
    trivial
  fail_if_success
    let _ := CasCatalogue.RegistrySnapshot
    trivial
  exact True.intro

#check CasCatalogue.checkedRegistryManifest
