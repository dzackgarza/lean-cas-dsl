/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasContract.Registry.Extension

@[expose] public section

/-!
# Checked registry manifest

The registry extension owns its state and its serializer. External code can
request the checked manifest, but cannot provide replacement registry data.
-/
