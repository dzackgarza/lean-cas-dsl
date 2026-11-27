module

import CasCatalogue.TestSuite
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCatalogue.TestSuite
meta import LeanCategories.Catalogue

open Lean Elab Command

run_cmd do
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  IO.FS.writeFile (root / ".tmp/source-occurrences-empty.json")
    (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress

#cas_tests "tests/runtime/source_occurrences.cas"
  manifest "scripts/probes/kernel_session_peer.json"
  reporting ".tmp/source-occurrences-flat.json" computing

#cas_tests "tests/runtime/source_occurrences_nested.cas"
  manifest ".tmp/source-occurrences-empty.json"
  reporting ".tmp/source-occurrences-nested.json" computing
