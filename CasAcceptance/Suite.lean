/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.TestSuite
public meta import CasAcceptance.Standard
public meta import CasCatalogue.TestSuite

public section

/-!
# The acceptance suite, over this repository's litmus leaves

The files of `tests/acceptance/`, written in the language, run over the realizations installed
here. Gaps are reported, not failed: they are the implementations the suite derives.
-/

#cas_tests "tests/acceptance"
