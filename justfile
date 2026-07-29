# lean-cas-dsl — categorically organized CAS in Lean, an nbdsl DSL plugin.
#
# One Lake package (library CasDsl + prelude CasDsl.Notebook) over the
# nbdsl-worker core, plus the Python half of the Sage adapter
# (backends/sage_adapter.py, runs under `sage -python`). Lake owns
# compilation; language-level QC delegates to the global gates.

set dotenv-load := true

# Show available recipes
default:
    @just --list

# Fetch Mathlib's prebuilt compilation cache
cache:
    @lake exe cache get

# Build the CasDsl library (and the worker it depends on)
build:
    @lake build CasDsl

# Run the repository QC gate
test: build
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry

[private]
test-commit: test

# Run the CI quality gate
test-ci: test

[private]
test-push: test-ci
