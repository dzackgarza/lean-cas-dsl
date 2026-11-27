#!/usr/bin/env bash
set -eu
source scripts/container.sh
incontainer lake env python3 .tmp/validation-value-visibility-20261125-02/runner.py
