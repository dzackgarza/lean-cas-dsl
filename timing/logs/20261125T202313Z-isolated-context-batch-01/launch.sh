#!/usr/bin/env bash
set -eu
source scripts/container.sh
incontainer lake env python3 .tmp/validation-context-batch-20261125-01/runner.py
