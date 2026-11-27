#!/usr/bin/env bash
set -eu
source scripts/container.sh
incontainer lake env python3 .tmp/validation-json-graph-20261125-03/runner.py
