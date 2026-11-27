#!/usr/bin/env bash
set -eu
source scripts/container.sh
incontainer lake env python3 .tmp/diagnostic-json-graph-20261125-01/runner.py
