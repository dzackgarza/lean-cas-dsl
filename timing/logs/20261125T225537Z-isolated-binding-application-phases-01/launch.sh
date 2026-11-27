#!/usr/bin/env bash
set -eu
source scripts/container.sh
incontainer lake env python3 .tmp/validation-binding-application-phases-20261125-01/runner.py
