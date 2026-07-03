#!/usr/bin/env bash
# Build + render the DedekindResidue Verso blueprint.
#
# NOTE (macOS): this CANNOT run on macOS — Lean clamps RLIMIT_NOFILE to
# OPEN_MAX (10240) at startup, and the classic-mode Verso genre importing the
# module-system mathlib needs ~15k open files (.olean + .olean.server per
# module). Run on Linux (CI), where no such clamp applies.
set -euo pipefail
cd "$(dirname "$0")/.."
ulimit -n 65536 || true
lake build DedekindResidueBlueprint
lake build DedekindResidueBlueprintMain
lake env lean --run ../DedekindResidueBlueprintMain.lean --output _out/site
test -d _out/site && echo "site rendered under _blueprint/_out/site"
