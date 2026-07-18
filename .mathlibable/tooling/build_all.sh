#!/usr/bin/env bash
# build_all.sh — TRUE full-tree build gate for AINTLIB `main`.
#
# `lake build <lib>` compiles only modules reachable from that lib's root import,
# so orphan / WIP files (imported by nobody) are INVISIBLE — the green-gate blind
# spot that let mathlib-bump fallout hide in FLT37 orphans (#5700/#5705). This
# builds EVERY module in the workspace (via all_modules.py), orphans included, so
# RC=0 means the whole tree really compiles.
#
# Ends with a machine-readable `### build_all RC=<n>` line.
# Upgraded 2026-07-13 from lib-roots-only to full-module enumeration.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 3   # repo root (.mathlibable/tooling → repo)

export LEAN4_GUARDRAILS_BYPASS=1
PY="${LEAN4_PYTHON_BIN:-python3}"
TOOL="$(dirname "$0")/all_modules.py"

mapfile -t MODS < <("$PY" "$TOOL")
echo "### build_all: ${#MODS[@]} modules (full-tree, orphans included)"

# Build in batches so one invocation isn't thousands of args; lake parallelises
# within a batch and shares the build across batches. A batch failing does not
# abort the rest — we want the full red set, not just the first error.
rc=0
BATCH=250
total=${#MODS[@]}
for ((i=0; i<total; i+=BATCH)); do
  slice=("${MODS[@]:i:BATCH}")
  echo "### batch $((i/BATCH+1)): modules $((i+1))-$((i+${#slice[@]})) of $total"
  if ! lake build "${slice[@]}" 2>&1; then
    rc=1
  fi
done

echo "### build_all RC=$rc"
exit $rc
