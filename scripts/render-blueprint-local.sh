#!/usr/bin/env bash
#
# Render a project's Verso blueprint IN PLACE in the main (already-built) AINTLIB checkout,
# using the disk-safe "path-mathlib" recipe. This is the counterpart to build-blueprints.sh:
#
#   - build-blueprints.sh  — CI-oriented: throwaway worktree per dev branch + `lake update` +
#     `lake exe cache get`. Needs an AINTLIB olean cache and plenty of free disk. It re-resolves
#     mathlib, so on a near-full disk it tries to clone ~7 GB of mathlib and fails.
#
#   - render-blueprint-local.sh (this) — reuses THIS checkout's already-built mathlib + project
#     oleans via the side-build's committed lake-manifest.json (mathlib pinned as a *path* to
#     ../../../.lake/packages/mathlib — NO clone, NO `lake update`, NO `cache get`), and hardlinks
#     the Verso packages from a sibling side-build (cp -al, near-zero disk). This is what actually
#     works on the dev machine (~99 % full).
#
# Usage:
#   scripts/render-blueprint-local.sh <ProjectDir> <BlueprintLib> [<DonorProjectDir>]
# e.g.
#   scripts/render-blueprint-local.sh Chebotarev        CebotarevDensityBlueprint  LeanModularForms
#   scripts/render-blueprint-local.sh FltRegularBernoulli BernoulliRegularBlueprint LeanModularForms
#
# Prereqs: the side-build (projects/<ProjectDir>/_blueprint/) exists with its lakefile.toml +
# lake-manifest.json (mathlib as a path), and the blueprint sources live one dir up as
# <BlueprintLib>/ + <BlueprintLib>.lean + <BlueprintLib>Main.lean.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROJ="${1:?usage: render-blueprint-local.sh <ProjectDir> <BlueprintLib> [<DonorProjectDir>]}"
LIB="${2:?missing <BlueprintLib>}"
DONOR="${3:-LeanModularForms}"
SB="$ROOT/projects/$PROJ/_blueprint"
PATCH="$ROOT/scripts/patches/verso-blueprint-v4.30-on-v4.31-toolchain.patch"

test -f "$SB/lakefile.toml"      || { echo "no side-build at $SB"; exit 1; }
test -f "$SB/lake-manifest.json" || { echo "no lake-manifest.json at $SB"; exit 1; }
test -d "$ROOT/.lake/packages/mathlib/.lake/build/lib" \
  || { echo "this checkout's mathlib is not built — run 'lake exe cache get' + build AINTLIB first"; exit 1; }

# HARD GUARD: the manifest MUST keep mathlib as the local path. If it ever became a git require,
# building would clone ~7 GB and fill the disk. Refuse rather than risk it.
if ! grep -q '"dir": "../../../.lake/packages/mathlib"' "$SB/lake-manifest.json"; then
  echo "REFUSING: $SB/lake-manifest.json does not pin mathlib to ../../../.lake/packages/mathlib"
  echo "         (a 'lake update' likely turned it back into a git clone — restore the path form first)."
  exit 1
fi

# Provision the Verso packages by hardlink from a sibling side-build (near-zero disk). NEVER clone.
if [ ! -d "$SB/.lake/packages/VersoBlueprint" ]; then
  echo "provisioning $PROJ/_blueprint/.lake/packages from $DONOR (cp -al, hardlinked)…"
  mkdir -p "$SB/.lake/packages"
  cp -al "$ROOT/projects/$DONOR/_blueprint/.lake/packages/." "$SB/.lake/packages/"
fi

# Patch VersoBlueprint v4.30 to compile on the v4.31 toolchain (idempotent).
hr="$SB/.lake/packages/VersoBlueprint/src/VersoBlueprint/Lib/HoverRender.lean"
if [ -f "$hr" ] && grep -q 'simpa using this' "$hr"; then
  ( cd "$SB/.lake/packages/VersoBlueprint" && git apply "$PATCH" )
  echo "applied VersoBlueprint v4.30-on-v4.31 patch"
fi

cd "$SB"
echo "==> lake build $LIB   (no update; mathlib via path)"
lake build "$LIB"
echo "==> render"
lake env lean --run "../${LIB}Main.lean" --output _out/site
echo "rendered: $SB/_out/site/html-multi  ($(find _out/site/html-multi -name index.html | wc -l) pages)"
