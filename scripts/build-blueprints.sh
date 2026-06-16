#!/usr/bin/env bash
#
# Build every project's Verso blueprint and assemble ONE multi-blueprint static site.
#
#   output:  _site/<subdir>/   (one self-contained blueprint each)  +  _site/index.html
#
# GitHub Pages serves one site per repo, but it serves a whole directory tree — so each
# blueprint is just a SUBDIRECTORY. The rendered sites use relative links, so each drops
# under $PAGES_BASE/<subdir>/ with no base-path tweaking. The assembled _site/ is pushed to
# the dedicated Pages repo (the heavy Verso build never touches AINTLIB's build / daily bump).
#
# Each blueprint is a self-contained side-build at  projects/<P>/_blueprint/  (its own lakefile:
# path-requires the AINTLIB workspace + patched VersoBlueprint, mathlib last). We build each in
# a throwaway worktree of its dev branch so branches never interfere.
#
# NOTE: until AINTLIB publishes an olean cache, each side-build compiles the AINTLIB libs it needs
# from source (via the path-require) — slow. The cache makes this fast; CI also caches .lake/packages.
#
# LOCAL builds: this script's `lake update` re-resolves mathlib and (on a near-full disk) tries to
# clone ~7 GB and fails. To render a single blueprint locally against THIS already-built checkout
# without any clone, use  scripts/render-blueprint-local.sh <ProjectDir> <BlueprintLib>  instead
# (mathlib via path, verso packages hardlinked). That is the path actually used to publish the
# four live blueprints; build-blueprints.sh is the CI-on-a-fresh-runner path.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/_site"; rm -rf "$OUT"; mkdir -p "$OUT"
PATCH="$ROOT/scripts/patches/verso-blueprint-v4.30-on-v4.31-toolchain.patch"

# project | dev branch | side-build dir (rel to repo) | blueprint lib | render Main module | subdir
# (add a row as each project's blueprint side-build lands on its dev branch — see projects/PadicLFunctions/_blueprint)
BLUEPRINTS=(
  "padic|dev/padic|projects/PadicLFunctions/_blueprint|PadicLFunctionsBlueprint|PadicLFunctionsBlueprintMain|padic"
  "leanmodularforms|dev/leanmodularforms|projects/LeanModularForms/_blueprint|LeanModularFormsBlueprint|LeanModularFormsBlueprintMain|leanmodularforms"
  # chebotarev + flt-bernoulli are migrated, built green, and LIVE, but their sources currently sit on
  # dev/leanmodularforms (the build host) rather than their own dev branches — so their worktree rows are
  # commented until the per-project branches exist (each row needs a distinct branch to worktree). Render
  # them locally with: scripts/render-blueprint-local.sh Chebotarev CebotarevDensityBlueprint
  #                    scripts/render-blueprint-local.sh FltRegularBernoulli BernoulliRegularBlueprint
  # "chebotarev|dev/chebotarev|projects/Chebotarev/_blueprint|CebotarevDensityBlueprint|CebotarevDensityBlueprintMain|chebotarev"
  # "flt-bernoulli|dev/flt-bernoulli|projects/FltRegularBernoulli/_blueprint|BernoulliRegularBlueprint|BernoulliRegularBlueprintMain|flt-bernoulli"
)

build_one() {
  local proj="$1" branch="$2" bpdir="$3" lib="$4" main="$5" sub="$6"
  echo "==> blueprint: $proj  ($branch)"
  local wt="$ROOT/.bp-$proj"
  git -C "$ROOT" worktree add -f "$wt" "$branch" >/dev/null
  (
    cd "$wt/$bpdir"
    lake update
    # Patch VersoBlueprint v4.30 to compile on the v4.31 toolchain (idempotent).
    hr=".lake/packages/VersoBlueprint/src/VersoBlueprint/Lib/HoverRender.lean"
    if [ -f "$hr" ] && grep -q 'simpa using this' "$hr"; then
      ( cd .lake/packages/VersoBlueprint && git apply "$PATCH" )
    fi
    lake exe cache get || true                 # mathlib oleans
    lake build "$lib"                          # verifies the blueprint's (lean := …) refs resolve
    lake env lean --run "../$main.lean" --output _out/site   # render html-multi
    rm -rf "$OUT/$sub"; cp -R _out/site/html-multi "$OUT/$sub"
  )
  git -C "$ROOT" worktree remove -f "$wt" || true
}

for entry in "${BLUEPRINTS[@]}"; do
  IFS='|' read -r p b d l m s <<< "$entry"
  build_one "$p" "$b" "$d" "$l" "$m" "$s"
done

# landing page linking each blueprint
{
  echo '<!doctype html><meta charset=utf-8><title>AINTLIB blueprints</title>'
  echo '<h1>AINTLIB blueprints</h1><ul>'
  for entry in "${BLUEPRINTS[@]}"; do IFS='|' read -r p b d l m s <<< "$entry"; echo "  <li><a href=\"./$s/\">$p</a></li>"; done
  echo '</ul>'
} > "$OUT/index.html"

echo "assembled $OUT  (blueprints: $(ls -1 "$OUT" | grep -v '^index.html$' | tr '\n' ' '))"
