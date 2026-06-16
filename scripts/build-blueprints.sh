#!/usr/bin/env bash
#
# Build every project's Verso blueprint and assemble ONE multi-blueprint static site.
#
#   output:  _site/<subdir>/   (one self-contained blueprint each)  +  _site/index.html
#
# GitHub Pages serves one site per repo, but it serves a whole directory tree — so each
# blueprint is just a SUBDIRECTORY. Each must be built with base path  $PAGES_BASE/<subdir>/
# so its internal links/assets resolve under the subdir. The assembled _site/ is then pushed
# to the dedicated Pages repo (the heavy Verso build never touches AINTLIB's build / daily bump).
#
# Blueprint source lives on each dev/<project> branch under projects/<P>/; we build each in its
# own throwaway git worktree so branches never interfere.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PAGES_BASE="${PAGES_BASE:-/AINTLIB-blueprints}"     # project-site base of the Pages repo
OUT="$ROOT/_site"; rm -rf "$OUT"; mkdir -p "$OUT"
PATCH="$ROOT/scripts/patches/verso-blueprint-v4.30-on-v4.31-toolchain.patch"

# project | dev branch | project dir | blueprint lib | render exe | subdir
# (uncomment / add a row as each project's blueprint is wired onto its dev branch)
BLUEPRINTS=(
  "padic|dev/padic|projects/PadicLFunctions|PadicLFunctionsBlueprint|blueprint-gen|padic"
  # "leanmodularforms|dev/leanmodularforms|projects/LeanModularForms|<BlueprintLib>|blueprint-gen|leanmodularforms"
  # "chebotarev|dev/chebotarev|projects/Chebotarev|CebotarevBlueprint|blueprint-gen|chebotarev"
  # "flt-bernoulli|dev/flt-bernoulli|projects/FltRegularBernoulli|<BlueprintLib>|blueprint-gen|flt-bernoulli"
)

build_one() {
  local proj="$1" branch="$2" pdir="$3" lib="$4" exe="$5" sub="$6"
  echo "==> blueprint: $proj  ($branch)"
  local wt="$ROOT/.bp-$proj"
  git -C "$ROOT" worktree add -f "$wt" "$branch" >/dev/null
  (
    cd "$wt"
    lake exe cache get >/dev/null 2>&1 || true
    # Patch VersoBlueprint v4.30 so it builds on the v4.31 toolchain, then build + render.
    # patch -p1 -d .lake/packages/VersoBlueprint < "$PATCH" || true
    # lake build "$lib"
    # lake exe "$exe" --base "$PAGES_BASE/$sub/" --out _bpout      # render html-multi
    #
    # ---- until the per-project blueprint build above is wired, emit a placeholder so the
    #      assembly + publish path is exercisable end-to-end: ----
    mkdir -p _bpout/html-multi
    printf '<!doctype html><title>%s blueprint</title><h1>%s blueprint</h1><p>placeholder — wire the Verso render in scripts/build-blueprints.sh</p>\n' "$proj" "$proj" > _bpout/html-multi/index.html
    rm -rf "$OUT/$sub"; cp -R _bpout/html-multi "$OUT/$sub"
  )
  git -C "$ROOT" worktree remove -f "$wt" >/dev/null 2>&1 || true
}

for entry in "${BLUEPRINTS[@]}"; do
  IFS='|' read -r p b d l e s <<< "$entry"
  build_one "$p" "$b" "$d" "$l" "$e" "$s"
done

# landing page linking each blueprint
{
  echo '<!doctype html><meta charset=utf-8><title>AINTLIB blueprints</title>'
  echo '<h1>AINTLIB blueprints</h1><ul>'
  for entry in "${BLUEPRINTS[@]}"; do IFS='|' read -r p b d l e s <<< "$entry"; echo "  <li><a href=\"./$s/\">$p</a></li>"; done
  echo '</ul>'
} > "$OUT/index.html"

echo "assembled $OUT  (blueprints: $(ls -1 "$OUT" | grep -v '^index.html$' | tr '\n' ' '))"
