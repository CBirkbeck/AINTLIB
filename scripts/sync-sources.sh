#!/usr/bin/env bash
set -uo pipefail
GH="/Users/mcu22seu/Documents/GitHub"
OUT="$GH/AINTLIB/sources/_scan.tsv"
mkdir -p "$GH/AINTLIB/sources"
printf 'repo\tlean\tcommit\tremote\tblueprint_dir\n' > "$OUT"

REPOS=( "Adic spaces" chebotarev-density flt-regular-bernoulli LeanModularForms \
  LeanModularForms-hecke FLT flt-regular Hasse-Weil WeilConjectures EulerProducts \
  DirichletNonvanishing LocalClassFieldTheory "Nagel--Lutz" NewtonPolys \
  power_reside_symbols GLn_F_q ModFormDims )

for r in "${REPOS[@]}"; do
  d="$GH/$r"
  if [ ! -d "$d/.git" ]; then echo "skip: $r (no git)"; continue; fi
  git -C "$d" fetch --quiet origin 2>/dev/null
  if ! git -C "$d" pull --ff-only --quiet 2>/dev/null; then
    echo "WARN: $r not fast-forwardable — left as-is (local changes?)"
  fi
  lean=$(cat "$d/lean-toolchain" 2>/dev/null | tr -d '\n')
  commit=$(git -C "$d" rev-parse --short HEAD 2>/dev/null)
  remote=$(git -C "$d" remote get-url origin 2>/dev/null)
  bp=""
  for b in blueprint Blueprint docs/blueprint; do
    [ -d "$d/$b" ] && bp="$b" && break
  done
  printf '%s\t%s\t%s\t%s\t%s\n' "$r" "$lean" "$commit" "$remote" "$bp" >> "$OUT"
done

echo "--- scan ---"
column -t -s $'\t' "$OUT"
