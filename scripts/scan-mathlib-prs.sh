#!/usr/bin/env bash
set -uo pipefail
OUT="/Users/mcu22seu/Documents/GitHub/AINTLIB/sources/mathlib-nt-prs.json"
gh pr list --repo leanprover-community/mathlib4 \
  --label t-number-theory --state open --limit 200 \
  --json number,title,url,updatedAt,labels > "$OUT"
echo "open t-number-theory PRs: $(jq length "$OUT")"
jq -r '.[] | "#\(.number)\t\(.title)"' "$OUT" | head -60
