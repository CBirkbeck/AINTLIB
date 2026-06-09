#!/usr/bin/env bash
set -uo pipefail
OUT="/Users/mcu22seu/Documents/GitHub/AINTLIB/sources/discovery.tsv"
printf 'stars\tfullName\tdescription\n' > "$OUT"
q () { gh search repos "$1" --language Lean --limit 50 \
        --json fullName,description,stargazersCount 2>/dev/null \
      | jq -r '.[] | "\(.stargazersCount)\t\(.fullName)\t\(.description // "")"'; }
{ q "number theory"; q "blueprint"; q "modular forms"; q "elliptic curves"; \
  q "class field theory"; q "p-adic"; q "L-function"; q "cyclotomic"; q "primes"; \
  q "diophantine"; } | sort -u | sort -rn >> "$OUT"
echo "--- top discoveries ---"; head -50 "$OUT" | column -t -s $'\t'
