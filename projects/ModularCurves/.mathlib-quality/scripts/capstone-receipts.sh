#!/bin/bash
# CHARTER-GH (GH4) / CHARTER-FIN (F4): THE HEADLINE receipt fire — one command, machine-judged.
# Usage: bash projects/ModularCurves/.mathlib-quality/scripts/capstone-receipts.sh
# v2 (v10.329): per-receipt PASS/FAIL verdicts + hard exit code.
#   PASS  = axiom set exactly ⊆ {propext, Classical.choice, Quot.sound}
#   FAIL  = sorryAx / any other axiom / receipt missing
# Exit 0 ⟺ all seven receipts PASS ⟺ THE HEADLINE.
set -e
cd "$(git rev-parse --show-toplevel)"
TMP=$(mktemp /tmp/capstone_receipts_XXXX.lean)
cat > "$TMP" <<'LEAN'
import ModularCurves.Moduli.GammaHClosure
open ModularCurves
#print axioms ModularCurves.gammaFullNaive_rigid_and_representable
#print axioms ModularCurves.gammaFullDrinfeld_rigid_and_representable
#print axioms ModularCurves.gammaOneDrinfeld_rigid_and_representable_of_hbound
#print axioms ModularCurves.gammaBot_representable
#print axioms ModularCurves.gammaH_representable_of_orderOf
#print axioms ModularCurves.gammaOneDrinfeld_representable_prep
#print axioms ModularCurves.levelSpaceΓπ_etale
LEAN
echo "== THE HEADLINE RECEIPTS =="
OUT=$(lake env lean "$TMP" 2>&1) || { echo "$OUT"; echo "ELABORATION FAILED"; rm -f "$TMP"; exit 2; }
echo "$OUT"
rm -f "$TMP"

echo "== CONE RESIDUALS (sorry-token lines per file) =="
for f in \
  projects/ModularCurves/ModularCurves/EllipticCurve/EndomorphismDegree.lean \
  projects/ModularCurves/ModularCurves/Moduli/Bootstrap.lean \
  projects/ModularCurves/ModularCurves/Moduli/EllCategory.lean \
  projects/ModularCurves/ModularCurves/Moduli/QuotientProblem.lean \
  projects/ModularCurves/ModularCurves/Moduli/EngineMouth.lean \
  projects/ModularCurves/ModularCurves/Moduli/EngineDescent.lean \
  projects/ModularCurves/ModularCurves/Moduli/LevelThreeTorsor.lean \
  projects/ModularCurves/ModularCurves/Moduli/SqrtCoverGlue.lean \
  projects/ModularCurves/ModularCurves/Moduli/Recollement.lean \
  projects/ModularCurves/ModularCurves/LevelStructure/ExactOrder.lean \
  projects/ModularCurves/ModularCurves/Moduli/GammaHMaster.lean \
  projects/ModularCurves/ModularCurves/Moduli/GammaHClosure.lean ; do
  [ -f "$f" ] && printf "%s: %s\n" "$(basename "$f" .lean)" "$(grep -c "sorry" "$f")"
done

echo "== VERDICTS =="
NORM=$(echo "$OUT" | tr '\n' ' ')
FAILED=0
for name in \
  gammaFullNaive_rigid_and_representable \
  gammaFullDrinfeld_rigid_and_representable \
  gammaOneDrinfeld_rigid_and_representable_of_hbound \
  gammaBot_representable \
  gammaH_representable_of_orderOf \
  gammaOneDrinfeld_representable_prep \
  levelSpaceΓπ_etale ; do
  SEG=$(echo "$NORM" | sed -n "s/.*'ModularCurves\.$name' depends on axioms: \[\([^]]*\)\].*/\1/p")
  if [ -z "$SEG" ]; then
    echo "FAIL  $name  (receipt missing from output)"
    FAILED=1
  else
    EXTRA=$(echo "$SEG" | tr ',' '\n' | sed 's/^ *//;s/ *$//' | grep -v '^$' \
      | grep -v -x 'propext' | grep -v -x 'Classical\.choice' | grep -v -x 'Quot\.sound' || true)
    if [ -z "$EXTRA" ]; then
      echo "PASS  $name"
    else
      echo "FAIL  $name  (extra axioms: $(echo "$EXTRA" | tr '\n' ' '))"
      FAILED=1
    fi
  fi
done

echo "== RESULT =="
if [ "$FAILED" -eq 0 ]; then
  echo "★★★ THE HEADLINE: all seven receipts are {propext, Classical.choice, Quot.sound}-clean ★★★"
  exit 0
else
  echo "headline not yet: at least one receipt failed (see VERDICTS)"
  exit 1
fi
