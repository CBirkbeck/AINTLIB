#!/bin/bash
# CHARTER-GH (GH4): THE HEADLINE receipt fire — one command.
# Usage: bash projects/ModularCurves/.mathlib-quality/scripts/capstone-receipts.sh
# Prints #print-axioms receipts for the seven headliners + the residual-sorry census of the cone.
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
lake env lean "$TMP" 2>&1
echo "== CONE RESIDUALS (sorry lines) =="
grep -c "sorry" projects/ModularCurves/ModularCurves/EllipticCurve/EndomorphismDegree.lean | sed 's/^/EndomorphismDegree: /'
grep -c "sorry" projects/ModularCurves/ModularCurves/Moduli/Bootstrap.lean | sed 's/^/Bootstrap: /'
grep -c "sorry" projects/ModularCurves/ModularCurves/Moduli/EllCategory.lean | sed 's/^/EllCategory: /'
grep -c "sorry" projects/ModularCurves/ModularCurves/Moduli/QuotientProblem.lean | sed 's/^/QuotientProblem: /'
rm -f "$TMP"
