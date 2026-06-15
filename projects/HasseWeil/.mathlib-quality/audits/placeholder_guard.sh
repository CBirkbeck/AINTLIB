#!/usr/bin/env bash
# placeholder_guard.sh — mechanical guard against "rotten placeholder" isogenies.
#
# WHY THIS EXISTS
# ---------------
# `HasseWeil.Isogeny` stores `pullback` and `toAddMonoidHom` as INDEPENDENT
# fields with no enforced compatibility. A "rotten placeholder" pairs a CORRECT
# point-map with a DELIBERATELY-WRONG pullback (`pullback := AlgHom.id`, or
# `pullback := <other>.pullback`). Because `Isogeny.degree` is read off the
# pullback, a placeholder silently yields a wrong degree (often 1), letting
# FALSE theorems type-check (`pointCount = 1`, `q² ≤ 4q`). This cost the project
# a long detour (see placeholder-audit-2026-05-28.md).
#
# This guard gates the things grep CAN decide cleanly:
#   CHECK 1  new rotten DEFINITION  (`pullback := AlgHom.id` in real code)
#   CHECK 3  vacuous `: True := …` theorem with a substantive name
#   CHECK 4  custom `axiom`
# It then PRINTS (informational, non-gating) the placeholder-into-consumer
# flows for manual review, because witness-parametric *hypotheses* mentioning a
# placeholder degree are legitimate and cannot be separated from unsafe
# *proofs* by grep alone (the reviewer's "graph-based, not grep-based" point).
#
# Run:  bash .mathlib-quality/audits/placeholder_guard.sh
# Exit: 0 = no NEW gated regression; 1 = a new rotten def / vacuous thm / axiom.

set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2
SRC=HasseWeil
violations=0
note() { printf '  %s\n' "$1"; }
hdr()  { printf '\n=== %s ===\n' "$1"; }

# Strip lines where the match is inside a comment/docstring. Real Lean code for
# `pullback := AlgHom.id F …` never contains a backtick; doc mentions always do.
strip_docs() { grep -v '`' | grep -vE ':[0-9]+:[[:space:]]*--'; }

# ---------------------------------------------------------------------------
hdr "CHECK 1 (GATED): new rotten definition — pullback := AlgHom.id in code"
# Allowlist GENUINE identity constructions (id pullback paired with id point map):
#   HasseWeil/Basic.lean             Isogeny.id  +  mulByInt n=0 branch (known, guarded)
#   HasseWeil/Curves/CurveMap.lean   CurveMap.id (no point-map field at all)
# Known-rotten baseline (Strategy-B will delete these — they are NOT new):
#   HasseWeil/Endomorphism.lean      isogOneSub, isogSmulSub
while IFS= read -r line; do
  file="${line%%:*}"
  case "$file" in
    HasseWeil/Basic.lean|HasseWeil/Curves/CurveMap.lean) ;;          # genuine / guarded
    HasseWeil/Endomorphism.lean) note "KNOWN-ROTTEN (Strategy-B target): $line" ;;
    *) note "NEW VIOLATION: $line"; violations=$((violations + 1)) ;;
  esac
done < <(grep -rn "pullback := AlgHom.id" "$SRC" 2>/dev/null | strip_docs)

# Also catch the dual-style lie `pullback := <x>.pullback` inside a *def* that is
# NOT a genuine comp/base-change. `dualOfPicZeroPullback` was de-placeholdered
# on 2026-05-28 (now takes a genuine `dual_pullback` witness), so NO file is
# allowlisted here anymore — any `pullback := <x>.pullback` outside comp/
# base-change is a NEW violation (including a regression in IsogenyBaseChange).
while IFS= read -r line; do
  note "NEW VIOLATION (dual-style pullback lie): $line"; violations=$((violations + 1))
done < <(grep -rn "pullback := .*\.pullback\b" "$SRC" 2>/dev/null | strip_docs \
          | grep -v "comp\|mkBaseChange")

# Also catch `AlgHom.id` hidden in an if/match branch (`then/else/=> AlgHom.id`),
# which the literal `pullback := AlgHom.id` grep misses. The ONLY genuine
# (mathematically unavoidable) instance is `mulByInt`'s n=0 junk default: the
# zero map [0] is not an isogeny, so `Isogeny W W` cannot represent it — see the
# `n = 0` note in Basic.lean. Anything else is a rotten branch hiding a fake.
while IFS= read -r line; do
  file="${line%%:*}"
  case "$file" in
    HasseWeil/Basic.lean) ;;   # mulByInt n=0 junk default (documented, guarded)
    *) note "NEW VIOLATION (branch-hidden AlgHom.id): $line"; violations=$((violations + 1)) ;;
  esac
done < <(grep -rnE "(then|else|=>)[[:space:]]+AlgHom\.id\b" "$SRC" 2>/dev/null | strip_docs)

# ---------------------------------------------------------------------------
hdr "CHECK 3 (GATED): vacuous 'True := …' proof bodies"
# The theorem name + ': True :=' may span lines, so match the BODY directly:
# any code line `…True := trivial|True.intro|by trivial`, excluding proof-internal
# `have/let/suffices/show … : True := …` (those are harmless local steps).
while IFS= read -r line; do
  echo "$line" | grep -qE ':[0-9]+:[[:space:]]*(have|let|suffices|show)[[:space:]]' && continue
  note "VACUOUS: $line"; violations=$((violations + 1))
done < <(grep -rnE "True[[:space:]]*:=[[:space:]]*(trivial|True.intro|by[[:space:]]+trivial)" "$SRC" 2>/dev/null | strip_docs)

# ---------------------------------------------------------------------------
hdr "CHECK 4 (GATED): custom axiom declarations"
# Real axiom decl is `axiom <Ident> : …`; exclude prose ("axiom is …") + docs.
while IFS= read -r line; do
  note "AXIOM: $line"; violations=$((violations + 1))
done < <(grep -rnE "^[[:space:]]*axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_.]*[[:space:]]*[:({]" "$SRC" 2>/dev/null | strip_docs)

# ---------------------------------------------------------------------------
hdr "INFO (non-gating): placeholder names flowing into pullback/degree consumers"
echo "  (witness-parametric *hypotheses* are SAFE; only *proofs* of these are not."
echo "   Review each against placeholder-audit-2026-05-28.md.)"
PH='isogOneSub|isogSmulSub|oneSubFrobeniusIsog|dualOfPicZeroPullback|dualViaPicZero'
CONS='\.degree|\.sepDegree|\.pullback|\.toAlgebra|\.fieldRange|isogTrace|traceOfFrobenius'
n_info=$(grep -rnE "($PH)[^_a-zA-Z].*($CONS)" "$SRC" 2>/dev/null \
          | grep -vE 'isogOneSub_negFrobenius|isogOneSub_mulByInt|isogSmulSub_mulByInt' \
          | strip_docs | wc -l | tr -d ' ')
echo "  $n_info code site(s) reference a placeholder projection (see audit doc for the bucket classification)."

# ---------------------------------------------------------------------------
hdr "RESULT"
if [ "$violations" -eq 0 ]; then
  echo "PASS — no NEW rotten definitions / vacuous theorems / axioms."
  echo "(Known Strategy-B baseline items are listed above but not counted as new.)"
  exit 0
else
  echo "FAIL — $violations new gated item(s). A rotten placeholder, vacuous theorem,"
  echo "or custom axiom was introduced. Fix before merge."
  exit 1
fi
