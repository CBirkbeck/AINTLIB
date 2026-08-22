#!/usr/bin/env bash
# Kernel-level certification of the paper's headline theorems via leanprover/comparator:
# statement-identity against `Adic spaces/Comparator/Challenge.lean`, axiom budget
# [propext, Quot.sound, Classical.choice], and kernel acceptance.
#
# Prerequisites (one-time):
#   git clone https://github.com/leanprover/comparator ~/.cache/lean-certify/comparator
#   cd ~/.cache/lean-certify/comparator
#   # PIN IT: comparator's HEAD tracks the newest toolchain, but the judging kernel must
#   # match the judged development. This project is v4.33.0, so check out the last commit
#   # on that line (c0c5a52 as of 2026-08-22) before building.
#   git switch --detach c0c5a52 && lake build
#   # the lean4export artifact lake fetches is a Linux ELF; build it natively instead:
#   git clone https://github.com/leanprover/lean4export ~/.cache/lean-certify/lean4export
#   cd ~/.cache/lean-certify/lean4export && git switch --detach \
#     $(python3 -c "import json;print([p['rev'] for p in \
#       json.load(open('$HOME/.cache/lean-certify/comparator/lake-manifest.json'))['packages'] \
#       if p['name']=='lean4export'][0])") && lake build
#
# On Linux, install the real landrun (github.com/Zouuup/landrun) for sandboxing.
# On macOS, comparator's own scripts/fake-landrun.sh shim is used (no sandbox — acceptable
# here: the "solution" is this repository's own code, not an adversarial submission).
#
# Run from the REPO ROOT (the lake workspace), not from projects/AdicSpaces.
#
# CONFIG selects which certificate to run; the challenge/solution modules are read from it:
#   default  — Adic spaces/Comparator/comparator-config.json   ([FJP] Theorem 1.1 = thm:main)
#   also     — Adic spaces/Comparator/wp-config.json           ([WP] Theorem 8.1, the
#              weighted-parity example)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
CONFIG="${CONFIG:-projects/AdicSpaces/Adic spaces/Comparator/comparator-config.json}"

# Persistent by default. These lived in /tmp until 2026-08-22, when a cleared /tmp
# silently broke reproduction: both Lean builds passed and only the kernel replay failed.
# Override with COMPARATOR_DIR / COMPARATOR_LEAN4EXPORT if you keep them elsewhere.
CERTIFY_CACHE="${CERTIFY_CACHE:-$HOME/.cache/lean-certify}"
COMPARATOR_DIR="${COMPARATOR_DIR:-$CERTIFY_CACHE/comparator}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$CERTIFY_CACHE/lean4export/.lake/build/bin/lean4export}"
if ! command -v landrun >/dev/null 2>&1; then
  export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$COMPARATOR_DIR/scripts/fake-landrun.sh}"
fi

cd "$REPO_ROOT"

# Both modules are deliberately outside defaultTargets (the challenge is full of `sorry`), so
# they must be built by name. Build the challenge FIRST: comparator's guarantee assumes the
# challenge's oleans were not produced by a run that had already seen the solution.
#
# Comparator itself re-runs `lake build` on each module inside landrun (`safeLakeBuild`), which
# is why `Solution.lean` is a small forwarding file rather than a library module: only the
# untrusted submission belongs in the sandboxed build, not the whole project.
CHALLENGE_MOD="$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['challenge_module'])" "$CONFIG")"
SOLUTION_MOD="$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['solution_module'])" "$CONFIG")"
lake build "$CHALLENGE_MOD"
lake build "$SOLUTION_MOD"

exec lake env "$COMPARATOR_DIR/.lake/build/bin/comparator" "$CONFIG"
