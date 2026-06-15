#!/usr/bin/env bash

set -euo pipefail

# verso-blueprint v4.30.0 needs a one-line proof fix to compile under the
# project toolchain (v4.31.0-rc1); apply the checked-in patch idempotently.
# Drop this once verso-blueprint publishes a v4.31 branch.
if grep -q 'simpa using this' .lake/packages/VersoBlueprint/src/VersoBlueprint/Lib/HoverRender.lean 2>/dev/null; then
  (cd .lake/packages/VersoBlueprint && git apply "$OLDPWD"/scripts/patches/verso-blueprint-v4.30-on-v4.31-toolchain.patch)
fi

lake build PadicLFunctionsBlueprint
lake env lean --run PadicLFunctionsBlueprintMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
