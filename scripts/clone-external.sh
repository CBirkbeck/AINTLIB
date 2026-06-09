#!/usr/bin/env bash
set -uo pipefail
cd /Users/mcu22seu/Documents/GitHub
clone () { # owner/repo  target-dir
  if [ -d "$2" ]; then echo "exists: $2 (fetching)"; git -C "$2" fetch --quiet origin 2>/dev/null
  else echo "cloning: $1 -> $2"; gh repo clone "$1" "$2" -- --depth 1; fi
}
clone AlexKontorovich/PrimeNumberTheoremAnd PrimeNumberTheoremAnd
clone ImperialCollegeLondon/FLT FLT-imperial
clone pitmonticone/QuadraticIntegers QuadraticIntegers
clone amellendijk/lean-bombieri-vinogradov lean-bombieri-vinogradov
