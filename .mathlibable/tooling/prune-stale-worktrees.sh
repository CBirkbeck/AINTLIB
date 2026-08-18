#!/usr/bin/env bash
# Prune stale per-ticket fleet worktrees — the `aintlib-<lane>-<n>` storage leak.
#
# Workers create a worktree per ticket (each ~10G of .lake) and don't always remove it
# (esp. on crash / session-limit / bail). This removes a per-ticket worktree IFF its ticket
# is CLOSED (work merged → the worktree is pure leftover). Active (open-ticket) worktrees,
# the stable lane worktrees (aintlib-cleanup/-decompose/-generalise, no trailing -<n>),
# the dev worktrees, and aintlib-main are NEVER touched.
#
# Run periodically (cron). Safe to run during a freeze for lane worktrees; skips the
# generalise-reviewer's integrate-* worktrees while any freeze is active (it may be mid-merge).
set -uo pipefail
GH=/opt/homebrew/bin/gh; R=CBirkbeck/AINTLIB
cd /Users/mcu22seu/Documents/GitHub/aintlib-main || exit 1

FREEZE_OPEN=$($GH issue list --repo "$R" --label freeze:active --state open --json number --jq 'length' 2>/dev/null || echo 1)
removed=0; kept=0

# iterate registered worktree paths
for p in $(git worktree list --porcelain 2>/dev/null | awk '/^worktree /{print $2}'); do
  b=$(basename "$p")
  if [[ "$b" =~ ^aintlib-(cleanup|generalise|decompose)-([0-9]+)$ ]]; then
    n="${BASH_REMATCH[2]}"
    state=$("$GH" issue view "$n" --repo "$R" --json state --jq .state 2>/dev/null || echo "")
    if [ "$state" = "CLOSED" ]; then
      # ticket done + merged → the worktree is disposable leftover; --force ignores its .lake/untracked build
      if LEAN4_GUARDRAILS_BYPASS=1 git worktree remove --force "$p" 2>/dev/null; then
        echo "removed $b (ticket #$n CLOSED)"; removed=$((removed+1))
      fi
    else
      kept=$((kept+1))  # open/unknown ticket → active, keep
    fi
  elif [[ "$b" =~ ^aintlib-integrate-generalise- ]]; then
    if [ "$FREEZE_OPEN" = "0" ]; then
      if LEAN4_GUARDRAILS_BYPASS=1 git worktree remove --force "$p" 2>/dev/null; then
        echo "removed $b (integrate batch, no active freeze)"; removed=$((removed+1))
      fi
    else
      kept=$((kept+1))  # freeze active → reviewer may be mid-merge, keep
    fi
  fi
done

git worktree prune 2>/dev/null
echo "prune-stale-worktrees: removed=$removed kept(active)=$kept"
