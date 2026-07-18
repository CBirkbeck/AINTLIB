# AINTLIB Worker System — Design

**Status:** draft for review · **Date:** 2026-06-16

## Goal

A 4-account Claude system that continuously improves the AINTLIB monorepo: **one coordinator**
(writes tickets, bumps mathlib, does cross-cutting renames) and **three cron-driven workers**
running `/cleanup`, `/generalise`, and `/decompose-proof`. Coordination is through **GitHub Issues +
a Projects board**, so it survives restarts and could later span machines.

## Roles

- **Coordinator** (1 account — the human's main Claude session): runs `/overview`, files issues,
  keeps the board fed, runs the daily **mathlib bump**, does **cross-cutting renames**, **reviews +
  merges the `/generalise` PRs** (the one statement-changing lane), and **monitors `main` and reverts
  bad merges** from the auto-merging lanes.
- **Workers** (3 accounts, one lane each): `/cleanup`, `/generalise`, `/decompose-proof`. Each
  drains its lane and loops on a cron.

## Merge gate — split on "does the lane change the statement?"

- **`/cleanup`** (golf/style) and **`/decompose-proof`** (extracts helper lemmas; the top-level
  theorem statement is unchanged) → **auto-merge on green**. The verification bar guarantees the
  same theorem still proves, so no human gate is needed.
- **`/generalise`** (weakens hypotheses / generalises types — i.e. *changes the statement*) →
  worker stops at **`state:review`** and opens a PR; the **coordinator reviews the statement change
  and merges**. A generalisation can be subtly wrong or weaker-than-useful in a way `lake build`
  cannot detect, so this lane keeps a human-in-the-loop.

## Substrate — GitHub Issues + Projects board

- **One issue per ticket**, scoped to one result (or a tight, single-file group).
- **Lane labels:** `lane:cleanup`, `lane:generalise`, `lane:decompose` — which worker picks it up.
- **State labels:** `state:todo` → `state:in-progress` → closed (= done). The `/generalise` lane adds
  a `state:review` step before closing; `/cleanup` and `/decompose-proof` skip it (auto-merge).
- **Freeze signal:** a pinned issue labelled `freeze:active`. Its existence means "hold."
- A **Projects board** with columns Todo / In-progress / Done mirrors the state labels — the live view.
- **Issue body template:** target declaration(s) (qualified Lean names + file:line), the requested
  action, the acceptance bar, and a link back to the `/overview` finding that generated it.

## Ticket lifecycle

1. **Claim (atomic).** Worker queries `gh issue list --label lane:<mine> --label state:todo` filtered
   to unassigned, picks the top, and `gh issue edit --add-assignee @me`. GitHub assignment is atomic,
   so if two fire together only one wins; the loser re-queries. It swaps `state:todo`→`state:in-progress`
   and comments "claimed by <account> @ <ts>".
2. **Check freeze.** If any `freeze:active` issue is open, do **not** claim; idle until it clears.
3. **Work on a branch.** Cut `<lane>/<issue#>` off the latest `origin/main` in the worker's worktree;
   run the lane skill on the target.
4. **Verify locally (the green bar).** `lake build <lib>` green, **zero new `sorry`**, and
   `#print axioms` shows only `propext` / `Classical.choice` / `Quot.sound` (no regression vs. before).
   CI is deliberately **not** in the loop — a full mathlib-monorepo build per PR is too heavy;
   verification is local and incremental in the worker's worktree.
5. **Merge.** Re-check freeze. `git fetch origin main`; if `main` moved, rebase the small branch and
   re-verify. Push the branch and open a PR (audit trail + board link). Then:
   - **`/cleanup`, `/decompose-proof`** (statement-preserving): `gh pr merge --squash --delete-branch`
     and close the issue.
   - **`/generalise`** (statement-changing): set `state:review` and stop — the coordinator reviews the
     statement change and merges. Do **not** self-merge.
6. **Loop.** Take the next `state:todo` in the lane until the lane is empty or a freeze is active, then
   exit. The cron re-fires.

## Concurrency model

- Workers touch **different results**, so worker-vs-worker conflict is near zero. Small tickets
  (one file) keep any rebase trivial.
- The real contention source is the coordinator's **cross-cutting operations** — the bump and renames,
  which touch many files. Those run under the **freeze**:
  1. Coordinator opens / labels the `freeze:active` issue.
  2. Workers finish and merge their **current** ticket, then idle — no new claims, no new merges.
  3. Coordinator does the bump / rename on `main` and pushes.
  4. Coordinator clears `freeze:active`. Workers fetch, rebase any branch they were holding, and resume.
- Net: parallel essentially all the time; a few minutes of soft pause per bump / rename. No worker is
  ever killed, and a missed freeze costs only a rebase — never lost work.

## Coordinator loop

- **Keep the board fed:** `/overview` → file issues per lane, small (one result each).
- **Daily bump:** freeze → bump mathlib pin + `lean-toolchain`, `lake update`, `lake exe cache get`,
  mechanically repair the fallout to green → push `main` → unfreeze.
- **Renames as needed:** freeze → rename + fix every consumer → push → unfreeze.
- **Review `/generalise`:** watch the `state:review` column; check each generalisation actually holds
  and is the intended/useful statement, then merge.
- **Watch `main`:** the auto-merging lanes (`/cleanup`, `/decompose-proof`) land without review.
  Periodically diff recent merges and **revert** anything that introduced a gap. This post-merge spot
  check is the safety net for the statement-preserving lanes.

## Worker loop (cron prompt, per lane)

Each worker account runs a cron firing every ~20–30 min (cadence is the human's call). The prompt is
the lifecycle above, parameterised by lane and skill. Each firing **drains its lane then exits**;
the next firing continues. (Exact prompt text is produced in the implementation plan.)

## Deployment

- All four accounts run on **one machine**, sharing a single clone via **git worktrees** — one worktree
  per worker, each on its own branch with its own `.lake`. Each worker account has `gh` authenticated
  with **write access to `CBirkbeck/AINTLIB`**.
- A branch can only be checked out in one worktree, so each lane uses its own branch namespace
  (`cleanup/*`, `generalise/*`, `decompose/*`) and they never collide. `main` stays on the coordinator's
  checkout; everyone fetches `origin/main`.

## Risks + mitigations

- **The statement-changing lane (`/generalise`) is gated** by coordinator review, so a bad
  generalisation can't reach `main` unseen. The statement-preserving lanes (`/cleanup`,
  `/decompose-proof`) auto-merge, relying on the verification bar (no new sorries, axioms unchanged,
  build green) + coordinator post-merge spot-check and revert. If even those prove too loose, any lane
  can be moved behind `state:review` by flipping one branch in the worker prompt.
- **Coordinator rename racing a worker merge:** prevented by the freeze.
- **Worker crash mid-ticket:** the issue stays `in-progress`, assigned. The coordinator runs a
  **stale-claim sweep** — issues `in-progress` with no linked commits after N hours are unassigned and
  returned to `todo`.

## Setup checklist (implementation)

1. Create the labels + the Projects board (coordinator, via `gh`).
2. Add the worker protocol to `CLAUDE.md` so every session follows it.
3. Write the three worker cron prompts; the human installs one per worker account.
4. Run `/overview`; file the first batch of issues across the three lanes.
5. Smoke-test one ticket end-to-end per lane before turning the crons loose.
