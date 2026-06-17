# AINTLIB — rules for AI sessions

**AINTLIB is an AI-reviewed number-theory library** — built like mathlib, but maintained by AI
agents and tolerant of work-in-progress. It is **one Lake workspace** with every NT project side
by side under `projects/<P>/`, all on a **single mathlib that is bumped to latest daily**. Because
it is one build unit, any result can `import` any other — that is the entire point.

Work happens **across machines, through GitHub** (`CBirkbeck/AINTLIB`). Identify your role below and
follow that section.

## Structure
- **`main`** — the integrated library. Always builds. Bumped to latest mathlib **daily and
  centrally**. `sorry` is allowed here as an explicit work-in-progress marker.
- **`dev/<project>` branches** — each project's frontier, where new theorems are proved. Each
  carries its own dev ticket system.
- **Two ticket systems.** *Dev tickets* (per project, on its `dev/<project>` branch) track new
  math. *Cleanup tickets* (on `main`) are **GitHub issues labelled by lane** (see **Worker system**
  below) and track dedup / golf / style / cross-linking / generalisation /
  proof-decomposition. The handoff between them is **merging a dev branch into `main`**.

## Your working copy — all workers share ONE clone on this machine
Do **not** clone AINTLIB per worker. Use a **git worktree** per dev branch, so every worker runs in
parallel off the same `.git`:

    # once, from the main AINTLIB checkout (which stays on `main`):
    git worktree add ../aintlib-adic   dev/adic-spaces
    git worktree add ../aintlib-padic  dev/padic
    git worktree add ../aintlib-hasse  dev/hasse-weil

Each worker then lives in its own directory (`../aintlib-<proj>`) on its own branch — separate files
and a separate `.lake` build, fully isolated, no clobbering. In your worktree: `lake exe cache get`,
then build. Commit on your dev branch; PR to `main` when a ticket is done; `git rebase main` after
the daily bump (your worktree shares all of `main`'s refs locally — no fetch needed). Until AINTLIB
publishes its own olean cache, the *first* build in each worktree compiles the project tree from
source once (mathlib still comes from cache); after that it is incremental.

Workers on a *different* machine instead `git clone` AINTLIB and `git checkout dev/<project>` — all
the same rules apply from there.

## If you are a PRODUCER (proving new theorems)
You are on a `dev/<project>` branch, editing `projects/<YourProject>/`.
- **Prove theorems. That is the whole job.** Track the work in your project's dev tickets.
- **Reuse, don't duplicate.** Before proving anything nontrivial, search the whole repo and mathlib
  (`grep -r`, `import`, `exact?`/`apply?`); `import` existing results from *any* project. Re-proving
  something that already exists is the one cardinal sin here.
- **Leave `sorry`s** where you have not finished. They are fine.
- **Do NOT** clean, golf, restyle, deduplicate, or bump mathlib — all of that is done centrally on
  `main`. Spend your effort on math.
- **When a dev ticket is done**, open a PR from `dev/<project>` → `main`. That hands it to cleanup.
- **`main` is bumped daily.** Rebase your branch onto `main` when *you* reach a stable point — never
  mid-proof — so you absorb mathlib churn on your own schedule.

## If you are a CLEANER (the fleet, on `main`)
You are working an AINTLIB cleanup ticket.
- Deduplicate across projects, golf, apply mathlib style, generalise, decompose long proofs, cross-link
  consumers, and repair daily-bump fallout. **Leave `sorry`s alone** — they are the owning producer's WIP,
  never fleet work (only operate on sorry-free results).
- **Keep `main` green.** **Never** change a theorem/def statement to make something pass, and
  **never** add `sorry`/`admit`. If a `sorry` needs genuine new math, file a *dev* ticket to the
  owning project instead of forcing it.

## If you are the BUMP worker (daily, on `main`)
- Bump the mathlib pin in `lakefile.toml` + `lean-toolchain` to latest, `lake update`,
  `lake exe cache get`, then mechanically repair the fallout (renamed decls, signature skew) until
  green. No statement changes, no new sorries.
- Refresh and publish AINTLIB's olean cache so cross-machine clones build fast.

## Worker system — how the on-`main` fleet is coordinated

The cleanup fleet runs as **4 Claude accounts**: a **coordinator** + **3 lane workers**. Cleanup
tickets are **GitHub issues** on `CBirkbeck/AINTLIB`, labelled by lane + state. Full design:
`docs/superpowers/specs/2026-06-16-aintlib-worker-system-design.md`.

- **Coordinator** — files issues (from `/overview`), runs the daily **bump**, does cross-cutting
  **renames**, **reviews + merges the `/generalise` PRs**, and reverts bad auto-merges.
- **Lane workers** (one account each):
  - `lane:cleanup` → `/cleanup` (golf/style) — **auto-merges on green**
  - `lane:decompose` → `/decompose-proof` (extracts helpers; statement unchanged) — **auto-merges on green**
  - `lane:generalise` → `/generalise` (changes the statement) — **stops at `state:review`; coordinator merges**

**Worker loop — each cron firing:**
1. **Freeze check** — if any open issue has `freeze:active`, do nothing and exit.
2. **Claim (atomic)** — `gh issue list --label lane:<mine> --label state:todo`, pick an unassigned one,
   `gh issue edit <n> --add-assignee @me`, relabel `state:todo`→`state:in-progress`. (Assignment is atomic;
   if two workers race, only one wins — the other re-queries.)
3. **Work** — branch `<lane>/<issue#>` off the latest `origin/main` in your worktree; run your skill on the
   target. **Skip any target whose proof contains a `sorry`** (comment, return it to `state:todo`) — `sorry`s
   are the owning producer's WIP, never fleet work.
4. **Verify (the bar)** — `lake build` green, **zero new `sorry`**, `#print axioms` unchanged
   (only `propext` / `Classical.choice` / `Quot.sound`).
5. **Merge** — re-check freeze; `git fetch origin main`, rebase if it moved, re-verify; push + open a PR. Then:
   - `lane:cleanup` / `lane:decompose` → `gh pr merge --squash --delete-branch`, close the issue.
   - `lane:generalise` → relabel `state:review` and STOP — the coordinator reviews the statement change + merges.
6. **Loop** — take the next `state:todo` in your lane until it is empty or a freeze is active, then exit.

**Freeze rule (for the coordinator's bump + renames):** before a bump or a cross-cutting rename, open an
issue labelled `freeze:active`. Workers finish + merge their *current* ticket, then idle — no new claims or
merges. Do the op on `main`, push, then close the freeze issue; workers resume and rebase. A soft
drain-and-pause, never a kill; a missed freeze costs only a rebase.

**Branch namespaces:** `cleanup/*`, `generalise/*`, `decompose/*` — never shared, so worktrees never collide.

## Project context, tickets & reference material
Each project keeps its working context next to its code, under `projects/<P>/` on its
`dev/<project>` branch:
- **`.mathlib-quality/`** — the project's plan / ticket / expert-review system. **This is your dev
  ticket system** — keep using it exactly as before.
- **`docs/`, `blueprint/`, `scripts/`** — notes, the LaTeX blueprint, helper scripts.

All of it is non-`.lean` (no build impact) and stays on the **dev branches** — it is process, not the
cleaned library, so it is **not** merged into `main`.

**Reference PDFs and books are LOCAL ONLY — never committed, never pushed to GitHub.** They live in
`refs/<project>/` in the main checkout, which is gitignored (and `*.pdf` is ignored everywhere, so a
stray PDF can never be pushed). To read them from your worktree, symlink the shared store once:

    ln -s ../AINTLIB/refs refs

Then `refs/<project>/` is available to read and will never be committed.

## Build & conventions
- Toolchain in `lean-toolchain`; mathlib pinned in `lakefile.toml` (moves with the daily bump).
- `lake exe cache get` for mathlib oleans; build one target at a time (builds are incremental).
- Layout `projects/<P>/<Lib>/…`; genuinely-shared lemmas are refactored into `Common/`.
- Never put `2>/dev/null` next to a `lake`/`lean` command (a guardrail blocks it; use `2>&1`).
- Everything moves through GitHub PRs across machines — commit, push, PR; do not assume other
  workers share your filesystem.
