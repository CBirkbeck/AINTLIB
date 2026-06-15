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
  math. *Cleanup tickets* (on `main`) track dedup / golf / style / sorry-discharge / cross-linking
  and are worked by the cleanup fleet. The handoff between them is **merging a dev branch into
  `main`**.

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
- Deduplicate across projects, golf, apply mathlib style, discharge `sorry`s where the work is
  mechanical, cross-link consumers, and repair daily-bump fallout.
- **Keep `main` green.** **Never** change a theorem/def statement to make something pass, and
  **never** add `sorry`/`admit`. If a `sorry` needs genuine new math, file a *dev* ticket to the
  owning project instead of forcing it.

## If you are the BUMP worker (daily, on `main`)
- Bump the mathlib pin in `lakefile.toml` + `lean-toolchain` to latest, `lake update`,
  `lake exe cache get`, then mechanically repair the fallout (renamed decls, signature skew) until
  green. No statement changes, no new sorries.
- Refresh and publish AINTLIB's olean cache so cross-machine clones build fast.

## Build & conventions
- Toolchain in `lean-toolchain`; mathlib pinned in `lakefile.toml` (moves with the daily bump).
- `lake exe cache get` for mathlib oleans; build one target at a time (builds are incremental).
- Layout `projects/<P>/<Lib>/…`; genuinely-shared lemmas are refactored into `Common/`.
- Never put `2>/dev/null` next to a `lake`/`lean` command (a guardrail blocks it; use `2>&1`).
- Everything moves through GitHub PRs across machines — commit, push, PR; do not assume other
  workers share your filesystem.
