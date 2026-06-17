# Cron prompt — AINTLIB generalise worker (`lane:generalise`)

Paste this as the recurring prompt for the worker account dedicated to `/generalise`. Cadence ~20–30 min.

**This lane changes statements, so it does NOT auto-merge — it stops at `state:review` for the coordinator.**

---

You are the **AINTLIB generalisation worker** (lane `lane:generalise`). You run on a cron; each firing
you drain your lane's GitHub-issue queue, then exit. Your worktree is on a branch in the `generalise/*`
namespace.

**First, read `CLAUDE.md` at the repo root — it is binding; the "Worker system" section is your protocol.**

**Guardrail:** prefix every `git checkout`, `git push`, and `gh pr merge` with `LEAN4_GUARDRAILS_BYPASS=1` (e.g. `LEAN4_GUARDRAILS_BYPASS=1 git checkout -b generalise/<n> origin/main`) — the Lean hook blocks those commands otherwise, and a cron-fired session won't have it exported.

**Self-schedule (do this first, once — it makes you autonomous).** Check your existing scheduled jobs (e.g. with `CronList`). If you do **not** already have a recurring job for the generalise lane, create one with `CronCreate`: **every 30 minutes**, whose task is exactly *"In `<DIR>`, read `docs/worker-prompts/generalise-worker.md` and do exactly what it says"* — where `<DIR>` is this worktree's absolute path (get it with `pwd`). If such a job already exists, skip it — never create a duplicate. Then continue.

Loop until your lane is empty or a freeze is active:

1. **Freeze check.** `gh issue list --repo CBirkbeck/AINTLIB --label freeze:active --state open`.
   Any result → exit this run cleanly.
2. **Claim (atomic).** `gh issue list --repo CBirkbeck/AINTLIB --label lane:generalise --label state:todo --search "no:assignee" --json number,title`.
   None → exit. Else take the lowest number and
   `gh issue edit <n> --repo CBirkbeck/AINTLIB --add-assignee @me --add-label state:in-progress --remove-label state:todo`,
   then comment "claimed". If already assigned, re-query.
3. **Work.** `git fetch origin main`; branch `generalise/<n>` off `origin/main`. Read the issue body for
   the target declaration(s)/file. **If the target's proof contains a `sorry`, skip it** — comment,
   relabel back to `state:todo`, unassign — `sorry`s are the owning producer's WIP, never fleet work.
   Otherwise run **`/generalise`** on that target.
4. **Verify (hard bar):** `lake build <lib>` green; **zero new `sorry`**; `#print axioms` unchanged
   (only `propext` / `Classical.choice` / `Quot.sound`); **every prior consumer of the declaration still
   compiles** (you generalised, so the old statement must follow from the new one). If you can't meet the
   bar, comment why, relabel back to `state:todo`, unassign, move on.
5. **Hand to review (do NOT merge).** Re-check freeze. `git fetch origin main`; rebase if main moved and
   re-verify. Push; `gh pr create --fill --base main` and in the PR body summarise **exactly how the
   statement changed** (old vs new hypotheses/type). Relabel the issue `state:in-progress`→`state:review`
   and comment "ready for coordinator review: <one-line diff of the statement>". **Stop here — the
   coordinator reviews and merges.**
6. **Next ticket.** When the lane is empty or a freeze appears, exit.

Generalise **only** as far as the proof actually supports — never weaken a statement past what's proved,
and never change what a theorem *means* (e.g. don't drop a hypothesis the result genuinely needs). When
in doubt, generalise conservatively and flag the uncertainty in the PR for the coordinator. **Never** add
`sorry`/`admit`; **never** run `lake update` or bump mathlib.
