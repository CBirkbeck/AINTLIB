# Cron prompt — AINTLIB coordinator (maintenance, SAFE mode)

Runs on a cron (~every 2h). Each firing you do **fleet maintenance**, then exit. This is
**SAFE mode**: you **never** bump mathlib, **never** merge a statement-changing (`generalise`)
PR, and **never** add `sorry`. Those are surfaced for the human to do — not done here.

Repo: `CBirkbeck/AINTLIB`. Work from this worktree (`/Users/mcu22seu/Documents/GitHub/aintlib-main`,
on `main`). Use the **absolute** `gh` (`/opt/homebrew/bin/gh`) and python
(`/Users/mcu22seu/miniforge3/bin/python3`) — a cron-fired shell has a minimal PATH.

**Guardrail:** prefix any `git push` / `gh pr merge` with `LEAN4_GUARDRAILS_BYPASS=1`.

**Self-schedule (once).** `CronList`. If no recurring coordinator job exists, create a **durable**
one (`CronCreate`, `durable: true`, ~every 2h, off-minute) whose prompt is
*"In `/Users/mcu22seu/Documents/GitHub/aintlib-main`, read `docs/worker-prompts/coordinator.md` and do exactly what it says."*
If one already exists, skip — never duplicate. (Recurring crons auto-expire after 7 days; re-arm then.)

Each firing, in order:

1. **Freeze check.** `gh issue list --repo CBirkbeck/AINTLIB --label freeze:active --state open`.
   Any result → a bump/rename is in progress → **exit immediately, do nothing else**.

2. **Fleet status.** Pull open issues once and tally: `state:todo` (and how many are unassigned),
   `state:in-progress`, `state:review`, by lane. Note how many `lane:cleanup` closed in the last ~2h
   (throughput).

3. **Reset stuck tickets.** For each `state:in-progress` issue whose `updatedAt` is **>2h ago** and
   which has **no open linked PR**: relabel `state:in-progress`→`state:todo`, `--remove-assignee`,
   comment "reset: stale claim (no progress >2h)". (A worker claimed it then died/froze.) Be careful
   not to reset one that has an open PR in flight.

4. **Refill the cleanup queue (paced).** If unassigned `state:todo lane:cleanup` **< 40**:
   `/Users/mcu22seu/miniforge3/bin/python3 scripts/refill-cleanup-tickets.py --next --max 60`.
   It files the next un-ticketed project's cleanable files (dedup-safe, skips sorry-only files,
   one batch per run). If the queue is ≥ 40, **skip** — don't over-fill. Run a `--dry-run` first if
   unsure.

5. **Surface (do NOT act on) high-stakes items:**
   - **`generalise` review PRs:** any `state:review` issue → list it with the old→new statement so the
     human can review + merge. **Do not merge it yourself.**
   - **Mathlib bump:** if the `lakefile.toml` mathlib `rev` hasn't moved in **>24h** (or you can see
     mathlib master is well ahead), note **"bump due"**. **Do not bump.**

6. **Report** exactly one line, e.g.:
   `coordinator: todo=236(unassigned 236) inprog=2 review=0 | reset 0 | filed 0 (queue≥40) | bump:ok | review-PRs:0`

**Never** in this role: bump mathlib, merge a `generalise`/statement-changing PR, add `sorry`/`admit`,
ticket the vendored `FltRegular` project, or create a duplicate cron. If the cleanup queue is healthy
and nothing is stuck, a firing legitimately does nothing but report — that's fine.
