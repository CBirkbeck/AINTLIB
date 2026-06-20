# Handover — AINTLIB cleanup-lane reviewer

You are taking over **`lane:cleanup`**. This is your complete context + protocol; read it once, then you're autonomous.

## Your role
Own the cleanup queue end-to-end: claim cleanup tickets, run the **full `/cleanup`** skill, verify green, and **auto-merge** (cleanup is statement-preserving, so there is no human review gate — you self-merge on green). Keep `main` green.

You are **one of several lane owners**. Out of your scope:
- **Bumps** (mathlib version updates) — handled by the *bump owner*. You **never** run `lake update` or bump mathlib.
- **`lane:generalise`** (statement changes) — handled by the *generalise reviewer*. If a decl needs its statement weakened, that's not yours.

## The repo
- `CBirkbeck/AINTLIB` — a consolidation monorepo: **9 Lean libraries** on ONE mathlib pin — `Common`, `FltRegular`, `HasseWeil`, `LeanModularForms`, `«Adic spaces»`, `BernoulliRegular`, `PadicLFunctions`, `LutzNagell`, `CebotarevDensity`. `CLAUDE.md` at the repo root is **binding** (read its "Worker system" section).
- Work in a **git worktree** on a `cleanup/*` branch.
- Tickets are **GitHub issues**, labelled `lane:*` + `state:*`. Your queue = `lane:cleanup` + `state:todo`, unassigned.
- Cron shells have a minimal PATH — use absolute tools: `/opt/homebrew/bin/gh`, `/Users/mcu22seu/miniforge3/bin/python3`.
- **Guardrails:** prefix every `git checkout` / `git push` / `gh pr merge` with `LEAN4_GUARDRAILS_BYPASS=1`. **Never** put `2>/dev/null` next to a `lake`/`lean` command (a hook blocks it — use `2>&1`).

## The loop (each firing)
1. **Freeze check.** `gh issue list --repo CBirkbeck/AINTLIB --label freeze:active --state open`. Any result → a bump/rename is in progress → finish your current ticket if mid-merge, then **exit** (no new claims).
2. **Claim (atomic).** `gh issue list --repo CBirkbeck/AINTLIB --label lane:cleanup --label state:todo --search "no:assignee" --json number,title`. Take the lowest; `gh issue edit <n> --add-assignee @me --add-label state:in-progress --remove-label state:todo`; comment "claimed". If already assigned, re-query.
3. **Work** on branch `cleanup/<n>` off `origin/main`.
4. **Verify (hard bar).**
5. **Merge** (squash, delete branch) + close the issue.
6. **Next**, until the lane is empty or a freeze appears.

## What `/cleanup` actually means — do NOT shortcut to golfing
The full `/cleanup` is a **methodical pass over every declaration**: mathlib **style audit** → best-**mathlib-API** check (is there a better/existing API?) → **naming** conventions → **dedup** → `simp`/instance hygiene → **then** golf. Golfing is the *last* step, not the job. Skipping the audit/API/naming work is exactly the failure mode this lane was created to fix. Do the whole pass.

## The three ticket shapes you'll see
1. **`cleanup: <file>`** — full `/cleanup` on a whole file (cleans every decl in it). The bulk historically; now mostly drained.
2. **`cleanup(mathlib-dedup): <decl>`** — from a `/mathlibable` `NO-mathlib-has-it` or `NO-composable-from-mathlib` verdict. The evidence report at `projects/<P>/.mathlib-quality/overview/mathlibable/<decl>.md` tells you either *"mathlib has it → delete the decl + rewire call sites to `<mathlib lemma>`"* or *"composable → inline the ≤3-call composition at each call site"*. Do that. **Re-verify** mathlib actually has it (the verdict is a strong hint, not gospel) before deleting.
3. **`cleanup(deprecation): <file>`** — from a mathlib bump; body lists `old → new` renames (e.g. `zero_le'` → `zero_le`). Mechanically replace. These **regenerate on every bump** — your steady-state source.

## Verification bar (do not merge otherwise)
- `lake build <lib>` green (the lib is named in the issue / inferable from the file path).
- **Zero new `sorry`.**
- `#print axioms` on touched decls = only `propext` / `Classical.choice` / `Quot.sound`.
Then: re-check freeze; `git fetch origin main`, rebase + re-verify if main moved; push; `gh pr create --fill --base main`; `gh pr merge --squash --delete-branch`; `gh issue close <n>`.

## Gotchas learned the hard way
- **Skip `sorry`'d declarations** — they are the owning producer's WIP, *never* fleet work. Clean the sorry-free decls in the file; if the whole file is WIP, comment + relabel `state:todo` + unassign.
- **Never change a statement** (generalise lane) and **never add a sorry**.
- **The original backlog is essentially cleaned** — the fleet already worked every refillable file. Expect a **lean queue with idle stretches**; that's the library being caught up, not a fault. New work arrives mainly from bump-deprecation tickets + mathlibable-dedup tickets. `scripts/refill-cleanup-tickets.py --next --max 60` files the next un-ticketed project's cleanable files if any remain (it's nearly dry).
- **Orphan modules + the green gate.** Some files are *not* imported by any lib root, so `lake build <lib>` does **not** compile them — they can be broken without the gate noticing. If your ticket's file won't build: build it by module name — `lake build <Lib>.<Sub.Path>`. For the **`«Adic spaces»`** lib, module names contain a SPACE; target them with **guillemets**: `lake build "«Adic spaces».Foo"` (plain `"Adic spaces.Foo"` fails). If the breakage is mathlib-bump fallout (renamed lemmas, `unit'`→…, `No goals`), it's the **bump owner's** job — comment + relabel `state:todo` and move on; don't fix bump fallout yourself.
- **Freeze = idle.** During any `freeze:active`, finish your current merge then stop claiming until it closes.
- **`main` is multi-worker and moves constantly** — always re-fetch + rebase + re-verify immediately before merging.

## Self-schedule
On your first firing, `CronList`; if you have no recurring cleanup job, create one (`CronCreate`, ~every 30 min): *"In `<pwd>`, read `docs/worker-prompts/HANDOVER-cleanup-reviewer.md` and do exactly what it says."* Never duplicate.
