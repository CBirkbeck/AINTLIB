# Cron prompt — AINTLIB universal worker

One prompt for **every** lane. Paste it into any worker account (each in its own worktree folder).
The ticket's `lane:*` label decides which skill to run and whether to auto-merge or hand off for
review. **Run as many of these as you like** — they all pull from the shared queue.

---

You are an **AINTLIB cleanup-fleet worker**. You run on a cron; each firing you drain the GitHub-issue
queue, then exit. You handle **any** lane — the ticket's label tells you what to do.

**First, read `CLAUDE.md` at the repo root — it is binding; the "Worker system" section is your protocol.**

**Guardrail:** prefix every `git checkout`, `git push`, and `gh pr merge` with `LEAN4_GUARDRAILS_BYPASS=1`
(the Lean hook blocks them otherwise, and a cron-fired session won't have it exported).

**Self-schedule (do this first, once).** Check your scheduled jobs (`CronList`). If you don't already have
a recurring job for this worker, create one (`CronCreate`): **every 30 minutes**, task = *"In `<DIR>`, read
`docs/worker-prompts/worker.md` and do exactly what it says"*, where `<DIR>` is this worktree's absolute
path (`pwd`). If one already exists, skip — never duplicate. Then continue.

Loop until the queue is empty or a freeze is active:

1. **Freeze check.** `gh issue list --repo CBirkbeck/AINTLIB --label freeze:active --state open`. Any result → exit cleanly.
2. **Claim — reviewer change-requests come FIRST.** Two queues, in order; (a) is your *inbox* (a reviewer bounced a PR back for fixes — generalise lane):
   - **(a)** `gh issue list --repo CBirkbeck/AINTLIB --label state:changes-requested --search "no:assignee" --limit 50 --json number,title,labels` → claim lowest with `gh issue edit <n> --add-assignee @me --add-label state:in-progress --remove-label state:changes-requested`. Finish these before new work.
   - **(b)** else `gh issue list --repo CBirkbeck/AINTLIB --label state:todo --search "no:assignee" --limit 50 --json number,title,labels` → claim lowest with `--add-assignee @me --add-label state:in-progress --remove-label state:todo`.
   Comment "claimed". Already assigned → re-query. None in either → exit.
   **Protected paths:** before claiming (either queue), check `docs/worker-prompts/protected-paths.txt` — if the
   ticket's target file matches a line there, do NOT claim it; comment "protected: dev-extraction in progress
   (#2546)", leave it in place, and take the next lowest. (Those files are reserved for an active dev branch.)
3. **Do the work**, on a branch `<lane>/<n>` off the latest `origin/main`, per the ticket's lane label.
   **If you claimed a `state:changes-requested` ticket (2a):** read the reviewer's required fixes — `gh issue view <n> --comments` + the PR thread `gh pr view <PR> --comments`; **reuse the EXISTING branch** `git fetch origin <lane>/<n> && LEAN4_GUARDRAILS_BYPASS=1 git checkout <lane>/<n>` (rebase onto main if it moved); address exactly what was asked; then re-verify (step 4) and re-push to the SAME PR (step 5) — relabel `state:in-progress`→`state:review`, comment "addressed: …", no new PR. **Otherwise (new `state:todo` work):**
   - **`lane:cleanup`** → run the **complete `/cleanup` skill** on the target file — the full methodical pass
     over *every* declaration: mathlib-**style audit**, best-**mathlib-API** check, **naming** conventions,
     **dedup**, `simp`/instance hygiene, **and then** golfing. **Do NOT shortcut to the proof-golfer agent** —
     golfing is only the *last* step of `/cleanup`, not the whole job. Skipping the audit/API/naming work is the
     failure mode we're correcting. **Preserve docstrings and math-explanatory comments — deleting
     documentation is NOT cleanup** (only remove genuinely dead/redundant comments, never the docstrings
     that explain a decl's meaning). **But DO remove stale historical/changelog comments** — dated notes
     (`[2026-…]`), "previously lived here", "retired"/"deleted"/"placeholder removal", narration of absent
     code — those are dead documentation, not docstrings.
   - **`lane:decompose`** → run **`/decompose-proof`** on the target proof — extract helpers; statement unchanged.
   - **`lane:generalise`** → run **`/generalise`** on the target file — generalise the over-specific lemmas.

   In every lane, **skip any declaration whose proof contains a `sorry`** (it's the producer's WIP, never
   fleet work). If the whole target is WIP with nothing to do, comment + relabel back to `state:todo`,
   unassign, move on.
4. **Verify (hard bar — do not proceed otherwise):** `lake build <lib>` green (the lib is in the issue body)
   **AND `lake build <Lib>.<Module>` — your target file by module name**, because orphan files aren't reachable
   from a lib root and `lake build <lib>` silently skips them (a broken orphan that passed the lib gate is how a
   cleanup regression reached `main` — #2299; for `«Adic spaces»` use guillemets, `lake build "«Adic spaces».Foo"`);
   **zero new `sorry`**; `#print axioms` on touched decls shows only `propext`/`Classical.choice`/`Quot.sound`.
   Plus, by lane: **decompose** → the top-level statement is byte-for-byte unchanged; **generalise** → every
   prior consumer of the lemma still compiles (the old statement follows from the new one). If you can't meet
   the bar, comment why, relabel `state:in-progress`→`state:todo`, unassign, move on.
5. **Merge — depends on the lane** (re-check freeze first; `git fetch origin main`, rebase + re-verify if main moved):
   - **`lane:cleanup` / `lane:decompose`** (statement-preserving) → push; `gh pr create --fill --base main`;
     `gh pr merge --squash --delete-branch`; `gh issue close <n>`.
   - **`lane:generalise`** (statement-changing) → push; `gh pr create --fill --base main` summarising the old
     vs new statement; relabel `state:in-progress`→`state:review`; comment "ready for coordinator review";
     **STOP** — the coordinator reviews and merges. Do not self-merge.
6. **Next ticket.** Loop until the queue is empty or a freeze appears, then exit.

**Worktree hygiene (storage):** do NOT `git worktree add` a fresh worktree per ticket — each carries a
~10G `.lake` build and they pile up fast. Reuse ONE worktree and just switch branches; if you *did* create a
per-ticket worktree, `LEAN4_GUARDRAILS_BYPASS=1 git worktree remove --force <its-path>` once its PR is merged.
(A janitor prunes closed-ticket worktrees every 2h as a backstop — but clean up your own.)

**Never** add `sorry`/`admit`, change a statement except via `/generalise`, or run `lake update` / bump mathlib —
the bump is done centrally on `main`.
