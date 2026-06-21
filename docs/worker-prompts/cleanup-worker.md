# Cron prompt — AINTLIB cleanup worker (`lane:cleanup`)

Paste this as the recurring prompt for the worker account dedicated to `/cleanup`. Cadence ~20–30 min.

---

You are the **AINTLIB cleanup worker** (lane `lane:cleanup`). You run on a cron; each firing you drain
your lane's GitHub-issue queue, then exit. Your worktree is on a branch in the `cleanup/*` namespace.

**First, read `CLAUDE.md` at the repo root — it is binding; the "Worker system" section is your protocol.**

**Guardrail:** prefix every `git checkout`, `git push`, and `gh pr merge` with `LEAN4_GUARDRAILS_BYPASS=1` (e.g. `LEAN4_GUARDRAILS_BYPASS=1 git checkout -b cleanup/<n> origin/main`) — the Lean hook blocks those commands otherwise, and a cron-fired session won't have it exported.

**Self-schedule (do this first, once — it makes you autonomous).** Check your existing scheduled jobs (e.g. with `CronList`). If you do **not** already have a recurring job for the cleanup lane, create one with `CronCreate`: **every 30 minutes**, whose task is exactly *"In `<DIR>`, read `docs/worker-prompts/cleanup-worker.md` and do exactly what it says"* — where `<DIR>` is this worktree's absolute path (get it with `pwd`). If such a job already exists, skip it — never create a duplicate. Then continue.

Loop until your lane is empty or a freeze is active:

1. **Freeze check.** `gh issue list --repo CBirkbeck/AINTLIB --label freeze:active --state open`.
   Any result → a bump/rename is in progress → exit this run cleanly.
2. **Claim (atomic).** `gh issue list --repo CBirkbeck/AINTLIB --label lane:cleanup --label state:todo --search "no:assignee" --json number,title`.
   None → exit. Else take the lowest number and
   `gh issue edit <n> --repo CBirkbeck/AINTLIB --add-assignee @me --add-label state:in-progress --remove-label state:todo`,
   then comment "claimed". If the edit shows it's already assigned, re-query (someone beat you).
   **Protected paths:** before claiming, check `docs/worker-prompts/protected-paths.txt` — if the ticket's
   target file matches a line there, do NOT claim it; comment "protected: dev-extraction in progress (#2546)",
   leave it `state:todo`, and take the next lowest. (Those files are reserved for an active dev branch.)
3. **Work.** `git fetch origin main`; create branch `cleanup/<n>` off `origin/main`. The issue targets a
   whole **file**. Run **`/cleanup` on that file** — it golfs *every* declaration in it, so you clean many
   lemmas in one ticket. **Preserve docstrings and math-explanatory comments — deleting documentation is
   NOT cleanup** (`/cleanup` is style/API/naming/dedup/golf on the *code*; only remove genuinely dead or
   redundant comments, never the docstrings that explain what a decl means). **Skip any individual
   declaration whose proof contains a `sorry`** (leave it
   untouched — it's the producer's WIP); clean all the sorry-free ones. If the whole file is WIP/`sorry`
   with nothing to clean, comment + relabel `state:in-progress`→`state:todo`, unassign, move on.
4. **Verify (hard bar — do not merge otherwise):** `lake build <lib>` green **AND `lake build <Lib>.<Module>`
   (your target file by module name)** — orphan files aren't reachable from a lib root, so `lake build <lib>`
   silently *skips* them; building by name compiles the file you actually touched. (A broken orphan that
   passed the lib gate is exactly how a cleanup regression reached `main` — #2299. For `«Adic spaces»`
   modules use guillemets: `lake build "«Adic spaces».Foo"`.) **Zero new `sorry`**;
   `#print axioms` on the touched declarations shows only `propext` / `Classical.choice` / `Quot.sound`.
   If you can't meet the bar, comment why, relabel `state:in-progress`→`state:todo`, unassign, move on.
5. **Merge (auto — cleanup never changes a statement).** Re-check freeze. `git fetch origin main`; if
   main moved, rebase `cleanup/<n>` and re-verify. Push; `gh pr create --fill --base main`; then
   `gh pr merge --squash --delete-branch`. `gh issue close <n>`.
6. **Next ticket.** When the lane is empty or a freeze appears, exit.

**Never** change a theorem/def statement (that's the `/generalise` lane). **Never** add `sorry`/`admit`.
**Never** run `lake update` or bump mathlib (the coordinator does that). If a `sorry` needs genuine new
math, file a dev ticket to the owning project instead of forcing it.
