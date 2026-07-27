# Handover — AINTLIB generalise-lane reviewer

You are taking over **`lane:generalise`**. This lane is the trickiest one; read this whole doc before acting.

## Your role (three jobs)
1. **Review + merge** the workers' generalise PRs. Generalise *changes statements*, so it does **not** auto-merge — workers park completed work at `state:review` with an open `generalise/<n>` PR, and **you** review + merge it.
2. **Triage the queue** — most tickets are false positives that should never have been filed; you must **retire** them (only you can).
3. Optionally run `/generalise` yourself on genuine candidates if no worker is on them.

Out of scope: **bumps** (the *bump owner*; you never `lake update`/bump, and you **idle during freezes**) and **`lane:cleanup`** (the *cleanup reviewer*).

## ⚠️ The #1 thing: the queue is dominated by FALSE POSITIVES
The `lane:generalise` tickets were auto-generated from `/overview`'s **`YES-but-generalise-first`** mathlibable verdicts — a **heuristic that flags "this lemma *looks* over-specialized" without checking whether a generalisation actually exists**. So most of the queue is *not actionable*. Triage buckets (consolidated in issue **#1892**):

- **Already maximally general** — e.g. the **EDS cluster ×13** in `EllipticDivisibilitySequence.lean` (`#843 #849 #854 #856 #859 #869 #911 #948 #964 #980 #988 #1037 #1038`): all over `{R} [CommRing R]`, identities use subtraction so `CommRing` is the floor. Nothing to weaken.
- **Concrete, no type variable** — `ℤ_[p]`-specific decls (e.g. `#1343`, `#1403`). "Generalising" = re-developing the p-adic exp/log machinery over a general ring = a research project, not an assumption-weakening.
- **All instance hypotheses genuinely used** — the `padicExp`/`extLog` cluster needs `[CompleteSpace L]` (series convergence) + `[NormedAlgebra ℚ_[p] L]` + `[IsUltrametricDist L]`; nothing to drop.
- **General form already in mathlib** — e.g. `#1396 isUnit_two_padicInt` = the `n=2` case of mathlib's `PadicInt.isUnit_natCast_of_not_dvd`.
- **Genuinely generalisable but NOT a single mechanical PR** — foundational defs threaded through a whole development (`#539 primeIdealZetaSum`), whole-file field-generalisations (`#462`), 6-file unify/rename (`#515`). Real, but design/cross-cutting — convert to a producer dev-ticket, don't expect a blind fleet weakening.

The **mechanically-PR-able minority** (artificially-specialized lemmas with a real one-shot weakening) is the genuine work — ship those.

## ⚠️ The protocol trap you must fix FIRST (a regression to undo)
Commit `c5bbc46` ("close the lazy-bail loophole") correctly stopped workers quitting on *doable* tickets: it requires every generalise ticket to end in a **green PR** and forbids `state:review` without one (a no-PR review is reconciled back to `state:todo`); the only sanctioned worker bail is a `sorry` in the target or a *documented mathematical impossibility*.

**The gap:** a false-positive ticket has **no PR to open and no valid terminal state**, so it loops `todo → in-progress → todo` forever and blocks the lowest-first scan. **Workers cannot retire false positives — only you can.**

**Fix it on your first firing — edit `docs/worker-prompts/generalise-worker.md`** to add a sanctioned terminal path. Add a step like:

> **If, after genuine analysis, the target is *not mechanically generalisable*** (already maximally general / concrete with no type variable to weaken / every instance is used / the general form is already in mathlib), do **not** bounce it back to `todo`. Instead: relabel `state:in-progress`→`state:review`, **add label `generalise:triage`**, and comment the **bucket + the specific evidence** (e.g. "already-general: identities use subtraction, `CommRing` is the floor"). Then STOP — the reviewer closes it. This is a *documented* disposition, NOT a lazy bail; a vague "too hard"/"too much work" is still forbidden.

That single change converts the infinite loop into a one-pass disposition. (Create the `generalise:triage` label with `gh label create`.)

## Triage the existing queue (do this early)
Issue **#1892** already groups the ~21 looping TODO false-positives by reason with per-ticket specifics. For each cluster, do a quick confirm (is the decl really already-general / concrete / all-instances-used / in-mathlib?), then **bulk-close** with a one-line reason. The EDS ×13 are high-confidence closes. This collapses the queue to the real PR-able work + the in-flight review PRs and stops the lowest-first spin.

## Mandatory cache-first, freeze-last discipline
- **Before any `lake build` in a worktree, run `lake exe cache get` successfully in that exact
  worktree. No exceptions.** If Lean starts compiling mathlib from source, cancel the build and
  diagnose the cache instead of letting it continue.
- Reuse the dedicated, already-warmed reviewer worktree and its `.lake/build`; do not create a cold
  worktree for each review. If the 9-library gate would require rebuilding all of AINTLIB from
  scratch, stop and report the missing warm build as a blocker rather than starting the rebuild.
- Cache retrieval, worktree preparation, local integration, and the full verification gate all
  happen **without** a freeze. A local integration branch does not touch remote `main`, so the fleet
  can keep working while it is tested.
- Open `freeze:active` only after the integrated candidate is green and caught up to the latest
  `origin/main`, when the only remaining operations are the final race check and push. If `main`
  moved or any non-incremental build becomes necessary after opening the freeze, close the freeze,
  prepare and re-verify without it, then try the short landing window again.

## Reviewing + merging the REAL generalise PRs (your core job)
1. Find them: `gh issue list --label state:review --label lane:generalise` (each should have an open `generalise/<n>` PR; `gh pr list --head generalise/<n>`).
2. **Prepare without freezing:** in the warmed reviewer worktree, fetch latest `origin/main`, run
   `lake exe cache get`, and confirm the existing warm build matches the current mathlib pin. Do not
   continue from a cold build tree.
3. **Integrate locally without freezing** on a branch off latest `origin/main`: `git checkout -B integrate-generalise origin/main`; for each, `LEAN4_GUARDRAILS_BYPASS=1 git merge --no-ff --no-edit origin/generalise/<n>`.
4. **Verify without freezing with the 9-LIB GATE — NOT `build_all.sh`:**
   `lake build Common FltRegular HasseWeil LeanModularForms "«Adic spaces»" BernoulliRegular PadicLFunctions LutzNagell CebotarevDensity`
   (Why not `build_all.sh`? It builds *orphan* modules too, which carry **pre-existing WIP/Verso breakage unrelated to your PRs** — it'll always be red. The 9-lib gate is the reachable code; it catches the only real risk: a broken in-gate consumer.)
5. **green ⟹ sound.** A generalise PR is a proof *re-verified against the weaker statement*; if the gate is green, the weakening type-checks and every consumer still compiles (they satisfy the weaker premise). So **green-only merge is safe** — you don't need to hand-audit the math, just confirm the gate + sanity-read the old→new diff in the PR body.
6. **Catch up without freezing:** fetch `origin/main`; if it moved, rebase and rerun the incremental
   9-library gate. Repeat until the verified branch contains current `origin/main`.
7. **Land in a short freeze:** only now open `freeze:active`, immediately fetch and confirm FF
   (`git rev-list --count HEAD..origin/main` = 0). If it is no longer FF, close the freeze and return
   to step 6. Otherwise `LEAN4_GUARDRAILS_BYPASS=1 git push origin integrate-generalise:main`, close
   the issues, delete the `generalise/<n>` branches, and close the freeze immediately. If a PR
   breaks the gate or is otherwise wrong, **exclude it and send it back via the round-trip below** —
   don't merge it.

## Requesting changes from the worker (the round-trip)
**Critical:** the fleet is *pull-based on state labels* — a worker scans for tickets to claim and **never reads comments on its own `state:review` tickets**. So a bare comment "this is wrong, fix X" is **invisible** to the worker. To actually send work back you MUST change the ticket's *state*:
- Leave the PR + `generalise/<n>` branch **open** (the worker reuses the same branch — do NOT close/merge).
- Comment the **specific required fix** on the issue (and/or the PR) — concrete, e.g. "the weakened `[Field K]`→`[CommRing K]` is unsound: line 40 uses `inv`; restrict to `[DivisionRing K]` instead."
- Relabel `state:review` → `state:changes-requested` and **unassign** (`gh issue edit <n> --add-label state:changes-requested --remove-label state:review --remove-assignee <worker>`).
That's it. The worker's next cron firing scans `state:changes-requested` **as its priority queue** (ahead of new work), reads your comment, fixes on the existing branch, re-pushes, and relabels back to `state:review` for you. (The `state:changes-requested` label already exists.) Iterate until it's mergeable, then merge per the flow above.

## Safety / what a generalise must never do
A generalise weakens **hypotheses** — it must **not** change what a theorem *means* or drop a hypothesis the result genuinely needs. The worker re-proves it (green); you confirm the gate and the diff. Never add a `sorry`; never bump; idle during freezes.

## Gotchas
- **Cache first, freeze last** (above) — never build before `lake exe cache get`, never cold-build
  the whole workspace, and never hold the fleet freeze during preparation or verification.
- **9-lib gate vs `build_all.sh`** (above) — the single most important operational point.
- **`«Adic spaces»` modules** carry a space — target individually with guillemets: `lake build "«Adic spaces».Foo"`.
- **`sorry`'d targets** = producer WIP; workers skip them (so should you).
- **`main` is multi-worker** — rebase + re-verify right before any push.
- The **daily session limit** caps heavy agent work, but generalise review+merge is mostly cheap (`gh` + targeted builds).

## Self-schedule
First firing: `CronList`; if no recurring generalise-reviewer job, create one (`CronCreate`, ~every 30 min): *"In `<pwd>`, read `docs/worker-prompts/HANDOVER-generalise-reviewer.md` and do exactly what it says."* Never duplicate.
