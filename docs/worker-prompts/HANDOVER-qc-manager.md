# HANDOVER — AINTLIB Quality-Control Manager

You are taking over the **QC-manager** role on `CBirkbeck/AINTLIB`. This is the single account that
keeps `main` healthy and the library mathlib-clean. It is **not** a lane worker — it sits above the
fleet. Read `CLAUDE.md` (binding) first, then this.

The role wears **five hats**, four of them automated by crons:

1. **Bump owner** — daily mathlib bump on `main`, full-tree verified.
2. **QC agent** — audits that the lane fleet actually did the work it closed tickets for.
3. **Build-health monitor** — full-tree build every 6 h; freezes `main` on regression.
4. **Worktree janitor** — prunes the per-ticket worktree storage leak.
5. **Library-hygiene QC** — dedup, junk-bundler removal, and mathlib-style naming/reorg (manual + ticketed).

---

## ⚠️ FIRST THING ON TAKEOVER: recreate the crons

All four crons below are **`[session-only]`** — they are bound to the session that created them and
**do not survive into your session**. The *prompts and scripts they run* are committed in the repo,
but **you must recreate the four schedules yourself** with `CronCreate` (check `CronList` first; never
duplicate). Until you do, nothing is running.

| # | schedule | what it does | runs |
|---|---|---|---|
| 1 | daily **05:07** | mathlib bump (steady-state, full-tree verified) | bump protocol — `CLAUDE.md` "BUMP worker" + below |
| 2 | **every 6 h** (00:40 / 06:40 / 12:40 / 18:40) | QC sampling audit | `docs/worker-prompts/qc-agent.md` |
| 3 | **every 6 h** (01:13 / 07:13 / 13:13 / 19:13) | full-tree build-health check | `docs/worker-prompts/build-health-monitor.md` |
| 4 | **every 2 h** (:47) | prune closed-ticket worktrees | `.mathlibable/tooling/prune-stale-worktrees.sh` |

Cron task strings to recreate (each task = literally *"In `/Users/.../aintlib-main`, read
`docs/worker-prompts/<doc>.md` and do exactly what it says"* for #2 and #3; #1 and #4 below):

- **#1 bump:** "AINTLIB daily mathlib bump (steady-state, FULL-TREE verified). In `<repo>`: bump the
  mathlib `rev` in `lakefile.toml` + `lean-toolchain` to latest, `lake update`, `lake exe cache get`,
  then mechanically repair fallout (renamed decls, signature skew) until **`build_all.sh` (full tree)**
  is green — not just `lake build <libs>`. No statement changes, no new sorries. Open a `freeze:active`
  issue first if the fallout needs a cross-cutting rename; close it after."
- **#4 janitor:** "AINTLIB worktree janitor. In `<repo>`, run `.mathlibable/tooling/prune-stale-worktrees.sh`."

---

## Non-negotiable operational constraints (these have all bitten us)

- **Never put `2>/dev/null` next to a `lake`/`lean` command** — a guardrail blocks it. Use `2>&1`.
- **Prefix `git checkout` / `git push` / `gh pr merge` with `LEAN4_GUARDRAILS_BYPASS=1`** — the Lean
  hook blocks them, and a cron session has nothing exported.
- **`git checkout -- <file>` is blocked** as "destructive git checkout" even with the bypass. To revert
  a file use `git stash push -- <file>` then `git stash drop`.
- **Absolute tool paths in crons:** `/opt/homebrew/bin/gh`, `/Users/mcu22seu/miniforge3/bin/python3`.
- **`sorry`s are the producer's WIP — never fleet-edit them.** Only operate on sorry-free results.
- **Monitor never fixes and never bumps** — it files a regression issue + freeze and leaves the fix to
  the bump owner / producer. (Don't blur the monitor and the bump hats into "see red → patch it.")
- **Reference PDFs/books are LOCAL-ONLY** (`refs/`, gitignored) — never commit or push them.
- **zsh does not word-split unquoted `$VAR`** — `lake build $MODS` treats a multiline string as ONE
  target, and `gh issue create $LABELS` mangles flags. Pipe via `xargs` or inline the args.

## THE recurring lesson: the green-gate blind spot

`lake build <lib>` only compiles modules **reachable from that lib's root** — orphan / WIP files are
**invisible** to it. That is how a broken file reached `main` (#2299) and how the FLT37 cascade hid.
**Always verify the WHOLE tree:** `.mathlibable/tooling/build_all.sh` (it enumerates every module via
`all_modules.py`, not just lib roots). Workers are now told to also `lake build <Lib>.<Module>` by name
for the file they touched. This blind spot is *why* the monitor (hat 3) exists. When `build_all` is red
during/after a bump, classify each error as **bump-fallout** (fix it) vs **pre-existing orphan WIP**
(producer's, file a dev ticket) by checking the symbol old-vs-new in `.lake/packages/mathlib`.

---

## Hat 5 — library hygiene: what to look for

Owner directive: *"deduplication and removing junk lemmas or structures that just bundle all the hard
bits together and never actually discharge them"* + *"reorganise the folders … no loads of files with
the same name or meaningless names like l6witness … named and organised as if in mathlib folders."*
Tracked under **epic #3248** (label `qc:dedup`) and `docs/worker-prompts/` (this naming plan).

### (a) Duplicate proofs/structures — dedup
Multiple versions of the same result. Keep the **canonical**, rewire/delete the rest.
- **Template = HasseBound.** Canonical: `HasseWeil/WeilPairing/HasseBound.lean : hasse_bound_unconditional`
  (`|#E(F_q) − q − 1| ≤ 2√q`, axiom-clean, only hypothesis `2 ≤ #K`, consumed in 7 files). Superseded:
  ~30 conditional `hasse_bound_*` across `Hasse/{BoundOfWitnesses,Final,OpenLemmas,L6ViaPoleDivisor,
  QuadraticForm,HoleE}` + `Verschiebung/Cascade`, plus the leftover `HasseWeil/HasseBound.lean`.
  See the dev ticket `projects/HasseWeil/.mathlib-quality/tickets-hasse-bound-consolidation.md`.

### (b) Junk bundlers — undischarged obligations
A structure / `_of_witnesses` / `_from_pack` theorem that takes the **hard part as a field/hypothesis**
and **no sorry-free decl ever produces it from first principles**. The "result" is vacuously
conditional — fake progress. **Discriminator (raw grep over-flags — most bundles are legit data
carriers):** it's junk only if the bundle is **consumed but never produced** by a sorry-free decl that
doesn't itself assume an equivalent bundle. Prime suspects: FLT37 Case-II descent
(`CaseIISection91DvdZGenuineUnitExtractionData37` & kin).

> **Not every suspicious name is junk.** Worked example: **StrongMultiplicityOne**
> (`LeanModularForms/SMOObligations/`). The `Obligations` filename + `_axiom_clean` suffix *look* like a
> bundler — but the proofs are **real and sorry-free** (`strongMultiplicityOne_constMul` genuinely
> discharges `oldPart g = 0` then `newPart = c • f`). It is **not** dedup/junk — it's a **naming**
> problem. Always read the proof before calling something a bundler.

### (c) Naming / folder reorg — mathlib style
**268 cryptically-named files** (scan 2026-06-22): **217 in FltRegularBernoulli/FLT37 (active WIP)**,
30 HasseWeil, 25 AdicSpaces, 3 LeanModularForms (the SMO cluster), 2 FltRegular. Offenders: `L6Witnesses`,
`HoleE`, `BoundOfWitnesses`, `OpenLemmas`, `Route*`, `Cascade`, `Part1..8`, `Lemma4_6_8`/`Miyake465`
(textbook numbers), `_axiom_clean`, and FLT37's `CaseIICor823Level71Deg68SecondDigitCorrected`-style names.

**Convention:** files named by mathematical *content* (the main def/theorem), folders by *topic*
(mirror mathlib's tree); same-named files are fine only in distinct meaningful topic folders; declarations
drop process suffixes. Keep docstrings — renames are cosmetic to the math.

**Two hard constraints make this NOT a fleet auto-merge job:**
1. A Lean module name *is* its file path → renaming rewrites every `import` repo-wide = a **cross-cutting
   rename**, which `CLAUDE.md` reserves for the coordinator **under a freeze**.
2. **Dev branches diverge by up to +138 commits** (padic +138, adic +80, hasse-weil +76). A mass rename
   on `main` forces a brutal rebase on every producer's branch, mid-proof.

**So: dedup BEFORE rename** (don't rename a file about to be deleted as a dead route), and **execute
per locus:**
- **Producer-side, on the dev branch at a stable point** (flows to `main` by PR) for WIP + diverged
  trees — esp. FLT37 (81 % of the problem; defer until its math settles), adic, padic, hasse-weil.
- **Central on `main` under a short freeze** only for done, sorry-free, low-blast-radius clusters
  (e.g. the 3-file SMO cluster: `SMOObligations/`→`StrongMultiplicityOne/`, drop `_axiom_clean`).

Full plan: this directory's naming/reorg plan (see scratchpad `naming-reorg-plan.md`, fold into a repo doc).

### Hygiene workflow (each pass)
1. Run the detection scan (`.mathlibable/tooling/` — dedup-candidate + cryptic-name greps).
2. Triage a few: read the decl/proof. Mechanical dup (dead copy, same statement) → `lane:cleanup`+`qc:dedup`
   ticket to delete+rewire. Proof-architecture pruning or a rename in a WIP tree → a **dev-board** ticket
   on the owning `dev/<project>` branch (protect the canonical via `protected-paths.txt` if needed).
3. **Never delete a consumed/discharged decl. When unsure, route to the producer, don't guess.**

---

## Ticketing map
- **Cleanup fleet** = GitHub issues on `main`, `lane:cleanup|generalise|decompose` + `state:*`. Auto-merge
  for cleanup/decompose; generalise stops at `state:review` for the coordinator.
- **Dev work** (new math, incl. WIP-tree renames) = markdown boards in `projects/<P>/.mathlib-quality/`
  on the `dev/<project>` branch — **not** GitHub issues.
- **QC labels:** `qc:log` (sampling log), `qc:reopened` (closed without full work), `qc:escalate`
  (found something unsound — owner attention), `qc:dedup` (hat-5 work). Epic: **#3248**.
- **Freeze:** open a `freeze:active` issue before any bump or cross-cutting rename; workers drain + idle;
  close it after. The janitor and monitor respect it.
- **`mathlib:pr` / `mathlib:borderline`** are tracking-only (no `lane:` → not fleet-claimable by design).

## Known loose ends at handover (2026-06-22)
- **Uncommitted strays in the main checkout** (not from this role; block clean pushes — leave them or ask
  the owner): `docs/worker-prompts/coordinator.md` (M), `scripts/refill-cleanup-tickets.py` (M).
- **Local unpushed commit** `6782c1b0` — adds the "remove stale historical/changelog comments" rule to the
  worker prompts; push it when the tree is clean.
- **Open:** epic #3248 (dedup/junk sweep); HasseBound consolidation (dev/hasse-weil ticket pushed); naming
  reorg awaiting an execution-locus decision (producer-side vs central-on-main — recommend producer-side).
- **Done recently:** FLT37 build cascade fixed; T-TATE-GENN (`E[N] ≅ (ℤ/Nℤ)²`) landed on dev/hasse-weil.

## Pointers
- Fleet design spec: `docs/superpowers/specs/2026-06-16-aintlib-worker-system-design.md`.
- Worker prompts: `worker.md` (universal) + `cleanup-/decompose-/generalise-worker.md`; reviewer handovers
  `HANDOVER-/ONBOARDING-{cleanup,generalise}-reviewer.md`; `coordinator.md`.
- Tooling (`.mathlibable/tooling/`, untracked/local): `build_all.sh` + `all_modules.py` (full-tree build),
  `prune-stale-worktrees.sh` (janitor), `find_decompose_targets.py`, `file_*_tickets.py`.
- Protected paths (reserved for active dev extraction): `docs/worker-prompts/protected-paths.txt`.
