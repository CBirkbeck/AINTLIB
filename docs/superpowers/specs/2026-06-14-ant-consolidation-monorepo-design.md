# ANT Consolidation Monorepo — Design

- **Date:** 2026-06-14
- **Owner:** Chris Birkbeck (GitHub `CBirkbeck`)
- **Status:** Approved design → implementation gated on Phase 0 (user-handled bumps)
- **Repo:** repurpose `CBirkbeck/AINTLIB` (private). Current blueprint atlas moves to a branch.

---

## 1. Summary

Repurpose `AINTLIB`'s `main` into a **consolidation monorepo**: one buildable Lean workspace
that **vendors seven of the maintainer's number-theory projects onto a single mathlib (latest,
`v4.31.0-rc2`)**. On this unified, building codebase, agents **deduplicate and clean up**
overlapping work. New work flows **in** from the origin repos (which act as development
branches): a finished unit is handed over by merging it to the origin's `ready` branch, the
only thing the monorepo syncs; **landing it auto-fires the cleanup/dedup agents** on the changed
modules. Cleaned results flow **out** as PRs to the origin repos or to mathlib. Crucially,
because every origin now shares one mathlib, the monorepo publishes its cleaned `Common/` as a
**Lake-requireable package**, so workers on one project can **reuse results another project (or
mathlib) already proved instead of re-deriving them**. The existing blueprint atlas is preserved
on a `blueprint-atlas` branch and its public site stays live.

## 2. Goals / Non-goals

**Goals**
- One place where all of this NT work lives, builds together, and can be cleaned/deduplicated.
- **Cross-project reuse:** a worker on any project can use results from mathlib *or* from any
  other project — no re-deriving what already exists. This is a first-class goal.
- Origin repos behave as development branches feeding the monorepo when a unit of work completes;
  ongoing WIP keeps moving on feature branches, untouched.
- **Auto-cleanup:** consolidated work is cleaned/deduplicated automatically as it lands, not in a
  separate manual pass.
- A path to upstream cleaned results as PRs back to the origin repos / mathlib.

**Non-goals**
- Not a blueprint (that's the preserved `blueprint-atlas` branch).
- Not an attempt to combine incompatible mathlib versions (Phase 0 imposes one version first).
- Not (initially) a merged single namespace — projects are vendored side-by-side and
  deduplicated *gradually*.

## 3. Scope — 7 repos

| Project | origin repo | work branch (current) |
|---|---|---|
| flt-regular-bernoulli | CBirkbeck/flt-regular-bernoulli | master (+ 3 feature branches) |
| LeanModularForms | CBirkbeck/LeanModularForms | spread across 11 branches |
| Hasse-Weil | CBirkbeck/Hasse-Weil | worker-tensor-isom |
| Nagell–Lutz | CBirkbeck/LutzNagell | main |
| padic-L-functions | CBirkbeck/padic-L-functions | (default) |
| Adic spaces | CBirkbeck/Adic-Spaces | main |
| chebotarev-density | CBirkbeck/chebotarev-density | development |

Explicitly **out of scope for now:** power_residue_symbols, NewtonPoly, ModFormDims,
DirichletNonvanishing, GLn_F_q, LocalClassFieldTheory, and the Lean-3/abandoned repos.

## 4. Phase 0 — one mathlib (precondition, USER-handled)

Bring all 7 repos to **`leanprover/lean4:v4.31.0-rc2`** (latest mathlib master) BEFORE the
monorepo work begins. The maintainer is handling this. Current state and required bump:

- `v4.29.x` (heaviest): **Hasse-Weil**, **Nagell–Lutz**, **Adic spaces**.
- `v4.30.x` (one minor): **flt-regular-bernoulli**, **LeanModularForms**.
- `v4.31.0-rc1` (trivial): **chebotarev-density**, **padic-L-functions**.

The hard part is the **multi-branch repos** — **LeanModularForms (11 branches)** and
**flt-regular-bernoulli (master + 3)** — whose work must first be **merged into one canonical
branch** per repo, then bumped. This needs maintainer input on which branches are canonical
vs. droppable (archives, `broken-phase6-7`, `valence_tests`, etc.). Implementation (Phases 1–4)
is **gated** on this phase completing: each origin repo must build clean on `v4.31.0-rc2` with a
single designated `ready` branch holding its consolidated work.

## 5. Architecture — vendored Lake workspace

```
AINTLIB/                       main branch, lean-toolchain v4.31.0-rc2
  lakefile.toml                one workspace requiring mathlib (latest); each project a lean_lib
  projects/
    FltRegularBernoulli/
    LeanModularForms/
    HasseWeil/
    NagellLutz/
    PadicLFunctions/
    AdicSpaces/
    Chebotarev/
  Common/                      shared lemmas refactored out of the projects during dedup;
                               ALSO published as a standalone requireable package (see §7)
  sources/manifest.toml        per project: origin repo, `ready` branch, last-synced commit
  scripts/
    sync.sh                    pull a project's latest `ready` work into projects/<P>/;
                               on change, auto-fire the cleanup agents (§8)
    cleanup.sh                 dispatch the dedup/cleanup agents over a project's changed modules
    pr-back.sh                 push a cleaned module back to its origin (or a mathlib fork) as a PR
```

Everything builds together against the one mathlib. Each project keeps its own Lean namespace
initially; deduplication migrates genuinely-shared content into `Common/` and rewires consumers.
The vendored source is plain copied-in Lean (not a submodule), so the workspace is a single
unified build.

**`Common/` is dual-purpose:** inside the workspace it is a `lean_lib` the vendored projects
depend on; it is *also* published (as a tagged package on this same mathlib) so the **origin
repos can `require` it** and consume shared results on the development side. This is the
mechanism that makes cross-project reuse real, and it only works because Phase 0 pins everything
to one mathlib. There is no dependency cycle: `Common` holds refactored-out shared lemmas and
never vendors project-specific code, so the edge is strictly origins → `Common`.

## 6. Feeding mechanism — origins as dev branches → monorepo

Origin repos remain where new work happens. Each origin designates a **`ready` branch**: messy
WIP lives on feature branches and is left alone; when a unit of work is finished, the worker
**merges it to `ready`**. The monorepo only ever syncs from `ready`, so the repo keeps moving
while completed units get consolidated — the answer to "clean up what's done without freezing
ongoing work."

`scripts/sync.sh <project>` fetches the origin's `ready` branch (already on the shared mathlib by
the Phase-0 precondition), refreshes `projects/<P>/` from its Lean source, records the synced
commit in `sources/manifest.toml`, and — if anything changed — **auto-fires the cleanup agents**
(§8) over the changed modules.

**Trigger — manual now, push-triggered later (chosen).** Build `sync.sh` + auto-cleanup +
`pr-back.sh` first; the maintainer runs `sync.sh <project>` when a repo lands work on `ready`.
Once the pipeline is proven, add a per-origin CI workflow that fires a `repository_dispatch` to
the monorepo on merge-to-`ready`, so the same `sync.sh` entrypoint runs automatically. The
manual entrypoint is deliberately the thing CI will later call, so the upgrade is a wiring change,
not a rewrite.

Approaches weighed for the vendoring itself:
- **(a) sync-script + vendored copy — chosen.** Simple, full control, and it works precisely
  *because* all origins share one mathlib.
- (b) git subtree per project — preserves history but adds push/pull friction, and dedup that
  moves code across subtrees breaks the subtree mapping.
- (c) git submodules — **rejected**: each submodule would carry its own mathlib, defeating the
  unified build.

## 7. Contributor protocol — instructions for origin/dev-branch workers

Workers on the origin repos are given this protocol. Its purpose is the cross-project-reuse goal:
**hunt for what already exists; reuse it; don't re-derive.**

**Before proving any nontrivial result, search — in this order:**
1. **mathlib.** Use `exact?`/`apply?`/`rw?`, `loogle`, and leansearch/moogle. mathlib is already a
   dependency, so anything found is immediately usable. Re-proving a mathlib lemma is the single
   most common waste.
2. **the monorepo.** It is the index of all our NT work on this mathlib. Check whether `Common/`
   or another project already has the result (grep the vendored tree / ask the consolidation
   maintainer).

**Then reuse rather than re-derive:**
- Found in **mathlib** → use it directly.
- Found in the monorepo's **`Common`** → `require` the published `Common` package and use it
  (origins are on the same mathlib, so this just works).
- Found in **another project but not yet promoted to `Common`** → flag it for promotion. Until
  it lands in `Common`, either depend on it once promoted or temporarily copy the cleaned
  statement with a `-- TODO: reuse <Common.Lemma> once promoted` note. Don't silently re-prove it.

**Division of labor (so workers aren't blocked on polish):**
- Workers produce **correct, complete** results and merge finished units to `ready`. They do
  **not** need to pre-clean for mathlib style or hunt down every dedup — the monorepo's
  auto-cleanup (§8) handles dedup, style, and PR-back.
- WIP stays on feature branches; only `ready` is consumed by the monorepo.

This is the inversion of the old "don't bother checking whether a lemma exists" guidance: checking
first *is* the job, because reuse across mathlib and across projects is the point of the monorepo.

## 8. Cleanup & deduplication (auto-fired)

Cleanup is **automatic**, not a separate manual phase. When `sync.sh` lands changed modules, it
dispatches the cleanup agents over exactly what changed (`scripts/cleanup.sh <project>`):
they find duplicated/overlapping results across projects (e.g. shared cyclotomic, modular-forms,
valuation lemmas), refactor genuinely-shared ones into `Common/`, rewire consumers, discharge
`sorry`s, and apply mathlib style. This is where `/beastmode`, `/cleanup`, and the mathlib-quality
agents run — on code that actually compiles together, which is what makes cross-project dedup
possible. Promotions into `Common/` are what later become consumable by the origin workers (§7).

## 9. PR-back — monorepo → origin / mathlib

Cleaned results flow upstream: `scripts/pr-back.sh <project> <module>` prepares the cleaned
content as a branch on the origin repo (or a mathlib fork) and opens a PR; the manifest tracks
which results have been upstreamed and to where.

## 10. Preserving the blueprint

The current AINTLIB blueprint atlas moves to a **`blueprint-atlas` branch** (pushed), so it is
preserved and still renders/deploys; the public `AINTLIB-blueprint` site stays live (it is
decoupled — built HTML in a separate repo). Optionally, later, the blueprint can be regenerated
*from* the consolidated monorepo so it tracks the cleaned code.

## 11. Phasing

- **Phase 0 — one mathlib (USER):** bump + branch-consolidate all 7 repos to `v4.31.0-rc2`, each
  with a single `ready` branch. *(Gate: each origin builds clean on its `ready` branch.)*
- **Phase 1 — repurpose + scaffold:** move blueprint → `blueprint-atlas` branch; on `main`,
  scaffold the workspace lakefile (latest mathlib), `Common/` (incl. its publishable package
  config), `sources/manifest.toml`, `scripts/sync.sh`, `scripts/cleanup.sh`, `scripts/pr-back.sh`,
  and the written **contributor protocol** (§7) for the origin repos.
- **Phase 2 — vendor + build:** sync the 7 projects into `projects/`; get the whole workspace
  building together on the one mathlib.
- **Phase 3 — auto-cleanup wiring + first dedup:** wire `sync.sh` to auto-fire `cleanup.sh`;
  run the first dedup pass — refactor shared results into `Common/`, discharge sorries, style;
  publish `Common` so an origin can `require` it.
- **Phase 4 — PR-back + feeding automation:** `scripts/pr-back.sh` + first upstream PRs; then add
  the per-origin push-trigger CI (`repository_dispatch` on merge-to-`ready`).

## 12. Open items (carry into planning)

- **LeanModularForms branch consolidation:** which of the 11 branches are canonical vs. droppable;
  how to merge them into one `ready` branch (needs maintainer input during Phase 0).
- **flt-regular-bernoulli:** reconcile `master` with its 3 feature branches into one `ready` branch.
- Naming/namespace convention for `projects/<P>/` and for `Common/`.

## 13. Success criteria

- `AINTLIB` `main` builds a single Lake workspace on `v4.31.0-rc2` vendoring all 7 projects.
- A `sync.sh` run refreshes a project from its origin's `ready` branch, **auto-fires cleanup**, and
  the workspace still builds.
- Genuinely-shared lemmas live once, in `Common/`, with consumers rewired.
- `Common` is published such that an origin repo can `require` it and a worker reuses a lemma from
  another project instead of re-proving it (cross-project reuse demonstrated end-to-end).
- At least one cleaned result PR'd back to an origin repo (or mathlib) via `pr-back.sh`.
- The blueprint atlas is preserved on `blueprint-atlas` and the public site remains live.
