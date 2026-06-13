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
overlapping work; new work flows **in** from the origin repos (which act as development
branches), and cleaned results flow **out** as PRs to the origin repos or to mathlib. The
existing blueprint atlas is preserved on a `blueprint-atlas` branch and its public site stays
live.

## 2. Goals / Non-goals

**Goals**
- One place where all of this NT work lives, builds together, and can be cleaned/deduplicated.
- Origin repos behave as development branches feeding the monorepo after work completes.
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
single designated branch holding its consolidated work.

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
  Common/                      shared lemmas refactored out of the projects during dedup
  sources/manifest.toml        per project: origin repo, designated branch, last-synced commit
  scripts/
    sync.sh                    pull a project's latest origin work into projects/<P>/
    pr-back.sh                 push a cleaned module back to its origin (or a mathlib fork) as a PR
```

Everything builds together against the one mathlib. Each project keeps its own Lean namespace
initially; deduplication migrates genuinely-shared content into `Common/` and rewires consumers.
The vendored source is plain copied-in Lean (not a submodule), so the workspace is a single
unified build.

## 6. Feeding mechanism — origins as dev branches → monorepo

Origin repos remain where new work happens. New work lands in the monorepo via
`scripts/sync.sh <project>`: it fetches the origin's **designated branch** (already on the shared
mathlib by the Phase-0 precondition), refreshes `projects/<P>/` from its Lean source, and records
the synced commit in `sources/manifest.toml`. Run on demand (or when origin work completes).

Approaches weighed:
- **(a) sync-script + vendored copy — chosen.** Simple, full control, and it works precisely
  *because* all origins share one mathlib.
- (b) git subtree per project — preserves history but adds push/pull friction, and dedup that
  moves code across subtrees breaks the subtree mapping.
- (c) git submodules — **rejected**: each submodule would carry its own mathlib, defeating the
  unified build.

Optional later automation: a GitHub Action in each origin repo that fires a `repository_dispatch`
to the monorepo on completion to run the sync and open a PR. Start manual.

## 7. Cleanup & deduplication

Agents operate on the unified, building codebase: find duplicated/overlapping results across
projects (e.g. shared cyclotomic, modular-forms, valuation lemmas), refactor them into `Common/`,
discharge `sorry`s, and apply mathlib style. This is where `/beastmode`, `/cleanup`, and the
mathlib-quality agents run — on code that actually compiles together, which is what makes
cross-project dedup possible.

## 8. PR-back — monorepo → origin / mathlib

Cleaned results flow upstream: `scripts/pr-back.sh <project> <module>` prepares the cleaned
content as a branch on the origin repo (or a mathlib fork) and opens a PR; the manifest tracks
which results have been upstreamed and to where.

## 9. Preserving the blueprint

The current AINTLIB blueprint atlas moves to a **`blueprint-atlas` branch** (pushed), so it is
preserved and still renders/deploys; the public `AINTLIB-blueprint` site stays live (it is
decoupled — built HTML in a separate repo). Optionally, later, the blueprint can be regenerated
*from* the consolidated monorepo so it tracks the cleaned code.

## 10. Phasing

- **Phase 0 — one mathlib (USER):** bump + branch-consolidate all 7 repos to `v4.31.0-rc2`.
  *(Gate: each origin builds clean on a single designated branch.)*
- **Phase 1 — repurpose + scaffold:** move blueprint → `blueprint-atlas` branch; on `main`,
  scaffold the workspace lakefile (latest mathlib), `sources/manifest.toml`, `scripts/sync.sh`.
- **Phase 2 — vendor + build:** sync the 7 projects into `projects/`; get the whole workspace
  building together on the one mathlib.
- **Phase 3 — dedup/cleanup:** refactor shared results into `Common/`, discharge sorries, style.
- **Phase 4 — PR-back:** `scripts/pr-back.sh` + first upstream PRs; optional CI feeding automation.

## 11. Open items (carry into planning)

- **LeanModularForms branch consolidation:** which of the 11 branches are canonical vs. droppable;
  how to merge them (needs maintainer input during Phase 0).
- **flt-regular-bernoulli:** reconcile `master` with its 3 feature branches.
- Naming/namespace convention for `projects/<P>/` and for `Common/`.
- Whether/when to automate the origin→monorepo feeding via CI.

## 12. Success criteria

- `AINTLIB` `main` builds a single Lake workspace on `v4.31.0-rc2` vendoring all 7 projects.
- A `sync.sh` run refreshes a project from its origin's designated branch and the workspace still builds.
- Genuinely-shared lemmas live once, in `Common/`, with consumers rewired.
- At least one cleaned result PR'd back to an origin repo (or mathlib) via `pr-back.sh`.
- The blueprint atlas is preserved on `blueprint-atlas` and the public site remains live.
