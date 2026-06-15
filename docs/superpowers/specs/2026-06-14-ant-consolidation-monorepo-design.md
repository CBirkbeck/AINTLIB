# ANT Consolidation Monorepo — Design

- **Date:** 2026-06-14 (updated 2026-06-15: work-in-the-monorepo pivot)
- **Owner:** Chris Birkbeck (GitHub `CBirkbeck`)
- **Status:** Approved; implementation underway (7 projects vendored, first build running)
- **Repo:** `CBirkbeck/AINTLIB` (private). `main` = the monorepo; blueprint atlas on `blueprint-atlas`.

---

## 1. Summary

The monorepo is **one buildable Lean workspace on a single mathlib** that vendors seven of the
maintainer's number-theory projects side by side. It is the **primary workspace**: all work
happens *here*, in git worktrees of the monorepo, so every worker can see and reuse every other
project's results **immediately** — one build unit, no promotion gate, no cross-package cycles.
Parallel workers are driven by the maintainer's coordinator + ticket system. Cleaned results flow
**out** as PRs to the origin repos or to mathlib. The origin repos are the initial source (vendored
in once) and the downstream PR targets — they are no longer where day-to-day work happens. The
blueprint atlas is preserved on the `blueprint-atlas` branch and its public site stays live.

## 2. Goals / Non-goals

**Goals**
- One place where all this NT work lives, builds together, and is cleaned/deduplicated.
- **Maximum cross-project reuse, immediately:** any worker can `import` any project's results as
  they go (it's one build unit). No "wait until the monorepo has promoted the shared thing."
- Parallel work via monorepo worktrees, coordinated by the maintainer's ticket system.
- A path to upstream cleaned results as PRs back to the origin repos / mathlib.

**Non-goals**
- Not a blueprint (that's the preserved `blueprint-atlas` branch).
- Not combining incompatible mathlib versions (one pinned mathlib; we fix bump breakage here).
- **Not** separate, mutually-depending packages: Lake forbids dependency cycles and a repo can't
  depend on a monorepo that contains a copy of itself — which is exactly *why* it's one workspace.
- Not (initially) a merged namespace — projects are vendored side by side and deduped gradually.

## 3. Scope — 7 repos (canonical branch → vendored)

| Project | origin repo | canonical branch | mathlib state |
|---|---|---|---|
| flt-regular-bernoulli | CBirkbeck/flt-regular-bernoulli | `master` | rc2 `1680840` → pin |
| LeanModularForms | CBirkbeck/LeanModularForms | `master` | rc2 `d90090f` ✓ |
| Hasse-Weil | CBirkbeck/Hasse-Weil | `silverman-development` | rc2 `d90090f` ✓ |
| Adic spaces | CBirkbeck/Adic-Spaces | `faithful-LL-pairfree` | rc2 `d90090f` ✓ |
| Nagell–Lutz | CBirkbeck/LutzNagell | `main` | **v4.29 → bump here** |
| padic-L-functions | CBirkbeck/padic-L-functions | `main` | rc1 `66748b` → bump |
| chebotarev-density | CBirkbeck/chebotarev-density | `development` | rc1 `66748b` → bump |

Out of scope for now: power_residue_symbols and the other repos previously listed.

## 4. One mathlib

Pinned to **`d90090f647ca`** (v4.31.0-rc2) — already shared by HasseWeil, LeanModularForms,
AdicSpaces. The others are bumped onto it **in the monorepo** (bump breakage fixed here, per the
maintainer's call). `BernoulliRegular` additionally needs the external **`flt-regular`** package
(it imports `FltRegular.*`); pinned `@29a3bb88f596` with mathlib required first so `d90090f` wins.

## 5. Architecture — one Lake workspace

```
AINTLIB/                       main, lean-toolchain v4.31.0-rc2
  lakefile.toml                one package: require mathlib @ d90090f (+ flt-regular); a lean_lib per project + Common
  projects/
    FltRegularBernoulli/  LeanModularForms/  HasseWeil/  AdicSpaces/
    NagellLutz/  PadicLFunctions/  Chebotarev/
  Common/                      where cleanup parks genuinely-shared lemmas (in-tree lib, not published)
  sources/manifest.toml        per project: origin repo, canonical branch, synced commit
  scripts/pr-back.sh           push a cleaned module out to its origin (or a mathlib fork) as a PR
```

All projects' modules coexist in **one build unit**, so any project `import`s any other directly —
that is what makes see-everything / reuse-anything work, and it is only possible because they share
one mathlib and one package. `Common/` is just the in-tree destination for shared lemmas found
during dedup (consumers rewired); it is **not** published or required by anyone. Vendored source is
plain copied-in Lean (not a submodule).

## 6. Where work happens — monorepo worktrees

- **All work happens in the monorepo.** Each parallel worker takes a **git worktree of the
  monorepo**, edits its project under `projects/<P>/`, and may `import` any other project's results
  immediately.
- Driven by the maintainer's **coordinator + ticket system** (designing that system is out of scope
  for this spec — the monorepo is the substrate it runs on).
- **Reuse protocol for workers:** before proving anything nontrivial, search **(1) mathlib**, then
  **(2) the monorepo** (any project + `Common`), and **reuse rather than re-derive**. Because it is
  one build unit, reuse is a direct `import` — there is no gate and nothing to "promote" first.

## 7. Cleanup & deduplication

Ticketed work in the monorepo, on code that compiles together (which is what makes cross-project
dedup possible): find duplicated/overlapping results across projects, refactor genuinely-shared
ones into `Common/`, rewire consumers, discharge `sorry`s, apply mathlib style. This is where
`/beastmode`, `/cleanup`, and the mathlib-quality agents run.

## 8. PR-back — monorepo → origin / mathlib

`scripts/pr-back.sh <project> <module>` prepares the cleaned content as a branch on the origin repo
(or a mathlib fork) and opens a PR; the manifest tracks what has been upstreamed and to where.

## 9. Origins: initial source + transition

- **Initial:** each origin's canonical branch is vendored in once (done).
- **In-flight origin work** (the live `worktree-agent-*` branches and uncommitted changes on
  Hasse-Weil / Adic spaces / padic / …) drains into the monorepo once; after that, work shifts to
  monorepo worktrees.
- **Going forward** origins receive PRs (`pr-back.sh`); they are not edited directly.

## 10. Preserving the blueprint

The blueprint atlas is on the `blueprint-atlas` branch (preserved, still renders/deploys); the
public `AINTLIB-blueprint` site stays live (decoupled — built HTML in a separate repo). Optionally,
later, regenerate the blueprint *from* the consolidated monorepo.

## 11. Phasing

- **Phase 1 — scaffold (done):** workspace `lakefile.toml`, vendored `projects/`, toolchain rc2,
  blueprint → `blueprint-atlas`.
- **Phase 2 — build (in progress):** get the workspace building on `d90090f` — the 3 aligned
  projects + BernoulliRegular (with flt-regular) first.
- **Phase 3 — bump laggards:** Nagell–Lutz (v4.29→rc2), padic & chebotarev (rc1→rc2) onto the pin,
  fixed in the monorepo.
- **Phase 4 — cleanup/dedup + PR-back:** ticketed dedup into `Common/`; `pr-back.sh`; first
  upstream PRs.

## 12. Open items

- Namespace/convention for `projects/<P>/` and `Common/`.
- Draining in-flight origin work (worktree-agents, uncommitted) into the monorepo.
- (Resolved: LeanModularForms & flt-regular-bernoulli canonical branch = `master`; Hasse-Weil =
  `silverman-development`; mathlib pin = `d90090f`; build-in-the-monorepo for bumps.)

## 13. Success criteria

- `AINTLIB` `main` builds a single Lake workspace on `d90090f` vendoring all 7 projects.
- A worker in a monorepo worktree reuses another project's result by a direct `import` (cross-project
  reuse demonstrated, with no promotion gate).
- Genuinely-shared lemmas live once, in `Common/`, with consumers rewired.
- At least one cleaned result PR'd back to an origin repo (or mathlib) via `pr-back.sh`.
- The blueprint atlas is preserved on `blueprint-atlas` and the public site remains live.
