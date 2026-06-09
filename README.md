# AINTLIB — An Atlas of Number Theory in Lean

A single [Verso blueprint](https://github.com/leanprover/verso-blueprint) mapping the
**main (Wikipedia-level) results of number theory as formalised in Lean** — across
**mathlib**, the maintainer's local number-theory projects, and external projects
(PNT+, Imperial FLT, …) — into one interactive, cross-project **dependency graph** with
human-readable *unformalised* statements and paragraph-level proof sketches.

## 🔗 Live blueprint

**https://cbirkbeck.github.io/AINTLIB-blueprint/**

(Public site; this source repo is private.)

## Status

- **Phase 0 — Discovery & sync:** ✅ all source repos pulled/cloned, GitHub/web discovery, mathlib NT PRs snapshotted, source catalogue.
- **Phase 1 — Scaffold:** ✅ Lean project on mathlib, verso-blueprint building & rendering, 10-chapter skeleton.
- **Phase 2 — mathlib core:** ✅ the mathlib number-theory backbone, sorry-free status auto-tracked.
- **Phase 3 — Repos as linked chapters:** ✅ 22 external projects folded in (chebotarev density, flt-regular + bernoulli, Imperial FLT, Kummer criterion, LeanModularForms Hecke ring, LocalClassFieldTheory, Buzzard CFT, PNT+, DirichletNonvanishing, adic spaces, Hasse–Weil, Nagell–Lutz, pfr, …) — **all branches vetted; only repos with substantive Lean content included.**
- **Phase 4 — Frontier & polish:** ✅ forthcoming-in-mathlib PR nodes, connected dependency graph, overview map.

**Current size: 256 nodes · 432 dependency edges · 10 chapters** — mathlib core (146) + 22 external projects + 22 forthcoming-mathlib results, 249 in one connected component.

## The atlas model

The source repos span Lean v4.7 → v4.31 and cannot all compile together, so AINTLIB is an
**atlas**, not a unified build:

- The **mathlib number-theory core is live-built** (this project depends on one mathlib), so
  every `(lean := "Mathlib.NumberTheory.…")` reference is auto-tracked sorry-free.
- Each **other repo is a linked chapter**: nodes reference its declarations by name and link
  out to the repo (and its own blueprint), woven into the same dependency graph.

## Chapters

Elementary · Analytic · Algebraic · Class Field Theory & Galois · p-adic & Adic Spaces ·
Modular & Automorphic Forms · Elliptic Curves & Arithmetic Geometry · Fermat's Last Theorem
& Regular Primes · Diophantine & Transcendence · Additive & Combinatorial.

## Build & render

```bash
lake exe cache get          # fetch mathlib oleans
./scripts/ci-pages.sh       # build + render → _out/site/html-multi/
python3 -m http.server -d _out/site/html-multi/   # preview locally
```

Pinned: Lean **v4.30.0-rc2**, mathlib **@229580e**, VersoBlueprint **@v4.30.0** (a proven
verso-blueprint ↔ mathlib pairing).

## Layout

- `AINTLIB/Chapters/*.lean` — the blueprint chapters (Verso directives).
- `AINTLIB/Blueprint.lean` — assembles chapters + dependency graph + progress summary.
- `AINTLIB/Core.lean` — imports the cited mathlib modules so references resolve.
- `sources/manifest.toml` — every source repo (URL @ commit, Lean version, chapters).
- `sources/catalogue.md` — source decisions; `sources/mathlib-nt-prs.json` — the frontier.
- `docs/superpowers/specs/` + `docs/superpowers/plans/` — design & implementation plan.

Built with [Claude Code](https://claude.com/claude-code).
