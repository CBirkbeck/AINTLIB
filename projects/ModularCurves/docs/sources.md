# Sources — Modular Curves

A living bibliography for planning the modular-curves formalisation. Add, reorder, and
annotate freely — the entries below are **suggested starting points**, not a fixed list.

**How to use this file**
- Group a source under the heading it fits; note *what we want from it* (which chapters map
  to which formalisation targets), and a rough priority `[P0]…[P2]`.
- **Local PDFs are never committed.** Drop them in `refs/ModularCurves/` (gitignored) and
  reference them here by title. See `docs/README.md`.
- Prefer sources that give *constructions we can follow line by line* over surveys.

---

## 1. Core theory — analytic & algebraic (start here)

- **Diamond & Shurman, _A First Course in Modular Forms_ (GTM 228).** `[P0]`
  The canonical modern reference. Ch. 2 builds `X(Γ)` as a compact Riemann surface; Ch. 3
  gives the moduli interpretation and the curves `X₀(N)`, `X₁(N)`, `X(N)`. This is the main
  spine for the analytic construction.
- **Milne, _Modular Functions and Modular Forms_ (online notes, free).** `[P0]`
  Careful, self-contained construction of the curves as Riemann surfaces *and* as algebraic
  curves. Excellent for the compactification + cusps and for the analytic→algebraic bridge.
- **Shimura, _Introduction to the Arithmetic Theory of Automorphic Functions_.** `[P1]`
  Canonical models, Hecke correspondences, the arithmetic of the curves.
- **Serre, _A Course in Arithmetic_, Ch. VII.** `[P1]`
  `SL₂(ℤ)`, the fundamental domain, modular forms — background/warm-up, mostly in mathlib.

## 2. Moduli & arithmetic-geometric foundations (the scheme-theoretic direction)

- **Katz & Mazur, _Arithmetic Moduli of Elliptic Curves_ (Ann. of Math. Studies 108).** `[P1]`
  Modular curves as moduli of elliptic curves with level structure; integral models.
- **Deligne & Rapoport, _Les schémas de modules de courbes elliptiques_ (LNM 349).** `[P2]`
  Foundational integral models, cusps, generalized elliptic curves, the Tate curve.
- **B. Conrad, notes on _Arithmetic moduli of generalized elliptic curves_.** `[P2]`
  Modern exposition of DR/KM; useful when we reach the moduli-stack formulation.
- **The Stacks Project (online).** `[P2]`
  Algebraic-geometry / moduli foundations to cite as needed.

## 3. Level structure, cusps, dimension formulas

- **Diamond & Shurman, Ch. 1–3** (widths of cusps, genus, dimension formulas).
- **Stein, _Modular Forms: A Computational Approach_ (free).** `[P1]`
  Concrete formulas for cusps, indices, and dimensions — good for cross-checking statements.

## 4. Surveys / orientation (free, good for scoping)

- **Bruinier–van der Geer–Harder–Zagier, _The 1-2-3 of Modular Forms_.**
- Course notes: Milne (above), Darmon, Snowden — for filling specific gaps.

## 5. Existing Lean / mathlib infrastructure — **reuse first, do not re-prove**

Per AINTLIB's cardinal rule, search these before proving anything. `grep -r`, `exact?`,
`apply?`, and `import` from any project in the workspace.

**mathlib**
- `Mathlib.Analysis.Complex.UpperHalfPlane.*` — `ℍ`, the `GL₂⁺(ℝ)` / `SL₂(ℝ)` Möbius action,
  topology, metric, manifold structure (`Basic`, `Topology`, `Metric`, `Manifold`, `MoebiusAction`).
- `Mathlib.NumberTheory.Modular` — the `SL(2, ℤ)` action and its standard fundamental domain.
- `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups` — `Γ(N)`, `Γ₀(N)`, `Γ₁(N)`.
- `Mathlib.NumberTheory.ModularForms.*` — `SlashActions`, `SlashInvariantForms`, `Basic`
  (`ModularForm` / `CuspForm`), `Cusps`, `EisensteinSeries`, `QExpansion`, `Petersson`,
  `DimensionFormulas`, `LevelOne`.
- Algebraic-curve / moduli direction (later): `Mathlib.AlgebraicGeometry.*`,
  `Mathlib.Geometry.RingedSpace.*`, `Mathlib.Geometry.Manifold.*` (Riemann-surface structure).

**In-repo (AINTLIB) — `import` directly, this is the whole point of the monorepo**
- `projects/LeanModularForms/` — modular & cusp forms, slash actions, PSL₂ action, cusps,
  valence formula, dimension formulas, Petersson inner product. Closest existing project.
- `projects/HasseWeil/` — elliptic curves, `Pic⁰`, isogenies, torsion — for the
  moduli-of-elliptic-curves side.

## 6. Related AINTLIB dev branches — cross-link, don't duplicate

- `dev/leanmodularforms` → `projects/LeanModularForms/`
- `dev/hasse-weil` → `projects/HasseWeil/`
- `dev/modular-commensurable` — commensurability of subgroups; check before touching
  Hecke / correspondence material.

---

## 7. To add (your sources)

<!-- Chris: drop titles/links here; move them up into the sections above as they firm up. -->
-
-
-
