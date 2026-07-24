# Development Plan — Campaign 5: the adic Fargues–Fontaine curve (definition layer)

**Status: APPROVED by the owner 2026-07-24** (planned by `/develop`; scope decisions
D1/D2 confirmed: E = Q_p, F any perfectoid field of char p). Campaign-4 (FJP) triple
archived as `*-fjp-archived-2026-07-24.md`; this file, `tickets.md`, and
`decomposition.md` are the canonical Campaign-5 documents. Workers start via
`/beastmode` (first available ticket: T101).

## Goal

Formalise **Definition 2.1.1 of [BFHHLWY]** (arXiv:1705.00710 — the owner's paper) at
`E = Q_p`: for `F` a perfectoid field of characteristic `p` with pseudo-uniformizer `ϖ`,

```lean
-- the ring (M1–M2)
Ainf p F := WittVector p (OF F)                  -- (p,[ϖ])-adic complete Huber ring
-- the space (M4)
Y p F ϖ := {v ∈ Spa (Ainf p F) (ringPlus _) | ¬ v.vle (p * teichPi p F ϖ) 0}
-- the curve (M5)
Curve p F ϖ := Quotient (MulAction.orbitRel (Multiplicative ℤ) ↥(Y p F ϖ))
```

with the full point-set well-definedness package (the content of "it makes sense to
form the quotient" in the sources): the window covering, `φ`-translation and
disjointness, **freeness**, **wandering/proper discontinuity**, **open quotient map**,
**chart injectivity** (`U_0`, `V_0` embed homeomorphically), **two-chart covering of
𝒳**, **T0**, **quasicompactness**. Headline sorry-free targets, in priority order:

1. `isAdicComplete_Iinf` (+ `instIsHuberRingAinf`, `isAffinoidRing_Ainf`) — A_inf layer;
2. `smul_ne_of_ne_zero` + `exists_nhd_smul_disjoint` — free + properly discontinuous;
3. `isOpenQuotientMap_toCurve` + `injOn_toCurve_windowU/V` + `curve_eq_image_window_zero`
   — the quotient is honest, with Kedlaya's two charts;
4. `instT0SpaceCurve`, `instCompactSpaceCurve` (the latter descopable per RR2);
5. STRETCH: `Y_nonempty` (Gauss-norm point; own sub-decomposition later).

**Not in scope (follow-on campaign, mirroring the paper's own split into Def 2.1.1 vs
Prop 2.1.2):** the structure (pre)sheaf on `Curve`, sheafiness, "Noetherian adic space"
(Kedlaya [Ked16]), untilts/classical points, vector bundles, general `E` (needs ramified
Witt vectors — absent from mathlib).

## References (all local under `refs/AdicSpaces/`, never committed)

- [BFHHLWY] `1705.00710-BFHHLWY-extensions-ff-curve.pdf` — **Def 2.1.1 p. 6** (primary).
- [Ked-AWS] `kedlaya-aws-sheaves-stacks-shtukas.pdf` — §3.1, esp. **Rem. 3.1.9**
  (the U_n/V_n covering: the campaign's proof skeleton).
- [SW] `scholze-weinstein-berkeley-lectures.pdf` — §12.2, §13.1, Def 13.5.1.
- [Bhatt] `bhatt-679-perfectoid-lectures.pdf` — §3.1–3.2 (O_F-level facts).
- [KL15] `kedlaya-liu-relative-padic-hodge-1301.0792.pdf` — §8.7 (corroboration only).
- [FF] `fargues-fontaine-courbe.pdf` — reserved for the stretch (Gauss norms §1.4).
- [Ked16] `kedlaya-noetherian-ff-curves-1602.06899.pdf` — reserved for the follow-on.

Full verbatim quotes per leaf: `decomposition.md`.

## Mathlib inventory

| Concept | Status | Action |
|---|---|---|
| p-typical Witt vectors, Teichmüller (MonoidHom) | `Mathlib.RingTheory.WittVector.*` | USE |
| Frobenius as ring equiv on perfect coefficients | `WittVector.frobeniusEquiv` | USE |
| `W(k)` p-adically complete, k perfect | `WittVector.isAdicCompleteIdealSpanP` (Complete.lean) | USE (p-direction of M2) |
| Teichmüller-coefficient formulas | `WittVector.TeichmullerSeries` | USE (M2 coordinatewise step) |
| Adic topology + basis + nonarchimedean | `Ideal.adicTopology`, `isAdic_iff` | USE |
| Orbit quotients are open quotient maps | `MulAction.isOpenQuotientMap_quotientMk` (ConstMulAction.lean:574) | USE |
| Action by ring automorphisms | `MulSemiringAction.compHom` + `zpowersHom` | USE |
| Ramified Witt vectors `W_{E°}(-)` | absent | DEFER (general-E campaign) |
| Topology instance on `WittVector` | absent | DEFINE (M2; the (p,[ϖ])-adic instance) |
| Perfectoid fields, pseudo-uniformizers, Spv/Spa/rational subsets, Spa-compactness, group actions on Spa | project (`PerfectoidRing`, `PseudoUniformizer`, `ValuationSpectrum`, `AdicSpectrum`, `RationalSubsets`, `SpaCompact`, `ValuationAction`) | USE (one edit: drop unused `[Finite G]`, done) |

## File structure (new folder `Adic spaces/FarguesFontaine/`; legacy single file deleted — see decomposition §5)

- `PerfectoidFieldCharP.lean` — M1: `OF`, `toOF`, perfectness, ϖ-adic completeness of O_F.
- `AinfHuber.lean` — M2: `Ainf`, `teichPi`, `Iinf`, topology/Huber/A⁺=⊤ instances,
  **(p,[ϖ])-adic completeness** (campaign summit #1).
- `FrobeniusAction.lean` — M3: `frob`, continuity both ways, the `Multiplicative ℤ`
  `MulSemiringAction`, action on Spa.
- `YSpace.lean` — M4: `Y`, element facts, `KGE`/`KLE`, windows, covering/translation/
  disjointness/openness (campaign summit #2).
- `Curve.lean` — M5: freeness, wandering, `Curve`, quotient theorems, T0, qc, stretch
  nonemptiness.

## Dependency graph (milestones)

```
M1 (O_F facts) ──→ M2 (A_inf Huber+complete) ──→ M3 (φ-action) ──→ M4 (Y + windows) ──→ M5 (Curve)
                         └──────────────── M2 completeness feeds nothing in M4/M5 directly:
                                            M4–M5 need only the INSTANCES (topology/Huber/A⁺)
                                            and M3 — so M4/M5 tickets can run in parallel with
                                            the M2 completeness summit after M2's instance layer.
```

Parallel capacity ≈ 3 workers at peak (M2-summit ∥ M4-windows ∥ M5-after-M4-partial).

## Generality decisions

- `E = Q_p` only (D1); `F` any perfectoid field of char p, **not** nec. alg. closed
  (D2 — maximal generality; the sources' construction needs only Tate+perfectoid);
  windows via integer-cleared `KGE/KLE` predicates, no real-valued κ (D4); action
  convention `g • v = v ∘ φ^{-g}` shifting windows down (D5); ϖ-independence as set
  equality `Y_indep` only (D6). Full statements + justifications: decomposition §0.2.
- `vlt`, `KGE`, `KLE` are deliberately element-level (`v.vle` on ring elements) — rank-
  free, no value-group extraction in statements.

## Known risks

RR1 (M2 completeness fine structure — sources one-line; our coefficientwise expansion,
with an inverse-limit fallback), RR2 (window quasicompactness discharge — two candidate
routes, descope instruction embedded), RR3 (external gpt-5.6-sol review undelivered —
Codex infra down 2026-07-24; packet saved at
`chatgpt-packet-fargues-fontaine-plan-2026-07-24.md`; re-run before M2). Details:
decomposition §6.

## Campaign hygiene

- Cleanup cadence per §1g of `/develop` (tickets embed CLEANUP-* every 3 proof tickets
  per file, final per-file cleanups, CLEANUP-ALL before the M5 milestone, CLEANUP-FINAL).
- The bar per ticket: `lake build` green, zero new `sorry` outside the skeleton's own
  contract, `#print axioms` ∈ {propext, Classical.choice, Quot.sound}.
- Workers: `/beastmode` per ticket; statements frozen (B2-stop on statement bugs).
