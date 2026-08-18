# /mathlibable report — `Chebotarev.normLeOne_frontier_lipschitz_cover`

## Verdict: **YES-add-as-is** (ship as part of the `ForMathlib/NormLeOneLipschitz.lean` block)

One-line: mathlib has the *qualitative* ideal-count asymptotic but **not** the
effective "Lipschitz parametrizable boundary" input; this theorem is exactly
Davenport/Widmer's standard codimension-1 Lipschitz cover and is genuinely missing.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoning from source.
- decl `Chebotarev.normLeOne_frontier_lipschitz_cover`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:348`
- qualified name:           `Chebotarev.normLeOne_frontier_lipschitz_cover`
  (verified: file has `namespace Chebotarev` at line 79, no inner namespace before line 348).
- kind:                      theorem
- has sorry:                 no (proof complete; reduces to
  `exists_lipschitzWith_frontierCoverFamily` + `frontier_subset_frontierCoverFamily`)
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` —
  the effective (quantitative) regularity input for the lattice-point count, after
  Gun–Ramaré–Sivaraman §3.3 / Debaene / Widmer (GTM 110 Ch. V §2).

---

### Statement (Phase 1)

`Chebotarev.normLeOne_frontier_lipschitz_cover` is a theorem stating:

> Let `K` be a number field with `r = #InfinitePlace K` infinite places. The
> topological frontier of the set `normAtAllPlaces '' (normLeOne K) ⊆ realSpace K`
> (`realSpace K = InfinitePlace K → ℝ`, the sup-metric pi type, `dim = r`) is
> **Lipschitz parametrizable of codimension 1**: there is a finite number `m`, a
> single Lipschitz constant `M : ℝ≥0`, and `m` maps `φ : Fin m → ([0,1]^{r-1} → realSpace K)`,
> each `M`-Lipschitz, whose images of the unit cube `[0,1]^{r-1}` together cover the
> frontier.

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — a number field (file-level `variable (K …)`).

Hypotheses: none (it is an unconditional existence statement).

Conclusion (math): `∂(normAtAllPlaces '' normLeOne K)` is covered by finitely many
`M`-Lipschitz images of the unit cube of dimension `r − 1`.

Conclusion (Lean):
```lean
∃ (m : ℕ) (M : ℝ≥0)
  (φ : Fin m → (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K),
  (∀ j, LipschitzWith M (φ j)) ∧
    frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1
```

This is the literal Lean transcription of Widmer's predicate "S ⊆ ℝⁿ is Lipschitz
parametrizable of codimension k": `∃ M maps φᵢ : [0,1]^{n−k} → ℝⁿ, each L-Lipschitz,
S ⊆ ⋃ᵢ φᵢ([0,1]^{n−k})`, with `n = r`, `k = 1`, `L = M`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the headline `## Main result` of the file
(`Chebotarev.normLeOne_frontier_lipschitz_cover`, module docstring line 28), it is
the named-in-the-literature result ("the Lipschitz class of the boundary of the
fundamental domain", GRS §3.3 / Davenport's principle), and it is the foundation of
a multi-result development (the `_mixedSpace` and `_index` variants build on it).

(Literature width is EXHAUSTIVE regardless; recorded for framing.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` — one-line check n/a.
Body is a genuine multi-step proof (`obtain` the cover constant, `set` the index
equiv, `rw` the iUnion reindex, close with the subset lemma).

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found                                                                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Lipschitz parametrizable boundary lattice point counting number field Lang Widmer Davenport   | yes  | Widmer's *Lipschitz class* `Lip(n,M,L)`; boundary covered by `M` `L`-Lipschitz maps `[0,1]^{n-1}→ℝⁿ` | Widmer, *Lipschitz class, narrow class, and counting lattice points*, Proc. AMS 140 (2012); GTM-110 lineage |
|  2 | WebSearch (general / definitional)| Widmer Lipschitz parametrizable boundary definition finitely many maps unit cube M-Lipschitz codimension | yes  | "S ⊂ ℝⁿ is Lipschitz parametrizable of codimension k: ∃ M maps φᵢ:[0,1]^{n−k}→ℝⁿ, L-Lipschitz, S ⊆ ⋃φᵢ([0,1]^{n−k})" | **verbatim match** to the Lean statement (codim 1: `n−1`) |
|  3 | WebSearch (named source / aliases)| counting ideals in ray classes Gun Ramaré Sivaraman Lipschitz boundary fundamental domain     | yes  | GRS "compute the Lipschitz class of the boundary of the fundamental domain F"                          | arXiv:2208.06602 = JNT 243 (2023) — the file's cited source, §3.3 |
|  4 | WebSearch (origin principle)     | Davenport lemma lattice points boundary Lipschitz image unit cube error term                  | yes  | Davenport, *On a principle of Lipschitz*, J. LMS 26 (1951): `‖Z∩ℤⁿ‖ − Vol(Z)‖ ≤ Σ hⁿ⁻ʲ Vⱼ(Z)`; Lipschitz-cover refinement (Masser–Vaaler) | the historical root; Lipschitz-image-of-cube form is the modern packaging |
|  5 | WebSearch (mathlib status)       | mathlib4 number field ideal counting asymptotics Lipschitz frontier formalization Roblot      | yes  | mathlib `Ideal/Asymptotics` has the **qualitative `Tendsto count/s → c`** only; **no** `Lip(n,M,L)` / no error term | confirms the gap (see Phase 5) |
|  6 | ChatGPT MCP                      | "standard form of the Lipschitz-parametrizable-boundary hypothesis; generality; history"      | n/a  | MCP down per task brief — substituted by extra WebSearch rows #1–#5, #10 (4+ generality levels covered) | fallback used as instructed |
|  7 | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/` and `refs/Chebotarev/`                 | n/a  | neither directory exists (checked)                                                                    | recorded n/a |
|  8 | nLab                             | "lattice point counting" / "Lipschitz parametrizable"                                          | n/a  | nLab has no entry for this analytic-NT counting principle                                              | not a category-theoretic concept |
|  9 | Stacks Project                   | —                                                                                              | n/a  | not an algebraic-geometry / scheme-theoretic statement                                                 | analytic geometry-of-numbers |
| 10 | MathOverflow / arXiv (recent)    | (from #1/#2 result sets) Barroero–Widmer, "Sharp o-minimality and lattice point counting" (arXiv:2503.01731, 2025); "On the number of quadratic polynomials with a given portrait" (arXiv:2409.18074) | yes  | both restate the **same** `Lip(n,M,L)` / "uniformly Lipschitz parametrizable of codimension k" definition | the definition is alive and standard in 2024–2025 NT |

The protocol passed: WebSearch ran ≥3 queries at distinct generality levels
(specific form #1, definitional/general #2, named source #3, origin principle #4,
formalization status #5); ChatGPT MCP recorded n/a (down) with WebSearch substitution
as the brief allows; local refs checked (absent); nLab/Stacks/MathOverflow/arXiv each
checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **Lipschitz parametrizability of the boundary, of codimension 1**
(Widmer's *Lipschitz class* `Lip(n, M, L)`); historically *Davenport's principle of
Lipschitz*; in the number-field setting "the Lipschitz class of the boundary of the
fundamental domain" (Gun–Ramaré–Sivaraman §3.3, after Debaene; also Masser–Vaaler,
Barroero–Widmer).

Sources agree on the standard form: **yes**. Across Widmer (2012), GRS (2022/2023),
Barroero–Widmer (2025) and the quadratic-portraits paper (2024) the definition is
identical: a set is covered by finitely many uniformly-Lipschitz images of `[0,1]^{n−k}`.

Most general standard form: a set `S ⊆ ℝⁿ` (or in a finite-dim normed/metric space) is
*Lipschitz parametrizable of codimension k* if `∃ M ∈ ℕ, L ≥ 0, maps φ₁…φ_M : [0,1]^{n−k} → ℝⁿ`
with each `φᵢ` `L`-Lipschitz and `S ⊆ ⋃ᵢ φᵢ([0,1]^{n−k})`. The theorem at hand is the
**`k = 1`** instance for the specific set `∂(normAtAllPlaces '' normLeOne K)` in
`ℝⁿ = realSpace K`, `n = r = #InfinitePlace K`.

Generality dimensions where the literature varies:
  - codimension `k`: ranges over `1 … n`; this result is the `k = 1` (boundary) case — the
    canonical one for counting (a codim-1 boundary gives an `O(t^{n−1})` discrepancy).
  - ambient space: `ℝⁿ` classically; the Lean form already uses the abstract pi type
    `realSpace K` with its sup metric — equivalent, slightly more idiomatic.
  - Lipschitz constant bookkeeping (`L` vs per-map `Lᵢ` then `max`): the Lean form uses a
    single common `M` (= max), matching Widmer's single-constant convention.

Disagreement with the literature: **none**. The Lean statement is the textbook predicate.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): "∂S is Lipschitz parametrizable of codim 1":
finitely many `M`-Lipschitz maps `[0,1]^{r−1} → ℝ^r` covering `∂S`.

### 4a. Generality status table

| # | Parameter / hypothesis                | Current Lean form                          | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|--------------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | `K` number field, `S = normAtAllPlaces '' normLeOne K` | the specific ideal-counting region | a *named, specific* set whose boundary one wants to cover | NO | the whole point is to certify *this* set's boundary; it is not a free parameter to generalise away |
| 2 | codimension                           | 1 (cube dim `r − 1`, ambient dim `r`)      | codim `k` general                      | NO (not for this decl) | the lattice-count consumer needs exactly codim 1; a general-`k` predicate would be a *separate* (def) contribution, not a weakening of this theorem |
| 3 | ambient space                         | `realSpace K = InfinitePlace K → ℝ` (sup metric pi) | `ℝⁿ`                          | already general | already the abstract pi type, not `Fin r → ℝ`; idiomatic |
| 4 | Lipschitz constant                    | single common `M : ℝ≥0`                    | single `L` (Widmer) or per-map then max | already standard | matches Widmer's convention exactly |
| 5 | finiteness witness                    | `∃ m : ℕ` + `φ : Fin m → …`                | `∃ M maps φ₁…φ_M`                       | already general | the `Fin m`-indexed family is the clean Lean encoding of "finitely many maps" |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** for what it asserts (a codim-1 Lipschitz
cover of one specific, named set). There is nothing to weaken: the set is the object of
interest (not an over-strong hypothesis), and the ambient space / constant / finiteness
encodings are already the idiomatic abstract ones.

Number of weakening opportunities found: **0**.

Cost of restatement: n/a (no restatement needed for generality).

Note on the bigger abstraction: one *could* first define a reusable predicate
`IsLipschitzParametrizable (k) (S)` and state this as `IsLipschitzParametrizable 1 (…)`.
That is the Phase 4c modern-idiom question, handled next — and the conclusion there is
that the predicate is a *nice-to-have follow-up*, not a blocker, because (a) mathlib does
not yet have it, (b) the inline existential is exactly the literature predicate, and (c)
the downstream consumer (`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`) already
takes the unbundled existential as its `hlip` hypothesis, so bundling now would force an
immediate unbundling at the only call site.

### 4c. Modern mathlib-idiom check — Bourbaki 2.0

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                      | no       | — | no bundled-hypothesis preamble here; `K` already a typeclass bundle |
|  2 | sequences/metric → filters/topological?                                                              | no       | — | already topological (`frontier`, `LipschitzWith`); no sequence to filter-ise |
|  3 | construct an object where a universal property would characterise it?                                | no       | — | this is a covering existence statement, not a construction with a UP |
|  4 | set-with-closure-predicate → bundled substructure?                                                   | partial  | a reusable `def IsLipschitzParametrizable (n k) (S : Set E) : Prop := ∃ m (M:ℝ≥0) φ, (∀ j, LipschitzWith M (φ j)) ∧ S ⊆ ⋃ j, φ j '' Icc (0:Fin (n−k)→ℝ) 1` | a named predicate would let the `_mixedSpace`/`_index`/lattice-count API state `hlip` uniformly, and would be the natural home for general lemmas (image under Lipschitz map, codim monotonicity). **But mathlib has neither the predicate nor any consumer of it yet** — so this is an additive future contribution, not a reason to withhold the theorem. |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                                             | no       | — | `realSpace K` pi type is already the right ambient; the result is metric-geometric, not algebraic |
|  6 | 1-categorical → higher-categorical?                                                                  | no       | — | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                     | no       | — | the cube `[0,1]^{r−1}` is intrinsic to the codim-1 counting principle |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **partial / optional** — a reusable
`IsLipschitzParametrizable` predicate would be a clean mathlib addition, but it is an
*orthogonal additive* improvement, **not** a reformulation that supersedes this theorem.

- Real improvement (if pursued): yes for the *predicate* (it would unify the `hlip`
  hypothesis across this theorem, its `_mixedSpace`/`_index` variants, and the
  lattice-count lemma), but the improvement lives in a *new def*, after which **this exact
  existential is still the theorem you prove** (just spelled `IsLipschitzParametrizable 1 …`).
- Therefore this does **not** flip the verdict to YES-but-generalise-first: there is no
  weaker/more-general *statement of this fact* to prove instead. The "generalise first"
  target would be "introduce a def", which is a separate PR and does not change what this
  theorem asserts. The honest call is YES-add-as-is, with a note recommending the predicate
  be introduced alongside (so the family of three theorems shares one `hlip` vocabulary).

### Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (introduces no definitional equality or
typeclass-search path).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.normLeOne_frontier_lipschitz_cover`

```
[A] Lean-Finder       "frontier normLeOne Lipschitz cover" / "Lipschitz parametrizable boundary"   no hits (concept absent from mathlib)
[B] Loogle            LipschitzWith _ _ ∧ frontier _ ⊆ ⋃ _, _ '' Set.Icc 0 1                         no hits (no theorem of this shape)
[C] LeanSearch        "frontier of a set is covered by finitely many Lipschitz images of a cube"     no hits
[D] Grep mathlib src  (executed) "frontier"∧"LipschitzWith" co-occurrence: Gauge.lean,
                      Normed/Module/FiniteDimension.lean, Portmanteau.lean — none is a boundary-cover.
                      "parametriz"+"lipschitz": only unrelated reparametrization comments.
                      NormLeOne.lean ends at `volume_frontier_normLeOne` (measure-zero, NOT a cover).
                      Ideal/Asymptotics.lean: only `tendsto_norm_le_div_atTop` (qualitative).         building blocks only
[E] Name pattern      lipschitz_cover / frontier_lipschitz / Lip / parametrizable                     no hits
```

Searched for both:
  - the user's current form (codim-1 cover of `∂(normAtAllPlaces '' normLeOne K)`): **not in mathlib**.
  - the literature-standard form (general `IsLipschitzParametrizable`): **not in mathlib** —
    mathlib has no Lipschitz-parametrizable-boundary predicate at all.

**Key adjacent finding (the load-bearing one).** Mathlib *does* prove ideal-counting
asymptotics — `NumberField.Ideal.tendsto_norm_le_div_atTop` (Xavier Roblot, 2025,
`Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean:149`):
`(card {I // absNorm I ≤ s}) / s → (2^r₁ (2π)^r₂ R h)/(w √|d|)`.
But its proof is **purely qualitative**: it goes through the geometry-of-numbers
`Tendsto`/equidistribution route (`ZLattice.covolume`, the fundamental-cone `volume`,
`volume_frontier_normLeOne` to get a measure-zero boundary), and produces **no error
term** and uses **no Lipschitz cover**. The entire `expMapBasis` parametrization that
mathlib *does* have in `NormLeOne.lean` is used only to compute the volume and prove the
frontier is `volume`-null — never to bound lattice-point discrepancy.

Concluded: **not in mathlib** (all five methods exhausted, plus the general literature
form). Mathlib has the *qualitative* asymptotic and the building blocks
(`volume_frontier_normLeOne`, `expMapBasis`, `LipschitzWith`, `ContDiff.locallyLipschitz`,
`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`) but **not** the effective/
quantitative "Lipschitz cover of the frontier" needed for an error term.

---

## PHASE 6 — Composition check (+ call sites)

### 6.0. Call sites — `Chebotarev.normLeOne_frontier_lipschitz_cover`

Internal use count (term-level, outside the declaring file): **0 outside-file**, but
**1 in-file downstream consumer** that is itself a `## Main result`.
External-to-file callers (by docstring reference / pipeline): 3 files
(`ZetaProduct.lean`, `IdealCongruenceCount.lean`, and within the file the `_mixedSpace`/`_index` chain).

| Caller (file:line)                                        | Usage pattern |
|-----------------------------------------------------------|---------------|
| `…/ForMathlib/NormLeOneLipschitz.lean:657` (`_index`, via `_mixedSpace`) | `obtain ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace K` — the `_mixedSpace` variant (line 626) is the direct term-level consumer; it lifts this `realSpace` cover along the fibres of `normAtAllPlaces` |
| `…/ForMathlib/IdealCongruenceCount.lean:1760, 2852`       | `obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index K` — the `_index` form is the exact `hlip` hypothesis fed to the lattice-point count |
| `…/CebotarevDensity/ZetaProduct.lean:436, 1872` (docstrings) | cited as the "Lipschitz-frontier input" of the effective ideal count |

Inline-derivation grep (was this re-derived elsewhere without using the theorem?): **none**.
There is exactly one cover, computed once, consumed by the `_mixedSpace → _index → count`
chain. Pattern = real load-bearing API (K≥1 in-project consumer, no inline re-derivation) →
**YES-* leaning**.

### 6a. Composition check

Can `normLeOne_frontier_lipschitz_cover` be derived from mathlib in ≤3 chained calls?

Attempt 1: build the cover directly from mathlib's `expMapBasis` + `volume_frontier_normLeOne`.
  - Result: **fails**. `volume_frontier_normLeOne` gives a *measure-zero* boundary; that is
    strictly weaker than (and gives no route to) a Lipschitz cover. There is no mathlib lemma
    turning "frontier of an open-map image" into "finitely many Lipschitz cube images".
Attempt 2: `frontier (f '' s) ⊆ f '' (frontier s) ∪ {…}` then face-by-face Lipschitz.
  - Result: **fails as a ≤3-call composition**. This is precisely the ~170 lines of new
    development in this file (`frontier_image_paramSet_subset`, `image_boundary_subset_faces`,
    `faceMapZero`/`faceMapSide`, the `t = exp(x_{w₀})` linearisation of the unbounded
    `w₀`-direction, `exists_lipschitzWith_comp_clampUnit`, `frontierCoverFamily`,
    `exists_lipschitzWith_frontierCoverFamily`, `frontier_subset_frontierCoverFamily`). Each
    piece uses mathlib, but the assembly is a genuine multi-lemma proof, not a chained call.

Conclusion: **NOT-COMPOSABLE**. The result is the capstone of a substantial development;
mathlib supplies the analytic atoms (`ContDiff.locallyLipschitz`,
`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`, `LipschitzWith.projIcc`,
`expMapBasis` as an `OpenPartialHomeomorph`) but not the theorem nor any ≤3-line route to it.

---

## PHASE 7 — Verdict

## Verdict: `Chebotarev.normLeOne_frontier_lipschitz_cover`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): the statement is verbatim Widmer's "Lipschitz
  parametrizable boundary of codimension 1" (`Lip(n,M,L)`), the Davenport-principle
  refinement; cited source GRS arXiv:2208.06602 §3.3; concept confirmed standard across
  Widmer 2012, Masser–Vaaler, Barroero–Widmer 2025, and a 2024 portraits paper (≥5 sources).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — 0 weakening opportunities; ambient
  space already the abstract pi type, single-constant convention already standard. Phase 4c:
  an optional reusable `IsLipschitzParametrizable` predicate would be a *separate additive*
  contribution, not a superseding reformulation, so the verdict stays YES-add-as-is (not
  YES-but-generalise-first).
- Mathlib search (Phase 5): **not in mathlib**. Critically, mathlib's
  `NumberField.Ideal.tendsto_norm_le_div_atTop` (Roblot 2025) proves the *qualitative*
  count `~ c·s` via the geometry-of-numbers `Tendsto` route with **no error term and no
  Lipschitz cover**; mathlib's `NormLeOne.lean` uses `expMapBasis` only for the volume and
  the *measure-zero* frontier (`volume_frontier_normLeOne`).
- Composition check (Phase 6): **NOT-COMPOSABLE** — it is the capstone of ~170 lines of new
  development; mathlib provides the atoms, not the theorem or any ≤3-call route.

**Rationale.**
This theorem fills a specific, nameable gap in mathlib's analytic number theory: mathlib
can state that the number of ideals of norm `≤ s` is *asymptotically* `c·s`
(`tendsto_norm_le_div_atTop`), but it has **no effective version with an error term**,
because it lacks the standard input that produces one — a Lipschitz parametrization of the
counting region's boundary (Davenport/Widmer's *Lipschitz class*). The theorem supplies
exactly that input for the canonical fundamental-cone region: it certifies that
`∂(normAtAllPlaces '' normLeOne K)` is Lipschitz parametrizable of codimension 1, the
hypothesis form (`hlip`) consumed verbatim by an effective lattice-point count. The
statement matches the literature predicate to the letter, at the right generality
(abstract `realSpace K` ambient, single common constant, `Fin m`-indexed finite family),
and is non-composable from mathlib's primitives (the `t = exp(x_{w₀})` linearisation of the
unbounded `w₀`-direction and the face-by-face `C¹`-on-compact-cube Lipschitz bound are real
proof work, not a chained call).

It is genuine new mathematical content that composes immediately with mathlib's existing
geometry-of-numbers stack: once present, `MeasureTheory.Group.GeometryOfNumbers` /
`ZLattice.covolume` users gain the missing regularity hypothesis to upgrade Roblot's
qualitative asymptotic to an effective one, and the result is the load-bearing first link
of this project's `realSpace → mixedSpace → index → effective ideal count` chain (one
in-project consumer already; no inline re-derivation anywhere).

**WHY add it (the gap, named).**
- *Specific mathlib gap*: `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` proves
  `tendsto_norm_le_div_atTop` (leading term, no remainder). There is **no** effective ideal
  counting theorem in mathlib and **no** Lipschitz-boundary regularity lemma anywhere
  (confirmed: mathlib has no `Lip(n,M,L)`/`IsLipschitzParametrizable` predicate — Phase 5
  methods A–E + the `parametriz` grep all empty). This theorem is the missing prerequisite
  for the effective theory.
- *How it composes*: it is the `hlip` hypothesis of a Davenport/Widmer-style count
  (mathlib's `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` and the
  `ZLattice.covolume`/`GeometryOfNumbers` API are the natural neighbours). With it, the
  boundary-discrepancy `O(t^{r−1})` estimate becomes available to every consumer of
  `expMapBasis`/`normLeOne`.

**Proposed mathlib location:** `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOneLipschitz.lean`
(a new file `public import`-ing `…/NormLeOne.lean`), or appended to
`…/CanonicalEmbedding/NormLeOne.lean` if kept together with the volume/measure-zero results.

**Proposed PR title:** `feat(NumberTheory/NumberField): Lipschitz cover of the frontier of normLeOne`

**PR grouping (REQUIRED).** Ship as **one PR** with the whole supporting block from this
file, since the theorem is meaningless without its scaffolding and its `_mixedSpace`/`_index`
siblings are the consumers that justify it:
- supporting defs/lemmas (all YES-add-as-is companions in the same development):
  `clampUnit`, `clampUnit_mem_Icc`, `clampUnit_eq_self`, `lipschitzWith_clampUnit`,
  `exists_lipschitzWith_comp_clampUnit`, `contDiff_expMapBasis`, `faceMapZero`/`faceMapSide`
  (+ their `contDiff_…`), `cubeRelabel` (+ `lipschitzWith_cubeRelabel`, `…_mem_Icc`,
  `exists_cubeRelabel_eq`), `frontier_image_paramSet_subset`, `image_boundary_subset_faces`,
  `frontierCoverFamily`, `exists_lipschitzWith_frontierCoverFamily`,
  `frontier_subset_frontierCoverFamily`;
- the headline trio: this theorem + `normLeOne_frontier_lipschitz_cover_mixedSpace` +
  `normLeOne_frontier_lipschitz_cover_index`.
- **Strongly recommended companion**: introduce a reusable
  `def IsLipschitzParametrizable (n k : ℕ) (S : Set E) : Prop` (Phase 4c) in the same PR or a
  predecessor PR, and state all three theorems against it, so the effective-counting API
  speaks one `hlip` vocabulary. (Optional: does not block this theorem.)

**Pre-PR checklist before opening:**
- [ ] `/generalise Chebotarev.normLeOne_frontier_lipschitz_cover` — confirm no further
      weakening (expected: none; but tension the ambient-space typeclasses).
- [ ] Decide the `IsLipschitzParametrizable` predicate question (introduce now vs. follow-up).
- [ ] `/cleanup …/NormLeOneLipschitz.lean` — full style audit + diff gates on the whole block.
- [ ] Pick a reviewer from recent `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/`
      commits — **Xavier Roblot** is the author of `NormLeOne.lean` and `Ideal/Asymptotics.lean`
      and the natural reviewer; this theorem is the direct effective-counting sequel to his work.

---

## Next step

Open a mathlib PR titled
`feat(NumberTheory/NumberField): Lipschitz cover of the frontier of normLeOne`,
shipping `normLeOne_frontier_lipschitz_cover` together with its supporting development and
the `_mixedSpace`/`_index` consumers as one coherent contribution; before opening, run
`/generalise` then `/cleanup` on the file and decide whether to bundle a reusable
`IsLipschitzParametrizable` predicate. Suggested reviewer: Xavier Roblot.
