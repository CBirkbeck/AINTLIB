# /mathlibable report — `Chebotarev.ncard_index_image_le_of_diam_le`

## Baseline (Phase 0)

- lake build:               (not re-run — local build known stale; reasoning from source per task note)
- decl `Chebotarev.ncard_index_image_le_of_diam_le`:  ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean:102`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  effective lattice-point count with a Lipschitz-boundary `O(nᵈ⁻¹)`
  error term — the deepest analytic input to the class-field-theory-free Chebotarev proof; the
  file's `ForMathlib` header explicitly states it is "stated here for a future mathlib contribution".
- namespace: `Chebotarev` (single `namespace Chebotarev` block, `open … BoxIntegral.unitPartition`).
  Qualified name **confirmed** `Chebotarev.ncard_index_image_le_of_diam_le`.

## Statement (Phase 1)

`ncard_index_image_le_of_diam_le` is a theorem stating the basic combinatorial cell-incidence bound
of the geometry of numbers:

> Let `ι` be a finite type and equip `ι → ℝ` with the sup (ℓ∞) metric. Fix `n ∈ ℕ`, `n ≠ 0`, and let
> the cells of the `n⁻¹ℤ^ι` grid be the half-open boxes `unitPartition.box n ν` indexed by
> `ν = index n x = (⌈n·xᵢ⌉ − 1)ᵢ`. If a bounded set `T ⊆ ι → ℝ` has diameter `≤ r` (with `0 ≤ r`),
> then the number of distinct grid cells `T` meets — i.e. `(index n '' T).ncard` — is at most
> `(2⌈n·r⌉₊ + 1)^(card ι)`.

In dimension `d = card ι`: a set of diameter `r` meets at most `(2⌈n·r⌉ + 1)ᵈ` cells of a cube grid
of side `1/n`. (Sup metric is the right choice: a cube of side `1/n` then has diameter exactly `1/n`,
and the per-coordinate `⌈n·xᵢ⌉` indices of two points of `T` differ by at most `⌈n·r⌉`.)

Variables / typeclasses (Lean side):
- `{ι : Type*} [Fintype ι]` — index set / ambient dimension; `Fintype` gives the sup metric on `ι → ℝ`.
- `(n : ℕ) [NeZero n]` — grid refinement; cells have side `1/n`.
- `{T : Set (ι → ℝ)}` — the set being counted.
- `{r : ℝ}` — the diameter bound.

Hypotheses (Lean side):
- `(hr : 0 ≤ r)` — nonnegativity of the bound (used so `⌈n·r⌉₊` behaves).
- `(hdiam : Metric.diam T ≤ r)` — `T` has diameter at most `r`.
- `(hbdd : Bornology.IsBounded T)` — boundedness (needed for `Metric.diam` to be meaningful, since
  `Metric.diam` of an unbounded set collapses to `0`; `dist_le_diam_of_mem` needs it).

Conclusion (math): `T` meets at most `(2⌈n·r⌉ + 1)ᵈ` grid cells, `d = card ι`.
Conclusion (Lean): `(index n '' T).ncard ≤ (2 * ⌈(n : ℝ) * r⌉₊ + 1) ^ Fintype.card ι`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper lemma (a building block — listed under `## Main results` only as a "building block
reused by the unit-grid ideal-congruence count", not a named/main theorem). It is the elementary
cell-counting step feeding the single-chart bound `ncard_index_image_chart_le`.

(Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line check **n/a**. (Body is a ~28-line
combinatorial proof: empty-case split, a `Fintype.piFinset` of `Finset.Icc (cᵢ − K) (cᵢ + K)` cover,
`Set.ncard_le_ncard` into that finset, then `Int.card_Icc` / `Finset.prod_const`.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "number of lattice grid cells meeting a set of small diameter bound lattice point counting"             | partial | no *named* theorem; the mechanism is standard      | "basic counting mechanism for lattice points in cubes"; matches arXiv:1308.0954 (Cayley/quaternion height counting) |
|  2 | WebSearch (general / mechanism)  | "Lipschitz parametrizable boundary lattice point counting Davenport Widmer error term grid cells"       | yes  | "a Lipschitz map sends a cube in the domain into a cube in the codomain"; #lattice pts ≈ vol, error ∝ perimeter / boundary cells | Widmer, *Lipschitz class, narrow class, and counting lattice points* (Proc. AMS 140 (2012)); refined principle "due to Spain"; exactly the file's cited strategy |
|  3 | WebSearch (aliases / box-count)  | "set of diameter r covered by number of grid cubes side delta box covering lemma geometry of numbers"   | yes  | box-counting: `N(ε)` = min # cubes of side ε covering a set; "unit grid-cube" terminology | Stony Brook / Troscheit fractal-geometry notes; arXiv:1012.2289 "Covering Cubes and the Closest Vector Problem"; the diameter→#cubes bound is folklore, constant rarely pinned |
|  4 | ChatGPT MCP                      | standard-form + generality of "diam ≤ r ⇒ meets ≤ (2⌈nr⌉+1)ᵈ cells of side-1/n grid"                    | **n/a — server down** (Codex MCP failed to launch; task note warned of this). Compensated by extra WebSearch query #3 + nLab #6. |
|  5 | Local references                 | `.mathlib-quality/references/` for "Widmer / Lang / boundary cell"                                       | n/a  | directory absent (`refs/Chebotarev/` also absent)    | recorded n/a; file's own `## References` cite Lang GTM 110 Ch. VI §3 Thm 3 p.129 + Gun–Ramaré–Sivaraman JNT 243 (2023) §3.3, §3.5 (after Debaene) |
|  6 | nLab                             | "lattice point counting" / "box-counting dimension" / "Minkowski content"                               | partial | box-counting / Minkowski-dimension covering function `N(δ)` defined abstractly | nLab has the abstract covering-function notion, not this explicit affine-grid constant |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | not a categorical concept (elementary metric/combinatorial estimate) | — |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | not an algebraic-geometry concept                    | — |
|  9 | MathOverflow / Math.SE           | covered by mechanism search #2/#3; "number of grid boxes a bounded set intersects"                       | partial | the `(2⌈r/δ⌉+1)ᵈ`-type bound appears as folklore in answers on lattice/box covering | no canonical citable statement; constant varies (`+1`, `+2`, factor-3 expansions) |
| 10 | recent arXiv (last 5 years)      | Widmer / Gun–Ramaré–Sivaraman / o-minimal lattice counting (arXiv:2503.01731, 2411.13522)               | yes  | same mechanism; modern treatments (sharp o-minimality, heights over number fields) all use a diameter/Lipschitz → boundary-cell count | confirms the estimate is live and standard, used as a black-box lemma |

### Literature summary (Phase 3)

Concept identified as: the **boundary-cell / cube-incidence estimate** of the geometry of numbers —
"a set of diameter `r` meets at most `(2⌈r/δ⌉+1)ᵈ` cells of a cube grid of side `δ`" (here `δ = 1/n`).
The closely-related abstract notion is the **box-counting / covering function** `N(δ)`.

Sources agree on the standard form: **yes (on the mechanism), with no single canonical constant.**
Every treatment (Davenport; Lang GTM 110 Thm 3; Widmer; Spain's refinement; Gun–Ramaré–Sivaraman;
recent o-minimal work) uses *some* "diameter/Lipschitz-image ⇒ bounded number of grid cells" step as
a black box. The precise constant is incidental and varies by author (`2⌈nr⌉+1`, `⌈nr⌉+2`, factor-3
dilation arguments). The Lean form `(2⌈nr⌉₊+1)ᵈ` is the clean per-coordinate-interval bound.

Most general standard form: as stated — finite dimension `d`, arbitrary diameter bound `r`, sup-metric
cube grid of arbitrary side `1/n`. Nobody states it more generally than "set of diameter `r` in `ℝᵈ`
meets `≤ (const·r/δ + O(1))ᵈ` cubes of a side-`δ` axis-aligned grid"; the `O(1)` constant is what
this lemma pins down for the *specific* grid `unitPartition.box` that mathlib already ships.

Generality dimensions where the literature varies:
- dimension: always a finite `d` (= `card ι` here) — maximally general.
- grid: always an axis-aligned cube grid; mathlib's `unitPartition.box`/`index` is exactly that, so
  the Lean statement is tied to mathlib's own grid object — the right call for the library.
- metric: sup metric is the natural one (makes the cube-side-↔-diameter relation tight). The result
  is *false-flavoured* in ℓ² without inflating the constant — the literature implicitly uses sup too.

Disagreement with the literature: none. The Lean form is a faithful, fully-general instance of the
standard mechanism, specialised to mathlib's `unitPartition` grid (which is the point).

## Generality analysis — `Chebotarev.ncard_index_image_le_of_diam_le`

Literature-standard form (from Phase 3): set of diameter `r` in `ℝᵈ` meets `≤ (2⌈r/δ⌉+1)ᵈ` cells of a
side-`δ` axis-aligned cube grid; `δ = 1/n`, `d = card ι`.

| # | Parameter / hypothesis            | Current Lean form                | Literature-standard form          | Weaker form exists? | Reason |
|---|-----------------------------------|----------------------------------|------------------------------------|---------------------|--------|
| 1 | `{ι : Type*} [Fintype ι]`        | finite index type (sup metric)   | finite dimension `d`               | NO                  | `Fintype` is exactly "finite dimension"; needed for the sup metric on `ι → ℝ` and `Fintype.card`. Already maximal. |
| 2 | `(n : ℕ) [NeZero n]`             | positive grid refinement         | side `δ = 1/n`, any `δ>0`          | marginally          | mathlib's `unitPartition.index` is defined only for `ℕ` refinements (`index n x = ⌈n·xᵢ⌉−1`); generalising `δ` to arbitrary positive real would mean *not* using mathlib's grid — undesirable. Maximal within the mathlib grid API. |
| 3 | `{r : ℝ} (hr : 0 ≤ r)`          | arbitrary nonneg diameter bound  | arbitrary `r ≥ 0`                  | NO                  | already fully general. |
| 4 | `(hdiam : Metric.diam T ≤ r)`    | diameter bound                   | diameter bound                     | NO                  | this *is* the hypothesis of the standard statement. |
| 5 | `(hbdd : Bornology.IsBounded T)` | boundedness                      | (implicit — diam meaningful)       | NO                  | genuinely needed: `Metric.diam` of an unbounded set is `0`, so without `hbdd` the statement is false (`dist_le_diam_of_mem` requires it). Not removable. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within the mathlib `unitPartition` grid object it is
explicitly a statement about). `ι`/`Fintype`, `r`, and the diameter+bounded hypotheses are all at the
weakest sensible strength. The only "narrowing" — restricting the grid side to `1/n` for `n : ℕ` — is
forced by, and desirable for, reusing mathlib's existing `unitPartition.index`/`box` API. Weakening
opportunities found: 0.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                   | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                   | no       | already typeclass-driven (`Fintype`, `NeZero`) | — |
|  2 | sequences/metric → filters/topological?                                    | no       | it is a finite cardinality bound; no limiting process to filter-ise | — |
|  3 | construction → universal-property class?                                    | no       | states a `≤` on `ncard`, constructs nothing | — |
|  4 | set-with-predicate → bundled substructure?                                  | no       | `index n '' T` is the natural object; no lattice structure wanted | — |
|  5 | vector-space/metric/field-specific → weaker typeclass?                      | partial  | could phrase via `coveringNumber (1/n·…) T` (mathlib `Mathlib/Topology/MetricSpace/CoveringNumbers.lean`) | but that *loses* the grid-cell identity callers need; see verdict |
|  6 | 1-categorical → higher-categorical?                                         | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                            | no       | `n : ℕ` is intrinsic to `unitPartition.index`'s definition | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the role this lemma plays). One could *relate* the count to
mathlib's abstract `coveringNumber`, but that is a different, weaker statement: the callers
(`ncard_index_image_chart_le`, and downstream `abs_card_inter_sub_volume_mul_pow_le`) need the bound
on the *specific* quantity `(index n '' T).ncard` — the number of `unitPartition` cells met — because
that is what plugs into mathlib's `tendsto_card_div_pow_atTop_volume` machinery (which is phrased via
`index`/`box`). Re-routing through `coveringNumber` would force a conversion lemma in both directions
and buy nothing. This is a concrete cardinality estimate about mathlib's own grid; the grid-specific
form *is* the idiomatic mathlib form here.

## Diamond / defeq risk — `Chebotarev.ncard_index_image_le_of_diam_le`

n/a — declaration kind is `theorem` (introduces no definitional equalities or instances). Phase 4.5 skipped.

## Mathlib search-status: `Chebotarev.ncard_index_image_le_of_diam_le`

[A] Lean-Finder       (tool unavailable in this env)                              n/a: deferred-tool not loadable; compensated by [D]/[E] direct grep over the mathlib source tree
[B] Loogle            `index _ '' _ |>.ncard`, `Metric.diam _ ≤ _ → ncard _ ≤ _`  n/a: lean_loogle not available here; substituted with structural grep [D]
[C] LeanSearch        "number of grid cells a bounded set of small diameter meets" n/a: lean_leansearch not available here; substituted with [D]/[E]
[D] Grep mathlib src  `ncard.*index`, `index.*''.*ncard`, `diam.*ncard`,
                      `Metric.diam.*ncard`, cube-covering `ceil.*\^.*card` over
                      `Mathlib/Analysis/BoxIntegral/` and all of `Mathlib/`        **no hits** — mathlib has NO `index`-image cardinality bound and NO diameter→cell-count estimate
[E] Name pattern      walked `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`
                      decl list (`index`, `box`, `tag`, `setFinite_index`,
                      `diam_boxIcc`, `volume_box`, `tendsto_card_div_pow_*`)        partial neighbours only — see below

Searched for both:
  - user's current form (`(index n '' T).ncard ≤ (2⌈nr⌉₊+1)ᵈ`) → absent.
  - literature-standard form (diameter → #grid-cubes; covering-number version) → mathlib has the
    abstract `coveringNumber`/`externalCoveringNumber` API (`Mathlib/Topology/MetricSpace/CoveringNumbers.lean`)
    but it contains only qualitative comparison/monotonicity lemmas and `…_le_one_of_ediam_le`; there
    is **no** explicit `ℝᵈ` grid-cube covering bound and **no** link to `unitPartition`.

What mathlib *does* have (the neighbours, none of which is this):
  - `unitPartition.index`/`box`/`tag` (defs), `index_apply`, `mem_box_iff_index`  — the grid object.
  - `unitPartition.diam_boxIcc : Metric.diam (Box.Icc (box n ν)) ≤ 1/n`           — one cell's diameter.
  - `unitPartition.setFinite_index : Set.Finite {ν | box n ν ⊆ s}`                — finiteness, but for
     cells **contained in** `s`, NOT the image `index n '' s` of cells **meeting** `s`, and **no
     quantitative `ncard` bound**.
  - `tendsto_card_div_pow_atTop_volume`                                            — the *asymptotic*
     leading-term count, with **no effective `O(nᵈ⁻¹)` error** — which is exactly the gap this whole
     file (and this lemma as its combinatorial core) exists to fill.

Concluded: **not in mathlib** (all available search methods exhausted, plus the literature-standard /
covering-number form). The companion `setFinite_index_image_of_isBounded` (the *qualitative*
finiteness of `index n '' T`, line 80 of the same file) is *also* absent from mathlib — confirming the
`index n '' s` "cells meeting `s`" view is unbuilt upstream.

## Call sites — `Chebotarev.ncard_index_image_le_of_diam_le`

Internal use count: **2** (within the Chebotarev project, excluding the declaring file's own
docstring mention at line 34).
External-to-file callers: **2 distinct files** (one is the declaring file itself at a *later* line;
one is a genuinely separate file).

| Caller file:line                                                          | Usage pattern (one-line excerpt)                                            |
|---------------------------------------------------------------------------|-----------------------------------------------------------------------------|
| `…/ForMathlib/LatticePointCount.lean:185`                                 | `refine (ncard_index_image_le_of_diam_le n (by positivity) hdimg hbddφ).trans ?_` — inside the single-chart bound `ncard_index_image_chart_le` (the next theorem in the same file) |
| `…/ForMathlib/IdealCongruenceCount.lean:187`                              | `refine (ncard_index_image_le_of_diam_le 1 M.coe_nonneg ?_ hbddφ).trans ?_` — reused for the unit-grid ideal-congruence count (`n = 1` specialisation) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?): **(none)** — the
two consumers both go through this lemma; the second file deliberately reuses it at `n = 1` rather than
re-proving, which is the strongest "real reusable API" signal.

Composability signal: K = 2 cross-file internal uses (one in a *separate* `ForMathlib` file), no inline
re-derivation → real API, consumers depend on the exact `(index n '' T).ncard` form. Leans **YES-***.

## Composition check (Phase 6)

Can `ncard_index_image_le_of_diam_le` be derived from mathlib in ≤3 chained calls?

Attempt 1 — via `unitPartition.diam_boxIcc` + `setFinite_index`:
  - `diam_boxIcc` bounds *one* cell's diameter; `setFinite_index` gives finiteness of cells contained
    in `s`. Neither bounds `(index n '' T).ncard`. No arithmetic combination of the two yields the
    `(2⌈nr⌉+1)ᵈ` count.
  - Result: **fails.** The actual proof builds a `Fintype.piFinset` of per-coordinate
    `Finset.Icc (cᵢ−K) (cᵢ+K)` (`K = ⌈nr⌉₊`), shows `index n '' T ⊆` it via the per-coordinate
    `⌈n·xᵢ⌉` spread bound (the private `ceil_natCast_mul_le_ceil_natCast_mul_add` step), then
    `Set.ncard_le_ncard` + `Int.card_Icc` (`= 2K+1`) + `Finset.prod_const`. That is multiple
    `have`s with genuine per-coordinate reasoning — a real proof, not a chain.

Attempt 2 — via mathlib `coveringNumber` API:
  - `coveringNumber`/`externalCoveringNumber` give abstract `ℕ∞` covering numbers with only
    monotonicity/`≤1-of-ediam-le` lemmas; there is no `ℝᵈ` grid-cube cardinality bound and no bridge
    `coveringNumber → (index n '' T).ncard`. Cannot start.
  - Result: **fails.**

Conclusion: **NOT-COMPOSABLE.** No ≤3-call mathlib composition exists; the per-coordinate
finset-cover argument is irreducible new content over the current mathlib API.

## Verdict: `Chebotarev.ncard_index_image_le_of_diam_le`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): standard geometry-of-numbers boundary-cell mechanism (Davenport / Lang
  GTM 110 Thm 3 / Widmer / Spain / Gun–Ramaré–Sivaraman); the Lean form is a faithful, fully-general
  instance pinning the explicit constant for mathlib's own grid. No disagreement with the literature.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (`ι`/`Fintype`, `r`, diam + bounded hyps all
  weakest sensible); Phase 4c found no real modernisation — the grid-specific form is the idiomatic one.
- Mathlib search (Phase 5): **not in mathlib**; nearest neighbours (`diam_boxIcc`, `setFinite_index`,
  `tendsto_card_div_pow_atTop_volume`) are about cells *contained in* `s` or the *asymptotic* count —
  none is a quantitative `ncard` bound on cells *meeting* `T`.
- Composition check (Phase 6): **NOT-COMPOSABLE** (no ≤3-call derivation; genuine per-coordinate proof).

**Rationale:**

This is the quantitative cell-incidence core of the effective lattice-point count, and it sits directly
on top of mathlib's `BoxIntegral.unitPartition` API (`index`, `box`, `diam_boxIcc`,
`tendsto_card_div_pow_atTop_volume`). Mathlib ships the unit-partition grid and the *qualitative*
finiteness `setFinite_index` and the *asymptotic* count `tendsto_card_div_pow_atTop_volume`, but it has
**no effective error term** — no bound on how many grid cells a small-diameter set meets. That is a
concrete, named gap: `tendsto_card_div_pow_atTop_volume` is the leading-term statement with the error
left un-quantified, and this lemma (with its sibling `setFinite_index_image_of_isBounded` and the
chart-level `ncard_index_image_chart_le`) is exactly the missing combinatorial machinery to upgrade it
to an `O(nᵈ⁻¹)`-effective count. It composes with the existing API immediately: `index`, `box`,
`diam_boxIcc`, and the `unitPartition` finiteness lemmas all become usable in tandem with it, and it is
the natural prerequisite for an effective version of `tendsto_card_div_pow_atTop_volume` in
`Mathlib/Analysis/BoxIntegral/UnitPartition.lean`. The statement is at full generality (arbitrary
finite `ι`, arbitrary `r`, the only-removable-at-a-cost specialisation being the use of mathlib's own
`ℕ`-indexed grid — which is the point of reusing the API). It is not a one-liner, carries two real
cross-file consumers with no inline re-derivation, and is not composable in ≤3 mathlib calls. The file's
own `ForMathlib` header earmarks it for mathlib; the assessment agrees.

WHY add it (refactor-actionable):
- **New content / named gap:** mathlib's `unitPartition` API has the asymptotic
  `tendsto_card_div_pow_atTop_volume` but **no effective/quantitative boundary-cell bound**; this lemma
  supplies the `(index n '' T).ncard ≤ (2⌈nr⌉₊+1)ᵈ` estimate that an effective version of that theorem
  needs. Mathlib also lacks even the qualitative `index n '' T` finiteness (cells *meeting* a bounded
  set, vs. the contained-in-`s` `setFinite_index` it does have) — so this is part of a genuinely
  missing slice of the `unitPartition` API.
- **Composes with existing API:** once added, it sits alongside `diam_boxIcc` (single-cell diameter)
  and `setFinite_index` to give the full "cells meeting a set" story, and feeds an effective
  `tendsto_card_div_pow_atTop_volume`. It also pairs with the file's `setFinite_index_image_of_isBounded`
  and `ncard_index_image_chart_le` (likewise mathlib-absent) — these should be considered together.

Proposed mathlib location:    `Mathlib/Analysis/BoxIntegral/UnitPartition.lean` (same file as `index`,
`box`, `diam_boxIcc`, `setFinite_index`, `tendsto_card_div_pow_atTop_volume` — this lemma is part of
that exact API and references it directly). Namespace would change `Chebotarev.` →
`BoxIntegral.unitPartition.` on upstreaming.

Proposed PR title:            "feat(Analysis/BoxIntegral): cell-incidence bound for `unitPartition.index`
of a small-diameter set"

PR grouping: ship as one PR with the sibling building blocks from the same file that are likewise
mathlib-absent and form the effective-count layer — `setFinite_index_image_of_isBounded`
(qualitative finiteness of `index n '' T`) and `ncard_index_image_chart_le` (the single-chart
`O(nᵈ⁻¹)` bound), and ideally the terminal `abs_card_inter_sub_volume_mul_pow_le` /
`exists_card_inter_smul_lattice_sub_volume_mul_pow_le` as a follow-up PR. (Run `/mathlibable` on each
of those before grouping to confirm their individual verdicts.)

Pre-PR checklist before opening:
- [ ] `/generalise Chebotarev.ncard_index_image_le_of_diam_le` — confirm no further weakening (expect none).
- [ ] `/cleanup …/LatticePointCount.lean Chebotarev.ncard_index_image_le_of_diam_le` — full audit + diff gates;
      in particular fold the two private helpers (`ceil_natCast_mul_le_ceil_natCast_mul_add`,
      `abs_sub_le_one_div_of_ceil_natCast_mul_eq`) into the PR or inline as appropriate.
- [ ] Pick a reviewer from recent `Mathlib/Analysis/BoxIntegral/` commits (the `unitPartition` author).

---

## Next step

Run `/generalise Chebotarev.ncard_index_image_le_of_diam_le` to confirm no further weakening, then
`/cleanup` the declaration, then open a `feat(Analysis/BoxIntegral)` PR adding it (restated in the
`BoxIntegral.unitPartition` namespace) to `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`, grouped
with the sibling `setFinite_index_image_of_isBounded` and `ncard_index_image_chart_le`.
