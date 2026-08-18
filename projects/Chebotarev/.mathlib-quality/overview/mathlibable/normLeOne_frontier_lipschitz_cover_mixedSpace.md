# /mathlibable report — `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`

> Step-9 full mathlibable assessment. ForMathlib/ helper, author-earmarked for mathlib.
> Run 2026-06-18. ChatGPT MCP was down; `lean_loogle`/`lean_leansearch` index tools were
> unavailable in-session — mathlib search was done by authoritative grep over the vendored
> mathlib tree (`.lake/packages/mathlib/`, pin `v4.31.0-rc2`) plus WebSearch ×5.

### Baseline (Phase 0)
- lake build:               not re-run (stale per task brief); reasoning from source as instructed
- decl `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:626`
- qualified name VERIFIED: inside `namespace Chebotarev` (opens L79, `end Chebotarev` L673) ⇒
  `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace` (parsed name confirmed correct)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of `frontier (normLeOne K)` — the
  quantitative boundary regularity (Widmer/GRS §3.3, after Debaene) strengthening mathlib's
  measure-zero `volume_frontier_normLeOne`, feeding the effective lattice-point count.

---

### Statement (Phase 1)

`normLeOne_frontier_lipschitz_cover_mixedSpace` asserts: for a number field `K`, the topological
frontier of `normLeOne K` (= `fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ 1}`, a subset of
the mixed space `mixedSpace K = (∏ real places ℝ) × (∏ complex places ℂ)`) is **Lipschitz
class (m, M)**: there exist a finite count `m`, a constant `M : ℝ≥0`, and `m` maps
`φⱼ : (Fin (d−1) → ℝ) → mixedSpace K` (`d = finrank ℚ K`), each `M`-Lipschitz, whose images of
the unit cube `[0,1]^{d−1}` cover `frontier (normLeOne K)`.

This is exactly Widmer's "Lipschitz parametrizability of the boundary" (after Masser–Vaaler)
notion: ∂S covered by finitely many Lipschitz images of a unit cube of dimension one less than
the ambient dimension. It is the `mixedSpace`-level (`d−1`-dimensional) lift of the `realSpace`
cover `normLeOne_frontier_lipschitz_cover` (`r−1`-dimensional, `r = #InfinitePlace K`); the lift
folds the real-place signs into the finite index and adds the complex-place phases as the extra
`r₂` cube coordinates, `(r−1)+r₂ = d−1`.

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K]` `[NumberField K]` — the number field (section variable).

Hypotheses: none (it is an unconditional existence statement about `K`).

Conclusion (math): `frontier (normLeOne K)` is in the Lipschitz class `(m, M)` of subsets of
`mixedSpace K`, with cube dimension `d − 1`, `d = [K:ℚ]`.

Conclusion (Lean):
`∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K),`
`  (∀ j, LipschitzWith M (φ j)) ∧ frontier (normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a named `## Main results` entry of the module (L30), a genuine new theorem (quantitative
boundary regularity — not a restatement), and a direct strengthening of a mathlib result
(`volume_frontier_normLeOne`). It is the central deliverable that the whole 673-line file builds
toward at the mixed-space level.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` ⇒ one-liner check n/a. (Body is ~16 lines, L631–641, assembling several
heavy project lemmas: `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`,
`lipschitzWith_liftToMixed`, `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Lipschitz parametrization boundary fundamental domain lattice point counting number field Widmer Debaene" | yes | Widmer's "Lipschitz class (N,L)": ∂ covered by N maps from `[0,1]^{k}`, Lipschitz const ≤ L | hits Widmer (RHUL), arXiv:1611.10103 (GRS-adjacent), Masser–Vaaler lineage |
| 2 | WebSearch (general form) | "Masser Vaaler Lipschitz parametrizable boundary 'Lipschitz class' N L maps unit cube counting lattice points definition" | yes | "∂S covered by image of ≤ W maps from `[0,1]^{D−1}`; then `|Z − Vol/covol| ≤ cW(L/λ₁+1)^{D−1}`" (Widmer AMS Proc. 140 (2012)) | the general principle is fully ambient-dimension-general; the cover is its hypothesis |
| 3 | WebSearch (named-after / aliases) | "mathlib4 frontier normLeOne fundamental cone Lipschitz cover unit cube number field" | yes (lit, not mathlib) | "boundary of a number-field fundamental parallelotope covered by 2r maps from `[0,1]^{r−1}`; complex places contribute n+1 maps with constant ∝ 2π√(2n+1)" | the `2π` factor matches the proof's `M₀ + (B·2π).toNNReal` (L638) exactly |
| 4 | WebSearch (source paper) | "Gun Ramare Sivaraman 'Counting ideals in ray classes' JNT 2023 fundamental domain Lipschitz boundary mixed space" | yes | the cited source: JNT 243 (2023) 13–37, HAL hal-03805062 / arXiv:2208.06602; §3.3 has fundamental-domain + Lipschitz-boundary sections | confirms the project's docstring citation verbatim |
| 5 | ChatGPT MCP | (standard form / mathlib coverage / generality of Lipschitz-boundary) | n/a | — | MCP server down this session (Codex exec failed); compensated by extra WebSearch + direct mathlib grep |
| 6 | Local references | grep `.mathlib-quality/references/` + `refs/Chebotarev/` for "Lipschitz"/"Widmer" | n/a | — | refs are local-only/gitignored; not present in this checkout — recorded n/a |
| 7 | nLab | "Lipschitz parametrizable boundary" / "geometry of numbers counting" | n/a | — | not a categorical concept; nLab has no geometry-of-numbers counting page — n/a with reason |
| 8 | nCatLab | — | n/a | — | not categorical — n/a |
| 9 | Stacks Project | — | n/a | — | not an algebraic-geometry concept (analytic geometry of numbers) — n/a |
| 10 | MathOverflow / Math.SE | covered transitively via #1–#3 result sets (Widmer/Masser–Vaaler threads surfaced) | yes | same "Lipschitz class (N,L)" definition | no new generality dimension beyond #2 |
| 11 | recent arXiv (≤5 yr) | "Heights and morphisms in number fields" (arXiv:2411.13522), "Counting primitive points" (1204.0927) | yes | restate Widmer's class-(N,L) boundary cover and the resulting `O(t^{d−1})` error | confirms the notion is current and standard, unchanged formulation |

**Protocol pass:** WebSearch ran 4 distinct queries at different generality levels (specific
number-field form, the fully-general Widmer principle, the named/aliased form, the source paper).
ChatGPT MCP recorded n/a with reason (server down), compensated. Local refs / nLab / nCatLab /
Stacks / MathOverflow / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **Lipschitz parametrizability of the boundary** / "boundary of Lipschitz
class (N, L)" (Masser–Vaaler 1983; Widmer, *Lipschitz class, narrow class, and counting lattice
points*, Proc. AMS 140 (2012)). Applied to the number-field norm-≤-1 / fundamental-cone region by
Debaene and by Gun–Ramaré–Sivaraman, *Counting ideals in ray classes*, JNT 243 (2023) §3.3.

Sources agree on the standard form: **yes** — every source states the identical shape: ∂S ⊆ union
of ≤ N images of `[0,1]^{ambient−1}` under L-Lipschitz maps.

Most general standard form: the *counting principle* is stated for an **arbitrary bounded set in
`ℝ^d`** whose boundary is Lipschitz-(N,L). The **frontier-cover itself** (this theorem) is the
per-region hypothesis fed to that principle; in the literature it is established as a *step inside*
the counting proof for the specific region, never published as a standalone named lemma.

Generality dimensions where the literature varies:
  - ambient space: the cover is region-specific (here `mixedSpace K`); the *principle* is generic ℝ^d.
  - cube dimension: always `ambient − 1` (here `d − 1`, `d = [K:ℚ]`) — matches the statement.
  - Lipschitz constant: explicit in some treatments (the `2π`-flavoured complex-place constant);
    this theorem also produces an explicit `M = M₀ + (B·2π).toNNReal`.

Disagreement with the literature: **none**. The Lean statement is the literature-standard
"Lipschitz class (m, M)" predicate for `frontier (normLeOne K)`, ambient `mixedSpace K`, cube
dimension `d − 1`.

---

### Generality analysis — `normLeOne_frontier_lipschitz_cover_mixedSpace`

Literature-standard form (Phase 3): `frontier S` is Lipschitz class `(N, L)` — covered by finitely
many `L`-Lipschitz images of `[0,1]^{(dim ambient) − 1}`. Here `S = normLeOne K`, ambient
`mixedSpace K` of real dimension `d = finrank ℚ K`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `K` number field | `[Field K] [NumberField K]` | a number field | NO | `normLeOne`, `mixedSpace`, `finrank ℚ K` are all defined only for number fields; this is the natural and only domain |
| 2 | region `normLeOne K` | mathlib's `normLeOne K` | the norm-≤-1 fundamental-cone region | NO | the statement is *about this specific mathlib set*; generalising the region is a different theorem (the generic Widmer principle — a separate decl, the consumer) |
| 3 | cube dimension | `Fin (finrank ℚ K − 1)` | `[0,1]^{(amb dim)−1}` | NO | `finrank ℚ K = dim_ℝ (mixedSpace K)` exactly; this IS the standard ambient−1 |
| 4 | output ambient | `mixedSpace K` | the ambient containing S | NO | the frontier lives in `mixedSpace K` by construction |
| 5 | Lipschitz const `M` | existentially quantified `ℝ≥0` | a finite L | NO (already ∃) | existential is the standard packaging; an explicit value isn't required by the standard form |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it states — the region-specific frontier
cover). Number of weakening opportunities found: **0**. There is no slack: every parameter is
forced by the mathlib objects involved. The only "more general statement" in the literature is a
*different theorem* — the generic bounded-set Widmer counting principle — which is the downstream
*consumer* `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`, not a generalisation of this
hypothesis-lemma. Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | bundled "let X be a foo" ⟶ typeclasses? | no | — | hypotheses are already typeclasses (`NumberField K`); conclusion is a plain ∃ |
| 2 | sequences/metric ⟶ filters/topology? | no | — | already topological (`frontier`, `LipschitzWith`); no sequence in sight |
| 3 | construct ⟶ universal-property class? | no | — | it's an existence/covering statement, no object to characterise universally |
| 4 | set+closure-pred ⟶ bundled substructure? | no | — | `frontier`/`⊆`/`''` are the right vocabulary |
| 5 | vector-space/field-specific ⟶ weaker typeclass? | no | — | `mixedSpace K` is the fixed canonical ambient; nothing to weaken |
| 6 | 1-categorical ⟶ higher-categorical? | no | — | analytic statement, no categorification target |
| 7 | concrete index ⟶ general monoid/group? | **partially** (see note) | a generic Widmer "bounded + Lipschitz-(N,L) boundary" predicate, region-agnostic | this is the *consumer's* hypothesis shape, already present as the `hlip` field of `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`; this theorem is its `normLeOne` *witness* |

Note on #7: there IS a more abstract object in play — "boundary is Lipschitz-(N,L)" as a reusable
predicate. But that abstraction already exists in the project as the inline `hlip` hypothesis of
the counting workhorse. Abstracting it into a named mathlib *predicate/def* would be a separate,
additive contribution; it would not change or subsume this theorem, whose job is to *prove the
predicate holds for `normLeOne K`*. So this is not a "generalise this decl first" move.

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this declaration). The statement is already in contemporary
mathlib idiom (`frontier`, `LipschitzWith`, `⋃ j, φ j '' Icc 0 1`), at the only sensible
generality, and matches the literature standard. The adjacent abstraction (a generic
Lipschitz-boundary predicate + Widmer counting lemma) is a *different, additive* mathlib target
(the `IdealCongruenceCount`/`LatticePointCount` workhorses), not a regeneralisation of this lemma.

### Diamond / defeq risk — n/a

Declaration kind is `theorem` ⇒ Phase 4.5 skipped (no definitional equalities / instance-search
paths introduced).

---

### Mathlib search-status: `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`

[A] Lean-Finder       — tool unavailable this session                          n/a: index tool offline
[B] Loogle            `frontier _ ⊆ ⋃ _, _ '' Set.Icc 0 1`, `LipschitzWith _ _ ∧ frontier _ ⊆ _`  n/a: index tool offline → substituted with [D] grep over vendored tree
[C] LeanSearch        "frontier covered by Lipschitz images of unit cube"       n/a: index tool offline → substituted with WebSearch + [D]
[D] Grep mathlib src  `frontier.*⊆.*''.*Icc`, `Icc 0 1.*frontier`, `lipschitzCover`/`LipschitzCover`, `Lipschitz.*parametriz`, `boundary.*lipschitz` (whole tree, `-i`)  **NO HITS** (empty) — mathlib has no Lipschitz-cover-of-frontier API anywhere
[E] Name pattern      `normLeOne`, `volume_frontier_normLeOne` in mathlib       found `volume_frontier_normLeOne` (NormLeOne.lean:868) — measure-zero ONLY; no Lipschitz/cover variant

Searched for both:
  - the user's current form (`mixedSpace`, `normLeOne`, frontier cover) — not in mathlib
  - the literature-standard form (generic "Lipschitz class (N,L) boundary cover") — also not in
    mathlib (no `LipschitzCover`/boundary-parametrization API exists at all)

Building blocks that ARE in mathlib (used by the proof, confirmed by grep):
  - `Continuous.frontier_preimage_subset` — `Mathlib/Topology/Continuous.lean:200`
    (`frontier (f ⁻¹' t) ⊆ f ⁻¹' frontier t`)
  - `Homeomorph.image_frontier` — `Mathlib/Topology/Homeomorph/Defs.lean:312`
  - `LipschitzWith.comp`, `ContinuousLinearEquiv.lipschitz`, `IsometryEquiv.…isometry.lipschitz`
  - mathlib's `normLeOne` API: `normLeOne_eq_preimage_image`, `continuous_normAtAllPlaces`,
    `normAtAllPlaces`, `expMapBasis` family, `volume_frontier_normLeOne` (NormLeOne.lean)
  - the project's own `IsCover` neighbour exists in mathlib (`Topology/MetricSpace/Cover.lean`),
    but it is a covering-radius notion, NOT a Lipschitz-image-of-cube frontier cover.

Concluded: **not in mathlib** (the literature-standard form too). Mathlib has only the strictly
weaker `volume_frontier_normLeOne` (measure zero) for this exact region, plus the generic
topological glue this proof consumes — but no Lipschitz boundary-cover, region-specific or generic.

---

### Call sites — `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`

Internal use count: **1** (outside the declaring file's own docstring/self): 0 external files —
the sole consumer is in the SAME file.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ForMathlib/NormLeOneLipschitz.lean:657 | `obtain ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace K` (inside `normLeOne_frontier_lipschitz_cover_index`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - (none) — no other site re-derives a mixed-space Lipschitz frontier cover. The downstream
    `index K → ℝ` cover (`normLeOne_frontier_lipschitz_cover_index`) is built *by transporting*
    this theorem's output, and is in turn the `hlip` input ultimately reached from
    `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` / `…_coset_…_rpow_le`.

Call-sites reading: K = 1 internal use, but it is a *load-bearing structural link* in a deliberate
three-layer API (realSpace cover → **mixedSpace cover** → index-space cover → lattice count), not
an inlinable wrapper. The mixed-space layer is the mathematically essential middle step (it is
where the fibre/sign/phase lift happens); the single consumer is the relabelling chart, which
cannot bypass it. This is the "right abstraction with one current consumer because it's the middle
of a pipeline" pattern, not the "wrong abstraction, inline it" pattern.

---

### Composition check (Phase 6)

Can `normLeOne_frontier_lipschitz_cover_mixedSpace` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(volume_frontier_normLeOne K) |> …`
  - Mathlib decls used: `volume_frontier_normLeOne`
  - Result: **fails** — measure-zero gives no Lipschitz parametrization; there is no mathlib lemma
    "null frontier ⟹ Lipschitz-cover-of-frontier" (it is false in general).

Attempt 2: `(continuous_normAtAllPlaces K).frontier_preimage_subset _ |> Set.preimage_mono … |> …`
  - Mathlib decls used: `Continuous.frontier_preimage_subset`, `Set.preimage_mono`
  - Result: **partial** — yields only `frontier (normLeOne K) ⊆ normAtAllPlaces ⁻¹' frontier(image)`
    (this is precisely the project's helper `frontier_normLeOne_subset_preimage`). The hard part —
    parametrizing the preimage of the realSpace frontier cover by Lipschitz cube maps (signs folded
    into the index, complex phases as extra cube coords via the polar form
    `z = ‖z‖·exp((2πθ−π)i)`, with per-chart Lipschitz bounds) — is NOT supplied by mathlib. Needs
    `frontierCoverFamily`, `liftToMixed`, `lipschitzWith_liftToMixed`, `mixedCubeEquiv`,
    `mem_iUnion_image_liftToMixed_of_eq` — all project-defined across ~120 lines.

Conclusion: **NOT-COMPOSABLE**. Mathlib supplies a couple of the topological glue steps, but the
substantive content (the explicit Lipschitz cube charts and their constants on the mixed space) is
genuinely new and many lemmas deep. Far beyond a ≤3-call composition.

---

## Verdict: `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): the statement is exactly Widmer/Masser–Vaaler "Lipschitz class
  (m, M) of the boundary" for `frontier (normLeOne K)`, ambient `mixedSpace K`, cube dim `d−1`;
  source = GRS *Counting ideals in ray classes* JNT 243 (2023) §3.3, after Debaene. Standard form,
  no disagreement.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (0 weakenings; every parameter forced by
  the mathlib objects). Phase 4c: no modern-idiom restatement — already contemporary idiom; the
  adjacent abstraction is a *separate additive* target (the generic Widmer counting lemma), not a
  regeneralisation of this hypothesis-lemma.
- Mathlib search (Phase 5): **not in mathlib**, in either the specific or the literature-general
  form. Mathlib has only `volume_frontier_normLeOne` (strictly weaker: measure zero) for this
  region and no Lipschitz-boundary-cover API at all.
- Composition check (Phase 6): **NOT-COMPOSABLE** (≫ 3 calls; ~120 lines of project machinery).

**Rationale:**

Mathlib's own `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean` already
defines `normLeOne K` and proves the *qualitative* boundary fact `volume_frontier_normLeOne`
(the frontier is Lebesgue-null). The effective lattice-point count needs the strictly stronger
*quantitative* fact — that the frontier is Lipschitz-parametrizable (Widmer's "Lipschitz class
(N,L)") — and mathlib does **not** have it: a whole-tree grep for any
`frontier ⊆ ⋃ _, _ '' Icc 0 1` / `LipschitzCover` / Lipschitz-boundary-parametrization API comes
back empty. This theorem fills exactly that gap, in mathlib's own `mixedSpace K` / `normLeOne K`
vocabulary, at the only sensible generality (cube dimension `finrank ℚ K − 1 = dim_ℝ mixedSpace K
− 1`, matching the literature's ambient−1). It is the standard formulation, sits naturally beside
`volume_frontier_normLeOne` in the same file family, and is many lemmas deep — not a composition
of mathlib primitives (mathlib supplies only the `Continuous.frontier_preimage_subset` /
`Homeomorph.image_frontier` glue; the explicit Lipschitz cube charts, the sign/phase fibre lift,
and their constants are all genuinely new).

**WHY add it (refactor-actionable):**
- *New content vs. the named mathlib gap.* Mathlib has `volume_frontier_normLeOne` (NormLeOne.lean:868)
  but nothing quantitative about that frontier. This theorem is the canonical
  "Lipschitz cover of `frontier (normLeOne K)`" that the geometry-of-numbers lattice-point machinery
  requires — the standard Widmer/Masser–Vaaler input. Mathlib's `NumberField.Ideal.Asymptotics`
  (which already counts ideals) currently has no access to an explicit boundary cover; this is the
  missing regularity that would let an *effective* error term `O(t^{d−1})` be added there.
- *Composition with mathlib API.* Once present, it directly composes with `Homeomorph.image_frontier`
  + `ContinuousLinearEquiv.lipschitz` to transport to any coordinate chart (as the sibling
  `normLeOne_frontier_lipschitz_cover_index` already shows), and it is the exact `hlip`-shaped
  hypothesis a general Widmer counting lemma would consume — enabling the effective-count upgrade of
  `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean`.

Proposed mathlib location:    `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`
                              (or a new sibling `…/NormLeOneLipschitz.lean` if the file gets large)
Proposed PR title:            `feat(NumberTheory/NumberField): Lipschitz cover of the frontier of normLeOne`
PR grouping:                  ship as ONE PR with the two siblings in this file —
                              `Chebotarev.normLeOne_frontier_lipschitz_cover` (the realSpace cover,
                              L348) and `Chebotarev.normLeOne_frontier_lipschitz_cover_index` (the
                              index-space transport, L651) — plus their supporting defs
                              (`clampUnit`, `faceMapZero`, `faceMapSide`, `frontierCoverFamily`,
                              `liftToMixed` and their lemmas). The three covers form one coherent
                              API layer and should land together; each public `def` among the
                              supports needs its OWN Phase-4.5 diamond pass before the PR (they were
                              out of scope for this theorem-only assessment).
Pre-PR checklist before opening:
  - [ ] `/mathlibable` the supporting `def`s individually (clampUnit / faceMap* / frontierCoverFamily
        / liftToMixed) — they ship in the same PR and need the def-risk (Phase 4.5) gate.
  - [ ] `/generalise Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace` — confirm no easy
        further weakening (expected: none; recorded MAXIMALLY GENERAL here).
  - [ ] `/cleanup <file>` over `NormLeOneLipschitz.lean` — full style audit + axiom/diff gates.
  - [ ] strip the project-specific `Chebotarev` namespace / `Gun–Ramaré–Sivaraman` framing from the
        docstrings; keep the mathlib-neutral mathematical statement + the Widmer/Masser–Vaaler
        citation.
  - [ ] pick a reviewer from recent `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/` commits
        (the `NormLeOne` author).

---

## Next step

Run the supporting-`def` mathlibable passes + `/generalise` + `/cleanup` per the checklist above,
then open one `feat(NumberTheory/NumberField)` PR bundling the three frontier-cover theorems
(`…_cover`, `…_cover_mixedSpace`, `…_cover_index`) and their supports, landing next to
`volume_frontier_normLeOne`.
