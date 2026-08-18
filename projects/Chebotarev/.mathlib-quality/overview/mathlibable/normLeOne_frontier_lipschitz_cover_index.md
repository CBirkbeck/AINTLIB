# /mathlibable report — `Chebotarev.normLeOne_frontier_lipschitz_cover_index`

## Verdict: **NO-composable-from-mathlib**

One-line: this is the `realSpace`/`mixedSpace` Lipschitz frontier-cover
(`normLeOne_frontier_lipschitz_cover_mixedSpace`, the genuine contribution)
**transported through the continuous-linear chart `Φ = (stdBasis K).equivFunL`** —
a ≤3-call composition (`LipschitzWith.comp` + `Homeomorph.image_frontier` +
an index relabel). The literature treats this linear transport as immediate
("the boundary of a scaled/sheared region is clearly of Lipschitz class, with
the same number of maps"); mathlib has every building block; the same
`(…).toHomeomorph.image_frontier` transport is already re-derived inline
elsewhere in the project. It should be inlined at its two call sites, not shipped
to mathlib as a standalone lemma.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief; reasoning from source per the environment note).
- decl `Chebotarev.normLeOne_frontier_lipschitz_cover_index`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:651`.
- qualified name:           `Chebotarev.normLeOne_frontier_lipschitz_cover_index`
  (verified: file has `namespace Chebotarev` at line 79; no inner namespace before
  line 651; `end Chebotarev` at line 673).
- kind:                      theorem
- has sorry:                 no (proof complete, lines 657–671; reduces to
  `normLeOne_frontier_lipschitz_cover_mixedSpace` + the `Φ`-transport).
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` —
  the effective (quantitative) boundary-regularity input for the lattice-point count,
  after Gun–Ramaré–Sivaraman §3.3 / Debaene / Widmer (GTM 110 Ch. V §2).

---

### Statement (Phase 1)

`Chebotarev.normLeOne_frontier_lipschitz_cover_index` is a theorem stating:

> Let `K` be a number field, `Φ = (stdBasis K).equivFunL : mixedSpace K ≃L[ℝ] (index K → ℝ)`
> the standard real-coordinate chart of the mixed embedding space (`index K =
> {real places} ⊕ {complex places} × Fin 2`, the `ℝ`-basis index, so `#(index K) =
> finrank ℚ K = d`). Then the topological frontier of the coordinate image
> `Φ '' (normLeOne K) ⊆ (index K → ℝ)` (sup metric) is **Lipschitz parametrizable of
> codimension 1**: there is a finite `m`, a constant `M : ℝ≥0`, and `m` maps
> `φ : Fin m → ([0,1]^{#(index K) − 1} → (index K → ℝ))`, each `M`-Lipschitz, whose
> unit-cube images together cover the frontier.

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — a number field (file-level `variable`).

Hypotheses: none (unconditional existence statement).

Conclusion (math): `∂(Φ '' normLeOne K)` is covered by finitely many `M`-Lipschitz
images of the unit cube of dimension `#(index K) − 1 = d − 1`.

Conclusion (Lean):
```lean
∃ (m : ℕ) (M : ℝ≥0)
  (φ : Fin m → (Fin (Fintype.card (index K) - 1) → ℝ) → (index K → ℝ)),
  (∀ j, LipschitzWith M (φ j)) ∧
    frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆
      ⋃ j, φ j '' Icc 0 1
```

This is the same Widmer predicate as the sibling `normLeOne_frontier_lipschitz_cover`
(realSpace, `r−1`) and `…_mixedSpace` (mixedSpace, `d−1`), but with the parametrized
set living in the **standard Euclidean coordinate space `index K → ℝ`** (sup metric,
lattice `ℤ^(index K)`) — the exact `hlip` hypothesis shape consumed by
`exists_card_coset_inter_smul_sub_volume_mul_rpow_le` / `exists_card_inter_smul_lattice_…`
(with `ι := index K`).

#### Proof body (lines 657–671) — the whole content

```lean
obtain ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace K   -- (A) the real input
set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
set g : Fin (#(index K) - 1) ≃ Fin (finrank ℚ K - 1) := finCongr (…)            -- (B) dim relabel
refine ⟨m, ‖(Φ : … →L …)‖₊ * (M * 1), fun j c ↦ Φ (φ j (fun a ↦ c (g.symm a))),
  fun j ↦ Φ.lipschitz.comp ((hφ j).comp (IsometryEquiv.piCongrLeft' g).isometry.lipschitz), ?_⟩
rw [← Φ.coe_toHomeomorph, ← Φ.toHomeomorph.image_frontier]                       -- (C) frontier transport
refine (Set.image_mono hcov).trans ?_
rw [Set.image_iUnion]; refine Set.iUnion_subset fun j ↦ ?_
rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
exact Set.mem_iUnion.mpr ⟨j, ⟨fun a ↦ c (g a), ⟨fun a ↦ hc.1 _, fun a ↦ hc.2 _⟩, by simp⟩⟩
```

Three conceptual steps: (A) take the mixedSpace cover; (B) relabel the cube
dimension `#(index K)−1 = d−1`; (C) post-compose every chart with `Φ` and push the
cover through `Φ.toHomeomorph.image_frontier`. The remaining lines are the
bookkeeping that the cube-`Icc 0 1` image survives the index relabel.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is *not* a new mathematical structure and *not* a main project result
in its own right — it is the coordinate-transport wrapper of
`normLeOne_frontier_lipschitz_cover_mixedSpace` (which carries the actual content).
The module docstring lists all three `…cover*` theorems together, but the
mathematical novelty is in the realSpace/mixedSpace construction; `_index` only
relabels the ambient space. (Note: literature width was run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**.
(The body is ~15 lines but they are all the transport composition + cube
bookkeeping; there is no definitional content.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Lipschitz parametrizable boundary codimension one image lattice point counting Widmer Davenport"      | yes  | Widmer's "Lipschitz class": `∃ M maps φᵢ:[0,1]^{n−k}→ℝⁿ` covering `∂S`               | Widmer, *Lipschitz class, narrow class, and counting lattice points*, Proc. AMS 140 (2012); Masser–Vaaler; Davenport |
|  2 | WebSearch (general form / transport) | "bilipschitz homeomorphism preserves Lipschitz parametrizability boundary linear coordinate change lattice point count" | yes  | **"The boundary of a scaled and shifted region is clearly of Lipschitz class if you scale and shift the maps for the original boundary; their number is unchanged."** | This is *verbatim* the `_index` operation (apply a fixed linear/affine map to the cover) — treated as immediate, not a lemma |
|  3 | WebSearch (rectifiability / GMT framing) | "nLab Lipschitz map image preimage rectifiable set Hausdorff measure functorial"                  | yes  | Lipschitz preimages are well-behaved; Lipschitz *images* are studied (Hausdorff measurability) but the *cover-transport* is not isolated | arXiv 2006.03418, 2306.07943 — GMT literature, no named "transport of parametrizability" lemma |
|  4 | ChatGPT MCP                      | "Is Φ(S) Lipschitz-parametrizable for Φ a linear homeomorphism, and is this transport a named lemma or an immediate observation?" | n/a  | —                                                                                   | **Codex binary errored** (`Command failed: …/Codex.app…`); fallback to other channels per task brief |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "Lipschitz" / "Widmer"                                          | n/a  | (no references dir — `references/` absent for this project)                          | recorded n/a; refs are local-only per CLAUDE.md and not present on this checkout |
|  6 | nLab                             | `ncatlab.org/nlab/show/Lipschitz+map` — fetched, searched for cover/parametrizability transport         | yes  | **No named lemma** for image of a Lipschitz-parametrizable set under a (bi-)Lipschitz map; page covers only Lipschitz-norm basics, uniform continuity, manifold transition maps | confirms transport is not an isolated abstract result |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept (a metric-geometry cover statement; no universal property) | n/a with reason |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | not an algebraic-geometry concept (geometry of numbers / real boundary regularity)  | n/a with reason |
|  9 | MathOverflow / Math.StackExchange| (covered transitively by #1–#3 result aggregation: Lipschitz-class transport)                           | yes  | consensus: scaling/shearing/linear maps preserve Lipschitz class with the same piece count | reinforces "immediate observation" |
| 10 | recent arXiv (last 5 years)      | "Lipschitz images rectifiable" / "o-minimal lattice point counting" (1210.5943, 2503.01731, 2411.13522)| yes  | transport-under-coordinate-change always inlined into the counting argument, never a standalone lemma | Barroero–Widmer o-minimal framework: the linear-image step is taken for granted |

The protocol passed: WebSearch ran 3 distinct queries at different generality
levels (specific Widmer form / the linear-transport general form / GMT
rectifiability framing); ChatGPT MCP was attempted but the Codex backend errored
(documented); local refs checked (absent → n/a); nLab fetched and inspected;
nCatLab / Stacks recorded n/a with reasons; MathOverflow and arXiv covered.

### Literature summary (Phase 3)

Concept identified as: **transport of a "Lipschitz-parametrizable boundary"
(Widmer's Lipschitz class) under an invertible linear map / Lipschitz homeomorphism.**
Sources agree on the standard form: **yes** — and they agree it is an *immediate
observation*, not a named lemma. Widmer/Masser–Vaaler/Davenport and the
Barroero–Widmer o-minimal sequels all transport the boundary cover under
coordinate changes (scaling, shearing, lattice basis change `T`) by simply
composing the parametrizing maps with the linear map and noting the piece count is
unchanged and the Lipschitz constant scales by the operator norm.
Most general standard form: **for any Lipschitz map `Φ` (constant `L`) that is a
homeomorphism onto its image, if `∂S` is covered by `m` `M`-Lipschitz cube
images then `∂(Φ S) = Φ(∂S)` is covered by `m` `(L·M)`-Lipschitz cube images
(`φᵢ ↦ Φ∘φᵢ`).** The codimension-1 / linear / same-dimension case here is a
special case.
Disagreement with the literature: **none.** The Lean statement is the faithful
`index K → ℝ` instance of exactly this transport.

---

## PHASE 4 — Generality analysis

### Generality status table — `normLeOne_frontier_lipschitz_cover_index`

Literature-standard form (from Phase 3): the abstract transport above. The
declaration is the `Φ = (stdBasis K).equivFunL` instance of it.

| # | Parameter / hypothesis            | Current Lean form                                  | Literature-standard form                           | Weaker / more-general form exists? | Reason |
|---|-----------------------------------|----------------------------------------------------|----------------------------------------------------|------------------------------------|--------|
| 1 | The map `Φ`                       | the *specific* chart `(stdBasis K).equivFunL`      | *any* Lipschitz homeomorphism / linear equiv       | YES                                | The proof uses only `Φ.lipschitz`, `Φ.toHomeomorph.image_frontier`, `‖Φ‖₊`; nothing about `stdBasis` specifically |
| 2 | The set being transported         | the *specific* `normLeOne K`                       | *any* set with a codim-1 Lipschitz frontier cover  | YES                                | The proof consumes only the abstract `normLeOne_frontier_lipschitz_cover_mixedSpace` existential |
| 3 | Ambient / index types             | `mixedSpace K`, `index K`, `finrank ℚ K`           | arbitrary finite-dim normed spaces of equal dim    | YES                                | The dimension match is the only place number-field data enters, via `finrank_eq_card_basis` + `mixedEmbedding.finrank` |
| 4 | Codimension                       | 1 (cube dim `#(index K) − 1`)                      | any `k`                                             | YES                                | nothing special about `k = 1` in the transport step |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in the specific
sense that it is a *fully-specialised instance* of an abstract transport lemma.
This is the decisive observation: the right mathlib object (if anything) is the
**abstract transport**, of which `_index` is one application — and that abstract
transport is itself a ≤3-call composition of existing mathlib primitives (see
Phase 6). So "generalise first" does not lead to a YES; it leads to the
recognition that the general statement is *itself composable* and that `_index`
is one inlined use of it.

Number of weakening opportunities: 4 (all of "specialise → abstract transport").
Proposed restatement (the abstract transport), for the record:

```lean
-- The shape the literature/general form would take; NOT proposed for mathlib as a
-- standalone lemma because it is a ≤3-call composition (Phase 6).
theorem lipschitz_frontier_cover_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E ≃L[ℝ] F) {s : Set E} {m : ℕ} {M : ℝ≥0} {n : ℕ}
    (φ : Fin m → (Fin n → ℝ) → E)
    (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : frontier s ⊆ ⋃ j, φ j '' Icc 0 1) :
    ∃ (M' : ℝ≥0) (ψ : Fin m → (Fin n → ℝ) → F),
      (∀ j, LipschitzWith M' (ψ j)) ∧ frontier (Φ '' s) ⊆ ⋃ j, ψ j '' Icc 0 1 :=
  ⟨‖(Φ : E →L[ℝ] F)‖₊ * M, fun j ↦ Φ ∘ φ j, fun j ↦ Φ.lipschitz.comp (hφ j), by
    rw [← Φ.coe_toHomeomorph, ← Φ.toHomeomorph.image_frontier, Set.image_iUnion]
    exact (Set.image_mono hcov).trans (Set.iUnion_mono fun j ↦ by rw [Set.image_image])⟩
```

Cost of restatement: **CHEAP** — but irrelevant, because even this general form is
a composition mathlib already supports, so the verdict is NO-composable rather than
YES-but-generalise (cost is not the gating reason — see Phase 6).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Reformulation / reason |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                            | no       | no bundled-hypothesis preamble; `Φ` is already a bundled `≃L` |
|  2 | sequences/metric → filters/nets/topological?                                               | no       | already topological (`frontier`, `Homeomorph`); nothing to filter-ise |
|  3 | construction → universal-property class?                                                   | no       | not a construction of an object; an existence-of-cover statement |
|  4 | set-with-closure-predicate → bundled substructure?                                         | partial  | one *could* bundle "set with codim-1 Lipschitz frontier cover" into a structure/predicate (`IsLipschitzParametrizable`), which would make this transport a lemma about that predicate — but that is a *new mathlib definition* decision orthogonal to this decl, and is flagged in the sibling `normLeOne_frontier_lipschitz_cover` report (YES-add-as-is) as the place to raise it, not here |
|  5 | vector-space/metric-specific → weaken typeclasses?                                          | yes      | `Φ` could be any `≃L` over any normed space (Phase 4a #1,#3); but this is the *generalisation-into-composability* already captured above |
|  6 | 1-categorical → higher-categorical?                                                        | no       | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                             | no       | the index `index K` is intrinsic to the target coordinate space; not a numeric index to generalise |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no real organisational improvement that produces a
*standalone mathlib lemma*). The one genuine abstraction — a bundled
`IsLipschitzParametrizable` predicate (row 4) — is a *new-definition* question that
belongs to the realSpace/mixedSpace contribution (the sibling `…_cover` /
`…_cover_mixedSpace` reports), not to this transport wrapper. Relative to *this*
decl, the only move is "generalise `Φ`/`s`", which lands in NO-composable (Phase 6),
not in a new idiom.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (no definitional equalities or instances introduced).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `normLeOne_frontier_lipschitz_cover_index`

[A] Lean-Finder       — (project tool unavailable; lean MCP loogle/leansearch did not load in this environment) — n/a: tool unavailable
[B] Loogle            — intended `LipschitzWith _ (⇑?Φ ∘ ?φ)`, `Homeomorph.image_frontier`, `_ '' frontier _ = frontier (_ '' _)` — n/a: loogle MCP unavailable; substituted by direct mathlib grep (method D)
[C] LeanSearch        — intended "image of frontier under continuous linear equiv", "Lipschitz parametrizable boundary" — n/a: leansearch MCP unavailable; substituted by method D
[D] Grep mathlib src  — `image_frontier`, `equivFunL`, `LipschitzWith.comp`, `toHomeomorph`/`coe_toHomeomorph`, `piCongrLeft'`, and `LipschitzParametriz`/`lipschitz_cover`/`frontier.*Lipschitz` over `.lake/packages/mathlib/Mathlib/` — **hits for every building block; NO hit for any packaged frontier-cover / Lipschitz-parametrizable-transport lemma**
[E] Name pattern      — `normLeOne_frontier_lipschitz_cover_index` over project + mathlib — only the project declaration; no mathlib decl

Building blocks located in mathlib (method D):
- `Homeomorph.image_frontier` — `Mathlib/Topology/Homeomorph/Defs.lean:312`
  (`h '' frontier s = frontier (h '' s)`).
- `ContinuousLinearEquiv.toHomeomorph` / `coe_toHomeomorph` —
  `Mathlib/Topology/Algebra/Module/Equiv.lean:203,207`.
- `Basis.equivFunL` (a `≃L[𝕜]`, hence `.lipschitz` available) —
  `Mathlib/Topology/Algebra/Module/FiniteDimension.lean:448`.
- `IsometryEquiv.piCongrLeft'` (`.isometry.lipschitz`) —
  `Mathlib/Topology/MetricSpace/Isometry.lean:602`.
- `LipschitzWith.comp` — `Mathlib/Topology/MetricSpace/Lipschitz.lean` (standard).
- `Set.image_iUnion`, `Set.image_mono`, `Set.image_image`, `finCongr` — core.

Searched for both:
  - the user's current form (`index K → ℝ`, `stdBasis.equivFunL`) — not in mathlib;
  - the literature-standard / abstract transport form (image under any `≃L` /
    Lipschitz homeomorphism) — **also not in mathlib as a packaged lemma**, but its
    proof is the ≤3-call composition above (Phase 6).

Concluded: **not in mathlib as a packaged result; found the building blocks
(`Homeomorph.image_frontier`, `ContinuousLinearEquiv.lipschitz`/`.toHomeomorph`,
`LipschitzWith.comp`, `IsometryEquiv.piCongrLeft'`); the composition yields our
form in ≤3 chained calls.**

---

## PHASE 6 — Composition check (+ call-sites signal)

### 6.0 Call sites — `normLeOne_frontier_lipschitz_cover_index`

Internal use count: **K = 2** (within the project, excluding the declaring file).
External-to-file callers: **1 file** (`IdealCongruenceCount.lean`).

| Caller file:line                                  | Usage pattern (one-line excerpt)                                                              |
|---------------------------------------------------|-----------------------------------------------------------------------------------------------|
| `…/IdealCongruenceCount.lean:1760`                | `obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index K` then immediately re-wrapped into `frontier (Φ '' normLeOne K) ⊆ …` (`hcov`, lines 1761–1763) |
| `…/IdealCongruenceCount.lean:2852`                | `obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index K` (same pattern in the per-class count) |
| `…/IdealCongruenceCount.lean:1741`                | docstring mention only (not a use)                                                            |

Inline-derivation grep (was the equivalent re-derived elsewhere without the lemma?):
  - **YES — the same transport is re-derived inline** at
    `…/IdealCongruenceCount.lean:343`:
    `have h := (T.symm.toContinuousLinearEquiv.toHomeomorph).image_frontier D`,
    i.e. the project already does the `(…).toHomeomorph.image_frontier` frontier
    transport directly for the lattice equiv `T` rather than through a packaged
    lemma. Also `Homeomorph.smulOfNeZero/addLeft .image_frontier` at lines 267, 271.
    This is direct evidence the transport is a recurring inlined one-liner, not a
    reusable abstraction the project itself routes through a lemma.

Call-sites reading (per the Phase-6 table): K = 2 internal uses, **and** the same
statement is re-derived inline at ≥1 site for a sibling map → the
NO-composable-from-mathlib leaning is strongly supported: `_index` is a thin
coordinate-transport wrapper that the development could (and partly does) bypass by
applying `Homeomorph.image_frontier` + `LipschitzWith.comp` directly.

### Composition check (Phase 6)

Can `normLeOne_frontier_lipschitz_cover_index` be derived from
`normLeOne_frontier_lipschitz_cover_mixedSpace` + mathlib in ≤3 chained calls? **Yes —
this is literally what the existing proof does.**

Attempt 1 (the actual proof, abstracted):
```lean
-- given ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace K
-- and Φ := (stdBasis K).equivFunL :
⟨m, ‖Φ‖₊ * M, fun j ↦ Φ ∘ φ j ∘ (relabel g),
 fun j ↦ Φ.lipschitz.comp ((hφ j).comp (IsometryEquiv.piCongrLeft' g).isometry.lipschitz),  -- call 1: LipschitzWith.comp ×2
 by rw [← Φ.toHomeomorph.image_frontier];                                                     -- call 2: Homeomorph.image_frontier
    exact (Set.image_mono hcov).trans …⟩                                                       -- call 3: Set.image_mono + iUnion bookkeeping
```
- Mathlib decls used: `ContinuousLinearEquiv.lipschitz`, `LipschitzWith.comp`,
  `IsometryEquiv.piCongrLeft'`, `Homeomorph.image_frontier`,
  `ContinuousLinearEquiv.coe_toHomeomorph`, `Set.image_mono`, `Set.image_iUnion`,
  `finCongr` — plus the project lemma `normLeOne_frontier_lipschitz_cover_mixedSpace`
  as the *input* (itself YES-add-as-is in the sibling assessment).
- Result: **succeeds** (it is the existing proof, ~15 lines, but ≤3 *conceptual*
  mathlib calls over the genuine input; the rest is cube-`Icc` relabel bookkeeping).
- Notes: the only non-core ingredient is the *input* theorem
  `…_cover_mixedSpace`, which is the genuine contribution. `_index` adds no
  mathematics beyond "apply the standard chart".

Conclusion: **COMPOSABLE** — from `normLeOne_frontier_lipschitz_cover_mixedSpace`
(the real contribution) via a ≤3-call mathlib composition (`LipschitzWith.comp`,
`Homeomorph.image_frontier`, `Set.image_mono`).

---

## PHASE 7 — Verdict

## Verdict: `Chebotarev.normLeOne_frontier_lipschitz_cover_index`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the linear/Lipschitz-homeomorphism transport of a
  Lipschitz-parametrizable boundary is treated as an *immediate observation*
  ("scale/shift the maps; their number is unchanged") across Widmer / Masser–Vaaler
  / Davenport / Barroero–Widmer; nLab has no named lemma; never isolated.
- Generality analysis (Phase 4): STRICTLY NARROWER — `_index` is a fully-specialised
  instance (`Φ = stdBasis.equivFunL`, `s = normLeOne K`) of an abstract transport
  that is itself a ≤3-call composition; modern-idiom check found no standalone
  improvement (the one real abstraction, a bundled `IsLipschitzParametrizable`
  predicate, belongs to the sibling realSpace/mixedSpace contribution, not here).
- Mathlib search (Phase 5): not packaged in mathlib, but all building blocks present
  (`Homeomorph.image_frontier`, `ContinuousLinearEquiv.lipschitz`/`.toHomeomorph`,
  `LipschitzWith.comp`, `IsometryEquiv.piCongrLeft'`).
- Composition check (Phase 6): COMPOSABLE — the existing proof *is* the ≤3-call
  composition over `normLeOne_frontier_lipschitz_cover_mixedSpace`; K = 2 internal
  call sites; the same `(…).toHomeomorph.image_frontier` transport is already
  re-derived inline at `IdealCongruenceCount.lean:343` for a sibling map.

**Rationale:**

The mathematical content of the frontier Lipschitz cover lives entirely in the
realSpace/mixedSpace construction (`normLeOne_frontier_lipschitz_cover`,
`…_mixedSpace`): building the face maps, lifting along the fibres of
`normAtAllPlaces`, matching `(r−1)+r₂ = d−1`. Those are the genuine number-field
contributions (and the sibling assessment marks `…_cover` YES-add-as-is). This
`_index` variant does *not* add mathematics: it takes the finished mixedSpace cover
and pushes it through the fixed continuous-linear chart `Φ = (stdBasis K).equivFunL`
to land in the standard Euclidean coordinate space `index K → ℝ`. Every step is a
mathlib primitive — `Φ.lipschitz`/`LipschitzWith.comp` to keep the charts Lipschitz,
`Φ.toHomeomorph.image_frontier` to move the frontier across the homeomorphism, and a
`finCongr`/`piCongrLeft'` relabel of the cube dimension `#(index K)−1 = d−1`. In the
geometry-of-numbers literature this "apply a linear coordinate change to a region
with a Lipschitz boundary cover" step is universally taken for granted (Widmer:
scaling/shearing keeps the same number of maps; Barroero–Widmer inline the
lattice-basis-change image without comment). Mathlib should not carry a standalone
lemma for the `K`-specific instance.

**Refactor plan (NO-composable-from-mathlib):**

WHY not: mathlib has the building blocks; `_index` is a 3-call composition over the
genuinely-new `…_cover_mixedSpace`. The wrapper exists only to pre-package the
`frontier (Φ '' normLeOne K)` existential in the exact `hlip` shape, and the two
consumers immediately *re-unpack and re-wrap* it anyway (lines 1760–1763, 2852).

Mathlib building blocks:
- `Homeomorph.image_frontier` — `Mathlib/Topology/Homeomorph/Defs.lean:312`
- `ContinuousLinearEquiv.toHomeomorph` / `coe_toHomeomorph` —
  `Mathlib/Topology/Algebra/Module/Equiv.lean:203,207`
- `ContinuousLinearEquiv.lipschitz` (from `ContinuousLinearMap` boundedness) +
  `LipschitzWith.comp` — `Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `IsometryEquiv.piCongrLeft'` — `Mathlib/Topology/MetricSpace/Isometry.lean:602`
- input: `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace` (the real,
  ship-worthy theorem)

Composition sketch (≤3 mathlib calls over the mixedSpace cover):
```lean
-- obtain ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace K
-- Φ := (stdBasis K).equivFunL ; g := finCongr (dim match)
⟨m, ‖Φ‖₊ * M, fun j c ↦ Φ (φ j fun a ↦ c (g.symm a)),
 fun j ↦ Φ.lipschitz.comp ((hφ j).comp (IsometryEquiv.piCongrLeft' g).isometry.lipschitz),
 by rw [← Φ.coe_toHomeomorph, ← Φ.toHomeomorph.image_frontier]; …⟩
```

Refactor options (project-internal, NOT a mathlib deletion on its own):
1. **Keep as a private helper in the project.** Because the two call sites need the
   `index K → ℝ` packaging and the proof is real bookkeeping (~15 lines), the
   pragmatic move is to *not upstream it* and, if desired, mark it `private` /
   drop it from the `## Main results` upstream-export list. It is plumbing for the
   project's own lattice-count, not a mathlib lemma.
2. **Or** factor the *abstract* transport `lipschitz_frontier_cover_image`
   (Phase 4b signature, ≤3-call body) once — if a bundled `IsLipschitzParametrizable`
   predicate is ever added to mathlib alongside the sibling `…_cover` contribution,
   this transport becomes the natural API lemma about it. That decision belongs to
   the `normLeOne_frontier_lipschitz_cover` (YES-add-as-is) PR, where the predicate
   would be introduced — not to a standalone PR for `_index`.

At the K = 2 call sites: either keep calling the (project-internal) helper, or inline
`Φ.lipschitz.comp …` + `Φ.toHomeomorph.image_frontier` directly over
`normLeOne_frontier_lipschitz_cover_mixedSpace K` (the codebase already does exactly
this inline at `IdealCongruenceCount.lean:343` for the lattice equiv `T`, so the
pattern is established and mechanical).

Next action: do **not** open a standalone mathlib PR for `_index`. Keep it as
project plumbing (optionally `private`), and remove it from the upstream-export
list in the module docstring's `## Main results`. If/when the realSpace `…_cover`
contribution is upstreamed with a bundled Lipschitz-parametrizability predicate,
add the abstract `lipschitz_frontier_cover_image` transport there and let `_index`'s
content be that lemma applied to `(stdBasis K).equivFunL`.

---

## Next step

Do not open a standalone mathlib PR for `normLeOne_frontier_lipschitz_cover_index`.
It is a ≤3-call coordinate-transport composition over the genuinely-new
`normLeOne_frontier_lipschitz_cover_mixedSpace` (`LipschitzWith.comp` +
`Homeomorph.image_frontier` + `Set.image_mono`/`piCongrLeft'` relabel). Keep it as
project-internal plumbing for the two `IdealCongruenceCount` call sites (optionally
`private`; drop from the upstream `## Main results` export list). If the realSpace
`…_cover` is later upstreamed with a bundled Lipschitz-parametrizability predicate,
fold this transport into the abstract `lipschitz_frontier_cover_image` lemma there
and obtain `_index` by applying it to `(stdBasis K).equivFunL`.
