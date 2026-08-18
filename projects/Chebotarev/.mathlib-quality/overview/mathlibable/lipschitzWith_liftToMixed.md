# /mathlibable report — `Chebotarev.lipschitzWith_liftToMixed`

_Step-9 mathlibable assessment (AINTLIB /overview). Single declaration, full workflow._

## Baseline (Phase 0)

- lake build:               ⚠ not run (local build stale per task brief; reasoned from source + the mathlib tree at the project pin under `.lake/packages/mathlib`)
- decl `Chebotarev.lipschitzWith_liftToMixed`:  ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:479`
- namespace:                 `Chebotarev` (opens line 79, `end Chebotarev` line 673) ⇒ qualified name **`Chebotarev.lipschitzWith_liftToMixed`** (VERIFIED from source — author-supplied parse confirmed)
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the `mixedSpace`/`realSpace` frontier of the norm-`≤ 1` cone is covered by finitely many Lipschitz images of the unit cube `[0,1]^{r-1}`. This is the Gun–Ramaré–Sivaraman §3.3 (after Debaene) Lipschitz-boundary input, feeding the Widmer/Lang (GTM 110) boundary-cell lattice-point count.

---

## Statement (Phase 1)

`Chebotarev.lipschitzWith_liftToMixed` is a theorem giving a **global Lipschitz bound for the lift
`liftToMixed K ψ ε`** of a `realSpace K`-valued cube-cover map `ψ` to a `mixedSpace K`-valued map.

The lift `liftToMixed K ψ ε c` (def at line 463) sends a cube point `c : Fin (finrank ℚ K − 1) → ℝ`
to the mixed-space point whose:
- real-place coordinate `w` is `±(ψ …) w` (sign `ε w`), and
- complex-place coordinate `w` is `(ψ …) w · exp((2π θ_w − π) i)`, the modulus `(ψ …) w` paired with
  a phase `θ_w` read off the last `r₂` cube coordinates (via `mixedCubeEquiv`).

The theorem states: if `ψ` is `M₀`-Lipschitz (`hψ : LipschitzWith M₀ ψ`) and uniformly norm-bounded
by `B` on its image (`hB : ∀ c, ‖ψ c‖ ≤ B`), then for every sign pattern `ε`, the lift
`liftToMixed K ψ ε` is **`(M₀ + (B·2π).toNNReal)`-Lipschitz** as a map
`(Fin (finrank ℚ K − 1) → ℝ) → mixedSpace K`.

Mathematically: lifting a Lipschitz, bounded modulus-cover across the fibres of `normAtAllPlaces`
(real fibres = sign choices, complex fibres = circle of phases) produces a Lipschitz map, with
constant the modulus Lipschitz constant `M₀` plus the phase contribution `B·2π` (the circle has
radius ≤ `B`, the phase reparametrization is `2π`-Lipschitz).

Variables / typeclasses involved (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — the base number field (file-level `variable`, line 124).
- `ψ : (Fin (Fintype.card (InfinitePlace K) − 1) → ℝ) → realSpace K` — the `realSpace`-valued cover map.
- `M₀ : ℝ≥0`, `B : ℝ` — the Lipschitz constant and the uniform bound of `ψ`.
- `ε : {w : InfinitePlace K // IsReal w} → Bool` — the real-place sign pattern.

Hypotheses (Lean side):
- `hψ : LipschitzWith M₀ ψ` — the modulus cover is `M₀`-Lipschitz.
- `hB : ∀ c, ‖ψ c‖ ≤ B` — the modulus cover is uniformly bounded by `B`.

Conclusion (math): the fibre-lift `liftToMixed K ψ ε` is `(M₀ + B·2π)`-Lipschitz on the cube domain.

Conclusion (Lean):
```lean
LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (liftToMixed K ψ ε)
```

The proof (≈45 lines): reduces via `LipschitzWith.of_dist_le_mul`; splits the mixed-space product
distance with `Prod.dist_eq` + `max_le` + `dist_pi_le_iff` into real-place and complex-place
coordinates; on real places uses sign cancellation (`abs (±1) = 1`) to reduce to `ψ`'s Lipschitz
bound `M₀`; on complex places applies the file's per-place phase-modulus bound `dist_mul_exp_phase_le`
(`dist (a·uθc) (b·uθd) ≤ ‖a‖·(2π·dist θc θd) + dist a b`), then bounds `‖a‖ ≤ B`, the phase distance
by the cube distance, and the modulus distance by `M₀·dist c d`, assembling the NNReal constant
`M₀ + (B·2π).toNNReal` by `Real.coe_toNNReal` + `ring`.

---

## Size classification (Phase 2a)

Verdict: **SMALL** (helper) — but borderline, see note.
Reason: a helper `theorem`, not a `def`/`class`/`structure`, not itself listed under `## Main
results`, not named after a person/place. It is the Lipschitz-bound lemma feeding the cover.

Note: it is *upstream of* and *essential to* the file's genuine main results
(`normLeOne_frontier_lipschitz_cover_mixedSpace`, `…_index`) — it is the single quantitative-regularity
engine of the mixed-space cover. So while structurally a helper, its mathematical content is the load-
bearing step of the file's headline theorems. (Literature width is EXHAUSTIVE regardless; BIG/SMALL is
framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` ⇒ **n/a**. The one-line-definition negative-signal
check does not apply to theorems (and the proof body is ≈45 substantive lines regardless).

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                       | Hit? | Standard form found                                                                                  | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Lipschitz polar coordinate map modulus phase product estimate dist a u b v norm"                            | partial | polar/quasipolar: `‖(a u) − (b v)‖` bounded via modulus + angular variable; bi-Lipschitz in polar coords | no standalone named theorem; the estimate `dist(au,bv) ≤ ‖a‖·dist u v + ‖v‖·dist a b` is the textbook product split |
|  2 | WebSearch (general form / domain) | "number field mixed embedding fundamental domain frontier Lipschitz parametrization lattice point counting Widmer" | yes  | Widmer's *Lipschitz class*: a set is Lipschitz-parametrizable if `∂S` is covered by finitely many Lipschitz images of `[0,1]^{n−1}`; lift over `ℝ^{r₁} × ℂ^{r₂}` | **exactly this file's setup**; treated as standard machinery, never a named lemma |
|  3 | WebSearch (named-after / source)  | "Debaene counting ideals number field Lipschitz parametrizable boundary fundamental domain complex places phases" | yes  | Debaene/GRS partition the fundamental parallelepiped in any degree; show the domain is of Lipschitz class; complex places contribute phase coordinates | the fibre-lift over complex-place phases is the GRS §3.3 / Debaene construction, used inline |
|  4 | WebSearch (mathlib building block) | "mathlib LipschitzWith.prod_mk LipschitzWith on Pi types iff each coordinate Lipschitz lipschitzWith_pi"     | yes  | `lipschitzWith_pi` (Lipschitz into a Pi type ⇔ each coordinate Lipschitz); `LipschitzWith.prodMk` | the *combinators* the proof uses exist; the *assembled lift bound* does not |
|  5 | WebSearch (concept history)        | `"Lipschitz" map "well-defined" general form arbitrary metric space concept history Bourbaki`               | yes  | Lipschitz map = `ρ(f x, f y) ≤ C·d(x,y)` over any metric spaces; composition multiplies constants    | confirms the maximally general home of "Lipschitz constant of a lift" is generic metric spaces — but the *lift itself* is number-field-specific |
|  6 | ChatGPT MCP                      | self-contained 3-part question (standard form / maximal generality / mathlib-worthiness)                    | n/a  | —                                                                                                    | MCP **down** per task brief; substituted by WebSearch #1–#5 + nLab #7 + the source-paper lineage (GRS arXiv:1611.10103, Widmer Narrow_Lipschitz.pdf, Debaene-line arXiv:2604.19681 / hal-03805062) |
|  7 | nLab                             | "Lipschitz map" → ncatlab.org/nlab/show/Lipschitz+map (from #5 hits)                                          | yes  | composition rule `Lip(g∘h) ≤ Lip(g)·Lip(h)`; product/coproduct metrics; uniformly continuous          | gives the abstract composition/product principles the proof instantiates; no "fibre-lift Lipschitz bound" as a named result |
|  8 | nCatLab (categorical)            | —                                                                                                           | n/a  | —                                                                                                    | not a categorical concept (a concrete number-field metric estimate); nLab #7 covers the abstract content |
|  9 | Stacks Project (alg geom)        | —                                                                                                           | n/a  | —                                                                                                    | not an algebraic-geometry concept (analytic geometry-of-numbers boundary estimate) |
| 10 | MathOverflow / Math.SE           | (folded into #1/#2 — "Lipschitz parametrizability of fundamental domains / counting lattice points")        | yes  | same as #2 — Masser–Vaaler / Widmer Lipschitz-class counting principle; routine boundary input        | no controversy; the lift is bookkeeping inside the counting argument |
| 11 | recent arXiv (last 5 yrs)        | surfaced by #2/#3: GRS *Counting ideals in ray classes* (hal-03805062), *Explicit counting of ideals in arbitrary degree* (arXiv:2604.19681), Widmer *Lipschitz class, narrow class* | yes | the lattice/ideal counting lineage builds the cube-cover lift per-paper; it is **infrastructure**, never extracted as a reusable theorem | confirms: no source states "the lift of a bounded Lipschitz modulus-cover is Lipschitz" as a standalone lemma |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality levels (specific product/polar estimate;
  the domain-standard Lipschitz-class counting form; named-after Debaene/GRS source; the mathlib
  building-block combinators; concept history). ✓
- ChatGPT MCP attempted; server down (documented), substituted by WebSearch #1–#5 + nLab #7 + the
  primary-source lineage (GRS / Widmer / Debaene). ✓ (with caveat)
- Local references checked → n/a (no `projects/Chebotarev/.mathlib-quality/references/` directory). ✓
- nLab checked → hit (#7). ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: the **Lipschitz-regularity of the fibre-lift of a cube-cover map across the
fibres of the place-norm map `ℝ^{r₁} × ℂ^{r₂} → ℝ^{r}`** — i.e. the complex-place-phase lift in the
Widmer / Masser–Vaaler / Debaene / Gun–Ramaré–Sivaraman *Lipschitz-class* boundary-regularity machinery
for counting lattice points / ideals in number fields.
Sources agree on the standard form: **yes on the surrounding machinery, but as a *technique*, not a
named theorem.** Every source (Widmer *Lipschitz class, narrow class*; GRS arXiv:1611.10103 §3.3;
Debaene-line arXiv:2604.19681 / hal-03805062) needs "the boundary is Lipschitz-parametrizable" and
builds the cube-cover lift *inline*; none isolates "lift of a bounded `M₀`-Lipschitz modulus-cover is
`(M₀ + B·2π)`-Lipschitz" as a reusable statement.
Most general standard form: the *abstract* fact is generic — "a Lipschitz map composed/producted with
bounded Lipschitz data is Lipschitz, with the constants adding/multiplying" (nLab #7; mathlib's
`lipschitzWith_pi` + `LipschitzWith.comp` + the product-distance split). The *concrete* object
`liftToMixed K ψ ε` is number-field-specific (its type mentions `InfinitePlace K`, `realSpace K`,
`mixedSpace K`, `IsReal`/`IsComplex`, `mixedCubeEquiv`).
Generality dimensions where the literature varies:
  - the ambient space: literature uses `ℝ^{r₁} × ℂ^{r₂}` (Minkowski/mixed space); fully standard, matches
    mathlib's `mixedSpace K`.
  - the cover map `ψ`: each paper supplies a concrete face/box parametrization; ours is abstracted to
    "any `M₀`-Lipschitz, `B`-bounded `ψ`" — already the clean general hypothesis.
  - the constant: `M₀ + B·2π` is the natural modulus-plus-phase split; not a quantity the literature
    names (the papers only need *some* Lipschitz constant, not the sharp value).
Disagreement with the literature: **none** — this is a faithful, slightly-abstracted Lean rendering of
the GRS/Debaene complex-place-phase lift. The novelty is the formalisation + the explicit constant, not
the mathematics.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): "the fibre-lift of a bounded Lipschitz cube-cover across the
place-norm fibres of `ℝ^{r₁} × ℂ^{r₂}` is Lipschitz" — but stated only *as a technique* on the concrete
mixed space, never extracted. The maximally general *abstract* principle ("Pi/Prod of bounded Lipschitz
data is Lipschitz, constants add") is already mathlib's `lipschitzWith_pi` + `LipschitzWith.comp` +
product-distance API.

### Generality status table — `Chebotarev.lipschitzWith_liftToMixed`

| # | Parameter / hypothesis            | Current Lean form                                        | Literature-standard form                              | Weaker / more-general form exists? | Reason it can/can't be generalised |
|---|-----------------------------------|----------------------------------------------------------|-------------------------------------------------------|------------------------------------|-------------------------------------|
| 1 | base field `K`                    | `[Field K] [NumberField K]`                              | number field (Minkowski space `ℝ^{r₁}×ℂ^{r₂}`)         | NO                                 | the entire statement is *about* the number-field mixed embedding; the type mentions `InfinitePlace K`, `realSpace K`, `mixedSpace K`. Cannot abstract `K` away without dissolving the theorem. |
| 2 | the lift target                   | `liftToMixed K ψ ε : mixedSpace K`                       | the concrete complex-place-phase lift                  | NO                                 | `liftToMixed` is a project def referencing `mixedCubeEquiv`, `IsReal`/`IsComplex` places. The statement is inseparable from it. |
| 3 | modulus cover `ψ`                 | arbitrary `M₀`-Lipschitz, `B`-bounded                    | a concrete face/box parametrization (per source)       | already maximally abstract         | the hypotheses `LipschitzWith M₀ ψ` + `∀ c, ‖ψ c‖ ≤ B` are *already* the cleanest abstraction — strictly more general than any single source's concrete `ψ`. ✓ |
| 4 | sign pattern `ε`                  | arbitrary `{w // IsReal w} → Bool`                        | the real-place sign choices in the fibre              | already general                    | quantified over all `ε`; no narrowing. ✓ |
| 5 | the constant `M₀ + (B·2π).toNNReal` | sharp modulus-plus-phase split                          | literature needs only *some* constant                  | n/a (an improvement, not a narrowing) | the explicit `M₀ + B·2π` is *stronger* than what sources state; not a generality deficit. |

The hypotheses on `ψ` (rows 3–4) are already the maximally clean abstraction. The *non-generalisable*
core (rows 1–2) is that the **statement's type is built from project-only definitions** — it is not a
narrowness to weaken, it is the theorem's reason for existing.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within its setting** — but the setting itself is irreducibly
project-specific (the type mentions `liftToMixed`, `mixedSpace K`, `InfinitePlace K`).
Number of weakening opportunities found: **0** that keep the theorem meaningful. The `ψ`-hypotheses are
already abstracted to "any bounded Lipschitz cover"; the field/space/lift are load-bearing and cannot be
removed.
Proposed restatement: **none** as a mathlib *addition in this shape* — the statement cannot be lifted
out of the project because its type depends on `liftToMixed` and the mixed-embedding API. (See Phase 6
for the one genuinely-extractable abstract sub-fact.)
Cost of restatement: n/a (no restatement of *this* statement is possible without the project defs).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                         | no       | — | the hypotheses are already `LipschitzWith`/`‖·‖ ≤ B`, the right idioms |
|  2 | sequences/metric where filters/topological generalise?                                                      | no       | — | `LipschitzWith` is already the correct metric idiom; nothing sequential |
|  3 | construct an object where a universal-property class would characterise it?                                 | no       | — | nothing constructed here (this is a property of `liftToMixed`, which the def already built) |
|  4 | set-with-closure-predicate → bundled substructure?                                                          | no       | — | n/a |
|  5 | vector-space/field-specific result that typeclass hierarchy weakens?                                        | partial  | the *abstract* core (Pi/Prod of bounded Lipschitz data is Lipschitz) lives over generic (pseudo)metric/normed spaces | but that abstract core is **already in mathlib** (`lipschitzWith_pi`, `LipschitzWith.comp`, product-distance); see Phase 6 |
|  6 | 1-categorical statement with higher-categorical generalisation?                                             | no       | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) generalisable to additive groups/monoids?                                            | no       | — | the index `Fin (finrank ℚ K − 1)` and place-indexed products are intrinsic to the number-field setting |

Modern idiom available: **no** (as a mathlib *addition*). The only "modernisation" move is to recognise
that the abstract skeleton (a map into a `Prod`/`Pi` is Lipschitz when each block is, with constants
combining) is *already* mathlib's `lipschitzWith_pi` + `LipschitzWith.comp` + `dist_pi_le_iff` —
i.e. the proof already *uses* the modern idiom internally. There is no organisational improvement to
ship as a new declaration; the number-field-specific wrapper around those combinators is exactly what
`liftToMixed` + this lemma are. One-line reason: the contemporary-idiom content is mathlib's existing
Lipschitz-on-products API, which the proof already invokes — nothing new to extract at the project level.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (introduces no definitional equality or typeclass-search path).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.lipschitzWith_liftToMixed`

[A] Lean-Finder       n/a — lean_local_search / AI-index tools not available in this env; substituted by direct mathlib-tree grep [D] + WebSearch-backed loogle/leansearch [B][C]
[B] Loogle (web/type) `LipschitzWith _ (liftToMixed _ _ _)` and `LipschitzWith _ _ → LipschitzWith _ _ → LipschitzWith _ (Prod.mk _ _)` → the *target* shape (`liftToMixed`) has no hit (project def); the *abstract* product/Pi shape hits `lipschitzWith_pi`, `LipschitzWith.prodMk`, `LipschitzWith.comp`
[C] LeanSearch        (folded into WebSearch #4) "LipschitzWith on Pi/Prod iff each coordinate Lipschitz" → `lipschitzWith_pi`; "Lipschitz lift mixed embedding number field" → nothing
[D] Grep mathlib src  in `.lake/packages/mathlib/Mathlib/`: `liftToMixed`, `mixedCubeEquiv`, `frontierCoverFamily`, `normLeOne.*[Ll]ipschitz` → **zero hits** (all are project-only). Building blocks present: `LipschitzWith.of_dist_le_mul` (`Mathlib/Topology/MetricSpace/Lipschitz.lean:50`), `dist_pi_le_iff` (via `Mathlib/Topology/EMetricSpace/Pi.lean` family / `edist_pi_le_iff`), `lipschitzWith_smul`/`dist_smul_le` (`Mathlib/Analysis/Normed/MulAction.lean:48–55`), `dist_mul_mul_le` (`Mathlib/Analysis/Normed/Group/Uniform.lean:231`), `lipschitzWith_circleMap` (`Mathlib/MeasureTheory/Integral/CircleIntegral.lean:139`)
[E] Name pattern      `liftToMixed`, `lipschitzWith_lift*`, `lipschitz.*[Mm]ixed`, `lipschitz.*normLeOne` in the mathlib tree → **no hits**

Searched for both:
  - the user's current form (`LipschitzWith (M₀ + (B·2π).toNNReal) (liftToMixed K ψ ε)`): **not in
    mathlib** — and *cannot* be, since `liftToMixed` / `mixedSpace`-frontier-cover machinery is entirely
    project-local (mathlib has `normLeOne` and `volume_frontier_normLeOne` measure-zero, but **not** the
    quantitative Lipschitz cover; that is exactly what this file adds).
  - the literature-standard / abstract form ("Pi/Prod of bounded Lipschitz data is Lipschitz"):
    **found as building blocks** — `lipschitzWith_pi`, `LipschitzWith.comp`, `dist_pi_le_iff`,
    `lipschitzWith_smul`, `dist_mul_mul_le` — but assembled here into a number-field-specific lift bound
    that mathlib does not (and structurally cannot, without `liftToMixed`) contain.

Concluded: **not in mathlib** (all methods exhausted, plus the abstract form). The *combinator* building
blocks are present; the *assembled lift Lipschitz bound* and its host construction `liftToMixed` are not.
Note: mathlib *does* have the surrounding `normLeOne` API (`NumberField.mixedEmbedding.normLeOne`,
`volume_frontier_normLeOne`) — but only the **measure-zero** frontier fact, not the **quantitative
Lipschitz cover**, which is the whole point of this `ForMathlib/` file.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `Chebotarev.lipschitzWith_liftToMixed`

Internal use count (outside the declaring file): **0**
External-to-file callers: **0 distinct files**

| Caller file:line                                            | Usage pattern (one-line excerpt)                                                   |
|-------------------------------------------------------------|-------------------------------------------------------------------------------------|
| NormLeOneLipschitz.lean:639 (SAME declaring file)           | `fun j ↦ lipschitzWith_liftToMixed (hψ := hM₀ _) (hB := hB _) (ε := _), ?_⟩`        |

So `K = 0` external/cross-file uses; **exactly one** use, inside the same file, in
`Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace` (line 619, a genuine `## Main result`), where
it supplies the per-chart Lipschitz constant `M₀ + (B·2π).toNNReal` for the mixed-space cover.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `lipschitzWith_liftToMixed`?):
  - (none) — no other site re-proves a Lipschitz bound for `liftToMixed`. It is the unique engine.

Call-sites signal: `K = 1` internal use only (same file), but that one use is in the file's headline
theorem `normLeOne_frontier_lipschitz_cover_mixedSpace`. This is **not** a redundant wrapper bypassed by
consumers — it is the indispensable quantitative step. The signal is "essential internal API for a main
result", which (unlike a bypassed wrapper) does **not** lean NO-composable on its own; the
composability question is decided by Phase 6a below.

### Composition check (Phase 6)

Can `Chebotarev.lipschitzWith_liftToMixed` be derived from mathlib in ≤3 chained calls?

Attempt 1 (try to assemble from mathlib's Lipschitz-on-products combinators directly):
The lift is a `Prod` of a real-place `Pi`-map and a complex-place `Pi`-map. One would want
`LipschitzWith.prodMk` over `(lipschitzWith_pi …)` for each block. But:
  - the **real** block needs per-place sign cancellation `dist (±yc) (±yd) = dist yc yd` (`abs (±1)=1`)
    and the reduction `dist yc yd ≤ M₀·dist c d` *through the cube-coordinate restriction*
    `c ↦ ψ (c ∘ (mixedCubeEquiv).symm ∘ Sum.inl)` — itself a composition with a coordinate projection;
  - the **complex** block needs the per-place product/phase estimate
    `dist (a·uθc) (b·uθd) ≤ ‖a‖·(2π·dist θc θd) + dist a b` (the file's `dist_mul_exp_phase_le`, resting
    on `dist_mul_le_norm_mul_dist` + `lipschitzWith_phase` + `‖uθ‖ = 1`), then `‖a‖ ≤ B`, phase-distance
    ≤ cube-distance, modulus-distance ≤ `M₀·dist c d`;
  - then the two block constants `M₀` and `M₀ + B·2π` must be reconciled into the single `max` constant
    `M₀ + (B·2π).toNNReal` via NNReal coercion arithmetic (`Real.coe_toNNReal`, `NNReal.coe_add`, `ring`).
  - Mathlib decls that *would* be used: `LipschitzWith.of_dist_le_mul`, `dist_pi_le_iff`, `Prod.dist_eq`,
    `lipschitzWith_circleMap` (inside `lipschitzWith_phase`), `dist_pi_le_iff` again, `gcongr`.
  - Result: **fails as a ≤3-call composition.** This is ~45 lines: a `max_le` split, two
    `dist_pi_le_iff` reductions, sign cancellation, an `if`-`split_ifs`, the phase-modulus estimate,
    three `gcongr` bound-chasings, and the NNReal constant `ring`/`calc`. It is a genuine proof, not a
    `.comp`/`.trans`/single-application chain.

Attempt 2 (delegate to a hypothetical mathlib "Pi of bounded Lipschitz is Lipschitz" packaged lemma):
No such packaged lemma with the *modulus·phase* constant split exists in mathlib (Phase 5). Even with
`lipschitzWith_pi`, the per-complex-place summand is `a·exp(iθ)` (a *product* of two varying quantities,
not an isometry/`smul` by a constant), so it needs the bilinear product-distance estimate
`dist_mul_le_norm_mul_dist` — which mathlib **does not** have in the norm-weighted form (mathlib's
`dist_mul_mul_le` is the additive triangle form `dist(a₁a₂)(b₁b₂) ≤ dist a₁ b₁ + dist a₂ b₂`, no norm
weighting). So even the inner estimate is not an off-the-shelf mathlib call.
  - Result: **partial at best**, and what is missing (`dist_mul_le_norm_mul_dist` in norm-weighted form,
    plus the whole assembly) is itself new work.

Conclusion: **NOT-COMPOSABLE.** The statement is irreducibly tied to the project def `liftToMixed`, and
its proof is a real ≈45-line argument, not a ≤3-call mathlib composition. (The *one* genuinely-reusable
abstract sub-lemma — `dist_mul_le_norm_mul_dist`, the norm-weighted product-distance estimate at line
362 — is mathlib-gap-worthy in its own right, but that is a **separate declaration**, not
`lipschitzWith_liftToMixed`.)

---

## Verdict: `Chebotarev.lipschitzWith_liftToMixed`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the fibre-lift-over-complex-phases is the Widmer / Masser–Vaaler /
  Debaene / Gun–Ramaré–Sivaraman *Lipschitz-class* boundary-regularity **technique** for counting
  lattice points / ideals in number fields — ubiquitous in the area, but **never extracted as a named
  reusable theorem**; each source builds the cube-cover lift inline.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within its setting (the `ψ`-hypotheses are already the
  clean "any bounded Lipschitz cover" abstraction; 0 meaningful weakenings), but the setting itself is
  irreducibly project-specific — the statement's *type* is built from `liftToMixed`, `mixedSpace K`,
  `InfinitePlace K`, which are project-only.
- Mathlib search (Phase 5): **not in mathlib** (and structurally cannot be in this shape without
  `liftToMixed`). Mathlib has `normLeOne` + `volume_frontier_normLeOne` (measure-zero) but **not** the
  quantitative Lipschitz cover; the combinator building blocks (`lipschitzWith_pi`, `LipschitzWith.comp`,
  `dist_pi_le_iff`) are present but not assembled into this bound.
- Composition check (Phase 6): **NOT-COMPOSABLE** — ≈45-line proof, `K = 1` internal use that is the
  engine of a genuine `## Main result`; not a ≤3-call composition.

**Rationale.** This theorem sits in the awkward-but-common spot where the *statement* is not mathlibable
as written, yet the *mathematics* is exactly a piece of established infrastructure mathlib is missing.
The statement cannot be PR'd in this shape: its type names `liftToMixed K ψ ε`, a bespoke construction
referencing `mixedCubeEquiv`, `IsReal`/`IsComplex` places, and the place-indexed `mixedSpace K`. So the
literal answer to "should mathlib have `Chebotarev.lipschitzWith_liftToMixed`?" is no — but only because
the question is mis-scoped. The real question is whether mathlib should host the **whole `liftToMixed`
+ `frontierCoverFamily` + `normLeOne_frontier_lipschitz_cover*` ecosystem** — the quantitative
Lipschitz-boundary cover of the norm-`≤ 1` cone in the mixed embedding. That ecosystem *is* a genuine
mathlib gap: mathlib already has `normLeOne` and proves its frontier has measure zero
(`volume_frontier_normLeOne`), and the entire purpose of this `ForMathlib/` file is to supply the
*stronger, quantitative* regularity (finitely-many Lipschitz cube images) that the Widmer/Lang
lattice-point count needs — a natural and well-motivated extension of mathlib's existing
canonical-embedding API. Whether to upstream it is a **parent-def + main-results decision** (does mathlib
want the `liftToMixed`/cover ecosystem at all, under what names, in `NumberTheory/NumberField/
CanonicalEmbedding/`?), not a decision about this helper in isolation. The verdict therefore depends on a
scope judgment the skill cannot make alone: the helper rides on its parent's fate.

Two further facts sharpen the call. (i) `lipschitzWith_liftToMixed` is genuinely NOT-COMPOSABLE and is
the engine of two real main results — so it is *not* a deletable wrapper (contrast the sibling
`lipschitzWith_phase`, a fully-pinned `circleMap` specialisation that *is* NO-composable). If the
`liftToMixed` ecosystem goes to mathlib, this lemma goes **with it, essentially as-is**. (ii) The one
sub-fact inside it that *is* independently mathlibable — `dist_mul_le_norm_mul_dist` (line 362), the
norm-weighted product-distance estimate `dist(a·u)(b·v) ≤ ‖a‖·dist u v + ‖v‖·dist a b` over a normed
field, which mathlib lacks (it only has the additive `dist_mul_mul_le`) — should be split out and PR'd
separately regardless of the ecosystem decision. That split is an action item the human should confirm.

**Numbered questions (≤5):**

  1. **Scope of the upstreaming.** Do you intend to upstream the *whole* `normLeOne` quantitative
     Lipschitz-cover ecosystem (`liftToMixed`, `mixedCubeEquiv`, `frontierCoverFamily`,
     `normLeOne_frontier_lipschitz_cover{,_mixedSpace,_index}`) into mathlib's
     `NumberTheory/NumberField/CanonicalEmbedding/`, as the quantitative companion to the existing
     `volume_frontier_normLeOne`? (If yes, `lipschitzWith_liftToMixed` ships *with* it, essentially
     as-is — it is the engine and is NOT-COMPOSABLE. If no — the result stays project-local — then it
     is not a standalone mathlib candidate, because its type depends on project-only defs.)

  2. **Reviewer signalling.** The mathlib canonical-embedding file already contains `normLeOne` and its
     measure-zero frontier. Is there a maintainer/Zulip consensus that the *quantitative* Lipschitz
     boundary (Widmer/Debaene-style) is wanted upstream, or is the measure-zero version considered
     sufficient for mathlib's current purposes? (This determines whether Q1's "yes" is realistic.)

  3. **Split the reusable sub-lemma now?** Independently of Q1: should `dist_mul_le_norm_mul_dist`
     (the norm-weighted product-distance estimate over a `NormedField`, currently line 362 — a clean,
     general, genuinely-missing mathlib analytic lemma) be extracted and PR'd to
     `Mathlib/Analysis/Normed/...` on its own, regardless of the ecosystem decision? (Strong YES-leaning
     from the analysis; mathlib has only the additive `dist_mul_mul_le`.)

  4. **Constant sharpness as API.** If upstreamed, is the explicit constant `M₀ + (B·2π).toNNReal` the
     intended public API value, or would mathlib prefer the existence form `∃ M, LipschitzWith M …`
     (matching the cover theorems' `∃ M` shape) — i.e. is the sharp constant worth pinning in the
     signature, or is it bookkeeping that should be hidden?

Next action: user answers Q1–Q2 (the scope/appetite call) and Q3 (the independent split). If Q1 = yes,
re-run `/mathlibable` (or proceed to `/cleanup` + `/generalise`) on the **parent def `liftToMixed`** and
the main result `normLeOne_frontier_lipschitz_cover_mixedSpace` as the real PR unit, with
`lipschitzWith_liftToMixed` riding along. If Q1 = no, the result stays project-local and is dropped from
standalone mathlib consideration — but Q3 (`dist_mul_le_norm_mul_dist`) should still be actioned as its
own small PR.

---

## Next step

BORDERLINE — the verdict hinges on a scope decision the skill cannot make alone. The literal statement is
not mathlibable in isolation (its type depends on the project def `liftToMixed`), but it is the
NOT-COMPOSABLE engine of a genuine mathlib gap (the quantitative Lipschitz-boundary cover of `normLeOne`,
the Widmer/Debaene companion to mathlib's existing measure-zero `volume_frontier_normLeOne`). Answer
Q1–Q4: principally, **do you intend to upstream the whole `liftToMixed`/cover ecosystem?** If yes, this
lemma ships with it as-is; if no, it stays project-local. Independently, split out
`dist_mul_le_norm_mul_dist` (Q3) as its own small mathlib PR — that sub-lemma is cleanly general and
genuinely missing from mathlib.
