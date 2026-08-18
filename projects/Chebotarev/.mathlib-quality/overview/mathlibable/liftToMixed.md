# /mathlibable report — `Chebotarev.liftToMixed`

_Step-9 overview mathlibable assessment (full workflow). Build is stale (incompatible
olean header), so all reasoning is from source; the ChatGPT-math MCP was down — WebSearch
fallbacks used for the literature channels._

---

### Baseline (Phase 0)
- lake build:               ✗ stale (`incompatible header` on `Mathlib/Order/Filter/Interval.olean`; daily-bump skew). Reasoned from source per task instruction.
- decl `Chebotarev.liftToMixed`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:463`
- kind:                      `def` (`noncomputable`, under `@[expose] public section`)
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — finitely many Lipschitz images of the unit cube `[0,1]^{r-1}` covering the `realSpace`/`mixedSpace` frontier, the boundary-regularity input of Gun–Ramaré–Sivaraman / Widmer / Debaene for the effective lattice-point count.

True qualified name **confirmed**: `Chebotarev.liftToMixed` (namespace `Chebotarev`, opened at line 79; no inner namespace).

---

### Statement (Phase 1)

`Chebotarev.liftToMixed` is a **definition**: a map from the unit cube of the rank-`(d−1)`
coordinate space into the mixed (Minkowski) space `mixedSpace K = ℝ^{r₁} × ℂ^{r₂}` of a number
field `K`, reconstructing a mixed-space point from place-wise **norms + signs + phases**.

Given a number field `K` with `r = #InfinitePlace K` infinite places, signature `(r₁, r₂)`,
degree `d = finrank ℚ K` (`r₁ + 2r₂ = d`, `r = r₁ + r₂`):
- a "cover map" `ψ : (Fin (r−1) → ℝ) → realSpace K` producing modulus/norm values at each place,
- a sign pattern `ε : {w // IsReal w} → Bool`,

`liftToMixed K ψ ε` sends a cube point `c : Fin (d−1) → ℝ`, whose `d−1 = (r−1) + r₂` coordinates
are split by `mixedCubeEquiv K` into `r−1` "modulus" slots (fed to `ψ`) and `r₂` "phase" slots
(one per complex place), to the mixed-space point with
- real place `w`: coordinate `(±1)·ψ(modulus)(w)`, sign from `ε w`;
- complex place `w`: coordinate `ψ(modulus)(w) · exp((2π·θ_w − π)·i)`, with `θ_w` the phase slot.

By construction `normAtAllPlaces (liftToMixed K ψ ε c) = ψ(modulus)` whenever the moduli are
nonnegative — i.e. it is a fibre-wise section of `normAtAllPlaces`, parametrizing the fibre by
signs (real places) and phases (complex places) on top of a chosen norm-profile `ψ`.

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K]` — the number field.
- `ψ`, `ε`, `c` — as above (all explicit, no exotic typeclasses).

Hypotheses: none (it is a total definition; nonnegativity of moduli only matters for the
companion *correctness* lemma, not for the def itself).

Conclusion (math): a parametrization map `[0,1]^{d−1} → mixedSpace K`.
Conclusion (Lean): `mixedSpace K` (i.e. the def has type `… → mixedSpace K`).

---

### Size classification (Phase 2a)

Verdict: **BIG-ish / borderline** — it is a named `def` in a `## Main definitions` list and is
the structural backbone of the file's two `## Main results`. It does **not** introduce a new
*abstract* mathematical structure (no new class/topology/measurability notion); it is a concrete
construction. Recorded as **SMALL-leaning-BIG** for framing.
Reason: listed under `## Main definitions`; underpins the main Lipschitz-cover theorems; but it is
a concrete coordinate construction, not a new named concept.

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **~6 substantive lines** (a `Prod.mk` of two `fun w ↦ …` branches, the complex
branch carrying an `exp((2πθ−π)i)` factor and a `mixedCubeEquiv`-indexed argument split).
One-liner verdict: **MULTI-LINE** — not a one-liner; the Phase-2b exemption table is n/a.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | Lipschitz parametrization boundary fundamental domain number field counting lattice points GRS/Debaene | yes  | "Lipschitz parametrizable boundary" — boundary covered by finitely many Lipschitz cube-images | Gun–Ramaré–Sivaraman JNT 243 (2023) §3.3; "compute the Lipschitz class of the boundary of the fundamental domain"; follows Debaene |
|  2 | WebSearch (general form)         | counting points bounded height number field Lipschitz parametrizable boundary Widmer Schanuel       | yes  | Davenport's "Principle of Lipschitz"; Masser–Vaaler; Widmer Lemma 7.1 | the *abstract* notion: `S ⊂ ℝⁿ` Lip-param of codim `k` if `∃` `M` maps `[0,1]^{n−k}→ℝⁿ` with `‖φ(x)−φ(y)‖ ≤ L‖x−y‖` covering `S` |
|  3 | WebSearch (named-after / aliases)| Davenport "On a Principle of Lipschitz" 1951; "Lipschitz class" Widmer covolume                     | yes  | Davenport 1951 J. London Math. Soc. 26, 179–183; Widmer "Lipschitz class, narrow class, and counting lattice points" | the boundary-regularity hypothesis has Davenport's name attached; the construction reconstructing the point is ad hoc |
|  4 | ChatGPT MCP                      | "standard named object for norm+sign+phase lift to mixed space; natural generality?"                | n/a  | — | MCP down (Codex exec failed). Substituted by channels 1–3, 6, 9. |
|  5 | Local references                 | `.mathlib-quality/references/`, `refs/Chebotarev/`                                                  | n/a  | — | no references / refs dir present (checked: both absent) |
|  6 | nLab                             | polar coordinates                                                                                  | weak | nLab "polar coordinates" exists but brief | confirms `ℂ ≅ [0,∞)×(ℝ/2πℤ)` is the standard polar map; no number-field "lift" object |
|  7 | nCatLab (categorical)            | n/a — not a categorical concept                                                                    | n/a  | — | a concrete coordinate map; no universal property in play |
|  8 | Stacks Project (alg geom)        | n/a — not an algebraic-geometry concept                                                            | n/a  | — | analytic NT / geometry-of-numbers, not scheme theory |
|  9 | MathOverflow / MSE               | (covered via the survey hits in #1–#3, GN "Counting lattice points") generality of the boundary parametrization | yes  | confirms the lift is presented *ad hoc inside the counting argument*, never as a standalone named map | Gorodnik–Nevo, Widmer surveys: "Lipschitz parametrizability of the boundary" is the named *hypothesis*; the reconstructing map is bespoke |
| 10 | recent arXiv (last 5 yrs)        | Heights and morphisms in number fields (2411.13522); Sharp o-minimality & lattice point counting (2503.01731) | yes  | same — Lip-param boundary as a hypothesis; constructions bespoke | modern treatments (o-minimality) replace the explicit cube-lift entirely, confirming it is not a canonical object |

### Literature summary (Phase 3)

Concept identified as: **the explicit Lipschitz parametrization of the boundary of a
norm/height region in a number field's mixed space**, the constructive witness for the
"**Lipschitz parametrizable boundary**" hypothesis of Davenport's Principle of Lipschitz
(Davenport 1951; Masser–Vaaler; Widmer; Debaene; Gun–Ramaré–Sivaraman).

Sources agree on the standard form: **partially**.
- The **abstract hypothesis** ("boundary covered by finitely many `L`-Lipschitz images of the
  unit cube") *is* standard and named (Davenport/Widmer).
- The **specific map** `liftToMixed` (reconstructing a mixed-space point from norms+signs+phases,
  fibrewise over `normAtAllPlaces`) is **never a named standalone object** in the literature — it
  is built ad hoc inside each counting argument, and modern treatments (o-minimality) bypass it.

Most general standard form: the underlying mathematics is the assembly, over infinite places, of
two elementary parametrizations — (a) per complex place, polar `ℂ ≅ [0,∞) × (ℝ/2πℤ)`; (b) per
real place, sign `ℝ ≅ {±1} × [0,∞)` — composed with a chosen norm-profile map `ψ` and an affine
reparametrization of each angle to `[0,1]` (`Arg = 2πθ − π`). Nothing number-field-specific
beyond the *indexing by infinite places*.

Generality dimensions where the literature varies:
  - **ambient space**: literature states the boundary principle for general `S ⊂ ℝⁿ` (Davenport),
    then specializes the *construction* to the mixed space; mathlib would index by `InfinitePlace K`.
  - **angle convention**: `Arg ∈ (−π, π]` (mathlib `Complex.polarCoord`) vs. the affine cube form
    `2πθ − π`, `θ ∈ [0,1]` used here — a cosmetic reparametrization chosen to make the domain a cube.

Disagreement with the literature: none mathematically; the only gap is that the literature has no
*name* for this map, signalling it is argument-internal rather than a reusable primitive.

---

## PHASE 4 — Generality analysis

Literature-standard form (Phase 3): two elementary place-wise parametrizations (complex polar,
real sign) assembled over infinite places, plus a norm-profile `ψ` and an affine angle rescaling.

### Generality status table (Phase 4a)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker / more-general form exists? | Reason |
|---|------------------------|-------------------|--------------------------|-----------------------------------|--------|
| 1 | `[Field K] [NumberField K]` | a number field | none needed — the *map* uses only the index set `InfinitePlace K`, its real/complex split, and `r₁+2r₂=d` | **partly** — the construction proper needs only: a fintype of "places", a `IsReal`/`IsComplex` partition, and the cardinality identity. But it is genuinely tied to number-field data (`mixedSpace`, `mixedCubeEquiv` via `card_add_two_mul_card_eq_rank`). | the `mixedSpace K` codomain and the `(r−1)+r₂ = d−1` bookkeeping are number-field-specific; generalising away from `K` would lose the very identity that makes the cube dimension `d−1` |
| 2 | `ψ : (Fin (r−1)→ℝ) → realSpace K` | arbitrary modulus map | the norm-profile; arbitrary | maximal already (no hypotheses on `ψ` in the def) | the def imposes nothing on `ψ`; correctness (norm round-trip) is a separate lemma's nonnegativity hyp |
| 3 | `ε : {w//IsReal w} → Bool` | sign pattern | `{±1}` per real place | maximal | `Bool`-indexed sign is the natural finite choice |
| 4 | angle scaling `2πθ − π` | affine cube reparametrization of `Arg` | `Arg ∈ (−π,π]` directly (mathlib `Complex.polarCoord`/`polarSpaceCoord`) | a **modern-idiom** alternative exists (use `polarSpaceCoord.symm` + `AddCircle`/`Real.Angle`) | see Phase 4c — the affine form is chosen purely to land in `[0,1]`; mathlib's polar API uses `(−π,π)` |

### Generality verdict (Phase 4b)

The current form is: **NARROWER / BESPOKE than a hypothetical maximally-general "polar+sign lift",
but appropriately specialised to its purpose.** It is *not* over-restricted in its typeclasses in
the usual mathlib sense (no `NormedSpace`-where-`Module`-suffices issue); rather it is **welded to
project-internal scaffolding** (`mixedCubeEquiv`, the `Fin (d−1)`/`Fin (r−1)` index encoding) that
is itself bespoke.
Number of weakening opportunities found: **1 substantive** (the angle convention / use of mathlib's
polar API — see 4c); the typeclass assumptions are essentially forced by the `mixedSpace K` codomain.
Proposed restatement: deferred to 4c (the meaningful restatement is the modern-idiom one).
Cost of restatement: **MODERATE-to-EXPENSIVE** — re-expressing via `polarSpaceCoord.symm` changes
the downstream Lipschitz proof (`lipschitzWith_liftToMixed`) and the membership lemma
(`mem_iUnion_image_liftToMixed_of_eq`), both of which lean on the explicit `exp((2πθ−π)i)` form.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | bundled-hypothesis preamble → typeclasses/instances? | no | — | the inputs (`ψ`, `ε`, `c`) are genuine data, not "let X be a foo" preambles |
| 2 | sequences/metric → filters/topological? | no | — | no limit/sequence here; the Lipschitz statement is already the metric notion that is wanted |
| 3 | construction → universal-property class? | no | — | this is an explicit parametrization with no universal property |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no substructure |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | — | codomain `mixedSpace K` is fixed; nothing to weaken to modules/semirings |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | **partly** | re-express the per-complex-place phase via mathlib's `Complex.polarCoord.symm` / `AddCircle (2π)` and the per-real-place sign so that `liftToMixed = polarSpaceCoord.symm ∘ (assemble ψ, ε, rescale)`; index the cube by `InfinitePlace K`-derived data rather than the bespoke `mixedCubeEquiv`/`Fin` encoding | would let the def **reuse `NumberField.mixedEmbedding.polarSpaceCoord`** (the existing mixed-space polar homeomorphism) and its lemmas, instead of re-deriving `‖uθ‖=1`, the phase Lipschitz bound, and the polar round-trip by hand (`dist_mul_exp_phase_le`, `exists_phase_mem_Icc_mul_exp`) |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, partially** — there is a real organisational improvement in routing
the complex-place phase through mathlib's existing `Complex.polarCoord` / `polarSpaceCoord`
machinery rather than re-implementing the polar round-trip (`exists_phase_mem_Icc_mul_exp`) and the
`2π`-Lipschitz angle bound (`dist_mul_exp_phase_le`) from first principles.
  - Proposed mathlib-idiomatic restatement: a `liftToMixed` whose complex branch is
    `polarSpaceCoord.symm` applied to `(‖·‖ from ψ, angle from θ)` with the angle taken in mathlib's
    `Arg`-convention (and a thin `[0,1] ≃ (−π,π]` affine reindex only if the cube domain is still
    wanted), and whose real branch uses the sign explicitly.
  - Cost: **MODERATE–EXPENSIVE** (the companion proofs must be re-routed through the polar API).
  - Mathlib downstream this enables: reuse of `polarSpaceCoord`'s continuity/measurability and any
    future Lipschitz/`fderiv` lemmas about it; eliminates three bespoke helper lemmas.
  - Real mathematical improvement (not just cosmetic): **yes** — it removes a re-derivation of polar
    coordinates that mathlib already owns, the recurring "users re-implement polar by hand" gap.

**Caveat (honesty bar):** the gain is *organisational*, and it is not free — mathlib's
`polarSpaceCoord` is a partial **homeomorphism aimed at measure-theoretic change-of-variables**, not
a total cube-parametrization, and its `Arg`-convention domain `(−π,π)` is *open*, whereas this
construction deliberately wants the *closed* cube `[0,1]` (so the cover images are compact). Whether
the polar-API routing is actually cleaner for the *Lipschitz/compact-cover* purpose, or whether the
explicit `exp((2πθ−π)i)` form is genuinely better here, is a **judgment call** (see Phase 7).

---

## PHASE 4.5 — Diamond / defeq risk (`def`)

### Risk table (Phase 4.5a)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | no new instance; returns a plain `mixedSpace K` term; no class membership introduced |
| 2 | Reducibility leak | low | not `@[reducible]`; sealed `def`. The companion proofs `rw [liftToMixed]` to unfold deliberately — controlled unfolding, the intended API |
| 3 | Non-canonical unfolding | low | `simp` will not unfold it (no `@[simp]`); only explicit `rw [liftToMixed]` does, as used at lines 498/577 |
| 4 | Instance priority collision | n/a | not an `instance` |
| 5 | Universe-polymorphism issues | none | `K : Type*` but `mixedSpace K` lives in a fixed universe; no polymorphic codomain |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW.** No diamonds, no coercions; the only note is the intended controlled
unfolding via `rw [liftToMixed]`. No mitigation required.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.liftToMixed`

[A] Lean-Finder       (build stale — project Lean tools won't resolve)   n/a: stale build
[B] Loogle            `(_ → realSpace _) → _ → _ → mixedSpace _` shaped   n/a via project; substituted by direct mathlib grep
[C] LeanSearch        "lift realSpace cover map to mixedSpace by signs and phases"   no hit (mathlib index has no such map)
[D] Grep mathlib src  `liftToMixed`, `signAtPlace`, `phaseAt`, `fromNormSignPhase`, `exp.*2.*pi.*theta`   **no hits**
[D'] Grep mathlib src `Lipschitz.*parametriz` / `parametriz.*Lipschitz` / `IsLipschitzParam`   **no hits** (mathlib has no Lipschitz-parametrizable predicate at all)
[E] Name pattern      mixed-space polar/lift names                       FOUND adjacents (below), none equal

**Adjacent mathlib decls found (building blocks, not the map):**
- `NumberField.mixedEmbedding.mixedSpaceOfRealSpace` (`Basic.lean:1118`) — the **zero-phase** lift
  `realSpace → mixedSpace` (identity at real places, `ℝ→ℂ` at complex). No signs, no phases.
- `NumberField.mixedEmbedding.polarSpaceCoord` (`PolarCoord.lean:306`) — polar **partial
  homeomorphism** `mixedSpace ≃ polarSpace = ℝ^{r₁+r₂} × ℝ^{r₂}`, `x ↦ (‖x w‖ or x w, Arg(x w))`;
  `.symm` reconstructs from `(modulus, Arg)` data. Measure-theoretic; `Arg`-convention; no `ψ`, no
  sign-over-real-places packaging, not a cube map.
- `mixedEmbedding.polarCoord`, `polarCoordReal`, `Complex.polarCoord` — the underlying polar pieces.
- `normAtAllPlaces` (`Basic.lean:1172`) — the map `liftToMixed` is a fibre-section of.
- `ZLattice.covolume.tendsto_card_div_pow` / `…tendsto_card_le_div` (`ZLattice/Covolume.lean`) — the
  downstream lattice-count consumers, which take a *bounded measurable set*, **not** a Lipschitz
  cover — confirming mathlib currently has no quantitative-boundary API.
- `NumberField.mixedEmbedding.volume_frontier_normLeOne` (`NormLeOne.lean:868`) — mathlib proves the
  frontier has **measure zero only**; the file's docstring explicitly contrasts this with the
  *stronger* Lipschitz cover it builds.

Searched for both: the user's current form **and** the literature-standard "polar+sign lift" form.
Both absent as a named map.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard form). Mathlib has
the building blocks — `polarSpaceCoord.symm`, `mixedSpaceOfRealSpace`, `Complex.polarCoord`,
`normAtAllPlaces` — and the measure-zero frontier fact, but neither the sign+phase cube-lift nor any
Lipschitz-parametrizable-boundary API.**

---

## PHASE 6 — Composition check (+ call-sites)

### 6.0 Call sites — `Chebotarev.liftToMixed`

Internal use count: **5** (within the project, excluding the def itself), **all inside the same
file** `NormLeOneLipschitz.lean`. External-to-file callers: **0** files.

| Caller (file:line) | Usage pattern (excerpt) |
|--------------------|--------------------------|
| `NormLeOneLipschitz.lean:482` | `LipschitzWith (M₀ + …) (liftToMixed K ψ ε)` — statement of `lipschitzWith_liftToMixed` |
| `NormLeOneLipschitz.lean:498` | `rw [liftToMixed, liftToMixed, Prod.dist_eq]` — unfolding in the Lipschitz proof |
| `NormLeOneLipschitz.lean:562` | `… ⋃ ε, liftToMixed K ψ ε '' Icc 0 1` — statement of `mem_iUnion_image_liftToMixed_of_eq` |
| `NormLeOneLipschitz.lean:577` | `rw [liftToMixed, hproj]` — unfolding in the membership proof |
| `NormLeOneLipschitz.lean:608` | `liftToMixed K (frontierCoverFamily K p.1) p.2 '' Icc 0 1` — the actual frontier cover |
| `NormLeOneLipschitz.lean:636` | `fun p ↦ liftToMixed K (frontierCoverFamily K p.1) p.2` — feeds the main `_mixedSpace` theorem |

Inline-derivation grep (was the same map re-derived elsewhere without `liftToMixed`?): **(none)** —
no other project file re-derives this; the def is the single anchor for the mixed-space cover.

Call-sites signal: **K = 5 internal uses, no inline re-derivation, 0 external** → this is *real
internal API for one self-contained development*, not dead code and not a bypassed wrapper. The
absence of external callers is expected: the whole `ForMathlib/` file is a single not-yet-upstreamed
unit, and `liftToMixed` is its private construction shared across its own companion lemmas.

### Composition check (Phase 6a)

Can `liftToMixed` be reproduced by **≤3 chained mathlib calls** (so it could be inlined rather than
defined)?

Attempt 1: `polarSpaceCoord.symm ∘ (package ‖·‖ from ψ and Arg from θ)`.
  - Mathlib decls: `NumberField.mixedEmbedding.polarSpaceCoord`, `homeoRealMixedSpacePolarSpace`.
  - Result: **partial.** `polarSpaceCoord.symm` reconstructs the *complex* coordinates from
    `(modulus, Arg)` — but (i) it gives **no sign handling** for real places (it passes `x w`
    through directly; the `±` from `ε` must be injected separately), (ii) its angle is `Arg`, so the
    `(2πθ−π)` affine cube reindex is an extra step, and (iii) one must still build the `ψ`-fed
    modulus vector and the `mixedCubeEquiv` coordinate split. That is well over 3 calls and involves
    genuine packaging logic, not a `.symm`/`.trans`/single-application chain.

Attempt 2: `mixedSpaceOfRealSpace`-based.
  - `mixedSpaceOfRealSpace` is the **zero-phase** lift — it cannot produce the
    `exp((2πθ−π)i)` complex phases at all. Fails outright for the phase content.

Conclusion: **NOT-COMPOSABLE** as a ≤3-call inline. The map genuinely bundles three pieces of data
(`ψ` profile, sign pattern `ε`, phase reindex) plus the `mixedCubeEquiv` coordinate bookkeeping;
the result is a real definition, not a trivial composition. (This is a *def*, so "composability"
here means "could be inlined at the 5 call sites" — and it could not, cleanly.)

---

## Verdict: `Chebotarev.liftToMixed`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *boundary-regularity hypothesis* ("Lipschitz parametrizable
  boundary") is standard and named (Davenport 1951 / Widmer / Debaene / GRS), but the *map* itself
  is **never a named standalone object** — it is built ad hoc inside each counting argument, and
  modern (o-minimality) treatments bypass it entirely.
- Generality analysis (Phase 4): typeclasses are essentially forced (BESPOKE, not over-restricted);
  Phase 4c found a **real but non-free** modern-idiom improvement — route the complex phase through
  mathlib's existing `polarSpaceCoord` polar API instead of re-deriving polar coordinates by hand.
- Mathlib search (Phase 5): **not in mathlib**; building blocks present (`polarSpaceCoord.symm`,
  `mixedSpaceOfRealSpace`, `Complex.polarCoord`, `normAtAllPlaces`), and mathlib has only the
  measure-zero frontier (`volume_frontier_normLeOne`), no Lipschitz-cover / Lip-parametrizable API.
- Composition check (Phase 6): **NOT-COMPOSABLE** (≤3 mathlib calls cannot reproduce the
  sign+phase+`ψ`+`mixedCubeEquiv` bundling; cannot be inlined cleanly).

**Rationale.**
`liftToMixed` is genuine, non-trivial, sorry-free internal API (5 call sites, no re-derivation) for
a development that fills a *real* mathlib gap: the **quantitative** Lipschitz regularity of the
`normLeOne` frontier, which mathlib currently knows only up to measure zero
(`volume_frontier_normLeOne`). The mathematics it packages — per-complex-place polar coordinates and
per-real-place signs, assembled over infinite places — is standard, and the *consuming theorem*
(`lipschitzWith_liftToMixed`, feeding the GRS/Widmer/Debaene lattice-count) is exactly the kind of
result mathlib wants. So this is not a NO: mathlib does not have it, and it does not trivially
compose away.

But it is not a clean `YES-add-as-is` either, for two compounding reasons that require human/mathlib-
maintainer judgment. First, the literature deliberately keeps this map **anonymous and
argument-internal**; there is no canonical name or canonical signature for "the norm+sign+phase lift",
and the current signature is welded to project-private scaffolding (`mixedCubeEquiv`, the
`Fin (d−1)`/`Fin (r−1)` cube encoding via `card_add_two_mul_card_eq_rank`) that would need a
deliberate redesign before it reads as a reusable mathlib primitive rather than a bespoke step.
Second, Phase 4c surfaced a real organisational tension: mathlib **already owns** the mixed-space
polar machinery (`polarSpaceCoord`), and a from-scratch `exp((2πθ−π)i)` lift that re-derives the
polar round-trip (`exists_phase_mem_Icc_mul_exp`) and the `2π`-Lipschitz angle bound
(`dist_mul_exp_phase_le`) duplicates it — yet that polar API is an *open-domain measure-theoretic
homeomorphism*, awkward for the *closed-cube compact-cover* purpose here, so it is genuinely unclear
whether the right mathlib form keeps the explicit lift or routes through `polarSpaceCoord`. The cost
of choosing wrong is high (the companion Lipschitz/membership proofs depend on the explicit form).
These are taste/design questions the skill should not resolve unilaterally — hence BORDERLINE.

**Numbered questions for the user (mathlib-maintainer judgment):**

1. **Upstreaming target.** Is the intended mathlib contribution the *whole development*
   (Lipschitz-parametrizable frontier of `normLeOne` → the GRS/Widmer lattice-count input), with
   `liftToMixed` as a supporting `private`/section-local def? If yes, the def likely ships **as-is**
   (support role, not a public primitive) and the verdict collapses to a conditional YES.

2. **Polar-API routing.** Should the complex-place phase be re-expressed through the existing
   `NumberField.mixedEmbedding.polarSpaceCoord` / `Complex.polarCoord` (reusing mathlib's polar
   coordinates, per Phase 4c) rather than the bespoke `exp((2πθ−π)i)` form — accepting a
   MODERATE–EXPENSIVE rewrite of `lipschitzWith_liftToMixed` and `mem_iUnion_image_liftToMixed_of_eq`?
   (yes ⇒ `YES-but-generalise-first`, reason MODERN-IDIOM; no ⇒ keep explicit form.)

3. **Signature redesign.** Is it acceptable to keep the project-private `mixedCubeEquiv` /
   `Fin (d−1)` cube encoding in a mathlib version, or must the cube be indexed by intrinsic
   `InfinitePlace K` data (real-places ⊕ complex-places) before upstreaming? (the latter is the
   cleaner mathlib signature but a non-trivial refactor of the whole file.)

4. **Generality of the consumer, not the def.** Would mathlib rather have a reusable
   **`IsLipschitzParametrizable`-style predicate / boundary API** (which mathlib currently lacks
   entirely) into which this `normLeOne`-frontier result plugs, making `liftToMixed` an internal
   witness? If so, the headline contribution is that predicate, and `liftToMixed` is incidental.

**Next action:** user answers Q1–Q4. Q1=yes + Q2=no ⇒ ship the development with `liftToMixed` as a
support def (effectively `YES-add-as-is`, support role). Q2=yes ⇒ re-aim via `/generalise` to the
`polarSpaceCoord`-routed form first. Re-run `/mathlibable Chebotarev.liftToMixed` after the design
decision to lock the verdict.

---

## Next step

User answers the four numbered questions above (upstreaming target, polar-API routing, cube-index
redesign, predicate-vs-def). Then either commit `liftToMixed` as a support def alongside its
Lipschitz-cover theorems, or run `/generalise Chebotarev.liftToMixed` to re-route through mathlib's
`polarSpaceCoord` before opening a PR.
