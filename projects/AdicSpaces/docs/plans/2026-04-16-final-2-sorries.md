# Plan: Closing the Final 2 Sorries on `tateAcyclicity`

**Date**: 2026-04-16
**Goal**: Make `ValuationSpectrum.tateAcyclicity` fully sorry-free + axiom-clean.

## Current state

After the substantial session progress (10 sorries closed, `LaurentNormalized` typeclass established), the remaining blockers on `tateAcyclicity` are:

1. **S1**: `laurentOverlapBridge_exists_compatible` (LaurentRefinement:3173)
   — needs bivariate Example 6.39 to construct the overlap ring iso.

2. **S2**: `tateAcyclicity` Part 2 (LaurentRefinement:3737)
   — transitively blocked by S1 + `refines_by_standard_cover` + `restrictionMapHom_injective`.

A full closure requires also closing three **upstream** sorries:
- **S3**: `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` (StandardCover:274) — Wedhorn Cor 7.32 / Lemma 7.44.
- **S4**: `restrictionMapHom_injective` (PresheafTateStructure:1238) — Wedhorn Cor 8.32.

**Mathematical route** (following Wedhorn, pp. 82–85): we are proving Theorem 8.28(b) via:
- Lemma 8.33 (Laurent cover exact sequence for a single `f`) — partially scaffolded via `row3_exact` and `laurentCover_gluing_presheaf`.
- Lemma 8.34 (reduce rational covers to Laurent covers) — partially scaffolded via `tateAcyclicity_gluing_via_refinement` and `refines_by_standard_cover`.
- Cor 8.32 (faithful flatness for the Part 1 separation).

## Key Wedhorn references

### Example 6.38 and 6.39 (pp. 82-83)

For `f ∈ A`, `U₁ = R(f/1)`, `U₂ = R(1/f)`, `X = Spa A`:

```
𝒪_X(U₁) = A⟨ζ⟩/(f − ζ)              -- plus half "B₁_gen"
𝒪_X(U₂) = A⟨η⟩/(1 − fη)             -- minus half "B₂_gen"
𝒪_X(U₁ ∩ U₂) = A⟨ζ, η⟩/(f − ζ, 1 − fη)
            = A⟨ζ, η⟩/(f − ζ, 1 − ζη)
            = A⟨ζ, ζ⁻¹⟩/(f − ζ)      -- overlap "B₁₂_gen"
```

The last equality is the KEY: using `ζ · η = 1` (from `1 − ζη = 0` mod the ideal), `η = ζ⁻¹`.

### Lemma 8.33 (Laurent cover exactness, p. 83)

The augmented Čech complex for `{U₁, U₂}`:
```
0 → 𝒪_X(X) --ε--> 𝒪_X(U₁) × 𝒪_X(U₂) --δ--> 𝒪_X(U₁ ∩ U₂) → 0
```
is exact. Proof: diagram chase in
```
0 → A --ι--> A⟨ζ⟩ × A⟨η⟩ --λ--> A⟨ζ, ζ⁻¹⟩ → 0  (1st row, exact)
     ‖          ↓             ↓
     A --ε--> 𝒪_X(U₁) × 𝒪_X(U₂) --δ--> 𝒪_X(U₁ ∩ U₂)  (3rd row)
```
where `λ: (g(ζ), h(η)) ↦ g(ζ) − h(ζ⁻¹)`. Third row = first row modulo the ideals.

### Lemma 8.34 (refinement, p. 84)

Let `T ⊆ A` with `T · A = A`. The rational cover `U = (U_t)_{t∈T}` with `U_t = R(T/t)` is 𝒪_X-acyclic. Proof by induction: reduce to Laurent covers via Cor 7.32 (unit extraction), then apply Lemma 8.33 repeatedly.

### Corollary 8.32 (p. 83)

For a strongly noetherian Tate affinoid ring `A`, `X = Spa A`, and rational cover `(U_i)`:
```
𝒪_X(X) → ∏ᵢ 𝒪_X(Uᵢ)
```
is **faithfully flat**. In particular **injective** ⇒ `restrictionMapHom_injective`.

Proof uses Prop 8.30 (restriction between rational subsets is flat) and product-flat-over-each-factor.

## Phase 1: S1 — Overlap bridge (Example 6.39)

**Target theorem**: `laurentOverlapBridge_exists_compatible` (LaurentRefinement:3173).

**Strategy**: Construct the compatible bridge directly via composition of existing bridges.

### 1a: Observation — overlap = minus applied to plus

We have `laurentOverlapDatum D₀ f = laurentMinusDatum (laurentPlusDatum D₀ f) f`.

So `presheafValue(laurentOverlapDatum D₀ f) = presheafValue(laurentMinusDatum (laurentPlusDatum D₀ f) f)`.

By `laurentMinusBridge` applied to `laurentPlusDatum D₀ f` as base (recursively):
```
presheafValue(laurentMinusDatum (laurentPlusDatum D₀ f) f)
  ≃+* B₂_gen_over_{laurentPlus} ((laurentPlusDatum D₀ f).canonicalMap f)
```
where `B₂_gen_over_B b = B⟨η⟩/(1 − bη)`.

### 1b: Use `laurentPlusBridge` to identify base

By `laurentPlusBridge` at `(D₀, f)`:
```
presheafValue(laurentPlusDatum D₀ f) ≃+* B₁_gen_over_A (D₀.canonicalMap f)
   = A⟨ζ⟩ / (f − ζ)
```

Under this iso, `(laurentPlusDatum D₀ f).canonicalMap f` corresponds to the image of `ζ` (since `f = ζ` mod the ideal). So:
```
B₂_gen_over_{laurentPlus} ((laurentPlusDatum D₀ f).canonicalMap f)
  = (A⟨ζ⟩/(f−ζ))⟨η⟩ / (1 − ζ·η)
```
where in the inner ring, `ζ` is the image.

### 1c: Tensor identification (Example 6.39)

The iso from Wedhorn Example 6.39:
```
(A⟨ζ⟩/(f−ζ))⟨η⟩ / (1 − ζ·η)
  ≃+* A⟨ζ, η⟩ / (f − ζ, 1 − ζη)
  ≃+* A⟨ζ, ζ⁻¹⟩ / (f − ζ)
  = LaurentCover.B₁₂_gen f
```

This is the key algebraic primitive. We need:

**[NEW-T1]** The composition iso `(R/I)⟨η⟩/(1 − r·η) ≃+* R⟨η⟩/(I·R⟨η⟩ + (1 − r·η))` where `r` is the image of `r' ∈ R` (ideal extension).

**[NEW-T2]** `A⟨ζ,η⟩/(f − ζ, 1 − ζη) ≃+* A⟨ζ, ζ⁻¹⟩/(f − ζ)` — send `η ↦ ζ⁻¹`.

### 1d: Verify compatibility

For `τ₁₂ : presheafValue(overlap) ≃+* B₁₂_gen`, the compatibility requires:
- `plus_compat`: `τ₁₂ ∘ restrictionMap(plus → overlap) = posLift ∘ laurentPlusBridge`
- `minus_compat`: `τ₁₂ ∘ restrictionMap(minus → overlap) = negLift ∘ laurentMinusBridge`

These follow from naturality of the chain of isos in 1a–1c.

### 1e: Break-down into tickets

| Ticket | Description | Est. lines |
|---|---|---|
| T-OV-1 | Define `evalBivariateHom : A⟨ζ,η⟩ → presheafValue(overlap)` via `ζ ↦ canonicalMap f`, `η ↦ (canonicalMap f)⁻¹` (in presheafValue(minus) side) | 50 |
| T-OV-2 | Show `ker(evalBivariateHom) ⊇ (f − ζ, 1 − fη)` | 30 |
| T-OV-3 | Factor through the quotient, get `τ₁₂ : A⟨ζ,η⟩/(f − ζ, 1 − fη) → presheafValue(overlap)` | 20 |
| T-OV-4 | Show `τ₁₂` is an iso (via the inverse from `laurentMinus ∘ laurentPlus` composition) | 80 |
| T-OV-5 | Compose with `A⟨ζ,η⟩/(f − ζ, 1 − ζη) ≃ A⟨ζ,ζ⁻¹⟩/(f − ζ)` (Mathlib? — check) | 40 |
| T-OV-6 | Verify `plus_compat` (naturality of the plus-embedding) | 40 |
| T-OV-7 | Verify `minus_compat` (naturality of the minus-embedding) | 40 |
| T-OV-8 | Package as `laurentOverlapBridge_exists_compatible` | 10 |

**Total estimate**: ~310 new lines, split across 8 tickets.

## Phase 2: S3 — Nullstellensatz refinement (Lemma 8.34 step)

**Target**: `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` (StandardCover:274).

**Strategy**: Wedhorn Lemma 8.34(ii) — given a rational cover generated by a finite set `T = (f₀,...,fₙ)` with `T·A = ⊤` and nonempty base rational open, produce `S = {s⁻¹f₁, ..., s⁻¹fₙ}` for a unit `s ∈ A^×` satisfying the covering/containment/span-top conditions.

Key input: **Corollary 7.32** — for `X = Spa A` compact, a finite family `(f_i)` with no common zero admits a unit `s ∈ A^×` dominating: for all `x ∈ X` there exists `i` with `x(s) < x(f_i)`.

### 2a: Break-down

| Ticket | Description | Est. lines |
|---|---|---|
| T-NULL-1 | Port Wedhorn Cor 7.32 (extraction of dominating unit) to Lean | 100 |
| T-NULL-2 | Define the Zavyalov candidate family `{s⁻¹f_i}` via `RationalCovering` data | 40 |
| T-NULL-3 | Prove `refines_cover` (every Spa-point lands in some plus-piece) | 80 |
| T-NULL-4 | Prove `refines_contain` (each plus-piece ⊆ some `C` piece) | 60 |
| T-NULL-5 | Prove `refines_span_top` (the `{s⁻¹f_i}` span A) | 30 |
| T-NULL-6 | Assemble as `exists_nullstellensatz_refinement_of_rationalOpen_nonempty` | 20 |

**Total estimate**: ~330 new lines.

## Phase 3: S4 — restrictionMapHom injectivity (Cor 8.32)

**Target**: `restrictionMapHom_injective` (PresheafTateStructure:1238).

**Strategy**: Use Wedhorn Cor 8.32 and the existing Prop 8.30 (`restrictionMap_flat`).

Prop 8.30: `𝒪_X(V) → 𝒪_X(U)` is flat for rational `U ⊆ V`.

Cor 8.32 (by induction on cover size + Lemma 8.33 for Laurent cover case):
- Base: trivial cover = `{X}`, identity is faithfully flat.
- Step: given a rational cover, reduce to Laurent cover, apply Lemma 8.33 exactness.

### 3a: Break-down

| Ticket | Description | Est. lines |
|---|---|---|
| T-INJ-1 | Port Wedhorn Prop 8.30 (flatness of single restriction) | 120 |
| T-INJ-2 | Cor 8.32 via Laurent induction (uses Lemma 8.33) | 150 |
| T-INJ-3 | `restrictionMapHom_injective` as corollary of faithful flatness | 40 |

**Total estimate**: ~310 new lines.

## Phase 4: S2 — Final tateAcyclicity Part 2 assembly

Once S1, S3, S4 are closed, `tateAcyclicity` Part 2 is a mechanical combination:

```lean
intro f hcompat
-- Get the standard-cover refinement
obtain ⟨S, hS_cover, hS_contain⟩ :=
  RationalCovering.refines_by_standard_cover C hne
-- Build V_covers from S and τ: V → C
let V_covers : Finset (RationalLocData A) := ...  -- plus-pieces at S
let τ : {D // D ∈ V_covers} → {E // E ∈ C.covers} := ... -- from hS_contain
-- Apply tateAcyclicity_gluing_via_refinement
exact tateAcyclicity_gluing_via_refinement C V_covers ... τ ... f hcompat
  (by induction on S.elts.card using laurentCover_gluing_presheaf)
```

**Estimate**: ~50 lines, mechanical once dependencies land.

## Execution order

**Phase A (parallel)**:
- S3 (T-NULL-1 ... T-NULL-6) — separate file, completely independent
- S4 (T-INJ-1 ... T-INJ-3) — separate file, depends on Lemma 8.33 (already scaffolded)

**Phase B (serial, after A)**:
- S1 (T-OV-1 ... T-OV-8) — requires existing plus/minus bridges
- S2 (final assembly) — requires all above

**Parallelism**: up to 3 workers for Phase A. Phase B is serial (single file).

## Risk assessment

- **S1** (overlap bridge): Bivariate quotient constructions in Lean can have subtle reduction issues. The composition of bridges might require careful universe polymorphism. Estimated risk: **medium**.
- **S3** (Nullstellensatz): The Cor 7.32 unit extraction is deeply dependent on Wedhorn's Cor 7.32 (valuation trichotomy). If Cor 7.32 itself isn't in our project, we need to port it too. Estimated risk: **high**.
- **S4** (injectivity): Prop 8.30 requires `Module.Flat` and mathlib's flatness API for quotients. Lemma 8.31 is already proved. Estimated risk: **medium**.
- **S2** (final assembly): Once deps land, this is mechanical. Estimated risk: **low**.

## Incremental approach: this session

Given the scale (~950 new lines across 17 tickets), this session will likely make PARTIAL progress. The most impactful starting point is:

1. **Attempt S1 T-OV-1 through T-OV-3**: The forward direction of the overlap bridge (no inverse yet). If this lands, we have `τ₁₂` as a ring hom (not yet iso). Even this is progress.

2. **Add helper API for bivariate Tate algebra**: `evalHomBounded` for `A⟨ζ,η⟩` — this is a reusable primitive.

3. **Defer S3, S4 to later sessions**: These are substantial mathematical content that deserves their own focus.
