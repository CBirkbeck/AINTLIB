# Inventory: ./HasseWeil/FormalGroup/InvariantDiff.lean

**Import:** `HasseWeil.FormalGroup.Differential`

**Module header:** Packages `FormalGroup.invariantDiff` into a formal structure and proves Silverman IV.4.2 (every invariant differential is a scalar multiple of ω_F, uniqueness of the normalized differential) and IV.4.3 (chain rule for formal group homs).

**set_option:** `set_option linter.dupNamespace false` (line 35; suppresses the linter warning from namespace nesting, no mathematical relevance)

---

## Declarations

### `structure InvariantDifferential`
- **Type**: `(F : FormalGroup R) → Type*` with fields `toSeries : PowerSeries R` and `mul_dX_isConstant : ∃ c : R, toSeries * F.dX_at_zero = PowerSeries.C c`
- **What**: A power series `P(T)` together with a proof that `P(T) · F_X(0,T)` is a constant; this is the algebraic packaging of Silverman's invariant differential (Def + Prop IV.4.2).
- **How**: Pure structure definition; no proof work. The field `mul_dX_isConstant` is a `Prop` (proof-irrelevant), which enables the `@[ext]` lemma.
- **Hypotheses**: `R : CommRing`; `F : FormalGroup R`.
- **Uses from project**: `FormalGroup.dX_at_zero` (via `F.dX_at_zero`)
- **Used by**: every declaration in this file
- **Visibility**: public
- **Lines**: 51–55 (structure body)
- **Notes**: none

---

### `noncomputable def InvariantDifferential.scalar`
- **Type**: `(η : InvariantDifferential F) → R`
- **What**: Extracts the scalar `a ∈ R` as the constant coefficient `[T^0](η.toSeries)`.
- **How**: Direct application of `PowerSeries.constantCoeff`.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: none (uses mathlib `PowerSeries.constantCoeff`)
- **Used by**: `toSeries_mul_dX_at_zero`, `toSeries_eq_scalar_smul`, `IsNormalized`, `isNormalized_iff`, `eq_smul_normalized`
- **Visibility**: public
- **Lines**: 62–63 (1-line body)
- **Notes**: keyApi — used by 5+ other declarations in this file

---

### `theorem InvariantDifferential.toSeries_mul_dX_at_zero`
- **Type**: `(η : InvariantDifferential F) → η.toSeries * F.dX_at_zero = PowerSeries.C η.scalar`
- **What**: Makes the defining constant explicit: the product of the invariant differential with `F_X(0,T)` equals `C(η.scalar)`.
- **How**: Destructs `mul_dX_isConstant` to get `c`, identifies `η.scalar = c` by applying `PowerSeries.constantCoeff` to both sides (using `F.dX_at_zero_constantCoeff` to reduce the `F.dX_at_zero` factor to 1).
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: `FormalGroup.dX_at_zero_constantCoeff`
- **Used by**: `toSeries_eq_scalar_smul`
- **Visibility**: public
- **Lines**: 66–73 (7-line proof)
- **Notes**: none

---

### `theorem InvariantDifferential.toSeries_eq_scalar_smul`
- **Type**: `(η : InvariantDifferential F) → η.toSeries = η.scalar • F.invariantDiff`
- **What**: Every invariant differential is a scalar multiple of the canonical `F.invariantDiff`; this is the main content of Silverman IV.4.2.
- **How**: Calc proof: inserts `1 = F.dX_at_zero * F.invariantDiff` (via `FormalGroup.dX_at_zero_mul_invariantDiff`), rearranges by associativity, applies `toSeries_mul_dX_at_zero`, then uses the mathlib identity `PowerSeries.smul_eq_C_mul` to convert `C(a) * f = a • f`.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: `FormalGroup.dX_at_zero_mul_invariantDiff`, `InvariantDifferential.toSeries_mul_dX_at_zero`
- **Used by**: `isNormalized_iff`, `eq_smul_normalized`
- **Visibility**: public
- **Lines**: 78–88 (8-line proof)
- **Notes**: none

---

### `def InvariantDifferential.IsNormalized`
- **Type**: `(η : InvariantDifferential F) → Prop` defined as `η.scalar = 1`
- **What**: Predicate stating that an invariant differential is normalized (its constant coefficient equals 1).
- **How**: One-line definition using `scalar`.
- **Hypotheses**: none beyond structure
- **Uses from project**: `InvariantDifferential.scalar`
- **Used by**: `isNormalized_iff`, `normalizedDifferential_isNormalized`, `normalizedDifferential_unique`, `normalizedDifferential_unique'`
- **Visibility**: public
- **Lines**: 92–93 (1-line body)
- **Notes**: keyApi — used by 4 other declarations in this file

---

### `theorem InvariantDifferential.isNormalized_iff`
- **Type**: `(η : InvariantDifferential F) → η.IsNormalized ↔ η.toSeries = F.invariantDiff`
- **What**: Characterizes normalization: `η` is normalized iff its underlying series is exactly `F.invariantDiff`.
- **How**: Forward: use `toSeries_eq_scalar_smul` and rewrite the scalar to 1 by the hypothesis, then `one_smul`. Backward: apply `FormalGroup.invariantDiff_constantCoeff` (which says `[T^0](F.invariantDiff) = 1`) after substituting the series.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: `InvariantDifferential.toSeries_eq_scalar_smul`, `InvariantDifferential.scalar`, `FormalGroup.invariantDiff_constantCoeff`
- **Used by**: `normalizedDifferential_unique`
- **Visibility**: public
- **Lines**: 96–104 (7-line proof)
- **Notes**: none

---

### `noncomputable def FormalGroup.normalizedDifferential`
- **Type**: `(F : FormalGroup R) → InvariantDifferential F`
- **What**: Constructs the canonical normalized invariant differential `ω_F`, whose underlying series is `F.invariantDiff`.
- **How**: Sets `toSeries := F.invariantDiff` and proves `mul_dX_isConstant` using `FormalGroup.invariantDiff_mul_dX_at_zero` (which shows `F.invariantDiff * F.dX_at_zero = 1 = C(1)`).
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: `FormalGroup.invariantDiff`, `FormalGroup.invariantDiff_mul_dX_at_zero`
- **Used by**: `normalizedDifferential_isNormalized`, `normalizedDifferential_unique`, `eq_smul_normalized`, `invariantDifferential_chain`, `normalizedDifferential_unique'`
- **Visibility**: public
- **Lines**: 111–116 (3-line body incl. inline proof)
- **Notes**: keyApi — used by 5 other declarations in this file

---

### `theorem FormalGroup.normalizedDifferential_isNormalized`
- **Type**: `(F : FormalGroup R) → F.normalizedDifferential.IsNormalized`
- **What**: Proves `ω_F` is normalized, i.e., its constant coefficient equals 1.
- **How**: One-line: `F.invariantDiff_constantCoeff` (the project lemma stating `[T^0](F.invariantDiff) = 1`) directly gives the goal `F.normalizedDifferential.scalar = 1`.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: `FormalGroup.invariantDiff_constantCoeff`
- **Used by**: unused in file (used externally in `Logarithm.lean`, `CharP.lean`)
- **Visibility**: public
- **Lines**: 118–120 (1-line proof)
- **Notes**: none

---

### `theorem FormalGroup.normalizedDifferential_unique`
- **Type**: `(F : FormalGroup R) → {η : InvariantDifferential F} → η.IsNormalized → η.toSeries = F.normalizedDifferential.toSeries`
- **What**: Uniqueness at the level of underlying series: any normalized invariant differential has the same series as `ω_F`.
- **How**: Applies `InvariantDifferential.isNormalized_iff` (forward direction) and unfolds `normalizedDifferential.toSeries` to `F.invariantDiff`.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`, `η.IsNormalized`.
- **Uses from project**: `InvariantDifferential.isNormalized_iff`
- **Used by**: `normalizedDifferential_unique'`
- **Visibility**: public
- **Lines**: 125–128 (1-line proof)
- **Notes**: none

---

### `theorem InvariantDifferential.eq_smul_normalized`
- **Type**: `{F : FormalGroup R} → (η : InvariantDifferential F) → ∃! a : R, η.toSeries = a • F.normalizedDifferential.toSeries`
- **What**: Every invariant differential equals a unique scalar multiple of `ω_F`; this is the full statement of Silverman IV.4.2.
- **How**: Witnesses `η.scalar` using `toSeries_eq_scalar_smul`. Uniqueness: from `η.toSeries = b • F.invariantDiff`, apply `PowerSeries.constantCoeff` to both sides, use `FormalGroup.invariantDiff_constantCoeff` to simplify to `b = η.scalar`.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: `InvariantDifferential.scalar`, `InvariantDifferential.toSeries_eq_scalar_smul`, `FormalGroup.invariantDiff_constantCoeff`, `FormalGroup.normalizedDifferential`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–145 (12-line proof)
- **Notes**: none

---

### `theorem FormalGroupHom.invariantDifferential_chain`
- **Type**: `{F G : FormalGroup R} → (f : FormalGroupHom F G) → PowerSeries.subst f.toSeries G.normalizedDifferential.toSeries * PowerSeries.derivative R f.toSeries = PowerSeries.C (PowerSeries.coeff 1 f.toSeries) * F.normalizedDifferential.toSeries`
- **What**: Silverman IV.4.3 (chain rule): for a formal group hom `f : F → G`, the pullback of `ω_G` along `f` (i.e., `ω_G(f(T)) · f'(T)`) equals `f'(0) · ω_F`.
- **How**: One-line delegation to `FormalGroup.invariantDiff_chain` (the underlying series-level chain rule proved in `Differential.lean`), which does all the work.
- **Hypotheses**: `R : CommRing`, `F G : FormalGroup R`, `f : FormalGroupHom F G`.
- **Uses from project**: `FormalGroup.invariantDiff_chain`, `FormalGroup.normalizedDifferential`
- **Used by**: unused in file (used externally in `CharP.lean`)
- **Visibility**: public
- **Lines**: 154–160 (1-line proof)
- **Notes**: none

---

### `@[ext] theorem InvariantDifferential.ext`
- **Type**: `{F : FormalGroup R} → {η₁ η₂ : InvariantDifferential F} → η₁.toSeries = η₂.toSeries → η₁ = η₂`
- **What**: Extensionality: two invariant differentials are equal iff their underlying series agree (proof-irrelevance handles the `mul_dX_isConstant` prop field).
- **How**: `cases η₁; cases η₂; congr` — destructs to fields, then `congr` eliminates the goal using `congr` on the structure fields; the `Prop` field is equal by proof irrelevance.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`.
- **Uses from project**: none
- **Used by**: `normalizedDifferential_unique'`
- **Visibility**: public (tagged `@[ext]`)
- **Lines**: 168–170 (1-line proof)
- **Notes**: tagged `@[ext]`, enabling `ext` tactic on `InvariantDifferential`

---

### `theorem FormalGroup.normalizedDifferential_unique'`
- **Type**: `(F : FormalGroup R) → (η : InvariantDifferential F) → η.IsNormalized → η = F.normalizedDifferential`
- **What**: Strong uniqueness: any normalized invariant differential equals `F.normalizedDifferential` as a term of type `InvariantDifferential F` (not just the underlying series).
- **How**: Applies `InvariantDifferential.ext` to reduce to the series level, then invokes `normalizedDifferential_unique`.
- **Hypotheses**: `R : CommRing`, `F : FormalGroup R`, `η.IsNormalized`.
- **Uses from project**: `InvariantDifferential.ext`, `FormalGroup.normalizedDifferential_unique`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 179–182 (1-line proof)
- **Notes**: none

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `InvariantDifferential` (structure) | all |
| `scalar` | `toSeries_mul_dX_at_zero`, `toSeries_eq_scalar_smul`, `IsNormalized`, `isNormalized_iff`, `eq_smul_normalized` |
| `toSeries_mul_dX_at_zero` | `toSeries_eq_scalar_smul` |
| `toSeries_eq_scalar_smul` | `isNormalized_iff`, `eq_smul_normalized` |
| `IsNormalized` | `isNormalized_iff`, `normalizedDifferential_isNormalized`, `normalizedDifferential_unique`, `normalizedDifferential_unique'` |
| `isNormalized_iff` | `normalizedDifferential_unique` |
| `normalizedDifferential` | `normalizedDifferential_isNormalized`, `normalizedDifferential_unique`, `eq_smul_normalized`, `invariantDifferential_chain`, `normalizedDifferential_unique'` |
| `normalizedDifferential_isNormalized` | **unused in file** |
| `normalizedDifferential_unique` | `normalizedDifferential_unique'` |
| `eq_smul_normalized` | **unused in file** |
| `invariantDifferential_chain` | **unused in file** |
| `ext` | `normalizedDifferential_unique'` |
| `normalizedDifferential_unique'` | **unused in file** |

**keyApi** (3+ internal callers): `scalar` (5 callers), `IsNormalized` (4 callers), `normalizedDifferential` (5 callers).
