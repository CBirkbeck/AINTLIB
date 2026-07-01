module

public import Mathlib

/-!
# Normalisation conventions for the completed Dedekind zeta  (SP1-N)

Fixed **once**, here, so no downstream constant silently drifts by a hidden
`2^{r₂}` / `π^{r₂}` / `√Δ_K` (expert review Q5):

* **Gamma factors** (Deligne's convention, mathlib `Mathlib/Analysis/SpecialFunctions/Gamma/
  Deligne.lean`): `Γℝ(s) = π^{-s/2}·Γ(s/2)`, `Γℂ(s) = 2·(2π)^{-s}·Γ(s)`, related by the
  duplication formula `Γℝ(s)·Γℝ(s+1) = Γℂ(s)` (mathlib `Complex.Gammaℝ_mul_Gammaℝ_add_one`).
  The archimedean factor of `Λ_K` is `gammaFactor K s = Γℝ(s)^{r₁}·Γℂ(s)^{r₂}`.
* **Residue constant**: mathlib's `NumberField.dedekindZeta_residue K` is *definitionally*
  the class-number-formula constant `2^{r₁}·(2π)^{r₂}·R_K·h_K / (w_K·√|Δ_K|)` — the `2^{r₂}`
  bookkeeping is pinned by mathlib itself.
* **Fourier convention of the Belabas–Friedman paper** (eq. (2), audited verbatim
  2026-07-01): `F̂(γ) := ∫ F(t)·e^{itγ} dt` — plus sign in the exponent and **no** `2π`.
  Mathlib's `𝓕` instead has kernel `e^{-2πi·t·w}`. We define the paper's transform as
  `paperFourierIntegral` and prove the exact bridge `F̂(γ) = 𝓕F(-γ/(2π))` once, here.
  All explicit-formula statements (`∑_ρ F̂(γ_ρ)`) use the paper's convention.
-/

namespace DedekindResidue

@[expose] public section

open Complex MeasureTheory NumberField NumberField.InfinitePlace
open scoped Real FourierTransform

/-- The **archimedean gamma factor** of the completed Dedekind zeta function:
`γ_K(s) = Γℝ(s)^{r₁} · Γℂ(s)^{r₂}` in Deligne's normalisation. `Λ_K(s)` will be
`|Δ_K|^{s/2} · γ_K(s) · ζ_K(s)`. -/
noncomputable def gammaFactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

/-- The gamma factor is nonvanishing on the right half-plane `Re s > 0` (each `Γℝ`, `Γℂ`
factor is). -/
theorem gammaFactor_ne_zero_of_re_pos (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 0 < s.re) : gammaFactor K s ≠ 0 := by
  have hbase : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine mul_ne_zero (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)) (pow_ne_zero _ ?_)
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl hbase

/-- Value of the gamma factor at `s = 1`: `γ_K(1) = π^{-r₂}` (since `Γℝ(1) = 1`,
`Γℂ(1) = 1/π`) — the normalisation entering the `Λ_K`-residue bookkeeping. -/
theorem gammaFactor_one (K : Type*) [Field K] [NumberField K] :
    gammaFactor K 1 = (1 / π : ℂ) ^ nrComplexPlaces K := by
  rw [gammaFactor, Gammaℝ_one, Gammaℂ_one, one_pow, one_mul]

/-- The gamma factor written through `Γℝ` only, via the duplication formula
`Γℂ(s) = Γℝ(s)·Γℝ(s+1)`: `γ_K(s) = Γℝ(s)^{r₁+r₂}·Γℝ(s+1)^{r₂}`. -/
theorem gammaFactor_eq_Gammaℝ (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    gammaFactor K s
      = Gammaℝ s ^ (nrRealPlaces K + nrComplexPlaces K) * Gammaℝ (s + 1) ^ nrComplexPlaces K := by
  rw [gammaFactor, pow_add, mul_assoc, ← mul_pow]
  congr 2
  exact (Gammaℝ_mul_Gammaℝ_add_one s).symm

/-- The **paper's Fourier transform** (Belabas–Friedman eq. (2), verbatim convention):
`F̂(γ) := ∫_{-∞}^{+∞} F(t)·e^{itγ} dt` — plus sign, no `2π`. This is the transform appearing
in the explicit formula `∑_ρ F̂(γ_ρ)`; it differs from mathlib's `𝓕` (kernel `e^{-2πitw}`),
see `paperFourierIntegral_eq_fourierIntegral`. -/
noncomputable def paperFourierIntegral (F : ℝ → ℂ) (γ : ℝ) : ℂ :=
  ∫ t : ℝ, F t * Complex.exp (Complex.I * t * γ)

/-- **Convention bridge** (state once, here): the paper's transform is mathlib's `𝓕`
evaluated at `-γ/(2π)`. -/
theorem paperFourierIntegral_eq_fourierIntegral (F : ℝ → ℂ) (γ : ℝ) :
    paperFourierIntegral F γ = 𝓕 F (-γ / (2 * π)) := by
  rw [paperFourierIntegral, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [smul_eq_mul, mul_comm]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end

end DedekindResidue
