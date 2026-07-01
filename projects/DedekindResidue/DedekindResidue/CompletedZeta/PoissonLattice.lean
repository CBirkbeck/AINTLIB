module

public import Mathlib
public import DedekindResidue.CompletedZeta.DualLattice
public import DedekindResidue.CompletedZeta.PoissonSummation

/-!
# Poisson summation over a general `ℤ`-lattice  (SP1-AGP, leaf P.3)

Transport of the `ℤ^ι` Poisson formula (`tsum_eq_tsum_fourier_zpoint`) to an arbitrary
`ℤ`-lattice `L ⊂ EuclideanSpace ℝ ι`: conjugate by the linear equivalence sending the standard
lattice to `L`. The Fourier side transforms by the **`GL` change-of-variables law**
(`fourier_comp_linearEquiv`, new to this development: mathlib only has the isometry case
`Real.fourier_comp_linearIsometry`), the dual lattice appears via `dualZLattice_eq_span`
(P.1), and the covolume factor via `ZLattice.covolume_eq_det_mul_measureReal`.

## Main results (this file)
* `DedekindResidue.fourier_comp_linearEquiv` —
  `𝓕(g ∘ T) w = |det T|⁻¹ • 𝓕 g ((T⁻¹)^* w)` for `T ∈ GL(EuclideanSpace ℝ ι)`.
* (in progress) `DedekindResidue.tsum_eq_tsum_fourier_zlattice` — Poisson over `L`:
  `∑'_{v ∈ L} g(v) = covol(L)⁻¹ • ∑'_{w ∈ L♯} 𝓕g(w)`.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory Complex
open scoped FourierTransform

variable {ι : Type*} [Fintype ι]

/-- **Fourier transform under a linear change of variables** (`GL` version; mathlib has only
the isometry case). For an invertible linear `T` on Euclidean space,
`𝓕(g ∘ T) w = |det T|⁻¹ · 𝓕 g ((T⁻¹)^* w)`, by the substitution `v ↦ T⁻¹ v` (Haar scaling
`|det T|⁻¹`) and moving `T⁻¹` across the pairing to its adjoint. -/
theorem fourier_comp_linearEquiv
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (g : EuclideanSpace ℝ ι → ℂ)
    (w : EuclideanSpace ℝ ι) :
    𝓕 (fun v => g (T v)) w
      = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • 𝓕 g (LinearMap.adjoint (T.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) w) := by
  classical
  have hdet : LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 :=
    (LinearEquiv.isUnit_det' T).ne_zero
  set eT : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
    T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv with heT
  have hfun : (⇑eT : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      = ⇑(T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) := rfl
  have hmap : Measure.map (⇑eT) (volume : Measure (EuclideanSpace ℝ ι))
      = ENNReal.ofReal |(LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
        • volume := by
    rw [hfun]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hsub : ∀ F : EuclideanSpace ℝ ι → ℂ,
      ∫ v, F (T v) = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • ∫ y, F y := by
    intro F
    have h1 : ∫ v, F (T v) = ∫ y, F y ∂(Measure.map (⇑eT) volume) :=
      (integral_map_equiv eT F).symm
    rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  rw [Real.fourier_eq', Real.fourier_eq']
  have key := hsub (fun y => Complex.exp
    ((↑(-2 * Real.pi * inner ℝ (T.symm y) w) : ℂ) * Complex.I) • g y)
  simp only [LinearEquiv.symm_apply_apply] at key
  rw [key]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  have hadj : inner ℝ y ((LinearMap.adjoint
        (T.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) w)
      = inner ℝ (T.symm y) w := by
    rw [LinearMap.adjoint_inner_right]
    rfl
  rw [hadj]

end

end DedekindResidue
