module

public import Mathlib

/-!
# `n`-dimensional Poisson summation for the Gaussian class  (SP1-AGP, leaf P.2)

Mathlib has one-dimensional Poisson summation (`Real.tsum_eq_tsum_fourier`) and the
multivariate **torus Fourier series** (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`),
but **no** `n`-dimensional / lattice Poisson summation formula. This file builds it for the
standard lattice `ℤ^ι ⊂ EuclideanSpace ℝ ι`, in the shape needed for the Hecke theta
transformation: `∑_{n∈ℤ^ι} g(n) = ∑_{m∈ℤ^ι} 𝓕g(m)`.

The engine mirrors the one-dimensional proof in mathlib's `PoissonSummation.lean`: the only
genuinely new lemma is that the `m`-th coefficient of the torus-periodization of `g` is the
value of the Fourier transform `𝓕g` at the lattice point `m` (`mFourierCoeff_periodization`,
the analogue of `Real.fourierCoeff_tsum_comp_add`). Poisson then falls out of the multivariate
torus Fourier series evaluated at `0`.

## Main results (this file)
* `DedekindResidue.summable_gaussian_zlattice` — the Gaussian `x ↦ exp(-a‖x‖²)` (`a > 0`) is
  summable over any `ℤ`-lattice in `EuclideanSpace ℝ ι` (dominated by a summable power via
  `ZLattice.summable_norm_rpow`). This drives every convergence hypothesis downstream.
* `DedekindResidue.zpoint` — the standard embedding `ℤ^ι ↪ EuclideanSpace ℝ ι`.
* `DedekindResidue.tsum_eq_tsum_fourier_zpoint` — `n`-dimensional Poisson over `ℤ^ι`
  *(in progress)*.

See `.mathlib-quality/substrate-api.md` §C/§E for the torus-Fourier footholds.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped Real FourierTransform

variable {ι : Type*} [Fintype ι]

/-- The standard embedding of the integer lattice `ℤ^ι` into `EuclideanSpace ℝ ι`. -/
noncomputable def zpoint (n : ι → ℤ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => (n i : ℝ))

/-- **Gaussian summability over a lattice.** For `a > 0`, the Gaussian `x ↦ exp(-a‖x‖²)` is
summable over any `ℤ`-lattice `L ⊂ EuclideanSpace ℝ ι`. Proof: it is eventually dominated (as
`‖x‖ → ∞`, which happens cofinitely on the lattice since sub-level sets are finite) by
`‖x‖^{-d-1}`, which is summable by `ZLattice.summable_norm_rpow`. -/
theorem summable_gaussian_zlattice (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) :
    Summable (fun z : L => Real.exp (-a * ‖(z : EuclideanSpace ℝ ι)‖ ^ 2)) := by
  classical
  have hfin : Module.finrank ℤ (↥L) = Fintype.card ι := by
    rw [ZLattice.rank ℝ L, finrank_euclideanSpace]
  have hrlt : (-(Fintype.card ι : ℝ) - 1) < -(Module.finrank ℤ (↥L) : ℝ) := by
    rw [hfin]; linarith
  have hpow := ZLattice.summable_norm_rpow L (-(Fintype.card ι : ℝ) - 1) hrlt
  -- Gaussian is `o(t^{-d-1})` at infinity, so eventually `≤` it.
  have hbound : ∀ᶠ t : ℝ in atTop,
      Real.exp (-a * t ^ 2) ≤ t ^ (-(Fintype.card ι : ℝ) - 1) := by
    have h := rexp_neg_quadratic_isLittleO_rpow_atTop (a := -a) (by linarith) 0
      (-(Fintype.card ι : ℝ) - 1)
    simp only [neg_mul, zero_mul, add_zero] at h
    filter_upwards [h.eventuallyLE, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    calc Real.exp (-a * t ^ 2) = ‖Real.exp (-(a * t ^ 2))‖ := by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring_nf
      _ ≤ ‖t ^ (-(Fintype.card ι : ℝ) - 1)‖ := ht
      _ = t ^ (-(Fintype.card ι : ℝ) - 1) := by
            rw [Real.norm_rpow_of_nonneg htpos.le, Real.norm_eq_abs, abs_of_pos htpos]
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound
  -- Sub-level set `{z : L | ‖z‖ ≤ R}` is finite (lattice ∩ ball, proper space).
  have hcl : IsClosed (L : Set (EuclideanSpace ℝ ι)) := by
    rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete
  have hlevel : {z : L | ‖(z : EuclideanSpace ℝ ι)‖ ≤ R}.Finite := by
    have hfb : (Metric.closedBall 0 R ∩ (L : Set (EuclideanSpace ℝ ι))).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall hcl
    refine Set.Finite.of_finite_image (hfb.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by simpa using hz, z.2⟩
  refine Summable.of_norm_bounded_eventually hpow ?_
  rw [Filter.eventually_cofinite]
  refine hlevel.subset (fun z hz => ?_)
  simp only [Set.mem_setOf_eq]
  by_contra hlt
  rw [not_le] at hlt
  exact hz (by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hR _ hlt.le)

/-- **`n`-dimensional Poisson summation over `ℤ^ι`** (SP1-AGP P.2). For a continuous `g` on
`EuclideanSpace ℝ ι` whose lattice translates are locally summable and whose Fourier transform
is summable over `ℤ^ι`, `∑_{n} g(n) = ∑_{m} 𝓕g(m)`. Assembled from the multivariate torus
Fourier series and `mFourierCoeff_periodization`. -/
theorem tsum_eq_tsum_fourier_zpoint {g : C(EuclideanSpace ℝ ι, ℂ)}
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
        Summable fun n : ι → ℤ =>
          ‖(g.comp (ContinuousMap.addRight (zpoint n))).restrict K‖)
    (h_sum : Summable fun m : ι → ℤ => 𝓕 (⇑g) (zpoint m)) :
    ∑' n : ι → ℤ, g (zpoint n) = ∑' m : ι → ℤ, 𝓕 (⇑g) (zpoint m) := by
  sorry

end

end DedekindResidue
