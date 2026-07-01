module

public import Mathlib
public import DedekindResidue.CompletedZeta.DualLattice
public import DedekindResidue.CompletedZeta.PoissonSummation
public import DedekindResidue.CompletedZeta.PoissonLattice

/-!
# The lattice Gaussian theta function and its transformation law  (SP1-AGΘ)

For a `ℤ`-lattice `L ⊂ EuclideanSpace ℝ ι` the **theta function**
`Θ_L(t) := ∑_{v ∈ L} e^{-π t ‖v‖²}` (`t > 0`) satisfies the **inversion law**

`Θ_L(t) = covol(L)⁻¹ · t^{-n/2} · Θ_{L♯}(1/t)`,

the standard lattice theta transformation (Neukirch, *Algebraic Number Theory*, VII §3;
the 1-D case is mathlib's `jacobiTheta` functional equation). It is the Gaussian
instantiation of the lattice Poisson formula `tsum_eq_tsum_fourier_zlattice` (P.3): mathlib's
`fourier_gaussian_innerProductSpace` at `b = πt` gives `𝓕 g_t(w) = t^{-n/2} e^{-π‖w‖²/t}`,
and `summable_gaussian_zlattice` discharges the convergence hypotheses.

This is the analytic engine of the Hecke functional-equation route (SP1-AGE → SP1-FE):
applied to the ideal lattices of a number field it produces the completed `Λ_K`.

## Main definitions / results (this file)
* `DedekindResidue.thetaLattice L t` — `Θ_L(t) = ∑'_{v ∈ L} exp(-π t ‖v‖²)` (real-valued).
* (in progress) `thetaLattice_transform` — the inversion law above, for `t > 0`.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real

variable {ι : Type*} [Fintype ι]

/-- The **lattice theta function** `Θ_L(t) := ∑_{v ∈ L} e^{-π t ‖v‖²}` (real-valued; the sum
converges for `t > 0` by `summable_gaussian_zlattice`, and is junk `0` otherwise per `tsum`
convention — every theorem carries `0 < t`). -/
noncomputable def thetaLattice (L : Submodule ℤ (EuclideanSpace ℝ ι)) (t : ℝ) : ℝ :=
  ∑' v : L, Real.exp (-(π * t) * ‖(v : EuclideanSpace ℝ ι)‖ ^ 2)

/-- The theta sum converges for `t > 0`. -/
theorem summable_thetaLattice (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {t : ℝ} (ht : 0 < t) :
    Summable (fun v : L => Real.exp (-(π * t) * ‖(v : EuclideanSpace ℝ ι)‖ ^ 2)) :=
  summable_gaussian_zlattice L (by positivity)

open TopologicalSpace

/-- The centred Gaussian `x ↦ e^{-πt‖x‖²}` as a continuous map, in the exact shape of
mathlib's `fourier_gaussian_innerProductSpace` (`b = πt`). -/
noncomputable def gaussianCM (t : ℝ) : C(EuclideanSpace ℝ ι, ℂ) :=
  ⟨fun x => Complex.exp (-(π * t : ℂ) * (‖x‖ : ℂ) ^ 2), by fun_prop⟩

/-- Sub-level sets of a lattice are finite (lattice ∩ closed ball in a proper space). -/
theorem finite_norm_le_zlattice (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] (R : ℝ) :
    {v : L | ‖(v : EuclideanSpace ℝ ι)‖ ≤ R}.Finite := by
  have hcl : IsClosed (L : Set (EuclideanSpace ℝ ι)) := by
    rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete
  have hfb : (Metric.closedBall 0 R ∩ (L : Set (EuclideanSpace ℝ ι))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hcl
  refine Set.Finite.of_finite_image (hfb.subset ?_) (Subtype.val_injective.injOn)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨by simpa using hz, z.2⟩

/-- **Θ1: the Gaussian translate estimate.** For `t > 0`, the sup-norms of the lattice
translates of the Gaussian on any compact are summable: outside a finite sub-level set,
`sup_{x∈K} e^{-πt‖x+v‖²} ≤ e^{πtR²}·e^{-(πt/2)‖v‖²}` (reverse triangle + `(a-R)² ≥ a²/2-R²`),
and the right side is summable by `summable_gaussian_zlattice`. This discharges `h_norm` of
the lattice Poisson formula at the Gaussian. -/
theorem summable_norm_restrict_gaussianCM (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {t : ℝ} (ht : 0 < t)
    (K : Compacts (EuclideanSpace ℝ ι)) :
    Summable fun v : L =>
      ‖((gaussianCM t).comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict
        (K : Set (EuclideanSpace ℝ ι))‖ := by
  obtain ⟨R, hR⟩ := K.2.isBounded.subset_closedBall 0
  set R' := max R 0 with hR'
  have hKR : (K : Set (EuclideanSpace ℝ ι)) ⊆ Metric.closedBall 0 R' :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR0 : (0 : ℝ) ≤ R' := le_max_right _ _
  have hgnorm : ∀ y : EuclideanSpace ℝ ι,
      ‖gaussianCM t y‖ = Real.exp (-(π * t) * ‖y‖ ^ 2) := by
    intro y
    simp only [gaussianCM, ContinuousMap.coe_mk]
    rw [Complex.norm_exp]
    have : (-(π * t : ℂ) * (‖y‖ : ℂ) ^ 2) = ((-(π * t) * ‖y‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  refine Summable.of_norm_bounded_eventually
    (g := fun v : L => Real.exp (π * t * R' ^ 2)
      * Real.exp (-(π * t / 2) * ‖(v : EuclideanSpace ℝ ι)‖ ^ 2)) ?_ ?_
  · exact (summable_gaussian_zlattice L (by positivity)).mul_left _
  · rw [Filter.eventually_cofinite]
    refine (finite_norm_le_zlattice L R').subset (fun v hv => ?_)
    simp only [Set.mem_setOf_eq] at hv ⊢
    by_contra hnotle
    rw [not_le] at hnotle
    refine hv ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [← Real.exp_add]
    refine (ContinuousMap.norm_le _ (Real.exp_nonneg _)).mpr (fun x => ?_)
    show ‖gaussianCM t ((x : EuclideanSpace ℝ ι) + (v : EuclideanSpace ℝ ι))‖ ≤ _
    rw [hgnorm]
    refine Real.exp_le_exp.mpr ?_
    have hx : ‖(x : EuclideanSpace ℝ ι)‖ ≤ R' := by
      have := hKR x.2
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hvx : ‖(v : EuclideanSpace ℝ ι)‖ - R'
        ≤ ‖(x : EuclideanSpace ℝ ι) + (v : EuclideanSpace ℝ ι)‖ := by
      have h1 : ‖(v : EuclideanSpace ℝ ι)‖
          ≤ ‖(x : EuclideanSpace ℝ ι) + (v : EuclideanSpace ℝ ι)‖
            + ‖(x : EuclideanSpace ℝ ι)‖ := by
        calc ‖(v : EuclideanSpace ℝ ι)‖
            = ‖(x : EuclideanSpace ℝ ι) + (v : EuclideanSpace ℝ ι)
                - (x : EuclideanSpace ℝ ι)‖ := by rw [add_sub_cancel_left]
          _ ≤ _ := norm_sub_le _ _
      linarith
    have hsq : (‖(v : EuclideanSpace ℝ ι)‖ - R') ^ 2
        ≤ ‖(x : EuclideanSpace ℝ ι) + (v : EuclideanSpace ℝ ι)‖ ^ 2 := by
      refine sq_le_sq' ?_ hvx
      have := norm_nonneg ((x : EuclideanSpace ℝ ι) + (v : EuclideanSpace ℝ ι))
      linarith
    nlinarith [Real.pi_pos, sq_nonneg (‖(v : EuclideanSpace ℝ ι)‖ - 2 * R'), ht.le,
      mul_pos Real.pi_pos ht]

end

end DedekindResidue
