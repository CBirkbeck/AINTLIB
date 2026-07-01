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
* `thetaLattice_transform` — **the inversion law** `Θ_L(t) = covol(L)⁻¹·t^{-n/2}·Θ_{L♯}(1/t)`
  for `t > 0`, fully proven from the lattice Poisson formula + mathlib's Gaussian Fourier
  transform (`fourier_gaussianCM`), with both convergence hypotheses discharged
  (`summable_norm_restrict_gaussianCM`, `summable_fourier_gaussianCM`).
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

open scoped FourierTransform

/-- Pointwise norm of the Gaussian: `‖e^{-πt‖x‖²}‖ = e^{-πt‖x‖²}` (the exponent is real). -/
theorem norm_gaussianCM_apply (t : ℝ) (x : EuclideanSpace ℝ ι) :
    ‖gaussianCM t x‖ = Real.exp (-(π * t) * ‖x‖ ^ 2) := by
  simp only [gaussianCM, ContinuousMap.coe_mk]
  rw [Complex.norm_exp]
  have : (-(π * t : ℂ) * (‖x‖ : ℂ) ^ 2) = ((-(π * t) * ‖x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

/-- **Θ3: the Fourier transform of the Gaussian** (mathlib's
`fourier_gaussian_innerProductSpace` at `b = πt`, constants normalised):
`𝓕(e^{-πt‖·‖²})(w) = t^{-n/2}·e^{-π‖w‖²/t}` — the Gaussian is self-dual up to the scaling
`t ↦ 1/t` and the factor `t^{-n/2}` (Neukirch VII §3 shape). -/
theorem fourier_gaussianCM {t : ℝ} (ht : 0 < t) (w : EuclideanSpace ℝ ι) :
    𝓕 (⇑(gaussianCM (ι := ι) t)) w
      = ((t ^ (-(Fintype.card ι : ℝ) / 2) : ℝ) : ℂ) * gaussianCM t⁻¹ w := by
  have hb : (0 : ℝ) < ((π * t : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re]
    norm_num [Real.pi_pos.le]
    positivity
  have h := fourier_gaussian_innerProductSpace (b := (π * t : ℂ)) hb w
  have hcoe : (⇑(gaussianCM t) : EuclideanSpace ℝ ι → ℂ)
      = fun v => Complex.exp (-(π * t : ℂ) * (‖v‖ : ℂ) ^ 2) := rfl
  rw [hcoe]
  rw [h]
  congr 1
  · -- (π/(πt))^(n/2) = ↑(t^(-n/2))
    have h1 : ((π : ℂ) / (π * t : ℂ)) = ((t⁻¹ : ℝ) : ℂ) := by
      push_cast
      rw [div_mul_eq_div_div, div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
      simp [one_div]
    rw [h1, finrank_euclideanSpace]
    have h2 : ((Fintype.card ι : ℂ) / 2) = (((Fintype.card ι : ℝ) / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le)]
    congr 1
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_div]
  · -- cexp(-π²‖w‖²/(πt)) = gaussianCM t⁻¹ w
    show _ = Complex.exp (-(π * t⁻¹ : ℂ) * (‖w‖ : ℂ) ^ 2)
    congr 1
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by
      simpa using ht.ne'
    push_cast
    field_simp

/-- The Fourier transforms of the Gaussian are summable over the dual lattice — the `h_sum`
hypothesis of the lattice Poisson formula at the Gaussian (`Θ3` + `summable_gaussian_zlattice`
over `L♯`, whose lattice instances come from `DualLattice.lean`). -/
theorem summable_fourier_gaussianCM (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {t : ℝ} (ht : 0 < t) :
    Summable fun w : dualZLattice L =>
      𝓕 (⇑(gaussianCM (ι := ι) t)) (w : EuclideanSpace ℝ ι) := by
  have h1 : Summable (fun w : dualZLattice L =>
      ((t ^ (-(Fintype.card ι : ℝ) / 2) : ℝ) : ℂ)
        * gaussianCM (ι := ι) t⁻¹ (w : EuclideanSpace ℝ ι)) := by
    refine Summable.of_norm ?_
    have heq : (fun w : dualZLattice L => ‖((t ^ (-(Fintype.card ι : ℝ) / 2) : ℝ) : ℂ)
        * gaussianCM (ι := ι) t⁻¹ (w : EuclideanSpace ℝ ι)‖)
        = fun w : dualZLattice L => |t ^ (-(Fintype.card ι : ℝ) / 2)|
            * Real.exp (-(π * t⁻¹) * ‖(w : EuclideanSpace ℝ ι)‖ ^ 2) := by
      funext w
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gaussianCM_apply]
    rw [heq]
    exact (summable_gaussian_zlattice (dualZLattice L) (by positivity)).mul_left _
  exact h1.congr (fun w => (fourier_gaussianCM ht _).symm)

/-- Complexification of the theta sum: `↑Θ_M(s) = ∑'_{v∈M} gaussianCM s v`. -/
theorem ofReal_thetaLattice (M : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology M] [IsZLattice ℝ M] {s : ℝ} (hs : 0 < s) :
    ((thetaLattice M s : ℝ) : ℂ) = ∑' v : M, gaussianCM (ι := ι) s (v : EuclideanSpace ℝ ι) := by
  rw [thetaLattice]
  rw [show ((((∑' v : M, Real.exp (-(π * s) * ‖(v : EuclideanSpace ℝ ι)‖ ^ 2)) : ℝ)) : ℂ)
      = Complex.ofRealCLM (∑' v : M, Real.exp (-(π * s) * ‖(v : EuclideanSpace ℝ ι)‖ ^ 2))
    from rfl]
  rw [ContinuousLinearMap.map_tsum Complex.ofRealCLM (summable_thetaLattice M hs)]
  refine tsum_congr (fun v => ?_)
  show ((Real.exp (-(π * s) * ‖(v : EuclideanSpace ℝ ι)‖ ^ 2) : ℝ) : ℂ) = _
  rw [Complex.ofReal_exp]
  show Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

/-- **The lattice theta transformation law** (SP1-AGΘ; Neukirch VII §3 shape):
`Θ_L(t) = covol(L)⁻¹ · t^{-n/2} · Θ_{L♯}(1/t)` for `t > 0` — the Gaussian instantiation of
Poisson summation over `L`. This is the analytic engine of the Hecke functional equation:
applied to the ideal lattices of a number field it yields the completed `Λ_K` (SP1-AGE). -/
theorem thetaLattice_transform (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {t : ℝ} (ht : 0 < t) :
    thetaLattice L t = (ZLattice.covolume L volume)⁻¹ * t ^ (-(Fintype.card ι : ℝ) / 2)
      * thetaLattice (dualZLattice L) t⁻¹ := by
  have hP := tsum_eq_tsum_fourier_zlattice L (g := gaussianCM t)
    (fun K => summable_norm_restrict_gaussianCM L ht K) (summable_fourier_gaussianCM L ht)
  have h3 : (∑' w : dualZLattice L, 𝓕 (⇑(gaussianCM (ι := ι) t)) (w : EuclideanSpace ℝ ι))
      = ((t ^ (-(Fintype.card ι : ℝ) / 2) : ℝ) : ℂ)
        * ∑' w : dualZLattice L, gaussianCM (ι := ι) t⁻¹ (w : EuclideanSpace ℝ ι) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun w => fourier_gaussianCM ht _)
  refine Complex.ofReal_injective ?_
  rw [ofReal_thetaLattice L ht, hP, h3, ← ofReal_thetaLattice (dualZLattice L) (inv_pos.mpr ht)]
  push_cast
  rw [Complex.real_smul]
  push_cast
  ring

open scoped RealInnerProductSpace

/-- Coordinatewise scaling by nonvanishing weights, as a linear equivalence — the diagonal
positive-definite change of variables for the **anisotropic** (multivariable) theta, which
Hecke's functional-equation argument integrates over the unit domain (SP1-AGE-0). -/
noncomputable def diagScale (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => c i * x i)
  invFun x := WithLp.toLp 2 (fun i => (c i)⁻¹ * x i)
  map_add' x y := by ext i; simp; ring
  map_smul' r x := by ext i; simp; ring
  left_inv x := by
    ext i
    field_simp [hc i]
  right_inv x := by
    ext i
    field_simp [hc i]

omit [Fintype ι] in
theorem diagScale_apply (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) (x : EuclideanSpace ℝ ι) (i : ι) :
    diagScale c hc x i = c i * x i := rfl

/-- `diagScale` is self-adjoint (its matrix is diagonal). -/
theorem adjoint_diagScale (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    LinearMap.adjoint ((diagScale c hc : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
      = ((diagScale c hc : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr ?_).symm
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : (((diagScale c hc : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) x) i = c i * x i := rfl
  have h2 : (((diagScale c hc : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) y) i = c i * y i := rfl
  rw [h1, h2]
  ring

/-- The determinant of `diagScale` is the product of the weights. -/
theorem det_diagScale (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    LinearMap.det ((diagScale c hc : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = ∏ i, c i := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis]
  have : LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis
      ((diagScale c hc : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [OrthonormalBasis.coe_toBasis]
    show diagScale c hc ((EuclideanSpace.basisFun ι ℝ).toBasis j) i = _
    rw [OrthonormalBasis.coe_toBasis, diagScale_apply]
    rw [EuclideanSpace.basisFun_apply]
    simp
  rw [this, Matrix.det_diagonal]

/-- The **anisotropic Gaussian** with diagonal weights `c`:
`x ↦ e^{-π ∑ᵢ cᵢ xᵢ²}` — the integrand of Hecke's multivariable theta (one weight per
infinite place). For positive weights it is the standard Gaussian composed with
`diagScale √c` (`weightedGaussianCM_eq_comp`). -/
noncomputable def weightedGaussianCM (c : ι → ℝ) : C(EuclideanSpace ℝ ι, ℂ) :=
  ⟨fun x => Complex.exp (-(π : ℂ) * ∑ i, (c i : ℂ) * (x i : ℂ) ^ 2), by fun_prop⟩

/-- The squared norm of a `diagScale √c`-scaled point is the weighted square sum. -/
theorem norm_diagScale_sqrt_sq (c : ι → ℝ) (hc : ∀ i, 0 < c i) (x : EuclideanSpace ℝ ι) :
    ‖diagScale (fun i => Real.sqrt (c i)) (fun i => Real.sqrt_ne_zero'.mpr (hc i)) x‖ ^ 2
      = ∑ i, c i * x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [diagScale_apply, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hc i).le]

/-- **Structural identity**: the anisotropic Gaussian is the standard Gaussian pulled back
along the diagonal scaling by `√c`. This feeds `fourier_comp_linearEquiv` (P3a) to compute
its Fourier transform. -/
theorem weightedGaussianCM_eq_comp (c : ι → ℝ) (hc : ∀ i, 0 < c i) (x : EuclideanSpace ℝ ι) :
    weightedGaussianCM c x
      = gaussianCM 1 ((diagScale (fun i => Real.sqrt (c i))
          (fun i => Real.sqrt_ne_zero'.mpr (hc i))) x) := by
  simp only [weightedGaussianCM, gaussianCM, ContinuousMap.coe_mk]
  congr 1
  have hn := norm_diagScale_sqrt_sq c hc x
  rw [show ((‖diagScale (fun i => Real.sqrt (c i))
      (fun i => Real.sqrt_ne_zero'.mpr (hc i)) x‖ : ℂ) ^ 2)
      = ((∑ i, c i * x i ^ 2 : ℝ) : ℂ) by rw [← hn]; push_cast; ring]
  push_cast
  ring

end

end DedekindResidue
