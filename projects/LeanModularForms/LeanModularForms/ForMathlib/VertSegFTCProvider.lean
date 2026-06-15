/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC

/-!
# Shared helpers for the vertical-edge `ArcFTCHyp` providers

The files `Seg1FTCProvider.lean` and `Seg4FTCProvider.lean` build
`ArcFTCHyp` for points on the right and left vertical edges of the
fundamental domain boundary. They share a great deal of mechanical
infrastructure about the arc piece (`vertSeg_h_arc`), the upper
horizontal piece (`vertSeg_h₅`), and the seg3 piece (`vertSeg_h₃`),
all of which use `fdBoundaryFun H t - z₀` and only differ on which
side `z₀` lies on.

This file collects:
* the shared reference functions `vertSeg_h_arc`, `vertSeg_h₃`,
  `vertSeg_h₅` (which depend only on `H`, `z₀`, `t`),
* their continuity / `HasDerivAt` / derivative formulas,
* the equality `fdBoundaryFun H t - z₀ = ...` on each segment,
* slitPlane membership lemmas that are direction-independent
  (`vertSeg_h₅`'s positive imaginary part, and the four `junction`
  identities).

Side-specific lemmas (the `slitPlane` membership for `-h` versus `h`,
the seg1-vs-seg4 t₀ computations, and the final FTC telescopes)
remain in their respective files.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Transfer integrability of `f'/f` to integrability of the boundary log-derivative
on `[a, b]`, given a pointwise ae-equality. -/
lemma vertSeg_integrable_transfer {H : ℝ} {z₀ : ℂ} {f : ℝ → ℂ} {a b : ℝ}
    (h_int : IntervalIntegrable (fun t => deriv f t / f t) volume a b)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv f t / f t) :
    IntervalIntegrable (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume a b :=
  h_int.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (h_ae.mono (fun _ ht hm => (ht hm).symm)))

/-- Transfer the FTC evaluation of `∫ f'/f` to `∫ (boundary log-derivative)`,
given a pointwise ae-equality. -/
lemma vertSeg_integral_transfer {H : ℝ} {z₀ : ℂ} {f : ℝ → ℂ} {a b : ℝ} {C : ℂ}
    (h_ftc : ∫ t in a..b, deriv f t / f t = C)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv f t / f t) :
    ∫ t in a..b, (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = C := by
  rw [intervalIntegral.integral_congr_ae h_ae]; exact h_ftc

/-- The log-difference `log((Kδ : ℂ) * (-I)) - log((Kδ : ℂ) * I) = -π·I` for `Kδ > 0`.
This is the universal final step of the `log_diff_eq_neg_pi_I` lemmas. -/
lemma vertSeg_log_diff_neg_I_pi {Kδ : ℝ} (hKδ : 0 < Kδ) :
    Complex.log (((Kδ : ℝ) : ℂ) * (-I)) - Complex.log (((Kδ : ℝ) : ℂ) * I) = -(↑Real.pi * I) := by
  rw [Complex.log_ofReal_mul hKδ (neg_ne_zero.mpr I_ne_zero),
    Complex.log_ofReal_mul hKδ I_ne_zero, Complex.log_neg_I, Complex.log_I]
  ring

/-- Combined transfer: integrability and FTC evaluation in one step. -/
lemma vertSeg_ftc_transfer {H : ℝ} {z₀ : ℂ} {f : ℝ → ℂ} {a b : ℝ} {C : ℂ}
    (h_ftc : IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
      ∫ t in a..b, deriv f t / f t = C)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv f t / f t) :
    IntervalIntegrable (fun t => (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t)
      volume a b ∧
    ∫ t in a..b, (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = C :=
  ⟨vertSeg_integrable_transfer h_ftc.1 h_ae, vertSeg_integral_transfer h_ftc.2 h_ae⟩

/-! ### Seg1 piece reference function (shared) -/

/-- The seg1-piece trajectory reference for any vertical-edge target `z₀`.
This is the difference `fdBoundaryFun H t - z₀` on the segment `t ∈ [0, 1/5]`,
where the boundary traces the right vertical edge from top to bottom. The
formula is the same for both seg1 and seg4 providers; only `z₀.re` differs
between the two use cases. -/
def vertSeg_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((1/2 - z₀.re : ℝ) : ℂ) +
  ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

lemma fdBoundary_sub_eq_vertSeg_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z₀ = vertSeg_h₀ H z₀ t := by
  simp only [fdBoundaryFun, ht, ite_true, vertSeg_h₀]
  refine Complex.ext ?_ ?_ <;> simp

@[fun_prop]
lemma vertSeg_h₀_continuous (H : ℝ) (z₀ : ℂ) : Continuous (vertSeg_h₀ H z₀) := by
  unfold vertSeg_h₀; fun_prop

lemma hasDerivAt_vertSeg_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t := by
  have h_real : HasDerivAt (fun s : ℝ => H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im)
      (-seg1Speed H) t := by
    have hd : HasDerivAt (fun s : ℝ => 5 * s * (H - Real.sqrt 3 / 2))
        (5 * (H - Real.sqrt 3 / 2)) t :=
      (((hasDerivAt_id t).const_mul 5).mul_const (H - Real.sqrt 3 / 2)).congr_deriv (by ring)
    exact (((hasDerivAt_const t H).sub hd).sub_const z₀.im).congr_deriv
      (by unfold seg1Speed; ring)
  have h1 : HasDerivAt
      (fun s : ℝ => ((H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ))
      (-(seg1Speed H : ℂ)) t :=
    (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact ((hasDerivAt_const t (((1/2 - z₀.re : ℝ) : ℂ))).add (h1.mul_const I)).congr_deriv
    (by ring)

lemma deriv_vertSeg_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h₀ H z₀) t = -(seg1Speed H : ℂ) * I :=
  (hasDerivAt_vertSeg_h₀ H z₀ t).deriv

/-- Ae-equality on any sub-interval of `[0, 1/5]` connecting `fdBoundaryFun H · - z₀`
to `vertSeg_h₀ H z₀ ·`. -/
lemma ae_eq_vertSeg_h₀ (H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1/5) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (vertSeg_h₀ H z₀) t / vertSeg_h₀ H z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt : t < 1/5 :=
    (lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)).trans_le hb
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] vertSeg_h₀ H z₀ :=
    Filter.eventually_of_mem (Iio_mem_nhds ht_lt)
      fun s hs => fdBoundary_sub_eq_vertSeg_h₀ H z₀ s hs.le
  rw [fdBoundary_sub_eq_vertSeg_h₀ H z₀ t ht_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

/-! ### Arc reference function (shared) -/

/-- The arc trajectory reference for any vertical-edge target `z₀`. -/
def vertSeg_h_arc (z₀ : ℂ) (t : ℝ) : ℂ :=
  exp (↑(fdArcAngle t) * I) - z₀

lemma fdBoundary_sub_eq_vertSeg_h_arc {H : ℝ} (z₀ : ℂ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z₀ = vertSeg_h_arc z₀ t := by
  unfold vertSeg_h_arc
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

@[fun_prop]
lemma vertSeg_h_arc_continuous (z₀ : ℂ) : Continuous (vertSeg_h_arc z₀) := by
  unfold vertSeg_h_arc; fun_prop

lemma hasDerivAt_vertSeg_h_arc (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h_arc z₀)
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
  unfold vertSeg_h_arc
  have h1 : HasDerivAt fdArcAngle (5 * Real.pi / 6) t := by
    unfold fdArcAngle
    exact (((((hasDerivAt_id t).const_mul (5 : ℝ)).sub_const 1).mul_const
      (Real.pi / 6)).const_add (Real.pi / 3)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => (↑(fdArcAngle s) : ℂ) * I)
      (↑(5 * Real.pi / 6) * I) t :=
    (h1.ofReal_comp.mul_const I).congr_deriv (by push_cast; ring)
  exact (h2.cexp.congr_deriv (by ring)).sub_const z₀

lemma deriv_vertSeg_h_arc (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h_arc z₀) t = ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
  (hasDerivAt_vertSeg_h_arc z₀ t).deriv

/-- The derivative of `vertSeg_h_arc` is continuous on any set. -/
lemma vertSeg_h_arc_deriv_continuousOn (z₀ : ℂ) (s : Set ℝ) :
    ContinuousOn (fun t => deriv (vertSeg_h_arc z₀) t) s := by
  refine Continuous.continuousOn ?_ |>.congr (fun t _ => deriv_vertSeg_h_arc z₀ t)
  fun_prop

/-! ### Seg3 reference function (shared definition) -/

/-- The seg3 trajectory reference for any vertical-edge target `z₀`. -/
def vertSeg_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((-1/2 - z₀.re : ℝ) : ℂ) +
  ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

lemma fdBoundary_sub_eq_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - z₀ = vertSeg_h₃ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false, vertSeg_h₃]
  refine Complex.ext ?_ ?_ <;> simp

@[fun_prop]
lemma vertSeg_h₃_continuous (H : ℝ) (z₀ : ℂ) : Continuous (vertSeg_h₃ H z₀) := by
  unfold vertSeg_h₃; fun_prop

lemma hasDerivAt_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h₃ H z₀) ((seg1Speed H : ℂ) * I) t := by
  have h_real : HasDerivAt
      (fun s : ℝ => Real.sqrt 3 / 2 + (5 * s - 3) * (H - Real.sqrt 3 / 2) - z₀.im)
      (seg1Speed H) t := by
    have hd : HasDerivAt (fun s : ℝ => 5 * s - 3) 5 t :=
      (((hasDerivAt_id t).const_mul 5).sub_const 3).congr_deriv (by ring)
    exact (((hd.mul_const (H - Real.sqrt 3 / 2)).const_add
      (Real.sqrt 3 / 2)).sub_const z₀.im).congr_deriv (by unfold seg1Speed; ring)
  exact ((hasDerivAt_const t (((-1/2 - z₀.re : ℝ) : ℂ))).add
    ((h_real.ofReal_comp.congr_deriv (by ring)).mul_const I)).congr_deriv (by ring)

lemma deriv_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h₃ H z₀) t = (seg1Speed H : ℂ) * I :=
  (hasDerivAt_vertSeg_h₃ H z₀ t).deriv

/-! ### Top horizontal reference function (shared) -/

/-- The top horizontal (seg5) trajectory reference for any vertical-edge target. -/
def vertSeg_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((5 * t - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I

lemma fdBoundary_sub_eq_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z₀ = vertSeg_h₅ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false, vertSeg_h₅]
  refine Complex.ext ?_ ?_ <;> simp

@[fun_prop]
lemma vertSeg_h₅_continuous (H : ℝ) (z₀ : ℂ) : Continuous (vertSeg_h₅ H z₀) := by
  unfold vertSeg_h₅; fun_prop

lemma hasDerivAt_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (vertSeg_h₅ H z₀) (5 : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((5 * s - 9/2 - z₀.re : ℝ) : ℂ)) 5 t := by
    have h_real : HasDerivAt (fun s : ℝ => 5 * s - 9/2 - z₀.re) 5 t :=
      ((((hasDerivAt_id t).const_mul 5).sub_const (9/2)).sub_const z₀.re).congr_deriv (by ring)
    exact (h_real.ofReal_comp).congr_deriv (by push_cast; ring)
  exact (h1.add_const _).congr_deriv (by ring)

lemma deriv_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (vertSeg_h₅ H z₀) t = 5 :=
  (hasDerivAt_vertSeg_h₅ H z₀ t).deriv

/-- `vertSeg_h₅` lies in `slitPlane` whenever `z₀.im < H`. -/
lemma vertSeg_h₅_slitPlane {H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) :
    vertSeg_h₅ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  unfold vertSeg_h₅
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  intro h
  linarith

/-- `-vertSeg_h₅` lies in `slitPlane` whenever `z₀.im < H`. -/
lemma neg_vertSeg_h₅_slitPlane {H : ℝ} {z₀ : ℂ} (hc_hi : z₀.im < H) (t : ℝ) :
    -(vertSeg_h₅ H z₀ t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  unfold vertSeg_h₅
  simp only [Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  intro h
  linarith

/-- FTC for the seg5 piece using positive log: applicable when `vertSeg_h₅` lies in
`slitPlane`. -/
lemma vertSeg_h₅_ftc (H : ℝ) {z₀ : ℂ} (hc_hi : z₀.im < H) :
    IntervalIntegrable
      (fun t => deriv (vertSeg_h₅ H z₀) t / vertSeg_h₅ H z₀ t) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (vertSeg_h₅ H z₀) t / vertSeg_h₅ H z₀ t =
      Complex.log (vertSeg_h₅ H z₀ 1) - Complex.log (vertSeg_h₅ H z₀ (4/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (vertSeg_h₅_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_vertSeg_h₅ H z₀ t).differentiableAt)
    (funext (deriv_vertSeg_h₅ H z₀) ▸ continuousOn_const)
  intro t _
  exact vertSeg_h₅_slitPlane hc_hi t

/-- FTC for the seg5 piece using negative log: applicable when `-vertSeg_h₅` lies in
`slitPlane`. -/
lemma neg_vertSeg_h₅_ftc (H : ℝ) {z₀ : ℂ} (hc_hi : z₀.im < H) :
    IntervalIntegrable
      (fun t => deriv (vertSeg_h₅ H z₀) t / vertSeg_h₅ H z₀ t) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (vertSeg_h₅ H z₀) t / vertSeg_h₅ H z₀ t =
      Complex.log (-(vertSeg_h₅ H z₀ 1)) - Complex.log (-(vertSeg_h₅ H z₀ (4/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (vertSeg_h₅_continuous H z₀).continuousOn
    (fun t _ => (hasDerivAt_vertSeg_h₅ H z₀ t).differentiableAt)
    (continuousOn_const.congr (fun t _ => deriv_vertSeg_h₅ H z₀ t))
  intro t _
  exact neg_vertSeg_h₅_slitPlane hc_hi t

/-! ### Junction identities (shared) -/

lemma vertSeg_junction_35 (H : ℝ) (z₀ : ℂ) :
    vertSeg_h_arc z₀ (3/5) = vertSeg_h₃ H z₀ (3/5) := by
  unfold vertSeg_h_arc vertSeg_h₃
  rw [show (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 from by unfold fdArcAngle; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, zero_add, add_zero] <;> ring

lemma vertSeg_junction_45 (H : ℝ) (z₀ : ℂ) :
    vertSeg_h₃ H z₀ (4/5) = vertSeg_h₅ H z₀ (4/5) := by
  unfold vertSeg_h₃ vertSeg_h₅
  refine Complex.ext ?_ ?_ <;> simp <;> ring

/-! ### Shared ae-equality for h_arc, h₃, h₅ pieces -/

/-- Ae-equality on any sub-interval of `(3/5, 4/5)` connecting `fdBoundaryFun H · - z₀`
to `vertSeg_h₃ H z₀ ·`. -/
lemma ae_eq_vertSeg_h₃ (H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b)
    (ha_ge : 3/5 ≤ a) (hb_le : b ≤ 4/5) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (vertSeg_h₃ H z₀) t / vertSeg_h₃ H z₀ t := by
  have h_excl : ({a, b} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr ((Set.toFinite ({a, b} : Set ℝ)).measure_zero volume)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt_b : t < b :=
    lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_insert_iff.mpr (Or.inr h)))
  have ht3_lt : 3/5 < t := lt_of_le_of_lt ha_ge ht_mem.1
  have ht4_lt : t < 4/5 := lt_of_lt_of_le ht_lt_b hb_le
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] vertSeg_h₃ H z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3_lt) (Iio_mem_nhds ht4_lt))
      fun s ⟨hs3, hs4⟩ => fdBoundary_sub_eq_vertSeg_h₃ H z₀ hs3 (le_of_lt hs4)
  rw [fdBoundary_sub_eq_vertSeg_h₃ H z₀ ht3_lt ht4_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

lemma ae_eq_vertSeg_h_arc (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (1/5 : ℝ) (3/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (vertSeg_h_arc z₀) t / vertSeg_h_arc z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (1/5 : ℝ) ≤ 3/5)] at ht_mem
  have ht1 : 1/5 < t := ht_mem.1
  have ht3_lt : t < 3/5 :=
    lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] vertSeg_h_arc z₀ :=
    Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht3_lt))
      fun _ ⟨hs1, hs3⟩ => fdBoundary_sub_eq_vertSeg_h_arc z₀ hs1 hs3.le
  rw [fdBoundary_sub_eq_vertSeg_h_arc z₀ ht1 ht3_lt.le,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

lemma ae_eq_vertSeg_h₅ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (vertSeg_h₅ H z₀) t / vertSeg_h₅ H z₀ t := by
  refine ae_of_all _ fun t ht_mem => ?_
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  have h_evEq : (fun s => fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] vertSeg_h₅ H z₀ :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht4) fun _ hs => fdBoundary_sub_eq_vertSeg_h₅ H z₀ hs
  rw [fdBoundary_sub_eq_vertSeg_h₅ H z₀ ht4,
    ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv, mul_comm]

end
