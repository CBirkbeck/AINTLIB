module

public import Mathlib
public import DedekindResidue.ExplicitFormula.TestFunction
public import DedekindResidue.Lemma2

/-!
# `F_{s,X}` is an admissible test function  (T-ADM discharge)

The paper's auxiliary function `F_{s,X}` (eqs. (11)–(12)) satisfies the Weil–Poitou
explicit-formula hypotheses (`IsAdmissibleTestFn`) for `Re s > 1`, `X > 1` — exactly the
regime in which Lemma 3's proof first applies the explicit formula ("Assume first that
`Re(s) > 1`. Then the assumptions in the explicit formula (3) apply to `F_{s,X}`", p. 6);
`Re s > 1/2` is subsequently reached by analytic continuation, never by re-checking
admissibility.

Main results:
* `continuous_auxF` — via the kink-free closed form `auxF_eq_max`;
* `auxF_mul_exp_bv`, `auxF_mul_exp_integrable` — the weighted conditions with witness
  `ε = (Re s - 1)/2`;
* `auxF_diffQuot_bv` — the difference-quotient condition (zero on the plateau,
  `1/x - T·e^{hT}·e^{-hx}/x²` on the tail);
* `isAdmissibleTestFn_auxF` — the bundled instance.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real



/-- Kink-free closed form for `auxF` (valid for `X > 1`): on both branches,
`F_{s,X}(t) = (T/max(|t|,T))·e^{-h(max(|t|,T)-T)}` with `T = log X`. -/
theorem auxF_eq_max (s : ℂ) {X : ℝ} (hX : 1 < X) (t : ℝ) :
    auxF s X t
      = ((Real.log X / max |t| (Real.log X) : ℝ) : ℂ)
        * Complex.exp (-(s - 1/2) * ((max |t| (Real.log X) - Real.log X : ℝ) : ℂ)) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  rw [auxF]
  rcases le_or_gt |t| (Real.log X) with hle | hgt
  · rw [if_pos hle, max_eq_right hle]
    rw [div_self hT0.ne', sub_self]
    push_cast
    rw [mul_zero, Complex.exp_zero, one_mul]
  · rw [if_neg (not_le.mpr hgt), max_eq_left (le_of_lt hgt)]

/-- `F_{s,X}` is continuous (for `X > 1`): both branches glue along `|t| = log X`,
as the kink-free `max` form shows. -/
theorem continuous_auxF (s : ℂ) {X : ℝ} (hX : 1 < X) : Continuous (auxF s X) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hmax : Continuous (fun t : ℝ => max |t| (Real.log X)) :=
    continuous_abs.max continuous_const
  have hne : ∀ t : ℝ, max |t| (Real.log X) ≠ 0 :=
    fun t => (lt_max_of_lt_right hT0).ne'
  have : Continuous (fun t : ℝ =>
      ((Real.log X / max |t| (Real.log X) : ℝ) : ℂ)
        * Complex.exp (-(s - 1/2) * ((max |t| (Real.log X) - Real.log X : ℝ) : ℂ))) := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_const.div hmax hne)
    · exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp (hmax.sub continuous_const)))
  exact this.congr (fun t => (auxF_eq_max s hX t).symm)

/-- The jump-average condition holds trivially for the continuous `F_{s,X}`. -/
theorem auxF_jump_avg (s : ℂ) {X : ℝ} (hX : 1 < X) (x : ℝ) :
    ∃ L R : ℂ,
      Filter.Tendsto (auxF s X) (nhdsWithin x (Set.Iio x)) (nhds L)
      ∧ Filter.Tendsto (auxF s X) (nhdsWithin x (Set.Ioi x)) (nhds R)
      ∧ auxF s X x = (L + R) / 2 := by
  refine ⟨auxF s X x, auxF s X x,
    ((continuous_auxF s hX).continuousAt.tendsto).mono_left nhdsWithin_le_nhds,
    ((continuous_auxF s hX).continuousAt.tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
  ring

section AdmAux

variable (s : ℂ) {X : ℝ}

/-- On the tail, the exponentially weighted auxiliary function is a constant times the
kernel `e^{mt}/t`, `m = (1/2+ε) - h`. Stated with the `-(-m)` spelling that the kernel
lemmas (`hasDerivAt_gAux_core` etc. at `h := -m`) produce. -/
theorem auxF_mul_exp_tail_eq (hX : 1 < X) :
    ∀ t ∈ Set.Ioi (Real.log X),
      auxF s X t * ((Real.exp ((1/2 + (s.re - 1)/2) * t) : ℝ) : ℂ)
        = ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (Complex.exp (-(-(((1/2 + (s.re - 1)/2 : ℝ) : ℂ) - (s - 1/2))) * t) / t) := by
  intro t ht
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have htpos : 0 < t := hT0.trans ht
  have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  have hnot : ¬ |t| ≤ Real.log X := by
    rw [abs_of_pos htpos]
    exact not_le.mpr ht
  rw [auxF, if_neg hnot, abs_of_pos htpos, neg_neg]
  push_cast
  rw [show -(s - 1/2) * ((t:ℂ) - (Real.log X : ℂ))
      = (s - 1/2) * (Real.log X : ℂ) + -(s - 1/2) * (t:ℂ) by ring, Complex.exp_add]
  rw [show ((1:ℂ)/2 + ((s.re : ℂ) - 1)/2 - (s - 1/2)) * (t:ℂ)
      = -(s - 1/2) * (t:ℂ) + ((1:ℂ)/2 + ((s.re : ℂ) - 1)/2) * (t:ℂ) by ring,
    Complex.exp_add]
  field_simp

/-- The real part of the tail-kernel exponent parameter is `(Re s - 1)/2 > 0`. -/
theorem tailExponent_re_pos (hs : 1 < s.re) :
    0 < (-((((1/2 + (s.re - 1)/2 : ℝ)) : ℂ) - (s - 1/2))).re := by
  have : (-((((1/2 + (s.re - 1)/2 : ℝ)) : ℂ) - (s - 1/2))).re
      = -(1/2 + (s.re - 1)/2) + (s.re - 1/2) := by
    simp [Complex.sub_re]
    ring
  rw [this]
  linarith

/-- **Bounded variation of the weighted test function** (with `ε = (Re s - 1)/2`,
requiring `Re s > 1` exactly as in the paper's proof of Lemma 3, where the explicit
formula is first applied for `Re s > 1`). -/
theorem auxF_mul_exp_bv (hX : 1 < X) (hs : 1 < s.re) :
    BoundedVariationOn
      (fun x : ℝ => auxF s X x * ((Real.exp ((1/2 + (s.re - 1)/2) * x) : ℝ) : ℂ))
      (Set.Ici 0) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  set m : ℂ := (((1/2 + (s.re - 1)/2 : ℝ)) : ℂ) - (s - 1/2) with hm
  have hmre : 0 < (-m).re := tailExponent_re_pos s hs
  refine boundedVariationOn_Ici_of_piecewise_deriv (b := Real.log X) hT0.le
    (Continuous.continuousOn (by
      exact (continuous_auxF s hX).mul
        (Complex.continuous_ofReal.comp (by fun_prop))))
    (f' := fun x : ℝ => if x < Real.log X
      then (((1/2 + (s.re - 1)/2) * Real.exp ((1/2 + (s.re - 1)/2) * x) : ℝ) : ℂ)
      else ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
        * (-(-m + 1/x) * (Complex.exp (-(-m) * x) / x)))
    ?_ ?_ ?_
  · -- plateau derivative
    intro x hx
    rw [if_pos hx.2]
    have hev : (fun y : ℝ => auxF s X y * ((Real.exp ((1/2 + (s.re - 1)/2) * y) : ℝ) : ℂ))
        =ᶠ[nhds x] fun y : ℝ => ((Real.exp ((1/2 + (s.re - 1)/2) * y) : ℝ) : ℂ) := by
      filter_upwards [eventually_abs_sub_lt x
        (by rw [abs_of_pos hx.1]; linarith [hx.2] : 0 < Real.log X - |x|)] with y hy
      have hyle : |y| ≤ Real.log X := by
        have := abs_sub_abs_le_abs_sub y x
        linarith [abs_sub_comm y x ▸ hy]
      rw [auxF_of_le s X hyle, one_mul]
    have hbase : HasDerivAt
        (fun y : ℝ => ((Real.exp ((1/2 + (s.re - 1)/2) * y) : ℝ) : ℂ))
        (((1/2 + (s.re - 1)/2) * Real.exp ((1/2 + (s.re - 1)/2) * x) : ℝ) : ℂ) x := by
      have := (((hasDerivAt_id x).const_mul ((1:ℝ)/2 + (s.re - 1)/2)).exp).ofReal_comp
      refine this.congr_deriv ?_
      simp only [id_eq]
      push_cast
      ring
    exact hbase.congr_of_eventuallyEq hev
  · -- tail derivative
    intro x hx
    rw [if_neg (not_lt.mpr (le_of_lt hx))]
    have hev : (fun y : ℝ => auxF s X y * ((Real.exp ((1/2 + (s.re - 1)/2) * y) : ℝ) : ℂ))
        =ᶠ[nhds x] fun y : ℝ =>
          ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
            * (Complex.exp (-(-m) * y) / y) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact auxF_mul_exp_tail_eq s hX y hy
    exact (((hasDerivAt_gAux_core (-m) (hT0.trans hx)).const_mul
      (((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ)))).congr_of_eventuallyEq
      hev)
  · -- integrability of the derivative
    rw [show Set.Ici (0:ℝ) = Set.Icc 0 (Real.log X) ∪ Set.Ioi (Real.log X) from
      (Set.Icc_union_Ioi_eq_Ici hT0.le).symm]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · -- plateau piece, a.e.-equal to the continuous formula
      have hbase : IntegrableOn
          (fun x : ℝ =>
            (((1/2 + (s.re - 1)/2) * Real.exp ((1/2 + (s.re - 1)/2) * x) : ℝ) : ℂ))
          (Set.Icc 0 (Real.log X)) :=
        Continuous.integrableOn_Icc (by fun_prop)
      refine hbase.congr ?_
      have hae : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc 0 (Real.log X))), x ≠ Real.log X := by
        refine ae_restrict_of_ae ?_
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton]
        exact measure_singleton _
      filter_upwards [ae_restrict_mem measurableSet_Icc, hae] with x hx hxne
      rw [if_pos (lt_of_le_of_ne hx.2 hxne)]
    · -- tail piece: the exponential kernel lemma
      have hbase : IntegrableOn (fun x : ℝ =>
          ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
            * (-(-m + 1/x) * (Complex.exp (-(-m) * x) / x) * ((1 : ℝ) : ℂ)))
          (Set.Ioi (Real.log X)) :=
        (integrableOn_gAux_deriv_mul_real (h := -m) hmre hT0
          (ψ := fun _ : ℝ => 1) continuous_const (C := 1)
          (fun t => by norm_num)).const_mul _
      refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
      rw [if_neg (not_lt.mpr (le_of_lt hx))]
      push_cast
      ring

/-- **Integrability of the weighted test function** on `[0,∞)` (same `ε`). -/
theorem auxF_mul_exp_integrable (hX : 1 < X) (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ => auxF s X x * ((Real.exp ((1/2 + (s.re - 1)/2) * x) : ℝ) : ℂ))
      (Set.Ici 0) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  set m : ℂ := (((1/2 + (s.re - 1)/2 : ℝ)) : ℂ) - (s - 1/2) with hm
  have hmre : 0 < (-m).re := tailExponent_re_pos s hs
  rw [show Set.Ici (0:ℝ) = Set.Icc 0 (Real.log X) ∪ Set.Ioi (Real.log X) from
    (Set.Icc_union_Ioi_eq_Ici hT0.le).symm]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · exact Continuous.integrableOn_Icc ((continuous_auxF s hX).mul
      (Complex.continuous_ofReal.comp (by fun_prop)))
  · have hbase : IntegrableOn (fun x : ℝ =>
        ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (Complex.exp (-(-m) * x) / x * ((1 : ℝ) : ℂ)))
        (Set.Ioi (Real.log X)) :=
      (integrableOn_exp_div_mul_real (h := -m) hmre hT0
        (ψ := fun _ : ℝ => 1) continuous_const (C := 1)
        (fun t => by norm_num)).const_mul _
    refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [auxF_mul_exp_tail_eq s hX x hx, hm]
    push_cast
    ring

/-- On the tail, the difference quotient is `1/x - c·e^{-hx}/x²` with `c = T·e^{hT}`. -/
theorem auxF_diffQuot_tail_eq (hX : 1 < X) :
    ∀ x ∈ Set.Ici (Real.log X),
      (1 - auxF s X x) / (x : ℂ)
        = 1/(x:ℂ) - ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
            * Complex.exp (-(s - 1/2) * x) / (x:ℂ)^2 := by
  intro x hx
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hxpos : 0 < x := lt_of_lt_of_le hT0 hx
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with heq | hlt
  · -- at the kink both sides vanish
    rw [auxF_of_le s X (by rw [abs_of_pos hxpos]; exact le_of_eq heq.symm)]
    rw [← heq]
    rw [show (s - 1/2) * (Real.log X : ℂ) = -(-(s - 1/2) * (Real.log X : ℂ)) by ring,
      Complex.exp_neg]
    field_simp
  · -- on the open tail, expand the branch
    have hnot : ¬ |x| ≤ Real.log X := by
      rw [abs_of_pos hxpos]
      exact not_le.mpr hlt
    rw [auxF, if_neg hnot, abs_of_pos hxpos]
    push_cast
    rw [show -(s - 1/2) * ((x:ℂ) - (Real.log X : ℂ))
        = (s - 1/2) * (Real.log X : ℂ) + -(s - 1/2) * (x:ℂ) by ring, Complex.exp_add]
    field_simp

/-- **Bounded variation of the difference quotient** `(1 - F_{s,X}(x))/x` on `[0,∞)`:
zero on the plateau, explicitly differentiable with integrable derivative on the tail. -/
theorem auxF_diffQuot_bv (hX : 1 < X) (hs : 1 < s.re) :
    BoundedVariationOn (fun x : ℝ => (1 - auxF s X x) / (x : ℂ)) (Set.Ici 0) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hh : 0 < (s - 1/2 : ℂ).re := by
    have hre : (s - 1/2 : ℂ).re = s.re - 1/2 := by
      simp [Complex.sub_re]
    rw [hre]
    linarith
  have hplateau : ∀ y ∈ Set.Icc (0:ℝ) (Real.log X), (1 - auxF s X y) / (y : ℂ) = 0 := by
    intro y hy
    rw [auxF_of_le s X (by rw [abs_of_nonneg hy.1]; exact hy.2), sub_self, zero_div]
  have hQf : ContinuousOn
      (fun y : ℝ => 1/(y:ℂ)
        - ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
            * Complex.exp (-(s - 1/2) * y) / (y:ℂ)^2)
      (Set.Ici (Real.log X)) := by
    have hne : ∀ y ∈ Set.Ici (Real.log X), ((y : ℝ) : ℂ) ≠ 0 :=
      fun y hy => by exact_mod_cast (lt_of_lt_of_le hT0 hy).ne'
    refine ContinuousOn.sub
      (continuousOn_const.div Complex.continuous_ofReal.continuousOn hne) ?_
    refine ContinuousOn.div (continuousOn_const.mul ?_) (by fun_prop) ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · exact fun y hy => pow_ne_zero 2 (hne y hy)
  have hcont : ContinuousOn (fun x : ℝ => (1 - auxF s X x) / (x : ℂ)) (Set.Ici 0) := by
    rw [show Set.Ici (0:ℝ) = Set.Icc 0 (Real.log X) ∪ Set.Ici (Real.log X) from
      (Set.Icc_union_Ici_eq_Ici hT0.le).symm]
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases hx with hx | hx
      · exact hx.1
      · exact le_trans hT0.le hx
    rcases lt_or_ge x (Real.log X) with hxT | hxT
    · refine ContinuousWithinAt.union ?_ ?_
      · exact continuousWithinAt_const.congr hplateau (hplateau x ⟨hx0, le_of_lt hxT⟩)
      · exact continuousWithinAt_of_notMem_closure
          (by rwa [closure_Ici, Set.mem_Ici, not_le])
    · refine ContinuousWithinAt.union ?_ ?_
      · rcases eq_or_lt_of_le hxT with heq | hlt
        · exact continuousWithinAt_const.congr hplateau
            (hplateau x ⟨hx0, le_of_eq heq.symm⟩)
        · refine continuousWithinAt_of_notMem_closure ?_
          rw [closure_Icc]
          exact fun hmem => absurd hmem.2 (not_le.mpr hlt)
      · exact ((hQf x hxT).congr (fun y hy => auxF_diffQuot_tail_eq s hX y hy)
          (auxF_diffQuot_tail_eq s hX x hxT))
  refine boundedVariationOn_Ici_of_piecewise_deriv (b := Real.log X) hT0.le hcont
    (f' := fun x : ℝ => if x < Real.log X then 0
      else -(1/(x:ℂ)^2)
        + ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (((s - 1/2) * x + 2) * Complex.exp (-(s - 1/2) * x)) / (x:ℂ)^3)
    ?_ ?_ ?_
  · -- plateau derivative: locally zero
    intro x hx
    rw [if_pos hx.2]
    have hev : (fun y : ℝ => (1 - auxF s X y) / (y : ℂ)) =ᶠ[nhds x]
        fun _ : ℝ => (0 : ℂ) := by
      filter_upwards [eventually_abs_sub_lt x
        (by rw [abs_of_pos hx.1]; linarith [hx.2] : 0 < Real.log X - |x|)] with y hy
      have hyle : |y| ≤ Real.log X := by
        have := abs_sub_abs_le_abs_sub y x
        linarith [abs_sub_comm y x ▸ hy]
      rw [auxF_of_le s X hyle, sub_self, zero_div]
    exact (hasDerivAt_const x (0:ℂ)).congr_of_eventuallyEq hev
  · -- tail derivative: differentiate the explicit formula, all in ℂ
    intro x hx
    rw [if_neg (not_lt.mpr (le_of_lt hx))]
    have hxpos : 0 < x := hT0.trans hx
    have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    have h1 : HasDerivAt (fun w : ℂ => 1/w) (-(((x:ℝ):ℂ)^2)⁻¹) ((x:ℝ):ℂ) := by
      simpa [one_div] using hasDerivAt_inv hxc
    have hnum : HasDerivAt (fun w : ℂ => Complex.exp (-(s - 1/2) * w))
        (Complex.exp (-(s - 1/2) * ((x:ℝ):ℂ)) * (-(s - 1/2) * 1)) ((x:ℝ):ℂ) :=
      ((hasDerivAt_id ((x:ℝ):ℂ)).const_mul (-(s - 1/2))).cexp
    have hden : HasDerivAt (fun w : ℂ => w^2)
        ((2:ℕ) * ((x:ℝ):ℂ)^(2-1)) ((x:ℝ):ℂ) := hasDerivAt_pow 2 _
    have hq := hnum.div hden (pow_ne_zero 2 hxc)
    have hC := (h1.sub ((hq.const_mul
      (((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ)))))).comp_ofReal
    have hev : (fun y : ℝ => (1 - auxF s X y) / (y : ℂ)) =ᶠ[nhds x]
        fun y : ℝ => 1/(y:ℂ)
          - ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
              * (Complex.exp (-(s - 1/2) * y) / (y:ℂ)^2) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [auxF_diffQuot_tail_eq s hX y (le_of_lt hy)]
      ring
    refine (hC.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
    ring
  · -- derivative integrability
    rw [show Set.Ici (0:ℝ) = Set.Icc 0 (Real.log X) ∪ Set.Ioi (Real.log X) from
      (Set.Icc_union_Ioi_eq_Ici hT0.le).symm]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · refine (integrableOn_zero :
        IntegrableOn (fun _ : ℝ => (0:ℂ)) (Set.Icc 0 (Real.log X)) volume).congr ?_
      have hae : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc 0 (Real.log X))), x ≠ Real.log X := by
        refine ae_restrict_of_ae ?_
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton]
        exact measure_singleton _
      filter_upwards [ae_restrict_mem measurableSet_Icc, hae] with x hx hxne
      rw [if_pos (lt_of_le_of_ne hx.2 hxne)]
    · -- tail: 1/x² plus the exponentially decaying part
      have hi1 : IntegrableOn (fun x : ℝ => 1/((x:ℝ):ℂ)^2) (Set.Ioi (Real.log X)) := by
        have hreal : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (Real.log X)) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) hT0
        have hcast : IntegrableOn (fun x : ℝ => ((x ^ (-2:ℝ) : ℝ) : ℂ))
            (Set.Ioi (Real.log X)) := hreal.ofReal
        refine hcast.congr_fun (fun x hx => ?_) measurableSet_Ioi
        have hxpos : 0 < x := hT0.trans hx
        have h2 : x ^ (-2 : ℝ) = (x^2)⁻¹ := by
          rw [show (-2 : ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hxpos.le,
            Real.rpow_natCast]
        show ((x ^ (-2:ℝ) : ℝ) : ℂ) = 1/((x:ℝ):ℂ)^2
        rw [h2]
        push_cast
        ring
      have hi2 : IntegrableOn (fun x : ℝ =>
          ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
            * (((s - 1/2) * x + 2) * Complex.exp (-(s - 1/2) * x)) / (x:ℂ)^3)
          (Set.Ioi (Real.log X)) := by
        have hbase := integrableOn_bounded_mul_exp_div (h := s - 1/2) hh hT0
          (φ := fun x : ℝ =>
            ((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
              * (((s - 1/2) * x + 2) / (x:ℂ)^2))
          (C := ‖((Real.log X : ℝ) : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))‖
            * (‖(s - 1/2 : ℂ)‖/Real.log X + 2/(Real.log X)^2)) ?_ ?_
        · refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
          have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT0.trans hx).ne'
          field_simp
        · refine ContinuousOn.mul continuousOn_const
            (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
          intro x hx
          have : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT0.trans hx).ne'
          exact pow_ne_zero 2 this
        · intro x hx
          have hxpos : 0 < x := hT0.trans hx
          rw [norm_mul]
          refine mul_le_mul le_rfl ?_ (norm_nonneg _) (norm_nonneg _)
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
          have hnum : ‖(s - 1/2) * ((x:ℝ):ℂ) + 2‖ ≤ ‖(s - 1/2 : ℂ)‖ * x + 2 := by
            have hht : ‖(s - 1/2) * ((x:ℝ):ℂ)‖ = ‖(s - 1/2 : ℂ)‖ * x := by
              simp [Complex.norm_real, abs_of_pos hxpos]
            have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
            calc ‖(s - 1/2) * ((x:ℝ):ℂ) + 2‖
                ≤ ‖(s - 1/2) * ((x:ℝ):ℂ)‖ + ‖(2:ℂ)‖ := norm_add_le _ _
              _ = ‖(s - 1/2 : ℂ)‖ * x + 2 := by rw [hht, h2]
          calc ‖(s - 1/2) * ((x:ℝ):ℂ) + 2‖ / x^2
              ≤ (‖(s - 1/2 : ℂ)‖ * x + 2) / x^2 := by gcongr
            _ = ‖(s - 1/2 : ℂ)‖/x + 2/x^2 := by field_simp
            _ ≤ ‖(s - 1/2 : ℂ)‖/Real.log X + 2/(Real.log X)^2 := by
                gcongr <;> exact le_of_lt hx
      refine ((hi1.neg).add hi2).congr_fun (fun x hx => ?_) measurableSet_Ioi
      rw [if_neg (not_lt.mpr (le_of_lt hx))]
      simp only [Pi.add_apply, Pi.neg_apply]

/-- **`F_{s,X}` is an admissible test function** for the Weil–Poitou explicit formula,
for `Re s > 1` and `X > 1` — exactly the regime in which the paper first applies the
explicit formula (Lemma 3's proof; `Re s > 1/2` is then reached by analytic
continuation, not by re-checking admissibility). Witness: `ε = (Re s - 1)/2`. -/
theorem isAdmissibleTestFn_auxF {X : ℝ} (hX : 1 < X) (hs : 1 < s.re) :
    IsAdmissibleTestFn (auxF s X) := by
  refine ⟨auxF_neg s X,
    ⟨(s.re - 1)/2, by linarith, ?_, ?_⟩, ?_, auxF_jump_avg s hX⟩
  · exact auxF_mul_exp_bv s hX hs
  · exact auxF_mul_exp_integrable s hX hs
  · simpa only [auxF_zero s (le_of_lt hX)] using auxF_diffQuot_bv s hX hs

end AdmAux

end

end DedekindResidue
