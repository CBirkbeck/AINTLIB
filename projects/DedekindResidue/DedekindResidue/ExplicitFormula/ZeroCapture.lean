module

public import Mathlib
public import DedekindResidue.ExplicitFormula.RectangleContour
public import DedekindResidue.CompletedZeta.AnalyticControl
public import CebotarevDensity.NumberFieldEulerProduct

/-!
# Zero capture on the explicit-formula rectangle  (SP2-RECT R-a)

The residue side of Poitou's contour identity needs `H = completedDedekindZetaEntire`
peeled into (divisor product)·(zero-free analytic) on an open **rectangle** — the
rectangle version of the ball peeling from SP1-AC. The nonvanishing witness is the
real ray: `H(x) ≠ 0` for real `x > 1`, by the Euler-product positivity
`Chebotarev.dedekindZeta_re_pos_of_one_lt` (first cross-project reuse) together with
the nonvanishing of `s(s−1)`, `|Δ|^{s/2}` and the archimedean factor.

Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-RECT R-a.
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- `H` does not vanish on the real ray `x > 1`: all factors of
`H = s(s−1)·|Δ|^{s/2}·γ(s)·ζ_K(s)` are nonzero there (the Euler product keeps
`Re ζ_K(x) > 0`). This is the witness for rectangle zero-peeling. -/
theorem completedDedekindZetaEntire_ne_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    completedDedekindZetaEntire K (x : ℂ) ≠ 0 := by
  have hx0 : (x : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hx1 : (x : ℂ) ≠ 1 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hxre : 1 < ((x : ℂ)).re := by simpa using hx
  rw [completedDedekindZetaEntire_eq K hx0 hx1,
    completedDedekindZeta_eq_of_one_lt_re K hxre, completedZetaPrefactor]
  refine mul_ne_zero (mul_ne_zero hx0 ?_) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  · -- |Δ|^{x/2} ≠ 0: nonzero base
    intro h0
    have hbase : ((|discr K| : ℝ) : ℂ) ≠ 0 := by
      have h1 := NumberField.discr_ne_zero K
      have h2 : |discr K| ≠ 0 := abs_ne_zero.mpr h1
      exact_mod_cast h2
    exact hbase ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  · exact gammaFactor_ne_zero_of_re_pos K (by simpa using (by linarith : (0:ℝ) < x))
  · -- ζ_K(x) ≠ 0 from positive real part
    intro h0
    have := Chebotarev.dedekindZeta_re_pos_of_one_lt (L := K) x hx
    rw [h0] at this
    simp at this

/-- Open rectangles are convex: they are intersections of linear preimages of
intervals under `re` and `im`. -/
theorem convex_reProdIm {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ (s ×ℂ t) :=
  (hs.linear_preimage Complex.reLm).inter (ht.linear_preimage Complex.imLm)

/-- Open rectangles are bounded. -/
theorem isBounded_Ioo_reProdIm (a b c d : ℝ) :
    Bornology.IsBounded (Set.Ioo a b ×ℂ Set.Ioo c d) :=
  (Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo c d)

/-- **Rectangle zero-peeling** (SP2-RECT R-a): on an open rectangle where `H` is not
identically zero, `H` factors as the divisor product times a zero-free analytic
function — the rectangle version of `exists_H_ball_factorization`. -/
theorem exists_H_rectangle_factorization {a b c d : ℝ}
    {w : ℂ} (hw : w ∈ Set.Ioo a b ×ℂ Set.Ioo c d)
    (hHw : completedDedekindZetaEntire K w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Set.Ioo a b ×ℂ Set.Ioo c d)
      ∧ (∀ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d, g z ≠ 0)
      ∧ ∀ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d,
          completedDedekindZetaEntire K z
            = (∏ᶠ u, (z - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K)
                (Set.Ioo a b ×ℂ Set.Ioo c d)) u)) * g z := by
  set U : Set ℂ := Set.Ioo a b ×ℂ Set.Ioo c d with hU
  have hUo : IsOpen U := (isOpen_Ioo).reProdIm (isOpen_Ioo)
  have hUc : Convex ℝ U := convex_reProdIm (convex_Ioo a b) (convex_Ioo c d)
  have hHmero : MeromorphicOn (completedDedekindZetaEntire K) U := fun z _ =>
    ((differentiable_completedDedekindZetaEntire K).analyticAt z).meromorphicAt
  have hordw : meromorphicOrderAt (completedDedekindZetaEntire K) w ≠ ⊤ := by
    rw [((differentiable_completedDedekindZetaEntire K).analyticAt w).meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (completedDedekindZetaEntire K) w = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hHw)
    rw [h0]
    simp
  have hord : ∀ u : U, meromorphicOrderAt (completedDedekindZetaEntire K) u ≠ ⊤ := by
    intro u
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hHmero
      hUc.isPreconnected hw u.2 hordw
  -- the rectangle sits in a compact closed ball, so the divisor support is finite
  obtain ⟨R₀, hR₀⟩ := (isBounded_Ioo_reProdIm a b c d).subset_closedBall (0 : ℂ)
  have hfin : ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun z _ => ((differentiable_completedDedekindZetaEntire K).analyticAt z).meromorphicAt)
      (isCompact_closedBall (0:ℂ) R₀) hR₀
  obtain ⟨g, hganal, hgne, heq⟩ :=
    MeromorphicOn.extract_zeros_poles hHmero hord hfin
  have hfinsupp : Function.HasFiniteSupport
      ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) : ℂ → ℤ) := hfin
  have hdivpos : ∀ u : ℂ,
      0 ≤ (MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u := by
    intro u
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ =>
      (differentiable_completedDedekindZetaEntire K).analyticAt z)) u
  have hprodanal : ∀ z : ℂ, AnalyticAt ℂ
      (∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u)) z :=
    fun z => Function.FactorizedRational.analyticAt (hdivpos z)
  have heqOn : Set.EqOn (completedDedekindZetaEntire K)
      ((∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u))
        • g) U := by
    refine eqOn_of_eventuallyEq_codiscreteWithin hUo heq
      (differentiable_completedDedekindZetaEntire K).continuous.continuousOn ?_
    refine ContinuousOn.smul ?_ (hganal.continuousOn)
    exact fun z _ => (hprodanal z).continuousAt.continuousWithinAt
  refine ⟨g, hganal, fun z hz => hgne ⟨z, hz⟩, fun z hz => ?_⟩
  have := heqOn hz
  rw [this, Pi.smul_apply', smul_eq_mul]
  congr 1
  rw [Function.FactorizedRational.finprod_eq_fun hfinsupp]

/-- **The rectangle argument principle for `H`** (SP2-RECT R-d): if `H` has no zeros
on the boundary of the rectangle and `Φ` is holomorphic at every point of the closed
rectangle, then `∮_{∂R} Φ·H'/H = 2πi·∑_ρ m_ρ·Φ(ρ)`, summed over the divisor of `H`
on the open rectangle. -/
theorem rectangleIntegral_mul_logDeriv_H {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Φ ζ)
    (hbound : ∀ ζ ∈ rectangleBoundary z w, completedDedekindZetaEntire K ζ ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Set.Ioo (z.re - 1) (w.re + 1) ×ℂ Set.Ioo (z.im - 1) (w.im + 1))
    (hHw₀ : completedDedekindZetaEntire K w₀ ≠ 0) :
    rectangleIntegral (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ) z w
      = 2 * Real.pi * Complex.I
        * ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
            (Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im)) ρ : ℂ)) * Φ ρ := by
  classical
  set U' : Set ℂ := Set.Ioo (z.re - 1) (w.re + 1) ×ℂ Set.Ioo (z.im - 1) (w.im + 1) with hU'
  have hU'o : IsOpen U' := isOpen_Ioo.reProdIm isOpen_Ioo
  set V : Set ℂ := Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im with hV
  set Rc : Set ℂ := Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im with hRc
  -- inclusions
  have hRcU' : Rc ⊆ U' := by
    intro ζ hζ
    rw [hRc, Complex.mem_reProdIm,
      Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le] at hζ
    rw [hU', Complex.mem_reProdIm]
    obtain ⟨h1, h2⟩ := hζ
    rw [Set.mem_Icc] at h1 h2
    constructor <;> rw [Set.mem_Ioo] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hbdRc : rectangleBoundary z w ⊆ Rc := by
    intro ζ hζ
    rw [rectangleBoundary] at hζ
    rw [hRc, Complex.mem_reProdIm]
    rcases hζ with hζ | hζ <;> rw [Complex.mem_reProdIm] at hζ
    · refine ⟨hζ.1, ?_⟩
      rcases hζ.2 with h | h <;> rw [h]
      · exact Set.left_mem_uIcc
      · exact Set.right_mem_uIcc
    · refine ⟨?_, hζ.2⟩
      rcases hζ.1 with h | h <;> rw [h]
      · exact Set.left_mem_uIcc
      · exact Set.right_mem_uIcc
  have hVU' : V ⊆ U' := by
    intro ζ hζ
    rw [hV, Complex.mem_reProdIm] at hζ
    rw [hU', Complex.mem_reProdIm]
    obtain ⟨h1, h2⟩ := hζ
    rw [Set.mem_Ioo] at h1 h2
    constructor <;> rw [Set.mem_Ioo] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- closed-minus-open is the boundary
  have hsplit_closed : ∀ v ∈ Rc, v ∈ V ∨ v ∈ rectangleBoundary z w := by
    intro v hv
    rw [hRc, Complex.mem_reProdIm, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le] at hv
    obtain ⟨h1, h2⟩ := hv
    rw [Set.mem_Icc] at h1 h2
    by_cases hin : v ∈ V
    · exact Or.inl hin
    · refine Or.inr ?_
      rw [hV, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo] at hin
      push Not at hin
      rw [rectangleBoundary]
      by_cases hres : v.re = z.re ∨ v.re = w.re
      · refine Set.mem_union_right _ ?_
        rw [Complex.mem_reProdIm]
        refine ⟨hres, ?_⟩
        rw [Set.uIcc_of_le him.le, Set.mem_Icc]
        exact h2
      · push Not at hres
        refine Set.mem_union_left _ ?_
        rw [Complex.mem_reProdIm]
        constructor
        · rw [Set.uIcc_of_le hre.le, Set.mem_Icc]
          exact h1
        · have hre1 : z.re < v.re := lt_of_le_of_ne h1.1 (Ne.symm hres.1)
          have hre2 : v.re < w.re := lt_of_le_of_ne h1.2 hres.2
          have himp := hin ⟨hre1, hre2⟩
          rcases eq_or_lt_of_le h2.1 with h | h
          · exact Or.inl h.symm
          · rcases eq_or_lt_of_le h2.2 with h' | h'
            · exact Or.inr h'
            · exact absurd (himp h) (not_le.mpr h')
  -- peel H on the enlarged rectangle
  obtain ⟨g, hganal, hgne, hfac⟩ := exists_H_rectangle_factorization K hw₀ hHw₀
  set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor (completedDedekindZetaEntire K) U') u
    with hD
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ := fun ζ =>
    (differentiable_completedDedekindZetaEntire K).analyticAt ζ
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ => hHanal ζ)) u
  obtain ⟨R₀, hR₀⟩ := (isBounded_Ioo_reProdIm (z.re - 1) (w.re + 1) (z.im - 1)
    (w.im + 1)).subset_closedBall (0 : ℂ)
  have hfin : (Function.support D).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset
      (fun ζ _ => (hHanal ζ).meromorphicAt) (isCompact_closedBall (0:ℂ) R₀) hR₀
  set F : Finset ℂ := hfin.toFinset with hF
  have hP₁ : ∀ ζ : ℂ, (∏ᶠ u, (ζ - u) ^ D u) = ∏ u ∈ F, (ζ - u) ^ D u := by
    intro ζ
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    refine hfin.mem_toFinset.mpr (Function.mem_support.mpr ?_)
    intro h0
    rw [h0, zpow_zero] at hu
    exact hu rfl
  have hfacF : ∀ ζ ∈ U', completedDedekindZetaEntire K ζ
      = (∏ u ∈ F, (ζ - u) ^ D u) * g ζ := by
    intro ζ hζ
    rw [hfac ζ hζ, hP₁ ζ]
  -- points of F are zeros of H
  have hFzero : ∀ u ∈ F, completedDedekindZetaEntire K u = 0 := by
    intro u hu
    by_contra hne0
    have hord0 : analyticOrderAt (completedDedekindZetaEntire K) u = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne0)
    have huU' : u ∈ U' := (MeromorphicOn.divisor (completedDedekindZetaEntire K)
      U').supportWithinDomain (hfin.mem_toFinset.mp hu)
    have hDu : D u = 0 := by
      rw [hD]
      simp only
      rw [MeromorphicOn.divisor_apply (fun ζ _ => (hHanal ζ).meromorphicAt) huU',
        (hHanal u).meromorphicOrderAt_eq, hord0]
      simp
    exact (Function.mem_support.mp (hfin.mem_toFinset.mp hu)) hDu
  -- boundary facts
  have hbdne : ∀ ζ ∈ rectangleBoundary z w, ∀ u ∈ F, ζ ≠ u := by
    intro ζ hζ u hu h0
    exact hbound ζ hζ (h0 ▸ hFzero u hu)
  have hbdg : ∀ ζ ∈ rectangleBoundary z w, g ζ ≠ 0 :=
    fun ζ hζ => hgne ζ (hRcU' (hbdRc hζ))
  -- pointwise boundary identity
  have hpt : Set.EqOn (fun ζ => Φ ζ * logDeriv (completedDedekindZetaEntire K) ζ)
      (fun ζ => (∑ u ∈ F, (D u : ℂ) * (Φ ζ * (ζ - u)⁻¹)) + Φ ζ * logDeriv g ζ)
      (rectangleBoundary z w) := by
    intro ζ hζ
    simp only
    rw [logDeriv_eq_sum_add_of_factorization hU'o hfacF hDnn hganal
      (hRcU' (hbdRc hζ)) (hbdg ζ hζ) (fun u hu => hbdne ζ hζ u hu)]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    ring
  -- continuity of the pieces on the boundary
  have hΦcont : ContinuousOn Φ (rectangleBoundary z w) :=
    fun ζ hζ => (hΦ ζ (hbdRc hζ)).continuousAt.continuousWithinAt
  have hsum_cont : ∀ u ∈ F, ContinuousOn
      (fun ζ => (D u : ℂ) * (Φ ζ * (ζ - u)⁻¹)) (rectangleBoundary z w) := by
    intro u hu
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul hΦcont ?_)
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro ζ hζ
    exact sub_ne_zero_of_ne (hbdne ζ hζ u hu)
  have hlast_cont : ContinuousOn (fun ζ => Φ ζ * logDeriv g ζ)
      (rectangleBoundary z w) := by
    refine ContinuousOn.mul hΦcont ?_
    have hld : (logDeriv g) = fun ζ => deriv g ζ / g ζ := rfl
    rw [hld]
    refine ContinuousOn.div ?_ ?_ ?_
    · intro ζ hζ
      exact ((hganal ζ (hRcU' (hbdRc hζ))).deriv.continuousAt).continuousWithinAt
    · intro ζ hζ
      exact ((hganal ζ (hRcU' (hbdRc hζ))).continuousAt).continuousWithinAt
    · intro ζ hζ
      exact hbdg ζ hζ
  -- split the boundary integral
  rw [rectangleIntegral_congr hpt]
  rw [rectangleIntegral_add (by
    refine continuousOn_finsetSum F (fun u hu => hsum_cont u hu)) hlast_cont]
  rw [rectangleIntegral_finset_sum F _ hsum_cont]
  -- more inclusions
  have hVRc : V ⊆ Rc := by
    intro ζ hζ
    rw [hV, Complex.mem_reProdIm] at hζ
    rw [hRc, Complex.mem_reProdIm, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
    exact ⟨Set.Ioo_subset_Icc_self hζ.1, Set.Ioo_subset_Icc_self hζ.2⟩
  have hminmax : Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Set.Ioo (min z.im w.im) (max z.im w.im) = V := by
    rw [hV, min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
      max_eq_right him.le]
  -- the zero-free part integrates to zero (Goursat)
  have hΦcontRc : ContinuousOn Φ Rc :=
    fun ζ hζ => (hΦ ζ hζ).continuousAt.continuousWithinAt
  have hglast : rectangleIntegral (fun ζ => Φ ζ * logDeriv g ζ) z w = 0 := by
    refine rectangleIntegral_eq_zero Set.countable_empty ?_ ?_
    · refine ContinuousOn.mul hΦcontRc ?_
      have hld : (logDeriv g) = fun ζ => deriv g ζ / g ζ := rfl
      rw [hld]
      refine ContinuousOn.div ?_ ?_ ?_
      · exact fun ζ hζ => ((hganal ζ (hRcU' hζ)).deriv.continuousAt).continuousWithinAt
      · exact fun ζ hζ => ((hganal ζ (hRcU' hζ)).continuousAt).continuousWithinAt
      · exact fun ζ hζ => hgne ζ (hRcU' hζ)
    · intro x hx
      have hxV : x ∈ V := by
        rw [← hminmax]
        exact hx.1
      refine DifferentiableAt.mul (hΦ x (hVRc hxV)) ?_
      have hld : (logDeriv g) = fun ζ => deriv g ζ / g ζ := rfl
      rw [hld]
      refine DifferentiableAt.div ?_ ?_ ?_
      · exact ((hganal x (hVU' hxV)).deriv).differentiableAt
      · exact (hganal x (hVU' hxV)).differentiableAt
      · exact hgne x (hVU' hxV)
  rw [hglast, add_zero]
  -- evaluate each peeled term
  have heval : ∀ u ∈ F, rectangleIntegral (fun ζ => Φ ζ * (ζ - u)⁻¹) z w
      = if u ∈ V then 2 * Real.pi * Complex.I * Φ u else 0 := by
    intro u hu
    by_cases hin : u ∈ V
    · rw [if_pos hin]
      have hin' := hin
      rw [hV, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo] at hin'
      exact rectangleIntegral_cauchy hΦ hin'.1.1 hin'.1.2 hin'.2.1 hin'.2.2
    · rw [if_neg hin]
      have hunotRc : u ∉ Rc := by
        intro huRc
        rcases hsplit_closed u huRc with h | h
        · exact hin h
        · exact hbound u h (hFzero u hu)
      refine rectangleIntegral_eq_zero Set.countable_empty ?_ ?_
      · refine ContinuousOn.mul hΦcontRc ?_
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro ζ hζ
        refine sub_ne_zero_of_ne ?_
        intro h0
        exact hunotRc (h0 ▸ hζ)
      · intro x hx
        have hxV : x ∈ V := by
          rw [← hminmax]
          exact hx.1
        refine DifferentiableAt.mul (hΦ x (hVRc hxV)) ?_
        refine DifferentiableAt.inv (differentiableAt_id.sub_const u) ?_
        refine sub_ne_zero_of_ne ?_
        intro h0
        exact hunotRc (h0 ▸ hVRc hxV)
  -- fold the sum into the divisor finsum
  have hDV : ∀ u ∈ V, (MeromorphicOn.divisor (completedDedekindZetaEntire K) V) u
      = D u := by
    intro u huV
    rw [hD]
    simp only
    rw [MeromorphicOn.divisor_apply (fun ζ _ => (hHanal ζ).meromorphicAt) huV,
      MeromorphicOn.divisor_apply (fun ζ _ => (hHanal ζ).meromorphicAt) (hVU' huV)]
  have hsupp : (Function.support
      (fun ρ => (((MeromorphicOn.divisor (completedDedekindZetaEntire K) V) ρ : ℂ)) * Φ ρ))
      ⊆ (F : Set ℂ) := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hdV : (MeromorphicOn.divisor (completedDedekindZetaEntire K) V) ρ ≠ 0 := by
      intro h0
      rw [h0] at hρ
      simp at hρ
    have hρV : ρ ∈ V := by
      by_contra hnot
      exact hdV (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnot)
    have : D ρ ≠ 0 := by
      rw [← hDV ρ hρV]
      exact hdV
    exact hfin.mem_toFinset.mpr (Function.mem_support.mpr this)
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [rectangleIntegral_const_mul, heval u hu]
  by_cases hin : u ∈ V
  · rw [if_pos hin, hDV u hin]
    ring
  · rw [if_neg hin,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hin]
    simp

end DedekindResidue

end
