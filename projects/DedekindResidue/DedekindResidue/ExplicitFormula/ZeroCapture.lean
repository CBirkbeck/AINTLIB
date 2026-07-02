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

/-- **Euler-product nonvanishing**: `ζ_K(s) ≠ 0` for `Re s > 1`. Each Euler factor is
`1 + f_𝔭` with `f_𝔭 = (1 − N𝔭^{-s})⁻¹ − 1` absolutely summable, so the product is a
nonzero limit (`tprod_one_add_ne_zero_of_summable`, the Dedekind-eta pattern). -/
theorem dedekindZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 := by
  rw [Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hs]
  set x : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ :=
    fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hx
  -- factor norms are at most 1/2
  have hnormeq : ∀ 𝔭, ‖x 𝔭‖ = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) := by
    intro 𝔭
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    rw [hx]
    simp only
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hhalf : ∀ 𝔭, ‖x 𝔭‖ ≤ 1/2 := by
    intro 𝔭
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      have : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
      exact_mod_cast this
    rw [hnormeq 𝔭]
    have hstep1 : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) ≤ (2:ℝ) ^ (-s.re) := by
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
      exact Real.rpow_le_rpow (by norm_num) h2 (by linarith)
    have hstep2 : (2:ℝ) ^ (-s.re) ≤ (2:ℝ) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hstep3 : (2:ℝ) ^ (-(1:ℝ)) = 1/2 := by
      rw [Real.rpow_neg_one]
      norm_num
    calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) ≤ (2:ℝ) ^ (-s.re) := hstep1
      _ ≤ (2:ℝ) ^ (-(1:ℝ)) := hstep2
      _ = 1/2 := hstep3
  have hfac_ne : ∀ 𝔭, (1 : ℂ) - x 𝔭 ≠ 0 := by
    intro 𝔭 h0
    have h1 : x 𝔭 = 1 := by linear_combination -h0
    have := hhalf 𝔭
    rw [h1] at this
    norm_num at this
  -- summability of the factor norms
  have hσsum : Summable (fun I : Chebotarev.NonzeroIdeal K =>
      (Ideal.absNorm I.1 : ℝ) ^ (-s.re)) := by
    have h1 := (Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow K
      (s := ((s.re : ℝ) : ℂ)) (by simpa using hs)).summable
    have h1' : Summable (fun I : Chebotarev.NonzeroIdeal K =>
        (((Ideal.absNorm I.1 : ℝ) ^ (-s.re) : ℝ) : ℂ)) := by
      refine h1.congr (fun I => ?_)
      rw [show ((Ideal.absNorm I.1 : ℕ) : ℂ) = (((Ideal.absNorm I.1 : ℝ)) : ℂ) by
          push_cast; ring,
        show -(((s.re : ℝ)) : ℂ) = (((-s.re : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    exact Complex.summable_ofReal.mp h1'
  have hprime_sum : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      ‖x 𝔭‖) := by
    have hinj : Function.Injective
        (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
          (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K)) := by
      intro 𝔭 𝔮 h
      have h' : (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K) = ⟨𝔮.1, 𝔮.2.2⟩ := h
      exact Subtype.ext (Subtype.mk_eq_mk.mp h')
    have hcomp := hσsum.comp_injective hinj
    exact hcomp.congr (fun 𝔭 => (hnormeq 𝔭).symm)
  -- the correction terms and their bound
  have hfbound : ∀ 𝔭, ‖(1 - x 𝔭)⁻¹ - 1‖ ≤ 2 * ‖x 𝔭‖ := by
    intro 𝔭
    have hid : (1 - x 𝔭)⁻¹ - 1 = x 𝔭 * (1 - x 𝔭)⁻¹ := by
      have he := hfac_ne 𝔭
      field_simp
      ring
    rw [hid, norm_mul]
    have hlow : (1:ℝ)/2 ≤ ‖1 - x 𝔭‖ := by
      have h1 : ‖(1:ℂ)‖ - ‖x 𝔭‖ ≤ ‖1 - x 𝔭‖ := norm_sub_norm_le _ _
      rw [norm_one] at h1
      linarith [hhalf 𝔭]
    have hinv : ‖(1 - x 𝔭)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      rw [show (2:ℝ) = (1/2)⁻¹ by norm_num]
      refine (inv_le_inv₀ ?_ (by norm_num)).mpr hlow
      have := hhalf 𝔭
      have h1 : (0:ℝ) < 1/2 := by norm_num
      linarith
    calc ‖x 𝔭‖ * ‖(1 - x 𝔭)⁻¹‖ ≤ ‖x 𝔭‖ * 2 :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = 2 * ‖x 𝔭‖ := by ring
  have hfsum : Summable (fun 𝔭 => ‖(1 - x 𝔭)⁻¹ - 1‖) :=
    Summable.of_nonneg_of_le (fun 𝔭 => norm_nonneg _) hfbound (hprime_sum.mul_left 2)
  -- assemble
  have hcongr : (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 - x 𝔭)⁻¹)
      = ∏' 𝔭, (1 + ((1 - x 𝔭)⁻¹ - 1)) :=
    tprod_congr (fun 𝔭 => by ring)
  rw [hcongr]
  refine tprod_one_add_ne_zero_of_summable (fun 𝔭 => ?_) hfsum
  rw [show (1:ℂ) + ((1 - x 𝔭)⁻¹ - 1) = (1 - x 𝔭)⁻¹ by ring]
  exact inv_ne_zero (hfac_ne 𝔭)

/-- `H = completedDedekindZetaEntire` does not vanish on `Re s > 1`. -/
theorem completedDedekindZetaEntire_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZetaEntire K s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h0
    rw [h0] at hs
    simp at hs
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hs, completedZetaPrefactor]
  refine mul_ne_zero (mul_ne_zero hs0 ?_) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  · intro h0
    have hbase : ((|discr K| : ℝ) : ℂ) ≠ 0 := by
      have h2 : |discr K| ≠ 0 := abs_ne_zero.mpr (NumberField.discr_ne_zero K)
      exact_mod_cast h2
    exact hbase ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  · exact gammaFactor_ne_zero_of_re_pos K (by linarith)
  · exact dedekindZeta_ne_zero_of_one_lt_re K hs
/-- `H` does not vanish on `Re s < 0` (functional-equation reflection). -/
theorem completedDedekindZetaEntire_ne_zero_of_re_lt_zero {s : ℂ} (hs : s.re < 0) :
    completedDedekindZetaEntire K s ≠ 0 := by
  rw [← completedDedekindZetaEntire_one_sub K s]
  refine completedDedekindZetaEntire_ne_zero_of_one_lt_re K ?_
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- **Strip confinement**: every zero of `H` has real part in `[0, 1]`. -/
theorem re_mem_of_completedDedekindZetaEntire_eq_zero {ρ : ℂ}
    (h0 : completedDedekindZetaEntire K ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  constructor
  · by_contra h
    exact completedDedekindZetaEntire_ne_zero_of_re_lt_zero K (by linarith) h0
  · by_contra h
    exact completedDedekindZetaEntire_ne_zero_of_one_lt_re K (by linarith) h0

/-- **Separation pigeonhole** (SP2-RECT R-e core): in any unit interval there is a
point at distance at least `1/(2(N+1))` from every member of a finite set of size at
most `N` — among the `N+1` midpoints of equal subintervals, at least one is far from
all of `S`, since distinct midpoints cannot share a close neighbour. -/
theorem exists_dist_ge_of_card_le {S : Finset ℝ} {N : ℕ} (hcard : S.card ≤ N) (a : ℝ) :
    ∃ t ∈ Set.Icc a (a + 1), ∀ s ∈ S, 1 / (2 * (N + 1)) ≤ |t - s| := by
  classical
  by_contra hcon
  push Not at hcon
  have hNpos : (0:ℝ) < 2 * ((N:ℝ) + 1) := by positivity
  -- each midpoint has a close member of S
  have hmid : ∀ k : Fin (N + 1), ∃ s ∈ S,
      |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1))) - s| < 1 / (2 * ((N:ℝ) + 1)) := by
    intro k
    have hk1 : (0:ℝ) ≤ (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)) := by positivity
    have hk2 : (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)) ≤ 1 := by
      rw [div_le_one hNpos]
      have : (k:ℝ) ≤ N := by
        have := k.2
        have h1 : (k:ℕ) ≤ N := by omega
        exact_mod_cast h1
      linarith
    have hmem : a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)) ∈ Set.Icc a (a + 1) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    obtain ⟨s, hs, hlt⟩ := hcon _ hmem
    exact ⟨s, hs, by linarith [hlt]⟩
  choose f hfS hfclose using hmid
  -- pigeonhole: N+1 midpoints into ≤ N members
  have hlt : S.card < (Finset.univ : Finset (Fin (N + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, _, k', hk'mem, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun k _ => hfS k)
  -- two distinct midpoints within 1/(N+1) of the same point: contradiction
  have h1 := hfclose k
  have h2 := hfclose k'
  rw [heq] at h1
  have htri : |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
      - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))| < 1 / ((N:ℝ) + 1) := by
    calc |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
        - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))|
        ≤ |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1))) - f k'|
          + |f k' - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))| := abs_sub_le _ _ _
      _ < 1 / (2 * ((N:ℝ) + 1)) + 1 / (2 * ((N:ℝ) + 1)) := by
          rw [abs_sub_comm (f k')]
          exact add_lt_add h1 h2
      _ = 1 / ((N:ℝ) + 1) := by
          field_simp
          ring
  have hdiff : |(a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
      - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))|
      = |(k:ℝ) - (k':ℝ)| / ((N:ℝ) + 1) := by
    rw [show (a + (2 * (k:ℝ) + 1) / (2 * ((N:ℝ) + 1)))
        - (a + (2 * (k':ℝ) + 1) / (2 * ((N:ℝ) + 1)))
        = ((k:ℝ) - (k':ℝ)) / ((N:ℝ) + 1) by field_simp; ring]
    rw [abs_div]
    congr 1
    rw [abs_of_pos (by positivity : (0:ℝ) < (N:ℝ) + 1)]
  have hge : (1:ℝ) ≤ |(k:ℝ) - (k':ℝ)| := by
    have hkk' : (k:ℕ) ≠ (k':ℕ) := fun h => hne (Fin.ext h)
    have h1 : ((k:ℕ) : ℤ) ≠ ((k':ℕ) : ℤ) := by exact_mod_cast hkk'
    have h2 : (1:ℤ) ≤ |((k:ℕ) : ℤ) - ((k':ℕ) : ℤ)| := Int.one_le_abs (sub_ne_zero_of_ne h1)
    have h3 : ((|((k:ℕ) : ℤ) - ((k':ℕ) : ℤ)| : ℤ) : ℝ) = |(k:ℝ) - (k':ℝ)| := by
      push_cast
      ring_nf
    calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
      _ ≤ ((|((k:ℕ) : ℤ) - ((k':ℕ) : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h2
      _ = |(k:ℝ) - (k':ℝ)| := h3
  rw [hdiff] at htri
  have : (1:ℝ) / ((N:ℝ) + 1) ≤ |(k:ℝ) - (k':ℝ)| / ((N:ℝ) + 1) := by
    gcongr
  linarith

end DedekindResidue

end
