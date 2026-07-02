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

end DedekindResidue

end
