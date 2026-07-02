module

public import Mathlib
public import DedekindResidue.CompletedZeta.Existence
public import DedekindResidue.CompletedZeta.GammaStrip

/-!
# Analytic control of the completed Dedekind zeta function  (SP1-AC leaf A2)

Uniform vertical-strip bounds for the Hecke pair's Mellin transforms, from the triangle
inequality applied to the strong pair's full-line Mellin representation:

* `norm_heckeΛ₀_le` — `‖Λ₀(s)‖` is at most the norm-integral at `Re s`;
* `integrable_heckeΛ₀_norm` — those norm-integrals converge at every real exponent;
* `exists_heckeΛ₀_strip_bound` — `‖Λ₀‖` is bounded on every vertical strip, uniformly
  in the imaginary direction (the `x^{σ-1} ≤ x^{a-1} + x^{b-1}` endpoint trick).

Downstream (per `.mathlib-quality/decomposition-sp1ac.md`): Λ- and
`H(s) = s(s-1)Λ_K(s)`-versions, the ζ_K convexity bounds (with `GammaStrip`), Jensen
zero-counting, and the Landau local partial fractions.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real

variable (K : Type*) [Field K] [NumberField K]

/-- Pointwise Mellin triangle inequality for the entire completed theta transform:
`‖Λ₀(s)‖` is at most the norm-integral at the real part. -/
theorem norm_heckeΛ₀_le (s : ℂ) :
    ‖(heckeFEPair K).Λ₀ s‖
      ≤ ∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖ := by
  rw [WeakFEPair.Λ₀, mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- The norm-integrals converge at every real exponent (the strong pair has full-line
Mellin convergence). -/
theorem integrable_heckeΛ₀_norm (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
      (Set.Ioi 0) := by
  have hconv : MellinConvergent ((heckeFEPair K).f_modif) (a : ℂ) :=
    ((heckeFEPair K).toStrongFEPair.hasMellin (a : ℂ)).1
  have hnn : IntegrableOn
      (fun x : ℝ => ‖((x:ℂ) ^ ((a:ℂ) - 1) • (heckeFEPair K).f_modif x)‖)
      (Set.Ioi 0) := hconv.norm
  refine hnn.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show ‖((x:ℂ) ^ ((a:ℂ) - 1) • (heckeFEPair K).f_modif x)‖
    = x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- **AC-A2: uniform vertical-strip bound for `Λ₀`** — on any strip `a ≤ Re s ≤ b`,
`‖Λ₀(s)‖` is bounded by a constant depending only on the strip (and `K`), uniformly
in the imaginary direction. -/
theorem exists_heckeΛ₀_strip_bound (a b : ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖(heckeFEPair K).Λ₀ s‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
    + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖, ?_⟩
  intro s ha hb
  refine le_trans (norm_heckeΛ₀_le K s) ?_
  have hmono : ∀ x ∈ Set.Ioi (0:ℝ),
      x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖
        ≤ x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
          + x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ := by positivity
      nlinarith [norm_nonneg ((heckeFEPair K).f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
    · have h1 : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖ := by positivity
      nlinarith [norm_nonneg ((heckeFEPair K).f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
  calc (∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖)
      ≤ ∫ x in Set.Ioi (0:ℝ),
          (x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
            + x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖) :=
        setIntegral_mono_on (integrable_heckeΛ₀_norm K s.re)
          ((integrable_heckeΛ₀_norm K a).add (integrable_heckeΛ₀_norm K b))
          measurableSet_Ioi hmono
    _ = (∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
          + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ :=
        integral_add (integrable_heckeΛ₀_norm K a) (integrable_heckeΛ₀_norm K b)

end

end DedekindResidue
