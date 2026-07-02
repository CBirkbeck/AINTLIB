module

public import Mathlib
public import DedekindResidue.AuxiliaryFunction
public import DedekindResidue.CompletedZeta.Normalisation

/-!
# Lemma 2: the Fourier transform of the auxiliary function  (T003)

Belabas–Friedman Lemma 2 (eq. 8): the paper-convention Fourier transform (eq. 2,
`F̂(γ) = ∫ F(t)e^{itγ}dt`) of the test function `F_{s,X}` in closed form. This file builds
it bottom-up: the evenness reduction to a cosine transform, the plateau contribution
`2 sin(γT)/γ`, the exponential-tail integration by parts (paper eq. 7), and the assembly.

The main statement is for `γ ≠ 0`; the `sin(γT)/γ` term forces a separate `γ = 0`
companion (the pointwise limit), faithful to the paper's implicit convention.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real


/-- The paper Fourier transform of an even function reduces to a cosine transform on the
positive ray. -/
theorem paperFourierIntegral_even (F : ℝ → ℂ) (hF : ∀ t, F (-t) = F t) (γ : ℝ)
    (hInt : Integrable (fun t : ℝ => F t * Complex.exp (Complex.I * t * γ))) :
    paperFourierIntegral F γ
      = 2 * ∫ t in Set.Ioi (0:ℝ), F t * ((Real.cos (t * γ) : ℝ) : ℂ) := by
  rw [paperFourierIntegral]
  rw [← integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hInt, Set.compl_Iic]
  have hneg : (∫ t in Set.Iic (0:ℝ), F t * Complex.exp (Complex.I * t * γ))
      = ∫ t in Set.Ioi (0:ℝ), F t * Complex.exp (-(Complex.I * t * γ)) := by
    rw [show Set.Iic (0:ℝ) = Set.Iic (-(0:ℝ)) by norm_num]
    rw [← integral_comp_neg_Ioi (f := fun t : ℝ => F t * Complex.exp (Complex.I * t * γ))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hF]
    push_cast
    ring_nf
  have hInt' : Integrable (fun t : ℝ => F t * Complex.exp (-(Complex.I * t * γ))) := by
    have h1 := hInt.comp_neg
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    show F (-t) * Complex.exp (Complex.I * (-t : ℝ) * γ)
      = F t * Complex.exp (-(Complex.I * t * γ))
    rw [hF]
    push_cast
    ring_nf
  rw [hneg, ← integral_add hInt'.integrableOn hInt.integrableOn]
  · rw [show (2 : ℂ) * (∫ t in Set.Ioi (0:ℝ), F t * ((Real.cos (t * γ) : ℝ) : ℂ))
      = ∫ t in Set.Ioi (0:ℝ), 2 * (F t * ((Real.cos (t * γ) : ℝ) : ℂ)) from
      (integral_const_mul 2 _).symm]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf

open scoped Real in
/-- The plateau contribution: `∫_0^T cos(tγ) dt = sin(Tγ)/γ` (`γ ≠ 0`, `T ≥ 0`). -/
theorem integral_plateau_cos {T γ : ℝ} (hT : 0 ≤ T) (hγ : γ ≠ 0) :
    (∫ t in Set.Ioc (0:ℝ) T, ((Real.cos (t * γ) : ℝ) : ℂ))
      = ((Real.sin (T * γ) / γ : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_comp_mul_right (fun t => Real.cos t) hγ]
  rw [integral_cos]
  simp [div_eq_inv_mul]

end

end DedekindResidue
