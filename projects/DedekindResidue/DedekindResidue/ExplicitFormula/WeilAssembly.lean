/-
DedekindResidue: assembly of Weil's explicit formula (Poitou's formula (6)).

This file combines the zero-capture contour (Prop 1, `ZeroCapture.lean`), the
prime side (Prop 2, `PrimeSide.lean`/`FourierJordan.lean`) and the Γ-side
(Prop 3 + I_G, `GammaSide.lean`) into Poitou's explicit formula, following
"Sur les petits discriminants" (Séminaire DPP 1976/77, exposé 6).
-/
module

public import Mathlib
public import DedekindResidue.ExplicitFormula.ZeroCapture
public import DedekindResidue.ExplicitFormula.GammaSide

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex intervalIntegral Real Filter NumberField
open scoped ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- **The right-edge split of `Λ_ent'/Λ_ent`** (Poitou p. 6-01/6-02): on `Re s > 1`,

`logDeriv Λ_ent(s) = 1/s + 1/(s-1) + (1/2)log|d| + γ_K'/γ_K(s) + ζ_K'/ζ_K(s)`. -/
theorem logDeriv_completedDedekindZetaEntire_split {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedDedekindZetaEntire K) s
      = 1/s + 1/(s-1) + ((Real.log |NumberField.discr K| : ℝ) : ℂ)/2
        + logDeriv (gammaFactor K) s
        + logDeriv (NumberField.dedekindZeta K) s := by
  have hUo : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h0
    rw [h0, Complex.one_re] at hs
    linarith
  have hspos : 0 < s.re := by linarith
  have hdiscr0 : (0:ℝ) < (|NumberField.discr K| : ℝ) := by
    have h0 : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
    have h1 : 0 < |NumberField.discr K| := abs_pos.mpr h0
    exact_mod_cast h1
  have hdiscrC : (((|NumberField.discr K| : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdiscr0.ne'
  -- the eventual product form
  have hev : completedDedekindZetaEntire K =ᶠ[nhds s]
      fun z => z * (z - 1) * (((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z)) := by
    filter_upwards [hUo.mem_nhds hs] with z hz
    have hz1 : (1:ℝ) < z.re := hz
    have hz0' : z ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hz1
      linarith
    have hz1' : z ≠ 1 := by
      intro h0
      rw [h0, Complex.one_re] at hz1
      linarith
    rw [completedDedekindZetaEntire_eq K hz0' hz1',
      completedDedekindZeta_eq_of_one_lt_re K hz1, completedZetaPrefactor]
    ring
  have hld : logDeriv (completedDedekindZetaEntire K) s
      = logDeriv (fun z : ℂ => z * (z - 1) * (((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z))) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hld]
  -- nonvanishing and differentiability of the factors
  have hγne : gammaFactor K s ≠ 0 := gammaFactor_ne_zero_of_re_pos K hspos
  have hζne : NumberField.dedekindZeta K s ≠ 0 := dedekindZeta_ne_zero_of_one_lt_re K hs
  have hγd : DifferentiableAt ℂ (gammaFactor K) s :=
    ((differentiableAt_Gammaℝ_of_re_pos hspos).pow _).mul
      ((differentiableAt_Gammaℂ_of_re_pos hspos).pow _)
  have hcpow_d : DifferentiableAt ℂ
      (fun z : ℂ => ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)) s := by
    have h0 : HasDerivAt (fun w : ℂ => w / 2) (1/2) s := by
      have h1 := (hasDerivAt_id s).div_const (2:ℂ)
      have h3 : (1:ℂ)/2 = 1/2 := by norm_num
      rw [h3] at h1
      exact h1
    exact (h0.const_cpow (Or.inl hdiscrC)).differentiableAt
  have hcpow_ne : ((|NumberField.discr K| : ℝ) : ℂ) ^ (s/2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hdiscrC
  have hζd : DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
    have hev2 : NumberField.dedekindZeta K =ᶠ[nhds s]
        fun z => completedDedekindZetaEntire K z
          / (z * (z - 1) * (((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
              * gammaFactor K z)) := by
      filter_upwards [hUo.mem_nhds hs] with z hz
      have hz1 : (1:ℝ) < z.re := hz
      have hzpos : 0 < z.re := by linarith
      have hz0' : z ≠ 0 := by
        intro h0
        rw [h0, Complex.zero_re] at hz1
        linarith
      have hz1' : z ≠ 1 := by
        intro h0
        rw [h0, Complex.one_re] at hz1
        linarith
      have hcne : ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
        exact Or.inl hdiscrC
      have hγnez : gammaFactor K z ≠ 0 := gammaFactor_ne_zero_of_re_pos K hzpos
      rw [completedDedekindZetaEntire_eq K hz0' hz1',
        completedDedekindZeta_eq_of_one_lt_re K hz1, completedZetaPrefactor]
      field_simp
    rw [hev2.differentiableAt_iff]
    refine DifferentiableAt.div ((differentiable_completedDedekindZetaEntire K) s) ?_ ?_
    · exact (differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (hcpow_d.mul hγd)
    · refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) ?_
      exact mul_ne_zero hcpow_ne (gammaFactor_ne_zero_of_re_pos K hspos)
  have hγζne : gammaFactor K s * NumberField.dedekindZeta K s ≠ 0 := mul_ne_zero hγne hζne
  have hγζd : DifferentiableAt ℂ
      (fun z => gammaFactor K z * NumberField.dedekindZeta K z) s := hγd.mul hζd
  have hpre_ne : ((|NumberField.discr K| : ℝ) : ℂ) ^ (s/2)
      * (gammaFactor K s * NumberField.dedekindZeta K s) ≠ 0 := by
    refine mul_ne_zero ?_ hγζne
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hdiscrC
  have hpre_d : DifferentiableAt ℂ
      (fun z : ℂ => ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z)) s :=
    hcpow_d.mul hγζd
  have hid_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hid_d : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  -- peel the factors
  rw [logDeriv_mul (f := fun z : ℂ => z * (z - 1))
      (g := fun z : ℂ => ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z)) s hid_ne hpre_ne hid_d hpre_d]
  rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hs0
      (sub_ne_zero.mpr hs1) differentiableAt_id (differentiableAt_id.sub_const 1)]
  rw [logDeriv_cpow_half_mul (f := fun z : ℂ => gammaFactor K z
      * NumberField.dedekindZeta K z) hdiscrC hγζne hγζd]
  rw [logDeriv_mul (f := gammaFactor K) (g := NumberField.dedekindZeta K) s hγne hζne
      hγd hζd]
  have h1 : logDeriv (fun z : ℂ => z) s = 1/s := by
    rw [logDeriv_apply, deriv_id'']
  have h2 : logDeriv (fun z : ℂ => z - 1) s = 1/(s-1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  have h3 : Complex.log (((|NumberField.discr K| : ℝ)) : ℂ)
      = ((Real.log |NumberField.discr K| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hdiscr0.le]
  rw [h1, h2, h3]
  ring

end DedekindResidue
