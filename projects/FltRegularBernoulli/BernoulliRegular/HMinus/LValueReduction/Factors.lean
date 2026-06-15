module

public import BernoulliRegular.HMinus.ClassNumberFormula
public import BernoulliRegular.HMinus.KplusEulerProduct

/-!
# Class-number factors for `hMinus` reduction

This file packages the complex-valued class-number factors and their basic
cyclotomic simplifications used in the `hMinus` reduction chain.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

section Factors

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

def cyclotomicClassNumberFactor : ℂ :=
  (((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
    ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K) : ℝ) : ℂ)

lemma h_formula_cyclotomic_complex (hp_odd' : p ≠ 2) :
    ((h K : ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
        cyclotomicClassNumberFactor (p := p) (K := K) := by
  simpa [cyclotomicClassNumberFactor] using congrArg (fun x : ℝ => (x : ℂ))
    (h_formula_cyclotomic (p := p) (K := K) hp_odd')

def maximalRealSubfieldClassNumberFactor : ℂ :=
  (((((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
      Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
    (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
        Units.regulator (NumberField.maximalRealSubfield K)) : ℝ) : ℂ))

lemma hPlus_formula_complex :
    ((hPlus K : ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) *
        maximalRealSubfieldClassNumberFactor (K := K) := by
  simpa [maximalRealSubfieldClassNumberFactor] using congrArg (fun x : ℝ => (x : ℂ))
    (hPlus_formula (K := K))

theorem maximalRealSubfieldClassNumberFactor_eq_explicit (hp_odd' : p ≠ 2) :
    maximalRealSubfieldClassNumberFactor (K := K) =
      (((((2 : ℝ) * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2))) /
        (2 ^ ((p - 1) / 2 : ℕ) * Units.regulator (NumberField.maximalRealSubfield K)) : ℝ) :
        ℂ)) := by
  rw [maximalRealSubfieldClassNumberFactor]
  congr 1
  rw [maximalRealSubfield_torsionOrder_eq_two (K := K),
    maximalRealSubfield_archimedeanFactor_eq_pow (p := p) (K := K),
    abs_discr_maximalRealSubfield_eq_pow (p := p) (K := K) hp_odd']
  norm_num

set_option linter.unusedSectionVars false in
theorem hPlus_formula_of_Kplus_residue
    {KplusResidue : ℂ}
    (hresPlus :
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
        KplusResidue) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) * KplusResidue := by
  calc
    ((hPlus K : ℕ) : ℂ) =
        ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) *
          maximalRealSubfieldClassNumberFactor (K := K) := hPlus_formula_complex (K := K)
    _ = KplusResidue * maximalRealSubfieldClassNumberFactor (K := K) := by
          rw [hresPlus]
    _ = maximalRealSubfieldClassNumberFactor (K := K) * KplusResidue := by
          ring

omit [IsCMField K] in
lemma maximalRealSubfieldClassNumberFactor_ne_zero :
  maximalRealSubfieldClassNumberFactor (K := K) ≠ 0 := by
  let L := NumberField.maximalRealSubfield K
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B : ℝ := (Units.torsionOrder L : ℝ) * Real.sqrt |discr L|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  have hq_pos : 0 < B / A := div_pos hB_pos hA_pos
  change (((B / A : ℝ) : ℂ) ≠ 0)
  exact_mod_cast hq_pos.ne'

def cyclotomicRelativeLValueCoefficient : ℂ :=
  cyclotomicClassNumberFactor (p := p) (K := K) /
    maximalRealSubfieldClassNumberFactor (K := K)

theorem cyclotomicRelativeLValueCoefficient_eq_explicit
    (hp_odd' : p ≠ 2) :
    cyclotomicRelativeLValueCoefficient (p := p) (K := K) =
      ((((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
        ((2 * Real.pi) ^ ((p - 1) / 2) * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2))) : ℝ) : ℂ)) := by
  let L := NumberField.maximalRealSubfield K
  have hLreg_ne : Units.regulator L ≠ 0 :=
    (Units.regulator_pos L).ne'
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp.out.pos
  have hsqrt_pos : 0 < Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) :=
    Real.sqrt_pos.2 <| pow_pos hp_pos _
  have hsqrt_ne : Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) ≠ 0 := hsqrt_pos.ne'
  have hpow_pi_ne : ((2 * Real.pi) ^ ((p - 1) / 2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hpow_two_ne : (2 : ℝ) ^ ((p - 3) / 2 : ℕ) ≠ 0 := by
    positivity
  have hreg :
      Units.regulator K =
        (2 : ℝ) ^ ((p - 3) / 2 : ℕ) * Units.regulator L :=
    (div_eq_iff hLreg_ne).mp <| by
      simpa [L] using
        (regulator_div_regulator_maximalRealSubfield_eq_pow (p := p) (K := K) hp_odd' : _)
  have hexp : ((p - 1) / 2 : ℕ) = ((p - 3) / 2) + 1 := by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n, hn⟩
    have hp3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.out.two_le
      omega
    have hn_pos : 0 < n := by
      rw [hn] at hp3
      omega
    have hdiv1 : (p - 1) / 2 = n := by
      rw [hn, show 2 * n + 1 - 1 = 2 * n by omega,
        Nat.mul_div_right _ (by decide : 0 < 2)]
    have hdiv2 : (p - 3) / 2 = n - 1 := by
      rw [hn, show 2 * n + 1 - 3 = 2 * (n - 1) by omega,
        Nat.mul_div_right _ (by decide : 0 < 2)]
    rw [hdiv1, hdiv2]
    exact (Nat.sub_add_cancel (n := n) (m := 1) (Nat.succ_le_of_lt hn_pos)).symm
  have hpow_two :
      (2 : ℝ) ^ ((p - 1) / 2 : ℕ) =
        2 * (2 : ℝ) ^ ((p - 3) / 2 : ℕ) := by
    rw [hexp, pow_succ]
    ring
  rw [cyclotomicRelativeLValueCoefficient, cyclotomicClassNumberFactor,
    maximalRealSubfieldClassNumberFactor_eq_explicit (p := p) (K := K) hp_odd']
  suffices hreal :
      ((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K)) /
        (((2 : ℝ) * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2))) /
          (2 ^ ((p - 1) / 2 : ℕ) * Units.regulator L)) =
      ((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
        ((2 * Real.pi) ^ ((p - 1) / 2) * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2))) : ℝ) by
    simpa [Complex.ofReal_div] using congrArg (fun x : ℝ => (x : ℂ)) hreal
  rw [hreg, hpow_two]
  field_simp [hLreg_ne, hsqrt_ne, hpow_pi_ne, hpow_two_ne]

theorem cyclotomicRelativeLValueCoefficient_eq_final
    (hp_odd' : p ≠ 2) :
    cyclotomicRelativeLValueCoefficient (p := p) (K := K) =
      ((((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ ((p - 1) / 2))) /
        (2 * Real.pi) ^ ((p - 1) / 2) : ℝ) : ℂ)) := by
  let a : ℕ := (p - 1) / 2
  let b : ℕ := (p - 3) / 2
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp.out.pos
  have hpowA_nonneg : 0 ≤ (p : ℝ) ^ a := by
    positivity
  have hsqrtB_ne : Real.sqrt ((p : ℝ) ^ b) ≠ 0 :=
    Real.sqrt_ne_zero'.2 <| pow_pos hp_pos _
  have hpow_pi_ne : ((2 * Real.pi) ^ a : ℝ) ≠ 0 := by
    positivity
  have hsplit_exp : p - 2 = a + b := by
    dsimp [a, b]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n, hn⟩
    rw [hn]
    omega
  have hsqrt_split :
      Real.sqrt ((p : ℝ) ^ (p - 2)) =
        Real.sqrt ((p : ℝ) ^ a) * Real.sqrt ((p : ℝ) ^ b) := by
    rw [hsplit_exp, pow_add, Real.sqrt_mul hpowA_nonneg]
  suffices hreal :
      ((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ a * Real.sqrt ((p : ℝ) ^ b))) =
        ((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ a)) / (2 * Real.pi) ^ a : ℝ) by
    rw [cyclotomicRelativeLValueCoefficient_eq_explicit (p := p) (K := K) hp_odd']
    simpa [a, b, Complex.ofReal_div] using congrArg (fun x : ℝ => (x : ℂ)) hreal
  rw [hsqrt_split]
  field_simp [hsqrtB_ne, hpow_pi_ne]

/- The `K⁺` class-number scalar in the notation used by the repaired
cyclotomic `hMinus` reduction chain. -/
abbrev cyclotomicHPlusFactor : ℂ :=
  maximalRealSubfieldClassNumberFactor (K := K)

set_option linter.unusedSectionVars false in
lemma cyclotomicClassNumberFactor_eq_relative_coefficient_mul_hPlusFactor :
    cyclotomicClassNumberFactor (p := p) (K := K) =
      cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
        cyclotomicHPlusFactor (K := K) := by
  symm
  rw [cyclotomicRelativeLValueCoefficient, cyclotomicHPlusFactor, div_eq_mul_inv, mul_assoc,
    inv_mul_cancel₀ (maximalRealSubfieldClassNumberFactor_ne_zero (K := K)), mul_one]

end Factors

end BernoulliRegular
