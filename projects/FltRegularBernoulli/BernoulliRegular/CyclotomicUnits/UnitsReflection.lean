import BernoulliRegular.CyclotomicUnits.ClassNumber
import BernoulliRegular.CyclotomicUnits.KummerLogDeterminant
import BernoulliRegular.CyclotomicUnits.LogDomain
import BernoulliRegular.CyclotomicUnits.SaturationIndex

/-!
# Cyclotomic-unit route to weak reflection

This file assembles the completed cyclotomic-unit tickets:

* CU-13 turns Bernoulli numerator nonvanishing into Kummer-log determinant
  nonvanishing.
* CU-14 turns that determinant into p-saturation of `CPlus`.
* CU-15 turns p-saturation into p-nondivisibility of the cyclotomic-unit
  index.
* CU-06 identifies the p-primary part of that index with `hPlus`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- CU-16: Bernoulli numerator nonvanishing in the classical range implies
that `p` does not divide the real cyclotomic-unit index. -/
theorem not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero
    (hp_odd : p ≠ 2)
    (hB : ∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 →
      ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num) :
    ¬ p ∣ (CPlus (p := p) (K := K)
      (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index := by
  have hp_three : 3 ≤ p := by
    have hp_two := (Fact.out : Nat.Prime p).two_le
    omega
  by_cases hp_eq_three : p = 3
  · have hindex :
        (CPlus (p := p) (K := K) hp_three).index = 1 := by
      rw [CPlus_eq_top_of_eq_three (p := p) (K := K) hp_three hp_eq_three]
      exact Subgroup.index_top
    rw [show
      (CPlus (p := p) (K := K)
        (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index =
          (CPlus (p := p) (K := K) hp_three).index by rfl]
    rw [hindex]
    intro hdiv
    exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp hdiv)
  · have hp_five : 5 ≤ p := by
      obtain ⟨k, hk⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two hp_odd
      have hp_two := (Fact.out : Nat.Prime p).two_le
      omega
    have hdet :
        (CyclotomicUnits.concreteKummerLogMatrix
          (p := p) (K := K) hp_three hp_five).det ≠ 0 :=
      (CyclotomicUnits.kummerLogMatrix_det_ne_zero_iff_bernoulli_nonzero
        (p := p) (K := K) hp_three hp_five).mpr hB
    have hsat :
        pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p :=
      CyclotomicUnits.cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero
        (p := p) (K := K) hp_three hp_five hdet
    have hnot := not_dvd_index_of_pSaturated (p := p) (K := K) hp_three hsat
    rwa [show
      (CPlus (p := p) (K := K)
        (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index =
          (CPlus (p := p) (K := K) hp_three).index by rfl]

/-- CU-17: contrapositive weak reflection from the cyclotomic-unit route. -/
theorem not_dvd_hPlus_of_not_dvd_hMinus_units
    (hp_odd : p ≠ 2) (hminus : ¬ (p : ℕ) ∣ hMinus K) :
    ¬ (p : ℕ) ∣ hPlus K := by
  have hp_three : 3 ≤ p := by
    have hp_two := (Fact.out : Nat.Prime p).two_le
    omega
  have hB :
      ∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 →
        ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num :=
    bernoulli_nonzero_of_not_dvd_hMinus
      (p := p) (K := K) hp_odd hminus
  have hindex :
      ¬ p ∣ (CPlus (p := p) (K := K) hp_three).index := by
    simpa using
      not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero
        (p := p) (K := K) hp_odd hB
  intro hplus
  have hnormalized :
      p ∣ (normalizedCPlus (p := p) (K := K) hp_odd hp_three).index :=
    (cyclotomicUnitIndex_primeConductor_pPrimary
      (p := p) (K := K) hp_odd).mpr hplus
  have hCPlus :
      p ∣ (CPlus (p := p) (K := K) hp_three).index :=
    (CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd
      (p := p) (K := K) hp_odd hp_three).mpr hnormalized
  exact hindex hCPlus

/-- CU-18: weak reflection by contrapositive from the cyclotomic-unit route. -/
theorem weakReflection_dvd_hMinus_of_dvd_hPlus_units
    (hp_odd : p ≠ 2) (hplus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ hMinus K := by
  by_contra hminus
  exact not_dvd_hPlus_of_not_dvd_hMinus_units
    (p := p) (K := K) hp_odd hminus hplus

/-- The total class-number divisibility criterion obtained from the
cyclotomic-unit weak-reflection route. -/
theorem dvd_h_iff_exists_dvd_bernoulli_units
    (hp_odd : p ≠ 2) :
    (p : ℕ) ∣ h K ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  rw [dvd_h_iff_dvd_hMinus_of_dvd_hPlus_imp hp_odd
      (weakReflection_dvd_hMinus_of_dvd_hPlus_units (p := p) (K := K) hp_odd),
    p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd]

end BernoulliRegular

end
