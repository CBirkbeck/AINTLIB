module

public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.BernoulliGeneralized
public import BernoulliRegular.HMinus

/-!
# Bernoulli criterion from the relative class number formula

This file starts L4/T024. The main theorem here is Diekmann Theorem 42 in the
form needed later in the project: divisibility of the relative class number is
equivalent to divisibility of one of the relevant even Bernoulli numerators.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section HMinusCriterion

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

lemma exists_odd_index_iff_exists_k (hp_odd : p ≠ 2) (Q : ℕ → Prop) :
    (∃ j, j ∈ (Finset.range (p - 2)).filter (fun j => Odd j) ∧ Q (j + 1)) ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ Q (2 * k) := by
  constructor
  · rintro ⟨j, hj, hQ⟩
    have hj_lt : j < p - 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_odd : Odd j := (Finset.mem_filter.mp hj).2
    have hp_mod : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp_odd)
    let k := j / 2 + 1
    have hj_mod : j % 2 = 1 := Nat.odd_iff.mp hj_odd
    have hk_even : 2 * k = j + 1 := by
      dsimp [k]
      have htwo := Nat.two_mul_odd_div_two hj_mod
      omega
    refine ⟨k, by omega, by
      rw [hk_even]
      omega, ?_⟩
    simpa [hk_even] using hQ
  · rintro ⟨k, hk_one, hk_range, hQ⟩
    refine ⟨2 * k - 1, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · rw [Nat.odd_iff]
        omega
    · have hsucc : (2 * k - 1) + 1 = 2 * k := by omega
      simpa [hsucc] using hQ

/-- Diekmann Theorem 42: `p` divides the relative class number iff it divides
the numerator of one of the relevant even Bernoulli numbers. -/
theorem p_dvd_hMinus_iff_p_dvd_some_bernoulli (hp_odd' : p ≠ 2) :
    (p : ℕ) ∣ hMinus K ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  obtain ⟨z, hz⟩ := BernoulliRegular.hMinus_formula_bernoulli_mod_p
    (p := p) (K := K) hp_odd'
  let S := (Finset.range (p - 2)).filter (fun j => Odd j)
  have hfactor :
      ∀ j ∈ S,
        ∃ a : ℤ_[p],
          (a : ℚ_[p]) =
            (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) ∧
          (IsUnit a ↔ ¬ (p : ℤ) ∣ (bernoulli (j + 1)).num) := by
    intro j hj
    have hj_lt : j < p - 2 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    simpa [Nat.cast_add, Nat.cast_one] using
      (exists_padicInt_bernoulli_factor (p := p) (hp := hp) (n := j + 1) hp_odd'
        (by omega) (by omega)
        (BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one
          (p := p) (n := j + 1) (hp := hp) hp_odd' (by omega)))
  classical
  let a : ℕ → ℤ_[p] := fun j =>
    if hj : j ∈ S then Classical.choose (hfactor j hj) else 1
  let A : ℤ_[p] := ∏ j ∈ S, a j
  have ha_cast :
      ∀ j ∈ S,
        ((a j : ℤ_[p]) : ℚ_[p]) =
          (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p])) := by
    intro j hj
    simpa [a, hj, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Classical.choose_spec (hfactor j hj)).1
  have ha_unit :
      ∀ j ∈ S, IsUnit (a j) ↔ ¬ (p : ℤ) ∣ (bernoulli (j + 1)).num := by
    intro j hj
    simpa [a, hj] using (Classical.choose_spec (hfactor j hj)).2
  have hA_cast :
      ((A : ℤ_[p]) : ℚ_[p]) =
        Finset.prod S (fun j =>
          (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p]))) := by
    calc
      ((A : ℤ_[p]) : ℚ_[p]) = ∏ j ∈ S, ((a j : ℤ_[p]) : ℚ_[p]) := by
        dsimp [A]
        change (algebraMap ℤ_[p] ℚ_[p]) (∏ j ∈ S, a j) =
          ∏ j ∈ S, (algebraMap ℤ_[p] ℚ_[p]) (a j)
        rw [map_prod]
      _ = Finset.prod S (fun j =>
            (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p]))) :=
          Finset.prod_congr rfl ha_cast
  have hzA :
      (((hMinus K : ℕ) : ℚ_[p])) =
        ((A : ℤ_[p]) : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p]) := by
    calc
      (((hMinus K : ℕ) : ℚ_[p])) =
          Finset.prod S (fun j =>
            (-(1 / 2 : ℚ_[p])) * ((((bernoulli (j + 1) : ℚ) / (j + 1) : ℚ) : ℚ_[p]))) +
            (p : ℚ_[p]) * (z : ℚ_[p]) := hz
      _ = ((A : ℤ_[p]) : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p]) := by rw [hA_cast]
  have hpz_lt : ‖(p : ℚ_[p]) * (z : ℚ_[p])‖ < 1 := by
    have hp_lt : ‖(p : ℚ_[p])‖ < 1 := by
      simpa using (Padic.norm_natCast_lt_one_iff (p := p) (n := p)).2 (dvd_rfl)
    calc
      ‖(p : ℚ_[p]) * (z : ℚ_[p])‖ = ‖(z : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ := by
        rw [norm_mul, mul_comm]
      _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right z.2 (norm_nonneg _) hp_lt
  have hA_lt_iff :
      ‖A‖ < 1 ↔
        ∃ j, j ∈ S ∧ (p : ℤ) ∣ (bernoulli (j + 1)).num := by
    have hA_units : IsUnit A ↔ ∀ j ∈ S, IsUnit (a j) := IsUnit.prod_iff (s := S) (f := a)
    constructor
    · intro hA_lt
      have hA_nonunit : ¬ IsUnit A := (PadicInt.not_isUnit_iff (z := A)).2 hA_lt
      rw [hA_units] at hA_nonunit
      rcases not_forall.mp hA_nonunit with ⟨j, hj_bad_imp⟩
      obtain ⟨hjS, hj_bad⟩ := Classical.not_imp.mp hj_bad_imp
      exact ⟨j, hjS, Classical.not_not.mp ((not_congr (ha_unit j hjS)).mp hj_bad)⟩
    · rintro ⟨j, hjS, hj_bad⟩
      refine (PadicInt.not_isUnit_iff (z := A)).1 ?_
      rw [hA_units]
      exact fun hUnits => (ha_unit j hjS).mp (hUnits j hjS) hj_bad
  constructor
  · intro hhMinus
    have hhMinus_lt : ‖(((hMinus K : ℕ) : ℚ_[p]))‖ < 1 := by
      simpa using (Padic.norm_natCast_lt_one_iff (p := p) (n := hMinus K)).2 hhMinus
    have hA_lt : ‖((A : ℤ_[p]) : ℚ_[p])‖ < 1 := by
      by_cases hA_lt : ‖((A : ℤ_[p]) : ℚ_[p])‖ < 1
      · exact hA_lt
      have hA_eq : ‖((A : ℤ_[p]) : ℚ_[p])‖ = 1 := le_antisymm A.2 (le_of_not_gt hA_lt)
      have hpz_eq : ‖(p : ℚ_[p]) * (z : ℚ_[p])‖ = ‖((A : ℤ_[p]) : ℚ_[p])‖ :=
        Padic.norm_eq_of_norm_add_lt_right
          (z1 := (p : ℚ_[p]) * (z : ℚ_[p]))
          (z2 := ((A : ℤ_[p]) : ℚ_[p])) <| by
            simpa [hzA, add_comm, hA_eq] using hhMinus_lt
      have hpz_one : ‖(p : ℚ_[p]) * (z : ℚ_[p])‖ = 1 := hpz_eq.trans hA_eq
      exact absurd (hpz_one ▸ hpz_lt) (lt_irrefl _)
    exact (exists_odd_index_iff_exists_k (p := p) hp_odd'
      (Q := fun n => (p : ℤ) ∣ (bernoulli n).num)).1 ((hA_lt_iff).1 <| by
        simpa [PadicInt.padic_norm_e_of_padicInt] using hA_lt)
  · rintro hbad
    have hA_lt : ‖((A : ℤ_[p]) : ℚ_[p])‖ < 1 := by
      simpa [PadicInt.padic_norm_e_of_padicInt] using
        (hA_lt_iff).2 <| (exists_odd_index_iff_exists_k (p := p)
          hp_odd'
          (Q := fun n => (p : ℤ) ∣ (bernoulli n).num)).2 hbad
    have hhMinus_lt : ‖(((hMinus K : ℕ) : ℚ_[p]))‖ < 1 := by
      have hle :
          ‖(((hMinus K : ℕ) : ℚ_[p]))‖ ≤
            max ‖((A : ℤ_[p]) : ℚ_[p])‖ ‖(p : ℚ_[p]) * (z : ℚ_[p])‖ := by
        simpa [hzA] using
          (Padic.nonarchimedean (((A : ℤ_[p]) : ℚ_[p])) ((p : ℚ_[p]) * (z : ℚ_[p])))
      exact lt_of_le_of_lt hle (max_lt hA_lt hpz_lt)
    simpa using (Padic.norm_natCast_lt_one_iff (p := p) (n := hMinus K)).1 hhMinus_lt

end HMinusCriterion

end BernoulliRegular
