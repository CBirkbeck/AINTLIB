import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

/-!
# LeanBridge issue #50: abc quality

This file uses mathlib's integer radical and defines the associated real-valued abc quality.
-/

open scoped BigOperators

namespace XYin.Experiments.Issue50

open UniqueFactorizationMonoid

private lemma isRelPrime_int_of_gcd_eq_one {a b : ℤ} (h : Int.gcd a b = 1) :
    IsRelPrime a b := by
  intro d hda hdb
  rw [Int.isUnit_iff_natAbs_eq]
  have hda' : ((d.natAbs : ℕ) : ℤ) ∣ a := (Int.natAbs_dvd).mpr hda
  have hdb' : ((d.natAbs : ℕ) : ℤ) ∣ b := (Int.natAbs_dvd).mpr hdb
  have hg : d.natAbs ∣ Int.gcd a b := Int.dvd_gcd hda' hdb'
  rw [h] at hg
  exact Nat.dvd_one.mp hg

private lemma radical_two : radical (2 : ℤ) = 2 := by
  rw [radical_of_prime (show Prime (2 : ℤ) by norm_num)]
  rfl

private lemma radical_three : radical (3 : ℤ) = 3 := by
  rw [radical_of_prime (show Prime (3 : ℤ) by norm_num)]
  rfl

private lemma radical_five : radical (5 : ℤ) = 5 := by
  rw [radical_of_prime (show Prime (5 : ℤ) by norm_num)]
  rfl

lemma radical_dvd_int (n : ℤ) : radical n ∣ n :=
  radical_dvd_self

/-- The height appearing in the numerator of the abc quality. -/
def abcHeight (a b c : ℤ) : ℕ :=
  max a.natAbs (max b.natAbs c.natAbs)

/-- The abc quality `log(max(|a|, |b|, |c|)) / log(rad(abc))`. -/
noncomputable def abcQuality (a b c : ℤ) : ℝ :=
  Real.log (abcHeight a b c : ℝ) / Real.log (((radical (a * b * c : ℤ) : ℤ) : ℝ))

/-- A pairwise coprime integer triple satisfying `a + b = c`. -/
structure CoprimeTriple (a b c : ℤ) : Prop where
  sum_eq : a + b = c
  coprime_ab : Nat.Coprime a.natAbs b.natAbs
  coprime_ac : Nat.Coprime a.natAbs c.natAbs
  coprime_bc : Nat.Coprime b.natAbs c.natAbs

lemma abcQuality_pos_of_one_lt_height_radical {a b c : ℤ}
    (hH : 1 < abcHeight a b c) (hR : 1 < radical (a * b * c : ℤ)) :
    0 < abcQuality a b c := by
  exact div_pos (Real.log_pos (by exact_mod_cast hH)) (Real.log_pos (by exact_mod_cast hR))

lemma one_lt_abcQuality_of_radical_lt_height {a b c : ℤ}
    (hR : 1 < radical (a * b * c : ℤ))
    (hRH : radical (a * b * c : ℤ) < (abcHeight a b c : ℤ)) :
    1 < abcQuality a b c := by
  rw [abcQuality]
  have hlogR : 0 < Real.log (((radical (a * b * c : ℤ) : ℤ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast hR)
  exact (one_lt_div hlogR).2 <|
    Real.log_lt_log (by exact_mod_cast Int.radical_pos (a * b * c : ℤ))
      (by exact_mod_cast hRH)

lemma one_eight_nine_coprimeTriple : CoprimeTriple 1 8 9 where
  sum_eq := by norm_num
  coprime_ab := by norm_num
  coprime_ac := by norm_num
  coprime_bc := by norm_num

lemma five_twentyseven_thirtytwo_coprimeTriple : CoprimeTriple 5 27 32 where
  sum_eq := by norm_num
  coprime_ab := by norm_num
  coprime_ac := by norm_num
  coprime_bc := by norm_num

lemma radical_one_eight_nine : radical (1 * 8 * 9 : ℤ) = 6 := by
  rw [show (1 * 8 * 9 : ℤ) = (2 : ℤ) ^ 3 * (3 : ℤ) ^ 2 by norm_num]
  rw [radical_mul (isRelPrime_int_of_gcd_eq_one (by norm_num))]
  rw [radical_pow, radical_pow]
  · rw [radical_two, radical_three]
    norm_num
  · norm_num
  · norm_num

lemma abcHeight_one_eight_nine : abcHeight 1 8 9 = 9 := by
  norm_num [abcHeight]

lemma one_lt_abcQuality_one_eight_nine : 1 < abcQuality 1 8 9 := by
  rw [abcQuality, abcHeight_one_eight_nine, radical_one_eight_nine]
  have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  exact (one_lt_div hlog6).2 <| by
    simpa using
      (Real.log_lt_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) < 9))

lemma radical_five_twentyseven_thirtytwo : radical (5 * 27 * 32 : ℤ) = 30 := by
  rw [show (5 * 27 * 32 : ℤ) = ((2 : ℤ) ^ 5 * (3 : ℤ) ^ 3) * 5 by norm_num]
  rw [radical_mul (isRelPrime_int_of_gcd_eq_one (by norm_num))]
  rw [radical_mul (isRelPrime_int_of_gcd_eq_one (by norm_num))]
  rw [radical_pow, radical_pow]
  · rw [radical_two, radical_three, radical_five]
    norm_num
  · norm_num
  · norm_num

lemma abcHeight_five_twentyseven_thirtytwo : abcHeight 5 27 32 = 32 := by
  norm_num [abcHeight]

lemma one_lt_abcQuality_five_twentyseven_thirtytwo : 1 < abcQuality 5 27 32 := by
  rw [abcQuality, abcHeight_five_twentyseven_thirtytwo,
    radical_five_twentyseven_thirtytwo]
  have hlog30 : 0 < Real.log (30 : ℝ) := Real.log_pos (by norm_num)
  exact (one_lt_div hlog30).2 <| by
    simpa using
      (Real.log_lt_log (by norm_num : (0 : ℝ) < 30) (by norm_num : (30 : ℝ) < 32))

end XYin.Experiments.Issue50
