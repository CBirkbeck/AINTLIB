module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseExp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogFormal

/-!
# Formal Artin-Hasse logarithm identity

This file proves the formal identity
`logOf (artinHasseExpSeries ell) = artinHasseLogSeries ell` over `ℚ`, together
with coefficient forms used by the later finite denominator transport.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace FiniteArtinHasseFormal

open PowerSeries

theorem coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero
    {A : Type*} [CommRing A] (F : PowerSeries A)
    (hF0 : PowerSeries.constantCoeff F = 0) {n d : ℕ} (hdn : d < n) :
    PowerSeries.coeff d (F ^ n) = 0 := by
  have hle : (n : ℕ∞) ≤ (F ^ n).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hF0
  exact PowerSeries.coeff_of_lt_order d ((ENat.coe_lt_coe.mpr hdn).trans_le hle)

theorem coeff_subst_log_eq_sum_Icc
    {A : Type*} [CommRing A] [Algebra ℚ A] (F : PowerSeries A)
    (hF0 : PowerSeries.constantCoeff F = 0) (d : ℕ) :
    PowerSeries.coeff d (PowerSeries.subst F (PowerSeries.log A)) =
      ∑ n ∈ Finset.Icc 1 d,
        algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / n) *
          PowerSeries.coeff d (F ^ n) := by
  classical
  have hsubst : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hF0
  rw [PowerSeries.coeff_subst' hsubst]
  rw [finsum_eq_sum_of_support_subset]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    have hn0 : n ≠ 0 := by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact Nat.ne_zero_of_lt hn1
    simp [PowerSeries.coeff_log, hn0, smul_eq_mul]
  · rw [Function.support_subset_iff]
    intro n hnmem
    by_contra hnI
    by_cases hn0 : n = 0
    · subst n
      simp at hnmem
    · have hdn : d < n := by
        by_contra hdn
        have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
        have hnd : n ≤ d := by omega
        exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
      have hcoeff := coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero F hF0 hdn
      simp [hcoeff] at hnmem

/-- The formal logarithm of the Artin-Hasse exponential is its defining
Artin-Hasse logarithm series. -/
theorem logOf_artinHasseExpSeries (ell : ℕ) [Fact (Nat.Prime ell)] :
    PowerSeries.logOf (artinHasseExpSeries ell) = artinHasseLogSeries ell := by
  let E : PowerSeries ℚ := artinHasseExpSeries ell
  let L : PowerSeries ℚ := artinHasseLogSeries ell
  let a : PowerSeries ℚ := E - 1
  have hE0 : PowerSeries.constantCoeff E = 1 := by
    simp [E]
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    simp [L]
  have ha0 : PowerSeries.constantCoeff a = 0 := by
    simp [a, hE0]
  have ha : PowerSeries.HasSubst a :=
    PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  have hLsubst : PowerSeries.HasSubst L := by
    simpa [L] using artinHasseLogSeries_hasSubst ell
  have hE_deriv : d⁄dX ℚ E = E * d⁄dX ℚ L := by
    change d⁄dX ℚ (PowerSeries.subst L (PowerSeries.exp ℚ)) =
      PowerSeries.subst L (PowerSeries.exp ℚ) * d⁄dX ℚ L
    rw [PowerSeries.derivative_subst ℚ hLsubst, PowerSeries.derivative_exp]
  have hgeom :
      PowerSeries.subst a (d⁄dX ℚ (PowerSeries.log ℚ)) * E = 1 := by
    have h := FiniteLogFormal.subst_deriv_log_mul_one_add (A := ℚ) ha
    simpa [a] using h
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℚ ha]
    have hda : d⁄dX ℚ a = d⁄dX ℚ E := by
      simp [a]
    rw [hda, hE_deriv]
    calc
      PowerSeries.subst a (d⁄dX ℚ (PowerSeries.log ℚ)) * (E * d⁄dX ℚ L)
          = (PowerSeries.subst a (d⁄dX ℚ (PowerSeries.log ℚ)) * E) *
              d⁄dX ℚ L := by
            ring
      _ = d⁄dX ℚ L := by
            rw [hgeom, one_mul]
  · rw [PowerSeries.constantCoeff_logOf hE0, hL0]

/-- Coefficient form of `logOf_artinHasseExpSeries`. -/
theorem coeff_logOf_artinHasseExpSeries (ell n : ℕ) [Fact (Nat.Prime ell)] :
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf (artinHasseExpSeries ell)) =
      (PowerSeries.coeff (R := ℚ) n) (artinHasseLogSeries ell) := by
  rw [logOf_artinHasseExpSeries]

theorem coeff_logOf_artinHasseExpSeries_eq_sum_Icc
    (ell d : ℕ) [Fact (Nat.Prime ell)] :
    (PowerSeries.coeff (R := ℚ) d)
        (PowerSeries.logOf (artinHasseExpSeries ell)) =
      ∑ n ∈ Finset.Icc 1 d,
        (((-1 : ℚ) ^ (n + 1)) / n) *
          PowerSeries.coeff d ((artinHasseExpSeries ell - 1) ^ n) := by
  let E : PowerSeries ℚ := artinHasseExpSeries ell
  let A : PowerSeries ℚ := E - 1
  have hE0 : PowerSeries.constantCoeff E = 1 := by
    simp [E]
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    simp [A, hE0]
  rw [PowerSeries.logOf_eq]
  simpa [A] using coeff_subst_log_eq_sum_Icc (A := ℚ) A hA0 d

/-- Explicit coefficient formula for `logOf (artinHasseExpSeries ell)`. -/
@[simp] theorem coeff_logOf_artinHasseExpSeries_eq
    (ell n : ℕ) [Fact (Nat.Prime ell)] :
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf (artinHasseExpSeries ell)) =
      if ell ^ Nat.log ell n = n ∧ n ≠ 0 then
        (1 : ℚ) / (ell : ℚ) ^ Nat.log ell n
      else 0 := by
  rw [logOf_artinHasseExpSeries, artinHasseLogSeries_coeff]

/-- Coefficient of `logOf (E_ell)` at an `ell`-power. -/
theorem coeff_logOf_artinHasseExpSeries_eq_of_pow
    (ell k : ℕ) [Fact (Nat.Prime ell)] :
    (PowerSeries.coeff (R := ℚ) (ell ^ k))
        (PowerSeries.logOf (artinHasseExpSeries ell)) =
      (1 : ℚ) / (ell : ℚ) ^ k := by
  have hell : 1 < ell := (Fact.out : Nat.Prime ell).one_lt
  rw [coeff_logOf_artinHasseExpSeries_eq, Nat.log_pow hell]
  rw [if_pos ⟨rfl, pow_ne_zero k (Nat.Prime.ne_zero Fact.out)⟩]

/-- Coefficient of `logOf (E_ell)` away from `ell`-powers. -/
theorem coeff_logOf_artinHasseExpSeries_eq_zero_of_not_pow
    (ell n : ℕ) [Fact (Nat.Prime ell)] (hn : ¬ ∃ k : ℕ, n = ell ^ k) :
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf (artinHasseExpSeries ell)) = 0 := by
  rw [coeff_logOf_artinHasseExpSeries_eq]
  simp only [ite_eq_right_iff]
  rintro ⟨hlog, _hn0⟩
  exact False.elim (hn ⟨Nat.log ell n, hlog.symm⟩)

/-- The factorial-cleared formal logarithm coefficient contributed by the
`n`-th power of `E_ell - 1` in total degree `d`, as an element of the
localized coefficient ring `ℤ_(ell)`. -/
noncomputable def factorialWeightedLogCoeff
    (ell d n : ℕ) [Fact (Nat.Prime ell)] :
    DieudonneDwork.rIntegralRatSubring ell :=
  let hE : DieudonneDwork.IsRIntegralPS ell (artinHasseExpSeries ell) :=
    fun m => artinHasseExpSeries_coeff_isRIntegral ell m
  let hA : DieudonneDwork.IsRIntegralPS ell (artinHasseExpSeries ell - 1) :=
    hE.sub (DieudonneDwork.IsRIntegralPS.one ell)
  ((d.factorial / n : ℕ) : DieudonneDwork.rIntegralRatSubring ell) *
    ((-1 : DieudonneDwork.rIntegralRatSubring ell) ^ (n + 1)) *
      (⟨(PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ell - 1) ^ n),
        hA.pow n d⟩ : DieudonneDwork.rIntegralRatSubring ell)

theorem coe_factorialWeightedLogCoeff
    (ell d n : ℕ) [Fact (Nat.Prime ell)] (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    ((factorialWeightedLogCoeff ell d n : DieudonneDwork.rIntegralRatSubring ell) :
        ℚ) =
      (d.factorial : ℚ) *
        (((-1 : ℚ) ^ (n + 1) / n) *
          (PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ell - 1) ^ n)) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
  have hdiv : n ∣ d.factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero hn0) hnd
  have hcast_div :
      ((d.factorial / n : ℕ) : ℚ) = (d.factorial : ℚ) / (n : ℚ) :=
    Nat.cast_div hdiv (by exact_mod_cast hn0)
  simp only [factorialWeightedLogCoeff, Subring.coe_mul, Subring.coe_natCast,
    Subring.coe_pow, Subring.coe_neg, Subring.coe_one]
  rw [hcast_div]
  field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn0]

theorem coe_sum_factorialWeightedLogCoeff
    (ell d : ℕ) [Fact (Nat.Prime ell)] :
    (((∑ n ∈ Finset.Icc 1 d, factorialWeightedLogCoeff ell d n) :
        DieudonneDwork.rIntegralRatSubring ell) : ℚ) =
      (d.factorial : ℚ) *
        (PowerSeries.coeff (R := ℚ) d)
          (PowerSeries.logOf (artinHasseExpSeries ell)) := by
  classical
  rw [coeff_logOf_artinHasseExpSeries_eq_sum_Icc]
  rw [Finset.mul_sum]
  change (DieudonneDwork.rIntegralRatSubring ell).subtype
      (∑ n ∈ Finset.Icc 1 d, factorialWeightedLogCoeff ell d n) =
    ∑ n ∈ Finset.Icc 1 d,
      (d.factorial : ℚ) *
        (((-1 : ℚ) ^ (n + 1) / n) *
          (PowerSeries.coeff (R := ℚ) d) ((artinHasseExpSeries ell - 1) ^ n))
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
  exact coe_factorialWeightedLogCoeff ell d n hn1 hnd

theorem sum_factorialWeightedLogCoeff_eq_zero_of_not_pow
    (ell d : ℕ) [Fact (Nat.Prime ell)]
    (hd : ¬ ∃ r : ℕ, d = ell ^ r) :
    (∑ n ∈ Finset.Icc 1 d, factorialWeightedLogCoeff ell d n :
      DieudonneDwork.rIntegralRatSubring ell) = 0 := by
  ext
  rw [coe_sum_factorialWeightedLogCoeff]
  rw [coeff_logOf_artinHasseExpSeries_eq_zero_of_not_pow ell d hd]
  simp

theorem sum_factorialWeightedLogCoeff_eq_factorial_div_pow
    (ell r : ℕ) [Fact (Nat.Prime ell)] :
    (∑ n ∈ Finset.Icc 1 (ell ^ r), factorialWeightedLogCoeff ell (ell ^ r) n :
      DieudonneDwork.rIntegralRatSubring ell) =
      (((ell ^ r).factorial / (ell ^ r) : ℕ) :
        DieudonneDwork.rIntegralRatSubring ell) := by
  ext
  have hell0 : ell ≠ 0 := (Fact.out : Nat.Prime ell).ne_zero
  have hd0 : ell ^ r ≠ 0 := pow_ne_zero r hell0
  have hdiv : ell ^ r ∣ (ell ^ r).factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero hd0) le_rfl
  have hcast_div :
      (((ell ^ r).factorial / (ell ^ r) : ℕ) : ℚ) =
        ((ell ^ r).factorial : ℚ) / ((ell ^ r : ℕ) : ℚ) :=
    Nat.cast_div hdiv (by exact_mod_cast hd0)
  rw [coe_sum_factorialWeightedLogCoeff]
  rw [coeff_logOf_artinHasseExpSeries_eq_of_pow]
  change ((ell ^ r).factorial : ℚ) * (1 / (ell : ℚ) ^ r) =
    (((ell ^ r).factorial / (ell ^ r) : ℕ) : ℚ)
  rw [hcast_div]
  have hell_rat_ne : (ell : ℚ) ^ r ≠ 0 :=
    pow_ne_zero r (by exact_mod_cast hell0)
  have hpow_cast : (((ell ^ r : ℕ) : ℚ)) = (ell : ℚ) ^ r := by
    norm_num
  rw [hpow_cast]
  field_simp [hell_rat_ne]

end FiniteArtinHasseFormal

end Furtwaengler

end BernoulliRegular

end
