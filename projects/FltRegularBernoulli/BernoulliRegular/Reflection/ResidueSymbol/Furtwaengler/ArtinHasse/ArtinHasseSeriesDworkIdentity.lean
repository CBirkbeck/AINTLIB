module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DieudonneDwork
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Artin-Hasse exponential power series

This file defines the Artin-Hasse log and exponential power series over `ℚ`,
indexed by a prime `r`:

* `artinHasseLogSeries r : PowerSeries ℚ` is `L_r(T) = ∑_{i ≥ 0} T^{r^i} / r^i`.
* `artinHasseExpSeries r : PowerSeries ℚ` is `E_r(T) = exp(L_r(T))`.

The "is a power of `r`" predicate is decidable via `Nat.log`: for `r ≥ 2`,
`n = r^i` for some `i ≥ 0` iff `r ^ Nat.log r n = n ∧ n ≠ 0`. (For `n = 0`,
`r ^ Nat.log r 0 = r ^ 0 = 1 ≠ 0`, so the predicate fails as expected.)

These are the building blocks of the Dwork coefficient sequence used by the
`FullTeichDworkSetup` interface in REF-18 (the project's Φ/Kelly/Furtwängler
route). p-integrality of the Artin-Hasse exponential coefficients (the
substantive Dieudonné-Dwork content) is proved separately.

## References

* Alain M. Robert, *A Course in p-adic Analysis* (GTM 198, Springer 2000),
  §7.1 Definition 1, p. 187.
* Neal Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*
  (GTM 58, Springer 1984), §IV.2 Definition, p. 93.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

/-- The Artin-Hasse "log" series at prime `r`:
`L_r(T) := ∑_{i ≥ 0} T^{r^i} / r^i ∈ ℚ[[T]]`.

Coefficient `[T^n] L_r(T)` is `1 / r^(Nat.log r n)` if `n = r^(Nat.log r n)`
and `n ≠ 0` (i.e., if `n` is a positive power of `r`), else `0`.
The constant coefficient is `0` because `0` is excluded explicitly. -/
noncomputable def artinHasseLogSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    if r ^ Nat.log r n = n ∧ n ≠ 0 then
      (1 : ℚ) / (r : ℚ) ^ Nat.log r n
    else 0

@[simp] theorem artinHasseLogSeries_coeff (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseLogSeries r) =
      if r ^ Nat.log r n = n ∧ n ≠ 0 then
        (1 : ℚ) / (r : ℚ) ^ Nat.log r n
      else 0 := by
  unfold artinHasseLogSeries
  exact PowerSeries.coeff_mk n _

@[simp] theorem artinHasseLogSeries_constantCoeff (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.constantCoeff (R := ℚ)) (artinHasseLogSeries r) = 0 := by
  unfold artinHasseLogSeries
  rw [PowerSeries.constantCoeff_mk]
  simp

@[simp] theorem artinHasseLogSeries_coeff_one (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.coeff (R := ℚ) 1) (artinHasseLogSeries r) = 1 := by
  rw [artinHasseLogSeries_coeff, Nat.log_one_right r]
  simp

theorem artinHasseLogSeries_hasSubst (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries.HasSubst (artinHasseLogSeries r) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (artinHasseLogSeries_constantCoeff r)

/-- The Artin-Hasse exponential at prime `r`:
`E_r(T) := exp(L_r(T)) ∈ ℚ[[T]]`.

Defined via formal power-series substitution of `L_r(T)` into the universal
exponential series. The substitution is well-defined because
`L_r(T)` has zero constant coefficient (`artinHasseLogSeries_constantCoeff`). -/
noncomputable def artinHasseExpSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  PowerSeries.subst (artinHasseLogSeries r) (PowerSeries.exp ℚ)

@[simp] theorem artinHasseExpSeries_constantCoeff (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.constantCoeff (R := ℚ)) (artinHasseExpSeries r) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply (artinHasseExpSeries r) |>.symm]
  unfold artinHasseExpSeries
  rw [PowerSeries.coeff_subst' (artinHasseLogSeries_hasSubst r), finsum_eq_single _ 0]
  · -- main term at d = 0: (coeff 0 exp) • coeff 0 (L^0) = 1 • 1 = 1
    simp
  · -- terms at d ≠ 0 vanish: coeff 0 (L^d) = 0 since L has constant coeff 0
    intro d hd
    have hL_const : (PowerSeries.constantCoeff (R := ℚ)) (artinHasseLogSeries r) = 0 :=
      artinHasseLogSeries_constantCoeff r
    have h_pow_const : (PowerSeries.constantCoeff (R := ℚ))
        ((artinHasseLogSeries r) ^ d) = 0 := by
      rw [map_pow, hL_const, zero_pow hd]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h_pow_const]
    simp

private theorem artinHasseLogSeries_coeff_eq_X_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseLogSeries r) =
      (PowerSeries.coeff (R := ℚ) n) (PowerSeries.X : PowerSeries ℚ) := by
  have hr_prime : Nat.Prime r := Fact.out
  have hr_pos : 0 < r := hr_prime.pos
  rw [artinHasseLogSeries_coeff, PowerSeries.coeff_X]
  by_cases hn1 : n = 1
  · subst n
    simp [Nat.log_one_right]
  · have hnot :
        ¬ (r ^ Nat.log r n = n ∧ n ≠ 0) := by
      rintro ⟨hlog, _hn0⟩
      have hlog_zero : Nat.log r n = 0 := by
        cases hlogn : Nat.log r n with
        | zero => rfl
        | succ m =>
            have hr_le_pow : r ≤ r ^ (m + 1) := by
              rw [pow_succ']
              exact Nat.le_mul_of_pos_right r (pow_pos hr_pos m)
            have hr_le_n : r ≤ n := by
              rw [← hlog, hlogn]
              exact hr_le_pow
            exact False.elim ((not_lt_of_ge hr_le_n) hn)
      have hn_eq_one : n = 1 := by
        rw [← hlog, hlog_zero]
        simp
      exact hn1 hn_eq_one
    rw [if_neg hnot, if_neg hn1]

private theorem artinHasseLogSeries_trunc_eq_X
    (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries.trunc r (artinHasseLogSeries r) =
      PowerSeries.trunc r (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hn : n < r
  · rw [if_pos hn, if_pos hn, artinHasseLogSeries_coeff_eq_X_of_lt r hn]
  · rw [if_neg hn, if_neg hn]

private theorem artinHasseLogSeries_pow_coeff_eq_X_pow_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] (d : ℕ) {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) ((artinHasseLogSeries r) ^ d) =
      (PowerSeries.coeff (R := ℚ) n) ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
  have htrunc := artinHasseLogSeries_trunc_eq_X r
  have hpow :
      PowerSeries.trunc r ((artinHasseLogSeries r) ^ d) =
        PowerSeries.trunc r ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
    rw [← PowerSeries.trunc_trunc_pow (artinHasseLogSeries r) r d,
      ← PowerSeries.trunc_trunc_pow (PowerSeries.X : PowerSeries ℚ) r d,
      htrunc]
  have hcoeff := congrArg (fun P : Polynomial ℚ ↦ P.coeff n) hpow
  simpa [PowerSeries.coeff_trunc, hn] using hcoeff

private theorem artinHasseExpSeries_coeff_eq_exp_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries r) =
      (PowerSeries.coeff (R := ℚ) n) (PowerSeries.exp ℚ) := by
  unfold artinHasseExpSeries
  calc
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.subst (artinHasseLogSeries r) (PowerSeries.exp ℚ)) =
        (PowerSeries.coeff (R := ℚ) n)
          (PowerSeries.subst (PowerSeries.X : PowerSeries ℚ) (PowerSeries.exp ℚ)) := by
      rw [PowerSeries.coeff_subst' (artinHasseLogSeries_hasSubst r),
        PowerSeries.coeff_subst' (PowerSeries.HasSubst.X' (R := ℚ))]
      apply finsum_congr
      intro d
      rw [artinHasseLogSeries_pow_coeff_eq_X_pow_of_lt r d hn]
    _ = (PowerSeries.coeff (R := ℚ) n) (PowerSeries.exp ℚ) := by
      rw [PowerSeries.X_subst]

/-- Below degree `r`, the Artin-Hasse exponential has the same coefficients as
the ordinary exponential. -/
theorem artinHasseExpSeries_coeff_eq_inv_factorial_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries r) =
      (1 : ℚ) / (Nat.factorial n : ℚ) := by
  rw [artinHasseExpSeries_coeff_eq_exp_of_lt r hn]
  simp

/-- The series `E_r(T) - 1`, whose compositional inverse is the formal source
of the corrected Dwork parameter. -/
noncomputable def artinHasseExpMinusOneSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  artinHasseExpSeries r - 1

@[simp] theorem artinHasseExpMinusOneSeries_constantCoeff
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.constantCoeff (R := ℚ)) (artinHasseExpMinusOneSeries r) = 0 := by
  simp [artinHasseExpMinusOneSeries]

@[simp] theorem artinHasseExpMinusOneSeries_coeff_one
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpMinusOneSeries r) = 1 := by
  have hr : 1 < r := (Fact.out : Nat.Prime r).one_lt
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpSeries r) = 1 := by
    simpa using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt r hr
  simp [artinHasseExpMinusOneSeries, hcoeff]

/-- The compositional inverse of `E_r(T) - 1`. Evaluating this at
`ζ_r - 1` in a suitable complete local ring is the formal construction of the
corrected Dwork parameter. -/
noncomputable def artinHasseExpInverseSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  PowerSeries.substInv P

@[simp] theorem artinHasseExpInverseSeries_constantCoeff
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.constantCoeff (R := ℚ)) (artinHasseExpInverseSeries r) = 0 := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simp [artinHasseExpInverseSeries]

@[simp] theorem artinHasseExpInverseSeries_coeff_one
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpInverseSeries r) = 1 := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simp [artinHasseExpInverseSeries, P, hcoeff]

theorem artinHasseExpInverseSeries_coeff_two_of_two_lt
    (r : ℕ) [Fact (Nat.Prime r)] (hr : 2 < r) :
    (PowerSeries.coeff (R := ℚ) 2) (artinHasseExpInverseSeries r) = -(1 / 2 : ℚ) := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff_one : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  have hcoeff_two : (PowerSeries.coeff (R := ℚ) 2) P = (1 / 2 : ℚ) := by
    have hE := artinHasseExpSeries_coeff_eq_inv_factorial_of_lt r hr
    simpa [P, artinHasseExpMinusOneSeries] using hE
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff_one]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simp [artinHasseExpInverseSeries, PowerSeries.substInv, PowerSeries.substInvFun,
    P, hcoeff_one, hcoeff_two]

/-- Formal right-inverse identity for `artinHasseExpInverseSeries`. -/
theorem artinHasseExpMinusOneSeries_subst_inverse
    (r : ℕ) [Fact (Nat.Prime r)] :
    (artinHasseExpMinusOneSeries r).subst (artinHasseExpInverseSeries r) =
      (PowerSeries.X : PowerSeries ℚ) := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simpa [artinHasseExpInverseSeries, P] using
    PowerSeries.subst_substInv_right P (by simp [P])

/-- Equivalently, substituting the inverse series into `E_r(T)` gives
`1 + T`. -/
theorem artinHasseExpSeries_subst_inverse
    (r : ℕ) [Fact (Nat.Prime r)] :
    (artinHasseExpSeries r).subst (artinHasseExpInverseSeries r) =
      1 + (PowerSeries.X : PowerSeries ℚ) := by
  have hinv := artinHasseExpMinusOneSeries_subst_inverse r
  have hsubst : PowerSeries.HasSubst (artinHasseExpInverseSeries r) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (artinHasseExpInverseSeries_constantCoeff r)
  rw [artinHasseExpMinusOneSeries, PowerSeries.subst_sub hsubst, sub_eq_iff_eq_add] at hinv
  have hone :
      PowerSeries.subst (artinHasseExpInverseSeries r) (1 : PowerSeries ℚ) = 1 := by
    simpa using
      (PowerSeries.subst_C (a := artinHasseExpInverseSeries r) (r := (1 : ℚ)))
  rw [hone] at hinv
  simpa [add_comm] using hinv

/-- Coefficient form of `artinHasseExpSeries_subst_inverse`. -/
theorem artinHasseExpSeries_subst_inverse_coeff
    (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n)
        ((artinHasseExpSeries r).subst (artinHasseExpInverseSeries r)) =
      if n = 0 then 1 else if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : PowerSeries ℚ ↦ (PowerSeries.coeff (R := ℚ) n) F)
    (artinHasseExpSeries_subst_inverse r)
  by_cases hn0 : n = 0
  · simpa [PowerSeries.coeff_one, PowerSeries.coeff_X, hn0] using h
  · by_cases hn1 : n = 1
    · simpa [PowerSeries.coeff_one, PowerSeries.coeff_X, hn0, hn1] using h
    · simpa [PowerSeries.coeff_one, PowerSeries.coeff_X, hn0, hn1] using h

private theorem artinHasseLogSeries_coeff_eq_of_pow
    (r : ℕ) [Fact (Nat.Prime r)] (k : ℕ) :
    (PowerSeries.coeff (R := ℚ) (r ^ k)) (artinHasseLogSeries r) =
      (1 : ℚ) / (r : ℚ) ^ k := by
  have hr : 1 < r := (Fact.out : Nat.Prime r).one_lt
  rw [artinHasseLogSeries_coeff, Nat.log_pow hr]
  rw [if_pos ⟨rfl, pow_ne_zero k (Nat.Prime.ne_zero Fact.out)⟩]

private theorem artinHasseLogSeries_coeff_eq_zero_of_not_pow
    (r n : ℕ) [Fact (Nat.Prime r)] (hn : ¬ ∃ k : ℕ, n = r ^ k) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseLogSeries r) = 0 := by
  rw [artinHasseLogSeries_coeff]
  simp only [ite_eq_right_iff]
  rintro ⟨hlog, hn0⟩
  exact False.elim (hn ⟨Nat.log r n, hlog.symm⟩)

private theorem artinHasseLogSeries_smul_subst_X_pow_eq_smul_X
    (r : ℕ) [Fact (Nat.Prime r)] :
    (r : ℚ) • artinHasseLogSeries r -
        PowerSeries.subst (PowerSeries.X ^ r) (artinHasseLogSeries r) =
      (r : ℚ) • (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  have hr_prime : Nat.Prime r := Fact.out
  have hr_pos : 0 < r := hr_prime.pos
  have hr_ne_zero : r ≠ 0 := hr_prime.ne_zero
  have hr_one_lt : 1 < r := hr_prime.one_lt
  rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_smul,
    PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hr_ne_zero]
  by_cases hn0 : n = 0
  · simp [hn0]
  · by_cases hn1 : n = 1
    · have hr_not_dvd_one : ¬ r ∣ n := by
        rw [hn1]
        exact Nat.not_dvd_of_pos_of_lt zero_lt_one hr_one_lt
      have hr_not_dvd_one' : ¬ r ∣ 1 := by
        simpa [hn1] using hr_not_dvd_one
      rw [hn1, if_neg hr_not_dvd_one']
      simp
    · have hn_ne_one : n ≠ 1 := hn1
      by_cases hn_pow : ∃ k : ℕ, n = r ^ k
      · rcases hn_pow with ⟨k, rfl⟩
        cases k with
        | zero =>
            exact False.elim (hn_ne_one (by simp))
        | succ k =>
            have hdiv : r ∣ r ^ (k + 1) := by
              rw [pow_succ']
              exact dvd_mul_right r (r ^ k)
            have hquot : r ^ (k + 1) / r = r ^ k := by
              rw [pow_succ']
              exact Nat.mul_div_right (r ^ k) hr_pos
            have hXcoeff :
                (PowerSeries.coeff (R := ℚ) (r ^ (k + 1))) PowerSeries.X = 0 := by
              rw [PowerSeries.coeff_X,
                if_neg (Nat.ne_of_gt (Nat.one_lt_pow (Nat.succ_ne_zero k) hr_one_lt))]
            have hq : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr_ne_zero
            rw [if_pos hdiv, hquot, artinHasseLogSeries_coeff_eq_of_pow,
              artinHasseLogSeries_coeff_eq_of_pow, hXcoeff]
            simp only [Algebra.algebraMap_self, RingHom.id_apply]
            field_simp [pow_succ, hq]
            ring_nf
            calc
              -1 + (r : ℚ) * (r : ℚ) ^ k * (r : ℚ)⁻¹ * ((r : ℚ)⁻¹) ^ k
                  = -1 + ((r : ℚ) * (r : ℚ)⁻¹) *
                      (((r : ℚ) * (r : ℚ)⁻¹) ^ k) := by
                    rw [mul_pow]
                    ring
              _ = 0 := by
                    rw [mul_inv_cancel₀ hq]
                    simp
      · have hnotdiv_or_zero_raw :
            (if r ∣ n then
                ((PowerSeries.coeff (R := ℚ) (n / r)) (artinHasseLogSeries r) : ℚ)
              else 0) = 0 := by
          by_cases hdiv : r ∣ n
          · rw [if_pos hdiv]
            have hn_div_not_pow : ¬ ∃ k : ℕ, n / r = r ^ k := by
              rintro ⟨k, hk⟩
              apply hn_pow
              refine ⟨k + 1, ?_⟩
              calc
                n = (n / r) * r := (Nat.div_mul_cancel hdiv).symm
                _ = r ^ k * r := by rw [hk]
                _ = r ^ (k + 1) := by rw [pow_succ']; ring
            exact artinHasseLogSeries_coeff_eq_zero_of_not_pow r (n / r) hn_div_not_pow
          · simp [hdiv]
        have hnotdiv_or_zero :
            (if r ∣ n then
                (algebraMap ℚ ℚ)
                  ((PowerSeries.coeff (R := ℚ) (n / r)) (artinHasseLogSeries r))
              else 0) = 0 := by
          simpa using hnotdiv_or_zero_raw
        rw [hnotdiv_or_zero, artinHasseLogSeries_coeff_eq_zero_of_not_pow r n hn_pow]
        simp [PowerSeries.coeff_X, hn_ne_one]

private theorem artinHasseExpSeries_derivative
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.derivative ℚ) (artinHasseExpSeries r) =
      artinHasseExpSeries r * (PowerSeries.derivative ℚ) (artinHasseLogSeries r) := by
  unfold artinHasseExpSeries
  rw [PowerSeries.derivative_subst ℚ (artinHasseLogSeries_hasSubst r),
    PowerSeries.derivative_exp]

private theorem derivative_rescale_exp_rat (a : ℚ) :
    (PowerSeries.derivative ℚ) (PowerSeries.rescale a (PowerSeries.exp ℚ)) =
      a • PowerSeries.rescale a (PowerSeries.exp ℚ) := by
  rw [PowerSeries.rescale_eq_subst,
    PowerSeries.derivative_subst ℚ (PowerSeries.HasSubst.smul_X' a),
    PowerSeries.derivative_exp, ← PowerSeries.rescale_eq_subst]
  simp [PowerSeries.smul_eq_C_mul, smul_eq_mul]
  ring

private theorem eq_rescale_exp_of_derivative_eq_smul
    (a : ℚ) {F : PowerSeries ℚ}
    (hderiv : (PowerSeries.derivative ℚ) F = a • F)
    (hconst : PowerSeries.constantCoeff F = 1) :
    F = PowerSeries.rescale a (PowerSeries.exp ℚ) := by
  let H : PowerSeries ℚ := PowerSeries.rescale a (PowerSeries.exp ℚ)
  have hHderiv : (PowerSeries.derivative ℚ) H = a • H := by
    simpa [H] using derivative_rescale_exp_rat a
  ext n
  induction n with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hconst,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_exp]
      simp
  | succ n ih =>
      have eqF :
          (PowerSeries.coeff (R := ℚ) n) ((PowerSeries.derivative ℚ) F) =
            (PowerSeries.coeff (R := ℚ) n) (a • F) := by
        rw [hderiv]
      have eqH :
          (PowerSeries.coeff (R := ℚ) n) ((PowerSeries.derivative ℚ) H) =
            (PowerSeries.coeff (R := ℚ) n) (a • H) := by
        rw [hHderiv]
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul] at eqF
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul] at eqH
      norm_num at eqF eqH ⊢
      rw [ih] at eqF
      have hmul :
          (PowerSeries.coeff (R := ℚ) (n + 1)) F * ((n + 1 : ℕ) : ℚ) =
            (PowerSeries.coeff (R := ℚ) (n + 1)) H * ((n + 1 : ℕ) : ℚ) := by
        rw [show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by norm_num]
        rw [eqF, eqH]
      have hcoeff :
          (PowerSeries.coeff (R := ℚ) (n + 1)) F =
            (PowerSeries.coeff (R := ℚ) (n + 1)) H :=
        mul_right_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) hmul
      simpa [H] using hcoeff

/-- Formal Dieudonné-Dwork quotient identity for the Artin-Hasse exponential:
`E_r(T)^r / E_r(T^r) = exp(rT)` over `ℚ`. -/
theorem artinHasseExpSeries_dwork_quotient_eq_rescale_exp
    (r : ℕ) [Fact (Nat.Prime r)] :
    artinHasseExpSeries r ^ r *
        (PowerSeries.subst (PowerSeries.X ^ r) (artinHasseExpSeries r))⁻¹ =
      PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ) := by
  let L : PowerSeries ℚ := artinHasseLogSeries r
  let E : PowerSeries ℚ := artinHasseExpSeries r
  let M : PowerSeries ℚ := PowerSeries.subst (PowerSeries.X ^ r) L
  let S : PowerSeries ℚ := PowerSeries.subst (PowerSeries.X ^ r) E
  have hr_prime : Nat.Prime r := Fact.out
  have hr_ne_zero : r ≠ 0 := hr_prime.ne_zero
  have hXr : PowerSeries.HasSubst (PowerSeries.X ^ r : PowerSeries ℚ) :=
    PowerSeries.HasSubst.X_pow hr_ne_zero
  have hM0 : PowerSeries.constantCoeff M = 0 := by
    simp [M, L, artinHasseLogSeries_constantCoeff, hr_ne_zero]
  have hMsubst : PowerSeries.HasSubst M :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hM0
  have hEderiv :
      (PowerSeries.derivative ℚ) E = E * (PowerSeries.derivative ℚ) L := by
    simpa [E, L] using artinHasseExpSeries_derivative r
  have hS_as_exp : S = PowerSeries.subst M (PowerSeries.exp ℚ) := by
    simp [S, E, M, L, artinHasseExpSeries,
      PowerSeries.subst_comp_subst_apply (artinHasseLogSeries_hasSubst r) hXr]
  have hSderiv :
      (PowerSeries.derivative ℚ) S = S * (PowerSeries.derivative ℚ) M := by
    rw [hS_as_exp, PowerSeries.derivative_subst ℚ hMsubst, PowerSeries.derivative_exp]
  have hlog_deriv :
      (r : ℚ) • (PowerSeries.derivative ℚ) L - (PowerSeries.derivative ℚ) M =
        (r : ℚ) • (1 : PowerSeries ℚ) := by
    have h :=
      congrArg (fun F : PowerSeries ℚ ↦ (PowerSeries.derivative ℚ) F)
        (artinHasseLogSeries_smul_subst_X_pow_eq_smul_X r)
    simpa [L, M] using h
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    simp [S, E, artinHasseExpSeries_constantCoeff, hr_ne_zero]
  have hSinv_mul : S⁻¹ * S = 1 :=
    PowerSeries.inv_mul_cancel S (by simp [hS0])
  have hS_mul_inv : S * S⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel S (by simp [hS0])
  let G : PowerSeries ℚ := E ^ r * S⁻¹
  have hGderiv_pre :
      (PowerSeries.derivative ℚ) G =
        ((r : ℚ) • (PowerSeries.derivative ℚ) L -
          (PowerSeries.derivative ℚ) M) * G := by
    dsimp [G]
    change PowerSeries.derivativeFun (E ^ r * S⁻¹) =
      ((r : ℚ) • (PowerSeries.derivative ℚ) L -
        (PowerSeries.derivative ℚ) M) * (E ^ r * S⁻¹)
    rw [PowerSeries.derivativeFun_mul]
    change E ^ r * (PowerSeries.derivative ℚ) S⁻¹ +
        S⁻¹ * (PowerSeries.derivative ℚ) (E ^ r) =
      ((r : ℚ) • (PowerSeries.derivative ℚ) L -
        (PowerSeries.derivative ℚ) M) * (E ^ r * S⁻¹)
    rw [PowerSeries.derivative_inv', PowerSeries.derivative_pow, hEderiv, hSderiv]
    simp only [PowerSeries.smul_eq_C_mul]
    have hcancel_inv :
        S⁻¹ ^ 2 * (S * (PowerSeries.derivative ℚ) M) =
          S⁻¹ * (PowerSeries.derivative ℚ) M := by
      rw [pow_two]
      calc
        (S⁻¹ * S⁻¹) * (S * (PowerSeries.derivative ℚ) M)
            = (S⁻¹ * S) * (S⁻¹ * (PowerSeries.derivative ℚ) M) := by
                  ring
        _ = S⁻¹ * (PowerSeries.derivative ℚ) M := by
                  rw [hSinv_mul]
                  ring
    have hEpow : E ^ (r - 1) * E = E ^ r := by
      rw [← pow_succ, Nat.sub_add_cancel hr_prime.pos]
    have hcancel_inv_neg :
        -S⁻¹ ^ 2 * (S * (PowerSeries.derivative ℚ) M) =
          -(S⁻¹ * (PowerSeries.derivative ℚ) M) := by
      calc
        -S⁻¹ ^ 2 * (S * (PowerSeries.derivative ℚ) M)
            = -(S⁻¹ ^ 2 * (S * (PowerSeries.derivative ℚ) M)) := by
                ring
        _ = -(S⁻¹ * (PowerSeries.derivative ℚ) M) := by
                rw [hcancel_inv]
    rw [hcancel_inv_neg, ← hEpow]
    norm_num
    ring
  have hGderiv : (PowerSeries.derivative ℚ) G = (r : ℚ) • G := by
    rw [hGderiv_pre, hlog_deriv]
    simp [PowerSeries.smul_eq_C_mul]
  exact eq_rescale_exp_of_derivative_eq_smul (r : ℚ) hGderiv (by
    simp [artinHasseExpSeries_constantCoeff, hr_ne_zero])

/-- Multiplication form of the formal Dwork quotient identity, avoiding an
inverse on the target side:
`E_r(T)^r = exp(rT) * E_r(T^r)`. -/
theorem artinHasseExpSeries_pow_eq_rescale_exp_mul_subst_X_pow
    (r : ℕ) [Fact (Nat.Prime r)] :
    artinHasseExpSeries r ^ r =
      PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ) *
        PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r)
          (artinHasseExpSeries r) := by
  let E : PowerSeries ℚ := artinHasseExpSeries r
  let S : PowerSeries ℚ :=
    PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r) (artinHasseExpSeries r)
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    simp [S, artinHasseExpSeries_constantCoeff, (Fact.out : Nat.Prime r).ne_zero]
  have hcancel : S⁻¹ * S = 1 :=
    PowerSeries.inv_mul_cancel S (by simp [hS0])
  calc
    artinHasseExpSeries r ^ r = (artinHasseExpSeries r ^ r * S⁻¹) * S := by
      rw [mul_assoc, hcancel, mul_one]
    _ = PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ) * S := by
      rw [artinHasseExpSeries_dwork_quotient_eq_rescale_exp]
    _ = PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ) *
        PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r)
          (artinHasseExpSeries r) := rfl

private theorem rescale_exp_sub_one_coeff_rMultiple
    (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℚ, DieudonneDwork.IsRIntegralRat r q ∧
      (PowerSeries.coeff (R := ℚ) n)
          (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ) - 1) =
        (r : ℚ) * q := by
  let v : ℕ := padicValNat r n.factorial
  let m : ℕ := Nat.divMaxPow n.factorial r
  let q : ℚ := Rat.divInt ((r ^ (n - 1 - v) : ℕ) : ℤ) (m : ℤ)
  have hr_prime : Nat.Prime r := Fact.out
  have hr_ne_zero : r ≠ 0 := hr_prime.ne_zero
  have hfact_ne : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hfact : r ^ v * m = n.factorial := by
    simp [v, m, Nat.pow_padicValNat_mul_divMaxPow]
  have hm_ne : m ≠ 0 := by
    intro hm
    have : n.factorial = 0 := by simpa [hm] using hfact.symm
    exact hfact_ne this
  refine ⟨q, ?_, ?_⟩
  · unfold DieudonneDwork.IsRIntegralRat
    have hm_not_dvd : ¬ r ∣ m := by
      simpa [m] using Nat.not_dvd_divMaxPow hr_prime.one_lt hfact_ne
    have hm_coprime : m.Coprime r := by
      rw [Nat.coprime_comm]
      exact hr_prime.coprime_iff_not_dvd.mpr hm_not_dvd
    refine Nat.Coprime.coprime_dvd_left ?_ hm_coprime
    have hden_dvd_int :
        (((Rat.divInt ((r ^ (n - 1 - v) : ℕ) : ℤ) (m : ℤ)).den : ℕ) : ℤ) ∣
          (m : ℤ) :=
      Rat.den_dvd ((r ^ (n - 1 - v) : ℕ) : ℤ) (m : ℤ)
    exact Int.natCast_dvd_natCast.mp hden_dvd_int
  · have hvlt : v < n := by
      simpa [v] using padicValNat_factorial_lt_of_ne_zero r (Nat.ne_of_gt hn)
    have hvle : v ≤ n - 1 := Nat.le_sub_one_of_lt hvlt
    have hnv : n - 1 = (n - 1 - v) + v :=
      (Nat.sub_add_cancel hvle).symm
    have hn_decomp : n = (n - 1 - v) + v + 1 := by
      calc
        n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
        _ = ((n - 1 - v) + v) + 1 := by
          nth_rewrite 1 [hnv]
          rfl
        _ = (n - 1 - v) + v + 1 := by rfl
    have hfact_q : ((n.factorial : ℕ) : ℚ) = (r : ℚ) ^ v * (m : ℚ) := by
      rw [← hfact]
      norm_num [Nat.cast_mul, Nat.cast_pow]
    have hpow_decomp :
        (r : ℚ) ^ n =
          (r : ℚ) * ((r : ℚ) ^ (n - 1 - v) * (r : ℚ) ^ v) := by
      calc
        (r : ℚ) ^ n = (r : ℚ) ^ (((n - 1 - v) + v) + 1) := by
          nth_rewrite 1 [hn_decomp]
          rfl
        _ = ((r : ℚ) ^ (n - 1 - v) * (r : ℚ) ^ v) * (r : ℚ) := by
          rw [pow_succ, pow_add]
        _ = (r : ℚ) * ((r : ℚ) ^ (n - 1 - v) * (r : ℚ) ^ v) := by
          ring
    rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    have hcoeff_one : (PowerSeries.coeff (R := ℚ) n) (1 : PowerSeries ℚ) = 0 := by
      simp [PowerSeries.coeff_one, Nat.ne_of_gt hn]
    rw [hcoeff_one]
    simp only [q]
    rw [Rat.divInt_eq_div]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Int.cast_natCast, Nat.cast_pow]
    rw [hpow_decomp, hfact_q]
    field_simp [Nat.cast_ne_zero.mpr hr_ne_zero, Nat.cast_ne_zero.mpr hm_ne]
    ring_nf
    norm_num [Nat.cast_pow]

theorem artinHasseExpSeries_coeff_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    DieudonneDwork.IsRIntegralRat r
      ((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries r)) := by
  have hps : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) := by
    refine (DieudonneDwork.IsRIntegralPS.dieudonneDwork_mpr
      (r := r) (F := artinHasseExpSeries r)
      (artinHasseExpSeries_constantCoeff r)) ?_
    intro n hn
    have hquot := artinHasseExpSeries_dwork_quotient_eq_rescale_exp r
    simpa [hquot] using rescale_exp_sub_one_coeff_rMultiple r n hn
  exact hps n

/-- The ordinary exponential `exp(rT)` has `r`-integral coefficients. -/
theorem rescale_exp_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] :
    DieudonneDwork.IsRIntegralPS r
      (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) := by
  intro n
  by_cases hn0 : n = 0
  · simp [hn0, DieudonneDwork.IsRIntegralRat.one]
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    rcases rescale_exp_sub_one_coeff_rMultiple r n hn with ⟨q, hq, hcoeff⟩
    have hcoeff' :
        (PowerSeries.coeff (R := ℚ) n)
            (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) =
          (r : ℚ) * q := by
      have hcoeff_one :
          (PowerSeries.coeff (R := ℚ) n) (1 : PowerSeries ℚ) = 0 := by
        simp [PowerSeries.coeff_one, hn0]
      rw [map_sub, hcoeff_one] at hcoeff
      simpa [sub_zero] using hcoeff
    rw [hcoeff']
    exact (DieudonneDwork.IsRIntegralRat.natCast r r).mul hq

private theorem rescale_exp_coeff_mul_eq_choose_mul_coeff
    (r : ℕ) [Fact (Nat.Prime r)] (i j : ℕ) :
    (PowerSeries.coeff (R := ℚ) i)
        (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) *
      (PowerSeries.coeff (R := ℚ) j)
        (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) =
      ((Nat.choose (i + j) i : ℕ) : ℚ) *
        (PowerSeries.coeff (R := ℚ) (i + j))
          (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    PowerSeries.coeff_exp]
  have hr : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime r).ne_zero
  have hi : ((i.factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : ((j.factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hij : (((i + j).factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (i + j))
  have hfact :
      ((Nat.choose (i + j) i : ℕ) : ℚ) *
          ((i.factorial : ℕ) : ℚ) * ((j.factorial : ℕ) : ℚ) =
        (((i + j).factorial : ℕ) : ℚ) := by
    have hfact_nat :
        Nat.choose (i + j) i * i.factorial * j.factorial = (i + j).factorial := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Nat.add_choose_mul_factorial_mul_factorial j i
    exact_mod_cast hfact_nat
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  field_simp [hr, hi, hj, hij]
  rw [pow_add, ← hfact]
  ring

theorem rescale_exp_mapTo_coeff_mul_eq_choose_mul_coeff
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (i j : ℕ) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (PowerSeries.coeff (R := A) i) Rps *
        (PowerSeries.coeff (R := A) j) Rps =
      ((Nat.choose (i + j) i : ℕ) : A) *
        (PowerSeries.coeff (R := A) (i + j)) Rps := by
  dsimp only
  let hRes : DieudonneDwork.IsRIntegralPS r
      (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) :=
    rescale_exp_isRIntegral r
  let qi : DieudonneDwork.rIntegralRatSubring r :=
    ⟨(PowerSeries.coeff (R := ℚ) i)
        (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)), hRes i⟩
  let qj : DieudonneDwork.rIntegralRatSubring r :=
    ⟨(PowerSeries.coeff (R := ℚ) j)
        (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)), hRes j⟩
  let qij : DieudonneDwork.rIntegralRatSubring r :=
    ⟨(PowerSeries.coeff (R := ℚ) (i + j))
        (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)), hRes (i + j)⟩
  have hq : qi * qj = ((Nat.choose (i + j) i : ℕ) : DieudonneDwork.rIntegralRatSubring r) *
      qij := by
    apply Subtype.ext
    change
      (PowerSeries.coeff (R := ℚ) i)
          (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) *
        (PowerSeries.coeff (R := ℚ) j)
          (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) =
        ((Nat.choose (i + j) i : ℕ) : ℚ) *
          (PowerSeries.coeff (R := ℚ) (i + j))
            (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ))
    exact rescale_exp_coeff_mul_eq_choose_mul_coeff r i j
  calc
    (PowerSeries.coeff (R := A) i) (hRes.mapTo φ) *
        (PowerSeries.coeff (R := A) j) (hRes.mapTo φ)
        = φ qi * φ qj := by simp [qi, qj]
    _ = φ (qi * qj) := by rw [map_mul]
    _ = φ (((Nat.choose (i + j) i : ℕ) : DieudonneDwork.rIntegralRatSubring r) *
          qij) := by rw [hq]
    _ = ((Nat.choose (i + j) i : ℕ) : A) *
        (PowerSeries.coeff (R := A) (i + j)) (hRes.mapTo φ) := by
          simp [qij]

theorem rescale_exp_mapTo_mul
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (a b : A) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    PowerSeries.rescale a Rps * PowerSeries.rescale b Rps =
      PowerSeries.rescale (a + b) Rps := by
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, add_pow]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcoeff :
      (PowerSeries.coeff (R := A) i) Rps *
          (PowerSeries.coeff (R := A) (n - i)) Rps =
        ((Nat.choose n i : ℕ) : A) * (PowerSeries.coeff (R := A) n) Rps := by
    simpa [Rps, Nat.add_sub_of_le hin] using
      rescale_exp_mapTo_coeff_mul_eq_choose_mul_coeff r φ i (n - i)
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
  change
    a ^ i * (PowerSeries.coeff (R := A) i) Rps *
        (b ^ (n - i) * (PowerSeries.coeff (R := A) (n - i)) Rps) =
      a ^ i * b ^ (n - i) * ((Nat.choose n i : ℕ) : A) *
        (PowerSeries.coeff (R := A) n) Rps
  calc
    a ^ i * (PowerSeries.coeff (R := A) i) Rps *
        (b ^ (n - i) * (PowerSeries.coeff (R := A) (n - i)) Rps)
        = a ^ i * b ^ (n - i) *
            ((PowerSeries.coeff (R := A) i) Rps *
              (PowerSeries.coeff (R := A) (n - i)) Rps) := by
          ring
    _ = a ^ i * b ^ (n - i) *
        (((Nat.choose n i : ℕ) : A) * (PowerSeries.coeff (R := A) n) Rps) := by
          rw [hcoeff]
    _ = a ^ i * b ^ (n - i) * ((Nat.choose n i : ℕ) : A) *
        (PowerSeries.coeff (R := A) n) Rps := by
          ring

/-- The Artin-Hasse Dwork quotient has `r`-integral coefficients. -/
theorem artinHasseExpSeries_dwork_quotient_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] :
    DieudonneDwork.IsRIntegralPS r
      (artinHasseExpSeries r ^ r *
        (PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r)
          (artinHasseExpSeries r))⁻¹) := by
  let hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral r n
  let hSub : DieudonneDwork.IsRIntegralPS r
      (PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r) (artinHasseExpSeries r)) :=
    hE.subst_X_pow (Fact.out : Nat.Prime r).ne_zero
  have hSub0 :
      PowerSeries.constantCoeff
          (PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r)
            (artinHasseExpSeries r)) = 1 := by
    simp [artinHasseExpSeries_constantCoeff, (Fact.out : Nat.Prime r).ne_zero]
  exact (hE.pow r).mul (hSub.inv_of_constantCoeff_one hSub0)

/-- The Dwork quotient identity transported through any coefficient map out of
the localized Artin-Hasse coefficient ring. -/
theorem artinHasseExpSeries_dwork_quotient_mapTo_eq_rescale_exp
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommSemiring A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) :
    (artinHasseExpSeries_dwork_quotient_isRIntegral r).mapTo φ =
      (rescale_exp_isRIntegral r).mapTo φ :=
  DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq φ _ _
    (artinHasseExpSeries_dwork_quotient_eq_rescale_exp r)

end Furtwaengler

end BernoulliRegular

end
