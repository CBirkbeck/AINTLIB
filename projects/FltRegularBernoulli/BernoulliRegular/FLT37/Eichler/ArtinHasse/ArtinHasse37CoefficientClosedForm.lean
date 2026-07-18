module

public import BernoulliRegular.CyclotomicUnits.KummerLogNormalization.NormalizedUnitLog

/-!
# The degree-`68` Artin-Hasse exponential structure: `E₃₇ ≡ exp(T)·(1 + T³⁷/37) mod T⁷⁴`,
# the closed-form coefficients `[Tᵐ] E₃₇ = 1/m! + (1/37)·[m≥37]/(m−37)!`, and the explicit
# degree-`68` log-coefficient

This file develops the **concrete degree-`68`** content of the Artin-Hasse normalized log
coefficient `formalSum68 = 68!·[T⁶⁸] log((E₃₇(T)−1)/T)`
(`CaseIICor823Level71Factorial37Extraction.formalSum68`), in the actual `PowerSeries ℚ` objects,
to ground the value residual `FormalSum68RatValue`.  It imports only; it does **not** modify any
existing file.  No `sorry`, no `axiom`.

## The structural identity (proven here)

The Artin-Hasse exponential is `E₃₇(T) = artinHasseExpSeries 37 = subst(L₃₇, exp)` with the
Artin-Hasse log `L₃₇ = ∑ᵢ T^(37ⁱ)/37ⁱ`.  Its formal derivative satisfies the **Artin-Hasse ODE**
`E₃₇′ = E₃₇·L₃₇′` (chain rule + `exp′ = exp`).  Since `L₃₇ = T + T³⁷/37 + T^{37²}/37² + ⋯`, its
derivative is `L₃₇′ = 1 + T³⁶ + (higher, degree ≥ 37²−1 = 1368)`, so for `n + 1 ≤ 73` the ODE reads
coefficientwise

  `(n+1)·[T^(n+1)] E₃₇ = [Tⁿ] E₃₇ + [n ≥ 36]·[T^(n−36)] E₃₇`.

The closed form `cₘ := 1/m! + (1/37)·[m ≥ 37]/(m−37)!` satisfies this recurrence (with `c₀ = 1`), so
by strong induction `[Tᵐ] E₃₇ = cₘ` for every `m ≤ 73` (`coeff_E37_eq`).  Equivalently
`E₃₇ ≡ exp(T)·(1 + T³⁷/37) mod T⁷⁴` (the two agree exactly up to degree `73`; they differ only at
degree `≥ 74 = 37²`, where the `T^(37²)/37²` and `(T³⁷/37)²/2` Frobenius terms enter).

## Why the closed form, not the Bernoulli formula

The proven `coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_bernoulli`
(`KummerLogFormalEvaluator/Coefficient.lean`) gives `formalSum_d = B_d/d` only for `2j ≤ p − 3 = 34`
(the Artin-Hasse exponential `E₃₇` agrees with the ordinary `exp` only below degree `37`).  At
`d = 68 > 34` the closed form `cₘ` above carries the genuine degree-`68 ≥ p` content (the Frobenius
correction `T³⁷/37`), which is exactly the difference between the Artin-Hasse value and the
out-of-range algebraic `B₆₈/68`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open PowerSeries

namespace ArtinHasse37

instance instFact37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- Local shorthand: the Artin-Hasse log series `L₃₇ = ∑ᵢ T^{37ⁱ}/37ⁱ` at `p = 37`. -/
def L37 : PowerSeries ℚ := Furtwaengler.artinHasseLogSeries 37

/-- Local shorthand: the Artin-Hasse exponential `E₃₇ = exp(L₃₇)` at `p = 37`. -/
def E37 : PowerSeries ℚ := Furtwaengler.artinHasseExpSeries 37

/-! ## 1. The Artin-Hasse ODE `E₃₇′ = E₃₇ · L₃₇′` -/

/-- **The Artin-Hasse ODE** (proven): `d⁄dX (E₃₇) = E₃₇ · d⁄dX (L₃₇)`.  Chain rule
(`derivative_subst`) applied to `E₃₇ = subst(L₃₇, exp)`, together with `exp′ = exp`
(`derivative_exp`) and `subst(L₃₇, exp) = E₃₇`. -/
theorem derivative_E37 :
    d⁄dX ℚ E37 = E37 * d⁄dX ℚ L37 := by
  rw [E37, L37]
  have hsub : HasSubst (Furtwaengler.artinHasseLogSeries 37) :=
    Furtwaengler.artinHasseLogSeries_hasSubst 37
  have hE : Furtwaengler.artinHasseExpSeries 37 =
      (PowerSeries.exp ℚ).subst (Furtwaengler.artinHasseLogSeries 37) := rfl
  rw [hE, derivative_subst hsub, derivative_exp ℚ]

/-! ## 2. The coefficients of `L₃₇′` below degree `73` -/

/-- **`L₃₇′` coefficients below degree `73`** (proven): for `j ≤ 72`,
`[Tʲ] (d⁄dX L₃₇) = if j = 0 then 1 else if j = 36 then 1 else 0`.

`[Tʲ] (d⁄dX L₃₇) = (j+1)·[T^(j+1)] L₃₇`, and `[T^(j+1)] L₃₇ = 1/37^(log₃₇(j+1))` iff `j+1` is a
positive power of `37`, else `0`.  For `j+1 ≤ 73` the only powers of `37` are `1` (`j = 0`, giving
`1·1 = 1`) and `37` (`j = 36`, giving `37·(1/37) = 1`); all other coefficients vanish. -/
theorem coeff_derivative_L37_of_le {j : ℕ} (hj : j ≤ 72) :
    (PowerSeries.coeff (R := ℚ) j) (d⁄dX ℚ L37) =
      (if j = 0 then 1 else if j = 36 then 1 else 0 : ℚ) := by
  rw [L37, coeff_derivative, Furtwaengler.artinHasseLogSeries_coeff]
  -- The `if`-condition `37 ^ log₃₇(j+1) = j+1 ∧ j+1 ≠ 0` is equivalent to `j+1 ∈ {1, 37}`.
  by_cases h0 : j = 0
  · subst h0
    simp [Nat.log_one_right]
  · by_cases h36 : j = 36
    · subst h36
      norm_num [show Nat.log 37 37 = 1 by norm_num [Nat.log]]
    · -- `j ≠ 0, 36`, `j ≤ 72`: `j+1` is not a power of `37`, so the coefficient is `0`.
      rw [if_neg h0, if_neg h36]
      have hcond : ¬ (37 ^ Nat.log 37 (j + 1) = j + 1 ∧ j + 1 ≠ 0) := by
        rintro ⟨hpow, _⟩
        -- `j + 1 ≤ 73 < 37² = 1369`, so `log₃₇(j+1) < 2`, hence `∈ {0, 1}`.
        have hlt : Nat.log 37 (j + 1) < 2 :=
          Nat.log_lt_of_lt_pow (by omega) (by omega : j + 1 < 37 ^ 2)
        interval_cases h : (Nat.log 37 (j + 1))
        · rw [pow_zero] at hpow; omega
        · rw [pow_one] at hpow; omega
      rw [if_neg hcond, zero_mul]

/-! ## 3. The coefficient recurrence for `E₃₇` -/

/-- **The `E₃₇` coefficient recurrence below degree `73`** (proven): for `n ≤ 72`,

  `(n+1)·[T^(n+1)] E₃₇ = [Tⁿ] E₃₇ + (if 36 ≤ n then [T^(n−36)] E₃₇ else 0)`.

Taking `[Tⁿ]` of the Artin-Hasse ODE `E₃₇′ = E₃₇·L₃₇′` (`derivative_E37`): the left side is
`(n+1)·[T^(n+1)] E₃₇` (`coeff_derivative`); the right side `[Tⁿ](E₃₇·L₃₇′)` is, via `coeff_mul` over
the antidiagonal of `n` and the `L₃₇′` coefficients (`coeff_derivative_L37_of_le`, nonzero only at
shift `0` with value `1` and shift `36` with value `1`), exactly `[Tⁿ] E₃₇ + [n ≥ 36]·[T^(n−36)]
E₃₇`. -/
theorem coeff_E37_recurrence {n : ℕ} (hn : n ≤ 72) :
    (PowerSeries.coeff (R := ℚ) (n + 1)) E37 * (n + 1) =
      (PowerSeries.coeff (R := ℚ) n) E37 +
        (if 36 ≤ n then (PowerSeries.coeff (R := ℚ) (n - 36)) E37 else 0) := by
  have hode := congrArg (PowerSeries.coeff (R := ℚ) n) derivative_E37
  rw [coeff_derivative] at hode
  rw [hode, PowerSeries.coeff_mul]
  -- Evaluate the antidiagonal sum: only `(n,0)` and (when `n ≥ 36`) `(n-36,36)` survive.
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- Summand at `k`: `[T^k] E₃₇ · [T^(n-k)] L₃₇′`.  `[T^(n-k)] L₃₇′` is nonzero only when
  -- `n - k = 0` (i.e. `k = n`, value `1`) or `n - k = 36` (i.e. `k = n - 36`, value `1`).
  have hsummand : ∀ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff (R := ℚ) k) E37 *
          (PowerSeries.coeff (R := ℚ) (n - k)) (d⁄dX ℚ L37) =
        (if k = n then (PowerSeries.coeff (R := ℚ) n) E37 else 0) +
          (if k = n - 36 then
            (if 36 ≤ n then (PowerSeries.coeff (R := ℚ) (n - 36)) E37 else 0) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [coeff_derivative_L37_of_le (by omega : n - k ≤ 72)]
    by_cases h0 : n - k = 0
    · -- `n - k = 0`: since `k ≤ n`, this is `k = n`.
      have hkn : k = n := by omega
      rw [h0, if_pos rfl, if_pos hkn, mul_one]
      -- The `k = n - 36` indicator: present only if `n = n - 36`, i.e. `n < 36` (`36 ≤ n` false).
      by_cases h36b : k = n - 36
      · rw [if_pos h36b, if_neg (by omega : ¬ 36 ≤ n), add_zero, hkn]
      · rw [if_neg h36b, add_zero, hkn]
    · by_cases h36 : n - k = 36
      · -- `n - k = 36`: `n ≥ 36` and `k = n - 36`.
        have hkn : k = n - 36 := by omega
        have hge : 36 ≤ n := by omega
        have hk1 : ¬ (k = n) := by omega
        rw [h36, if_neg (by norm_num : ¬ (36 : ℕ) = 0), if_pos rfl, mul_one,
          if_neg hk1, if_pos hkn, if_pos hge, zero_add, hkn]
      · -- `n - k ∉ {0, 36}`: the `L₃₇′` coefficient is `0`, and the RHS second term is `0`.
        rw [if_neg h0, if_neg h36, mul_zero]
        have hk1 : ¬ (k = n) := by omega
        rw [if_neg hk1]
        by_cases h36b : k = n - 36
        · -- `k = n - 36` and `n - k ≠ 36` force `¬ 36 ≤ n`, so the inner indicator is `0`.
          rw [if_pos h36b, if_neg (by omega : ¬ 36 ≤ n), add_zero]
        · rw [if_neg h36b, add_zero]
  rw [Finset.sum_congr rfl hsummand]
  -- The `k = n` indicator sums to `[Tⁿ] E₃₇` (`n ∈ range (n+1)`); the `k = n-36` indicator sums to
  -- the `36 ≤ n`-guarded `[T^(n−36)] E₃₇` (`n-36 ∈ range (n+1)` always) (`Finset.sum_ite_eq'`).
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr (by omega : n < n + 1)),
    if_pos (Finset.mem_range.mpr (by omega : n - 36 < n + 1))]

/-! ## 4. The closed form `cₘ` and the structural coefficient identity for `E₃₇` -/

/-- **The closed-form coefficient** `cₘ := 1/m! + (1/37)·[m ≥ 37]/(m−37)!`.  For `m ≤ 73` this is
`[Tᵐ] E₃₇` (`coeff_E37_eq`); it is exactly `[Tᵐ] (exp(T)·(1 + T³⁷/37))`. -/
def c (m : ℕ) : ℚ :=
  1 / (Nat.factorial m : ℚ) +
    (if 37 ≤ m then (1 / 37 : ℚ) * (1 / (Nat.factorial (m - 37) : ℚ)) else 0)

/-- **`c` satisfies the `E₃₇` recurrence** (proven): for `n ≤ 72`,

  `(n+1)·c (n+1) = c n + (if 36 ≤ n then c (n − 36) else 0)`,

the same recurrence `coeff_E37_recurrence` proves for `[T^·] E₃₇`.  A direct rational identity,
by cases on `n` versus `36` (whether the `n − 36` shift term is present) and `n + 1` versus `37`
(whether `c (n+1)` carries the Frobenius `1/37` term). -/
theorem c_recurrence {n : ℕ} (hn : n ≤ 72) :
    c (n + 1) * (n + 1) = c n + (if 36 ≤ n then c (n - 36) else 0) := by
  have hfac : ∀ k, (Nat.factorial (k + 1) : ℚ) = (k + 1) * (Nat.factorial k : ℚ) := by
    intro k; rw [Nat.factorial_succ]; push_cast; ring
  have hfac_ne : ∀ k, (Nat.factorial k : ℚ) ≠ 0 := by
    intro k; exact_mod_cast Nat.factorial_ne_zero k
  rcases lt_or_ge n 36 with hlt | hge
  · -- `n < 36`: no shift term on the right; `n + 1 ≤ 36 < 37`, so `c (n+1)` has no Frobenius term.
    rw [c, c, if_neg (by omega : ¬ 37 ≤ n + 1), if_neg (by omega : ¬ 37 ≤ n),
      if_neg (by omega : ¬ 36 ≤ n), add_zero, add_zero, add_zero]
    rw [hfac n]
    field_simp
  · -- `n ≥ 36`: shift term present; split on `n = 36` (then `n + 1 = 37` introduces the term).
    rw [if_pos hge]
    rcases eq_or_lt_of_le hge with heq | hgt
    · -- `n = 36`: `c 37 = 1/37! + (1/37)·1/0!`, `c 36 = 1/36!`, `c 0 = 1`.
      subst heq
      rw [c, c, c, if_pos (by norm_num : 37 ≤ 37), if_neg (by norm_num : ¬ 37 ≤ 36),
        if_neg (by norm_num : ¬ 37 ≤ (0 : ℕ))]
      norm_num [Nat.factorial]
    · -- `n > 36`: both `c (n+1)` and `c (n-36)` carry their Frobenius/factorial pieces.  The core
      -- identity is `(n+1) = (n−36) + 37`, via `(n+1)! = (n+1)·n!` and `(n−36)! = (n−36)·(n−37)!`.
      have hge37 : 37 ≤ n := by omega
      rw [c, c, c, if_pos (by omega : 37 ≤ n + 1), if_pos hge37,
        if_neg (by omega : ¬ 37 ≤ n - 36), add_zero]
      -- Expose `(n+1)! = (n+1)·n!` and `(n+1)-37 = n-36 = (n-36)·(n-37)!`.
      have hr1 : (Nat.factorial (n + 1) : ℚ) = ((n : ℚ) + 1) * (Nat.factorial n : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hr2 : ((n + 1 - 37 : ℕ)) = (n - 36 : ℕ) := by omega
      have hr3 : (Nat.factorial (n - 36) : ℚ) =
          (((n : ℚ) - 36)) * (Nat.factorial (n - 37) : ℚ) := by
        have : n - 36 = (n - 37) + 1 := by omega
        rw [this, Nat.factorial_succ]
        push_cast [Nat.cast_sub (by omega : 37 ≤ n)]; ring
      rw [hr2, hr1, hr3]
      -- Two independent factorial atoms `n!`, `(n-37)!`; the identity is `(n+1) = (n-36) + 37`.
      have hnf : (Nat.factorial n : ℚ) ≠ 0 := hfac_ne n
      have hdf : (Nat.factorial (n - 37) : ℚ) ≠ 0 := hfac_ne (n - 37)
      have hnp : ((n : ℚ) + 1) ≠ 0 := by positivity
      have hcm : ((n : ℚ) - 36) ≠ 0 := by
        have h36 : (36 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 36 < n)
        linarith
      field_simp
      ring

/-- **The constant coefficient of `E₃₇` is `1`** (proven): `[T⁰] E₃₇ = c 0 = 1`. -/
theorem coeff_zero_E37 : (PowerSeries.coeff (R := ℚ) 0) E37 = c 0 := by
  rw [E37, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Furtwaengler.artinHasseExpSeries_constantCoeff, c]
  norm_num

/-- **The structural coefficient identity for `E₃₇`** (proven): for every `m ≤ 73`,

  `[Tᵐ] E₃₇ = cₘ = 1/m! + (1/37)·[m ≥ 37]/(m−37)!`.

By strong induction on `m`: the base case `m = 0` is `coeff_zero_E37`, and the step at `m + 1`
combines the power-series recurrence `coeff_E37_recurrence` with the matching closed-form recurrence
`c_recurrence` (both `[Tⁿ] E₃₇ = cₙ` and `[T^(n−36)] E₃₇ = c (n−36)` available by strong induction,
as `n, n − 36 < n + 1`).  This is the `E₃₇ ≡ exp(T)·(1 + T³⁷/37) mod T⁷⁴` structure coefficientwise:
`cₘ` is precisely `[Tᵐ] (exp(T)·(1 + T³⁷/37))`. -/
theorem coeff_E37_eq : ∀ {m : ℕ}, m ≤ 73 → (PowerSeries.coeff (R := ℚ) m) E37 = c m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m with
    | 0 => exact coeff_zero_E37
    | (n + 1) =>
      have hn : n ≤ 72 := by omega
      -- Solve `[T^(n+1)] E₃₇·(n+1) = [Tⁿ] E₃₇ + [36≤n]·[T^(n-36)] E₃₇` for `[T^(n+1)] E₃₇`.
      have hrec := coeff_E37_recurrence (n := n) hn
      have hcrec := c_recurrence (n := n) hn
      have hcn : (PowerSeries.coeff (R := ℚ) n) E37 = c n := ih n (by omega) (by omega)
      have hcsub : (if 36 ≤ n then (PowerSeries.coeff (R := ℚ) (n - 36)) E37 else 0) =
          (if 36 ≤ n then c (n - 36) else 0) := by
        by_cases hge : 36 ≤ n
        · rw [if_pos hge, if_pos hge, ih (n - 36) (by omega) (by omega)]
        · rw [if_neg hge, if_neg hge]
      rw [hcn, hcsub] at hrec
      -- Now `[T^(n+1)] E₃₇·(n+1) = c (n+1)·(n+1)`; cancel the nonzero `(n+1)`.
      have hnp : ((n : ℚ) + 1) ≠ 0 := by positivity
      have hmul : (PowerSeries.coeff (R := ℚ) (n + 1)) E37 * (n + 1) = c (n + 1) * (n + 1) := by
        rw [hrec, ← hcrec]
      exact mul_right_cancel₀ hnp hmul

/-! ## 5. The bridge to the normalized numerator `g_AH = (E₃₇ − 1)/T` -/

/-- **The coefficients of the normalized Artin-Hasse numerator** `g_AH = (E₃₇ − 1)/T` below degree
`73` (proven): for `k ≤ 72`,

  `[Tᵏ] (rationalArtinHasseNormalizedExpMinusOneSeries 37) = c (k + 1)`.

`g_AH` is defined by shifting `E₃₇ − 1` (`rationalArtinHasseNormalizedExpMinusOneSeries_coeff`):
`[Tᵏ] g_AH = [T^(k+1)] (E₃₇ − 1) = [T^(k+1)] E₃₇` (as `k + 1 ≥ 1`), which is `c (k + 1)` by
`coeff_E37_eq` (`k + 1 ≤ 73`). -/
theorem coeff_gAH_eq {k : ℕ} (hk : k ≤ 72) :
    (PowerSeries.coeff (R := ℚ) k)
        (CyclotomicUnits.rationalArtinHasseNormalizedExpMinusOneSeries 37) = c (k + 1) := by
  rw [CyclotomicUnits.rationalArtinHasseNormalizedExpMinusOneSeries_coeff]
  -- `expMinusOneSeries 37 = E₃₇ - 1`; its `(k+1)`-coefficient is `[T^(k+1)] E₃₇` (since `k+1 ≥ 1`).
  have hE : BernoulliRegular.CyclotomicUnits.PadicLogSetup.FormalDwork.expMinusOneSeries 37 =
      E37 - 1 := rfl
  rw [hE, map_sub, PowerSeries.coeff_one, if_neg (by omega : ¬ k + 1 = 0), sub_zero,
    coeff_E37_eq (by omega : k + 1 ≤ 73)]

end ArtinHasse37

end BernoulliRegular.FLT37.Eichler

end
