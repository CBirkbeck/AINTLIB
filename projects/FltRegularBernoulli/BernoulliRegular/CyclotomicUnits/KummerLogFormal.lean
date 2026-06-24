module

public import BernoulliRegular.BernoulliGeneralized
public import BernoulliRegular.CyclotomicUnits.PadicLogSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseFormal
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal Kummer logarithm series

This file starts the purely formal coefficient calculation used by the
cyclotomic-units route.  The power-series variable is `T`; the scalar `X`
lives as a polynomial coefficient, so the formal Kummer logarithm is an
element of `ℚ[X]⟦T⟧`.

No analytic `p`-adic logarithm is used here.  The only logarithm below is
`PowerSeries.logOf`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits

/-- The coefficient ring for the two-variable formal Kummer logarithm:
power series in `T` whose coefficients are polynomials in the formal scalar
`X`. -/
abbrev KummerLogCoeffRing : Type :=
  Polynomial ℚ

/-- The formal scalar `X`, regarded as a coefficient of the `T`-power series. -/
abbrev kummerLogScalarX : KummerLogCoeffRing :=
  Polynomial.X

/-- The normalized Artin-Hasse numerator `(E_p(T)-1)/T`, represented by
shifting the coefficients of `E_p(T)-1`. -/
def formalArtinHasseNormalizedExpMinusOne (p : ℕ) [Fact p.Prime] :
    PowerSeries KummerLogCoeffRing :=
  PowerSeries.mk fun n ↦
    Polynomial.C
      ((PowerSeries.coeff (R := ℚ) (n + 1))
        (PadicLogSetup.FormalDwork.expMinusOneSeries p))

@[simp]
theorem formalArtinHasseNormalizedExpMinusOne_coeff (p n : ℕ) [Fact p.Prime] :
    (PowerSeries.coeff (R := KummerLogCoeffRing) n)
        (formalArtinHasseNormalizedExpMinusOne p) =
      Polynomial.C
        ((PowerSeries.coeff (R := ℚ) (n + 1))
          (PadicLogSetup.FormalDwork.expMinusOneSeries p)) := by
  simp [formalArtinHasseNormalizedExpMinusOne]

@[simp]
theorem formalArtinHasseNormalizedExpMinusOne_constantCoeff (p : ℕ)
    [Fact p.Prime] :
    PowerSeries.constantCoeff (formalArtinHasseNormalizedExpMinusOne p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [formalArtinHasseNormalizedExpMinusOne]

/-- The normalized denominator `(E_p(X*T)-1)/(X*T)`, obtained by the formal
rescaling operation `T ↦ X*T`. -/
def formalArtinHasseScaledNormalizedExpMinusOne (p : ℕ) [Fact p.Prime] :
    PowerSeries KummerLogCoeffRing :=
  PowerSeries.rescale kummerLogScalarX
    (formalArtinHasseNormalizedExpMinusOne p)

@[simp]
theorem formalArtinHasseScaledNormalizedExpMinusOne_constantCoeff (p : ℕ)
    [Fact p.Prime] :
    PowerSeries.constantCoeff (formalArtinHasseScaledNormalizedExpMinusOne p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    formalArtinHasseScaledNormalizedExpMinusOne,
    PowerSeries.coeff_rescale]
  simp [kummerLogScalarX]

/-- The formal Kummer logarithm
`log ((E_p(T)-1)/T) - log ((E_p(X*T)-1)/(X*T))`.

This is the normalized formal version of
`log (X * (E_p(T)-1)/(E_p(X*T)-1))`, after cancelling the common factor
`X*T` in the quotient. -/
def formalKummerLogSeries (p : ℕ) [Fact p.Prime] :
    PowerSeries KummerLogCoeffRing :=
  PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p) -
    PowerSeries.logOf (formalArtinHasseScaledNormalizedExpMinusOne p)

/-- The formal Kummer logarithm is exactly the difference of the two
one-variable normalized Artin-Hasse logarithms. -/
theorem formalKummerLogSeries_eq_logOf_normalized_sub_scaled (p : ℕ)
    [Fact p.Prime] :
    formalKummerLogSeries p =
      PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p) -
        PowerSeries.logOf (formalArtinHasseScaledNormalizedExpMinusOne p) :=
  rfl

/-- The quotient of normalized Artin-Hasse units as a formal power series.
This is the formal replacement for division by `(E_p(X*T)-1)/(X*T)`. -/
def formalKummerQuotientUnit (p : ℕ) [Fact p.Prime] :
    PowerSeries KummerLogCoeffRing :=
  formalArtinHasseNormalizedExpMinusOne p *
    PowerSeries.invOfUnit (formalArtinHasseScaledNormalizedExpMinusOne p) 1

/-- The formal quotient unit really is the normalized numerator divided by the
normalized denominator. -/
theorem formalKummerQuotientUnit_mul_scaled_eq_normalized (p : ℕ)
    [Fact p.Prime] :
    formalKummerQuotientUnit p * formalArtinHasseScaledNormalizedExpMinusOne p =
      formalArtinHasseNormalizedExpMinusOne p := by
  calc
    formalKummerQuotientUnit p * formalArtinHasseScaledNormalizedExpMinusOne p
        =
          formalArtinHasseNormalizedExpMinusOne p *
            (PowerSeries.invOfUnit (formalArtinHasseScaledNormalizedExpMinusOne p) 1 *
              formalArtinHasseScaledNormalizedExpMinusOne p) := by
          rw [formalKummerQuotientUnit]
          ring
    _ = formalArtinHasseNormalizedExpMinusOne p * 1 := by
          rw [PowerSeries.invOfUnit_mul
            (formalArtinHasseScaledNormalizedExpMinusOne p) 1
            (formalArtinHasseScaledNormalizedExpMinusOne_constantCoeff p)]
    _ = formalArtinHasseNormalizedExpMinusOne p := by rw [mul_one]

/-- The ordinary formal exponential numerator `(exp(T)-1)/T`.  This is used
as the low-degree model for the Artin-Hasse normalized numerator. -/
def formalExpNormalizedMinusOne : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    (PowerSeries.coeff (R := ℚ) (n + 1)) (PowerSeries.exp ℚ)

@[simp]
theorem formalExpNormalizedMinusOne_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n) formalExpNormalizedMinusOne =
      (PowerSeries.coeff (R := ℚ) (n + 1)) (PowerSeries.exp ℚ) := by
  simp [formalExpNormalizedMinusOne]

@[simp]
theorem formalExpNormalizedMinusOne_constantCoeff :
    PowerSeries.constantCoeff formalExpNormalizedMinusOne = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [formalExpNormalizedMinusOne]

theorem exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne :
    PowerSeries.exp ℚ - 1 =
      PowerSeries.X * formalExpNormalizedMinusOne := by
  simpa [formalExpNormalizedMinusOne] using
    (PowerSeries.sub_const_eq_X_mul_shift (PowerSeries.exp ℚ))

theorem bernoulliPowerSeries_mul_formalExpNormalizedMinusOne :
    _root_.bernoulliPowerSeries ℚ * formalExpNormalizedMinusOne = 1 := by
  apply PowerSeries.X_mul_cancel
  calc
    PowerSeries.X * (_root_.bernoulliPowerSeries ℚ * formalExpNormalizedMinusOne)
        = _root_.bernoulliPowerSeries ℚ *
            (PowerSeries.X * formalExpNormalizedMinusOne) := by ring
    _ = _root_.bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) := by
          rw [← exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
    _ = PowerSeries.X := by
          rw [_root_.bernoulliPowerSeries_mul_exp_sub_one]
    _ = PowerSeries.X * (1 : PowerSeries ℚ) := by rw [mul_one]

theorem derivative_logOf_formalExpNormalizedMinusOne_mul_self :
    (d⁄dX ℚ (PowerSeries.logOf formalExpNormalizedMinusOne)) *
        formalExpNormalizedMinusOne =
      d⁄dX ℚ formalExpNormalizedMinusOne := by
  let N : PowerSeries ℚ := formalExpNormalizedMinusOne
  have hN0 : PowerSeries.constantCoeff (N - 1) = 0 := by
    simp [N]
  have hsubst : PowerSeries.HasSubst (N - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hN0
  have hgeom :
      PowerSeries.subst (N - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) * N = 1 := by
    have h :=
      Furtwaengler.FiniteLogFormal.subst_deriv_log_mul_one_add (A := ℚ) hsubst
    simpa [N, sub_eq_add_neg, add_assoc] using h
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℚ hsubst]
  have hderiv_sub : d⁄dX ℚ (N - 1) = d⁄dX ℚ N := by simp
  calc
    (PowerSeries.subst (N - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) *
          d⁄dX ℚ (N - 1)) * N
        =
          (PowerSeries.subst (N - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) * N) *
            d⁄dX ℚ N := by
          rw [hderiv_sub]
          ring
    _ = 1 * d⁄dX ℚ N := by rw [hgeom]
    _ = d⁄dX ℚ N := by rw [one_mul]

theorem X_mul_derivative_logOf_formalExpNormalizedMinusOne :
    PowerSeries.X * (d⁄dX ℚ (PowerSeries.logOf formalExpNormalizedMinusOne)) =
      PowerSeries.X + _root_.bernoulliPowerSeries ℚ - 1 := by
  let N : PowerSeries ℚ := formalExpNormalizedMinusOne
  let B : PowerSeries ℚ := _root_.bernoulliPowerSeries ℚ
  let D : PowerSeries ℚ := d⁄dX ℚ (PowerSeries.logOf N)
  have hBN : B * N = 1 := by
    simpa [B, N] using bernoulliPowerSeries_mul_formalExpNormalizedMinusOne
  have hNB : N * B = 1 := by rw [mul_comm, hBN]
  have hDN : D * N = d⁄dX ℚ N := by
    simpa [D, N] using derivative_logOf_formalExpNormalizedMinusOne_mul_self
  have hD_eq : D = B * (d⁄dX ℚ N) := by
    calc
      D = D * 1 := by rw [mul_one]
      _ = D * (N * B) := by rw [hNB]
      _ = (D * N) * B := by ring
      _ = (d⁄dX ℚ N) * B := by rw [hDN]
      _ = B * (d⁄dX ℚ N) := by ring
  have hN_XdN :
      N + PowerSeries.X * (d⁄dX ℚ N) = PowerSeries.exp ℚ := by
    calc
      N + PowerSeries.X * (d⁄dX ℚ N)
          = d⁄dX ℚ (PowerSeries.X * N) := by
            change N + PowerSeries.X * PowerSeries.derivativeFun N =
              PowerSeries.derivativeFun (PowerSeries.X * N)
            rw [PowerSeries.derivativeFun_mul]
            have hdx : PowerSeries.derivativeFun (PowerSeries.X : PowerSeries ℚ) = 1 := by
              ext n
              by_cases hn : n = 0
              · simp [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_X, hn]
              · simp [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_X, hn]
            rw [hdx]
            ring
      _ = d⁄dX ℚ (PowerSeries.exp ℚ - 1) := by
            rw [← exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
      _ = PowerSeries.exp ℚ := by
            simp [PowerSeries.derivative_exp]
  have hBexp : B * PowerSeries.exp ℚ = PowerSeries.X + B := by
    calc
      B * PowerSeries.exp ℚ
          = B * ((PowerSeries.exp ℚ - 1) + 1) := by ring
      _ = B * (PowerSeries.exp ℚ - 1) + B := by ring
      _ = B * (PowerSeries.X * N) + B := by
            rw [exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
      _ = PowerSeries.X * (B * N) + B := by ring
      _ = PowerSeries.X + B := by rw [hBN, mul_one]
  calc
    PowerSeries.X * D
        = PowerSeries.X * (B * (d⁄dX ℚ N)) := by rw [hD_eq]
    _ = B * (PowerSeries.X * (d⁄dX ℚ N)) := by ring
    _ = B * (PowerSeries.exp ℚ - N) := by
          have hsub : PowerSeries.X * (d⁄dX ℚ N) = PowerSeries.exp ℚ - N := by
            rw [← hN_XdN]
            abel
          rw [hsub]
    _ = B * PowerSeries.exp ℚ - B * N := by ring
    _ = (PowerSeries.X + B) - 1 := by rw [hBexp, hBN]
    _ = PowerSeries.X + B - 1 := by ring

theorem coeff_logOf_formalExpNormalizedMinusOne_eq_bernoulli
    {n : ℕ} (hn : 1 < n) :
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf formalExpNormalizedMinusOne) =
      (_root_.bernoulli n : ℚ) / ((n : ℚ) * (Nat.factorial n : ℚ)) := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hn_ne_zero : n ≠ 0 := Nat.ne_of_gt hnpos
  have hn_ne_one : n ≠ 1 := by omega
  have hcoeff :=
    congrArg (PowerSeries.coeff (R := ℚ) n)
      X_mul_derivative_logOf_formalExpNormalizedMinusOne
  rw [show n = (n - 1) + 1 by omega, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative] at hcoeff
  have hnsub : n - 1 + 1 = n := by omega
  rw [hnsub] at hcoeff
  have hncast : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
    exact_mod_cast hnsub
  rw [hncast] at hcoeff
  have hcoeff' :
      (PowerSeries.coeff (R := ℚ) n)
          (PowerSeries.logOf formalExpNormalizedMinusOne) * (n : ℚ) =
        (_root_.bernoulli n : ℚ) / (Nat.factorial n : ℚ) := by
    simpa [_root_.bernoulliPowerSeries, PowerSeries.coeff_X, hn_ne_zero, hn_ne_one]
      using hcoeff
  calc
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.logOf formalExpNormalizedMinusOne)
        =
          ((PowerSeries.coeff (R := ℚ) n)
            (PowerSeries.logOf formalExpNormalizedMinusOne) * (n : ℚ)) / (n : ℚ) := by
          field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn_ne_zero]
    _ = ((_root_.bernoulli n : ℚ) / (Nat.factorial n : ℚ)) / (n : ℚ) := by
          rw [hcoeff']
    _ = (_root_.bernoulli n : ℚ) / ((n : ℚ) * (Nat.factorial n : ℚ)) := by
          field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn_ne_zero,
            show (Nat.factorial n : ℚ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n]

theorem coeff_logOf_formalExpNormalizedMinusOne_one :
    (PowerSeries.coeff (R := ℚ) 1)
        (PowerSeries.logOf formalExpNormalizedMinusOne) =
      (1 / 2 : ℚ) := by
  have hcoeff :=
    congrArg (PowerSeries.coeff (R := ℚ) 1)
      X_mul_derivative_logOf_formalExpNormalizedMinusOne
  rw [show 1 = 0 + 1 by rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative] at hcoeff
  have h :
      (PowerSeries.coeff (R := ℚ) 1)
          (PowerSeries.logOf formalExpNormalizedMinusOne) =
        (1 + -1 / 2 : ℚ) := by
    simpa [_root_.bernoulliPowerSeries, _root_.bernoulli_one] using hcoeff
  rw [h]
  norm_num

theorem coeff_pow_eq_of_coeff_eq_le
    {A : Type*} [CommSemiring A] {F G : PowerSeries A} :
    ∀ (m d : ℕ), (∀ k, k ≤ d → PowerSeries.coeff k F = PowerSeries.coeff k G) →
      PowerSeries.coeff d (F ^ m) = PowerSeries.coeff d (G ^ m)
  | 0, d, _ => by simp
  | m + 1, d, h => by
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, k⟩ hik
      have hiksum : i + k = d := Finset.mem_antidiagonal.mp hik
      have hi : i ≤ d := by omega
      have hk : k ≤ d := by omega
      change PowerSeries.coeff i (F ^ m) * PowerSeries.coeff k F =
        PowerSeries.coeff i (G ^ m) * PowerSeries.coeff k G
      rw [coeff_pow_eq_of_coeff_eq_le (m := m) (d := i)
          (fun t ht ↦ h t (ht.trans hi)),
        h k hk]

theorem coeff_logOf_eq_of_coeff_eq_le
    {A : Type*} [CommRing A] [Algebra ℚ A] {F G : PowerSeries A} {d : ℕ}
    (hF0 : PowerSeries.constantCoeff F = 1)
    (hG0 : PowerSeries.constantCoeff G = 1)
    (hcoeff : ∀ k, k ≤ d → PowerSeries.coeff k F = PowerSeries.coeff k G) :
    PowerSeries.coeff d (PowerSeries.logOf F) =
      PowerSeries.coeff d (PowerSeries.logOf G) := by
  have hFsub0 : PowerSeries.constantCoeff (F - 1) = 0 := by simp [hF0]
  have hGsub0 : PowerSeries.constantCoeff (G - 1) = 0 := by simp [hG0]
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq,
    Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (F - 1) hFsub0 d,
    Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (G - 1) hGsub0 d]
  refine Finset.sum_congr rfl ?_
  intro m hm
  congr 1
  exact coeff_pow_eq_of_coeff_eq_le (m := m) (d := d) fun k hk ↦ by
    simp [hcoeff k hk]

theorem map_logOf_of_constantCoeff_eq_one
    {A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℚ A] [Algebra ℚ A']
    (f : A →+* A') {F : PowerSeries A}
    (hF0 : PowerSeries.constantCoeff F = 1) :
    PowerSeries.map f (PowerSeries.logOf F) =
      PowerSeries.logOf (PowerSeries.map f F) := by
  have hsub0 : PowerSeries.constantCoeff (F - 1) = 0 := by simp [hF0]
  have hsubst : PowerSeries.HasSubst (F - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hsub0
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq]
  change (PowerSeries.subst (F - 1) (PowerSeries.log A)).map f =
    PowerSeries.subst ((PowerSeries.map f) F - 1) (PowerSeries.log A')
  rw [PowerSeries.map_subst hsubst, PowerSeries.map_log]
  congr 1
  ext n
  calc
    (PowerSeries.coeff n) ((MvPowerSeries.map f) (F - 1))
        = f ((PowerSeries.coeff n) (F - 1)) :=
          PowerSeries.coeff_map (f := f) n (F - 1)
    _ = (PowerSeries.coeff n) ((PowerSeries.map f) F - 1) := by
          simp [PowerSeries.coeff_map]

theorem coeff_logOf_map_C_formalExpNormalizedMinusOne (n : ℕ) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) n)
        (PowerSeries.logOf
          (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ)
            formalExpNormalizedMinusOne)) =
      Polynomial.C
        ((PowerSeries.coeff (R := ℚ) n)
          (PowerSeries.logOf formalExpNormalizedMinusOne)) := by
  have hmap :=
    map_logOf_of_constantCoeff_eq_one
      (Polynomial.C : ℚ →+* Polynomial ℚ)
      (F := formalExpNormalizedMinusOne)
      formalExpNormalizedMinusOne_constantCoeff
  have hcoeff := congrArg (PowerSeries.coeff (R := KummerLogCoeffRing) n) hmap
  simpa using hcoeff.symm

theorem coeff_logOf_rescale_eq_pow_mul_coeff_logOf
    {A : Type*} [CommRing A] [Algebra ℚ A] (a : A)
    {F : PowerSeries A} (hF0 : PowerSeries.constantCoeff F = 1) (d : ℕ) :
    PowerSeries.coeff d (PowerSeries.logOf (PowerSeries.rescale a F)) =
      a ^ d * PowerSeries.coeff d (PowerSeries.logOf F) := by
  have hres0 : PowerSeries.constantCoeff (PowerSeries.rescale a F) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    simp [hF0]
  have hFsub0 : PowerSeries.constantCoeff (F - 1) = 0 := by
    simp [hF0]
  have hRsub0 : PowerSeries.constantCoeff (PowerSeries.rescale a F - 1) = 0 := by
    simp [hres0]
  have hsub :
      PowerSeries.rescale a F - 1 = PowerSeries.rescale a (F - 1) := by
    rw [map_sub, map_one]
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq,
    Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (PowerSeries.rescale a F - 1) hRsub0 d,
    Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (F - 1) hFsub0 d]
  calc
    (∑ n ∈ Finset.Icc 1 d,
        algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / n) *
          PowerSeries.coeff d ((PowerSeries.rescale a F - 1) ^ n))
        =
          ∑ n ∈ Finset.Icc 1 d,
            algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / n) *
              (a ^ d * PowerSeries.coeff d ((F - 1) ^ n)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [hsub, ← map_pow, PowerSeries.coeff_rescale]
    _ =
          a ^ d *
            ∑ n ∈ Finset.Icc 1 d,
              algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / n) *
                PowerSeries.coeff d ((F - 1) ^ n) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring

theorem coeff_logOf_formalArtinHasseNormalizedExpMinusOne_eq_bernoulli
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
        (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p)) =
      Polynomial.C
        ((_root_.bernoulli (2 * j) : ℚ) /
          (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ))) := by
  let G : PowerSeries KummerLogCoeffRing :=
    PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) formalExpNormalizedMinusOne
  have hG0 : PowerSeries.constantCoeff G = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [G]
  have hlow :
      ∀ k, k ≤ 2 * j →
        (PowerSeries.coeff (R := KummerLogCoeffRing) k)
            (formalArtinHasseNormalizedExpMinusOne p) =
          PowerSeries.coeff k G := by
    intro k hk
    have hklt : k + 1 < p := by omega
    dsimp [G]
    rw [formalArtinHasseNormalizedExpMinusOne_coeff, formalExpNormalizedMinusOne_coeff]
    have hAH :
        (PowerSeries.coeff (R := ℚ) (k + 1))
            (PadicLogSetup.FormalDwork.expMinusOneSeries p) =
          (PowerSeries.coeff (R := ℚ) (k + 1)) (PowerSeries.exp ℚ) := by
      simp [PadicLogSetup.FormalDwork.expMinusOneSeries,
        Furtwaengler.artinHasseExpMinusOneSeries,
        Furtwaengler.artinHasseExpSeries_coeff_eq_inv_factorial_of_lt p hklt]
    rw [hAH]
  calc
    (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
        (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p))
        =
          (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
            (PowerSeries.logOf G) :=
          coeff_logOf_eq_of_coeff_eq_le
            (formalArtinHasseNormalizedExpMinusOne_constantCoeff p) hG0 hlow
    _ = Polynomial.C
          ((PowerSeries.coeff (R := ℚ) (2 * j))
            (PowerSeries.logOf formalExpNormalizedMinusOne)) := by
          dsimp [G]
          rw [coeff_logOf_map_C_formalExpNormalizedMinusOne]
    _ = Polynomial.C
          ((_root_.bernoulli (2 * j) : ℚ) /
            (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ))) := by
          rw [coeff_logOf_formalExpNormalizedMinusOne_eq_bernoulli]
          omega

theorem coeff_logOf_formalArtinHasseNormalizedExpMinusOne_one
    {p : ℕ} [Fact p.Prime] (hp_three : 3 ≤ p) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) 1)
        (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p)) =
      Polynomial.C (1 / 2 : ℚ) := by
  let G : PowerSeries KummerLogCoeffRing :=
    PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) formalExpNormalizedMinusOne
  have hG0 : PowerSeries.constantCoeff G = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [G]
  have hlow :
      ∀ k, k ≤ 1 →
        (PowerSeries.coeff (R := KummerLogCoeffRing) k)
            (formalArtinHasseNormalizedExpMinusOne p) =
          PowerSeries.coeff k G := by
    intro k hk
    have hklt : k + 1 < p := by omega
    dsimp [G]
    rw [formalArtinHasseNormalizedExpMinusOne_coeff, formalExpNormalizedMinusOne_coeff]
    have hAH :
        (PowerSeries.coeff (R := ℚ) (k + 1))
            (PadicLogSetup.FormalDwork.expMinusOneSeries p) =
          (PowerSeries.coeff (R := ℚ) (k + 1)) (PowerSeries.exp ℚ) := by
      simp [PadicLogSetup.FormalDwork.expMinusOneSeries,
        Furtwaengler.artinHasseExpMinusOneSeries,
        Furtwaengler.artinHasseExpSeries_coeff_eq_inv_factorial_of_lt p hklt]
    rw [hAH]
  calc
    (PowerSeries.coeff (R := KummerLogCoeffRing) 1)
        (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p))
        =
          (PowerSeries.coeff (R := KummerLogCoeffRing) 1)
            (PowerSeries.logOf G) :=
          coeff_logOf_eq_of_coeff_eq_le
            (formalArtinHasseNormalizedExpMinusOne_constantCoeff p) hG0 hlow
    _ = Polynomial.C
          ((PowerSeries.coeff (R := ℚ) 1)
            (PowerSeries.logOf formalExpNormalizedMinusOne)) := by
          dsimp [G]
          rw [coeff_logOf_map_C_formalExpNormalizedMinusOne]
    _ = Polynomial.C (1 / 2 : ℚ) := by
          rw [coeff_logOf_formalExpNormalizedMinusOne_one]

theorem coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_pow_mul
    (p d : ℕ) [Fact p.Prime] :
    (PowerSeries.coeff (R := KummerLogCoeffRing) d)
        (PowerSeries.logOf (formalArtinHasseScaledNormalizedExpMinusOne p)) =
      kummerLogScalarX ^ d *
        (PowerSeries.coeff (R := KummerLogCoeffRing) d)
          (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p)) := by
  simpa [formalArtinHasseScaledNormalizedExpMinusOne] using
    (coeff_logOf_rescale_eq_pow_mul_coeff_logOf
      (A := KummerLogCoeffRing) kummerLogScalarX
      (F := formalArtinHasseNormalizedExpMinusOne p)
      (formalArtinHasseNormalizedExpMinusOne_constantCoeff p) d)

theorem coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_bernoulli
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
        (PowerSeries.logOf (formalArtinHasseScaledNormalizedExpMinusOne p)) =
      kummerLogScalarX ^ (2 * j) *
        Polynomial.C
          ((_root_.bernoulli (2 * j) : ℚ) /
            (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ))) := by
  rw [coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_pow_mul,
    coeff_logOf_formalArtinHasseNormalizedExpMinusOne_eq_bernoulli hj hjp]

theorem coeff_formalKummerLogSeries_eq_neg_bernoulli_mul_X_pow_sub_one
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
        (formalKummerLogSeries p) =
      -Polynomial.C
          ((_root_.bernoulli (2 * j) : ℚ) /
            (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ))) *
        (Polynomial.X ^ (2 * j) - 1) := by
  let q : ℚ :=
    (_root_.bernoulli (2 * j) : ℚ) /
      (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ))
  have hnorm :
      (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
          (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p)) =
        Polynomial.C q := by
    simpa [q] using
      (coeff_logOf_formalArtinHasseNormalizedExpMinusOne_eq_bernoulli
        (p := p) (j := j) hj hjp)
  have hscaled :
      (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
          (PowerSeries.logOf (formalArtinHasseScaledNormalizedExpMinusOne p)) =
        kummerLogScalarX ^ (2 * j) * Polynomial.C q := by
    simpa [q] using
      (coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_bernoulli
        (p := p) (j := j) hj hjp)
  calc
    (PowerSeries.coeff (R := KummerLogCoeffRing) (2 * j))
        (formalKummerLogSeries p)
        =
          Polynomial.C q - kummerLogScalarX ^ (2 * j) * Polynomial.C q := by
          simp [formalKummerLogSeries, hnorm, hscaled]
    _ =
          -Polynomial.C q * (Polynomial.X ^ (2 * j) - 1) := by
          simp only [kummerLogScalarX]
          ring

/-- Reduction of a rational number modulo `p`, written using numerator and
denominator.  The later coefficient theorems use separate hypotheses proving
that the denominators in question are units modulo `p`. -/
def ratReductionZMod (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  (q.num : ZMod p) / (q.den : ZMod p)

/-- The Bernoulli factor in the final formal congruence, namely the reduction
of `B_(2*j)/(2*j)` modulo `p`. -/
def bernoulliFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  ratReductionZMod p (((_root_.bernoulli (2 * j) : ℚ) / (2 * j : ℚ)))

/-- The explicit unit factor used for the CU-11d coefficient convention.  The
factorial is a unit in the final range `2*j <= p - 3`. -/
def kummerLogUnitFactor (p : ℕ) (_j : ℕ) [Fact p.Prime] : ZMod p :=
  -(((Nat.factorial (2 * _j) : ℕ) : ZMod p)⁻¹)

theorem factorial_two_mul_index_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (((Nat.factorial (2 * j) : ℕ) : ZMod p)) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ Nat.factorial (2 * j) :=
    (ZMod.natCast_eq_zero_iff (Nat.factorial (2 * j)) p).mp hzero
  have hlt : 2 * j < p := by omega
  exact Nat.not_lt.mpr ((Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)).mp hp_dvd) hlt

theorem factorial_two_mul_index_zmod_isUnit {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    IsUnit (((Nat.factorial (2 * j) : ℕ) : ZMod p)) :=
  isUnit_iff_ne_zero.mpr (factorial_two_mul_index_zmod_ne_zero hj hjp)

theorem kummerLogUnitFactor_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 := by
  simpa [kummerLogUnitFactor] using
    (neg_ne_zero.mpr (inv_ne_zero (factorial_two_mul_index_zmod_ne_zero hj hjp)))

theorem kummerLogUnitFactor_isUnit {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    IsUnit (kummerLogUnitFactor p j) :=
  isUnit_iff_ne_zero.mpr (kummerLogUnitFactor_ne_zero hj hjp)

/-- Under the CU-11d range hypotheses, the integer `2*j` is nonzero modulo
`p`. -/
theorem two_mul_index_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ((2 * j : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ 2 * j :=
    (ZMod.natCast_eq_zero_iff (2 * j) p).mp hzero
  have hpos : 0 < 2 * j := by omega
  have hp_le : p ≤ 2 * j := Nat.le_of_dvd hpos hp_dvd
  omega

/-- Under the CU-11d range hypotheses, `2*j` is a unit modulo `p`. -/
theorem two_mul_index_zmod_isUnit {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    IsUnit ((2 * j : ℕ) : ZMod p) :=
  isUnit_iff_ne_zero.mpr (two_mul_index_zmod_ne_zero hj hjp)

/-- Under the CU-11d range hypotheses, `p` does not divide the denominator of
`B_(2*j)`. -/
theorem prime_not_dvd_bernoulli_den_two_mul {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ¬ p ∣ (_root_.bernoulli (2 * j)).den := by
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    have : 2 * j ≤ 0 := by omega
    omega
  exact BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one
    (p := p) (n := 2 * j) hp_ne_two (by omega)

/-- Under the CU-11d range hypotheses, the Bernoulli denominator is nonzero
modulo `p`. -/
theorem bernoulli_den_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (((_root_.bernoulli (2 * j)).den : ℕ) : ZMod p) ≠ 0 := fun hzero ↦
  prime_not_dvd_bernoulli_den_two_mul hj hjp
    ((ZMod.natCast_eq_zero_iff ((_root_.bernoulli (2 * j)).den) p).mp hzero)

/-- Under the CU-11d range hypotheses, the Bernoulli denominator is a unit
modulo `p`. -/
theorem bernoulli_den_zmod_isUnit {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    IsUnit (((_root_.bernoulli (2 * j)).den : ℕ) : ZMod p) :=
  isUnit_iff_ne_zero.mpr (bernoulli_den_zmod_ne_zero hj hjp)

/-- The two denominator-unit facts needed to interpret
`B_(2*j)/(2*j)` modulo `p` in the CU-11d range. -/
theorem bernoulliFactor_denominators_isUnit {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    IsUnit (((_root_.bernoulli (2 * j)).den : ℕ) : ZMod p) ∧
      IsUnit ((2 * j : ℕ) : ZMod p) :=
  ⟨bernoulli_den_zmod_isUnit hj hjp, two_mul_index_zmod_isUnit hj hjp⟩

/-- The coefficient ring for the final mod-`p` formal Kummer coefficient. -/
abbrev KummerLogModCoeffRing (p : ℕ) : Type :=
  Polynomial (ZMod p)

/-- The reduced scalar multiplying `X^(2*j)-1` in the final mod-`p`
coefficient formula.  It is the Bernoulli factor times the factorial unit
coming from the formal logarithm coefficient convention. -/
def reducedKummerLogCoeffFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  kummerLogUnitFactor p j * bernoulliFactor p j

/-- The final mod-`p` formal coefficient target for CU-11d. -/
def formalKummerLogCoeffModP (p j : ℕ) [Fact p.Prime] :
    KummerLogModCoeffRing p :=
  Polynomial.C (reducedKummerLogCoeffFactor p j) *
    (Polynomial.X ^ (2 * j) - 1)

theorem reducedKummerLogCoeffFactor_eq_unit_mul_bernoulliFactor
    (p j : ℕ) [Fact p.Prime] :
    reducedKummerLogCoeffFactor p j =
      kummerLogUnitFactor p j * bernoulliFactor p j :=
  rfl

/-- The denominator units needed to interpret the CU-11d coefficient after
reduction modulo `p`. -/
theorem reducedKummerLogCoeffFactor_denominators_isUnit
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    IsUnit (((Nat.factorial (2 * j) : ℕ) : ZMod p)) ∧
      IsUnit (((_root_.bernoulli (2 * j)).den : ℕ) : ZMod p) ∧
        IsUnit ((2 * j : ℕ) : ZMod p) :=
  ⟨factorial_two_mul_index_zmod_isUnit hj hjp,
    bernoulli_den_zmod_isUnit hj hjp, two_mul_index_zmod_isUnit hj hjp⟩

/-- The factorial unit factor remains nonzero after reduction modulo `p`. -/
theorem reducedKummerLogCoeffFactor_unit_ne_zero
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 :=
  kummerLogUnitFactor_ne_zero hj hjp

/-- The CU-11d coefficient identity in the chosen `ZMod p[X]` formal target. -/
theorem formalKummerLogCoeffModP_eq
    (p j : ℕ) [Fact p.Prime] :
    formalKummerLogCoeffModP p j =
      Polynomial.C (kummerLogUnitFactor p j * bernoulliFactor p j) *
        (Polynomial.X ^ (2 * j) - 1) :=
  rfl

/-- Final unspecialized CU-11d coefficient theorem over `ZMod p[X]`.  This is
the form intended for later specialization of `X`. -/
theorem formalKummerLogCoeffModP_eq_unit_mul_bernoulliFactor
    (p j : ℕ) [Fact p.Prime] :
    formalKummerLogCoeffModP p j =
      Polynomial.C (kummerLogUnitFactor p j * bernoulliFactor p j) *
        (Polynomial.X ^ (2 * j) - 1) :=
  formalKummerLogCoeffModP_eq p j

/-- The unit factor in the final unspecialized CU-11d theorem is nonzero. -/
theorem formalKummerLogCoeffModP_unit_ne_zero
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 :=
  kummerLogUnitFactor_ne_zero hj hjp

/-- Evaluation form of the final unspecialized CU-11d theorem.  CU-11e will
apply this with `x` a Teichmuller/residue column value. -/
theorem formalKummerLogCoeffModP_eval
    (p j : ℕ) [Fact p.Prime] (x : ZMod p) :
    Polynomial.eval x (formalKummerLogCoeffModP p j) =
      (kummerLogUnitFactor p j * bernoulliFactor p j) *
        (x ^ (2 * j) - 1) := by
  simp [formalKummerLogCoeffModP, reducedKummerLogCoeffFactor]

end CyclotomicUnits
end BernoulliRegular

end
