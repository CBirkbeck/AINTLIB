module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLog

/-!
# Denominator bridge for finite logarithm terms

This file records the quotient-level denominator identities for the finite-log
terms.  The construction in `FiniteLog` chooses local representatives for
`x^n / n`; the main lemmas here say that multiplying the chosen quotient term
by `n` recovers the expected numerator.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Multiplying the unsigned finite-log term by `n` recovers `x^n` in the
quotient.  This is the quotient-facing bridge from the local-denominator
construction to the expected rational term `x^n / n`. -/
theorem finiteLogTermCore_natCast_mul_eq_mk {N n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
        F.finiteLogTermCore N n x hx =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ n) := by
  classical
  let m : ℕ := n.factorization ℓ
  let d : F.Q.primeCompl := F.finiteLogTermDenom n x hx
  let c : F.Q.primeCompl := F.ordComplPrimeCompl hn
  let y : 𝓞 R' := F.finiteLogTermNumerator n x hx
  let s : F.Q.primeCompl := d * c
  have hspec : ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x ^ n := by
    simpa [m, d, y] using F.finiteLogTermNumerator_mul_spec hn hx
  have hn_decomp_nat : ℓ ^ m * ordCompl[ℓ] n = n := by
    simpa [m] using Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hn_cast :
      ((n : ℕ) : 𝓞 R') = ((ℓ : 𝓞 R') ^ m) * (c : 𝓞 R') := by
    rw [← hn_decomp_nat]
    simp [m, c, ordComplPrimeCompl, Nat.cast_mul, Nat.cast_pow]
  rw [finiteLogTermCore, dif_neg hn]
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N
          (F.finiteLogTermNumerator n x hx)
          (F.finiteLogTermDenom n x hx * F.ordComplPrimeCompl hn)
        =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
          (Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
            F.quotientFractionEvalPrimeCompl N y s) := by
        simp [hn_cast, y, s, d, c, mul_comm, mul_left_comm]
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
          F.quotientFractionEvalPrimeCompl N y s) := by
        ring
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N
          (((ℓ : 𝓞 R') ^ m) * y) s := by
        rw [F.quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl]
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N
          ((d : 𝓞 R') * x ^ n) s := by
        rw [hspec]
    _ =
      F.quotientFractionEvalPrimeCompl N
        ((c : 𝓞 R') * ((d : 𝓞 R') * x ^ n)) s := by
        rw [← F.quotientFractionEvalPrimeCompl_one
          N (c : 𝓞 R')]
        rw [← F.quotientFractionEvalPrimeCompl_mul]
        simp [s]
    _ =
      F.quotientFractionEvalPrimeCompl N
        ((s : 𝓞 R') * x ^ n) s := by
        congr 1
        simp [s, d, c, mul_assoc, mul_comm]
    _ = Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ n) :=
        F.quotientFractionEvalPrimeCompl_den_mul_eq_mk N (x ^ n) s

/-- Signed denominator bridge for the finite-log term:
`n * ((-1)^(n+1) x^n/n) = (-1)^(n+1) x^n` in the quotient. -/
theorem finiteLogTerm_natCast_mul_eq_mk {N n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
        F.finiteLogTerm N n x hx =
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ n) := by
  rw [finiteLogTerm]
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
        (((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          F.finiteLogTermCore N n x hx)
        =
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
          F.finiteLogTermCore N n x hx) := by
        ring
    _ =
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ n) := by
        rw [F.finiteLogTermCore_natCast_mul_eq_mk hn hx]

/-- The chosen unsigned finite-log representative at the zero argument is zero. -/
theorem finiteLogTermCore_arg_zero (N n : ℕ) (h0 : (0 : 𝓞 R') ∈ F.Q) :
    F.finiteLogTermCore N n 0 h0 = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hell_ne : ((ℓ : 𝓞 R') ^ n.factorization ℓ) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
  have hnum : F.finiteLogTermNumerator n 0 h0 = 0 := by
    have hspec := F.finiteLogTermNumerator_mul_spec hn h0
    have hmul :
        ((ℓ : 𝓞 R') ^ n.factorization ℓ) *
            F.finiteLogTermNumerator n 0 h0 = 0 := by
      simpa [hn] using hspec
    exact (mul_eq_zero.mp hmul).resolve_left hell_ne
  rw [finiteLogTermCore, dif_neg hn, hnum]
  exact F.quotientFractionEvalPrimeCompl_eq_zero_of_mem
    N (F.finiteLogTermDenom n 0 h0 * F.ordComplPrimeCompl hn) (by simp)

/-- The signed finite-log term at the zero argument is zero. -/
theorem finiteLogTerm_arg_zero (N n : ℕ) (h0 : (0 : 𝓞 R') ∈ F.Q) :
    F.finiteLogTerm N n 0 h0 = 0 := by
  simp [finiteLogTerm, F.finiteLogTermCore_arg_zero N n h0]

/-- The finite logarithm at the zero argument is zero. -/
theorem finiteLog_arg_zero (N : ℕ) (h0 : (0 : 𝓞 R') ∈ F.Q) :
    F.finiteLog N 0 h0 = 0 := by
  classical
  simp [finiteLog, F.finiteLogTerm_arg_zero]

/-- If the principal-unit coordinate is already zero modulo `Q^(N+1)`, its
finite logarithm vanishes. -/
theorem finiteLog_eq_zero_of_mem_Q_pow_succ {N : ℕ}
    {x : 𝓞 R'} (hx : x ∈ F.Q) (hxN : x ∈ F.Q ^ (N + 1)) :
    F.finiteLog N x hx = 0 := by
  have h0 : (0 : 𝓞 R') ∈ F.Q := by simp
  have hsub : x - 0 ∈ F.Q ^ (N + 1) := by simpa using hxN
  calc
    F.finiteLog N x hx = F.finiteLog N 0 h0 :=
      F.finiteLog_eq_of_sub_mem hx h0 hsub
    _ = 0 := F.finiteLog_arg_zero N h0

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular
