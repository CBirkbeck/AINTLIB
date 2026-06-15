module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientExpansion
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MultinomialMod
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Trace coefficient valuation reductions (REF-18c2c4-L2c3d3)

The full L2c3d3 coefficient estimate is

`traceCharacterChooseSumRec a n ∈ Q^(s-n)`.

This file proves the no-sorry valuation reductions that isolate the remaining
core estimate:

* if `n ≥ ℓ`, the coefficient is exactly zero because every trace value has
  representative `< ℓ`;
* if `n < ℓ`, then `n!` is a `Q`-unit, so membership of the factorial-cleared
  coefficient in any `Q`-power implies membership of the original coefficient
  in the same power.

The remaining middle range is therefore the factorial-cleared Gauss-period
estimate.  After L2c3d2, this can be stated concretely as a valuation for
the desc-factorial trace sums.  The required strengthening is a genuine
Teichmuller-lift congruence; first-order finite-field orthogonality only
detects membership in `Q`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The reciprocal degree-zero trace coefficient vanishes in the
Stickelberger range. -/
theorem traceCharacterChooseSumRec_zero_eq_zero
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.traceCharacterChooseSumRec a 0 = 0 := by
  unfold traceCharacterChooseSumRec traceCharacterChooseSum
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one
    (S.residueCharInt_pow_ne_one (a := p - a) (by omega) (by omega))

/-- The reciprocal degree-zero trace coefficient lies in every `Q`-power. -/
theorem traceCharacterChooseSumRec_zero_mem_Q_pow
    (a r : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.traceCharacterChooseSumRec a 0 ∈ S.Q ^ r := by
  rw [S.traceCharacterChooseSumRec_zero_eq_zero a ha₁ ha₂]
  exact zero_mem _

/-- In the trace coefficient range `n < ℓ`, `n!` is not in the selected
prime `Q`. -/
theorem natCast_factorial_not_mem_Q_of_lt_ell {n : ℕ} (hn : n < ℓ) :
    (Nat.factorial n : 𝓞 R') ∉ S.Q := by
  classical
  intro hmem
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have hres :
      S.residueMap (Nat.factorial n : 𝓞 R') = 0 :=
    (S.toConcreteStickelbergerSetup.mem_Q_iff_residueMap_eq_zero
      (Nat.factorial n : 𝓞 R')).1 hmem
  rw [map_natCast] at hres
  have hnot_dvd : ¬ ℓ ∣ Nat.factorial n :=
    factorial_not_dvd_of_lt_prime hn
  exact hnot_dvd ((CharP.cast_eq_zero_iff k ℓ (Nat.factorial n)).1 hres)

/-- Cancel a factorial prime to `Q` from a `Q`-power membership. -/
theorem mem_Q_pow_of_mul_factorial_mem {x : 𝓞 R'} {n r : ℕ}
    (hn : n < ℓ) (hx : x * (Nat.factorial n : 𝓞 R') ∈ S.Q ^ r) :
    x ∈ S.Q ^ r := by
  have hunitQ := S.natCast_factorial_not_mem_Q_of_lt_ell hn
  rcases Ideal.IsPrime.mem_pow_mul S.Q hx with hxQ | hfacQ
  · exact hxQ
  · exact (hunitQ hfacQ).elim

/-- For `n ≥ ℓ`, the reciprocal trace-binomial coefficient is exactly zero:
all trace representatives lie in `[0, ℓ)`, so `choose trace.val n = 0`. -/
theorem traceCharacterChooseSumRec_eq_zero_of_ell_le
    (a n : ℕ) (hn : ℓ ≤ n) :
    S.traceCharacterChooseSumRec a n = 0 := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  unfold traceCharacterChooseSumRec traceCharacterChooseSum
  refine Finset.sum_eq_zero fun x _ => ?_
  have hval :
      (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val < n :=
    (ZMod.val_lt _).trans_le hn
  rw [Nat.choose_eq_zero_of_lt hval, Nat.cast_zero, mul_zero]

/-- The zero range of `traceCharacterChooseSumRec` lies in every `Q`-power. -/
theorem traceCharacterChooseSumRec_mem_Q_pow_of_ell_le
    (a n r : ℕ) (hn : ℓ ≤ n) :
    S.traceCharacterChooseSumRec a n ∈ S.Q ^ r := by
  rw [S.traceCharacterChooseSumRec_eq_zero_of_ell_le a n hn]
  exact zero_mem _

/-- Convert a factorial-cleared coefficient estimate into the original
coefficient estimate.  The `n ≥ ℓ` range is zero, and the `n < ℓ` range
cancels `n!` because it is a `Q`-unit. -/
theorem traceCharacterChooseSumRec_mem_Q_pow_of_mul_factorial_mem
    (a n r : ℕ)
    (hfac :
      S.traceCharacterChooseSumRec a n * (Nat.factorial n : 𝓞 R') ∈ S.Q ^ r) :
    S.traceCharacterChooseSumRec a n ∈ S.Q ^ r := by
  by_cases hn : n < ℓ
  · exact S.mem_Q_pow_of_mul_factorial_mem hn hfac
  · exact S.traceCharacterChooseSumRec_mem_Q_pow_of_ell_le a n r (Nat.le_of_not_gt hn)

/-- Assembly form for L2c3d3: it is enough to prove the factorial-cleared
estimate in the nonzero range `n < ℓ`. -/
theorem traceCharacterChooseSumRec_mem_Q_pow_sub_of_factorialCleared
    (a s : ℕ)
    (hfac :
      ∀ n, n ≤ s → n < ℓ →
        S.traceCharacterChooseSumRec a n * (Nat.factorial n : 𝓞 R') ∈ S.Q ^ (s - n)) :
    ∀ n, n ≤ s → S.traceCharacterChooseSumRec a n ∈ S.Q ^ (s - n) := by
  intro n hn_le
  by_cases hnℓ : n < ℓ
  · exact S.traceCharacterChooseSumRec_mem_Q_pow_of_mul_factorial_mem a n (s - n)
      (hfac n hn_le hnℓ)
  · exact S.traceCharacterChooseSumRec_mem_Q_pow_of_ell_le a n (s - n)
      (Nat.le_of_not_gt hnℓ)

/-- Stickelberger-range version of
`traceCharacterChooseSumRec_mem_Q_pow_sub_of_factorialCleared`: the
degree-zero coefficient is already zero, so the remaining core estimate is
only required for `0 < n < ℓ`. -/
theorem traceCharacterChooseSumRec_mem_Q_pow_sub_of_factorialCleared_middle
    (a s : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (hfac :
      ∀ n, n ≤ s → 0 < n → n < ℓ →
        S.traceCharacterChooseSumRec a n * (Nat.factorial n : 𝓞 R') ∈ S.Q ^ (s - n)) :
    ∀ n, n ≤ s → S.traceCharacterChooseSumRec a n ∈ S.Q ^ (s - n) := by
  intro n hn_le
  rcases n with _ | n
  · exact S.traceCharacterChooseSumRec_zero_mem_Q_pow a s ha₁ ha₂
  · exact S.traceCharacterChooseSumRec_mem_Q_pow_sub_of_factorialCleared a s
      (fun m hm_le hmℓ => by
        rcases m with _ | m
        · have hzero := S.traceCharacterChooseSumRec_zero_eq_zero a ha₁ ha₂
          rw [hzero, zero_mul]
          exact zero_mem _
        · exact hfac (m + 1) hm_le (Nat.succ_pos m) hmℓ)
      (n + 1) hn_le

/-- Concrete desc-factorial form of the remaining L2c3d3 middle-range
estimate.  This is the interface for the Teichmuller-lift/Gauss-period
congruence: after `traceCharacterChooseSumRec_mul_factorial_eq_descFactorialSum`,
the coefficientwise valuation is exactly a valuation of these finite sums. -/
theorem traceCharacterChooseSumRec_mem_Q_pow_sub_of_descFactorial_middle
    (a s : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (hdesc :
      ∀ n, n ≤ s → 0 < n → n < ℓ →
        (∑ x : k, (S.residueCharInt ^ (p - a)) x *
          (Nat.descFactorial
            (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val n : 𝓞 R')) ∈
            S.Q ^ (s - n)) :
    ∀ n, n ≤ s → S.traceCharacterChooseSumRec a n ∈ S.Q ^ (s - n) :=
  S.traceCharacterChooseSumRec_mem_Q_pow_sub_of_factorialCleared_middle
    a s ha₁ ha₂
    (fun n hn_le hn_pos hnℓ => by
      rw [S.traceCharacterChooseSumRec_mul_factorial_eq_descFactorialSum]
      exact hdesc n hn_le hn_pos hnℓ)

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
