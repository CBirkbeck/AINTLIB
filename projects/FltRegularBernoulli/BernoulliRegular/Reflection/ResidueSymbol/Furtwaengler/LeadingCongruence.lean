module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge

/-!
# Binomial leading congruence for integral Stickelberger Gauss sums

This file proves the formal congruence step used by the trace-form
Stickelberger calculation.  Since `ζ_ℓ = 1 + π` in `𝓞 R'` and `π ∈ Q`,
the integral Gauss sum is congruent modulo `Q^(s+1)` to its binomial
expansion truncated at degree `s`.

The remaining trace/multinomial calculation identifies the first non-zero
coefficient of this truncated expression.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Binomial truncation modulo an ideal power.

If `π ∈ I`, then `(1 + π)^m` is congruent modulo `I^(s+1)` to the binomial
sum truncated at degree `s`. -/
theorem one_add_pow_sub_choose_sum_mem_pow
    {A : Type*} [CommRing A] {I : Ideal A} {π : A} (hπ : π ∈ I) (m s : ℕ) :
    (1 + π) ^ m -
        ∑ n ∈ Finset.range (s + 1), π ^ n * (Nat.choose m n : A) ∈
      I ^ (s + 1) := by
  classical
  let term : ℕ → A := fun n => π ^ n * (Nat.choose m n : A)
  have hfull : (1 + π) ^ m = ∑ n ∈ Finset.range (m + 1), term n := by
    rw [show (1 + π : A) = π + 1 by ring, add_pow]
    simp [term]
  by_cases hms : m ≤ s
  · have hsubset : Finset.range (m + 1) ⊆ Finset.range (s + 1) := by
      intro n hn
      rw [Finset.mem_range] at hn ⊢
      omega
    have hsum :
        ∑ n ∈ Finset.range (m + 1), term n =
          ∑ n ∈ Finset.range (s + 1), term n := by
      refine Finset.sum_subset hsubset ?_
      intro n hn hn_small
      rw [Finset.mem_range] at hn
      rw [Finset.mem_range] at hn_small
      have hm_lt_n : m < n := by omega
      simp [term, Nat.choose_eq_zero_of_lt hm_lt_n]
    rw [hfull, hsum]
    simp [term]
  · push Not at hms
    have hsle : s + 1 ≤ m + 1 := by omega
    have hsplit := Finset.sum_range_add_sum_Ico term hsle
    rw [hfull, ← hsplit]
    have htail :
        ∑ n ∈ Finset.Ico (s + 1) (m + 1), term n ∈ I ^ (s + 1) := by
      refine Ideal.sum_mem _ fun n hn => ?_
      have hn_ge : s + 1 ≤ n := (Finset.mem_Ico.mp hn).1
      have hpow : π ^ n ∈ I ^ (s + 1) :=
        Ideal.pow_le_pow_right hn_ge (Ideal.pow_mem_pow hπ n)
      change term n ∈ I ^ (s + 1)
      change π ^ n * (Nat.choose m n : A) ∈ I ^ (s + 1)
      exact Ideal.mul_mem_right _ _ hpow
    simpa [term, add_comm, add_left_comm, add_assoc] using htail

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- The degree-`n` binomial coefficient sum appearing in the `π`-expansion of
`g(χ_q^a, ψ)`. -/
noncomputable def binomialCoeffSum (a n : ℕ) : 𝓞 R' :=
  ∑ x : k, (S.residueCharInt ^ a) x * (Nat.choose (S.psiExponent x) n : 𝓞 R')

/-- The binomial approximation to the integral Gauss sum through degree `s`,
written in coefficient form. -/
noncomputable def binomialCoeffApprox (a s : ℕ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (s + 1), S.binomialCoeffSum a n * S.π ^ n

/-- The same approximation, kept in pointwise form before interchanging the
two finite sums. -/
noncomputable def binomialPointwiseApprox (a s : ℕ) : 𝓞 R' :=
  ∑ x : k, (S.residueCharInt ^ a) x *
    ∑ n ∈ Finset.range (s + 1),
      S.π ^ n * (Nat.choose (S.psiExponent x) n : 𝓞 R')

/-- The pointwise and coefficient forms of the truncated binomial approximation
are equal. -/
theorem binomialPointwiseApprox_eq_coeffApprox (a s : ℕ) :
    S.binomialPointwiseApprox a s = S.binomialCoeffApprox a s := by
  classical
  unfold binomialPointwiseApprox binomialCoeffApprox binomialCoeffSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The integral Gauss sum is congruent modulo `Q^(s+1)` to its binomial
approximation through degree `s`. -/
theorem gaussSumInt_sub_binomialPointwiseApprox_mem_Q_pow (a s : ℕ) :
    S.gaussSumInt a - S.binomialPointwiseApprox a s ∈ S.Q ^ (s + 1) := by
  classical
  unfold gaussSumInt binomialPointwiseApprox
  change
    (∑ x : k, (S.residueCharInt ^ a) x * S.psiInt x) -
        ∑ x : k, (S.residueCharInt ^ a) x *
          (∑ n ∈ Finset.range (s + 1),
            S.π ^ n * (Nat.choose (S.psiExponent x) n : 𝓞 R')) ∈
      S.Q ^ (s + 1)
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun x _ => ?_
  have hzeta : S.zeta_ell_int = 1 + S.π := by
    rw [S.hπ]
    ring
  have htrunc := one_add_pow_sub_choose_sum_mem_pow (I := S.Q) S.π_mem_Q
    (S.psiExponent x) s
  change
    (S.residueCharInt ^ a) x * S.psiInt x -
        (S.residueCharInt ^ a) x *
          (∑ n ∈ Finset.range (s + 1),
            S.π ^ n * (Nat.choose (S.psiExponent x) n : 𝓞 R')) ∈
      S.Q ^ (s + 1)
  rw [← mul_sub]
  refine Ideal.mul_mem_left _ _ ?_
  change
    S.psiInt x -
        (∑ n ∈ Finset.range (s + 1),
          S.π ^ n * (Nat.choose (S.psiExponent x) n : 𝓞 R')) ∈
      S.Q ^ (s + 1)
  change
    S.zeta_ell_int ^ S.psiExponent x -
        (∑ n ∈ Finset.range (s + 1),
          S.π ^ n * (Nat.choose (S.psiExponent x) n : 𝓞 R')) ∈
      S.Q ^ (s + 1)
  rw [hzeta]
  exact htrunc

/-- Coefficient-form version of
`gaussSumInt_sub_binomialPointwiseApprox_mem_Q_pow`. -/
theorem gaussSumInt_sub_binomialCoeffApprox_mem_Q_pow (a s : ℕ) :
    S.gaussSumInt a - S.binomialCoeffApprox a s ∈ S.Q ^ (s + 1) := by
  rw [← S.binomialPointwiseApprox_eq_coeffApprox a s]
  exact S.gaussSumInt_sub_binomialPointwiseApprox_mem_Q_pow a s

/-- If the coefficient approximation has a proposed leading term modulo
`Q^(s+1)`, then the integral Gauss sum has the same leading congruence. -/
theorem gaussSumInt_sub_lead_mem_Q_pow_of_binomialCoeffApprox
    (a s : ℕ) {lead : 𝓞 R'}
    (hlead : S.binomialCoeffApprox a s - lead ∈ S.Q ^ (s + 1)) :
    S.gaussSumInt a - lead ∈ S.Q ^ (s + 1) := by
  have happrox := S.gaussSumInt_sub_binomialCoeffApprox_mem_Q_pow a s
  rw [show S.gaussSumInt a - lead =
      (S.gaussSumInt a - S.binomialCoeffApprox a s) +
        (S.binomialCoeffApprox a s - lead) by ring]
  exact (S.Q ^ (s + 1)).add_mem happrox hlead

/-- Exact-order consequence of a leading-term evaluation of the binomial
coefficient approximation. -/
theorem gaussSumInt_qadic_ord_at_prime_of_binomialCoeffApprox
    (a : ℕ) {lead : 𝓞 R'}
    (h_lead_mem :
      lead ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)))
    (h_lead_not_mem_succ :
      lead ∉ S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1))
    (h_approx :
      S.binomialCoeffApprox a (digitSum ℓ (a * ((Fintype.card k - 1) / p))) - lead ∈
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1)) :
    S.gaussSumInt a ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      S.gaussSumInt a ∉
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1) :=
  S.gaussSumInt_qadic_ord_at_prime_of_leading_congruence a
    h_lead_mem h_lead_not_mem_succ
    (S.gaussSumInt_sub_lead_mem_Q_pow_of_binomialCoeffApprox
      a (digitSum ℓ (a * ((Fintype.card k - 1) / p))) h_approx)

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
