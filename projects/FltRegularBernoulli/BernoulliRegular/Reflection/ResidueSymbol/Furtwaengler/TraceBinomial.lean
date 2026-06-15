module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingCongruence
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup

/-!
# Trace-form binomial truncation (REF-18c2c4-L2c2)

Specialises the binomial-truncation layer of `LeadingCongruence.lean` to
the trace-form additive character carried by a
`TraceFormStickelbergerSetup`. The bundle's `psiExponent` agrees with the
canonical trace `(Algebra.trace (ZMod ℓ) k (traceScale · x)).val` (via
`psiExponent_trace`), so all binomial-truncation theorems for
`ConcreteStickelbergerSetup` immediately specialise.

The remaining mathematical work — multinomial reduction, character
orthogonality, minimal-weight uniqueness — lives in REF-18c2c4-L2c3.

## Main definitions

* `TraceFormStickelbergerSetup.traceCharacterChooseSum`: the residual
  character sum `T_n(a) = ∑ x : k, χ_q^a(x) · C((Tr(c·x)).val, n)`.
* `TraceFormStickelbergerSetup.traceBinomialApprox`: the truncated
  binomial expansion `∑_{n ≤ s} π^n · T_n(a)`.
* `TraceFormStickelbergerSetup.gaussSumIntRec`: the reciprocal-convention
  Gauss sum, implemented with the ordinary character by reindexing
  `a ↦ p - a`.

## Main theorems

* `gaussSumInt_sub_traceBinomialApprox_mem_Q_pow`:
  `gaussSumInt a − traceBinomialApprox a s ∈ Q^(s+1)`.
* `gaussSumInt_qadic_ord_at_prime_of_traceLead`: exact-order transfer
  theorem in trace form, ready for L2c3 leading-term consumption.
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

/-- The residual character sum at degree `n` in the trace-form binomial
expansion: `T_n(a) = ∑ x : k, χ_q^a(x) · C((Tr_{k/𝔽_ℓ}(traceScale · x)).val, n)`.

This is the coefficient of `π^n` in the binomial expansion of the integral
Gauss sum, before any combinatorial reduction. -/
noncomputable def traceCharacterChooseSum (a n : ℕ) : 𝓞 R' :=
  ∑ x : k, (S.residueCharInt ^ a) x *
    (Nat.choose (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val n : 𝓞 R')

/-- Reciprocal-convention residual character sum. The underlying character
stored in the setup is ordinary (`χ(x) ≡ x^d mod Q`), so the reciprocal
power `χ^{-a}` is represented in the Stickelberger range by `χ^(p-a)`. -/
noncomputable def traceCharacterChooseSumRec (a n : ℕ) : 𝓞 R' :=
  S.traceCharacterChooseSum (p - a) n

/-- The trace-form binomial approximation of the integral Gauss sum
through `π`-degree `s`:
`∑_{n ≤ s} π^n · T_n(a)`. -/
noncomputable def traceBinomialApprox (a s : ℕ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (s + 1), S.traceCharacterChooseSum a n * S.π ^ n

/-- Reciprocal-convention trace-form binomial approximation. -/
noncomputable def traceBinomialApproxRec (a s : ℕ) : 𝓞 R' :=
  S.traceBinomialApprox (p - a) s

/-- Reciprocal-convention integral Gauss sum, implemented by reindexing the
ordinary character power. -/
noncomputable def gaussSumIntRec (a : ℕ) : 𝓞 R' :=
  S.gaussSumInt (p - a)

/-- The bundle's `binomialCoeffSum` agrees with `traceCharacterChooseSum`. -/
theorem binomialCoeffSum_eq_traceCharacterChooseSum (a n : ℕ) :
    S.toConcreteStickelbergerSetup.binomialCoeffSum a n =
      S.traceCharacterChooseSum a n := by
  unfold ConcreteStickelbergerSetup.binomialCoeffSum traceCharacterChooseSum
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [S.psiExponent_trace]

/-- The bundle's `binomialCoeffApprox` agrees with `traceBinomialApprox`. -/
theorem binomialCoeffApprox_eq_traceBinomialApprox (a s : ℕ) :
    S.toConcreteStickelbergerSetup.binomialCoeffApprox a s =
      S.traceBinomialApprox a s := by
  unfold ConcreteStickelbergerSetup.binomialCoeffApprox traceBinomialApprox
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [S.binomialCoeffSum_eq_traceCharacterChooseSum]

/-- The reciprocal approximation is the ordinary approximation at index
`p-a`. -/
theorem traceBinomialApproxRec_eq (a s : ℕ) :
    S.traceBinomialApproxRec a s = S.traceBinomialApprox (p - a) s := rfl

/-- The integral Gauss sum is congruent modulo `Q^(s+1)` to its
trace-form binomial approximation through `π`-degree `s`. -/
theorem gaussSumInt_sub_traceBinomialApprox_mem_Q_pow (a s : ℕ) :
    S.gaussSumInt a - S.traceBinomialApprox a s ∈ S.Q ^ (s + 1) := by
  rw [← S.binomialCoeffApprox_eq_traceBinomialApprox]
  exact S.toConcreteStickelbergerSetup.gaussSumInt_sub_binomialCoeffApprox_mem_Q_pow a s

/-- Reciprocal-convention version of the trace-form binomial truncation. -/
theorem gaussSumIntRec_sub_traceBinomialApproxRec_mem_Q_pow (a s : ℕ) :
    S.gaussSumIntRec a - S.traceBinomialApproxRec a s ∈ S.Q ^ (s + 1) :=
  S.gaussSumInt_sub_traceBinomialApprox_mem_Q_pow (p - a) s

/-- Exact-order consequence of a leading-term evaluation of the
trace-form binomial approximation. This is the trace-form analogue of
`gaussSumInt_qadic_ord_at_prime_of_binomialCoeffApprox` and is the
interface consumed by L2c3. -/
theorem gaussSumInt_qadic_ord_at_prime_of_traceLead
    (a : ℕ) {lead : 𝓞 R'}
    (h_lead_mem :
      lead ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)))
    (h_lead_not_mem_succ :
      lead ∉ S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1))
    (h_approx :
      S.traceBinomialApprox a (digitSum ℓ (a * ((Fintype.card k - 1) / p))) - lead ∈
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1)) :
    S.gaussSumInt a ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      S.gaussSumInt a ∉
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1) := by
  apply S.toConcreteStickelbergerSetup.gaussSumInt_qadic_ord_at_prime_of_binomialCoeffApprox a
    h_lead_mem h_lead_not_mem_succ
  rw [S.binomialCoeffApprox_eq_traceBinomialApprox]
  exact h_approx

/-- Reciprocal-convention exact-order consequence of a leading-term
evaluation. This is the convention-correct interface for the digit-sum
target `s_ℓ(a*d)`. -/
theorem gaussSumIntRec_qadic_ord_at_prime_of_traceLead
    (a : ℕ) {lead : 𝓞 R'}
    (h_lead_mem :
      lead ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)))
    (h_lead_not_mem_succ :
      lead ∉ S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1))
    (h_approx :
      S.traceBinomialApproxRec a (digitSum ℓ (a * ((Fintype.card k - 1) / p))) -
          lead ∈
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1)) :
    S.gaussSumIntRec a ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      S.gaussSumIntRec a ∉
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1) :=
  exact_mem_pow_of_sub_mem_succ h_lead_mem h_lead_not_mem_succ
    (by
      have htrunc := S.gaussSumIntRec_sub_traceBinomialApproxRec_mem_Q_pow a
        (digitSum ℓ (a * ((Fintype.card k - 1) / p)))
      rw [show S.gaussSumIntRec a - lead =
          (S.gaussSumIntRec a -
              S.traceBinomialApproxRec a
                (digitSum ℓ (a * ((Fintype.card k - 1) / p)))) +
            (S.traceBinomialApproxRec a
                (digitSum ℓ (a * ((Fintype.card k - 1) / p))) - lead) by ring]
      exact (S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1)).add_mem
        htrunc h_approx)

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
