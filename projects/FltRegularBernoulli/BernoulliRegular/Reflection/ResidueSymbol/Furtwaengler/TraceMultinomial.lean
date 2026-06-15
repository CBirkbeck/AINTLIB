module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Multinomial expansion of `traceSum^n` (Layer 1, REF-18c2c4)

For a finite field `k = 𝔽_{ℓ ^ f}` of characteristic `ℓ`, define

  `traceSum x := x + x^ℓ + x^{ℓ²} + ... + x^{ℓ^{f-1}}`.

This equals `algebraMap 𝔽_ℓ k (Algebra.trace 𝔽_ℓ k x)` by the standard
finite-field trace formula (`FiniteField.algebraMap_trace_eq_sum_pow`).

The multinomial expansion of `(traceSum x)^n` over a commutative
semiring `R` (with `x ∈ R`) gives

  `(traceSum x)^n = ∑_{(k₀,...,k_{f-1}) : Σk_i = n} multinomial · x^{Σk_i·ℓ^i}`.

This is **Layer 1** combinatorics for the digit-sum Stickelberger
congruence: the exponent vector `(k₀,...,k_{f-1})` becomes the
multi-index, and the weighted sum `Σ k_i ℓ^i` is exactly the integer
that the multinomial expansion contributes to the `x^a` coefficient.

The minimal-weight argument (next file) will show that the smallest
`n` for which the coefficient at `x^a` is non-zero equals
`digitSum ℓ a`.
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler

variable {R : Type*} [CommSemiring R]

/-- The integer-formula trace sum `Σ_{i=0}^{f-1} x^{ℓ^i}` in any
commutative semiring. For `R = k = 𝔽_{ℓ ^ f}` this equals
`algebraMap 𝔽_ℓ k (Algebra.trace 𝔽_ℓ k x)`. -/
def traceSum (ℓ f : ℕ) (x : R) : R :=
  ∑ i ∈ Finset.range f, x ^ (ℓ ^ i)

@[simp] theorem traceSum_zero_arg (ℓ : ℕ) (x : R) : traceSum ℓ 0 x = 0 := by
  simp [traceSum]

theorem traceSum_succ (ℓ f : ℕ) (x : R) :
    traceSum ℓ (f + 1) x = traceSum ℓ f x + x ^ (ℓ ^ f) := by
  simp [traceSum, Finset.sum_range_succ]

/-- **Multinomial expansion of `(traceSum x)^n`.** For any commutative
semiring `R` and `x ∈ R`:

`(traceSum ℓ f x)^n = ∑_{ks ∈ piAntidiag (range f) n} multinomial · ∏ x^{ℓ^i · k_i}`.

Specialisation of mathlib's `Finset.sum_pow_eq_sum_piAntidiag`. -/
theorem traceSum_pow_eq_sum_multinomial (ℓ f : ℕ) (x : R) (n : ℕ) :
    (traceSum ℓ f x) ^ n =
      ∑ k ∈ Finset.piAntidiag (Finset.range f) n,
        Nat.multinomial (Finset.range f) k *
          ∏ i ∈ Finset.range f, (x ^ (ℓ ^ i)) ^ k i := by
  unfold traceSum
  exact Finset.sum_pow_eq_sum_piAntidiag (Finset.range f) (fun i => x ^ (ℓ ^ i)) n

/-- **Multinomial expansion of `(traceSum x)^n`, simplified power form.**
The product `∏ (x^{ℓ^i})^{k_i}` collapses to `x^{Σ k_i · ℓ^i}`. -/
theorem traceSum_pow_eq_sum_multinomial' (ℓ f : ℕ) (x : R) (n : ℕ) :
    (traceSum ℓ f x) ^ n =
      ∑ k ∈ Finset.piAntidiag (Finset.range f) n,
        Nat.multinomial (Finset.range f) k *
          x ^ (∑ i ∈ Finset.range f, k i * ℓ ^ i) := by
  rw [traceSum_pow_eq_sum_multinomial]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm]

/-- **Trace-power expansion is the algebraMap of `(Algebra.trace x)^n`.**
Bridge between the integer formula `traceSum` and the genuine algebraic
trace. For `K = 𝔽_ℓ` and `L = k = 𝔽_{ℓ ^ f}` with `Nat.card K = ℓ`:

`algebraMap K L (Algebra.trace K L x ^ n) = (traceSum ℓ f x) ^ n`. -/
theorem algebraMap_trace_pow_eq_traceSum_pow
    {K L : Type*} [Field K] [Field L] [Finite L] [Algebra K L]
    {ℓ f : ℕ} (h_card_K : Nat.card K = ℓ) (h_finrank : Module.finrank K L = f)
    (x : L) (n : ℕ) :
    algebraMap K L (Algebra.trace K L x) ^ n = (traceSum ℓ f x) ^ n := by
  congr 1
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  unfold traceSum
  rw [h_finrank]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_card_K]

end Furtwaengler

end BernoulliRegular
