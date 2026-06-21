module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceBinomial
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceMultinomial
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Trace coefficient expansions (REF-18c2c4-L2c3d2)

This file packages the coefficient-expansion API needed after the
reciprocal-convention correction.  The raw combinatorics in
`TraceMultinomial.lean` expands `(traceSum x)^n`; here we record the
weighted exponent contributed by a multi-index, specialise the trace
formula to a `TraceFormStickelbergerSetup`, and expose a factorial-cleared
form of the reciprocal trace-binomial coefficient sums.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Weighted exponent contributed by a trace multi-index `ks`.

For `traceSum ℓ f x = ∑_{i < f} x^(ℓ^i)`, the multi-index `ks` contributes
the monomial exponent `∑_{i < f} ks i * ℓ^i`. -/
def traceMultiIndexExponent (ℓ f : ℕ) (ks : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range f, ks i * ℓ ^ i

variable {R : Type*} [CommSemiring R]

/-- Multinomial expansion of a scaled trace sum.

This is the form used for trace-form additive characters, where the trace
is evaluated at `c * x`. -/
theorem traceSum_mul_pow_eq_sum_multinomial
    (ℓ f : ℕ) (c x : R) (n : ℕ) :
    (traceSum ℓ f (c * x)) ^ n =
      ∑ ks ∈ Finset.piAntidiag (Finset.range f) n,
        (Nat.multinomial (Finset.range f) ks : R) *
          c ^ traceMultiIndexExponent ℓ f ks *
          x ^ traceMultiIndexExponent ℓ f ks := by
  rw [traceSum_pow_eq_sum_multinomial']
  refine Finset.sum_congr rfl fun ks _ => ?_
  simp only [traceMultiIndexExponent, mul_pow]
  ring

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The `ZMod ℓ`-dimension of the residue field is the setup parameter `f`.

This lets the standard finite-field trace formula use the same `S.f` that
appears in the Stickelberger digit-sum notation. -/
theorem trace_finrank_eq_f : Module.finrank (ZMod ℓ) k = S.f := by
  have hpow : ℓ ^ Module.finrank (ZMod ℓ) k = ℓ ^ S.f := by
    rw [FiniteField.pow_finrank_eq_card, S.card_k]
  exact Nat.pow_right_injective (Fact.out : Nat.Prime ℓ).one_lt hpow

/-- Setup-specialised bridge from the algebraic trace to `traceSum`. -/
theorem algebraMap_trace_pow_eq_traceSum_pow_setup (x : k) (n : ℕ) :
    algebraMap (ZMod ℓ) k (Algebra.trace (ZMod ℓ) k x) ^ n =
      (traceSum ℓ S.f x) ^ n :=
  algebraMap_trace_pow_eq_traceSum_pow
    (K := ZMod ℓ) (L := k) (ℓ := ℓ) (f := S.f)
    (Nat.card_zmod ℓ) S.trace_finrank_eq_f x n

/-- Multinomial expansion of the `n`-th power of the scaled algebraic trace
appearing in the trace-form additive character. -/
theorem algebraMap_scaled_trace_pow_eq_sum_multinomial
    (x : k) (n : ℕ) :
    algebraMap (ZMod ℓ) k
        (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)) ^ n =
      ∑ ks ∈ Finset.piAntidiag (Finset.range S.f) n,
        (Nat.multinomial (Finset.range S.f) ks : k) *
          (S.traceScale : k) ^ traceMultiIndexExponent ℓ S.f ks *
          x ^ traceMultiIndexExponent ℓ S.f ks := by
  rw [S.algebraMap_trace_pow_eq_traceSum_pow_setup ((S.traceScale : k) * x) n]
  exact traceSum_mul_pow_eq_sum_multinomial ℓ S.f (S.traceScale : k) x n

section UnitSums

variable [DecidableEq k]

/-- Unit-sum form of the scaled trace-power expansion.  After interchanging
finite sums, each multi-index has an explicit natural coefficient, trace
scale power, and monomial exponent. -/
theorem unitSum_scaled_trace_pow_eq_sum_multinomial
    (A n : ℕ) :
    (∑ x : kˣ,
        (x : k) ^ A *
          algebraMap (ZMod ℓ) k
            (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * (x : k))) ^ n) =
      ∑ ks ∈ Finset.piAntidiag (Finset.range S.f) n,
        ((Nat.multinomial (Finset.range S.f) ks : k) *
          (S.traceScale : k) ^ traceMultiIndexExponent ℓ S.f ks) *
          ∑ x : kˣ, (x : k) ^ (A + traceMultiIndexExponent ℓ S.f ks) := by
  calc
    (∑ x : kˣ,
        (x : k) ^ A *
          algebraMap (ZMod ℓ) k
            (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * (x : k))) ^ n)
        =
      ∑ x : kˣ,
        (x : k) ^ A *
          (∑ ks ∈ Finset.piAntidiag (Finset.range S.f) n,
            (Nat.multinomial (Finset.range S.f) ks : k) *
              (S.traceScale : k) ^ traceMultiIndexExponent ℓ S.f ks *
              (x : k) ^ traceMultiIndexExponent ℓ S.f ks) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [S.algebraMap_scaled_trace_pow_eq_sum_multinomial (x : k) n]
    _ =
      ∑ x : kˣ, ∑ ks ∈ Finset.piAntidiag (Finset.range S.f) n,
        (x : k) ^ A *
          ((Nat.multinomial (Finset.range S.f) ks : k) *
            (S.traceScale : k) ^ traceMultiIndexExponent ℓ S.f ks *
            (x : k) ^ traceMultiIndexExponent ℓ S.f ks) := by
        simp_rw [Finset.mul_sum]
    _ =
      ∑ ks ∈ Finset.piAntidiag (Finset.range S.f) n, ∑ x : kˣ,
        (x : k) ^ A *
          ((Nat.multinomial (Finset.range S.f) ks : k) *
            (S.traceScale : k) ^ traceMultiIndexExponent ℓ S.f ks *
            (x : k) ^ traceMultiIndexExponent ℓ S.f ks) := by
        rw [Finset.sum_comm]
    _ =
      ∑ ks ∈ Finset.piAntidiag (Finset.range S.f) n,
        ((Nat.multinomial (Finset.range S.f) ks : k) *
          (S.traceScale : k) ^ traceMultiIndexExponent ℓ S.f ks) *
          ∑ x : kˣ, (x : k) ^ (A + traceMultiIndexExponent ℓ S.f ks) := by
        refine Finset.sum_congr rfl fun ks _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [pow_add]
        ring

end UnitSums

/-- Factorial-cleared form of the reciprocal trace-binomial coefficient sum.

This replaces `Nat.choose` by the descending factorial, which is the
integer-polynomial expression used by later coefficient-valuation
arguments. -/
theorem traceCharacterChooseSumRec_mul_factorial_eq_descFactorialSum
    (a n : ℕ) :
    S.traceCharacterChooseSumRec a n * (Nat.factorial n : 𝓞 R') =
      ∑ x : k, (S.residueCharInt ^ (p - a)) x *
        (Nat.descFactorial
          (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val n : 𝓞 R') := by
  unfold traceCharacterChooseSumRec traceCharacterChooseSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc]
  congr 1
  rw [← Nat.cast_mul]
  congr 1
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
