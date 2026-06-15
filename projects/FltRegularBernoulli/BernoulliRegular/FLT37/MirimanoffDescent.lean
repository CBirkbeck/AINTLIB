module

public import BernoulliRegular.FLT37.CaseI

/-!
# Mirimanoff descent algebra (F37-A2/A3)

This file isolates the algebraic interface between the per-index
`(ζ - 1)^2` coefficients `w_k` produced in `CaseI.lean` and the
Mirimanoff polynomial identities from `Mirimanoff.lean`.

The genuine F37-A2 descent still has to construct the proportionality
data from Galois action and Stickelberger. Once that data is available,
the lemmas here turn it into the weighted finite sum recognised as
`φ_3(t)`, the algebraic bridge used by F37-A3 and the `ℓ = 37`
specialisation in F37-A4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

/-- Cross-index linearity for a family of `w_k` values, in the
cross-multiplied form expected from the `(ζ - 1)^2` Taylor coefficient
relations. -/
def WIntCrossLinearData (p : ℕ) (w : ℕ → ZMod p) : Prop :=
  ∀ ⦃k₁ k₂ : ℕ⦄, k₁ ∈ Finset.Ico 1 p → k₂ ∈ Finset.Ico 1 p →
    ((k₂ : ZMod p) ^ 2) * w k₁ = ((k₁ : ZMod p) ^ 2) * w k₂

/-- Stronger descent data: the `w_k` are all proportional to `k^2`
with a single constant `C`. This is the algebraic shape supplied by the
classical Galois-descent/Stickelberger argument. -/
def WIntDescentData (p : ℕ) (w : ℕ → ZMod p) (C : ZMod p) : Prop :=
  ∀ ⦃k : ℕ⦄, k ∈ Finset.Ico 1 p → w k = C * (k : ZMod p) ^ 2

/-- Proportional `w_k` data imply the expected cross-index linearity. -/
theorem WIntDescentData.crossLinear {p : ℕ} {w : ℕ → ZMod p} {C : ZMod p}
    (h : WIntDescentData p w C) : WIntCrossLinearData p w := by
  intro k₁ k₂ hk₁ hk₂
  rw [h hk₁, h hk₂]
  ring

/-- Integer divisibility form of the per-index relation, transported to
`ZMod p`. This is the local bridge from `CaseI.lean`'s integer
congruences to the finite-field algebra used in the descent sums. -/
theorem wInt_relation_zmod_of_int_dvd {p : ℕ} {a b w_int : ℤ} {k : ℕ}
    (h : (p : ℤ) ∣ 2 * w_int * (a + b) - (k : ℤ) ^ 2 * a * b) :
    (2 : ZMod p) * (w_int : ZMod p) * ((a + b : ℤ) : ZMod p) =
      ((k : ZMod p) ^ 2) * (a : ZMod p) * (b : ZMod p) := by
  have hzero :
      ((2 * w_int * (a + b) - (k : ℤ) ^ 2 * a * b : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  rw [Int.cast_sub, sub_eq_zero] at hzero
  simpa [Int.cast_pow] using hzero

/-- If the `w_k` are proportional to `k^2`, their weighted generating
sum is `C` times the third Mirimanoff polynomial. -/
theorem WIntDescentData.sum_eq_const_mul_mirimanoffPolynomial_three
    {p : ℕ} [Fact p.Prime] {w : ℕ → ZMod p} {C t : ZMod p}
    (h : WIntDescentData p w C) :
    (∑ k ∈ Finset.Ico 1 p, w k * t ^ k) =
      C * (mirimanoffPolynomial p 3).eval t := by
  calc
    (∑ k ∈ Finset.Ico 1 p, w k * t ^ k)
        = ∑ k ∈ Finset.Ico 1 p, (C * (k : ZMod p) ^ 2) * t ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [h hk]
    _ = C * ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 * t ^ k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = C * (mirimanoffPolynomial p 3).eval t := by
          congr 1
          simp [mirimanoffPolynomial, Polynomial.eval_finsetSum]

/-- Vanishing form of the weighted-sum bridge. -/
theorem WIntDescentData.sum_eq_zero_of_phi_three_eq_zero
    {p : ℕ} [Fact p.Prime] {w : ℕ → ZMod p} {C t : ZMod p}
    (h : WIntDescentData p w C)
    (hφ : (mirimanoffPolynomial p 3).eval t = 0) :
    (∑ k ∈ Finset.Ico 1 p, w k * t ^ k) = 0 := by
  rw [h.sum_eq_const_mul_mirimanoffPolynomial_three, hφ, mul_zero]

/-- Re-export of the regular-case per-index cross-linearity theorem under
the F37-A2 naming. -/
theorem caseI_wInt_cross_linearity_of_regular
    {p : ℕ} [hp : Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < p) (hk₂ : k₂ < p) :
    ∃ w_int_k₁ w_int_k₂ : ℤ,
      (p : ℤ) ∣ (2 * w_int_k₁ * (a + b) - (k₁ : ℤ)^2 * a * b) ∧
      (p : ℤ) ∣ (2 * w_int_k₂ * (a + b) - (k₂ : ℤ)^2 * a * b) ∧
      (p : ℤ) ∣ ((k₂ : ℤ)^2 * w_int_k₁ - (k₁ : ℤ)^2 * w_int_k₂) :=
  fltCaseI_w_int_cross_linearity_of_regular (K := K)
    hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk₁ hk₂

end FLT37

end BernoulliRegular
