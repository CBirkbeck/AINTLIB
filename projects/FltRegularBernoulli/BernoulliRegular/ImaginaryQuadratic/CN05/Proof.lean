/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.ImaginaryQuadratic.CN05.Two

/-!
# The CN-05 coefficient identity

This file proves the CN-05 coefficient identity for all natural numbers and deduces the
corresponding zeta-function identity for imaginary quadratic fields.
-/

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

section CN05_statement

variable (p : ℕ) [hp : Fact p.Prime]

/-- **CN-05 at odd q ≠ p unified**: LHS = RHS for any odd prime q ≠ p. -/
theorem CN05CoeffEq_at_prime_pow_odd_ne_p (hp3 : p % 4 = 3) (q : ℕ)
    [hq : Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  have hq_ne : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h_zero
    have hp_dvd : (p : ℕ) ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h_zero
    rcases (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_dvd with h
    exact hqp h.symm
  have h_or : legendreDirichletNat p q = 1 ∨ legendreDirichletNat p q = -1 := by
    change legendreDirichlet p ((q : ℕ) : ZMod p) = 1 ∨
      legendreDirichlet p ((q : ℕ) : ZMod p) = -1
    rw [legendreDirichlet_apply]
    rcases quadraticChar_dichotomy hq_ne with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  rcases h_or with hη | hη
  · exact CN05CoeffEq_at_prime_pow_split_via_eta p hp3 q hq_odd hqp hη k
  · exact CN05CoeffEq_at_prime_pow_inert_via_eta p hp3 q hq_odd hqp hη k

/-- **CN-05 coefficient equality at any prime power q^k**. -/
theorem CN05CoeffEq_at_prime_pow (hp3 : p % 4 = 3) (q : ℕ) (hq : q.Prime) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqp : q = p
  · rw [hqp]; exact CN05CoeffEq_at_prime_pow_p p hp3 k
  · by_cases hq_two : q = 2
    · rw [hq_two]; exact CN05CoeffEq_at_prime_pow_two p hp3 k
    · exact CN05CoeffEq_at_prime_pow_odd_ne_p p hp3 q hq_two hqp k

/-- Convolution multiplicativity at coprime arguments. -/
lemma convolution_one_mul_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (m * n) =
      (LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) m) *
      (LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) n) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hOne : toArithmeticFunction (fun _ : ℕ ↦ (1 : ℂ)) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) := by
    ext k
    change (if k = 0 then 0 else 1) = ((ArithmeticFunction.zeta k : ℕ) : ℂ)
    by_cases hk : k = 0 <;>
      simp only [ArithmeticFunction.zeta_apply, hk, if_true, if_false, Nat.cast_zero,
        Nat.cast_one]
  have hEta : toArithmeticFunction (legendreDirichletNat p) =
      toArithmeticFunction (fun k ↦ legendreDirichlet p (k : ZMod p)) := rfl
  simpa [DirichletCharacter.zetaMul, LSeries.convolution, hOne, hEta] using
    (DirichletCharacter.isMultiplicative_zetaMul (legendreDirichlet p)).map_mul_of_coprime hcop

/-- **`idealNormMultiplicity` is multiplicative**: at coprime arguments over ℂ. -/
lemma idealNormMultiplicity_mul_complex {m n : ℕ} (hcop : Nat.Coprime m n) :
    ((idealNormMultiplicity (Kminus p) (m * n) : ℕ) : ℂ) =
      ((idealNormMultiplicity (Kminus p) m : ℕ) : ℂ) *
      ((idealNormMultiplicity (Kminus p) n : ℕ) : ℂ) := by
  exact_mod_cast idealNormMultiplicity_mul (Kminus p) hcop

/-- **CN05CoeffEq**: for all n, `idealNormMultiplicity = conv (1) η`. -/
theorem CN05CoeffEq_proof (hp3 : p % 4 = 3) : CN05CoeffEq p := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q k hq hk =>
    rw [CN05CoeffEq_at_prime_pow p hp3 q hq k]
  | zero =>
    rw [idealNormMultiplicity_zero, LSeries.convolution_def]
    simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty, Nat.cast_zero]
  | one =>
    rw [idealNormMultiplicity_one, LSeries.convolution_def]
    simp only [Nat.divisorsAntidiagonal_one, Finset.sum_singleton, legendreDirichletNat_one,
      mul_one, Nat.cast_one]
  | coprime a b ha hb hcop ih_a ih_b =>
    rw [idealNormMultiplicity_mul_complex p hcop, ih_a, ih_b,
      convolution_one_mul_coprime p hcop]

/-- **CN05Hypothesis proved**: `ζ_{Kminus p}(s) = ζ(s) · L(η, s)` on Re(s) > 1. -/
theorem CN05Hypothesis_proof (hp3 : p % 4 = 3) : CN05Hypothesis p :=
  CN05_of_CN05CoeffEq p (CN05CoeffEq_proof p hp3)

end CN05_statement

end BernoulliRegular
