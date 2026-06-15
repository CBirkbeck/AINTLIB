module

public import BernoulliRegular.ImaginaryQuadratic.CN05.Two

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
      LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  -- For odd q ≠ p, η(q) ∈ {1, -1}.
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
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [h]; simp)
  rcases h_or with hη | hη
  · exact CN05CoeffEq_at_prime_pow_split_via_eta p hp3 q hq_odd hqp hη k
  · exact CN05CoeffEq_at_prime_pow_inert_via_eta p hp3 q hq_odd hqp hη k

/-- **CN-05 coefficient equality at any prime power q^k**. -/
theorem CN05CoeffEq_at_prime_pow (hp3 : p % 4 = 3) (q : ℕ) (hq : q.Prime) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqp : q = p
  · rw [hqp]; exact CN05CoeffEq_at_prime_pow_p p hp3 k
  · by_cases hq_two : q = 2
    · rw [hq_two]; exact CN05CoeffEq_at_prime_pow_two p hp3 k
    · exact CN05CoeffEq_at_prime_pow_odd_ne_p p hp3 q hq_two hqp k

/-- Convolution multiplicativity at coprime arguments. -/
lemma convolution_one_mul_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (m * n) =
      (LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) m) *
      (LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) n) := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- Convert to ArithmeticFunction multiplicativity.
  -- conv 1 η n = ∑ d | n, η d (when n ≥ 1). Below we use the ArithmeticFunction framework.
  -- Use `Nat.divisorsAntidiagonal_mul_coprime` or direct sum computation.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.Coprime, Nat.gcd_zero_left] at hcop; subst hcop
    rw [LSeries.convolution_def]
    simp [Nat.divisorsAntidiagonal_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.Coprime, Nat.gcd_zero_right] at hcop; subst hcop
    rw [LSeries.convolution_def]
    simp [Nat.divisorsAntidiagonal_zero]
  -- Main case: both positive. Use ArithmeticFunction.
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  -- Define arithmetic functions
  let fOne : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else 1, by simp⟩
  let fEta : ArithmeticFunction ℂ :=
    ⟨fun n => if n = 0 then 0 else legendreDirichletNat p n, by simp⟩
  have hfOne_mul : fOne.IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
    · change (if (1 : ℕ) = 0 then 0 else 1) = 1
      simp
    · intro x y hx hy _
      change (if x * y = 0 then 0 else 1) =
        (if x = 0 then 0 else 1) * (if y = 0 then 0 else 1)
      simp [hx, hy, mul_ne_zero hx hy]
  have hfEta_mul : fEta.IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
    · change (if (1 : ℕ) = 0 then 0 else legendreDirichletNat p 1) = 1
      simpa using legendreDirichletNat_one p
    · intro x y hx hy _
      change (if x * y = 0 then 0 else legendreDirichletNat p (x * y)) =
        (if x = 0 then 0 else legendreDirichletNat p x) *
          (if y = 0 then 0 else legendreDirichletNat p y)
      rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
      change legendreDirichlet p ((x * y : ℕ) : ZMod p) =
        legendreDirichlet p ((x : ℕ) : ZMod p) * legendreDirichlet p ((y : ℕ) : ZMod p)
      push_cast; exact map_mul _ _ _
  have hconv_eq : ∀ k, 0 < k → LSeries.convolution (fun _ : ℕ => (1 : ℂ))
      (legendreDirichletNat p) k = (fOne * fEta) k := by
    intro k hk
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [LSeries.convolution_def]
    change ∑ x ∈ k.divisorsAntidiagonal, (1 : ℂ) * legendreDirichletNat p x.2 =
      ∑ x ∈ k.divisorsAntidiagonal, fOne x.1 * fEta x.2
    apply Finset.sum_congr rfl
    intro x hx
    have hx₁ : x.1 ≠ 0 := by
      have := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
      exact this.1
    have hx₂ : x.2 ≠ 0 := (Nat.ne_zero_of_mem_divisorsAntidiagonal hx).2
    change (1 : ℂ) * legendreDirichletNat p x.2 =
      (if x.1 = 0 then 0 else 1) * (if x.2 = 0 then 0 else legendreDirichletNat p x.2)
    rw [if_neg hx₁, if_neg hx₂]
  have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
  rw [hconv_eq _ hmn_pos, hconv_eq _ hm, hconv_eq _ hn]
  exact (hfOne_mul.mul hfEta_mul).map_mul_of_coprime hcop

/-- **`idealNormMultiplicity` is multiplicative**: at coprime arguments over ℂ. -/
lemma idealNormMultiplicity_mul_complex {m n : ℕ} (hcop : Nat.Coprime m n) :
    ((idealNormMultiplicity (Kminus p) (m * n) : ℕ) : ℂ) =
      ((idealNormMultiplicity (Kminus p) m : ℕ) : ℂ) *
      ((idealNormMultiplicity (Kminus p) n : ℕ) : ℂ) := by
  rw [idealNormMultiplicity_mul _ hcop]
  push_cast; ring

/-- **CN05CoeffEq**: for all n, `idealNormMultiplicity = conv (1) η`. -/
theorem CN05CoeffEq_proof (hp3 : p % 4 = 3) : CN05CoeffEq p := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q k hq hk =>
    rw [CN05CoeffEq_at_prime_pow p hp3 q hq k]
  | zero =>
    rw [idealNormMultiplicity_zero]
    rw [LSeries.convolution_def]
    simp [Nat.divisorsAntidiagonal_zero]
  | one =>
    rw [idealNormMultiplicity_one]
    rw [LSeries.convolution_def]
    simp [Nat.divisorsAntidiagonal_one, legendreDirichletNat_one p]
  | coprime a b ha hb hcop ih_a ih_b =>
    rw [idealNormMultiplicity_mul_complex p hcop, ih_a, ih_b,
      convolution_one_mul_coprime p hcop]

/-- **CN05Hypothesis proved**: `ζ_{Kminus p}(s) = ζ(s) · L(η, s)` on Re(s) > 1. -/
theorem CN05Hypothesis_proof (hp3 : p % 4 = 3) : CN05Hypothesis p :=
  CN05_of_CN05CoeffEq p (CN05CoeffEq_proof p hp3)

end CN05_statement

end BernoulliRegular
