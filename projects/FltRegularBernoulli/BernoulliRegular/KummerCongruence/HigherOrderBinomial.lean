module

public import BernoulliRegular.KummerCongruence.Voronoi
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Higher-order binomial approximations for Voronoi/Kummer

Per the 2026-05-07 reviewer followup (patch 2 substantive direction),
formalising Kellner's Proposition 2.7 (avoiding direct `B_{1184}`
computation) requires extending the Voronoi/Kummer infrastructure from
order-1 (the existing `voronoi_sub_pow_linear_approx`) to higher order.

This file ships the **quadratic** binomial approximation:

   `(x - p·y)^k = x^k - k·x^{k-1}·p·y + (k choose 2)·x^{k-2}·p²·y² + p³·z`

for some `z : R` and `k ≥ 2`. This is the natural next step after
`voronoi_sub_pow_linear_approx` and provides the algebraic core for a
future higher-order Voronoi/Kummer extension.

## References

* Kellner, *On irregular prime power divisors of the Bernoulli numbers*,
  Math. Comp. 76 (2007); arXiv:math/0409223.
* `BernoulliRegular.KummerCongruence.Voronoi` —
  `voronoi_sub_pow_linear_approx` (the order-1 version).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-- **Voronoi quadratic approximation**: in any commutative ring `R`, for
`k ≥ 2` and any `x y : R`,
  `(x - p·y)^k = x^k - k · x^{k-1} · p · y + (k choose 2) · x^{k-2} · p² · y² + p³ · z`
for some explicit `z : R`. The `z` collects all terms with `p^i ≥ p³`
in the binomial expansion. -/
lemma voronoi_sub_pow_quadratic_approx {R : Type*} [CommRing R]
    (p : R) {k : ℕ} (hk : 2 ≤ k) (x y : R) :
    ∃ z : R,
      (x - p * y) ^ k = x ^ k - (k : R) * x ^ (k - 1) * p * y +
        ((k.choose 2 : ℕ) : R) * x ^ (k - 2) * p ^ 2 * y ^ 2 + p ^ 3 * z := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- k = 2: (x - py)² = x² - 2pxy + p²y² + 0.
    refine ⟨0, ?_⟩
    change (x - p * y) ^ 2 = x ^ 2 - (2 : R) * x ^ (2 - 1) * p * y +
        ((Nat.choose 2 2 : ℕ) : R) * x ^ (2 - 2) * p ^ 2 * y ^ 2 + p ^ 3 * 0
    simp only [Nat.choose_self, Nat.cast_one, one_mul, mul_zero, add_zero]
    ring
  | succ n hn ih =>
    -- k = n+1 with n ≥ 2. Use ih and multiply by (x - py).
    obtain ⟨z, hz⟩ := ih
    refine ⟨z * x - ((n.choose 2 : ℕ) : R) * x ^ (n - 2) * y ^ 3 - p * y * z, ?_⟩
    -- (x - p*y)^(n+1) = (x - p*y)^n * (x - p*y).
    have h_step : (x - p * y) ^ (n + 1) = (x - p * y) ^ n * (x - p * y) := pow_succ _ _
    rw [h_step, hz]
    -- Index arithmetic.
    have h_n_minus_1 : x ^ (n - 1) * x = x ^ n := by
      rw [← pow_succ]; congr 1; omega
    have h_n_minus_2 : x ^ (n - 2) * x = x ^ (n - 1) := by
      rw [← pow_succ]; congr 1; omega
    have h_succ_minus_1 : (n + 1 - 1 : ℕ) = n := by omega
    have h_succ_minus_2 : (n + 1 - 2 : ℕ) = n - 1 := by omega
    rw [h_succ_minus_1, h_succ_minus_2]
    -- Combinatorial identity: (n+1).choose 2 = n.choose 2 + n.
    have h_choose : ((n + 1).choose 2 : R) = (n.choose 2 : R) + (n : R) := by
      have : (n + 1).choose 2 = n.choose 1 + n.choose 2 :=
        Nat.choose_succ_succ' n 1
      rw [this]
      push_cast
      rw [Nat.choose_one_right]
      ring
    rw [show ((n + 1 : ℕ) : R) = (n : R) + 1 from by push_cast; ring]
    rw [h_choose]
    linear_combination
      (-(n : R) * p * y) * h_n_minus_1 +
      (((n.choose 2 : ℕ) : R) * p ^ 2 * y ^ 2) * h_n_minus_2

/-- **Voronoi cubic approximation**: in any commutative ring `R`, for
`k ≥ 3` and any `x y : R`,
  `(x - p·y)^k = x^k - k · x^{k-1} · p · y + (k choose 2) · x^{k-2} · p² · y² -
                  (k choose 3) · x^{k-3} · p³ · y³ + p^4 · z`
for some explicit `z : R`. -/
lemma voronoi_sub_pow_cubic_approx {R : Type*} [CommRing R]
    (p : R) {k : ℕ} (hk : 3 ≤ k) (x y : R) :
    ∃ z : R,
      (x - p * y) ^ k = x ^ k - (k : R) * x ^ (k - 1) * p * y +
        ((k.choose 2 : ℕ) : R) * x ^ (k - 2) * p ^ 2 * y ^ 2 -
        ((k.choose 3 : ℕ) : R) * x ^ (k - 3) * p ^ 3 * y ^ 3 +
        p ^ 4 * z := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- k = 3: (x - py)³ = x³ - 3x²py + 3x·p²y² - p³y³ + 0.
    refine ⟨0, ?_⟩
    change (x - p * y) ^ 3 = x ^ 3 - (3 : R) * x ^ (3 - 1) * p * y +
        ((Nat.choose 3 2 : ℕ) : R) * x ^ (3 - 2) * p ^ 2 * y ^ 2 -
        ((Nat.choose 3 3 : ℕ) : R) * x ^ (3 - 3) * p ^ 3 * y ^ 3 +
        p ^ 4 * 0
    -- 3.choose 2 = 3, 3.choose 3 = 1.
    simp only [show (Nat.choose 3 2 : ℕ) = 3 from rfl,
      show (Nat.choose 3 3 : ℕ) = 1 from rfl,
      mul_zero, add_zero]
    push_cast
    ring
  | succ n hn ih =>
    -- k = n+1 with n ≥ 3. Use ih and multiply by (x - py).
    obtain ⟨z, hz⟩ := ih
    refine ⟨z * x + ((n.choose 3 : ℕ) : R) * x ^ (n - 3) * y ^ 4 - p * y * z, ?_⟩
    have h_step : (x - p * y) ^ (n + 1) = (x - p * y) ^ n * (x - p * y) := pow_succ _ _
    rw [h_step, hz]
    -- Index arithmetic.
    have h_n_minus_1 : x ^ (n - 1) * x = x ^ n := by
      rw [← pow_succ]; congr 1; omega
    have h_n_minus_2 : x ^ (n - 2) * x = x ^ (n - 1) := by
      rw [← pow_succ]; congr 1; omega
    have h_n_minus_3 : x ^ (n - 3) * x = x ^ (n - 2) := by
      rw [← pow_succ]; congr 1; omega
    have h_succ_minus_1 : (n + 1 - 1 : ℕ) = n := by omega
    have h_succ_minus_2 : (n + 1 - 2 : ℕ) = n - 1 := by omega
    have h_succ_minus_3 : (n + 1 - 3 : ℕ) = n - 2 := by omega
    rw [h_succ_minus_1, h_succ_minus_2, h_succ_minus_3]
    -- Combinatorial identities:
    -- (n+1).choose 2 = n.choose 2 + n.choose 1 = n.choose 2 + n.
    -- (n+1).choose 3 = n.choose 3 + n.choose 2.
    have h_choose_2 : ((n + 1).choose 2 : R) = (n.choose 2 : R) + (n : R) := by
      rw [Nat.choose_succ_succ' n 1]; push_cast; rw [Nat.choose_one_right]; ring
    have h_choose_3 : ((n + 1).choose 3 : R) = (n.choose 3 : R) + (n.choose 2 : R) := by
      rw [Nat.choose_succ_succ' n 2]; push_cast; ring
    rw [show ((n + 1 : ℕ) : R) = (n : R) + 1 from by push_cast; ring]
    rw [h_choose_2, h_choose_3]
    linear_combination
      (-(n : R) * p * y) * h_n_minus_1 +
      (((n.choose 2 : ℕ) : R) * p ^ 2 * y ^ 2) * h_n_minus_2 +
      (-((n.choose 3 : ℕ) : R) * p ^ 3 * y ^ 3) * h_n_minus_3

/-! ## Bernoulli p-adic integrality from denominator coprimality -/

/-- **`B_n ∈ ℤ_[p]` from `¬ p ∣ B_n.den`**. The `p`-adic integrality of
`B_n` follows directly from the denominator being a `p`-unit, via
mathlib's `Padic.norm_rat_le_one`. This bypasses the Adams /
von Staudt–Clausen dependency cycle for specific numerically-verified `n`. -/
theorem bernoulli_mem_padicInt_of_p_not_dvd_den
    {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
    (h : ¬ (p : ℕ) ∣ ((bernoulli n).den)) :
    ∃ z : ℤ_[p], (((bernoulli n : ℚ)) : ℚ_[p]) = (z : ℚ_[p]) := by
  have h_norm : ‖((bernoulli n : ℚ) : ℚ_[p])‖ ≤ 1 := Padic.norm_rat_le_one h
  refine ⟨⟨((bernoulli n : ℚ) : ℚ_[p]), h_norm⟩, rfl⟩

/-! ## Per-term quadratic bound for higher-order Voronoi -/

/-- **Per-term quadratic Voronoi bound**: for prime `p`, a coprime to p,
and any `j : ℕ`,
  `r_j^k = (j·a)^k - k · (j·a)^{k-1} · p · q_j + (k C 2) · (j·a)^{k-2} · p² · q_j² + p³·z_j`
where `r_j := (j*a) % p`, `q_j := (j*a) / p`, and `z_j ∈ ℤ_[p]` is some witness.

Cast in `ℤ_[p]`, this is the per-`j` building block for the order-2
Voronoi sum identity (analogous to the per-term linear bound in
`voronoi_sum_mod_p_sq`). The witness exists by applying
`voronoi_sub_pow_quadratic_approx` to `x := (j*a : ℤ_[p])`, `y := (q_j : ℤ_[p])`. -/
lemma voronoi_per_term_quadratic_bound
    {p : ℕ} [hp : Fact p.Prime]
    (a : ℕ) (j : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    ∃ z : ℤ_[p],
      ((((j * a) % p : ℕ)) : ℤ_[p]) ^ k =
        ((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 2) *
            (p : ℤ_[p]) ^ 2 * (((j * a / p : ℕ)) : ℤ_[p]) ^ 2 +
          (p : ℤ_[p]) ^ 3 * z := by
  -- Connect (j*a) % p with (j*a) - p · ((j*a) / p) as ℤ_[p] elements.
  have h_div_mod :
      ((((j * a) % p : ℕ)) : ℤ_[p]) =
        ((j * a : ℕ) : ℤ_[p]) - (p : ℤ_[p]) * (((j * a / p : ℕ)) : ℤ_[p]) := by
    rw [show ((j * a : ℕ) : ℤ_[p]) =
        (((j * a / p) * p + (j * a) % p : ℕ) : ℤ_[p]) from by
      rw [← (Nat.div_add_mod' _ _).symm]]
    push_cast; ring
  -- Apply quadratic approximation with x = (j*a : ℤ_[p]), y = (j*a/p : ℤ_[p]).
  obtain ⟨z, hz⟩ := voronoi_sub_pow_quadratic_approx (R := ℤ_[p])
    (p := (p : ℤ_[p])) (k := k) hk
    ((j * a : ℕ) : ℤ_[p]) (((j * a / p : ℕ)) : ℤ_[p])
  refine ⟨z, ?_⟩
  rw [h_div_mod]
  exact hz

end BernoulliRegular

end
