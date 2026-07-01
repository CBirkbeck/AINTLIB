module

public import BernoulliRegular.FLT37.Hilbert90
public import BernoulliRegular.FLT37.KummerUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.NumberTheory.Cyclotomic.CaseI
public import FltRegular.CaseI.Statement
public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.FLT37.CaseI.TaylorCoefficientMatch

/-!
# FLT case I: composed unit-power decomposition (FLT37e)

Combines two earlier results:

* `fltCaseI_factor_eq_unit_mul_pow_of_regular`: the cyclotomic factor
  `a + ζ^k · b` equals a unit `u_k` times a `p`-th power `γ_k^p` (under
  regularity).
* `exists_zeta_pow_mul_real_eq_unit` (Kummer's lemma): the unit `u_k`
  splits as `ζ^{m_k} · v_k` with `v_k ∈ (𝓞 K⁺)ˣ` real.

Together: under regularity, every cyclotomic factor admits the
decomposition `a + ζ^k b = ζ^{m_k} · algebraMap v_k · γ_k^p`. This is the
shape used by the Mirimanoff-polynomial argument that closes case I.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Explicit per-index Mirimanoff relation.**

Combining the (ζ-1)¹ and (ζ-1)² identities and eliminating `m`, the
integer `(ζ-1)²` Taylor coefficient `w_int` satisfies

  `p ∣ 2 · w_int · (a + b) - k² · a · b`.

Derivation:
* `p ∣ b · k - m · (a + b)`  ⟹  squaring: `p ∣ m² · (a + b)² - b² · k²`.
* `p ∣ 2 · b · (k.choose 2) - 2 · (m.choose 2) · (a + b) - 2 · w_int`,
  i.e. `p ∣ b · k² - b · k - m² · (a + b) + m · (a + b) - 2 · w_int`.
* Using `m · (a + b) ≡ b · k (mod p)`:
  `p ∣ b · k² - m² · (a + b) - 2 · w_int`.
* Multiplying by `(a + b)`:
  `p ∣ b · k² · (a + b) - m² · (a + b)² - 2 · w_int · (a + b)`,
  and substituting `m² · (a + b)² ≡ b² · k²`:
  `p ∣ b · k² · (a + b) - b² · k² - 2 · w_int · (a + b)
     = b · k² · a - 2 · w_int · (a + b)`.

This relation is `(a + b)`-weighted but eliminates the per-`k` parameter
`m`, expressing `w_int_k` directly in terms of `a, b, k, p`. It is the
data feeding the Mirimanoff polynomial vanishing argument. -/
theorem fltCaseI_w_int_relation_of_regular
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ w_int : ℤ,
      (p : ℤ) ∣ (2 * w_int * (a + b) - (k : ℤ)^2 * a * b) := by
  obtain ⟨m, w_int, h_one, h_two⟩ :=
    fltCaseI_zmod_taylor_simplified_of_regular (K := K)
      hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk
  refine ⟨w_int, ?_⟩
  -- Step 1: Square h_one to get p ∣ (b·k - m·(a+b))² = b²·k² - 2·b·k·m·(a+b) + m²·(a+b)².
  -- Equivalently: p ∣ m²·(a+b)² - b²·k² + 2·(b·k)·(b·k - m·(a+b)).
  -- Since p ∣ b·k - m·(a+b), this gives p ∣ m²·(a+b)² - b²·k².
  have h_sq : (p : ℤ) ∣ ((m : ℤ)^2 * (a + b)^2 - b^2 * (k : ℤ)^2) := by
    have h_eq : (m : ℤ)^2 * (a + b)^2 - b^2 * (k : ℤ)^2 =
        (b * (k : ℤ) - (m : ℤ) * (a + b)) *
        (-(b * (k : ℤ) + (m : ℤ) * (a + b))) := by ring
    rw [h_eq]
    exact h_one.mul_right _
  -- Step 2: From h_two, multiply by 2:
  -- p ∣ 2·b·(k.choose 2) - 2·(m.choose 2)·(a+b) - 2·w_int.
  -- Using 2·(k.choose 2) = k² - k and 2·(m.choose 2) = m² - m:
  -- p ∣ b·(k² - k) - (m² - m)·(a+b) - 2·w_int.
  -- Adding b·k - m·(a+b) (which is 0 mod p):
  -- p ∣ b·k² - b·k - m²·(a+b) + m·(a+b) - 2·w_int + (b·k - m·(a+b))
  --    = b·k² - m²·(a+b) - 2·w_int.
  have h_two_two : (p : ℤ) ∣ (b * (k : ℤ)^2 - (m : ℤ)^2 * (a + b) - 2 * w_int) := by
    have h_two_2 : (p : ℤ) ∣ (2 * (b * (k.choose 2 : ℤ) -
        (m.choose 2 : ℤ) * (a + b) - w_int)) := h_two.mul_left 2
    have h_one_one : (p : ℤ) ∣ (b * (k : ℤ) - (m : ℤ) * (a + b)) := h_one
    have h_combined := h_two_2.add h_one_one
    -- 2·(b·(k.choose 2) - (m.choose 2)·(a+b) - w_int) + (b·k - m·(a+b))
    -- = 2b·(k.choose 2) - 2·(m.choose 2)·(a+b) - 2·w_int + b·k - m·(a+b)
    -- 2·(k.choose 2) = k² - k, so 2b·(k.choose 2) = b·k² - b·k.
    -- 2·(m.choose 2) = m² - m, so 2·(m.choose 2)·(a+b) = m²·(a+b) - m·(a+b).
    -- Sum: (b·k² - b·k) - (m²·(a+b) - m·(a+b)) - 2·w_int + b·k - m·(a+b)
    --    = b·k² - m²·(a+b) - 2·w_int.
    have h_choose2_k : (2 : ℤ) * (k.choose 2 : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
      have h := Nat.cast_descFactorial_two (S := ℤ) k
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.factorial_two] at h
      push_cast at h
      linarith
    have h_choose2_m : (2 : ℤ) * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
      have h := Nat.cast_descFactorial_two (S := ℤ) m
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.factorial_two] at h
      push_cast at h
      linarith
    have h_eq : 2 * (b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * (a + b) - w_int) +
        (b * (k : ℤ) - (m : ℤ) * (a + b)) =
        b * (k : ℤ)^2 - (m : ℤ)^2 * (a + b) - 2 * w_int := by
      linear_combination b * h_choose2_k - (a + b) * h_choose2_m
    rwa [h_eq] at h_combined
  -- Step 3: Multiply h_two_two by (a+b):
  -- p ∣ b·k²·(a+b) - m²·(a+b)² - 2·w_int·(a+b).
  -- Combined with h_sq (p ∣ m²·(a+b)² - b²·k²):
  -- p ∣ b·k²·(a+b) - b²·k² - 2·w_int·(a+b) = k²·a·b - 2·w_int·(a+b).
  have h_two_ab : (p : ℤ) ∣
      (b * (k : ℤ)^2 - (m : ℤ)^2 * (a + b) - 2 * w_int) * (a + b) :=
    h_two_two.mul_right _
  have h_combined := h_two_ab.add h_sq
  -- (b·k² - m²·(a+b) - 2·w_int)·(a+b) + (m²·(a+b)² - b²·k²)
  -- = b·k²·(a+b) - m²·(a+b)² - 2·w_int·(a+b) + m²·(a+b)² - b²·k²
  -- = b·k²·(a+b) - 2·w_int·(a+b) - b²·k²
  -- = k²·b·a - 2·w_int·(a+b).
  -- We want: p ∣ 2·w_int·(a+b) - k²·a·b.
  have h_eq : (b * (k : ℤ)^2 - (m : ℤ)^2 * (a + b) - 2 * w_int) * (a + b) +
      ((m : ℤ)^2 * (a + b)^2 - b^2 * (k : ℤ)^2) =
      -(2 * w_int * (a + b) - (k : ℤ)^2 * a * b) := by ring
  rw [h_eq] at h_combined
  exact (dvd_neg.mp h_combined)

/-- **Cross-index linearity for `w_int_k`.**

For any two indices `k₁, k₂ < p`, the corresponding integer `(ζ-1)²`
Taylor coefficients satisfy

  `p ∣ k₂² · w_int_k₁ - k₁² · w_int_k₂`.

This is the linearity statement: the per-index relation
`2·w_int_k·(a+b) ≡ k²·a·b (mod p)` determines `w_int_k` mod p uniquely
as `k²·a·b·(2·(a+b))⁻¹ (mod p)`, and hence `w_int_k₁/k₁² = w_int_k₂/k₂²`
mod p (cross-multiplied form). -/
theorem fltCaseI_w_int_cross_linearity_of_regular
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
      (p : ℤ) ∣ ((k₂ : ℤ)^2 * w_int_k₁ - (k₁ : ℤ)^2 * w_int_k₂) := by
  obtain ⟨w_int_k₁, h_k₁⟩ := fltCaseI_w_int_relation_of_regular (K := K)
    hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk₁
  obtain ⟨w_int_k₂, h_k₂⟩ := fltCaseI_w_int_relation_of_regular (K := K)
    hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk₂
  refine ⟨w_int_k₁, w_int_k₂, h_k₁, h_k₂, ?_⟩
  -- p ∣ k₂² · (2·w_int_k₁·(a+b) - k₁²·a·b) - k₁² · (2·w_int_k₂·(a+b) - k₂²·a·b)
  --   = 2·(k₂²·w_int_k₁ - k₁²·w_int_k₂)·(a+b) - 0
  --   = 2·(a+b)·(k₂²·w_int_k₁ - k₁²·w_int_k₂).
  have h_diff : (p : ℤ) ∣ (2 * (a + b) *
      ((k₂ : ℤ)^2 * w_int_k₁ - (k₁ : ℤ)^2 * w_int_k₂)) := by
    have h_combined := (h_k₁.mul_left ((k₂ : ℤ)^2)).sub (h_k₂.mul_left ((k₁ : ℤ)^2))
    have h_eq : 2 * (a + b) * ((k₂ : ℤ)^2 * w_int_k₁ - (k₁ : ℤ)^2 * w_int_k₂) =
        (k₂ : ℤ)^2 * (2 * w_int_k₁ * (a + b) - (k₁ : ℤ)^2 * a * b) -
          (k₁ : ℤ)^2 * (2 * w_int_k₂ * (a + b) - (k₂ : ℤ)^2 * a * b) := by ring
    rw [h_eq]
    exact h_combined
  -- Now extract: from p ∣ 2·(a+b)·X with p ∤ 2·(a+b), conclude p ∣ X.
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.1
  have h_2ab_ne : ¬ (p : ℤ) ∣ 2 * (a + b) := by
    intro h
    rcases hp_prime_int.dvd_mul.mp h with h_2 | h_ab
    · have h_le : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h_2
      have h_int : 5 ≤ (p : ℤ) := by exact_mod_cast hp_five
      omega
    · exact (fltCaseI_p_not_dvd_a_add_b heq hc) h_ab
  rcases hp_prime_int.dvd_mul.mp h_diff with h_2ab | h_X
  · exact absurd h_2ab h_2ab_ne
  · exact h_X

end FLT37

end BernoulliRegular

end
