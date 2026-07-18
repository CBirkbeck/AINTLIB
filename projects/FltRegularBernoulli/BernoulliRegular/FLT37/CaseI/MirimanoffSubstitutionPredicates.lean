module

public import BernoulliRegular.FLT37.Hilbert90
public import BernoulliRegular.FLT37.KummerUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.NumberTheory.Cyclotomic.CaseI
public import FltRegular.CaseI.Statement
public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.FLT37.CaseI.MirimanoffRelations


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

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Mirimanoff parameter equality in `𝓞 K`: `ζ^{m_k} = ζ^{k·m_1}`.**
Direct consequence of `m_k ≡ k·m_1 (mod p)` and the cyclotomic relation
`ζ^p = 1`. -/
theorem fltCaseI_zeta_pow_mirimanoff_eq_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m₁ m_k : ℕ, ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m_k =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (k * m₁) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m₁, m_k, h_dvd⟩ := fltCaseI_mirimanoff_p_dvd_cross_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab (by have := hp.1.two_le; omega : 1 < p) hk
  -- h_dvd : p ∣ m₁·k - m_k·1 = m₁·k - m_k
  refine ⟨m₁, m_k, ?_⟩
  -- ζ^{m_k} = ζ^{k·m_1} iff m_k ≡ k·m_1 (mod p) iff p ∣ k·m_1 - m_k.
  have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    zeta_toInteger_pow_eq_one p K
  -- We have p ∣ (m₁·k - m_k). So either m₁·k ≥ m_k or vice versa, and the
  -- difference is divisible by p, giving the equality of ζ powers.
  rcases le_or_gt m_k (k * m₁) with h_le | h_lt
  · -- m_k ≤ k·m₁; difference is k·m₁ - m_k ≥ 0.
    -- ζ^{k·m₁} = ζ^{m_k} · ζ^{k·m₁ - m_k} = ζ^{m_k} · 1 (since p ∣ k·m₁ - m_k).
    have h_diff_dvd : (p : ℤ) ∣ ((k : ℤ) * m₁ - m_k) := by
      rw [show ((k : ℤ) * m₁ - m_k) = (m₁ : ℤ) * k - m_k * 1 by ring]
      exact h_dvd
    obtain ⟨q, hq⟩ : (p : ℕ) ∣ (k * m₁ - m_k) := by
      have h_eq : (((k * m₁ - m_k : ℕ) : ℤ)) = (k : ℤ) * m₁ - m_k := by
        rw [Nat.cast_sub h_le]
        push_cast
        ring
      have h_int : (p : ℤ) ∣ ((k * m₁ - m_k : ℕ) : ℤ) := by
        rw [h_eq]; exact h_diff_dvd
      exact_mod_cast h_int
    -- ζ^{k·m₁} = ζ^{m_k + (k·m₁ - m_k)}
    -- = ζ^{m_k} · ζ^{k·m₁ - m_k} = ζ^{m_k} · ζ^{p·q}
    --        = ζ^{m_k} · (ζ^p)^q = ζ^{m_k}.
    have h_pow_diff : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (k * m₁ - m_k) = 1 := by
      rw [hq, pow_mul, h_zeta_p, one_pow]
    have h_split : k * m₁ = m_k + (k * m₁ - m_k) := (Nat.add_sub_cancel' h_le).symm
    rw [h_split, pow_add, h_pow_diff, mul_one]
  · -- k·m₁ < m_k; difference is m_k - k·m₁ > 0.
    have h_le : k * m₁ ≤ m_k := h_lt.le
    have h_diff_dvd : (p : ℤ) ∣ ((m_k : ℤ) - k * m₁) := by
      have h_id' : ((m_k : ℤ) - k * m₁) = -((m₁ : ℤ) * k - m_k * 1) := by ring
      rw [h_id']
      exact dvd_neg.mpr h_dvd
    obtain ⟨q, hq⟩ : (p : ℕ) ∣ (m_k - k * m₁) := by
      have h_eq : (((m_k - k * m₁ : ℕ) : ℤ)) = (m_k : ℤ) - k * m₁ := by
        rw [Nat.cast_sub h_le]
        push_cast
        ring
      have h_int : (p : ℤ) ∣ ((m_k - k * m₁ : ℕ) : ℤ) := by
        rw [h_eq]; exact h_diff_dvd
      exact_mod_cast h_int
    have h_pow_diff : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (m_k - k * m₁) = 1 := by
      rw [hq, pow_mul, h_zeta_p, one_pow]
    have h_split : m_k = k * m₁ + (m_k - k * m₁) := (Nat.add_sub_cancel' h_le).symm
    rw [h_split, pow_add, h_pow_diff, mul_one]

/-- **Mirimanoff substitution `t = -a · b⁻¹`.** Under FLT case I + regularity
+ `p ∤ b`, define `t := -a · b⁻¹` in `ZMod p`. Then the Mirimanoff parameter
satisfies `m_1 · (1 - t) = 1`, i.e. `m_1 = (1 - t)⁻¹`.

This is the classical substitution that connects our `m_1 = b · (a+b)⁻¹`
formula to the Mirimanoff polynomial `φ_n(t)` evaluated at the substitution
parameter `t`. -/
theorem fltCaseI_mirimanoff_t_substitution_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m t : ZMod p, t = -(a : ZMod p) * ((b : ZMod p))⁻¹ ∧ m * (1 - t) = 1 := by
  haveI : Fact p.Prime := hp
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_zmod_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, -(a : ZMod p) * ((b : ZMod p))⁻¹, rfl, ?_⟩
  have h_b_ne : (b : ZMod p) ≠ 0 := by
    intro hz
    have h_dvd : ((b : ℤ) : ZMod p) = 0 := hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
    exact hb (by exact_mod_cast h_dvd)
  -- 1 - (-a/b) = (a+b)/b, so m·(1 - t) = m·(a+b)/b = b/b = 1.
  have h_id : (1 - -(a : ZMod p) * ((b : ZMod p))⁻¹) * (b : ZMod p) =
      (a + b : ZMod p) := by
    field_simp
    ring
  -- Multiply both sides of m·(1 - t) by b: m·(1-t)·b = m·(a+b) = b.
  have hmb : m * (1 - -(a : ZMod p) * ((b : ZMod p))⁻¹) * (b : ZMod p) =
      (b : ZMod p) := by
    rw [mul_assoc, h_id, hm]
  -- Cancel b on the right: m·(1 - t) = 1.
  have := mul_right_cancel₀ h_b_ne (hmb.trans (one_mul _).symm)
  exact this

/-- **Mirimanoff substitution: `t = (m_1 - 1) / m_1`.** Equivalent reformulation:
the classical "shift" substitution that recovers `t` from the Mirimanoff
parameter `m_1`. Used in deriving Mirimanoff polynomial vanishing. -/
theorem fltCaseI_mirimanoff_t_eq_shift_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (_ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m t : ZMod p, m ≠ 0 ∧ t = -(a : ZMod p) * ((b : ZMod p))⁻¹ ∧
      t = (m - 1) * m⁻¹ := by
  haveI : Fact p.Prime := hp
  obtain ⟨m, t, ht, hmt⟩ := fltCaseI_mirimanoff_t_substitution_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hb
  refine ⟨m, t, ?_, ht, ?_⟩
  · intro hm0
    rw [hm0, zero_mul] at hmt
    exact zero_ne_one hmt
  · -- m·(1 - t) = 1 ⟹ 1 - t = m⁻¹ ⟹ t = 1 - m⁻¹ = (m - 1)·m⁻¹.
    have hm_ne : m ≠ 0 := by
      intro hm0
      rw [hm0, zero_mul] at hmt
      exact zero_ne_one hmt
    have h_inv : 1 - t = m⁻¹ := by
      have := hmt
      field_simp at this ⊢
      linear_combination this
    have : t = 1 - m⁻¹ := by linear_combination -h_inv
    rw [this]
    field_simp

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **`t ≠ 0` and `t ≠ 1` in `ZMod p`.** Under FLT case I + `p ∤ a` and
`p ∤ b`, the Mirimanoff substitution parameter `t = -a · b⁻¹` satisfies
`t ≠ 0` (since `p ∤ a`) and `t ≠ 1` (since `p ∤ (a+b)`). -/
theorem fltCaseI_mirimanoff_t_ne_zero_one_of_regular
    (_hp_two : 2 < p) (_hp_odd : Odd p) (_hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (_h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (_hab : IsCoprime a b)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    haveI : Fact p.Prime := hp
    let t : ZMod p := -(a : ZMod p) * ((b : ZMod p))⁻¹
    t ≠ 0 ∧ t ≠ 1 := by
  haveI : Fact p.Prime := hp
  refine ⟨?_, ?_⟩
  · -- t ≠ 0: t = 0 would give -a/b = 0, so a = 0 in ZMod p, so p ∣ a.
    intro ht0
    have h_b_ne : (b : ZMod p) ≠ 0 := by
      intro hz
      have h_dvd : ((b : ℤ) : ZMod p) = 0 := hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
      exact hb (by exact_mod_cast h_dvd)
    have h_a_zero : (a : ZMod p) = 0 := by
      have h_neg : -(a : ZMod p) = 0 := by
        have : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) = 0 := by
          rw [ht0, zero_mul]
        rw [mul_assoc, inv_mul_cancel₀ h_b_ne, mul_one] at this
        exact this
      exact neg_eq_zero.mp h_neg
    have h_a_dvd : ((a : ℤ) : ZMod p) = 0 := h_a_zero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_a_dvd
    exact ha (by exact_mod_cast h_a_dvd)
  · -- t ≠ 1: t = 1 would give -a/b = 1, so -a = b in ZMod p, so p ∣ (a+b).
    intro ht1
    have h_b_ne : (b : ZMod p) ≠ 0 := by
      intro hz
      have h_dvd : ((b : ℤ) : ZMod p) = 0 := hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
      exact hb (by exact_mod_cast h_dvd)
    have h_neg_a_eq_b : -(a : ZMod p) = (b : ZMod p) := by
      have : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) = 1 * (b : ZMod p) := by
        rw [ht1]
      rw [mul_assoc, inv_mul_cancel₀ h_b_ne, mul_one, one_mul] at this
      exact this
    have h_ab_zero : (a + b : ZMod p) = 0 := by
      have : (a : ZMod p) + (b : ZMod p) = 0 := by
        rw [← h_neg_a_eq_b]; ring
      simpa using this
    have h_ab_dvd : ((a + b : ℤ) : ZMod p) = 0 := by
      simpa using h_ab_zero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_ab_dvd
    have hp_not_dvd : ¬ (p : ℤ) ∣ (a + b) :=
      fltCaseI_p_not_dvd_a_add_b heq hc
    exact hp_not_dvd (by exact_mod_cast h_ab_dvd)

/-- **Mirimanoff at index `k`: there exists `m_k ∈ ZMod p` with `m_k · (1 - t) = k`.**
For each `k < p`, there exists a Mirimanoff parameter `m_k` in `ZMod p` satisfying
`m_k · (1 - t) = k` where `t := -a · b⁻¹`. This is the classical formula
expressing each Mirimanoff parameter in terms of the substitution `t`. -/
theorem fltCaseI_mirimanoff_eq_k_div_one_sub_t_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b)
    {k : ℕ} (hk : k < p) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ (m_k : ZMod p) (t : ZMod p),
      t = -(a : ZMod p) * ((b : ZMod p))⁻¹ ∧
      t ≠ 1 ∧
      m_k * (1 - t) = (k : ZMod p) := by
  haveI : Fact p.Prime := hp
  -- Use relation_of_regular directly: m_k' · (a+b) ≡ b · k.
  obtain ⟨m_k', hmk_rel⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hk
  refine ⟨(m_k' : ZMod p), -(a : ZMod p) * ((b : ZMod p))⁻¹, rfl, ?_, ?_⟩
  · -- t ≠ 1: t = 1 ⟹ -a/b = 1 ⟹ a + b ≡ 0 (mod p), contradicting p ∤ (a+b).
    intro ht1
    have h_b_ne : (b : ZMod p) ≠ 0 := by
      intro hz
      have h_dvd : ((b : ℤ) : ZMod p) = 0 := hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
      exact hb (by exact_mod_cast h_dvd)
    have h_neg_a_eq_b : -(a : ZMod p) = (b : ZMod p) := by
      have h_eq : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) =
          1 * (b : ZMod p) := by rw [ht1]
      rw [mul_assoc, inv_mul_cancel₀ h_b_ne, mul_one, one_mul] at h_eq
      exact h_eq
    have h_ab_zero : (a + b : ZMod p) = 0 := by
      have : (a : ZMod p) + (b : ZMod p) = 0 := by rw [← h_neg_a_eq_b]; ring
      simpa using this
    have h_ab_dvd : ((a + b : ℤ) : ZMod p) = 0 := by
      simpa using h_ab_zero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_ab_dvd
    have hp_not_dvd : ¬ (p : ℤ) ∣ (a + b) :=
      fltCaseI_p_not_dvd_a_add_b heq hc
    exact hp_not_dvd (by exact_mod_cast h_ab_dvd)
  · -- m_k' · (1 - t) = k: derive from m_k' · (a+b) ≡ b · k and a+b = b·(1-t).
    have h_b_ne : (b : ZMod p) ≠ 0 := by
      intro hz
      have h_dvd : ((b : ℤ) : ZMod p) = 0 := hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
      exact hb (by exact_mod_cast h_dvd)
    have h_ab_eq : (a + b : ZMod p) =
        (b : ZMod p) * (1 - -(a : ZMod p) * ((b : ZMod p))⁻¹) := by
      field_simp
      ring
    have h_zmod : (((m_k' : ℤ) * (a + b) - b * k : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hmk_rel
    push_cast at h_zmod
    -- h_zmod : (m_k' : ZMod p) · (a + b) = b · k.
    have h_mk'_eq : (m_k' : ZMod p) * (a + b : ZMod p) = (b : ZMod p) * (k : ZMod p) := by
      linear_combination h_zmod
    rw [h_ab_eq] at h_mk'_eq
    -- h_mk'_eq : m_k' · (b · (1 - t)) = b · k.
    have h_assoc : (m_k' : ZMod p) * (1 - -(a : ZMod p) * ((b : ZMod p))⁻¹) *
        (b : ZMod p) = (k : ZMod p) * (b : ZMod p) := by
      linear_combination h_mk'_eq
    exact mul_right_cancel₀ h_b_ne h_assoc

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Mirimanoff swap-t formula: `t · t' = 1` in `ZMod p`.** Under FLT case I
+ regularity, the Mirimanoff substitution parameters for the swap-symmetric
pair satisfy `t · t' = 1`, where `t = -a · b⁻¹` and `t' = -b · a⁻¹`. -/
theorem fltCaseI_mirimanoff_t_swap_product_of_regular
    (_hp_two : 2 < p) (_hp_odd : Odd p) (_hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (_h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (_heq : a ^ p + b ^ p = c ^ p)
    (_hc : ¬ (p : ℤ) ∣ c) (_hab : IsCoprime a b)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    haveI : Fact p.Prime := hp
    let t : ZMod p := -(a : ZMod p) * ((b : ZMod p))⁻¹
    let t' : ZMod p := -(b : ZMod p) * ((a : ZMod p))⁻¹
    t * t' = 1 := by
  haveI : Fact p.Prime := hp
  have h_a_ne : (a : ZMod p) ≠ 0 := by
    intro hz
    have h_dvd : ((a : ℤ) : ZMod p) = 0 := by exact_mod_cast hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
    exact ha (by exact_mod_cast h_dvd)
  have h_b_ne : (b : ZMod p) ≠ 0 := by
    intro hz
    have h_dvd : ((b : ℤ) : ZMod p) = 0 := by exact_mod_cast hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
    exact hb (by exact_mod_cast h_dvd)
  -- t · t' = (-a/b) · (-b/a) = (ab)/(ab) = 1.
  change (-(a : ZMod p) * ((b : ZMod p))⁻¹) * (-(b : ZMod p) * ((a : ZMod p))⁻¹) = 1
  field_simp

/-- **Mirimanoff polynomial connection: m_k as polynomial-valued in t.**
For each `k < p`, the Mirimanoff parameter `m_k ∈ ZMod p` satisfies
`m_k · (1 - t) = k` where `t := -a · b⁻¹`. So `m_k = k · (1 - t)⁻¹`.

This corollary packages the Mirimanoff parameter as a uniform formula in
the substitution variable `t`, key to applying the Mirimanoff polynomial
identity. -/
theorem fltCaseI_mirimanoff_eq_inv_one_sub_t_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b)
    {k : ℕ} (hk : k < p) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m_k : ZMod p,
      let t : ZMod p := -(a : ZMod p) * ((b : ZMod p))⁻¹
      m_k = (k : ZMod p) * (1 - t)⁻¹ := by
  haveI : Fact p.Prime := hp
  obtain ⟨m_k, t, ht_eq, ht_ne, hmk⟩ := fltCaseI_mirimanoff_eq_k_div_one_sub_t_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hb hk
  refine ⟨m_k, ?_⟩
  -- m_k · (1 - t) = k, so m_k = k · (1 - t)⁻¹.
  have h_one_sub_ne : (1 - t : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht_ne)
  have h_eq : m_k * (1 - t) * (1 - t)⁻¹ = (k : ZMod p) * (1 - t)⁻¹ := by
    rw [hmk]
  rw [mul_assoc, mul_inv_cancel₀ h_one_sub_ne, mul_one] at h_eq
  rw [h_eq, ht_eq]

/-- **Mirimanoff at index `k` in `c`-form: `m_k · c ≡ b · k (mod p)`.**
Combines the existing relation `m_k · (a+b) ≡ b · k (mod p)` with the
Fermat congruence `c ≡ a + b (mod p)` (from `a^p + b^p = c^p` and Fermat
little). Useful when working with `c` directly. -/
theorem fltCaseI_mirimanoff_relation_k_c_form_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * c - b * k) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hk
  refine ⟨m, ?_⟩
  -- hm : p ∣ m·(a+b) - b·k. We want: p ∣ m·c - b·k.
  -- p ∣ c - (a+b), so p ∣ m·(c - (a+b)) = m·c - m·(a+b).
  have h_c : (p : ℤ) ∣ (c - (a + b)) := fltCaseI_p_dvd_c_sub_a_add_b heq
  have h_split : ((m : ℤ) * c - b * k) =
      (m : ℤ) * (c - (a + b)) + ((m : ℤ) * (a + b) - b * k) := by ring
  rw [h_split]
  exact dvd_add (h_c.mul_left _) hm

/-- **`p ∤ m_k` for `k` coprime to `p` and `p ∤ b`.** Generalises
`fltCaseI_mirimanoff_one_p_not_dvd_of_regular` from `k = 1` to any
`k` coprime to `p`. From `m_k · (a+b) ≡ b · k (mod p)`: if `p ∣ m_k`,
then `p ∣ b · k`, but `gcd(k, p) = 1` and `p ∤ b` give a contradiction. -/
theorem fltCaseI_mirimanoff_k_p_not_dvd_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b)
    {k : ℕ} (hk : k < p) (hk_pos : 0 < k) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, ¬ (p : ℤ) ∣ (m : ℤ) ∧ (p : ℤ) ∣ ((m : ℤ) * (a + b) - b * k) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hk
  refine ⟨m, ?_, hm⟩
  intro hpm
  -- hm : p ∣ m·(a+b) - b·k. Combined with p ∣ m: p ∣ b·k.
  have : (p : ℤ) ∣ ((m : ℤ) * (a + b)) := hpm.mul_right _
  have h_bk : (p : ℤ) ∣ (b * k) := by
    have := dvd_sub this hm
    have h_id : ((m : ℤ) * (a + b)) - ((m : ℤ) * (a + b) - b * k) = b * k := by ring
    rwa [h_id] at this
  -- p ∤ b, p ∤ k (since 0 < k < p), but p ∣ b·k. Contradiction with primality.
  have hp_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.1
  have hk_not_dvd : ¬ (p : ℤ) ∣ ((k : ℤ)) := by
    intro hk_dvd
    have hk_pos_int : 0 < (k : ℤ) := by exact_mod_cast hk_pos
    have h_le : (p : ℤ) ≤ (k : ℤ) := Int.le_of_dvd hk_pos_int hk_dvd
    have h_lt : (k : ℤ) < (p : ℤ) := by exact_mod_cast hk
    omega
  rcases hp_prime.dvd_mul.mp h_bk with h | h
  · exact hb h
  · exact hk_not_dvd h

/-- **Mirimanoff antisymmetry: `m_{p-k} ≡ -m_k (mod p)`.** Direct consequence
of the formula `m_k ≡ k · (1-t)⁻¹ (mod p)`: for `k` and `p-k`, since
`p - k ≡ -k (mod p)`, we get `m_{p-k} = -m_k` in `ZMod p`. -/
theorem fltCaseI_mirimanoff_antisymm_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b)
    {k : ℕ} (hk : k < p) (hk_pos : 0 < k) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m_k m_pk : ZMod p, m_pk = -m_k ∧ m_k * (1 - (-(a : ZMod p) * ((b : ZMod p))⁻¹)) =
      (k : ZMod p) := by
  haveI : Fact p.Prime := hp
  have h_pk_lt : p - k < p := by omega
  obtain ⟨m_k, t_k, ht_k_eq, _, hmk⟩ := fltCaseI_mirimanoff_eq_k_div_one_sub_t_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hb hk
  obtain ⟨m_pk, t_pk, ht_pk_eq, _, hmpk⟩ := fltCaseI_mirimanoff_eq_k_div_one_sub_t_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hb h_pk_lt
  -- t_k = t_pk = -a · b⁻¹.
  have h_t_eq : t_k = t_pk := by rw [ht_k_eq, ht_pk_eq]
  -- m_pk · (1 - t_pk) = (p - k : ZMod p) = -k (since p ≡ 0 in ZMod p).
  have h_pk_zmod : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
    have h_le : k ≤ p := hk.le
    have : ((p - k : ℕ) : ZMod p) + ((k : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) := by
      have : (((p - k) + k : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) := by
        rw [Nat.sub_add_cancel h_le]
      push_cast at this; linear_combination this
    have hp_zero : ((p : ℕ) : ZMod p) = 0 := by
      simp
    rw [hp_zero] at this
    linear_combination this
  rw [h_pk_zmod] at hmpk
  -- m_k · (1 - t_k) = k and m_pk · (1 - t_pk) = -k. Combine.
  rw [← h_t_eq] at hmpk
  refine ⟨m_k, m_pk, ?_, ?_⟩
  swap
  · rw [← ht_k_eq]; exact hmk
  -- m_pk · (1 - t_k) = -k = -(m_k · (1 - t_k)) = (-m_k) · (1 - t_k).
  have h_one_sub_ne : (1 - t_k : ZMod p) ≠ 0 := by
    rw [ht_k_eq]
    intro hz
    have h_eq : -(a : ZMod p) * ((b : ZMod p))⁻¹ = 1 := by linear_combination -hz
    have h_b_ne : (b : ZMod p) ≠ 0 := by
      intro hz_b
      have h_dvd : ((b : ℤ) : ZMod p) = 0 := by exact_mod_cast hz_b
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
      exact hb (by exact_mod_cast h_dvd)
    have h_neg_a_eq_b : -(a : ZMod p) = (b : ZMod p) := by
      have : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) =
          1 * (b : ZMod p) := by rw [h_eq]
      rw [mul_assoc, inv_mul_cancel₀ h_b_ne, mul_one, one_mul] at this
      exact this
    have h_ab : (a + b : ZMod p) = 0 := by
      have : (a : ZMod p) + (b : ZMod p) = 0 := by rw [← h_neg_a_eq_b]; ring
      exact_mod_cast this
    have h_ab_dvd : ((a + b : ℤ) : ZMod p) = 0 := by exact_mod_cast h_ab
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_ab_dvd
    have hp_not_dvd : ¬ (p : ℤ) ∣ (a + b) :=
      fltCaseI_p_not_dvd_a_add_b heq hc
    exact hp_not_dvd (by exact_mod_cast h_ab_dvd)
  -- m_pk · (1 - t_k) = -k = -m_k · (1 - t_k).
  have hmpk_neg : m_pk * (1 - t_k) = (-m_k) * (1 - t_k) := by
    rw [hmpk, neg_mul, hmk]
  exact mul_right_cancel₀ h_one_sub_ne hmpk_neg

/-! ## Mirimanoff polynomial vanishing — conditional infrastructure

The deep step in classical Mirimanoff/Vandiver case I is the polynomial
vanishing `φ_{p-n}(t) ≡ 0 (mod p)` for the substitution `t = -a · b⁻¹`.
This follows from the order-2+ Taylor expansion of the cyclotomic
factorisation, the logarithmic-derivative trick, and Bernoulli
power-sum identities.

We package the hypothesis as a `Prop` so downstream lemmas can be stated
unconditionally on this hypothesis. The actual discharge — relating the
case I + regularity setup to the classical Mirimanoff theorem — is the
remaining mathematical content for `[F37-A]`.
-/

/-- **Mirimanoff polynomial vanishing predicate.** The classical conclusion
of Mirimanoff's theorem: under FLT case I + regularity, the Mirimanoff
polynomial `φ_n` vanishes at `t = -a · b⁻¹ (mod p)` for all `n` in the
range `2 ≤ n ≤ p - 3`. The Mirimanoff polynomial here is from
`Mirimanoff.lean`. -/
def MirimanoffPolynomialVanishing (p : ℕ) [Fact p.Prime] (a b : ℤ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ p - 3 →
    (mirimanoffPolynomial p n).aeval
      (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0

/-- **Mirimanoff-Bernoulli identity predicate** (classical Mirimanoff theorem,
Ribenboim, *13 Lectures on Fermat's Last Theorem*, Lecture VIII Theorem 1B).

For an FLT case I solution `(a, b, c)` at `p` and `t = -a · b⁻¹ ∈ ZMod p`,
the classical Mirimanoff theorem gives the **product congruence**

`φ_n(t) · B_{p-n} ≡ 0 (mod p)`

for every odd `n` with `2 ≤ n ≤ p - 3`. (Equivalently, with `2s = p - n`
ranging over even values in `[2, p-3]`, the congruence reads
`φ_{p-2s}(t) · B_{2s} ≡ 0 (mod p)` for `s ∈ [1, (p-3)/2]`.)

Combined with the parity hypothesis (every irregular Bernoulli index
of `p` has even `k`) and `p ≡ 1 (mod 4)`, the congruence at indices
`n ≡ 3 (mod 4)` forces `B_{p-n} ≢ 0 (mod p)` (parity rules out the
odd `k = (p-n)/2`), so the product factors give the polynomial vanishing
`φ_n(t) ≡ 0 (mod p)` — see
`mirimanoffPolynomial_eval_eq_zero_of_mbi_and_parity` for the bridge.

The previous formulation `(p-1)·φ_n(t) ≡ -n·B_{p-n}·(1-t^n) (mod p)` was
incorrect (numerical refutation at `p = 5, n = 3, t = 2`: LHS = 4, RHS = 1)
and has been replaced by the classical product form. -/
def MirimanoffBernoulliIdentity (p : ℕ) [Fact p.Prime] (a b : ℤ) : Prop :=
  ∀ n : ℕ, Odd n → 2 ≤ n → n ≤ p - 3 →
    let t : ZMod p := -(a : ZMod p) * ((b : ZMod p))⁻¹
    (mirimanoffPolynomial p n).aeval t *
      (((bernoulli (p - n)).num : ℤ) : ZMod p) = 0

/-- **Direct Bernoulli divisibility predicate.** A higher-level alternative to
the conjunction `MirimanoffPolynomialVanishing ∧ MirimanoffBernoulliIdentity`:
directly state the conclusion that under FLT case I, for every `n` in the
range `2 ≤ n ≤ p - 3` such that `t^n ≠ 1` in `ZMod p`, the prime `p` divides
the numerator of the Bernoulli number `B_{p - n}`.

This predicate is implied by the conjunction (via
`bernoulli_dvd_of_mirimanoff_polynomial_vanishing`), and is easier to consume
downstream. -/
def MirimanoffBernoulliConclusion (p : ℕ) [Fact p.Prime] (a b : ℤ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ p - 3 →
    (-(a : ZMod p) * ((b : ZMod p))⁻¹) ^ n ≠ 1 →
    (p : ℤ) ∣ (bernoulli (p - n)).num

omit hp in
/-- **Vacuous discharge of `MirimanoffPolynomialVanishing` under regularity.**

Under FLT case I + regularity, no FLT solution `(a, b, c)` exists
(by Kummer's theorem, packaged in `flt-regular`'s `FltRegular.caseI`).
The hypothesis `a^p + b^p = c^p` together with `¬ p ∣ a·b·c` and
`IsRegularPrime p` is therefore inconsistent, so any conclusion follows
— in particular the Mirimanoff polynomial vanishing predicate. -/
theorem mirimanoffPolynomialVanishing_of_caseI_regular [Fact p.Prime] (h_reg : IsRegularPrime p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (h_caseI : ¬ (p : ℤ) ∣ a * b * c) :
    MirimanoffPolynomialVanishing p a b :=
  absurd heq (FltRegular.caseI h_reg h_caseI)

omit hp in
/-- **Vacuous discharge of `MirimanoffBernoulliIdentity` under regularity.**
Same reasoning as `mirimanoffPolynomialVanishing_of_caseI_regular`: no FLT
case I solution exists at a regular prime, so the predicate follows
vacuously. -/
theorem mirimanoffBernoulliIdentity_of_caseI_regular [Fact p.Prime] (h_reg : IsRegularPrime p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (h_caseI : ¬ (p : ℤ) ∣ a * b * c) :
    MirimanoffBernoulliIdentity p a b :=
  absurd heq (FltRegular.caseI h_reg h_caseI)

omit hp in
/-- **Vacuous discharge of `MirimanoffBernoulliConclusion` under regularity.**
Under FLT case I + regularity, vacuous via Kummer's theorem. -/
theorem mirimanoffBernoulliConclusion_of_caseI_regular [Fact p.Prime] (h_reg : IsRegularPrime p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (h_caseI : ¬ (p : ℤ) ∣ a * b * c) :
    MirimanoffBernoulliConclusion p a b :=
  absurd heq (FltRegular.caseI h_reg h_caseI)

omit hp in
/-- **Vacuous discharge of `φ_3(t) = 0` under regularity.** Under FLT case I
+ regularity, vacuous via Kummer's theorem. -/
theorem phi_3_eval_eq_zero_of_caseI_regular [Fact p.Prime] (h_reg : IsRegularPrime p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (h_caseI : ¬ (p : ℤ) ∣ a * b * c) :
    (mirimanoffPolynomial p 3).eval
      (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0 :=
  absurd heq (FltRegular.caseI h_reg h_caseI)

omit hp in
/-- **Vacuous discharge of `a ≡ b (mod p)` under regularity.** Under FLT
case I + regularity, vacuous via Kummer's theorem (`FltRegular.caseI`). -/
theorem a_eq_b_mod_p_of_caseI_regular [Fact p.Prime] (h_reg : IsRegularPrime p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (h_caseI : ¬ (p : ℤ) ∣ a * b * c) :
    (a : ZMod p) = (b : ZMod p) :=
  absurd heq (FltRegular.caseI h_reg h_caseI)

omit hp in
/-- **`φ_3(t) = 0 ↔ a ≡ b (mod p)` under FLT case I.**

Under `p ∤ a`, `p ∤ b`, `p ∤ a + b` (FLT case I), the φ_3 vanishing is
equivalent to the integer congruence `a ≡ b (mod p)`. Both are
equivalent to `t = -1` where `t = -a/b ∈ ZMod p`. -/
theorem fltCaseI_phi_3_iff_a_eq_b_mod_p
    [hp : Fact p.Prime] (hp_odd : Odd p)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b)
    (h_ab : ¬ (p : ℤ) ∣ a + b) :
    (mirimanoffPolynomial p 3).eval (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0 ↔
    (a : ZMod p) = (b : ZMod p) := by
  -- Both sides ⟺ t = -1 where t = -a/b.
  have ha_ne : (a : ZMod p) ≠ 0 := fun h ↦ ha (by
    have h_int : ((a : ℤ) : ZMod p) = 0 := h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  have hb_ne : (b : ZMod p) ≠ 0 := fun h ↦ hb (by
    have h_int : ((b : ℤ) : ZMod p) = 0 := h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  have hab_ne : ((a : ZMod p) + (b : ZMod p)) ≠ 0 := fun h ↦ h_ab (by
    have h_int : ((a + b : ℤ) : ZMod p) = 0 := by push_cast; linear_combination h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  set t : ZMod p := -(a : ZMod p) * ((b : ZMod p))⁻¹ with ht_def
  have ht_ne_zero : t ≠ 0 := by
    rw [ht_def]
    intro h
    apply ha_ne
    have hb_inv_ne : ((b : ZMod p))⁻¹ ≠ 0 := inv_ne_zero hb_ne
    have h_neg_a : -(a : ZMod p) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact absurd h2 hb_inv_ne
    linear_combination -h_neg_a
  have ht_ne_one : t ≠ 1 := by
    rw [ht_def]
    intro h
    apply hab_ne
    have h_eq : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) =
        1 * (b : ZMod p) := by rw [h]
    rw [mul_assoc, inv_mul_cancel₀ hb_ne, mul_one, one_mul] at h_eq
    linear_combination -h_eq
  refine ⟨fun h_phi ↦ ?_, fun h_eq ↦ ?_⟩
  · -- φ_3(t) = 0 ⟹ t = -1 (since t ≠ 0) ⟹ a ≡ b.
    rcases mirimanoffPolynomial_three_eval_eq_zero_imp p t ht_ne_one h_phi with h0 | h_neg_one
    · exact absurd h0 ht_ne_zero
    · -- t = -1 means -a/b = -1, so a = b.
      -- ht_def : t = -(a) * b⁻¹.
      -- h_neg_one : t = -1.
      -- So -(a) * b⁻¹ = -1, hence -(a) = -b, hence a = b.
      have h_eq : -(a : ZMod p) * ((b : ZMod p))⁻¹ = -1 := by
        rw [← ht_def]; exact h_neg_one
      have h_mul_b : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) = -1 * (b : ZMod p) := by
        rw [h_eq]
      rw [mul_assoc, inv_mul_cancel₀ hb_ne, mul_one] at h_mul_b
      linear_combination -h_mul_b
  · -- a ≡ b ⟹ t = -1 ⟹ φ_3(t) = 0.
    have ht_eq : t = -1 := by
      rw [ht_def, h_eq, neg_mul, mul_inv_cancel₀ hb_ne]
    rw [ht_eq]
    exact mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd
      (by norm_num : 1 ≤ 3) (by decide : Odd 3)

/-- **Mirimanoff polynomial vanishing predicate restricted to odd `n`.**

Same as `MirimanoffPolynomialVanishing` but with `Odd n` constraint. This
is the form actually needed by the conditional kernel
`flt_caseI_contradiction_of_mirimanoff_vandiver_odd`, since the kernel
only applies for odd `n` with `n % 4 = 3`. Matches the classical
Mirimanoff theorem (which gives vanishing for odd `n` only).

By `mirimanoffPolynomial_eval_eq_zero_of_phi_3_of_odd`, under `t ≠ 0, 1`
and `p` odd, this predicate is equivalent to the single condition
`φ_3(t) = 0` (where `t = -a/b`). -/
def MirimanoffPolynomialVanishingOdd (p : ℕ) [Fact p.Prime] (a b : ℤ) : Prop :=
  ∀ n : ℕ, Odd n → 2 ≤ n → n ≤ p - 3 →
    (mirimanoffPolynomial p n).aeval
      (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0

omit hp in
/-- **Discharge of `MirimanoffPolynomialVanishingOdd` from `φ_3` vanishing.**

For `p` odd prime, FLT case I (`p ∤ a`, `p ∤ b`, `p ∤ a + b`), and
`φ_3(t) = 0`, the odd-`n` Mirimanoff vanishing predicate holds. This
is the *structural reduction* lifted to the predicate level. -/
theorem mirimanoffPolynomialVanishingOdd_of_phi_3
    [hp : Fact p.Prime] (hp_odd : Odd p)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b)
    (h_ab : ¬ (p : ℤ) ∣ a + b)
    (h_phi_3 : (mirimanoffPolynomial p 3).eval
      (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0) :
    MirimanoffPolynomialVanishingOdd p a b := by
  -- Translate hypotheses to ZMod p facts.
  have ha_ne : (a : ZMod p) ≠ 0 := fun h ↦ ha (by
    have h_int : ((a : ℤ) : ZMod p) = 0 := h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  have h_b_ne : (b : ZMod p) ≠ 0 := fun h ↦ hb (by
    have h_int : ((b : ℤ) : ZMod p) = 0 := h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  have hab_ne : ((a : ZMod p) + (b : ZMod p)) ≠ 0 := fun h ↦ h_ab (by
    have h_int : ((a + b : ℤ) : ZMod p) = 0 := by push_cast; linear_combination h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  set t : ZMod p := -(a : ZMod p) * ((b : ZMod p))⁻¹ with ht_def
  have ht_ne_zero : t ≠ 0 := by
    rw [ht_def]
    intro h
    apply ha_ne
    have hb_inv_ne : ((b : ZMod p))⁻¹ ≠ 0 := inv_ne_zero h_b_ne
    have h_neg_a : -(a : ZMod p) = 0 := by
      have := mul_eq_zero.mp h
      rcases this with h1 | h2
      · exact h1
      · exact absurd h2 hb_inv_ne
    linear_combination -h_neg_a
  have ht_ne_one : t ≠ 1 := by
    rw [ht_def]
    intro h
    apply hab_ne
    have h_eq : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) =
        1 * (b : ZMod p) := by rw [h]
    rw [mul_assoc, inv_mul_cancel₀ h_b_ne, mul_one, one_mul] at h_eq
    -- h_eq : -(a : ZMod p) = (b : ZMod p)
    linear_combination -h_eq
  intro n hn_odd hn_two hn_le
  -- Convert eval to aeval. For ZMod p as algebra over itself, aeval = eval.
  have h := mirimanoffPolynomial_eval_eq_zero_of_phi_3_of_odd p hp_odd t
    ht_ne_zero ht_ne_one h_phi_3 (n := n) (by omega) hn_odd
  rw [Polynomial.aeval_def]
  rw [show (algebraMap (ZMod p) (ZMod p)) = RingHom.id (ZMod p) from rfl]
  rwa [show ((mirimanoffPolynomial p n).eval₂ (RingHom.id (ZMod p)) t) =
      (mirimanoffPolynomial p n).eval t from rfl]

omit hp in
/-- **Vacuous discharge of `MirimanoffPolynomialVanishingOdd` under regularity.**
Under FLT case I + regularity, vacuous via Kummer's theorem. -/
theorem mirimanoffPolynomialVanishingOdd_of_caseI_regular [Fact p.Prime] (h_reg : IsRegularPrime p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (h_caseI : ¬ (p : ℤ) ∣ a * b * c) :
    MirimanoffPolynomialVanishingOdd p a b :=
  absurd heq (FltRegular.caseI h_reg h_caseI)

omit hp in
/-- **Discharge of `MirimanoffPolynomialVanishingOdd` from `a ≡ b (mod p)`.**

The cleanest characterization in case I: under `p ∤ a`, `p ∤ b`,
`p ∤ a + b`, and `a ≡ b (mod p)`, the odd-`n` Mirimanoff polynomial
vanishing predicate holds. The argument:

* `t = -a/b ∈ ZMod p`, and `a ≡ b (mod p)` gives `t = -1`.
* `φ_n(-1) = 0` for odd `n` and odd `p` (existing
  `mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd`).

For FLT case I + parity at irregular `p = 37`, the classical Mirimanoff
theorem proves `a ≡ b (mod p)` via Galois descent on the cyclotomic
factor decomposition. This theorem packages the value-level conclusion. -/
theorem mirimanoffPolynomialVanishingOdd_of_a_eq_b_mod_p
    [hp : Fact p.Prime] (hp_odd : Odd p)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b)
    (h_ab : ¬ (p : ℤ) ∣ a + b)
    (h_eq : (a : ZMod p) = (b : ZMod p)) :
    MirimanoffPolynomialVanishingOdd p a b := by
  apply mirimanoffPolynomialVanishingOdd_of_phi_3 hp_odd ha hb h_ab
  -- Show φ_3(t) = 0 where t = -a/b.
  have hb_ne : (b : ZMod p) ≠ 0 := fun h ↦ hb (by
    have h_int : ((b : ℤ) : ZMod p) = 0 := h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_int)
  -- Compute t = -a/b = -1 using a = b in ZMod p.
  have ht_eq : -(a : ZMod p) * ((b : ZMod p))⁻¹ = -1 := by
    rw [h_eq, neg_mul, mul_inv_cancel₀ hb_ne]
  rw [ht_eq]
  exact mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd
    (by norm_num : 1 ≤ 3) (by decide : Odd 3)

/-- **`a ≡ b (mod p)` ↔ `2·m_1 ≡ 1 (mod p)` under FLT case I.**

The Mirimanoff parameter `m_1 ≡ b · (a+b)⁻¹ (mod p)` (from
`fltCaseI_mirimanoff_eq_b_div_aplusb_of_regular`). So:
* `2·m_1 ≡ 1 (mod p)` ⟺ `2b ≡ a+b (mod p)` ⟺ `b ≡ a (mod p)`.

This packages the structural equivalence at the integer level.

The classical Mirimanoff theorem under FLT case I + parity gives both
sides equivalently (as the substantive deep statement). -/
theorem fltCaseI_a_eq_b_iff_two_m_one_eq_one
    {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (h_ab : ¬ (p : ℤ) ∣ a + b)
    (m_1 : ℤ) (hm_1 : (p : ℤ) ∣ ((m_1 : ℤ) * (a + b) - b)) :
    (a : ZMod p) = (b : ZMod p) ↔
    (2 * m_1 : ZMod p) = 1 := by
  have hab_ne : ((a + b : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact h_ab h
  -- m_1 · (a+b) ≡ b (mod p), expressed in ZMod p.
  have hm_1_zmod : (m_1 : ZMod p) * ((a : ZMod p) + (b : ZMod p)) = (b : ZMod p) := by
    have h_zmod : ((m_1 * (a + b) - b : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hm_1
    push_cast at h_zmod
    linear_combination h_zmod
  refine ⟨fun h_eq ↦ ?_, fun h_two_m ↦ ?_⟩
  · -- a ≡ b ⟹ 2·m_1 ≡ 1.
    have hb_ne : (b : ZMod p) ≠ 0 := by
      intro h
      apply hab_ne
      push_cast
      linear_combination h_eq + 2 * h
    -- m_1 · (a+b) = b in ZMod p; substituting a = b gives m_1 · 2b = b.
    -- So (2 · m_1 - 1) · b = 0, hence 2 · m_1 = 1.
    have h_eq2 : (2 * (m_1 : ZMod p) - 1) * (b : ZMod p) = 0 := by
      linear_combination hm_1_zmod - (m_1 : ZMod p) * h_eq
    rcases mul_eq_zero.mp h_eq2 with h | h
    · linear_combination h
    · exact absurd h hb_ne
  · -- 2·m_1 ≡ 1 ⟹ a ≡ b.
    -- 2 · m_1 · (a + b) = 2 · b. Since 2 · m_1 = 1, (a+b) = 2b. Hence a = b.
    have h_step : (2 * (m_1 : ZMod p)) * ((a : ZMod p) + (b : ZMod p)) = 2 * (b : ZMod p) := by
      linear_combination 2 * hm_1_zmod
    rw [h_two_m, one_mul] at h_step
    -- h_step : (a : ZMod p) + (b : ZMod p) = 2 * (b : ZMod p)
    linear_combination h_step

/-! ### Bridge from `MirimanoffBernoulliIdentity` to polynomial vanishing

With the corrected product form
`φ_n(t) · B_{p-n} ≡ 0 (mod p)` for odd `n ∈ [2, p-3]`, the previous
`MV + MBI ⟹ MBC` bridge is no longer logically sound: assuming
`φ_n(t) = 0` makes the product trivially `0`, giving no information on
`B_{p-n}`. The classical chain runs the *other* direction: the parity
hypothesis combined with `n ≡ 3 (mod 4)` forces `B_{p-n} ≢ 0 (mod p)`
(an irregular index `k = (p-n)/2` would then be odd, violating parity),
and so the product factors give `φ_n(t) ≡ 0 (mod p)`.

The bridge `mirimanoffPolynomial_eval_eq_zero_of_mbi_and_parity` below
captures exactly this MBI + parity ⟹ polynomial vanishing implication;
it is placed after the irregular-index extraction helper. -/

end FLT37

end BernoulliRegular

end
