import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerCaseI
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AKPrimarity
import BernoulliRegular.FLT37.CaseI.Part1
import BernoulliRegular.FLT37.KummerUnits

/-!
# Case-I antiRadical is not a p-th power

For case-I FLT data, the σ-anti radical
`α₀ = (a + ζb)/(a + ζ⁻¹b)` is not a p-th power in `K`.

## Proof outline

1. **Algebraic identity (this file, partial)**: `α₀ - 1 = b·(ζ-1)·(ζ+1)/(ζa+b)` in K.

2. **(ζ-1)-adic valuation of `α₀ - 1`**: under case-I (`p ∤ b`, `p ∤ a+b`):
   `v_{ζ-1}(α₀ - 1) = 1`.

3. **Contradiction**: if `α₀ = γ^p` then `v_{ζ-1}(γ^p - 1) ≥ 2` (Fermat
   + binomial expansion), contradicting step 2.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial IsCyclotomicExtension
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- `NeZero p` from `Fact p.Prime` (needed by `toInteger_isPrimitiveRoot`). -/
local instance : NeZero p := ⟨hp.1.ne_zero⟩

/-- The fixed cyclotomic root `zeta_spec p ℚ K` as a unit of `𝓞 K` (replacing the
removed `IsPrimitiveRoot.unit'`). -/
local notation3 "ζcu" =>
  ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit

/-- **Pure-K algebraic identity**: in any field where `ζ ≠ 0` and the relevant
denominators are non-zero, `(a + ζb)/(a + ζ⁻¹b) - 1 = b·(ζ-1)·(ζ+1)/(ζa + b)`. -/
theorem field_alg_identity {F : Type*} [Field F]
    (a b : F) (ζ : F) (hζ : ζ ≠ 0)
    (h_orig : a + ζ⁻¹ * b ≠ 0)
    (h_new : ζ * a + b ≠ 0) :
    (a + ζ * b) / (a + ζ⁻¹ * b) - 1 = b * (ζ - 1) * (ζ + 1) / (ζ * a + b) := by
  rw [div_sub_one h_orig, div_eq_div_iff h_orig h_new]
  field_simp
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **antiRadical - 1 explicit form**: in `K`,
`α₀ - 1 = (algebraMap (b·(ζ-1)·(ζ+1))) / (algebraMap (ζ·a + b))`.

Direct consequence of `field_alg_identity` after rewriting α₀'s denominator
`complexConj (a + ζb) = a + ζ⁻¹·b` via `complexConj_K_apply_primRoot_eq_inv`. -/
theorem antiRadical_sub_one_eq
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (hζ_pow : IsPrimitiveRoot ζ p)
    (h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0)
    (h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab - 1 =
      algebraMap (𝓞 K) K ((b : 𝓞 K) * (ζ - 1) * (ζ + 1)) /
        algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) := by
  unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
  set ζK : K := algebraMap (𝓞 K) K ζ with hζK_def
  have h_conj : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) =
      (a : K) + ζK⁻¹ * (b : K) := by
    have h_unfold : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
        (a : K) + ζK * (b : K) := by
      rw [map_add, map_mul]; rfl
    rw [h_unfold, map_add, map_mul]
    have h_a : NumberField.IsCMField.complexConj K ((a : K)) = (a : K) := by
      have : (a : K) =
          algebraMap (NumberField.maximalRealSubfield K) K
            (algebraMap ℤ (NumberField.maximalRealSubfield K) a) := by
        rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
        rfl
      rw [this]
      exact (NumberField.IsCMField.complexConj K).commutes _
    have h_b : NumberField.IsCMField.complexConj K ((b : K)) = (b : K) := by
      have : (b : K) =
          algebraMap (NumberField.maximalRealSubfield K) K
            (algebraMap ℤ (NumberField.maximalRealSubfield K) b) := by
        rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
        rfl
      rw [this]
      exact (NumberField.IsCMField.complexConj K).commutes _
    have h_ζ : NumberField.IsCMField.complexConj K ζK = ζK⁻¹ :=
      complexConj_K_apply_primRoot_eq_inv (K := K) hζ_pow
    rw [h_a, h_b, h_ζ]
  have h_num : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
      (a : K) + ζK * (b : K) := by
    rw [map_add, map_mul]; rfl
  have h_rhs_num : algebraMap (𝓞 K) K ((b : 𝓞 K) * (ζ - 1) * (ζ + 1)) =
      (b : K) * (ζK - 1) * (ζK + 1) := by
    rw [map_mul, map_mul, map_sub, map_add, map_one]; rfl
  have h_rhs_denom : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
      ζK * (a : K) + (b : K) := by
    rw [map_add, map_mul]; rfl
  rw [h_conj, h_num, h_rhs_num, h_rhs_denom]
  have hζK_ne : ζK ≠ 0 := by
    rw [hζK_def, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hζ_pow.ne_zero hp.out.ne_zero
  have h_orig_ne : (a : K) + ζK⁻¹ * (b : K) ≠ 0 := by
    rwa [hζK_def, ← h_conj]
  have h_new_ne : ζK * (a : K) + (b : K) ≠ 0 := by
    rwa [hζK_def, ← h_rhs_denom]
  exact field_alg_identity (a : K) (b : K) ζK hζK_ne h_orig_ne h_new_ne

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Cross-multiplied form** of `antiRadical_sub_one_eq`: in `K`,
`(ζa + b) · (α₀ - 1) = b · (ζ - 1) · (ζ + 1)` (each coerced from `𝓞 K`).

Useful for ideal-level divisibility arguments without explicit denominators. -/
theorem antiRadical_sub_one_cleared
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (hζ_pow : IsPrimitiveRoot ζ p)
    (h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0)
    (h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0) :
    algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) *
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab - 1) =
      algebraMap (𝓞 K) K ((b : 𝓞 K) * (ζ - 1) * (ζ + 1)) := by
  have h_form := antiRadical_sub_one_eq (K := K) (p := p)
    a b ζ hab hζ_pow h_denom_orig_nz h_denom_new_nz
  rw [h_form, mul_div_cancel₀]
  exact h_denom_new_nz

omit hp [NumberField K] in
/-- **Bridge `IsPrimitiveRoot ζ p` from `𝓞 K` to `K`**: lift the primitive root
property along the (injective) algebraMap. Lets us apply flt-regular's
`unit'`-based machinery when our root lives at `𝓞 K`. -/
theorem IsPrimitiveRoot_K_of_OK
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
  hζ.map_of_injective (NumberField.RingOfIntegers.coe_injective)

omit [NumberField.IsCMField K] in
/-- **`zeta_sub_one_dvd_Int_iff` reformulation for ζ : 𝓞 K**: in `𝓞 K`,
`(ζ - 1) ∣ n` for `n : ℤ` ↔ `p ∣ n`. -/
theorem zetaSubOne_dvd_Int_iff_p_dvd_OK
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) {n : ℤ} :
    (ζ - 1 : 𝓞 K) ∣ (n : 𝓞 K) ↔ (p : ℤ) ∣ n := by
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
  have h_unit_coe : (hζ_K.toInteger : 𝓞 K) = ζ := by
    apply RingOfIntegers.ext
    show ((hζ_K.toInteger : 𝓞 K) : K) = (ζ : K)
    rfl
  have h_rewrite : (ζ - 1 : 𝓞 K) = (hζ_K.toInteger : 𝓞 K) - 1 := by
    rw [h_unit_coe]
  rw [h_rewrite]
  exact zeta_sub_one_dvd_Int_iff (hζ := hζ_K)

omit [NumberField.IsCMField K] in
/-- **Key (ζ-1)-non-divisibility for case-I**: in `𝓞 K`, the element
`b · (ζ + 1)` is not divisible by `(ζ - 1)`, under case-I conditions
`p ∤ b` and `p ≠ 2`. -/
theorem zetaSubOne_not_dvd_b_mul_zeta_add_one
    (b : ℤ) (hp_odd : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b)
    {ζ : 𝓞 K} (hζ_pow : IsPrimitiveRoot ζ p) :
    ¬ (ζ - 1 : 𝓞 K) ∣ (b : 𝓞 K) * (ζ + 1) := by
  intro h_dvd
  have h_rewrite : (b : 𝓞 K) * (ζ + 1) = ((2 * b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (ζ - 1) := by
    push_cast; ring
  rw [h_rewrite] at h_dvd
  have h_trivial : (ζ - 1 : 𝓞 K) ∣ (b : 𝓞 K) * (ζ - 1) := ⟨b, by ring⟩
  have h_2b : (ζ - 1 : 𝓞 K) ∣ ((2 * b : ℤ) : 𝓞 K) := by
    have h_diff : ((2 * b : ℤ) : 𝓞 K) =
        (((2 * b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (ζ - 1)) - (b : 𝓞 K) * (ζ - 1) := by ring
    rw [h_diff]
    exact dvd_sub h_dvd h_trivial
  have h_p_dvd : (p : ℤ) ∣ (2 * b : ℤ) :=
    (zetaSubOne_dvd_Int_iff_p_dvd_OK (hζ := hζ_pow) (n := 2 * b)).mp h_2b
  have hp_prime : Nat.Prime p := Fact.out
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_prime_int.dvd_or_dvd h_p_dvd with h2 | hb'
  · have h_le : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
    have h_pos : 2 ≤ (p : ℤ) := by exact_mod_cast hp_prime.two_le
    have h_p_eq : (p : ℤ) = 2 := le_antisymm h_le h_pos
    have : p = 2 := by exact_mod_cast h_p_eq
    exact hp_odd this
  · exact hb hb'

omit [NumberField.IsCMField K] in
/-- **(ζ-1)-non-divisibility of ζa + b** under case-I: in `𝓞 K`,
`(ζ - 1) ∤ (ζ·a + b)` when `p ∤ (a + b)`. -/
theorem zetaSubOne_not_dvd_zeta_mul_a_add_b
    (a b : ℤ) (h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (hζ_pow : IsPrimitiveRoot ζ p) :
    ¬ (ζ - 1 : 𝓞 K) ∣ (ζ * (a : 𝓞 K) + (b : 𝓞 K)) := by
  intro h_dvd
  have h_rewrite : ζ * (a : 𝓞 K) + (b : 𝓞 K) = ((a + b : ℤ) : 𝓞 K) + (a : 𝓞 K) * (ζ - 1) := by
    push_cast; ring
  rw [h_rewrite] at h_dvd
  have h_trivial : (ζ - 1 : 𝓞 K) ∣ (a : 𝓞 K) * (ζ - 1) := ⟨a, by ring⟩
  have h_ab : (ζ - 1 : 𝓞 K) ∣ ((a + b : ℤ) : 𝓞 K) := by
    have h_diff : ((a + b : ℤ) : 𝓞 K) =
        (((a + b : ℤ) : 𝓞 K) + (a : 𝓞 K) * (ζ - 1)) - (a : 𝓞 K) * (ζ - 1) := by ring
    rw [h_diff]
    exact dvd_sub h_dvd h_trivial
  exact h_a_plus_b ((zetaSubOne_dvd_Int_iff_p_dvd_OK (hζ := hζ_pow) (n := a + b)).mp h_ab)

omit [NumberField.IsCMField K] in
/-- **(ζ-1)-non-divisibility of b**: in `𝓞 K`, `(ζ - 1) ∤ (b : 𝓞 K)` when `p ∤ b`.

Direct corollary of `zetaSubOne_dvd_Int_iff_p_dvd_OK`. -/
theorem zetaSubOne_not_dvd_b
    (b : ℤ) (hb : ¬ (p : ℤ) ∣ b)
    {ζ : 𝓞 K} (hζ_pow : IsPrimitiveRoot ζ p) :
    ¬ (ζ - 1 : 𝓞 K) ∣ (b : 𝓞 K) := by
  intro h
  exact hb ((zetaSubOne_dvd_Int_iff_p_dvd_OK (hζ := hζ_pow)).mp h)

omit [NumberField K] in
/-- **`(ζ - 1)` is nonzero in `𝓞 K`** (since `p ≥ 2` and `ζ ≠ 1`). -/
theorem zeta_sub_one_ne_zero
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) :
    (ζ - 1 : 𝓞 K) ≠ 0 := by
  intro h
  have hp_prime : Nat.Prime p := Fact.out
  have h_eq : ζ = 1 := sub_eq_zero.mp h
  rw [h_eq] at hζ
  have h_one_pow : (1 : 𝓞 K) ^ 1 = 1 := by ring
  have h_dvd : p ∣ 1 := hζ.dvd_of_pow_eq_one 1 h_one_pow
  have h_p_le_one : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h_dvd
  have hp_ge_2 : 2 ≤ p := hp_prime.two_le
  omega

omit [NumberField.IsCMField K] in
/-- **`(ζ - 1)² ∤ b · (ζ - 1) · (ζ + 1)` under case-I**: cancel one factor of
`(ζ - 1)` and apply `zetaSubOne_not_dvd_b_mul_zeta_add_one`. -/
theorem zetaSubOne_sq_not_dvd_b_mul_zeta_sub_one_mul_zeta_add_one
    (b : ℤ) (hp_odd : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b)
    {ζ : 𝓞 K} (hζ_pow : IsPrimitiveRoot ζ p) :
    ¬ ((ζ - 1 : 𝓞 K)) ^ 2 ∣ (b : 𝓞 K) * (ζ - 1) * (ζ + 1) := by
  intro h_dvd
  have h_factor : (b : 𝓞 K) * (ζ - 1) * (ζ + 1) = (ζ - 1) * ((b : 𝓞 K) * (ζ + 1)) := by ring
  rw [h_factor] at h_dvd
  have h_sq_factor : ((ζ - 1 : 𝓞 K)) ^ 2 = (ζ - 1) * (ζ - 1) := by ring
  rw [h_sq_factor] at h_dvd
  have h_cancel : (ζ - 1 : 𝓞 K) ∣ ((b : 𝓞 K) * (ζ + 1)) :=
    (mul_dvd_mul_iff_left (zeta_sub_one_ne_zero (p := p) (K := K) hζ_pow)).mp h_dvd
  exact zetaSubOne_not_dvd_b_mul_zeta_add_one (p := p) (K := K) b hp_odd hb hζ_pow h_cancel

omit [NumberField.IsCMField K] in
/-- **Fermat's little theorem mod `(ζ-1)`**: for any `x ∈ 𝓞 K`,
`(ζ - 1) ∣ x^p - x`. -/
theorem zetaSubOne_dvd_pow_p_sub_self
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (x : 𝓞 K) :
    (ζ - 1 : 𝓞 K) ∣ x ^ p - x := by
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
  obtain ⟨n, hn⟩ := exists_zeta_sub_one_dvd_sub_Int (hζ := hζ_K) x
  have h_unit_coe : (hζ_K.toInteger : 𝓞 K) = ζ := rfl
  have h_unit_eq : (hζ_K.toInteger : 𝓞 K) - 1 = (ζ - 1 : 𝓞 K) := by
    rw [h_unit_coe]
  rw [h_unit_eq] at hn
  have h_xp_np : (ζ - 1 : 𝓞 K) ∣ x ^ p - (n : 𝓞 K) ^ p :=
    hn.trans (sub_dvd_pow_sub_pow x (n : 𝓞 K) p)
  have h_p_dvd_int : (p : ℤ) ∣ (n ^ p - n) := by
    have hp_prime : Nat.Prime p := Fact.out
    haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
    have h_zmod : ((n ^ p - n : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.pow_card]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_zmod
  have h_dvd_OK_np_n : (ζ - 1 : 𝓞 K) ∣ ((n : 𝓞 K) ^ p - (n : 𝓞 K)) := by
    have h_int_form : ((n : 𝓞 K) ^ p - (n : 𝓞 K)) = (((n ^ p - n : ℤ)) : 𝓞 K) := by
      push_cast; ring
    rw [h_int_form]
    exact (zetaSubOne_dvd_Int_iff_p_dvd_OK (hζ := hζ) (n := n ^ p - n)).mpr h_p_dvd_int
  have h_combine : x ^ p - x =
      (x ^ p - (n : 𝓞 K) ^ p) + ((n : 𝓞 K) ^ p - (n : 𝓞 K)) - (x - (n : 𝓞 K)) := by ring
  rw [h_combine]
  exact dvd_sub (dvd_add h_xp_np h_dvd_OK_np_n) hn

omit [NumberField K] in
/-- **Strengthening: `(ζ-1) ∣ x - y → (ζ-1)² ∣ x^p - y^p`** in `𝓞 K`. -/
theorem zetaSubOne_sq_dvd_pow_p_sub_pow_p_of_dvd_sub
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (x y : 𝓞 K) (h_dvd : (ζ - 1 : 𝓞 K) ∣ x - y) :
    ((ζ - 1 : 𝓞 K)) ^ 2 ∣ x ^ p - y ^ p := by
  have h_factor : x ^ p - y ^ p =
      (x - y) * ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) := by
    rw [mul_comm, ← Commute.geom_sum₂_mul (Commute.all x y) p]
  rw [h_factor]
  rw [sq]
  apply mul_dvd_mul h_dvd
  have h_each_term : ∀ i ∈ Finset.range p,
      (ζ - 1 : 𝓞 K) ∣ x ^ i * y ^ (p - 1 - i) - y ^ (p - 1) := by
    intro i _
    have h_xi_yi : (ζ - 1 : 𝓞 K) ∣ x ^ i - y ^ i :=
      h_dvd.trans (sub_dvd_pow_sub_pow x y i)
    have h_factor_term : x ^ i * y ^ (p - 1 - i) - y ^ (p - 1) =
        (x ^ i - y ^ i) * y ^ (p - 1 - i) := by
      have hp_prime : Nat.Prime p := Fact.out
      have hp_pos : 0 < p := hp_prime.pos
      have hi_lt : i < p := Finset.mem_range.mp (by assumption : i ∈ Finset.range p)
      have h_pow_split : y ^ (p - 1) = y ^ i * y ^ (p - 1 - i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h_pow_split]; ring
    rw [h_factor_term]
    exact h_xi_yi.mul_right _
  have h_sum_eq : (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) =
      (∑ i ∈ Finset.range p, (x ^ i * y ^ (p - 1 - i) - y ^ (p - 1))) +
        (p : 𝓞 K) * y ^ (p - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    ring
  rw [h_sum_eq]
  apply dvd_add
  · exact Finset.dvd_sum h_each_term
  have hp_prime : Nat.Prime p := Fact.out
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
  have h_assoc := associated_zeta_sub_one_pow_prime (hζ := hζ_K)
  have h_unit_coe : (hζ_K.toInteger : 𝓞 K) = ζ := rfl
  have h_unit_eq : (hζ_K.toInteger : 𝓞 K) - 1 = (ζ - 1 : 𝓞 K) := by rw [h_unit_coe]
  rw [h_unit_eq] at h_assoc
  have h_pow_dvd : (ζ - 1 : 𝓞 K) ∣ (ζ - 1 : 𝓞 K) ^ (p - 1) := by
    apply dvd_pow_self
    omega
  have h_p_dvd : (ζ - 1 : 𝓞 K) ∣ (p : 𝓞 K) := h_pow_dvd.trans h_assoc.dvd
  exact h_p_dvd.mul_right _

omit [NumberField.IsCMField K] in
/-- **Fermat-style divisibility equivalence**: in `𝓞 K`, for any `x, y`,
`(ζ - 1) ∣ x^p - y^p ↔ (ζ - 1) ∣ x - y`. -/
theorem zetaSubOne_dvd_pow_p_sub_pow_p_iff
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (x y : 𝓞 K) :
    (ζ - 1 : 𝓞 K) ∣ x ^ p - y ^ p ↔ (ζ - 1 : 𝓞 K) ∣ x - y := by
  have h_decomp : x ^ p - y ^ p = (x ^ p - x) - (y ^ p - y) + (x - y) := by ring
  constructor
  · intro h
    have h_xy : (ζ - 1 : 𝓞 K) ∣ (x ^ p - y ^ p) - ((x ^ p - x) - (y ^ p - y)) :=
      dvd_sub h ((zetaSubOne_dvd_pow_p_sub_self hζ x).sub
        (zetaSubOne_dvd_pow_p_sub_self hζ y))
    rw [show (x ^ p - y ^ p) - ((x ^ p - x) - (y ^ p - y)) = x - y from by ring] at h_xy
    exact h_xy
  · intro h
    rw [h_decomp]
    exact dvd_add (dvd_sub (zetaSubOne_dvd_pow_p_sub_self hζ x)
      (zetaSubOne_dvd_pow_p_sub_self hζ y)) h

omit [NumberField.IsCMField K] in
/-- **Integer-form contradiction (case-I non-pth-power)**: under case-I hypotheses
(`p ≠ 2`, `p ∤ b`, `p ∤ a+b`) and the assumption that there exist `num, den : 𝓞 K`
with `den ≠ 0`, `(ζ - 1) ∤ den`, and the descent equation
`(ζa + b) · num^p = (ζa + ζ²b) · den^p`, derive `False`.

This is the heart of the proof: the integer equation forces `(ζ-1)`-content
incompatibilities under case-I. -/
theorem caseI_no_integer_pth_power_descent
    (hp_odd : p ≠ 2)
    (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) (h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (num den : 𝓞 K)
    (h_den_zeta_coprime : ¬ (ζ - 1 : 𝓞 K) ∣ den)
    (h_eq : (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * num ^ p =
      (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) * den ^ p) :
    False := by
  have h_rearr : (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * (num ^ p - den ^ p) =
      (b : 𝓞 K) * (ζ - 1) * (ζ + 1) * den ^ p := by
    have h_expand : (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) - (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
        (b : 𝓞 K) * (ζ - 1) * (ζ + 1) := by ring
    have h_sub : (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * num ^ p -
        (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * den ^ p =
        (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) * den ^ p -
        (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * den ^ p := by rw [h_eq]
    linear_combination h_sub
  have h_zab_coprime : ¬ (ζ - 1 : 𝓞 K) ∣ (ζ * (a : 𝓞 K) + (b : 𝓞 K)) :=
    zetaSubOne_not_dvd_zeta_mul_a_add_b (p := p) (K := K) a b h_a_plus_b hζ
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
  have h_unit_eq : (hζ_K.toInteger : 𝓞 K) - 1 = (ζ - 1 : 𝓞 K) := rfl
  have h_prime : Prime (ζ - 1 : 𝓞 K) := h_unit_eq ▸ hζ_K.zeta_sub_one_prime'
  by_cases h_sub_dvd : (ζ - 1 : 𝓞 K) ∣ num - den
  ·
    have h_sq_dvd : ((ζ - 1 : 𝓞 K)) ^ 2 ∣ num ^ p - den ^ p :=
      zetaSubOne_sq_dvd_pow_p_sub_pow_p_of_dvd_sub hζ num den h_sub_dvd
    have h_sq_dvd_lhs : ((ζ - 1 : 𝓞 K)) ^ 2 ∣ (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * (num ^ p - den ^ p) :=
      h_sq_dvd.mul_left _
    rw [h_rearr] at h_sq_dvd_lhs
    have h_factor : (b : 𝓞 K) * (ζ - 1) * (ζ + 1) * den ^ p =
        (ζ - 1) * ((b : 𝓞 K) * (ζ + 1) * den ^ p) := by ring
    rw [h_factor] at h_sq_dvd_lhs
    rw [sq] at h_sq_dvd_lhs
    have h_dvd_cancel : (ζ - 1 : 𝓞 K) ∣ (b : 𝓞 K) * (ζ + 1) * den ^ p :=
      (mul_dvd_mul_iff_left (zeta_sub_one_ne_zero (p := p) (K := K) hζ)).mp h_sq_dvd_lhs
    rcases h_prime.dvd_or_dvd h_dvd_cancel with h1 | h2
    · exact zetaSubOne_not_dvd_b_mul_zeta_add_one (p := p) (K := K) b hp_odd hb hζ h1
    ·
      exact h_den_zeta_coprime (h_prime.dvd_of_dvd_pow h2)
  ·
    have h_pow_not_dvd : ¬ (ζ - 1 : 𝓞 K) ∣ num ^ p - den ^ p := by
      rwa [zetaSubOne_dvd_pow_p_sub_pow_p_iff hζ]
    have h_rhs_dvd : (ζ - 1 : 𝓞 K) ∣ (b : 𝓞 K) * (ζ - 1) * (ζ + 1) * den ^ p := by
      have : (b : 𝓞 K) * (ζ - 1) * (ζ + 1) * den ^ p = (ζ - 1) *
          ((b : 𝓞 K) * (ζ + 1) * den ^ p) := by ring
      rw [this]
      exact dvd_mul_right _ _
    rw [← h_rearr] at h_rhs_dvd
    rcases h_prime.dvd_or_dvd h_rhs_dvd with h1 | h2
    · exact h_zab_coprime h1
    · exact h_pow_not_dvd h2

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Cleared product form of antiRadical**: `α₀ · (ζa + b) = ζa + ζ²b` in K
(as algebraMap'd elements from 𝓞 K).

Derived from `α₀ - 1 = b(ζ-1)(ζ+1)/(ζa+b)` (`antiRadical_sub_one_cleared`)
plus the algebraic identity `(ζa+b) + b(ζ-1)(ζ+1) = ζa + ζ²b`. -/
theorem antiRadical_mul_zeta_mul_a_add_b
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (hζ_pow : IsPrimitiveRoot ζ p)
    (h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0)
    (h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab * algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
      algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) := by
  have h_cleared := antiRadical_sub_one_cleared (K := K) (p := p)
    a b ζ hab hζ_pow h_denom_orig_nz h_denom_new_nz
  have h_sum_id : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) +
      algebraMap (𝓞 K) K ((b : 𝓞 K) * (ζ - 1) * (ζ + 1)) =
      algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) := by
    rw [← map_add]
    congr 1
    ring
  have : BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab * algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab - 1) * algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) +
      algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) := by ring
  rw [this, mul_comm (_ - 1), h_cleared, add_comm, h_sum_id]

/-- **K-level antiRadical non-pth-power (with explicit (ζ-1)-coprime form)**:
under case-I hypotheses, antiRadical is not equal to γ^p in `K` — provided
γ admits a num/den representation with `(ζ-1) ∤ den`.

This wraps the integer-level `caseI_no_integer_pth_power_descent` via
`antiRadical_mul_zeta_mul_a_add_b`. -/
theorem caseI_antiRadical_ne_pth_power_of_coprime_form
    (hp_odd : p ≠ 2)
    (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) (h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0)
    (h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0)
    (γ : K)
    (num den : 𝓞 K)
    (_hden_ne : den ≠ 0)
    (hden_coprime : ¬ (ζ - 1 : 𝓞 K) ∣ den)
    (hγ_eq : γ * algebraMap (𝓞 K) K den = algebraMap (𝓞 K) K num) :
    γ ^ p ≠ BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab := by
  intro h_pow_eq
  have h_γ_pow : γ ^ p * (algebraMap (𝓞 K) K den) ^ p =
      (algebraMap (𝓞 K) K num) ^ p := by
    rw [← mul_pow, hγ_eq]
  rw [h_pow_eq] at h_γ_pow
  have h_cleared := antiRadical_mul_zeta_mul_a_add_b (K := K) (p := p)
    a b ζ hab hζ h_denom_orig_nz h_denom_new_nz
  have h_K_eq : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) *
      (algebraMap (𝓞 K) K num) ^ p =
      algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) *
      (algebraMap (𝓞 K) K den) ^ p := by
    calc algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) *
        (algebraMap (𝓞 K) K num) ^ p
        = algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) *
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab * (algebraMap (𝓞 K) K den) ^ p) := by rw [h_γ_pow]
      _ = (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab * algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K))) *
          (algebraMap (𝓞 K) K den) ^ p := by ring
      _ = algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) *
          (algebraMap (𝓞 K) K den) ^ p := by rw [h_cleared]
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    NumberField.RingOfIntegers.coe_injective
  have h_OK_eq : (ζ * (a : 𝓞 K) + (b : 𝓞 K)) * num ^ p =
      (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) * den ^ p := by
    apply h_inj
    rw [map_mul, map_mul, map_pow, map_pow]
    exact h_K_eq
  exact caseI_no_integer_pth_power_descent (p := p) (K := K)
    hp_odd a b hb h_a_plus_b hζ num den hden_coprime h_OK_eq

/-- **Case-I non-pth-power for integer γ**: special case where `γ ∈ 𝓞 K`
(image under algebraMap). No coprimality condition needed since `den = 1`.

For any `γ_𝓞 ∈ 𝓞 K`, `(algebraMap γ_𝓞)^p ≠ antiRadical K a b ζ hab` under
case-I conditions. -/
theorem caseI_antiRadical_ne_integer_pth_power
    (hp_odd : p ≠ 2)
    (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) (h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0)
    (h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0)
    (γ_𝓞 : 𝓞 K) :
    algebraMap (𝓞 K) K γ_𝓞 ^ p ≠
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab := by
  refine caseI_antiRadical_ne_pth_power_of_coprime_form (p := p) (K := K)
    hp_odd a b hb h_a_plus_b hζ hab h_denom_orig_nz h_denom_new_nz
    (algebraMap (𝓞 K) K γ_𝓞)
    γ_𝓞 1
    one_ne_zero ?_ ?_
  ·
    intro h_dvd
    have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
    have h_unit_eq : (hζ_K.toInteger : 𝓞 K) - 1 = (ζ - 1 : 𝓞 K) := rfl
    have h_prime : Prime (ζ - 1 : 𝓞 K) := h_unit_eq ▸ hζ_K.zeta_sub_one_prime'
    exact h_prime.not_unit (isUnit_of_dvd_one h_dvd)
  ·
    rw [map_one, mul_one]

omit [NumberField.IsCMField K] in
/-- **WLOG existence**: given any representation `γ · den₀ = num₀` with
`num₀, den₀ ∈ 𝓞 K`, `den₀ ≠ 0`, and equal `(ζ-1)`-multiplicities of `num₀`
and `den₀`, extract a representation `γ · den = num` with both `num, den`
coprime to `(ζ - 1)`.

The multiplicity-equality hypothesis encodes "γ is a (ζ-1)-adic unit". -/
theorem exists_zeta_coprime_repr_of_mult_eq
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (γ : K) (num₀ den₀ : 𝓞 K) (hden₀ : den₀ ≠ 0)
    (h_eq : γ * algebraMap (𝓞 K) K den₀ = algebraMap (𝓞 K) K num₀)
    (hnum₀ : num₀ ≠ 0)
    (h_mult_eq : multiplicity (ζ - 1 : 𝓞 K) num₀ = multiplicity (ζ - 1 : 𝓞 K) den₀) :
    ∃ (num den : 𝓞 K), den ≠ 0 ∧ ¬ (ζ - 1 : 𝓞 K) ∣ num ∧
      ¬ (ζ - 1 : 𝓞 K) ∣ den ∧
      γ * algebraMap (𝓞 K) K den = algebraMap (𝓞 K) K num := by
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
  have h_unit_eq : (hζ_K.toInteger : 𝓞 K) - 1 = (ζ - 1 : 𝓞 K) := rfl
  have h_prime : Prime (ζ - 1 : 𝓞 K) := h_unit_eq ▸ hζ_K.zeta_sub_one_prime'
  have hζ_ne : (ζ - 1 : 𝓞 K) ≠ 0 := zeta_sub_one_ne_zero (p := p) (K := K) hζ
  have h_finmult_num : FiniteMultiplicity (ζ - 1 : 𝓞 K) num₀ :=
    FiniteMultiplicity.of_prime_left h_prime hnum₀
  have h_finmult_den : FiniteMultiplicity (ζ - 1 : 𝓞 K) den₀ :=
    FiniteMultiplicity.of_prime_left h_prime hden₀
  obtain ⟨num, hnum_eq, hnum_coprime⟩ := h_finmult_num.exists_eq_pow_mul_and_not_dvd
  obtain ⟨den, hden_eq, hden_coprime⟩ := h_finmult_den.exists_eq_pow_mul_and_not_dvd
  refine ⟨num, den, ?_, hnum_coprime, hden_coprime, ?_⟩
  ·
    intro h
    rw [h, mul_zero] at hden_eq
    exact hden₀ hden_eq
  ·
    set k := multiplicity (ζ - 1 : 𝓞 K) den₀ with hk_def
    have h_num_pow : num₀ = (ζ - 1) ^ k * num := h_mult_eq ▸ hnum_eq
    have h_den_pow : den₀ = (ζ - 1) ^ k * den := hden_eq
    have h_num₀_K : algebraMap (𝓞 K) K num₀ =
        (algebraMap (𝓞 K) K (ζ - 1)) ^ k * algebraMap (𝓞 K) K num := by
      rw [h_num_pow, map_mul, map_pow]
    have h_den₀_K : algebraMap (𝓞 K) K den₀ =
        (algebraMap (𝓞 K) K (ζ - 1)) ^ k * algebraMap (𝓞 K) K den := by
      rw [h_den_pow, map_mul, map_pow]
    rw [h_num₀_K, h_den₀_K] at h_eq
    have hζ_K_ne : (algebraMap (𝓞 K) K (ζ - 1)) ≠ 0 := by
      rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      exact hζ_ne
    have hζ_K_pow_ne : (algebraMap (𝓞 K) K (ζ - 1)) ^ k ≠ 0 :=
      pow_ne_zero _ hζ_K_ne
    have h_assoc : γ * ((algebraMap (𝓞 K) K (ζ - 1)) ^ k * algebraMap (𝓞 K) K den) =
        ((algebraMap (𝓞 K) K (ζ - 1)) ^ k) * (γ * algebraMap (𝓞 K) K den) := by ring
    rw [h_assoc] at h_eq
    exact mul_left_cancel₀ hζ_K_pow_ne h_eq

/-- **Final K-level case-I non-pth-power** (modulo case-II hypotheses):
under case-I, antiRadical is not a p-th power in K.

Combines all building blocks:
- γ = 0: 0 ≠ antiRadical (which is non-zero by hab + denominator conditions).
- γ ≠ 0: use IsLocalization.surj for num₀/den₀ representation, derive
  the integer equation, extract multiplicity equality (case-I makes both
  num₀ and den₀ have equal (ζ-1)-content), apply WLOG extraction to get
  coprime form, then caseI_antiRadical_ne_pth_power_of_coprime_form. -/
theorem caseI_antiRadical_not_pth_power
    (hp_odd : p ≠ 2)
    (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) (h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0)
    (h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0)
    (h_α_ne : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0)
    (γ : K) :
    γ ^ p ≠ BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab := by
  intro h_pow_eq
  have h_α₀_ne : BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ 0 := by
    unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
    exact div_ne_zero h_α_ne h_denom_orig_nz
  have hγ_ne : γ ≠ 0 := by
    intro hγ
    rw [hγ, zero_pow] at h_pow_eq
    · exact h_α₀_ne h_pow_eq.symm
    · exact Fact.out (p := Nat.Prime p) |>.ne_zero
  obtain ⟨⟨num₀, den₀⟩, h_surj⟩ := IsLocalization.surj (𝓞 K)⁰ γ
  simp only at h_surj
  have hden₀_ne : (den₀ : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero den₀.2
  have h_cleared := antiRadical_mul_zeta_mul_a_add_b (K := K) (p := p)
    a b ζ hab hζ h_denom_orig_nz h_denom_new_nz
  have h_K_eq : algebraMap (𝓞 K) K ((num₀ : 𝓞 K) ^ p * (ζ * (a : 𝓞 K) + (b : 𝓞 K))) =
      algebraMap (𝓞 K) K ((ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) * (den₀ : 𝓞 K) ^ p) := by
    rw [map_mul, map_pow, map_mul, map_pow]
    rw [← h_surj]
    rw [mul_pow]
    calc γ ^ p * algebraMap (𝓞 K) K (den₀ : 𝓞 K) ^ p *
          algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K))
        = BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              K a b ζ hab * algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) *
            algebraMap (𝓞 K) K (den₀ : 𝓞 K) ^ p := by rw [h_pow_eq]; ring
      _ = algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) *
            algebraMap (𝓞 K) K (den₀ : 𝓞 K) ^ p := by rw [h_cleared]
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    NumberField.RingOfIntegers.coe_injective
  have h_OK_eq : (num₀ : 𝓞 K) ^ p * (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
      (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) * (den₀ : 𝓞 K) ^ p :=
    h_inj h_K_eq
  have hnum₀_ne : (num₀ : 𝓞 K) ≠ 0 := by
    intro h
    rw [h] at h_surj
    simp only [map_zero] at h_surj
    have : γ * algebraMap (𝓞 K) K (den₀ : 𝓞 K) = 0 := h_surj
    have : γ = 0 ∨ algebraMap (𝓞 K) K (den₀ : 𝓞 K) = 0 := mul_eq_zero.mp this
    rcases this with h1 | h2
    · exact hγ_ne h1
    · exact hden₀_ne ((FaithfulSMul.algebraMap_eq_zero_iff _ _).mp h2)
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p := IsPrimitiveRoot_K_of_OK hζ
  have h_unit_eq_aux : (hζ_K.toInteger : 𝓞 K) - 1 = (ζ - 1 : 𝓞 K) := rfl
  have h_prime : Prime (ζ - 1 : 𝓞 K) := h_unit_eq_aux ▸ hζ_K.zeta_sub_one_prime'
  have hp_prime : Nat.Prime p := Fact.out
  have h_mult_eq :
      multiplicity (ζ - 1 : 𝓞 K) (num₀ : 𝓞 K) = multiplicity (ζ - 1 : 𝓞 K) (den₀ : 𝓞 K) := by
    have h_finmult_num : FiniteMultiplicity (ζ - 1 : 𝓞 K) (num₀ : 𝓞 K) :=
      FiniteMultiplicity.of_prime_left h_prime hnum₀_ne
    have h_finmult_den : FiniteMultiplicity (ζ - 1 : 𝓞 K) (den₀ : 𝓞 K) :=
      FiniteMultiplicity.of_prime_left h_prime hden₀_ne
    have h_zab_coprime : ¬ (ζ - 1 : 𝓞 K) ∣ (ζ * (a : 𝓞 K) + (b : 𝓞 K)) :=
      zetaSubOne_not_dvd_zeta_mul_a_add_b (p := p) (K := K) a b h_a_plus_b hζ
    have h_apb_coprime : ¬ (ζ - 1 : 𝓞 K) ∣ ((a : 𝓞 K) + ζ * (b : 𝓞 K)) := by
      intro h_dvd
      have h_rewrite : (a : 𝓞 K) + ζ * (b : 𝓞 K) =
          ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (ζ - 1) := by push_cast; ring
      rw [h_rewrite] at h_dvd
      have h_triv : (ζ - 1 : 𝓞 K) ∣ (b : 𝓞 K) * (ζ - 1) := ⟨b, by ring⟩
      have h_ab_dvd : (ζ - 1 : 𝓞 K) ∣ ((a + b : ℤ) : 𝓞 K) := by
        have : ((a + b : ℤ) : 𝓞 K) =
            (((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (ζ - 1)) - (b : 𝓞 K) * (ζ - 1) := by ring
        rw [this]; exact dvd_sub h_dvd h_triv
      exact h_a_plus_b ((zetaSubOne_dvd_Int_iff_p_dvd_OK (hζ := hζ) (n := a + b)).mp h_ab_dvd)
    have h_zaz2b_coprime : ¬ (ζ - 1 : 𝓞 K) ∣ (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) := by
      have h_factor : ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K) = ζ * ((a : 𝓞 K) + ζ * (b : 𝓞 K)) := by
        ring
      rw [h_factor]
      intro h_dvd
      rcases h_prime.dvd_or_dvd h_dvd with h1 | h2
      ·
        have h_one : (ζ - 1 : 𝓞 K) ∣ (1 : 𝓞 K) := by
          have h_dvd_diff : (ζ - 1 : 𝓞 K) ∣ ζ - (ζ - 1) := dvd_sub h1 dvd_rfl
          have h_eq_one : ζ - (ζ - 1) = (1 : 𝓞 K) := by ring
          rwa [h_eq_one] at h_dvd_diff
        exact h_prime.not_unit (isUnit_of_dvd_one h_one)
      · exact h_apb_coprime h2
    have hζab_ne : ζ * (a : 𝓞 K) + (b : 𝓞 K) ≠ 0 := by
      intro h
      apply h_denom_new_nz
      have : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) = algebraMap (𝓞 K) K 0 := by
        rw [h]
      rwa [map_zero] at this
    have hζaz2b_ne : ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K) ≠ 0 := by
      intro h
      apply h_α_ne
      have h_factor : ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K) = ζ * ((a : 𝓞 K) + ζ * (b : 𝓞 K)) := by
        ring
      rw [h_factor] at h
      have hζ_ne_OK : ζ ≠ 0 := hζ.ne_zero hp_prime.ne_zero
      have h_apb_zero : (a : 𝓞 K) + ζ * (b : 𝓞 K) = 0 := by
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 hζ_ne_OK
        · exact h2
      have h_map_eq : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) = algebraMap (𝓞 K) K 0 := by
        rw [h_apb_zero]
      rwa [map_zero] at h_map_eq
    have h_finmult_zab : FiniteMultiplicity (ζ - 1 : 𝓞 K) (ζ * (a : 𝓞 K) + (b : 𝓞 K)) :=
      FiniteMultiplicity.of_prime_left h_prime hζab_ne
    have h_finmult_zaz2b : FiniteMultiplicity (ζ - 1 : 𝓞 K)
        (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) :=
      FiniteMultiplicity.of_prime_left h_prime hζaz2b_ne
    have h_lhs : multiplicity (ζ - 1 : 𝓞 K) ((num₀ : 𝓞 K) ^ p * (ζ * (a : 𝓞 K) + (b : 𝓞 K))) =
        p * multiplicity (ζ - 1 : 𝓞 K) (num₀ : 𝓞 K) := by
      rw [multiplicity_mul h_prime
        (Prime.finiteMultiplicity_mul h_prime (FiniteMultiplicity.pow h_prime h_finmult_num) h_finmult_zab),
        FiniteMultiplicity.multiplicity_pow h_prime h_finmult_num]
      have h_zab_mult_zero : multiplicity (ζ - 1 : 𝓞 K) (ζ * (a : 𝓞 K) + (b : 𝓞 K)) = 0 := by
        rw [multiplicity_eq_zero]; exact h_zab_coprime
      omega
    have h_rhs :
        multiplicity (ζ - 1 : 𝓞 K) ((ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) * (den₀ : 𝓞 K) ^ p) =
        p * multiplicity (ζ - 1 : 𝓞 K) (den₀ : 𝓞 K) := by
      rw [multiplicity_mul h_prime
        (Prime.finiteMultiplicity_mul h_prime h_finmult_zaz2b (FiniteMultiplicity.pow h_prime h_finmult_den)),
        FiniteMultiplicity.multiplicity_pow h_prime h_finmult_den]
      have h_zaz2b_mult_zero :
          multiplicity (ζ - 1 : 𝓞 K) (ζ * (a : 𝓞 K) + ζ ^ 2 * (b : 𝓞 K)) = 0 := by
        rw [multiplicity_eq_zero]; exact h_zaz2b_coprime
      omega
    have h_eq_mult : p * multiplicity (ζ - 1 : 𝓞 K) (num₀ : 𝓞 K) =
        p * multiplicity (ζ - 1 : 𝓞 K) (den₀ : 𝓞 K) := by
      rw [← h_lhs, ← h_rhs, h_OK_eq]
    have hp_pos : 0 < p := hp_prime.pos
    exact Nat.eq_of_mul_eq_mul_left hp_pos h_eq_mult
  obtain ⟨num, den, hden_ne, hnum_coprime, hden_coprime, hγ_eq⟩ :=
    exists_zeta_coprime_repr_of_mult_eq (p := p) (K := K) hζ γ
      (num₀ : 𝓞 K) (den₀ : 𝓞 K) hden₀_ne h_surj hnum₀_ne h_mult_eq
  exact caseI_antiRadical_ne_pth_power_of_coprime_form (p := p) (K := K)
    hp_odd a b hb h_a_plus_b hζ hab h_denom_orig_nz h_denom_new_nz γ
    num den hden_ne hden_coprime hγ_eq h_pow_eq

/-- **Consumer-friendly form**: case-I non-pth-power directly from
`(hp_odd, hcaseI, hζ, hab, p ∤ a+b)` — without needing to pass the
non-zero technical hypotheses. -/
theorem caseI_antiRadical_not_pth_power_clean
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    (h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) :
    γ ^ p ≠ BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab := by
  have hb : ¬ (p : ℤ) ∣ b := by
    intro hb_div
    apply hcaseI
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb_div _) _
  have h_α_ne : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0 :=
    caseI_factor_K_ne_zero (K := K) hp_odd hcaseI hζ
  have h_denom_orig_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0 :=
    caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ
  have h_denom_new_nz : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) ≠ 0 := by
    intro h_zero
    set ζK : K := algebraMap (𝓞 K) K ζ with hζK_def
    have hζK_ne : ζK ≠ 0 := by
      rw [hζK_def, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      have hp_prime : Nat.Prime p := Fact.out
      exact hζ.ne_zero hp_prime.ne_zero
    have h_zab_K : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
        ζK * (a : K) + (b : K) := by
      rw [map_add, map_mul]; rfl
    have h_conj_form : NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) =
        (a : K) + ζK⁻¹ * (b : K) := by
      have h_unfold : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
          (a : K) + ζK * (b : K) := by
        rw [map_add, map_mul]; rfl
      rw [h_unfold, map_add, map_mul]
      have h_a : NumberField.IsCMField.complexConj K ((a : K)) = (a : K) := by
        have : (a : K) =
            algebraMap (NumberField.maximalRealSubfield K) K
              (algebraMap ℤ (NumberField.maximalRealSubfield K) a) := by
          rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
          rfl
        rw [this]
        exact (NumberField.IsCMField.complexConj K).commutes _
      have h_b : NumberField.IsCMField.complexConj K ((b : K)) = (b : K) := by
        have : (b : K) =
            algebraMap (NumberField.maximalRealSubfield K) K
              (algebraMap ℤ (NumberField.maximalRealSubfield K) b) := by
          rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
          rfl
        rw [this]
        exact (NumberField.IsCMField.complexConj K).commutes _
      have h_ζ : NumberField.IsCMField.complexConj K ζK = ζK⁻¹ :=
        complexConj_K_apply_primRoot_eq_inv (K := K) hζ
      rw [h_a, h_b, h_ζ]
    have h_rel : algebraMap (𝓞 K) K (ζ * (a : 𝓞 K) + (b : 𝓞 K)) =
        ζK * NumberField.IsCMField.complexConj K
          (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) := by
      rw [h_zab_K, h_conj_form]
      field_simp
    rw [h_rel] at h_zero
    have : NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) = 0 := by
      rcases mul_eq_zero.mp h_zero with h | h
      · exact absurd h hζK_ne
      · exact h
    exact h_denom_orig_nz this
  exact caseI_antiRadical_not_pth_power (p := p) (K := K)
    hp_odd a b hb h_a_plus_b hζ hab h_denom_orig_nz h_denom_new_nz h_α_ne γ

/-- **`CaseI_AntiRadical_NotPthPower` discharge** from the explicit case-I theorem.

This delivers the named Prop directly. -/
theorem CaseI_AntiRadical_NotPthPower_holds :
    CaseI_AntiRadical_NotPthPower (p := p) (K := K) :=
  fun hp_odd _ _ _ hcaseI h_a_plus_b _ hζ hab v =>
    caseI_antiRadical_not_pth_power_clean (p := p) (K := K) hp_odd hcaseI h_a_plus_b hζ hab v

/-- **Direct consumer form from FLT case-I equation**: given the FLT
case-I equation `a^p + b^p = c^p` with `¬ p ∣ abc`, antiRadical is not
a p-th power in K. The `p ∤ a+b` hypothesis is derived internally
via `fltCaseI_p_not_dvd_a_add_b`. -/
theorem caseI_antiRadical_not_pth_power_of_FLT
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) :
    γ ^ p ≠ BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab := by
  have hc : ¬ (p : ℤ) ∣ c := by
    intro hc_div
    apply hcaseI
    exact dvd_mul_of_dvd_right hc_div _
  have h_a_plus_b : ¬ (p : ℤ) ∣ (a + b) :=
    BernoulliRegular.FLT37.fltCaseI_p_not_dvd_a_add_b (p := p) heq hc
  exact caseI_antiRadical_not_pth_power_clean (p := p) (K := K)
    hp_odd hcaseI h_a_plus_b hζ hab γ

/-- **Full AK-chain consumer: AK-5a+5b + AK-5c → IsUnramified L/K**, with
non-p-th-power and irreducibility baked in from the FLT case-I equation.

This is the cleanest API form, requiring only:
- `h_unit_form` (AK-5a + AK-5b output): `algebraMap u · γ^p = antiRadical K a b ζ hab`.
- `hcong` (AK-5c output): `(ζ-1)^p ∣ u - 1`.

The non-p-th-power side (`hu_no_root`) is discharged via
`caseI_antiRadical_not_pth_power_of_FLT` composed with `h_unit_form` (any K-root
of the unit form gives a K-root of antiRadical, contradicting the universal
non-p-th-power result).

The irreducibility (`h_irr`) of `X^p - C antiRadical` follows from the universal
non-p-th-power result via `Polynomial.X_pow_sub_C_irreducible_of_prime`. -/
theorem antiKummerLift_isUnramified_via_AK5_of_FLT
    (hp_odd : p ≠ 2) (hp_pos : 0 < p)
    (hK_prim : (primitiveRoots p K).Nonempty)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' p)
    (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * (γ ^ p) =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
    (hcong : (hζ'.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) :
    Algebra.Unramified (𝓞 K)
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
      (p := p) K
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.caseI_antiRadical_ne_zero
        (K := K) hp_odd hcaseI hζ hab))) := by
  have hu_no_root : ∀ v : K, v ^ p ≠ ((u : 𝓞 K) : K) := by
    intro v hv
    have h_prod : (v * γ) ^ p =
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab := by
      rw [mul_pow, hv, h_unit_form]
    exact caseI_antiRadical_not_pth_power_of_FLT
      hp_odd heq hcaseI hζ hab (v * γ) h_prod
  have h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro γ' hγ'
    exact caseI_antiRadical_not_pth_power_of_FLT
      hp_odd heq hcaseI hζ hab γ' hγ'
  exact antiKummerLift_isUnramified_via_AK5 (K := K) (p := p)
    hp_odd hp_pos hK_prim a b ζ hab _ γ hγ_ne hζ' u h_unit_form hcong hu_no_root h_irr

/-- **`CaseIAntiKummerLKUnramified` (at p = 37) from universal AK-5a/5b + AK-5c
output**. Composes `antiKummerLift_isUnramified_via_AK5_of_FLT` (per-case, FLT-clean)
with universal quantification over case-I FLT data + AK-5b + AK-5c data.

The hypothesis `h_AK5` packages: for every case-I FLT solution and every
primitive 37th root in K, there exist a non-zero `γ : K` and a unit `u`
satisfying the AK-5a+5b unit form and the AK-5c strong primarity.

Once `h_AK5` is discharged (via AK-5a Hilbert 92 + AK-5b unit extraction +
AK-5c Wieferich lifting), `CaseIAntiKummerLKUnramified` follows unconditionally. -/
theorem caseIAntiKummerLKUnramified_of_AK5_universal
    (h_AK5 : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1)) :
    CaseIAntiKummerLKUnramified := by
  intro a b c heq hcaseI ζ hζ hab
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨ζ', hζ'⟩ : (primitiveRoots 37 (CyclotomicField 37 ℚ)).Nonempty :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (B := CyclotomicField 37 ℚ)
      (Set.mem_singleton 37) (by decide : (37 : ℕ) ≠ 0)
      |>.imp fun _ h => (mem_primitiveRoots (by decide : 0 < 37)).mpr h
  obtain ⟨γ, hγ_ne, u, h_unit_form, hcong⟩ := h_AK5 heq hcaseI hζ hab
    ((mem_primitiveRoots (by decide : 0 < 37)).mp hζ')
  exact antiKummerLift_isUnramified_via_AK5_of_FLT
    (by decide : (37 : ℕ) ≠ 2) (by decide : 0 < 37)
    ⟨ζ', hζ'⟩ heq hcaseI hζ hab γ hγ_ne
    ((mem_primitiveRoots (by decide : 0 < 37)).mp hζ') u h_unit_form hcong

/-- **Stage 2 from AK-5a plus the extracted-unit `p`-congruence.**

This is the direct Stage 2 bridge for the remaining case-I work.  AK-5a gives
principality of `I / σI`, `antiRadical_unit_form_of_principal` extracts the
unit form `α₀ = u * γ^p`, and the explicit congruence input
`(p : 𝓞 K) ∣ u - 1` is converted to strong primarity by `AK5c`.

The theorem deliberately exposes the congruence producer as a concrete
assumption on the extracted AK-5b unit; it does not package that missing
mathematical step as a new opaque source theorem. -/
theorem stage2KummerRatioK_of_AK5a_and_extracted_unit_p_congr
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    (h_VC : ¬ (p : ℕ) ∣ hPlus K)
    (h_AK5a : AK5a_PrincipalMinusIdeals (p := p) (K := K))
    (h_unit_p_congr : ∀ {a b c : ℤ}
      (_heq : a ^ p + b ^ p = c ^ p)
      (_hcaseI : ¬ (p : ℤ) ∣ a * b * c)
      {ζ : 𝓞 K} (_hζ : IsPrimitiveRoot ζ p)
      (hab : ¬ (a = 0 ∧ b = 0))
      (I : Ideal (𝓞 K)) (_hI_ne : I ≠ ⊥)
      (_hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
      (γ : K) (_hγ_ne : γ ≠ 0)
      (_hγ_principal :
        (I : FractionalIdeal (𝓞 K)⁰ K) /
          (I.map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
            FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ γ)
      (u : (𝓞 K)ˣ)
      (_h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab),
      (p : 𝓞 K) ∣ (↑u : 𝓞 K) - 1) :
    Stage2KummerRatioK p K := by
  intro a b c _hgcd hcaseI heq ζ hζ I hI_ne hI_pow
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hab : ¬ (a = 0 ∧ b = 0) := by
    intro ⟨ha, _hb⟩
    apply hcaseI
    rw [ha]
    ring_nf
    exact ⟨0, rfl⟩
  by_cases h_pow :
      ∃ β : K, β ^ p =
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab
  · obtain ⟨β, hβ⟩ := h_pow
    exact stage2_conclusion_of_antiRadical_is_pth_power
      (K := K) hp_odd hcaseI hζ hab hβ
  · have h_irr : Irreducible (Polynomial.X ^ p -
        Polynomial.C
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab)
          : Polynomial K) := by
      rw [X_pow_sub_C_irreducible_iff_not_pth_power (K := K) hp_odd]
      intro β hβ
      exact h_pow ⟨β, hβ⟩
    have hζK : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
      hζ.map_of_injective RingOfIntegers.coe_injective
    obtain ⟨γ, hγ_ne, hγ_principal⟩ :=
      h_AK5a _hgcd hcaseI heq hζ hab hI_ne hI_pow
    obtain ⟨u, h_unit_form⟩ :=
      antiRadical_unit_form_of_principal (K := K) (p := p)
        a b ζ hab I hI_pow γ hγ_principal
    have hcong_p : (p : 𝓞 K) ∣ (↑u : 𝓞 K) - 1 :=
      h_unit_p_congr heq hcaseI hζ hab I hI_ne hI_pow γ hγ_ne hγ_principal
        u h_unit_form
    have hstrong :
        ((hζK.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) :=
      AK5c_Wieferich_lifting_of_p_dvd (K := K) hp_odd hcong_p hζK
    have h_LK_unram : Algebra.Unramified (𝓞 K)
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := p) K
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab)
          (caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab))) := by
      exact antiKummerLift_isUnramified_via_AK5_of_FLT
        (K := K) (p := p) hp_odd hp_pos
        ⟨algebraMap (𝓞 K) K ζ, (mem_primitiveRoots hp_pos).mpr hζK⟩
        heq hcaseI hζ hab γ hγ_ne hζK u h_unit_form hstrong
    exfalso
    exact caseI_FLT_false_of_h_irr_h_LK_unram_VC
      (K := K) hp_odd hp_ne_three h_VC hcaseI hζ hab h_irr h_LK_unram

/-- **Stage 2 from direct AK-5 unit-form data plus `p`-congruence.**

This variant is useful when the AK-5a principality step and AK-5b extraction
have already been composed outside this file.  The input gives, for every
actual case-I factor ideal, a non-zero `γ` and a unit `u` such that
`α₀ = u * γ^p`, together with the exact AK-5c input
`(p : 𝓞 K) ∣ u - 1`.

The proof is the same non-p-th-power branch used by
`stage2KummerRatioK_of_AK5a_and_extracted_unit_p_congr`: the p-congruence is
upgraded to strong primarity by the shipped Wieferich lift, the AK-5 chain
shows the anti-Kummer extension is unramified, and Hilbert-94/Vandiver
contradicts the non-p-th-power branch under `¬ p ∣ hPlus`. -/
theorem stage2KummerRatioK_of_AK5_unit_form_and_p_congr
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    (h_VC : ¬ (p : ℕ) ∣ hPlus K)
    (h_AK5 : ∀ {a b c : ℤ}
      (_heq : a ^ p + b ^ p = c ^ p)
      (_hcaseI : ¬ (p : ℤ) ∣ a * b * c)
      {ζ : 𝓞 K} (_hζ : IsPrimitiveRoot ζ p)
      (hab : ¬ (a = 0 ∧ b = 0))
      (I : Ideal (𝓞 K)) (_hI_ne : I ≠ ⊥)
      (_hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p),
      ∃ (γ : K) (_hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ),
        algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab ∧
        (p : 𝓞 K) ∣ (↑u : 𝓞 K) - 1) :
    Stage2KummerRatioK p K := by
  intro a b c _hgcd hcaseI heq ζ hζ I hI_ne hI_pow
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hab : ¬ (a = 0 ∧ b = 0) := by
    intro ⟨ha, _hb⟩
    apply hcaseI
    rw [ha]
    ring_nf
    exact ⟨0, rfl⟩
  by_cases h_pow :
      ∃ β : K, β ^ p =
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab
  · obtain ⟨β, hβ⟩ := h_pow
    exact stage2_conclusion_of_antiRadical_is_pth_power
      (K := K) hp_odd hcaseI hζ hab hβ
  · have h_irr : Irreducible (Polynomial.X ^ p -
        Polynomial.C
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab)
          : Polynomial K) := by
      rw [X_pow_sub_C_irreducible_iff_not_pth_power (K := K) hp_odd]
      intro β hβ
      exact h_pow ⟨β, hβ⟩
    have hζK : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
      hζ.map_of_injective RingOfIntegers.coe_injective
    obtain ⟨γ, hγ_ne, u, h_unit_form, hcong_p⟩ :=
      h_AK5 heq hcaseI hζ hab I hI_ne hI_pow
    have hstrong :
        ((hζK.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) :=
      AK5c_Wieferich_lifting_of_p_dvd (K := K) hp_odd hcong_p hζK
    have h_LK_unram : Algebra.Unramified (𝓞 K)
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := p) K
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab)
          (caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab))) := by
      exact antiKummerLift_isUnramified_via_AK5_of_FLT
        (K := K) (p := p) hp_odd hp_pos
        ⟨algebraMap (𝓞 K) K ζ, (mem_primitiveRoots hp_pos).mpr hζK⟩
        heq hcaseI hζ hab γ hγ_ne hζK u h_unit_form hstrong
    exfalso
    exact caseI_FLT_false_of_h_irr_h_LK_unram_VC
      (K := K) hp_odd hp_ne_three h_VC hcaseI hζ hab h_irr h_LK_unram

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **Cyclotomic Stage 2 from direct AK-5 unit-form data plus `p`-congruence.**

This is the direct `K = ℚ(ζ_p)` form of
`stage2KummerRatioK_of_AK5_unit_form_and_p_congr`.  It exposes the remaining
case-I mathematical target at the AK-5b/AK-5c surface: for each actual case-I
factor ideal, produce the AK-5 unit form `α₀ = u * γ^p` and the congruence
`u ≡ 1 mod p`. -/
theorem stage2KummerRatioK_of_AK5_unit_form_and_p_congr_cyclotomic
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    (h_VC : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_AK5 : ∀ {a b c : ℤ}
      (_heq : a ^ p + b ^ p = c ^ p)
      (_hcaseI : ¬ (p : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField p ℚ)} (_hζ : IsPrimitiveRoot ζ p)
      (hab : ¬ (a = 0 ∧ b = 0))
      (I : Ideal (𝓞 (CyclotomicField p ℚ))) (_hI_ne : I ≠ ⊥)
      (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) +
        ζ * (b : 𝓞 (CyclotomicField p ℚ))} :
          Set (𝓞 (CyclotomicField p ℚ))) = I ^ p),
      ∃ (γ : CyclotomicField p ℚ) (_hγ_ne : γ ≠ 0)
        (u : (𝓞 (CyclotomicField p ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          (u : 𝓞 (CyclotomicField p ℚ)) * γ ^ p =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField p ℚ) a b ζ hab ∧
        (p : 𝓞 (CyclotomicField p ℚ)) ∣
          (↑u : 𝓞 (CyclotomicField p ℚ)) - 1) :
    Stage2KummerRatioK p (CyclotomicField p ℚ) := by
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  intro a b c hgcd hcaseI heq ζ hζ I hI_ne hI_pow
  exact
    (stage2KummerRatioK_of_AK5_unit_form_and_p_congr
      (K := CyclotomicField p ℚ) hp_odd hp_ne_three h_VC h_AK5)
      hgcd hcaseI heq hζ hI_ne hI_pow

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **Halving exponents for primitive roots at odd prime level.**

If `ζ` is a primitive `p`-th root and `2 < p`, then every power `ζ^q` is an
even power of `ζ`.  This is the only modular arithmetic needed to cancel the
AK-5b root-of-unity factor by the Stage 2 normalization `ζ^k`. -/
theorem exists_half_exponent_pow_eq
    (hp_two : 2 < p) {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (q : ℕ) :
    ∃ k : ℕ, k < p ∧ ζ ^ (2 * k) = ζ ^ q := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hp_two) h_dvd
  let k : ℕ := (((2 : ZMod p)⁻¹ * (q : ZMod p)).val)
  refine ⟨k, ZMod.val_lt _, ?_⟩
  have hk_zmod : ((2 * k : ℕ) : ZMod p) = (q : ZMod p) := by
    simp only [k, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    rw [← mul_assoc, mul_inv_cancel₀ htwo_ne, one_mul]
  have hk_mod : 2 * k ≡ q [MOD p] :=
    (ZMod.natCast_eq_natCast_iff (2 * k) q p).mp hk_zmod
  exact pow_eq_pow_of_modEq hk_mod hζ.pow_eq_one

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Effect of Stage 2 normalization on the σ-anti radical.**

Multiplying the case-I factor `a + ζb` by `ζ^k` multiplies the Kummer ratio
`α/σ(α)` by `ζ^(2k)`.  This is the formal bridge that lets the later AK-5b
root-of-unity factor be cancelled by choosing the normalization exponent. -/
theorem normalized_antiRadical_ratio_eq_zeta_sq_mul
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0)) (k : ℕ) :
    (algebraMap (𝓞 K) K
      (ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K)))) /
    (algebraMap (𝓞 K) K
      (NumberField.IsCMField.ringOfIntegersComplexConj K
        (ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K))))) =
      (algebraMap (𝓞 K) K ζ) ^ (2 * k) *
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab := by
  let A : 𝓞 K := (a : 𝓞 K) + ζ * (b : 𝓞 K)
  have hζK_ne : algebraMap (𝓞 K) K ζ ≠ 0 := by
    intro h0
    have hpow := congrArg (algebraMap (𝓞 K) K) hζ.pow_eq_one
    rw [map_pow, h0, zero_pow hp.out.ne_zero, map_one] at hpow
    exact zero_ne_one hpow
  have hdenom : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K A) ≠ 0 := by
    simpa [A] using
      caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ
  have hconjζ :
      NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) =
        (algebraMap (𝓞 K) K ζ)⁻¹ :=
    complexConj_K_apply_primRoot_eq_inv (K := K) hζ
  have hconj_norm :
      algebraMap (𝓞 K) K
          (NumberField.IsCMField.ringOfIntegersComplexConj K (ζ ^ k * A)) =
        (algebraMap (𝓞 K) K ζ)⁻¹ ^ k *
          NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K A) := by
    change ((NumberField.IsCMField.ringOfIntegersComplexConj K (ζ ^ k * A) : 𝓞 K) : K) =
      (algebraMap (𝓞 K) K ζ)⁻¹ ^ k *
        NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K A)
    rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    change NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K (ζ ^ k * A)) =
      (algebraMap (𝓞 K) K ζ)⁻¹ ^ k *
        NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K A)
    rw [show algebraMap (𝓞 K) K (ζ ^ k * A) =
        (algebraMap (𝓞 K) K ζ) ^ k * algebraMap (𝓞 K) K A by
      rw [map_mul, map_pow]]
    rw [map_mul, map_pow, hconjζ]
  unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
  change algebraMap (𝓞 K) K (ζ ^ k * A) /
      algebraMap (𝓞 K) K
        (NumberField.IsCMField.ringOfIntegersComplexConj K (ζ ^ k * A)) =
    (algebraMap (𝓞 K) K ζ) ^ (2 * k) *
      (algebraMap (𝓞 K) K A /
        NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K A))
  rw [map_mul, map_pow, hconj_norm]
  rw [inv_pow]
  field_simp [hζK_ne, hdenom]
  rw [pow_mul]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **AK-5b output σ-anti structure**: from the unit form `algebraMap u · γ^p = α₀`
(AK-5b output) and the σ-anti property `σ(α₀) = α₀^(-1)` (case-I antiRadical),
the extracted unit `u` and the K-element `γ` satisfy a σ-anti relation:

`algebraMap (σ(u) · u) · (σ(γ) · γ)^p = 1` in K.

This is the structural starting point for AK-5c: it says the unit `σ(u) · u`
(which is real, i.e., in `(𝓞 K⁺)ˣ`) is a `(-p)`-th power of `σ(γ) · γ` (which
is also real, in `(K⁺)^×`). Combined with p-saturation of real units under VC
(Sinnott index formula), this provides the bridge to deriving `p ∣ u - 1` for
the AK-5c Wieferich lifting hypothesis. -/
theorem AK5b_sigma_anti_unit_relation
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    algebraMap (𝓞 K) K
      ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) *
        (NumberField.IsCMField.complexConj K γ * γ) ^ p = 1 := by
  have h_denom_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0 :=
    caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ
  have h_anti :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical_sigma_inv
      (K := K) a b ζ hab h_denom_nz
  have h_apply_sigma : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p) =
      NumberField.IsCMField.complexConj K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) := by
    rw [h_unit_form]
  rw [h_anti, map_mul, map_pow] at h_apply_sigma
  have h_bridge : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K (u : 𝓞 K)) =
      algebraMap (𝓞 K) K
        ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K)) := by
    exact (NumberField.IsCMField.coe_ringOfIntegersComplexConj K _).symm
  rw [h_bridge] at h_apply_sigma
  have h_prod := congrArg₂ (· * ·) h_unit_form h_apply_sigma
  have h_α₀_ne : BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ 0 :=
    caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab
  rw [mul_inv_cancel₀ h_α₀_ne] at h_prod
  rw [map_mul, mul_pow]
  linear_combination h_prod

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **σ(u) · u is a p-th power in K^×**: corollary of
`AK5b_sigma_anti_unit_relation`. From the AK-5b unit form, the σ-fixed real
combination `σ(u) · u` (lifted to K) admits an explicit p-th root, namely
`(σ(γ) · γ)^(-1)`.

This is the first step of the AK-5c bridge: the Norm-type product `σ(u) · u`
is a p-th power in K^×. The next step (integral closure on `(σγ·γ)^(-1)`)
shows it's a p-th power in `(𝓞 K⁺)ˣ`, which under Kummer's classical lemma
for real units gives `u` is congruent to an integer mod `p`, the AK-5c
Wieferich input. -/
theorem AK5b_sigma_anti_unit_is_pth_power_in_K
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ w : K, w ^ p =
      algebraMap (𝓞 K) K
        ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) := by
  have h_rel := AK5b_sigma_anti_unit_relation (K := K)
    hp_odd hcaseI hζ hab γ u h_unit_form
  refine ⟨(NumberField.IsCMField.complexConj K γ * γ)⁻¹, ?_⟩
  have hσγ_ne : NumberField.IsCMField.complexConj K γ ≠ 0 := by
    intro h
    apply hγ_ne
    have := congrArg (NumberField.IsCMField.complexConj K) h
    rwa [NumberField.IsCMField.complexConj_apply_apply, map_zero] at this
  have h_σγ_γ_ne : NumberField.IsCMField.complexConj K γ * γ ≠ 0 :=
    mul_ne_zero hσγ_ne hγ_ne
  have h_pow_ne : (NumberField.IsCMField.complexConj K γ * γ) ^ p ≠ 0 :=
    pow_ne_zero _ h_σγ_γ_ne
  rw [show ((NumberField.IsCMField.complexConj K γ * γ)⁻¹) ^ p =
      ((NumberField.IsCMField.complexConj K γ * γ) ^ p)⁻¹ from inv_pow _ _]
  apply mul_left_cancel₀ h_pow_ne
  rw [mul_inv_cancel₀ h_pow_ne, ← h_rel, mul_comm]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(σ(γ)·γ)⁻¹` is integral over 𝓞K**: corollary of
`AK5b_sigma_anti_unit_is_pth_power_in_K`. Since `((σγ·γ)⁻¹)^p = σ(u)·u ∈ 𝓞K`,
the K-element `(σγ·γ)⁻¹` is a root of the monic polynomial
`X^p - C (σ(u)·u) ∈ 𝓞K[X]`, hence integral over 𝓞K.

Combined with integral closure of 𝓞K in K, this shows `(σγ·γ)⁻¹ ∈ 𝓞K`, and
combined with σ-fixedness, in `𝓞K⁺`. The induced real unit
`v := (σγ·γ)⁻¹` satisfies `v^p = σ(u)·u`, providing the entry point to
Kummer's classical lemma for the AK-5c Wieferich bridge. -/
theorem AK5b_sigma_gamma_inv_isIntegral
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    IsIntegral (𝓞 K) (NumberField.IsCMField.complexConj K γ * γ)⁻¹ := by
  have h_rel := AK5b_sigma_anti_unit_relation (K := K)
    hp_odd hcaseI hζ hab γ u h_unit_form
  have hσγ_ne : NumberField.IsCMField.complexConj K γ ≠ 0 := by
    intro h
    apply hγ_ne
    have := congrArg (NumberField.IsCMField.complexConj K) h
    rwa [NumberField.IsCMField.complexConj_apply_apply, map_zero] at this
  have h_σγ_γ_ne : NumberField.IsCMField.complexConj K γ * γ ≠ 0 :=
    mul_ne_zero hσγ_ne hγ_ne
  have h_pow_ne : (NumberField.IsCMField.complexConj K γ * γ) ^ p ≠ 0 :=
    pow_ne_zero _ h_σγ_γ_ne
  refine ⟨Polynomial.X ^ p - Polynomial.C
    ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [show ((NumberField.IsCMField.complexConj K γ * γ)⁻¹) ^ p =
        ((NumberField.IsCMField.complexConj K γ * γ) ^ p)⁻¹ from inv_pow _ _]
    apply sub_eq_zero.mpr
    apply mul_left_cancel₀ h_pow_ne
    rw [mul_inv_cancel₀ h_pow_ne, ← h_rel, mul_comm]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(σ(γ)·γ)⁻¹` lifts to 𝓞K** (from AK-5b unit form + integral closure).

Composes `AK5b_sigma_gamma_inv_isIntegral` (integral over 𝓞K) with transitivity
(integral over ℤ via 𝓞K integral over ℤ) and the construction of an element
of 𝓞K from an integral-over-ℤ K-element.

The resulting `v : 𝓞K` is σ-fixed (since `(σγ·γ)⁻¹` is σ-fixed in K), hence
lies in `𝓞K⁺` via the K⁺ embedding. The next step (Kummer's classical lemma)
uses this to derive `v ≡ rational integer mod p` and then connects to `u`. -/
theorem AK5b_sigma_gamma_inv_in_ringOfIntegers
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ v : 𝓞 K, (v : K) = (NumberField.IsCMField.complexConj K γ * γ)⁻¹ := by
  have h_int := AK5b_sigma_gamma_inv_isIntegral (K := K)
    hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  have h_int_Z : IsIntegral ℤ (NumberField.IsCMField.complexConj K γ * γ)⁻¹ :=
    isIntegral_trans (R := ℤ) (A := 𝓞 K) (B := K)
      (NumberField.IsCMField.complexConj K γ * γ)⁻¹ h_int
  exact ⟨⟨_, h_int_Z⟩, rfl⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(σγ·γ)⁻¹` lifts to a σ-fixed (real) element of 𝓞K**. Extends
`AK5b_sigma_gamma_inv_in_ringOfIntegers` with the σ-fixedness witness:
since `(σγ·γ)⁻¹` is σ-fixed in K (because `(σγ·γ)` is σ-fixed),
the lift `v : 𝓞K` is also σ-fixed, hence lies in the real subring. -/
theorem AK5b_sigma_gamma_inv_real_in_ringOfIntegers
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ v : 𝓞 K,
      (v : K) = (NumberField.IsCMField.complexConj K γ * γ)⁻¹ ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K v = v := by
  obtain ⟨v, hv⟩ := AK5b_sigma_gamma_inv_in_ringOfIntegers
    (K := K) hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  refine ⟨v, hv, ?_⟩
  apply RingOfIntegers.ext
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj, hv,
      map_inv₀, map_mul, NumberField.IsCMField.complexConj_apply_apply]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(σγ·γ)⁻¹` lifts to a σ-fixed unit `v ∈ (𝓞 K)ˣ`** with `v^p = σ(u)·u` in K.

Extends `AK5b_sigma_gamma_inv_real_in_ringOfIntegers` by upgrading the lift from
a 𝓞K element to a unit, using that `v^p = σ(u)·u ∈ (𝓞K)ˣ` (a unit), hence v is
a unit (via `isUnit_pow_iff`).

The conclusion is the structural data for the AK-5c Wieferich bridge: a real
unit `v` whose p-th power equals the σ-fixed combination `σ(u)·u` of the
extracted AK-5b unit. -/
theorem AK5b_sigma_gamma_inv_unit
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ v : (𝓞 K)ˣ,
      ((v : 𝓞 K) : K) = (NumberField.IsCMField.complexConj K γ * γ)⁻¹ ∧
      ((v : 𝓞 K) : K) ^ p =
        algebraMap (𝓞 K) K
          ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) := by
  obtain ⟨v, hv⟩ := AK5b_sigma_gamma_inv_in_ringOfIntegers
    (K := K) hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  have h_rel := AK5b_sigma_anti_unit_relation (K := K)
    hp_odd hcaseI hζ hab γ u h_unit_form
  have hσγ_ne : NumberField.IsCMField.complexConj K γ ≠ 0 := by
    intro h
    apply hγ_ne
    have := congrArg (NumberField.IsCMField.complexConj K) h
    rwa [NumberField.IsCMField.complexConj_apply_apply, map_zero] at this
  have h_pow_ne : (NumberField.IsCMField.complexConj K γ * γ) ^ p ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hσγ_ne hγ_ne)
  have h_v_pth : ((v : K)) ^ p = algebraMap (𝓞 K) K
        ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) := by
    rw [hv,
        show ((NumberField.IsCMField.complexConj K γ * γ)⁻¹) ^ p =
          ((NumberField.IsCMField.complexConj K γ * γ) ^ p)⁻¹ from inv_pow _ _]
    apply mul_left_cancel₀ h_pow_ne
    rw [mul_inv_cancel₀ h_pow_ne, ← h_rel, mul_comm]
  have h_v_pow_unit : IsUnit (v ^ p) := by
    have h_int_eq : (v ^ p : 𝓞 K) =
        ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) := by
      apply RingOfIntegers.ext
      push_cast
      rw [h_v_pth, map_mul]
    rw [h_int_eq]
    have h_σu_unit : IsUnit (NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K)) :=
      MulEquiv.isUnit_map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toMulEquiv
        |>.mpr u.isUnit
    exact IsUnit.mul h_σu_unit u.isUnit
  have h_v_unit : IsUnit v :=
    (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp h_v_pow_unit
  refine ⟨h_v_unit.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]; exact hv
  · simp only [IsUnit.unit_spec]; exact h_v_pth

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(σγ·γ)⁻¹` lifts to a σ-fixed (real) unit in `(𝓞K)ˣ`**: combines
`AK5b_sigma_gamma_inv_unit` (unit lift) with σ-fixedness witness at the unit
level.

Once σ-fixedness at the unit level is established, `unitsComplexConj_eq_self_iff`
gives `v ∈ realUnits K`, and `mem_realUnits_iff` produces the K⁺-side preimage
`v_plus : (𝓞K⁺)ˣ` with `algebraMap v_plus = v`. -/
theorem AK5b_sigma_gamma_inv_real_unit
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ v : (𝓞 K)ˣ, NumberField.IsCMField.unitsComplexConj K v = v ∧
      ((v : 𝓞 K) : K) ^ p =
        algebraMap (𝓞 K) K
          ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) := by
  obtain ⟨v, hv_K, hv_pow⟩ := AK5b_sigma_gamma_inv_unit (K := K)
    hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  refine ⟨v, ?_, hv_pow⟩
  apply Units.ext
  show (NumberField.IsCMField.ringOfIntegersComplexConj K (v : 𝓞 K) : 𝓞 K) = (v : 𝓞 K)
  apply RingOfIntegers.ext
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj, hv_K,
      map_inv₀, map_mul, NumberField.IsCMField.complexConj_apply_apply]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(σγ·γ)⁻¹` descends to a real unit `v_plus : (𝓞K⁺)ˣ`** with
`algebraMap v_plus = v` in `(𝓞K)ˣ`, where v is the σ-fixed unit lift from
`AK5b_sigma_gamma_inv_real_unit`.

Composition with `unitsComplexConj_eq_self_iff` and `mem_realUnits_iff`. The
output v_plus is the concrete K⁺-side real unit whose K-image satisfies
`algebraMap v_plus ^ p = σ(u)·u` in (𝓞K)ˣ. -/
theorem AK5b_sigma_gamma_inv_real_unit_descent
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (v_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ) (v : (𝓞 K)ˣ),
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
          v_plus = v ∧
      ((v : 𝓞 K) : K) ^ p =
        algebraMap (𝓞 K) K
          ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) := by
  obtain ⟨v, hv_fixed, hv_pow⟩ := AK5b_sigma_gamma_inv_real_unit (K := K)
    hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  have h_v_in : v ∈ NumberField.IsCMField.realUnits K :=
    (NumberField.IsCMField.unitsComplexConj_eq_self_iff (K := K) v).mp hv_fixed
  obtain ⟨v_plus, hv_plus⟩ := (NumberField.IsCMField.mem_realUnits_iff (K := K) v).mp h_v_in
  refine ⟨v_plus, v, ?_, hv_pow⟩
  apply Units.ext
  simp [Units.coe_map, hv_plus]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Integer-level σ(u)·u = (algebraMap v_plus)^p**: the clean integer-level
form of the AK-5b → real-unit descent. Produces v_plus : (𝓞K⁺)ˣ such that
`(algebraMap v_plus)^p = σ(u)·u` in `𝓞K`.

This is the cleanest entry point for the AK-5c Wieferich bridge: a concrete
real unit v_plus whose p-th power equals the σ-fixed combination σ(u)·u of
the AK-5b extracted unit. Subsequent steps (Kummer's classical lemma) would
derive v_plus ≡ rational integer mod p, then combine with σ-anti structure
of u to derive u ≡ rational integer mod p, finally invoking
`AK5c_Wieferich_lifting_of_int_congr`. -/
theorem AK5b_sigma_anti_unit_eq_real_unit_pow
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ v_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) v_plus)^p =
        ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K) : 𝓞 K) := by
  obtain ⟨v_plus, v, h_alg_eq, h_v_pow⟩ :=
    AK5b_sigma_gamma_inv_real_unit_descent
      (K := K) hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  refine ⟨v_plus, ?_⟩
  have h_alg_int : (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) v_plus) =
      (v : 𝓞 K) := by
    have := congrArg (fun w : (𝓞 K)ˣ => (w : 𝓞 K)) h_alg_eq
    simpa using this
  rw [h_alg_int]
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  push_cast
  exact h_v_pow

/-- **σ-anti units in `(𝓞 K)ˣ` decompose as `ζ^m · alg s` with `s^2 = 1`**.

For `μ ∈ (𝓞 K)ˣ` σ-anti (i.e., `unitsComplexConj K μ = μ⁻¹`), the
decomposition `μ = ζ^m · algebraMap s` from `exists_zeta_pow_mul_real_eq_unit`
forces `s : (𝓞 K⁺)ˣ` to satisfy `s² = 1`. So σ-anti units are precisely
the 2p-th roots of unity in `(𝓞 K)ˣ`.

This is the structural fact underlying the AK chain: the σ-anti unit
`μ = σ(u)·u⁻¹` (for u from AK-5b extraction) is necessarily a 2p-th root
of unity, which constrains u modulo p-th powers strongly. -/
theorem sigma_anti_unit_decomposition
    (hp_two : 2 < p)
    {μ : (𝓞 K)ˣ}
    (hμ_anti : NumberField.IsCMField.unitsComplexConj K μ = μ⁻¹) :
    ∃ (m : ℕ) (s : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      μ = ζcu ^ m *
        Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom s ∧
      s ^ 2 = 1 := by
  obtain ⟨m, s, hs⟩ :=
    BernoulliRegular.FLT37.exists_zeta_pow_mul_real_eq_unit (K := K) (p := p) hp_two μ
  refine ⟨m, s, hs, ?_⟩
  set ζU : (𝓞 K)ˣ := ζcu with hζU_def
  set algS : (𝓞 K)ˣ := Units.map
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom s with halgS_def
  have h_ζ_torsion : ζU ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.1.pos,
        ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit hp.1.ne_zero).pow_eq_one⟩)
  have h_σ_ζ : NumberField.IsCMField.unitsComplexConj K ζU = ζU⁻¹ :=
    NumberField.IsCMField.unitsComplexConj_torsion (K := K) ⟨ζU, h_ζ_torsion⟩
  have h_σ_ζ_pow : NumberField.IsCMField.unitsComplexConj K (ζU ^ m) = ζU⁻¹ ^ m := by
    rw [map_pow, h_σ_ζ]
  have h_algS_in_real : algS ∈ NumberField.IsCMField.realUnits K := ⟨s, rfl⟩
  have h_σ_algS : NumberField.IsCMField.unitsComplexConj K algS = algS :=
    (NumberField.IsCMField.unitsComplexConj_eq_self_iff (K := K) algS).mpr h_algS_in_real
  rw [hs] at hμ_anti
  rw [map_mul, h_σ_ζ_pow, h_σ_algS, mul_inv, ← inv_pow] at hμ_anti
  have h_algS_eq : algS = algS⁻¹ :=
    mul_left_cancel hμ_anti
  have h_algS_sq : algS * algS = 1 := by
    nth_rewrite 2 [h_algS_eq]
    exact mul_inv_cancel _
  have h_unit_alg_inj : Function.Injective
      (Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom) :=
    Units.map_injective (FaithfulSMul.algebraMap_injective _ _)
  apply h_unit_alg_inj
  rw [map_pow]
  show algS ^ 2 = (Units.map _) 1
  rw [map_one, sq]
  exact h_algS_sq

/-- **AK-5b extracted unit `u` has σ-anti ratio in 2p-th roots of unity**:
the unit `μ := σ(u)·u⁻¹` arising from any unit `u ∈ (𝓞K)ˣ` (no hypothesis
needed) is automatically σ-anti, and by `sigma_anti_unit_decomposition` it
decomposes as `ζ^m · algebraMap s` with `s² = 1`.

This is the structural fact about AK-5b extracted units that's needed for
proving u is constrained modulo p-th powers (toward the AK-5c bridge). -/
theorem AK5b_unit_sigma_anti_ratio_decomposition
    (hp_two : 2 < p)
    (u : (𝓞 K)ˣ) :
    ∃ (m : ℕ) (s : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      NumberField.IsCMField.unitsComplexConj K u * u⁻¹ =
        ζcu ^ m *
          Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom s ∧
      s ^ 2 = 1 := by
  set μ := NumberField.IsCMField.unitsComplexConj K u * u⁻¹ with hμ_def
  have h_σ_inv : ∀ x : (𝓞 K)ˣ,
      NumberField.IsCMField.unitsComplexConj K
        (NumberField.IsCMField.unitsComplexConj K x) = x := by
    intro x
    apply Units.ext
    apply RingOfIntegers.ext
    show ((NumberField.IsCMField.ringOfIntegersComplexConj K
        (NumberField.IsCMField.ringOfIntegersComplexConj K (x : 𝓞 K))) : K) = ((x : 𝓞 K) : K)
    rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj,
        NumberField.IsCMField.coe_ringOfIntegersComplexConj,
        NumberField.IsCMField.complexConj_apply_apply]
  have hμ_anti : NumberField.IsCMField.unitsComplexConj K μ = μ⁻¹ := by
    rw [hμ_def, map_mul, map_inv, h_σ_inv]
    rw [mul_inv, mul_comm, inv_inv]
  exact sigma_anti_unit_decomposition (K := K) hp_two hμ_anti

/-- **Combined AK-5b structural data**: from the AK-5b extracted unit form, derive
both the σ-Norm p-th-power relation AND the σ-anti ratio decomposition in one
existential package.

Output:
- `m : ℕ`, `s : (𝓞K⁺)ˣ` with `s² = 1`: σ-anti ratio σ(u)·u⁻¹ = ζ^m · alg s.
- `v_plus : (𝓞K⁺)ˣ`: (alg v_plus)^p = σ(u)·u in 𝓞K.

Combining these: σ(u)² · u⁻¹ · u = σ(u)·u · σ(u)·u⁻¹ = (alg v_plus)^p · ζ^m · alg s.
So σ(u)² = ζ^m · alg(s · v_plus^p) in (𝓞K)ˣ. Since s² = 1 and 2 ⨯ p odd are
coprime, this gives a strong constraint on σ(u), hence on u, modulo p-th powers. -/
theorem AK5b_combined_structural_data
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m : ℕ) (s : (𝓞 (NumberField.maximalRealSubfield K))ˣ)
      (v_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      s ^ 2 = 1 ∧
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) v_plus) ^ p =
        ((NumberField.IsCMField.ringOfIntegersComplexConj K u : 𝓞 K) * (u : 𝓞 K)) ∧
      NumberField.IsCMField.unitsComplexConj K u * u⁻¹ =
        ζcu ^ m *
          Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom s := by
  obtain ⟨v_plus, h_v_pow⟩ :=
    AK5b_sigma_anti_unit_eq_real_unit_pow
      (K := K) hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  obtain ⟨m, s, h_decomp, h_s_sq⟩ :=
    AK5b_unit_sigma_anti_ratio_decomposition (K := K) hp_two u
  exact ⟨m, s, v_plus, h_s_sq, h_v_pow, h_decomp⟩

/-- **AK-5b square constraint**: the AK-5b extracted unit has σ-square equal to
a root-of-unity factor times the image of a real unit.

This packages the two outputs of `AK5b_combined_structural_data` into the form
needed by the AK-5c congruence bridge:
`σ(u)·u = alg(v)^p` and `σ(u)·u⁻¹ = ζ^m·alg(s)` combine to
`σ(u)^2 = ζ^m·alg(s·v^p)` in `(𝓞 K)ˣ`. -/
theorem AK5b_sigma_sq_eq_zeta_mul_real_unit
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m : ℕ) (w_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      NumberField.IsCMField.unitsComplexConj K u ^ 2 =
        ζcu ^ m *
          (Units.map
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom)
            w_plus := by
  obtain ⟨m, s, v_plus, _h_s_sq, h_v_pow, h_ratio⟩ :=
    AK5b_combined_structural_data (K := K) hp_two hp_odd hcaseI hζ hab γ
      hγ_ne u h_unit_form
  let algMapUnits : (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
  refine ⟨m, s * v_plus ^ p, ?_⟩
  have h_norm_units :
      algMapUnits v_plus ^ p = NumberField.IsCMField.unitsComplexConj K u * u := by
    apply Units.ext
    exact h_v_pow
  calc
    NumberField.IsCMField.unitsComplexConj K u ^ 2
        = (NumberField.IsCMField.unitsComplexConj K u * u) *
            (NumberField.IsCMField.unitsComplexConj K u * u⁻¹) := by
          simp [sq, mul_left_comm, mul_comm]
    _ = algMapUnits v_plus ^ p *
          (ζcu ^ m * algMapUnits s) := by
          rw [h_norm_units, h_ratio]
    _ = ζcu ^ m * algMapUnits (s * v_plus ^ p) := by
          rw [map_mul, map_pow]
          simp [mul_assoc, mul_comm]

/-- **AK-5b square constraint for `u` itself**: the AK-5b extracted unit has
square equal to an inverse root-of-unity factor times the image of a real unit.

This is the conjugate companion to `AK5b_sigma_sq_eq_zeta_mul_real_unit`, derived
from the same two structural identities:
`σ(u)·u = alg(v)^p` and `σ(u)·u⁻¹ = ζ^m·alg(s)`.
It packages the form needed when the AK-5c congruence bridge works with `u`
rather than with `σ(u)`. -/
theorem AK5b_unit_sq_eq_zeta_inv_mul_real_unit
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m : ℕ) (w_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      u ^ 2 =
        (ζcu ^ m)⁻¹ *
          (Units.map
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom)
            w_plus := by
  obtain ⟨m, s, v_plus, _h_s_sq, h_v_pow, h_ratio⟩ :=
    AK5b_combined_structural_data (K := K) hp_two hp_odd hcaseI hζ hab γ
      hγ_ne u h_unit_form
  let algMapUnits : (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
  refine ⟨m, s⁻¹ * v_plus ^ p, ?_⟩
  have h_norm_units :
      algMapUnits v_plus ^ p = NumberField.IsCMField.unitsComplexConj K u * u := by
    apply Units.ext
    exact h_v_pow
  have h_ratio_inv :
      u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹ =
        (ζcu ^ m * algMapUnits s)⁻¹ := by
    calc
      u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹
          = (NumberField.IsCMField.unitsComplexConj K u * u⁻¹)⁻¹ := by
              simp [mul_comm]
      _ = (ζcu ^ m * algMapUnits s)⁻¹ := by
              rw [h_ratio]
  calc
    u ^ 2 = (NumberField.IsCMField.unitsComplexConj K u * u) *
            (u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹) := by
          simp [sq, mul_left_comm, mul_comm]
    _ = algMapUnits v_plus ^ p *
          ((ζcu ^ m * algMapUnits s)⁻¹) := by
          rw [h_norm_units, h_ratio_inv]
    _ = (ζcu ^ m)⁻¹ * algMapUnits (s⁻¹ * v_plus ^ p) := by
          rw [map_mul, map_inv, map_pow]
          simp [mul_left_comm, mul_comm]

/-- **AK-5b paired square constraints with one exponent.**

This strengthens the two separate square-constraint lemmas by producing a
single exponent `m` which works simultaneously for `σ(u)^2` and `u^2`.
Keeping the same root-of-unity exponent is the useful form for the remaining
AK-5c congruence step: it records that the conjugate pair differs only by the
inverse root-of-unity factor, up to real units. -/
theorem AK5b_paired_square_constraints
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m : ℕ)
      (w_sigma_plus w_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      NumberField.IsCMField.unitsComplexConj K u ^ 2 =
        ζcu ^ m *
          (Units.map
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom)
            w_sigma_plus ∧
      u ^ 2 =
        (ζcu ^ m)⁻¹ *
          (Units.map
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom)
            w_plus := by
  obtain ⟨m, s, v_plus, _h_s_sq, h_v_pow, h_ratio⟩ :=
    AK5b_combined_structural_data (K := K) hp_two hp_odd hcaseI hζ hab γ
      hγ_ne u h_unit_form
  let algMapUnits : (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
  refine ⟨m, s * v_plus ^ p, s⁻¹ * v_plus ^ p, ?_⟩
  have h_norm_units :
      algMapUnits v_plus ^ p = NumberField.IsCMField.unitsComplexConj K u * u := by
    apply Units.ext
    exact h_v_pow
  constructor
  · calc
      NumberField.IsCMField.unitsComplexConj K u ^ 2
          = (NumberField.IsCMField.unitsComplexConj K u * u) *
              (NumberField.IsCMField.unitsComplexConj K u * u⁻¹) := by
            simp [sq, mul_left_comm, mul_comm]
      _ = algMapUnits v_plus ^ p *
            (ζcu ^ m * algMapUnits s) := by
            rw [h_norm_units, h_ratio]
      _ = ζcu ^ m * algMapUnits (s * v_plus ^ p) := by
            rw [map_mul, map_pow]
            simp [mul_assoc, mul_comm]
  · have h_ratio_inv :
        u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹ =
          (ζcu ^ m * algMapUnits s)⁻¹ := by
      calc
        u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹
            = (NumberField.IsCMField.unitsComplexConj K u * u⁻¹)⁻¹ := by
                simp [mul_comm]
        _ = (ζcu ^ m * algMapUnits s)⁻¹ := by
                rw [h_ratio]
    calc
      u ^ 2 = (NumberField.IsCMField.unitsComplexConj K u * u) *
              (u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹) := by
            simp [sq, mul_left_comm, mul_comm]
      _ = algMapUnits v_plus ^ p *
            ((ζcu ^ m * algMapUnits s)⁻¹) := by
            rw [h_norm_units, h_ratio_inv]
      _ = (ζcu ^ m)⁻¹ * algMapUnits (s⁻¹ * v_plus ^ p) := by
            rw [map_mul, map_inv, map_pow]
            simp [mul_left_comm, mul_comm]

/-- **AK-5b paired square constraints modulo real `p`-th powers.**

The paired square constraints can be sharpened because the auxiliary real unit
`s` from the σ-anti decomposition satisfies `s^2 = 1`; since `p` is odd, this
implies `s = s^p`.  Thus the real-unit factors in the square constraints are
not merely arbitrary real units, but real `p`-th powers. -/
theorem AK5b_paired_square_constraints_mod_real_powers
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m : ℕ)
      (t_sigma_plus t_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      NumberField.IsCMField.unitsComplexConj K u ^ 2 =
        ζcu ^ m *
          ((Units.map
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom)
            t_sigma_plus) ^ p ∧
      u ^ 2 =
        (ζcu ^ m)⁻¹ *
          ((Units.map
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom)
            t_plus) ^ p := by
  obtain ⟨m, s, v_plus, h_s_sq, h_v_pow, h_ratio⟩ :=
    AK5b_combined_structural_data (K := K) hp_two hp_odd hcaseI hζ hab γ
      hγ_ne u h_unit_form
  let algMapUnits : (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd
  have h_s_pow : s ^ p = s := by
    obtain ⟨n, hn⟩ := hp_odd_nat
    rw [hn, pow_succ, pow_mul, h_s_sq, one_pow, one_mul]
  have h_s_inv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_right (by simpa [sq] using h_s_sq)
  have h_s_inv_pow : s⁻¹ ^ p = s⁻¹ := by
    rw [h_s_inv, h_s_pow]
  have h_sigma_real_pow :
      algMapUnits (s * v_plus ^ p) = (algMapUnits (s * v_plus)) ^ p := by
    rw [map_mul, map_pow, map_mul, mul_pow]
    rw [show algMapUnits s ^ p = algMapUnits (s ^ p) by rw [map_pow], h_s_pow]
  have h_real_pow :
      algMapUnits (s⁻¹ * v_plus ^ p) = (algMapUnits (s⁻¹ * v_plus)) ^ p := by
    rw [map_mul, map_pow, map_mul, mul_pow]
    rw [show algMapUnits s⁻¹ ^ p = algMapUnits (s⁻¹ ^ p) by rw [map_pow], h_s_inv_pow]
  refine ⟨m, s * v_plus, s⁻¹ * v_plus, ?_⟩
  have h_norm_units :
      algMapUnits v_plus ^ p = NumberField.IsCMField.unitsComplexConj K u * u := by
    apply Units.ext
    exact h_v_pow
  constructor
  · calc
      NumberField.IsCMField.unitsComplexConj K u ^ 2
          = (NumberField.IsCMField.unitsComplexConj K u * u) *
              (NumberField.IsCMField.unitsComplexConj K u * u⁻¹) := by
            simp [sq, mul_left_comm, mul_comm]
      _ = algMapUnits v_plus ^ p *
            (ζcu ^ m * algMapUnits s) := by
            rw [h_norm_units, h_ratio]
      _ = ζcu ^ m * algMapUnits (s * v_plus ^ p) := by
            rw [map_mul, map_pow]
            simp [mul_assoc, mul_comm]
      _ = ζcu ^ m * (algMapUnits (s * v_plus)) ^ p := by
            rw [h_sigma_real_pow]
  · have h_ratio_inv :
        u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹ =
          (ζcu ^ m * algMapUnits s)⁻¹ := by
      calc
        u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹
            = (NumberField.IsCMField.unitsComplexConj K u * u⁻¹)⁻¹ := by
                simp [mul_comm]
        _ = (ζcu ^ m * algMapUnits s)⁻¹ := by
                rw [h_ratio]
    calc
      u ^ 2 = (NumberField.IsCMField.unitsComplexConj K u * u) *
              (u * (NumberField.IsCMField.unitsComplexConj K u)⁻¹) := by
            simp [sq, mul_left_comm, mul_comm]
      _ = algMapUnits v_plus ^ p *
            ((ζcu ^ m * algMapUnits s)⁻¹) := by
            rw [h_norm_units, h_ratio_inv]
      _ = (ζcu ^ m)⁻¹ * algMapUnits (s⁻¹ * v_plus ^ p) := by
            rw [map_mul, map_inv, map_pow]
            simp [mul_left_comm, mul_comm]
      _ = (ζcu ^ m)⁻¹ * (algMapUnits (s⁻¹ * v_plus)) ^ p := by
            rw [h_real_pow]

/-- **AK-5b unit is a root-of-unity factor times a `p`-th power.**

This is the group-theoretic consequence of
`AK5b_paired_square_constraints_mod_real_powers`: from
`u^2 = (ζ^m)⁻¹ · A^p` and oddness of `p`, choose `r` with `2r = p + 1`.
Then
`u = ((ζ^m)⁻¹)^r · (A^r · u⁻¹)^p`.

The remaining AK-5c arithmetic task is to use the weak-primary case-I
normalization to force the root-of-unity factor to be trivial modulo the
required `p`-congruence. -/
theorem AK5b_unit_is_zeta_factor_times_pth_power
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m r : ℕ) (w : (𝓞 K)ˣ),
      2 * r = p + 1 ∧
      u = ((ζcu ^ m)⁻¹) ^ r * w ^ p := by
  obtain ⟨m, _t_sigma_plus, t_plus, _h_sigma_sq, h_unit_sq⟩ :=
    AK5b_paired_square_constraints_mod_real_powers
      (K := K) hp_two hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  let algMapUnits : (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
  let A : (𝓞 K)ˣ := algMapUnits t_plus
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd
  obtain ⟨n, hn⟩ := hp_odd_nat
  let r : ℕ := n + 1
  have h_two_r : 2 * r = p + 1 := by
    dsimp [r]
    omega
  refine ⟨m, r, A ^ r * u⁻¹, h_two_r, ?_⟩
  have hu_sq : u ^ 2 = (ζcu ^ m)⁻¹ * A ^ p := by
    simpa [A, algMapUnits] using h_unit_sq
  have hpow : (u ^ 2) ^ r =
      (((ζcu ^ m)⁻¹ * A ^ p) ^ r) := by
    rw [hu_sq]
  rw [← pow_mul] at hpow
  rw [h_two_r, pow_succ] at hpow
  rw [mul_pow] at hpow
  rw [show (A ^ p) ^ r = (A ^ r) ^ p by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm p r]] at hpow
  calc
    u = (u ^ p)⁻¹ * (u ^ p * u) := by simp
    _ = (u ^ p)⁻¹ *
        (((ζcu ^ m)⁻¹) ^ r * (A ^ r) ^ p) := by
          rw [hpow]
    _ = ((ζcu ^ m)⁻¹) ^ r * (A ^ r * u⁻¹) ^ p := by
          rw [mul_pow, inv_pow]
          simp [mul_comm, mul_left_comm]

/-- **AK-5b anti-radical is a root-of-unity factor times a `p`-th power.**

Composes `AK5b_unit_is_zeta_factor_times_pth_power` with the AK-5b unit form
`α₀ = u · γ^p`.  This moves the remaining AK-5c obstruction from the extracted
unit to the anti-radical itself: after AK-5b, `α₀` is known to be a fixed
root-of-unity factor times a `p`-th power in `K`. -/
theorem AK5b_antiRadical_is_zeta_factor_times_pth_power
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    (γ : K) (hγ_ne : γ ≠ 0) (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ (m r : ℕ) (β : K),
      2 * r = p + 1 ∧
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab =
        algebraMap (𝓞 K) K
          ((((ζcu ^ m)⁻¹) ^ r : (𝓞 K)ˣ) : 𝓞 K) *
          β ^ p := by
  obtain ⟨m, r, w, h_two_r, hu⟩ :=
    AK5b_unit_is_zeta_factor_times_pth_power
      (K := K) hp_two hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  refine ⟨m, r, algebraMap (𝓞 K) K (w : 𝓞 K) * γ, h_two_r, ?_⟩
  rw [← h_unit_form, hu]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_pow]
  ring

/-- **Stage 2 from AK-5a plus the AK-5b root-of-unity cancellation.**

AK-5a gives principality of `I / σI`, hence the unit form
`α₀ = u · γ^p`.  AK-5b shows `α₀` is a root-of-unity factor times a `p`-th
power.  The Stage 2 normalization by `ζ^k` multiplies the ratio by `ζ^(2k)`;
since `2` is invertible modulo odd `p`, choose `k` to cancel that factor. -/
theorem stage2KummerRatioK_of_AK5a
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_AK5a : AK5a_PrincipalMinusIdeals (p := p) (K := K)) :
    Stage2KummerRatioK p K := by
  intro a b c _hgcd hcaseI _heq ζ hζ I _hI_ne hI_pow
  have hab : ¬ (a = 0 ∧ b = 0) := by
    intro ⟨ha, _hb⟩
    apply hcaseI
    rw [ha]
    ring_nf
    exact ⟨0, rfl⟩
  obtain ⟨γ, hγ_ne, hγ_principal⟩ :=
    h_AK5a _hgcd hcaseI _heq hζ hab _hI_ne hI_pow
  obtain ⟨u, h_unit_form⟩ :=
    antiRadical_unit_form_of_principal (K := K) (p := p)
      a b ζ hab I hI_pow γ hγ_principal
  obtain ⟨m, r, β, _h_two_r, hα⟩ :=
    AK5b_antiRadical_is_zeta_factor_times_pth_power
      (K := K) hp_two hp_odd hcaseI hζ hab γ hγ_ne u h_unit_form
  let θU : (𝓞 K)ˣ := (((ζcu ^ m)⁻¹) ^ r)
  have hθinv_pow : (((θU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ p) = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    rw [show θU⁻¹ ^ p = 1 by
      dsimp [θU]
      simp only [inv_pow, inv_inv, ← pow_mul]
      rw [show m * r * p = p * (m * r) by ring]
      rw [pow_mul,
        ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit hp.1.ne_zero).pow_eq_one,
        one_pow]]
    rfl
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨q, _hq_lt, hq⟩ := hζ.eq_pow_of_pow_eq_one hθinv_pow
  obtain ⟨k, hk_lt, hk_pow⟩ := exists_half_exponent_pow_eq
    (K := K) hp_two hζ q
  have hζ_cancel_OK : ζ ^ (2 * k) = ((θU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [hk_pow, hq]
  have hθ_cancel_OK : (((θU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (θU : 𝓞 K)) = 1 := by
    change (((θU⁻¹ * θU : (𝓞 K)ˣ) : 𝓞 K) = (1 : 𝓞 K))
    rw [inv_mul_cancel]
    rfl
  have hroot_cancel :
      (algebraMap (𝓞 K) K ζ) ^ (2 * k) *
          algebraMap (𝓞 K) K (θU : 𝓞 K) = 1 := by
    rw [← map_pow, hζ_cancel_OK, ← map_mul, hθ_cancel_OK, map_one]
  refine ⟨k, hk_lt, β, ?_, ?_⟩
  · have hα_ne :
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab ≠ 0 :=
      caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab
    intro hβ
    apply hα_ne
    rw [hα, hβ, zero_pow hp.out.ne_zero, mul_zero]
  · rw [normalized_antiRadical_ratio_eq_zeta_sq_mul
        (K := K) hp_odd hcaseI hζ hab k]
    rw [hα]
    change (algebraMap (𝓞 K) K ζ) ^ (2 * k) *
        (algebraMap (𝓞 K) K (θU : 𝓞 K) * β ^ p) = β ^ p
    calc
      (algebraMap (𝓞 K) K ζ) ^ (2 * k) *
          (algebraMap (𝓞 K) K (θU : 𝓞 K) * β ^ p)
          = ((algebraMap (𝓞 K) K ζ) ^ (2 * k) *
              algebraMap (𝓞 K) K (θU : 𝓞 K)) * β ^ p := by ring
      _ = 1 * β ^ p := by rw [hroot_cancel]
      _ = β ^ p := by simp

/-- **Stage 2 from a concrete Hilbert-90 cross-multiplication witness.**

This is the direct Case-I source surface produced by the AK-1...AK-4 route:
for each actual FLT factor ideal `I`, supply a unit `δ : Kˣ` satisfying
`I · (σδ) = σI · (δ)`.  The already-proved Hilbert-90/class-group conversion
gives AK-5a under `p ∤ h⁺`, and the AK-5b normalization above gives Stage 2. -/
theorem stage2KummerRatioK_of_cross_mul_witness_and_not_dvd_hPlus
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_cross_data :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} :
          Set (𝓞 K)) = I ^ p) →
        ∃ δ : Kˣ,
          ((I : FractionalIdeal (𝓞 K)⁰ K) *
              FractionalIdeal.spanSingleton (𝓞 K)⁰
                (NumberField.IsCMField.complexConj K (δ : K)) =
            ((I.map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
              FractionalIdeal (𝓞 K)⁰ K) *
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K)))) :
    Stage2KummerRatioK p K :=
  stage2KummerRatioK_of_AK5a (K := K) hp_two hp_odd
    (AK5a_PrincipalMinusIdeals_of_cross_mul_witness_and_not_dvd_hPlus
      (K := K) hp_odd h_not_dvd h_cross_data)

/-- **Stage 2 from principality of actual case-I factor ideals.**

This removes the intermediate `CaseIClassEqDischarge` wrapper from the Stage 2
route.  The explicit remaining case-I source is: for each actual FLT case-I
factorisation `(a + ζ b) = I^p`, the factor ideal `I` is principal. -/
theorem stage2KummerRatioK_of_factorIdeal_isPrincipal
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_principal :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, I ≠ ⊥ →
        Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
        I.IsPrincipal) :
    Stage2KummerRatioK p K :=
  stage2KummerRatioK_of_AK5a (K := K) hp_two hp_odd
    (AK5a_PrincipalMinusIdeals_of_factorIdeal_isPrincipal (K := K) h_principal)

/-- **Stage 2 from triviality of the actual case-I factor-ideal classes.**

This is the class-group form of
`stage2KummerRatioK_of_factorIdeal_isPrincipal`.  It exposes the exact
remaining class-group target `ClassGroup.mk0 I = 1` for the case-I factor
ideal, then uses the already-formal AK-5b normalization to get Stage 2. -/
theorem stage2KummerRatioK_of_factorIdeal_class_eq_one
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_class_one :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p) →
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
            nonZeroDivisors (Ideal (𝓞 K))) = 1) :
    Stage2KummerRatioK p K :=
  stage2KummerRatioK_of_AK5a (K := K) hp_two hp_odd
    (AK5a_PrincipalMinusIdeals_of_factorIdeal_class_eq_one (K := K) h_class_one)

/-- **Stage 2 from class equality plus plus-coprime.**

This packages the refined AK-5a bridge:
`CaseIClassEqDischarge` and `¬ p ∣ h⁺` give the AK-5a principal-minus-ideal
output, and the existing AK-5b normalization chain then gives
`Stage2KummerRatioK`.  The class-equality proof remains the explicit source
input; this theorem is only formal composition. -/
theorem stage2KummerRatioK_of_classEqDischarge_and_not_dvd_hPlus
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_class : CaseIClassEqDischarge p K) :
    Stage2KummerRatioK p K :=
  stage2KummerRatioK_of_AK5a (K := K) hp_two hp_odd
    (AK5a_PrincipalMinusIdeals_of_classEqDischarge_and_not_dvd_hPlus
      (K := K) hp_odd h_not_dvd h_class)

/-- **Stage 2 from the concrete square-class target plus plus-coprime.**

For actual case-I FLT factor ideals, the p-torsion equality is already proved
from `(a + ζ b) = I^p`.  If the remaining square-class equality
`[σI]^2 = [I]^2` is supplied, then `p ≠ 2` gives the class-equality discharge,
the plus-coprime principalization gives AK-5a, and the existing AK-5b
normalization chain gives `Stage2KummerRatioK`. -/
theorem stage2KummerRatioK_of_factor_class_square_eq_and_not_dvd_hPlus
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_sq :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        ∀ {I : Ideal (𝓞 K)}, (hI_nz : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
          (ClassGroup.mk0
              (⟨I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((map_ne_bot_iff_complexConj K I).mpr hI_nz)⟩
                : nonZeroDivisors (Ideal (𝓞 K)))) ^ 2 =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz⟩
                : nonZeroDivisors (Ideal (𝓞 K)))) ^ 2) :
    Stage2KummerRatioK p K :=
  stage2KummerRatioK_of_AK5a (K := K) hp_two hp_odd
    (AK5a_PrincipalMinusIdeals_of_factor_class_square_eq_and_not_dvd_hPlus
      (K := K) hp_odd h_not_dvd h_sq)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **Cyclotomic Stage 2 from the concrete square-class target plus
plus-coprime.**

This is the direct `K = ℚ(ζ_p)` form of
`stage2KummerRatioK_of_factor_class_square_eq_and_not_dvd_hPlus`.  It uses the
stronger cyclotomic reduction which first combines the proved product relation
`[I] * [σI] = 1` with `[σI]^2 = [I]^2` and `p`-torsion to show `[I] = 1`,
then feeds principality into AK-5a and Stage 2. -/
theorem stage2KummerRatioK_of_factor_class_square_eq_and_not_dvd_hPlus_cyclotomic
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (hp_two : 2 < p) (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_sq :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 (CyclotomicField p ℚ)}, IsPrimitiveRoot ζ p →
        ∀ {I : Ideal (𝓞 (CyclotomicField p ℚ))}, (hI_nz : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) +
            ζ * (b : 𝓞 (CyclotomicField p ℚ))} :
              Set (𝓞 (CyclotomicField p ℚ))) = I ^ p →
          (ClassGroup.mk0
              (⟨Ideal.map
                (NumberField.IsCMField.ringOfIntegersComplexConj
                  (CyclotomicField p ℚ)).toRingHom I,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((Ideal.map_eq_bot_iff_of_injective
                    (f := (NumberField.IsCMField.ringOfIntegersComplexConj
                      (CyclotomicField p ℚ)).toRingHom)
                    (NumberField.IsCMField.ringOfIntegersComplexConj
                      (CyclotomicField p ℚ)).injective).not.mpr hI_nz)⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ)))) ^ 2) =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ)))) ^ 2)) :
    Stage2KummerRatioK p (CyclotomicField p ℚ) := by
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  intro a b c hgcd hcaseI heq ζ hζ I hI_ne hI_pow
  exact
    (stage2KummerRatioK_of_AK5a
      (p := p) (K := CyclotomicField p ℚ) hp_two hp_odd
      (AK5a_PrincipalMinusIdeals_of_factor_class_square_eq_and_not_dvd_hPlus_cyclotomic
        (p := p) hp_odd h_not_dvd h_sq))
      hgcd hcaseI heq hζ hI_ne hI_pow

end BernoulliRegular.FLT37.LehmerVandiver.CaseI

end
