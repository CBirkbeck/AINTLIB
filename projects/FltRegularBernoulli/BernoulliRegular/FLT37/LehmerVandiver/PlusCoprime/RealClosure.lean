module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealResidue

/-!
# LV005-real closure: σ-twin squared bridge

This file mirrors the bare-form
`zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow`
to obtain a σ-twin version, then combines them into a "double-squared"
bridge for `pollaczekUnitPlus`.

**Mathematical content.** Apply the ring homomorphism
`ringOfIntegersComplexConj K : 𝓞 K → 𝓞 K` (i.e., complex conjugation σ)
to the bare squared LV004g-1 bridge, getting
`∏_b (ζ^{p-b} - 1)^{4 b^E} = (ζ^{p-1} - 1)^{4S} · σ(E)^4`.

Multiplying with the bare bridge:
`∏_b ((ζ^b - 1)(ζ^{p-b} - 1))^{4 b^E} = ((ζ-1)(ζ^{p-1}-1))^{4S} · plus^4`.

This is the "double-squared" bridge for pollaczekUnitPlus, the input to
the residue-substitution chain that connects `Φ(Q(plus^4))` to the
symmetric numerical product `∏_b ((2 - 16^b - 28^b) · 39)^{4 b^E}` and
ultimately delivers `realLocalCert`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), Corollary 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

set_option backward.isDefEq.respectTransparency false in
/-- The complex-conjugate of the squared Lehmer-Vandiver bridge. -/
theorem complexConj_zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (hp_odd : p ≠ 2) (i : ℕ) :
    ringOfIntegersComplexConj K
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) =
      ringOfIntegersComplexConj K
          ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
            (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
        ringOfIntegersComplexConj K ((pollaczekUnit p K i : 𝓞 K) ^ 4) := by
  rw [← map_mul]
  exact congrArg (ringOfIntegersComplexConj K)
    (LehmerVandiver.zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow
      p K hp_odd i)

set_option backward.isDefEq.respectTransparency false in
/-- Expands complex conjugation over the half-range product. -/
theorem complexConj_zeta_pow_sub_one_prod_eq
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (f : ℕ → ℕ) :
    ringOfIntegersComplexConj K
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ f b) =
      ∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) ^ b - 1) ^ f b := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  rw [map_pow, map_sub, map_pow, map_one, complexConj_apply_zeta (p := p) (K := K)]

set_option backward.isDefEq.respectTransparency false in
/-- Expands complex conjugation over a power of the cyclotomic generator minus one. -/
theorem complexConj_zeta_sub_one_pow_eq
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (n : ℕ) :
    ringOfIntegersComplexConj K ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ n) =
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1) ^ n) := by
  rw [map_pow, map_sub, map_one, complexConj_apply_zeta (p := p) (K := K)]

/-- Coercion of conjugation on units agrees with conjugation on ring integers. -/
theorem unitsComplexConj_val_eq_ringOfIntegersComplexConj
    (K : Type*) [Field K] [NumberField K] [IsCMField K] (u : (𝓞 K)ˣ) :
    ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) = ringOfIntegersComplexConj K (u : 𝓞 K) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coercion of `pollaczekUnitPlus` is a Pollaczek unit times its conjugate. -/
theorem pollaczekUnitPlus_val
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (i : ℕ) :
    ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) := by
  simp only [pollaczekUnitPlus]
  rw [Units.val_mul, unitsComplexConj_val_eq_ringOfIntegersComplexConj]

set_option backward.isDefEq.respectTransparency false in
/-- The fourth power of `pollaczekUnitPlus` factors through complex conjugation. -/
theorem pollaczekUnitPlus_val_pow_four
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (i : ℕ) :
    ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4 =
      (((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4) *
        (ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4) := by
  rw [pollaczekUnitPlus_val, mul_pow]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplies the squared Lehmer-Vandiver bridge by its complex conjugate. -/
theorem zeta_pow_sub_one_double_prod_eq_pollaczekUnitPlus_pow_four
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (hp_odd : p ≠ 2) (i : ℕ) :
    (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) *
      (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) ^ b - 1) ^
          (4 * b ^ (p - 1 - i))) =
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
        ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4 := by
  have h_bare := LehmerVandiver.zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow
    p K hp_odd i
  have h_sigma_app : ringOfIntegersComplexConj K
      (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) =
        ringOfIntegersComplexConj K
          (((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
              (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
            ((pollaczekUnit p K i : 𝓞 K) ^ 4)) :=
    congrArg (ringOfIntegersComplexConj K) h_bare
  rw [map_mul, complexConj_zeta_pow_sub_one_prod_eq p K (fun b ↦ 4 * b ^ (p - 1 - i)),
    complexConj_zeta_sub_one_pow_eq p K
      (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))] at h_sigma_app
  have h_combined := congrArg₂ (· * ·) h_bare h_sigma_app
  rw [map_pow] at h_combined
  rw [pollaczekUnitPlus_val_pow_four]
  ring_nf
  ring_nf at h_combined
  exact h_combined

set_option backward.isDefEq.respectTransparency false in
/-- Maps the double-squared bridge to the quotient by `lehmerVandiverPrime`. -/
theorem lehmerVandiverPrime_quotient_double_squared_bridge
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ)
    [IsCMField (CyclotomicField p ℚ)] :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) ^ b - 1) ^
            (4 * b ^ (p - 1 - i))) *
          (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
            ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
                𝓞 (CyclotomicField p ℚ)) ^ (p - 1)) ^ b - 1) ^
              (4 * b ^ (p - 1 - i)))) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) - 1) ^
            (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
          ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) ^ (p - 1) - 1) ^
            (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)))) *
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((pollaczekUnitPlus p (CyclotomicField p ℚ) i :
          (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 4 := by
  simp only [← map_pow, ← map_mul]
  exact congrArg (Ideal.Quotient.mk
    (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne))
    (zeta_pow_sub_one_double_prod_eq_pollaczekUnitPlus_pow_four
      p (CyclotomicField p ℚ) hp_odd i)

set_option backward.isDefEq.respectTransparency false in
/-- Substitutes residues into the complex-conjugate half-range product. -/
theorem lehmerVandiverPrime_quotient_complexConj_lhs_eq_of_exp
    (p : ℕ) [Fact p.Prime]
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (f : ℕ → ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) ^ (p - 1)) ^ b - 1) ^ f b) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          ((((t : ZMod ℓ) ^ k).val : ℕ) ^ ((p - 1) * b) - 1 :
            𝓞 (CyclotomicField p ℚ)) ^ f b) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  rw [← pow_mul, map_pow, map_pow]
  congr 1
  exact lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
    (p := p) ℓ k hℓ ht_coprime ht_ne ((p - 1) * b)

set_option backward.isDefEq.respectTransparency false in
/-- Substitutes residues into every factor of the quotient double-squared bridge. -/
theorem lehmerVandiverPrime_quotient_double_squared_bridge_substituted
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ)
    [IsCMField (CyclotomicField p ℚ)] :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          ((((t : ZMod ℓ) ^ k).val : ℕ) ^ b - 1 :
            𝓞 (CyclotomicField p ℚ)) ^ (4 * b ^ (p - 1 - i))) *
          (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
            ((((t : ZMod ℓ) ^ k).val : ℕ) ^ ((p - 1) * b) - 1 :
              𝓞 (CyclotomicField p ℚ)) ^ (4 * b ^ (p - 1 - i)))) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((((((t : ZMod ℓ) ^ k).val : ℕ) - 1 :
            𝓞 (CyclotomicField p ℚ)) ^
            (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
          ((((((t : ZMod ℓ) ^ k).val : ℕ) ^ (p - 1) - 1 :
              𝓞 (CyclotomicField p ℚ)) ^
            (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))))) *
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((pollaczekUnitPlus p (CyclotomicField p ℚ) i :
          (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 4 := by
  have h_bridge := lehmerVandiverPrime_quotient_double_squared_bridge
    p hp_odd ℓ k hℓ ht_coprime ht_ne i
  have h_lhs_bare := LehmerVandiver.lehmerVandiverPrime_quotient_half_range_eq_of_exp
    p ℓ k hℓ ht_coprime ht_ne (fun b ↦ 4 * b ^ (p - 1 - i))
  have h_lhs_sigma := lehmerVandiverPrime_quotient_complexConj_lhs_eq_of_exp
    p ℓ k hℓ ht_coprime ht_ne (fun b ↦ 4 * b ^ (p - 1 - i))
  have h_pre_bare := LehmerVandiver.lehmerVandiverPrime_quotient_zeta_sub_one_pow_eq
    p ℓ k hℓ ht_coprime ht_ne
    (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))
  have h_pre_sigma : Ideal.Quotient.mk
      (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
      ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
          𝓞 (CyclotomicField p ℚ)) ^ (p - 1) - 1) ^
        (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
      (((((t : ZMod ℓ) ^ k).val : ℕ) ^ (p - 1) - 1 :
          𝓞 (CyclotomicField p ℚ)) ^
        (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) := by
    rw [map_pow, map_pow]
    congr 1
    exact lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
      (p := p) ℓ k hℓ ht_coprime ht_ne (p - 1)
  rw [map_mul, map_mul]
  rw [map_mul, map_mul] at h_bridge
  rw [← h_lhs_bare, ← h_lhs_sigma, ← h_pre_bare, ← h_pre_sigma]
  exact h_bridge

set_option backward.isDefEq.respectTransparency false in
/-- Transports the quotient double-squared bridge to `ZMod ℓ`. -/
theorem lehmerVandiverPrime_double_squared_bridge_zmod
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ)
    [IsCMField (CyclotomicField p ℚ)] :
    (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((t : ZMod ℓ) ^ k) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) *
      (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((t : ZMod ℓ) ^ k) ^ ((p - 1) * b) - 1) ^ (4 * b ^ (p - 1 - i))) =
      (((t : ZMod ℓ) ^ k - 1) ^
        (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      (((t : ZMod ℓ) ^ k) ^ (p - 1) - 1) ^
        (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) *
      (lehmerVandiverPrime_quotientEquiv (p := p) ℓ k hℓ ht_coprime ht_ne
        (Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
          ((pollaczekUnitPlus p (CyclotomicField p ℚ) i :
            (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))) ^ 4 := by
  have h := lehmerVandiverPrime_quotient_double_squared_bridge_substituted
    p hp_odd ℓ k hℓ ht_coprime ht_ne i
  have hΦ_tk := LehmerVandiver.lehmerVandiverPrime_quotientEquiv_quotient_apply_natCast_tk
    p ℓ k hℓ ht_coprime ht_ne
  have h_eq := congrArg (lehmerVandiverPrime_quotientEquiv (p := p)
    ℓ k hℓ ht_coprime ht_ne) h
  simp only [map_mul, map_prod, map_pow, map_sub, map_one, hΦ_tk] at h_eq
  exact h_eq

section FLT37Numerical

private theorem ZMod.pow_eq_pow_mod_card_sub_one
    {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) (m : ℕ) :
    x ^ m = x ^ (m % (p - 1)) := by
  conv_lhs => rw [← Nat.mod_add_div m (p - 1)]
  rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

private theorem flt37_double_squared_bridge_factor_eq (b : ℕ) :
    ((((2 : ZMod 149) ^ 4) ^ b - 1) * (((2 : ZMod 149) ^ 4) ^ (36 * b) - 1)) =
      2 - (16 : ZMod 149) ^ b - (28 : ZMod 149) ^ b := by
  rw [show (2 : ZMod 149) ^ 4 = 16 by norm_num, pow_mul,
    show (16 : ZMod 149) ^ 36 = 28 by decide]
  have hmul : (16 : ZMod 149) ^ b * (28 : ZMod 149) ^ b = 1 := by
    rw [← mul_pow, show (16 : ZMod 149) * 28 = 1 by decide, one_pow]
  calc
    ((16 : ZMod 149) ^ b - 1) * (28 ^ b - 1) =
        16 ^ b * 28 ^ b - 16 ^ b - 28 ^ b + 1 := by ring
    _ = 2 - 16 ^ b - 28 ^ b := by rw [hmul]; ring

private theorem flt37_scale_product_eq_one :
    (∏ b ∈ Finset.Ico 1 19, (39 : ZMod 149) ^ ((4 * b ^ 4) % 148)) = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ b ∈ Finset.Ico 1 19, (4 * b ^ 4) % 148 = 1184 := by
    norm_num [Finset.sum_Ico_succ_top]
  rw [hsum, show (1184 : ℕ) = 148 * 8 by norm_num, pow_mul,
    ZMod.pow_card_sub_one_eq_one (by decide : (39 : ZMod 149) ≠ 0), one_pow]

private theorem flt37_residue_product_eq_reduced_bridge_product :
    (∏ b ∈ Finset.Ico 1 19,
        ((2 - (16 : ZMod 149) ^ b - (28 : ZMod 149) ^ b) * 39 : ZMod 149) ^
          ((4 * b ^ 4) % 148)) =
      (∏ b ∈ Finset.Ico 1 19,
        ((((2 : ZMod 149) ^ 4) ^ b - 1) * (((2 : ZMod 149) ^ 4) ^ (36 * b) - 1)) ^
          ((4 * b ^ 4) % 148)) := by
  calc
    _ = ∏ b ∈ Finset.Ico 1 19,
          (((((2 : ZMod 149) ^ 4) ^ b - 1) *
              (((2 : ZMod 149) ^ 4) ^ (36 * b) - 1)) * 39) ^ ((4 * b ^ 4) % 148) := by
      refine Finset.prod_congr rfl fun b _ ↦ ?_
      rw [flt37_double_squared_bridge_factor_eq]
    _ = ∏ b ∈ Finset.Ico 1 19,
          ((((2 : ZMod 149) ^ 4) ^ b - 1) *
              (((2 : ZMod 149) ^ 4) ^ (36 * b) - 1)) ^ ((4 * b ^ 4) % 148) *
            (39 : ZMod 149) ^ ((4 * b ^ 4) % 148) := by
      refine Finset.prod_congr rfl fun b _ ↦ ?_
      rw [mul_pow]
    _ = (∏ b ∈ Finset.Ico 1 19,
          ((((2 : ZMod 149) ^ 4) ^ b - 1) *
              (((2 : ZMod 149) ^ 4) ^ (36 * b) - 1)) ^ ((4 * b ^ 4) % 148)) *
        (∏ b ∈ Finset.Ico 1 19, (39 : ZMod 149) ^ ((4 * b ^ 4) % 148)) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [flt37_scale_product_eq_one, mul_one]

/-- The Fermat-reduced FLT37 double-squared bridge product is nontrivial. -/
theorem flt37_double_squared_bridge_lhs_reduced_ne_one :
    (∏ b ∈ Finset.Ico 1 19,
      ((((2 : ZMod 149) ^ 4) ^ b - 1) * (((2 : ZMod 149) ^ 4) ^ (36 * b) - 1)) ^
        ((4 * b ^ 4) % 148)) ≠ 1 := by
  rw [← flt37_residue_product_eq_reduced_bridge_product]
  exact flt37_pollaczekUnitPlus_residue_pow_four_ne_one

/-- Fermat reduction identifies the unreduced and reduced FLT37 bridge products. -/
theorem flt37_double_squared_bridge_lhs_unreduced_eq_reduced :
    (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
      ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^((37 - 1) * b) - 1)) ^
        (4 * b ^ (37 - 1 - 32))) =
      (∏ b ∈ Finset.Ico 1 19,
        ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^(36 * b) - 1)) ^
          ((4 * b^4) % 148)) := by
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  refine Finset.prod_congr rfl fun b hb ↦ ?_
  obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
  have h_base_ne : ∀ b' ∈ Finset.Ico 1 19,
      ((((2 : ZMod 149)^4)^b' - 1) * (((2 : ZMod 149)^4)^(36 * b') - 1)) ≠ 0 := by
    decide +revert
  simpa only [show (149 - 1 : ℕ) = 148 from rfl,
      show (37 - 1 - 32 : ℕ) = 4 from rfl] using
    ZMod.pow_eq_pow_mod_card_sub_one
      (h_base_ne b (Finset.mem_Ico.mpr ⟨hb1, hb2⟩)) (4 * b ^ (37 - 1 - 32))

/-- The unreduced FLT37 double-squared bridge product is nontrivial. -/
theorem flt37_double_squared_bridge_lhs_ne_one :
    (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
      ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^((37 - 1) * b) - 1)) ^
        (4 * b ^ (37 - 1 - 32))) ≠ 1 := by
  rw [flt37_double_squared_bridge_lhs_unreduced_eq_reduced]
  exact flt37_double_squared_bridge_lhs_reduced_ne_one

/-- The FLT37 double-squared bridge prefactor is one in `ZMod 149`. -/
theorem flt37_double_squared_bridge_prefactor_eq_one :
    ((2 : ZMod 149) ^ 4 - 1) ^
        (4 * ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) *
      (((2 : ZMod 149) ^ 4) ^ (37 - 1) - 1) ^
        (4 * ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) = 1 := by
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  have hsum : ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32) = 432345 := by
    decide
  change ((2 : ZMod 149) ^ 4 - 1) ^ (4 * _) *
      (((2 : ZMod 149) ^ 4) ^ 36 - 1) ^ (4 * _) = 1
  rw [hsum]
  have h_b1_ne : ((2 : ZMod 149) ^ 4 - 1) ≠ 0 := by decide +revert
  have h_b2_ne : (((2 : ZMod 149) ^ 4) ^ 36 - 1) ≠ 0 := by decide +revert
  rw [ZMod.pow_eq_pow_mod_card_sub_one h_b1_ne (4 * 432345),
      ZMod.pow_eq_pow_mod_card_sub_one h_b2_ne (4 * 432345)]
  decide +revert

set_option backward.isDefEq.respectTransparency false in
/-- The fourth power of the FLT37 Pollaczek-unit residue equals the unreduced bridge product. -/
theorem flt37_phi_q_pollaczekUnitPlus_pow_four_eq_lhs_unreduced
    [Fact (Nat.Prime 37)] [Fact (Nat.Prime 149)]
    (k : ℕ) (hℓ : 149 = k * 37 + 1) {t : ℕ}
    (ht_coprime : t.Coprime 149) (ht_ne : (t : ZMod 149) ^ k ≠ 1)
    (hkt : k = 4) (htval : t = 2)
    [IsCMField (CyclotomicField 37 ℚ)] :
    (lehmerVandiverPrime_quotientEquiv (p := 37) 149 k hℓ ht_coprime ht_ne
      (Ideal.Quotient.mk
        (lehmerVandiverPrime 37 149 k hℓ ht_coprime ht_ne)
        ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)))) ^ 4 =
      (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
        ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^((37 - 1) * b) - 1)) ^
          (4 * b ^ (37 - 1 - 32))) := by
  subst hkt htval
  have h_bridge := lehmerVandiverPrime_double_squared_bridge_zmod 37 (by decide)
    149 4 hℓ ht_coprime ht_ne 32
  push_cast at h_bridge ⊢
  have h_lhs_combine :
      (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
          (((((2 : ZMod 149)) ^ 4) ^ b - 1) ^ (4 * b ^ (37 - 1 - 32))) ) *
        (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
          (((((2 : ZMod 149)) ^ 4) ^ ((37 - 1) * b) - 1) ^
            (4 * b ^ (37 - 1 - 32)))) =
      (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
          ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^((37 - 1) * b) - 1)) ^
            (4 * b ^ (37 - 1 - 32))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [mul_pow]
  rw [← h_lhs_combine, h_bridge, flt37_double_squared_bridge_prefactor_eq_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The FLT37 real Pollaczek unit is not a 37th power modulo the Lehmer-Vandiver prime. -/
theorem flt37_not_isPthPowerModPrime_pollaczekUnitPlus
    [Fact (Nat.Prime 37)] [Fact (Nat.Prime 149)]
    (k : ℕ) (hℓ : 149 = k * 37 + 1) {t : ℕ}
    (ht_coprime : t.Coprime 149) (ht_ne : (t : ZMod 149) ^ k ≠ 1)
    (hkt : k = 4) (htval : t = 2)
    [IsCMField (CyclotomicField 37 ℚ)] :
    ¬ IsPthPowerModPrime 37
      (lehmerVandiverPrime 37 149 k hℓ ht_coprime ht_ne)
      ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
  subst hkt htval
  have hplus_ne := pollaczekUnitPlus_notMem_lehmerVandiverPrime 37 149 4 hℓ
    ht_coprime ht_ne 32
  rw [isPthPowerModPrime_lehmerVandiverPrime_iff
    (p := 37) 149 4 hℓ ht_coprime ht_ne hplus_ne]
  intro h_one
  rw [map_pow] at h_one
  have h_phi := congrArg (lehmerVandiverPrime_quotientEquiv (p := 37)
    149 4 hℓ ht_coprime ht_ne) h_one
  rw [map_pow, map_one] at h_phi
  rw [flt37_phi_q_pollaczekUnitPlus_pow_four_eq_lhs_unreduced
    4 hℓ ht_coprime ht_ne rfl rfl] at h_phi
  exact flt37_double_squared_bridge_lhs_ne_one h_phi

set_option backward.isDefEq.respectTransparency false in
/-- The concrete FLT37 certificate for the real Pollaczek unit modulo the auxiliary prime. -/
theorem flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete
    [IsCMField (CyclotomicField 37 ℚ)] :
    ¬ IsPthPowerModPrime 37
      (lehmerVandiverPrime 37 149 4
        (by decide : (149 : ℕ) = 4 * 37 + 1)
        (by decide : (2 : ℕ).Coprime 149)
        (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
      ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  exact flt37_not_isPthPowerModPrime_pollaczekUnitPlus 4
    (by decide : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide +revert : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1) rfl rfl

end FLT37Numerical

end FLT37

end BernoulliRegular

end
