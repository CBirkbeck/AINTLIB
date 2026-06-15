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
/-- **σ-applied squared LV004g-1 bridge.** Apply
`ringOfIntegersComplexConj K` to
`zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow`,
yielding
`∏_b σ(ζ^b - 1)^{4 b^E} = σ(ζ-1)^{4S} · σ(E)^4` in `𝓞 K`.

This is the σ-twin of the bare bridge, with `σ(ζ^b - 1) = ζ^{(p-1)b} - 1`.
The bridge identifies `σ(E)^4` as a quotient of half-range σ-products. -/
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
/-- **Unfold σ over the LHS half-range product.** Using the ring-hom
property of `ringOfIntegersComplexConj K`,
`σ(∏_b (ζ^b - 1)^{f b}) = ∏_b (σ(ζ)^b - 1)^{f b}`. Combined with
`complexConj_apply_zeta`, this gives
`σ(LHS) = ∏_b (ζ^{(p-1)b} - 1)^{f b}` in `𝓞 K`. -/
theorem complexConj_zeta_pow_sub_one_prod_eq
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (f : ℕ → ℕ) :
    ringOfIntegersComplexConj K
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ f b) =
      ∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) ^ b - 1) ^ f b := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_pow, map_sub, map_pow, map_one]
  -- Goal: σ(ζ)^b = (ζ ^ (p - 1))^b; use complexConj_apply_zeta.
  rw [complexConj_apply_zeta (p := p) (K := K)]

set_option backward.isDefEq.respectTransparency false in
/-- **Unfold σ over `(ζ - 1)^n`.** Using `complexConj_apply_zeta`,
`σ((ζ - 1)^n) = (ζ^{p-1} - 1)^n` in `𝓞 K`. -/
theorem complexConj_zeta_sub_one_pow_eq
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (n : ℕ) :
    ringOfIntegersComplexConj K ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ n) =
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1) ^ n) := by
  rw [map_pow, map_sub, map_one]
  rw [complexConj_apply_zeta (p := p) (K := K)]

/-- **Connection: `(unitsComplexConj K u : 𝓞 K) = ringOfIntegersComplexConj K (u : 𝓞 K)`.**
The two complex-conjugation operations agree on underlying elements:
`unitsComplexConj` is `ringOfIntegersComplexConj` lifted to units. -/
theorem unitsComplexConj_val_eq_ringOfIntegersComplexConj
    (K : Type*) [Field K] [NumberField K] [IsCMField K] (u : (𝓞 K)ˣ) :
    ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) = ringOfIntegersComplexConj K (u : 𝓞 K) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Coercion of `pollaczekUnitPlus` to `𝓞 K`.** Direct unfold of the
σ-symmetrised definition: `(plus : 𝓞 K) = (E : 𝓞 K) · σ(E : 𝓞 K)`. -/
theorem pollaczekUnitPlus_val
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (i : ℕ) :
    ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) := by
  unfold pollaczekUnitPlus
  rw [Units.val_mul, unitsComplexConj_val_eq_ringOfIntegersComplexConj]

set_option backward.isDefEq.respectTransparency false in
/-- **Squared connection: `(plus : 𝓞 K)^4 = (E : 𝓞 K)^4 · σ(E : 𝓞 K)^4`.** -/
theorem pollaczekUnitPlus_val_pow_four
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (i : ℕ) :
    ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4 =
      (((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4) *
        (ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^ 4) := by
  rw [pollaczekUnitPlus_val, mul_pow]

set_option backward.isDefEq.respectTransparency false in
/-- **Double-squared bridge for `pollaczekUnitPlus`.** Multiply the bare
squared LV004g-1 bridge by its σ-applied version (in `𝓞 K`):

  `∏_b (ζ^b - 1)^{4 b^E} · σ(∏_b (ζ^b - 1)^{4 b^E}) =`
    `((ζ-1)^{4S} · E^4) · σ((ζ-1)^{4S} · E^4)`
    `= (ζ-1)^{4S} · σ(ζ-1)^{4S} · plus^4`.

After unfolding σ over the LHS and the prefactor:

  `∏_b (ζ^b - 1)^{4 b^E} · ∏_b ((ζ^{p-1})^b - 1)^{4 b^E} =`
    `(ζ-1)^{4S} · (ζ^{p-1} - 1)^{4S} · plus^4`. -/
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
  rw [map_mul] at h_sigma_app
  rw [complexConj_zeta_pow_sub_one_prod_eq p K (fun b => 4 * b ^ (p - 1 - i))] at h_sigma_app
  rw [complexConj_zeta_sub_one_pow_eq p K
    (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))] at h_sigma_app
  -- Now h_sigma_app : LHS_sigma = (ζ^{p-1} - 1)^{4S} · σ(E^4)
  -- Multiply h_bare and h_sigma_app: LHS_bare · LHS_sigma = ... · E^4 · σ(E^4)
  have h_combined := congrArg₂ (· * ·) h_bare h_sigma_app
  -- Push σ inside the pow (map_pow) to make σ(E^4) = σ(E)^4 syntactically.
  rw [map_pow] at h_combined
  -- Simplify RHS: a · b · (c · d) = (a · c) · (b · d) [commutative ring]
  -- and identify b · d = E^4 · σ(E^4) = plus^4
  rw [pollaczekUnitPlus_val_pow_four]
  ring_nf
  ring_nf at h_combined
  exact h_combined

set_option backward.isDefEq.respectTransparency false in
/-- **Q-form of the double-squared bridge.** Apply `Ideal.Quotient.mk
lehmerVandiverPrime` to
`zeta_pow_sub_one_double_prod_eq_pollaczekUnitPlus_pow_four`. -/
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
  -- RHS combines via map_mul, map_pow to Q(prefactor · plus^4).
  simp only [← map_pow, ← map_mul]
  exact congrArg (Ideal.Quotient.mk
    (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne))
    (zeta_pow_sub_one_double_prod_eq_pollaczekUnitPlus_pow_four
      p (CyclotomicField p ℚ) hp_odd i)

set_option backward.isDefEq.respectTransparency false in
/-- **Residue substitution: σ-half-range product.** Applies the residue
substitution `Q(ζ^a - 1) = Q(((t^k).val)^a - 1)` at index `a = (p-1)·b`
to each factor of the σ-applied half-range product. Result:

  Q(∏_b ((ζ^{p-1})^b - 1)^{f b}) = Q(∏_b (((t^k).val)^{(p-1)·b} - 1)^{f b})

in `𝓞 K / 𝔩`. -/
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
  refine Finset.prod_congr rfl fun b _ => ?_
  -- Rewrite (ζ^{p-1})^b to ζ^{(p-1)·b}
  rw [← pow_mul]
  rw [map_pow, map_pow]
  congr 1
  -- Apply existing residue substitution at index (p-1)·b.
  exact lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
    (p := p) ℓ k hℓ ht_coprime ht_ne ((p - 1) * b)

set_option backward.isDefEq.respectTransparency false in
/-- **Combined residue substitution: Q-form double-squared bridge in
`(t^k).val`-form.** Combines the bare and σ-applied half-range residue
substitutions to express the Q-form double-squared bridge with all
ζ-elements replaced by their `(t^k).val` residues. -/
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
  -- Start from the Q-form double-squared bridge.
  have h_bridge := lehmerVandiverPrime_quotient_double_squared_bridge
    p hp_odd ℓ k hℓ ht_coprime ht_ne i
  -- Substitute each half-range factor: bare via existing
  -- `lehmerVandiverPrime_quotient_half_range_eq_of_exp`,
  -- σ-applied via the new `lehmerVandiverPrime_quotient_complexConj_lhs_eq_of_exp`.
  have h_lhs_bare := LehmerVandiver.lehmerVandiverPrime_quotient_half_range_eq_of_exp
    p ℓ k hℓ ht_coprime ht_ne (fun b => 4 * b ^ (p - 1 - i))
  have h_lhs_sigma := lehmerVandiverPrime_quotient_complexConj_lhs_eq_of_exp
    p ℓ k hℓ ht_coprime ht_ne (fun b => 4 * b ^ (p - 1 - i))
  -- Substitute prefactor: bare via `lehmerVandiverPrime_quotient_zeta_sub_one_pow_eq`,
  -- σ-applied via `lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq` at index p-1.
  have h_pre_bare := LehmerVandiver.lehmerVandiverPrime_quotient_zeta_sub_one_pow_eq
    p ℓ k hℓ ht_coprime ht_ne
    (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))
  -- σ-applied prefactor: σ((ζ-1)^N) = (ζ^{p-1}-1)^N. Apply Q;
  -- the residue substitution for Q((ζ^{p-1}-1)^N).
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
    -- Q(ζ^{p-1} - 1) = Q((t^k.val)^{p-1} - 1) by existing residue lemma at index p-1.
    exact lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
      (p := p) ℓ k hℓ ht_coprime ht_ne (p - 1)
  -- Split Q over multiplications so individual substitutions can fire.
  rw [map_mul, map_mul]
  rw [map_mul, map_mul] at h_bridge
  -- Now apply each substitution to the matching factor.
  rw [← h_lhs_bare, ← h_lhs_sigma, ← h_pre_bare, ← h_pre_sigma]
  exact h_bridge

set_option backward.isDefEq.respectTransparency false in
/-- **ZMod ℓ form of the double-squared bridge.** Apply
`lehmerVandiverPrime_quotientEquiv` to
`lehmerVandiverPrime_quotient_double_squared_bridge_substituted`,
transporting the residue identity from `𝓞 K / 𝔩` to `ZMod ℓ`:

  `∏_b ((t^k)^b - 1)^{4 b^E} · ∏_b ((t^k)^{(p-1)b} - 1)^{4 b^E} =`
    `((t^k - 1) · ((t^k)^{p-1} - 1))^{4S} · Φ(Q(plus))^4`

in ZMod ℓ. -/
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

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000

/-- **Local Fermat exponent reduction for `ZMod p`.** Replicates
`FLT37Closure`'s private helper. For `x : ZMod p` with `x ≠ 0` and `m`,
`x^m = x^(m % (p - 1))`. -/
private theorem ZMod_pow_eq_pow_mod_card_sub_one
    {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) (m : ℕ) :
    x ^ m = x ^ (m % (p - 1)) := by
  conv_lhs => rw [← Nat.mod_add_div m (p - 1)]
  rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

/-- **FLT37 numerical fact (decide-friendly form).** The LHS of the
double-squared bridge in ZMod 149 with Fermat-reduced outer exponents
is non-trivial. -/
theorem flt37_double_squared_bridge_lhs_reduced_ne_one :
    (∏ b ∈ Finset.Ico 1 19,
      ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^(36 * b) - 1)) ^
        ((4 * b^4) % 148)) ≠ 1 := by
  decide

/-- **FLT37 LHS Fermat-reduction.** Per-term Fermat on the outer
exponent `4·b^4` to relate the unreduced bridge LHS to the
decide-friendly reduced form. The base
`((16)^b - 1) · ((16)^{36·b} - 1)` is non-zero for `b ∈ {1, …, 18}` —
verified by `decide +revert`. -/
theorem flt37_double_squared_bridge_lhs_unreduced_eq_reduced :
    (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
      ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^((37 - 1) * b) - 1)) ^
        (4 * b ^ (37 - 1 - 32))) =
      (∏ b ∈ Finset.Ico 1 19,
        ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^(36 * b) - 1)) ^
          ((4 * b^4) % 148)) := by
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  -- (37-1)/2 + 1 = 19, (37-1)·b = 36·b, 37-1-32 = 4
  refine Finset.prod_congr rfl fun b hb => ?_
  obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
  -- Fermat reduction on the outer exponent: x^m = x^(m % 148) for x ≠ 0.
  have h_base_ne : ∀ b' ∈ Finset.Ico 1 19,
      ((((2 : ZMod 149)^4)^b' - 1) * (((2 : ZMod 149)^4)^(36 * b') - 1)) ≠ 0 := by
    decide +revert
  have hb_old : b ∈ Finset.Ico 1 19 := Finset.mem_Ico.mpr ⟨hb1, hb2⟩
  -- ZMod.pow_eq_pow_mod_card_sub_one : x ≠ 0 → x^m = x^(m % (149 - 1))
  have h_pow_red := ZMod_pow_eq_pow_mod_card_sub_one (h_base_ne b hb_old)
    (4 * b ^ (37 - 1 - 32))
  -- 149 - 1 = 148, and (37 - 1 - 32) = 4
  simp only [show (149 - 1 : ℕ) = 148 from rfl,
    show (37 - 1 - 32 : ℕ) = 4 from rfl] at h_pow_red
  exact h_pow_red

/-- **FLT37 LHS ≠ 1 (unreduced form).** Combine the decide fact with the
Fermat reduction to get non-triviality of the unreduced bridge LHS. -/
theorem flt37_double_squared_bridge_lhs_ne_one :
    (∏ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1),
      ((((2 : ZMod 149)^4)^b - 1) * (((2 : ZMod 149)^4)^((37 - 1) * b) - 1)) ^
        (4 * b ^ (37 - 1 - 32))) ≠ 1 := by
  rw [flt37_double_squared_bridge_lhs_unreduced_eq_reduced]
  exact flt37_double_squared_bridge_lhs_reduced_ne_one

/-- **FLT37 prefactor cancellation.** The bridge prefactor
`((16 - 1)·(16^{36} - 1))^{4·S}` is `1` in ZMod 149.

Proof: `4·S = 4·432345 = 148·11685`, so the exponent is a multiple of
148, and the base is non-zero; apply Fermat. -/
theorem flt37_double_squared_bridge_prefactor_eq_one :
    ((2 : ZMod 149) ^ 4 - 1) ^
        (4 * ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) *
      (((2 : ZMod 149) ^ 4) ^ (37 - 1) - 1) ^
        (4 * ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) = 1 := by
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  have hsum : ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32) = 432345 := by
    decide
  -- Concretize natural-number subtractions: 37-1 = 36, (37-1)/2+1 = 19, 37-1-32 = 4.
  change ((2 : ZMod 149) ^ 4 - 1) ^ (4 * _) *
      (((2 : ZMod 149) ^ 4) ^ 36 - 1) ^ (4 * _) = 1
  rw [hsum]
  -- Goal: (16 - 1)^{4·432345} · (16^{36} - 1)^{4·432345} = 1
  -- Per-term Fermat reduction.
  have h_b1_ne : ((2 : ZMod 149) ^ 4 - 1) ≠ 0 := by decide +revert
  have h_b2_ne : (((2 : ZMod 149) ^ 4) ^ 36 - 1) ≠ 0 := by decide +revert
  rw [ZMod_pow_eq_pow_mod_card_sub_one h_b1_ne (4 * 432345),
      ZMod_pow_eq_pow_mod_card_sub_one h_b2_ne (4 * 432345)]
  decide +revert

set_option backward.isDefEq.respectTransparency false in
/-- **FLT37 main residue identity**: combining the ZMod ℓ form of the
double-squared bridge with the prefactor cancellation gives
`Φ(Q(plus))^4 = LHS_double_unreduced` in ZMod 149. -/
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
  have h_pre := flt37_double_squared_bridge_prefactor_eq_one
  -- Push casts in both bridge and goal so they line up.
  push_cast at h_bridge ⊢
  -- Bridge gives: LHS_split = prefactor · Φ(Q(plus))^4 (now with no ↑ cast).
  -- Combine the LHS two products into a single product with multiplied factors.
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
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [mul_pow]
  -- Apply: (Φ(Q(plus)))^4 = LHS_split, and identify LHS_split = combined LHS.
  rw [← h_lhs_combine, h_bridge, h_pre, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **FLT37 final closure: `¬IsPthPower pollaczekUnitPlus mod 𝔩`.**
Combines:
- `isPthPowerModPrime_lehmerVandiverPrime_iff` (cyclic criterion, abstract over x)
- `pollaczekUnitPlus_notMem_lehmerVandiverPrime` (auxiliary)
- `flt37_phi_q_pollaczekUnitPlus_pow_four_eq_lhs_unreduced` (residue chain)
- `flt37_double_squared_bridge_lhs_ne_one` (LHS ≠ 1)

For the FLT37 certificate `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`,
`pollaczekUnitPlus 37 K 32` is **not** a `p`-th power modulo
`lehmerVandiverPrime`. -/
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
  -- Auxiliary: plus ∉ 𝔩.
  have hplus_ne := pollaczekUnitPlus_notMem_lehmerVandiverPrime 37 149 4 hℓ
    ht_coprime ht_ne 32
  -- Cyclic criterion (abstract): IsPthPower x ↔ Q(x^k) = 1.
  rw [isPthPowerModPrime_lehmerVandiverPrime_iff
    (p := 37) 149 4 hℓ ht_coprime ht_ne hplus_ne]
  intro h_one
  -- Apply map_pow to expose Q(plus)^4 = 1.
  rw [map_pow] at h_one
  -- Apply Φ to both sides: (Φ(Q(plus)))^4 = 1.
  have h_phi := congrArg (lehmerVandiverPrime_quotientEquiv (p := 37)
    149 4 hℓ ht_coprime ht_ne) h_one
  rw [map_pow, map_one] at h_phi
  -- Use the residue chain: (Φ(Q(plus)))^4 = LHS_double in ZMod 149.
  rw [flt37_phi_q_pollaczekUnitPlus_pow_four_eq_lhs_unreduced
    4 hℓ ht_coprime ht_ne rfl rfl] at h_phi
  -- Combined: LHS_double = 1, contradicting flt37_double_squared_bridge_lhs_ne_one.
  exact flt37_double_squared_bridge_lhs_ne_one h_phi

set_option backward.isDefEq.respectTransparency false in
/-- **FLT37 closure (concrete form, real Pollaczek unit).** The fully-instantiated
version: with all parameters fixed to the FLT37 certificate tuple `(p, i, ℓ, t, k)
= (37, 32, 149, 2, 4)`, `pollaczekUnitPlus 37 K 32` is not a `p`-th power modulo
`lehmerVandiverPrime`. This is the `realLocalCert` field of `FLT37BridgeBundle`. -/
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
