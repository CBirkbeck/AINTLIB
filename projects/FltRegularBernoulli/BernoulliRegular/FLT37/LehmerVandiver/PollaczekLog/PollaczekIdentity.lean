/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekR
public import BernoulliRegular.UnitQuotient.DeltaAction

/-!
# Pollaczek's identity (LV004d)

This file works toward Washington's Pollaczek identity (p. 158, line 5):
for an odd prime `p`, `K = ℚ(ζ_p)`, and a primitive root `g` mod `p`,

  `pollaczekR p K i ^ (g^i - 1) = pollaczekUnit p K i * α^p`

for some `α ∈ (𝓞 K)^×`. The proof uses the change of variable `a → ag`
in the `pollaczekR` definition, applied via the Galois automorphism
`σ_g(ζ) = ζ^g`, plus telescoping of the cyclotomic-unit factors.

## Approach

The starting point is the existing K-side Galois infrastructure in
`BernoulliRegular.UnitQuotient.DeltaAction`:

* `cyclotomicSigmaOfUnit p K a` is the Galois automorphism
  `σ_a : Gal(K/ℚ)` corresponding to `a : (ZMod p)ˣ`, satisfying
  `σ_a(ζ) = ζ^{a.val}`.
* `cyclotomicRingOfIntegersEquiv p K a` is the induced ring automorphism
  on `𝓞 K`.

For a primitive root `g` mod `p` (i.e. a generator of the cyclic group
`(ZMod p)ˣ`, which exists by `ZMod.isCyclic_units_prime`), `σ_g` acts on
the Pollaczek factor `F_a = ζ^{a/2} - ζ^{-a/2}` by sending it to
`F_{ag mod p}`, i.e. it permutes the factors of `pollaczekR p K i` via
`a ↦ ag mod p`.

## Current status

This file currently provides the primitive-root and basic Galois-action
infrastructure for LV004d. The full Pollaczek identity proof (change of
variable + telescoping) is still pending; see the ticket
`.mathlib-quality/flt37-tickets.md` (LV004d) for the planned approach.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 158.
* `BernoulliRegular.UnitQuotient.DeltaAction` for the K-side Galois
  action infrastructure.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PrimitiveRoot

/-- **Primitive-root witness.** For an odd prime `p`, the multiplicative
group `(ZMod p)ˣ` is cyclic (mathlib instance `IsCyclic (ZMod p)ˣ` for a
finite integral-domain unit group), so it has a generator `g`. -/
noncomputable def pollaczekPrimRoot : (ZMod p)ˣ :=
  Classical.choose (α := (ZMod p)ˣ) IsCyclic.exists_generator

/-- The defining property of `pollaczekPrimRoot p`: it generates
`(ZMod p)ˣ`. -/
theorem pollaczekPrimRoot_generator (g' : (ZMod p)ˣ) :
    g' ∈ Subgroup.zpowers (pollaczekPrimRoot p) :=
  (Classical.choose_spec (α := (ZMod p)ˣ) IsCyclic.exists_generator) g'

end PrimitiveRoot

section PollaczekRFactorMod

/-- **`pollaczekRFactor` depends only on `a mod p`.** Since the
half-exponent `pollaczekRExp p a = (a : ZMod p) · 2⁻¹` is a function of
`a mod p`, and `pollaczekRFactor p K a` is determined by
`(pollaczekRExp p a).val`, we have

  `(a : ZMod p) = (b : ZMod p) ⟹ pollaczekRFactor p K a = pollaczekRFactor p K b`.

This is the "ζ-periodicity" reduction needed to compute σ_g(F_b) as
F_{(g · b mod p).val} in the Pollaczek-identity proof. -/
theorem pollaczekRFactor_eq_of_natCast_eq {a b : ℕ}
    (h : (a : ZMod p) = (b : ZMod p)) :
    pollaczekRFactor p K a = pollaczekRFactor p K b := by
  unfold pollaczekRFactor
  congr 4 <;> (unfold pollaczekRExp; rw [h])

/-- **Bound on `((a · b) mod p).val`.** For `a ∈ (ZMod p)ˣ` (so `a ≠ 0`)
and `b ∈ Finset.Ico 1 p` (so `(b : ZMod p) ≠ 0`), the product
`(a : ZMod p) * b` is nonzero in `ZMod p` (a field), hence its
natural-number representative also lies in `Finset.Ico 1 p`. -/
theorem val_unit_mul_mem (a : (ZMod p)ˣ) {b : ℕ} (hb : b ∈ Finset.Ico 1 p) :
    (((a : ZMod p) * b).val) ∈ Finset.Ico 1 p := by
  simp only [Finset.mem_Ico] at hb ⊢
  refine ⟨?_, ZMod.val_lt _⟩
  by_contra hle
  have hval : ((a : ZMod p) * b).val = 0 := by omega
  rw [ZMod.val_eq_zero] at hval
  refine (mul_ne_zero (Units.ne_zero a) ?_) hval
  rw [Ne, ZMod.natCast_eq_zero_iff b p]
  intro hdvd; exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- **Inverse property for the multiplication-by-`a` involution on
`Finset.Ico 1 p`.** For `a ∈ (ZMod p)ˣ` and `b ∈ Finset.Ico 1 p`,

  `(a⁻¹ · ((a · b) mod p).val).val = b`.

This is the left-inverse property witnessing that `b ↦ ((a · b) mod p).val`
is a bijection on `Finset.Ico 1 p` (with inverse given by `a⁻¹`). -/
theorem val_unit_mul_left_inv (a : (ZMod p)ˣ) {b : ℕ} (hb : b ∈ Finset.Ico 1 p) :
    ((((a⁻¹ : (ZMod p)ˣ) : ZMod p)) * (((a : ZMod p) * b).val) : ZMod p).val = b := by
  simp only [Finset.mem_Ico] at hb
  have h1 : ((((a⁻¹ : (ZMod p)ˣ) : ZMod p)) * (((a : ZMod p) * b).val) : ZMod p) = b := by
    rw [ZMod.natCast_val, ZMod.cast_id,
      show ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((a : ZMod p) * b) =
            (((a⁻¹ * a : (ZMod p)ˣ) : ZMod p)) * b from by push_cast; ring,
      inv_mul_cancel, Units.val_one, one_mul]
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt hb.2]

/-- **Exponent discrepancy is divisible by `p`.** For `a ∈ (ZMod p)ˣ`,
`b : ℕ`, and `E : ℕ`, the natural numbers `((a · b) mod p).val ^ E`
and `(a.val) ^ E · b ^ E` agree modulo `p` (as integers). This is the
core fact powering the `p`-th-power extraction step of the Pollaczek
identity: when σ_g acts on `R_i = ∏_b F_b^{b^E}` and is reindexed,
the discrepancy between the natural-number exponent
`((g⁻¹ · b) mod p).val ^ E` and the ZMod-p exponent
`(g⁻¹.val) ^ E · b ^ E` is a multiple of `p`, so the corresponding
factor `F_b ^ (multiple of p)` is a `p`-th power. -/
theorem val_unit_mul_pow_modEq (a : (ZMod p)ˣ) (b E : ℕ) :
    (p : ℤ) ∣ ((((a : ZMod p) * b).val) ^ E : ℤ) -
        ((a : ZMod p).val ^ E : ℤ) * (b : ℤ) ^ E := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
  ring

/-- **Balanced division-and-difference identity over `ℕ`.** For
naturals `a, b` and a positive prime `p` with `(p : ℤ) ∣ a - b` (i.e.
`a ≡ b (mod p)` as integers), we have

  `a + p · ((b -ₙ a) / p) = b + p · ((a -ₙ b) / p)`,

where `-ₙ` denotes truncated `Nat` subtraction. The two `Nat`-division
witnesses are zero unless their numerators are positive, so this
captures the balanced form `a + p · α = b + p · β` (one of `α, β` is
zero) for any sign of the integer difference. -/
private theorem balanced_sub_div (p a b : ℕ) (h : (p : ℤ) ∣ (a : ℤ) - b) :
    a + p * ((b - a) / p) = b + p * ((a - b) / p) := by
  rcases le_or_gt a b with hab | hab
  · rw [show a - b = 0 from Nat.sub_eq_zero_of_le hab, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
    have hd : p ∣ b - a := by
      have h_int_neg : (p : ℤ) ∣ -((a : ℤ) - b) := dvd_neg.mpr h
      rw [neg_sub] at h_int_neg
      exact_mod_cast (show ((p : ℕ) : ℤ) ∣ ((b - a : ℕ) : ℤ) from by
        rw [show ((b - a : ℕ) : ℤ) = (b : ℤ) - a from by omega]; exact h_int_neg)
    rw [Nat.mul_div_cancel' hd]; omega
  · rw [show b - a = 0 from Nat.sub_eq_zero_of_le (le_of_lt hab), Nat.zero_div, Nat.mul_zero,
      Nat.add_zero]
    have hd : p ∣ a - b := by
      exact_mod_cast (show ((p : ℕ) : ℤ) ∣ ((a - b : ℕ) : ℤ) from by
        rw [show ((a - b : ℕ) : ℤ) = (a : ℤ) - b from by omega]; exact h)
    rw [Nat.mul_div_cancel' hd]; omega

/-- **Fermat reduction `(g⁻¹.val)^E ≡ g^i (mod p)` for `E = p - 1 - i`.**
This is the modular identity that absorbs the natural-number exponent
on `g⁻¹.val` into the integer power `i`, using Fermat's little theorem
`g^{p-1} = 1` in `(ZMod p)ˣ`. The intended use is in computing
`σ_g(R_i)` modulo `p`-th powers: the natural-number exponent
`((g⁻¹.val)^{p-1-i})` collapses to `g^i` modulo `p`. -/
theorem inv_val_pow_E_eq_pow_i (g : (ZMod p)ˣ) {i : ℕ} (hi : i < p - 1) :
    (((g⁻¹ : (ZMod p)ˣ) : ZMod p).val ^ (p - 1 - i) : ZMod p) =
      ((g : (ZMod p)ˣ) : ZMod p) ^ i := by
  -- Prove the unit-side equation `(g⁻¹)^E = g^i` in `(ZMod p)ˣ`, then descend.
  have h_unit : (g⁻¹ : (ZMod p)ˣ) ^ (p - 1 - i) = g ^ i := by
    have hg_p1 : g ^ (p - 1) = 1 := by
      have h := pow_card_eq_one (G := (ZMod p)ˣ) (x := g)
      rw [ZMod.card_units] at h
      exact h
    have hsum : g ^ (p - 1 - i) * g ^ i = 1 := by
      rw [← pow_add, show p - 1 - i + i = p - 1 from by omega, hg_p1]
    rw [inv_pow, show g ^ i = (g ^ (p - 1 - i))⁻¹ from eq_inv_of_mul_eq_one_right hsum]
  have := congr_arg (Units.val : (ZMod p)ˣ → ZMod p) h_unit
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at this
  rw [ZMod.natCast_val, ZMod.cast_id]
  exact this

end PollaczekRFactorMod

section GaloisAction

variable {p}

/-- **Galois action on `ζ_int^n`.** Under the Galois automorphism
`σ_a` corresponding to `a ∈ (ZMod p)ˣ`, the natural-number power
`ζ_int^n ∈ 𝓞 K` is sent to `ζ_int^{a.val · n}`.

Combines `cyclotomicSigmaOfUnit_smul_zetaInteger` (the action on `ζ`
itself) with multiplicativity of the action via `map_pow` on the
ring-hom-induced action. -/
theorem cyclotomicSigmaOfUnit_smul_zetaInteger_pow (a : (ZMod p)ˣ) (n : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        (cyclotomicZetaInteger (p := p) K ^ n) =
      cyclotomicZetaInteger (p := p) K ^ ((a : ZMod p).val * n) := by
  rw [show cyclotomicSigmaOfUnit (p := p) K a •
          cyclotomicZetaInteger (p := p) K ^ n =
        (cyclotomicSigmaOfUnit (p := p) K a •
          cyclotomicZetaInteger (p := p) K) ^ n from
      map_pow (MulSemiringAction.toRingHom _ _ _) _ _,
    cyclotomicSigmaOfUnit_smul_zetaInteger (p := p) (K := K) a, ← pow_mul]

/-- **Galois action on `ζ_int^b - 1`.** The `σ_a` automorphism sends
`ζ_int^b - 1` to `ζ_int^{a.val · b} - 1`, by ring-hom propagation
through the `(_ ^ b - 1)` expression and
`cyclotomicSigmaOfUnit_smul_zetaInteger_pow`. This is a building block
for the Pollaczek identity (acting on the cyclotomic-unit
factorisation `F_b = ζ^{-(b/2).val} · (ζ^b - 1)` of
`pollaczekRFactor`). -/
theorem cyclotomicSigmaOfUnit_smul_zeta_pow_sub_one (a : (ZMod p)ˣ) (b : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        ((cyclotomicZetaInteger (p := p) K) ^ b - 1) =
      (cyclotomicZetaInteger (p := p) K) ^ ((a : ZMod p).val * b) - 1 := by
  rw [← MulSemiringAction.toRingHom_apply Gal(K/ℚ) _
      (cyclotomicSigmaOfUnit (p := p) K a)]
  simp only [map_sub, map_pow, map_one, MulSemiringAction.toRingHom_apply]
  rw [cyclotomicSigmaOfUnit_smul_zetaInteger, ← pow_mul]

/-- **Galois action on the unit-zpow cast `(ζ_unit'^n : 𝓞 K)`.** For
`a ∈ (ZMod p)ˣ` and `n : ℤ`, `σ_a` sends
`((zeta_unit')^n : (𝓞 K)ˣ : 𝓞 K)` to `((zeta_unit')^{a.val · n} : (𝓞 K)ˣ : 𝓞 K)`.

Proof: factor through `Units.map` of the induced ring iso
`cyclotomicRingOfIntegersEquiv`. The unit map sends
`zeta_unit'` to `zeta_unit'^{a.val}` (because at the ring level,
`σ_a(ζ_int) = ζ_int^{a.val}` by `cyclotomicSigmaOfUnit_smul_zetaInteger`),
then propagate through `map_zpow` and `← zpow_mul` for the integer
power. This is the bridge from the ring-level σ_a action to the
unit-zpow factorisations used in `pollaczekRFactor`. -/
theorem cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast (a : (ZMod p)ˣ) (n : ℤ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        ((zetaUnitR p K ^ n : (𝓞 K)ˣ) : 𝓞 K) =
      ((zetaUnitR p K ^ ((a : ZMod p).val * n) : (𝓞 K)ˣ) : 𝓞 K) := by
  set σ_unit : (𝓞 K)ˣ →* (𝓞 K)ˣ :=
    Units.map (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom
  have h1 : cyclotomicSigmaOfUnit (p := p) K a •
          ((zetaUnitR p K ^ n : (𝓞 K)ˣ) : 𝓞 K) =
        (σ_unit (zetaUnitR p K ^ n) : 𝓞 K) := rfl
  have hzeta_unit : σ_unit (zetaUnitR p K) =
      zetaUnitR p K ^ (a : ZMod p).val := by
    apply Units.ext
    change (cyclotomicRingOfIntegersEquiv (p := p) K a)
        (zetaUnitR p K : 𝓞 K) = _
    change (cyclotomicSigmaOfUnit (p := p) K a) •
        (zetaUnitR p K : 𝓞 K) = _
    rw [show (zetaUnitR p K : 𝓞 K) = cyclotomicZetaInteger (p := p) K from
      zetaUnitR_coe p K, cyclotomicSigmaOfUnit_smul_zetaInteger, Units.val_pow_eq_pow_val]
    rfl
  rw [h1, map_zpow σ_unit, hzeta_unit]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]

/-- **Galois action on `pollaczekRFactor`.** For `a ∈ (ZMod p)ˣ` and
`b : ℕ`, the σ_a Galois automorphism sends `F_b = pollaczekRFactor p K b`
to `F_{(a · b).val}`:

  σ_a(F_b) = F_{((a : ZMod p) * b).val}.

This is the central transformation lemma for the Pollaczek identity:
when σ_g (with g a primitive root) is applied to
`pollaczekR p K i = ∏_b F_b^{b^E}`, it permutes the factors via
`b ↦ (g · b).val`, giving the change-of-variable form.

Proof: unfold the difference-of-zpow definition of `pollaczekRFactor`;
apply `cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast` to each half;
then use `zpow_eq_zpow_iff_modEq` (with `orderOf zeta_unit' = p`) plus
the ZMod p arithmetic identity
`a.val · (b · 2⁻¹) ≡ (a · b) · 2⁻¹ (mod p)` to identify the
two ζ-zpow exponents up to multiples of `p`. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekRFactor (a : (ZMod p)ˣ) (b : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a • pollaczekRFactor p K b =
      pollaczekRFactor p K (((a : ZMod p) * b).val) := by
  unfold pollaczekRFactor
  rw [smul_sub, cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast,
    cyclotomicSigmaOfUnit_smul_zetaUnit_zpow_cast]
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζu : (𝓞 K)ˣ := zetaUnitR p K with hζu
  have hord : orderOf ζu = p := by
    rw [hζu, ← orderOf_units, zetaUnitR_coe]
    exact ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.eq_orderOf).symm
  have hcong : (((a : ZMod p).val : ℤ) * ((pollaczekRExp p b).val : ℤ)) ≡
      ((pollaczekRExp p (((a : ZMod p) * b).val)).val : ℤ) [ZMOD (p : ℤ)] := by
    rw [Int.ModEq, ← ZMod.intCast_eq_intCast_iff']
    push_cast
    unfold pollaczekRExp
    simp only [ZMod.natCast_val, ZMod.cast_id]
    ring
  have happly : ∀ {m n : ℤ}, m ≡ n [ZMOD (p : ℤ)] →
      ((ζu ^ m : (𝓞 K)ˣ) : 𝓞 K) = ((ζu ^ n : (𝓞 K)ˣ) : 𝓞 K) := by
    intro m n hmn; congr 1
    exact zpow_eq_zpow_iff_modEq.mpr (hord ▸ hmn)
  congr 1
  · exact happly hcong
  · rw [show ((a : ZMod p).val : ℤ) * (-((pollaczekRExp p b).val : ℤ)) =
          -(((a : ZMod p).val : ℤ) * ((pollaczekRExp p b).val : ℤ)) from by ring]
    exact happly hcong.neg

/-- **Galois action on `pollaczekR p K i`.** Applying σ_a term-wise
to the product `pollaczekR p K i = ∏_b F_b^{b^{p-1-i}}` yields

  σ_a(R_i) = ∏_b F_{((a · b) mod p).val}^{b^{p-1-i}},

i.e. σ_a permutes the factor indices via `b ↦ (a · b).val` while
keeping the exponents `b^{p-1-i}` unchanged. Combining with a
reindexing `b' = (a · b).val` (a bijection on `Finset.Ico 1 p` when
`a ∈ (ZMod p)ˣ`) gives the change-of-variable form needed for the
Pollaczek identity. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekR (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a • pollaczekR p K i =
      ∏ b ∈ Finset.Ico 1 p,
        pollaczekRFactor p K (((a : ZMod p) * b).val) ^ b ^ (p - 1 - i) := by
  unfold pollaczekR
  rw [show cyclotomicSigmaOfUnit (p := p) K a •
        ∏ b ∈ Finset.Ico 1 p, pollaczekRFactor p K b ^ b ^ (p - 1 - i) =
      ∏ b ∈ Finset.Ico 1 p,
        cyclotomicSigmaOfUnit (p := p) K a •
          (pollaczekRFactor p K b ^ b ^ (p - 1 - i)) from
    map_prod (MulSemiringAction.toRingHom _ _ _) _ _]
  refine Finset.prod_congr rfl ?_
  intro b _
  rw [show cyclotomicSigmaOfUnit (p := p) K a •
            pollaczekRFactor p K b ^ b ^ (p - 1 - i) =
          (cyclotomicSigmaOfUnit (p := p) K a • pollaczekRFactor p K b) ^
            b ^ (p - 1 - i) from
      map_pow (MulSemiringAction.toRingHom _ _ _) _ _,
    cyclotomicSigmaOfUnit_smul_pollaczekRFactor]

/-- **Reindexed σ_a action on `pollaczekR`.** Reindexing the σ_a-action
product `∏_b F_{(a · b).val}^{b^E}` via the involution
`b ↔ (a · b).val` (with inverse `b' ↔ (a⁻¹ · b').val`,
`val_unit_mul_left_inv`) gives

  σ_a(R_i) = ∏_b' F_{b'}^{((a⁻¹ · b').val)^E}.

Now both products run over the same index set `Finset.Ico 1 p`, with
the σ_a-shift absorbed into the *exponents*: each F_{b'} now has
exponent `((a⁻¹ · b').val)^E` instead of the original `b'^E`. The
discrepancy `((a⁻¹ · b').val)^E vs (a⁻¹ · b')^E` (in ZMod p) modulo
`p` is what generates the `p`-th power in the Pollaczek identity.

Uses `Finset.prod_nbij'` with bound and inverse properties from
`val_unit_mul_mem` and `val_unit_mul_left_inv`. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekR_reindexed (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a • pollaczekR p K i =
      ∏ b ∈ Finset.Ico 1 p,
        pollaczekRFactor p K b ^
          ((((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b).val) ^ (p - 1 - i) := by
  rw [cyclotomicSigmaOfUnit_smul_pollaczekR]
  refine Finset.prod_nbij' (fun b => (((a : ZMod p) * b).val))
    (fun b' => (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b').val) ?_ ?_ ?_ ?_ ?_
  · intro b hb; exact val_unit_mul_mem (p := p) a hb
  · intro b' hb'; exact val_unit_mul_mem (p := p) a⁻¹ hb'
  · intro b hb; exact val_unit_mul_left_inv (p := p) a hb
  · intro b' hb'
    have := val_unit_mul_left_inv (p := p) a⁻¹ hb'
    rw [inv_inv] at this
    exact this
  · intro b hb
    have hbeq := val_unit_mul_left_inv (p := p) a hb
    rw [hbeq]

/-- **Balanced σ_a action on `pollaczekR` (Pollaczek identity, equality
form).** Putting together the change-of-variable reindex and the
exponent-discrepancy `p`-divisibility gives the balanced equation

  σ_a(R_i) · α^p = R_i^{(a⁻¹.val)^E} · β^p

where:
* `α := ∏_b F_b ^ (((a⁻¹.val^E · b^E) -ₙ ((a⁻¹ · b).val^E)) / p)`
  absorbs the discrepancy when `(a⁻¹.val^E · b^E) > ((a⁻¹ · b).val^E)`,
* `β := ∏_b F_b ^ ((((a⁻¹ · b).val^E) -ₙ (a⁻¹.val^E · b^E)) / p)`
  absorbs the discrepancy when `((a⁻¹ · b).val^E) > (a⁻¹.val^E · b^E)`.

The natural-number truncated subtraction `-ₙ` makes both witnesses
nonneg `Nat`s, with one of `α, β` always reducing to `1` per term `b`.

This is the key equality form of the Pollaczek identity: σ_a sends R_i
to `R_i^{(a⁻¹.val)^E}` modulo `p`-th powers (the ratio `α^p / β^p`).
Specialising to `a = pollaczekPrimRoot p` and `E = p - 1 - i`, the
exponent `(a⁻¹.val)^E` collapses to `g^i` modulo `p` via
`inv_val_pow_E_eq_pow_i`, giving the Pollaczek-identity exponent
`R_i^{g^i}` modulo `p`-th powers. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekR_balanced (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a • pollaczekR p K i *
        (∏ b ∈ Finset.Ico 1 p,
          pollaczekRFactor p K b ^
            ((((a⁻¹ : (ZMod p)ˣ) : ZMod p).val ^ (p - 1 - i) * b ^ (p - 1 - i) -
              (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b).val ^ (p - 1 - i)) / p)) ^ p =
      pollaczekR p K i ^ ((((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) ^ (p - 1 - i)) *
        (∏ b ∈ Finset.Ico 1 p,
          pollaczekRFactor p K b ^
            (((((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b).val ^ (p - 1 - i) -
              ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val ^ (p - 1 - i) * b ^ (p - 1 - i)) / p)) ^ p := by
  rw [cyclotomicSigmaOfUnit_smul_pollaczekR_reindexed (p := p)]
  set E := p - 1 - i
  rw [show pollaczekR p K i ^ ((((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) ^ E) =
        ∏ b ∈ Finset.Ico 1 p,
          pollaczekRFactor p K b ^ (((((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) ^ E * b ^ E)) from by
    unfold pollaczekR
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl ?_
    intro b _
    rw [← pow_mul, mul_comm]]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro b _
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  have := balanced_sub_div p ((((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b).val ^ E)
    ((((a⁻¹ : (ZMod p)ˣ) : ZMod p)).val ^ E * b ^ E)
    (val_unit_mul_pow_modEq (p := p) a⁻¹ b E)
  linarith

end GaloisAction

end FLT37

end BernoulliRegular

end
