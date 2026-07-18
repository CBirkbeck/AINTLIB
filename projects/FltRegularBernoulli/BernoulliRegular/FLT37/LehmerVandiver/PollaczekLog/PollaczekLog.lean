/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekIdentity
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PrimeIdentification
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PthPower
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.RPollaczekUnitBridge

/-!
# Pollaczek's log identity (LV004g — Washington Prop 8.18 assembly)

This file is the **final assembly** of Washington's Proposition 8.18.
It combines the building blocks from the `LV004` cluster:

* `LV004a/f` (`PthPower.lean`): the `IsPthPowerModPrime` predicate and
  the cyclic-group residue criterion.
* `LV004b` (`PollaczekR.lean`): the auxiliary cyclotomic element
  `pollaczekR p K i`.
* `LV004c` (`PrimeIdentification.lean`): the prime
  `lehmerVandiverPrime p ℓ k h` lying over `ℓ` with `ζ ≡ t^k (mod 𝔩)`.
* `LV004d` (`PollaczekIdentity.lean`): the balanced Pollaczek identity
  `σ_a(R_i) · α^p = R_i^{(a⁻¹.val)^E} · β^p`.
* `LV004e` (`PollaczekR.lean`): the half-range factorisation
  `R_i = sign · ∏_b F_b^{2 b^E} · γ^p` and its cyclotomic-unit form.
* `LV001/LV002` (`Certificate.lean`): the certificate `Q_i^k`.

## Strategy

The bridge from "the certificate `Q_i^k ≢ 1 (mod ℓ)`" to "`E_i` not a
`p`-th power mod `𝔩`" works in three layers:

**Layer 1 (mod-`p`-th-powers transfer).** From LV004d's balanced
equality `σ_g(R_i) · α^p = R_i^{(g⁻¹.val)^E} · β^p` in `𝓞 K`, working
modulo `𝔩` and using the multiplicativity of `IsPthPowerModPrime` on
`p`-th powers and on units (provided `α, β ∉ 𝔩`), we obtain the
mod-`p`-th-powers congruence `σ_g(R_i) ≡ R_i^{g^i (mod p)} (mod p`-th
powers, mod 𝔩`)`.

**Layer 2 (cyclotomic-unit form).** From LV004e's
`pollaczekR_half_range_factorisation` plus `pollaczekR_half_range_main_zeta_form`,
`R_i` is congruent (modulo `p`-th powers) to a ζ-prefactor times the
half-range cyclotomic-unit product `∏_b (ζ^b - 1)^{2 b^E}`, paired with
a sign factor.

**Layer 3 (residue specialisation).** Substituting `ζ ≡ t^k (mod 𝔩)`
(LV004c) into the half-range cyclotomic-unit product gives the
half-range certificate `Q_i^k (mod ℓ)`. The `IsPthPowerModPrime` test
via the cyclic-group criterion (LV004f) becomes the certificate test.

## Status

**Layers 1 and 2 are now substantially complete** (~830 lines).
Top-level results (in dependency order):

* `IsPthPowerModPrime.{congr, mul_pow_iff, mul_iff, transfer_balanced,
  pow_eq_of_modEq}` — the foundational `IsPthPowerModPrime` API.
* `pow_notMem_of_notMem`, `zeta_sub_one_notMem_lehmerVandiverPrime`,
  `zeta_pow_sub_one_notMem_lehmerVandiverPrime` — residue-field
  non-degeneracy under the LV001/2 certificate hypotheses.
* `lehmerVandiverPrime_quotientEquiv : 𝓞 K / 𝔩 ≃+* ZMod ℓ`,
  `lehmerVandiverPrime_quotient_card = ℓ` — the residue field iso.
* `isPthPowerModPrime_lehmerVandiverPrime_iff` — cyclic criterion at
  `lehmerVandiverPrime`: `IsPthPower x ↔ Q(x^k) = 1`.
* `isPthPowerModPrime_lehmerVandiverPrime_sq_iff` — squaring lemma
  `IsPthPower (x^2) ↔ IsPthPower x` for `p` odd (LV004g-2).
* `isPthPowerModPrime_pollaczekR_iff_main`,
  `isPthPowerModPrime_main_iff_zeta_form` — chain reductions from R_i
  to the cyclotomic-half-range product (LV004e composition).
* `isPthPowerModPrime_zeta_form_iff_pollaczekUnit` — the LV004g-1+2
  composition: cyclotomic-half-range ↔ `pollaczekUnit²` ↔ `pollaczekUnit`.
* **`isPthPowerModPrime_pollaczekR_iff_pollaczekUnit`** — the LV004g
  main theorem: `IsPthPower R_i ↔ IsPthPower (pollaczekUnit p K i)`.
* `isPthPowerModPrime_pollaczekUnit_iff_quotient_pow_eq_one` — final
  cyclic-criterion form: `IsPthPower pollaczekUnit ↔
  Q(pollaczekUnit^k) = 1` in `𝓞 K / 𝔩 ≃+* ZMod ℓ`.

**Layer 3 (residue specialisation to LV001/2 certificate) is still open**.
The remaining residual is computing `Q(pollaczekUnit^k)` explicitly in
`ZMod ℓ` via the iso, and matching against the certificate ratio
`Q_i^k = lehmerVandiverProduct / lehmerVandiverPrefactor`. The match
involves the algebraic identity

  (1 - t^k)^{kS} = (-1)^{kS} · t^{k²·d_i/2}    in ZMod ℓ,

where `S = ∑_b b^{p-1-i}` and `d_i = ∑_a a^{p-i}`. For the FLT37
specific case `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`, this can be
verified numerically; the general identity may require a Bernoulli /
power-sum analysis.

The companion file `CertificateMatch.lean` ships LV004g-3:
`product² = prefactor² ↔ product = ±prefactor` plus the sufficient
condition `product ≠ ±prefactor → product² ≠ prefactor²`, which is
the algebraic skeleton of the certificate test.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), Proposition 8.18, p. 158.
-/

@[expose] public section

namespace BernoulliRegular

section PthPowerTransfer

variable {R : Type*} [CommRing R] {p : ℕ} {𝔩 : Ideal R}

/-- **`IsPthPowerModPrime` is `congruent`-invariant.** If `x ≡ y (mod 𝔩)`,
then `x` is a `p`-th power mod `𝔩` iff `y` is. -/
theorem IsPthPowerModPrime.congr {x y : R} (h : x - y ∈ 𝔩) :
    IsPthPowerModPrime p 𝔩 x ↔ IsPthPowerModPrime p 𝔩 y := by
  simp only [IsPthPowerModPrime]
  refine ⟨?_, ?_⟩ <;>
    rintro ⟨z, hz⟩ <;>
    refine ⟨z, ?_⟩ <;>
    [(rw [show Ideal.Quotient.mk 𝔩 y = Ideal.Quotient.mk 𝔩 x from ?_, hz]);
     (rw [show Ideal.Quotient.mk 𝔩 x = Ideal.Quotient.mk 𝔩 y from ?_, hz])] <;>
    [(rw [Ideal.Quotient.eq, ← neg_sub]; exact (Ideal.neg_mem_iff _).mpr h);
     (rw [Ideal.Quotient.eq]; exact h)]

/-- **`p`-th power closure under multiplication by `p`-th powers.** If
`x · α^p` is a `p`-th power mod `𝔩` and `α ∉ 𝔩` (so `α` is invertible
in the residue field, when `𝔩` is maximal), then `x` is a `p`-th power
mod `𝔩` (and conversely).

The forward direction is automatic: if `x · α^p = z^p (mod 𝔩)`, then
working in the residue field (assuming `α ∉ 𝔩`), `x = z^p · (α^p)⁻¹ =
(z · α⁻¹)^p`. -/
theorem IsPthPowerModPrime.mul_pow_iff [𝔩.IsMaximal]
    {x α : R} (hα : α ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩 (x * α ^ p) ↔ IsPthPowerModPrime p 𝔩 x := by
  letI : Field (R ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩
    have hα' : (Ideal.Quotient.mk 𝔩 α) ≠ 0 :=
      fun h => hα ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    refine ⟨z * (Ideal.Quotient.mk 𝔩 α)⁻¹, ?_⟩
    rw [map_mul, map_pow] at hz
    rw [mul_pow]
    rw [show ((Ideal.Quotient.mk 𝔩 α)⁻¹) ^ p =
        ((Ideal.Quotient.mk 𝔩 α) ^ p)⁻¹ from inv_pow _ _]
    field_simp
    linear_combination hz
  · intro hx
    exact hx.mul (IsPthPowerModPrime.pow_self α)

/-- **Transfer through a balanced equation.** Given an equation
`x * α^p = y * β^p` in `R` (e.g. coming from LV004d's balanced
Pollaczek identity), and assuming `α, β ∉ 𝔩` (so both `α, β` are
invertible in the residue field at `𝔩` when `𝔩` is maximal),
`x` is a `p`-th power mod `𝔩` iff `y` is. -/
theorem IsPthPowerModPrime.transfer_balanced [𝔩.IsMaximal]
    {x y α β : R} (h : x * α ^ p = y * β ^ p)
    (hα : α ∉ 𝔩) (hβ : β ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩 x ↔ IsPthPowerModPrime p 𝔩 y := by
  rw [← IsPthPowerModPrime.mul_pow_iff (α := α) hα, h,
    IsPthPowerModPrime.mul_pow_iff (α := β) hβ]

/-- **`x ∉ 𝔩 ⟹ x^k ∉ 𝔩` (for prime `𝔩`).** Powers of non-members
of a prime ideal remain outside the ideal. -/
theorem pow_notMem_of_notMem [hℓ : 𝔩.IsPrime] {x : R} (hx : x ∉ 𝔩) (k : ℕ) :
    x ^ k ∉ 𝔩 := by
  intro hmem; exact hx (hℓ.mem_of_pow_mem k hmem)

/-- **Multiplying by a `p`-th-power-mod-`𝔩` element is invertible for
the predicate.** For `u ∉ 𝔩` (so `u` is a unit in the residue field at
`𝔩`, when `𝔩` is maximal) and `IsPthPowerModPrime p 𝔩 u`, we have

  `IsPthPowerModPrime p 𝔩 (x · u) ↔ IsPthPowerModPrime p 𝔩 x`.

This generalises `IsPthPowerModPrime.mul_pow_iff` to the case where `u`
is only known to be a `p`-th power mod `𝔩` (not necessarily of the form
`α^p` in `R`). The forward direction divides by the residue-field
inverse of `u`, available since `R ⧸ 𝔩` is a field. -/
theorem IsPthPowerModPrime.mul_iff [Fact p.Prime] [𝔩.IsMaximal]
    {x u : R} (hu : u ∉ 𝔩) (hu_pth : IsPthPowerModPrime p 𝔩 u) :
    IsPthPowerModPrime p 𝔩 (x * u) ↔ IsPthPowerModPrime p 𝔩 x := by
  letI : Field (R ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  have hu0 : (Ideal.Quotient.mk 𝔩 u) ≠ 0 :=
    fun h => hu ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  refine ⟨?_, fun hx => hx.mul hu_pth⟩
  rintro ⟨z, hz⟩
  obtain ⟨v, hv⟩ := hu_pth
  have hp_pos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hv0 : v ≠ 0 :=
    fun h => hu0 (by rw [hv, h, zero_pow hp_pos.ne'])
  refine ⟨z * v⁻¹, ?_⟩
  rw [map_mul, hv] at hz
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination hz

/-- **`IsPthPowerModPrime` is invariant under modular exponent shifts.**
For `x ∉ 𝔩` (and `𝔩` maximal), `m ≡ n (mod p)` (as integers) implies
`IsPthPowerModPrime p 𝔩 (x^m) ↔ IsPthPowerModPrime p 𝔩 (x^n)`.

This is the Fermat-style "natural-number → modular" collapse: the
discrepancy `m - n = p · k` (as integers) gives `x^m = x^n · (x^k)^p`,
and `(x^k)^p` is a `p`-th power that drops out modulo `𝔩` (provided
`x^k ∉ 𝔩`, which follows from `x ∉ 𝔩` and `𝔩` prime). -/
theorem IsPthPowerModPrime.pow_eq_of_modEq [𝔩.IsMaximal]
    {x : R} (hx : x ∉ 𝔩) {m n : ℕ} (h : (p : ℤ) ∣ (m : ℤ) - n) :
    IsPthPowerModPrime p 𝔩 (x ^ m) ↔ IsPthPowerModPrime p 𝔩 (x ^ n) := by
  haveI : 𝔩.IsPrime := Ideal.IsMaximal.isPrime ‹_›
  rcases le_or_gt n m with hle | hlt
  · obtain ⟨k, hk⟩ : p ∣ m - n := by
      have h_int_eq : ((m - n : ℕ) : ℤ) = (m : ℤ) - n := by omega
      exact_mod_cast (show ((p : ℕ) : ℤ) ∣ ((m - n : ℕ) : ℤ) by
        rw [h_int_eq]
        exact h)
    rw [show x ^ m = x ^ n * (x ^ k) ^ p from by
      rw [show m = n + p * k from by omega, pow_add, pow_mul, pow_right_comm]]
    exact IsPthPowerModPrime.mul_pow_iff (pow_notMem_of_notMem hx k)
  · obtain ⟨k, hk⟩ : p ∣ n - m := by
      have h_neg : (p : ℤ) ∣ (n : ℤ) - m := by
        have := dvd_neg.mpr h; rw [neg_sub] at this; exact this
      have h_int_eq : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := by omega
      exact_mod_cast (show ((p : ℕ) : ℤ) ∣ ((n - m : ℕ) : ℤ) by
        rw [h_int_eq]
        exact h_neg)
    rw [show x ^ n = x ^ m * (x ^ k) ^ p from by
      rw [show n = m + p * k from by omega, pow_add, pow_mul, pow_right_comm]]
    exact (IsPthPowerModPrime.mul_pow_iff (pow_notMem_of_notMem hx k)).symm

end PthPowerTransfer

section PollaczekLogTransfer

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace FLT37

variable {p : ℕ} [hp : Fact p.Prime]
  {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  {𝔩 : Ideal (𝓞 K)} [𝔩.IsMaximal]

/-- The "α" witness from `cyclotomicSigmaOfUnit_smul_pollaczekR_balanced`,
extracted as a named definition for use in the
`IsPthPowerModPrime`-transfer chain. This is the product
`∏_b F_b ^ ((a⁻¹.val^E · b^E -ₙ ((a⁻¹ · b).val)^E) / p)` over `b` in
`Finset.Ico 1 p`, with `E = p - 1 - i`. -/
noncomputable def pollaczekBalancedAlpha (a : (ZMod p)ˣ) (i : ℕ) : 𝓞 K :=
  ∏ b ∈ Finset.Ico 1 p,
    pollaczekRFactor p K b ^
      ((((a⁻¹ : (ZMod p)ˣ) : ZMod p).val ^ (p - 1 - i) * b ^ (p - 1 - i) -
        (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b).val ^ (p - 1 - i)) / p)

/-- The "β" witness from `cyclotomicSigmaOfUnit_smul_pollaczekR_balanced`. -/
noncomputable def pollaczekBalancedBeta (a : (ZMod p)ˣ) (i : ℕ) : 𝓞 K :=
  ∏ b ∈ Finset.Ico 1 p,
    pollaczekRFactor p K b ^
      (((((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b).val ^ (p - 1 - i) -
        ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val ^ (p - 1 - i) * b ^ (p - 1 - i)) / p)

/-- **`IsPthPowerModPrime` transfer for the σ_a Pollaczek balanced
equality.** Combining
`cyclotomicSigmaOfUnit_smul_pollaczekR_balanced` (the LV004d balanced
identity in `𝓞 K`) with `IsPthPowerModPrime.transfer_balanced` (the
mod-`p`-th-powers transfer through a balanced `α^p`-`β^p` equation),
provided the two `Nat`-power witnesses
`pollaczekBalancedAlpha`, `pollaczekBalancedBeta` are not in `𝔩`,
we obtain

  `IsPthPowerModPrime p 𝔩 (σ_a(R_i)) ↔
   IsPthPowerModPrime p 𝔩 (R_i ^ (a⁻¹.val)^{p-1-i})`.

Specialising `a = pollaczekPrimRoot p` and using `inv_val_pow_E_eq_pow_i`
to absorb the `(a⁻¹.val)^{p-1-i}` exponent (collapsed mod `p`) into
`g^i`, this reduces the residue test on `σ_g(R_i)` to a residue test
on `R_i^{g^i}`. -/
theorem isPthPowerModPrime_sigma_smul_pollaczekR_iff
    (a : (ZMod p)ˣ) (i : ℕ)
    (hα : pollaczekBalancedAlpha (p := p) (K := K) a i ∉ 𝔩)
    (hβ : pollaczekBalancedBeta (p := p) (K := K) a i ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩
        (cyclotomicSigmaOfUnit (p := p) K a • pollaczekR p K i) ↔
      IsPthPowerModPrime p 𝔩
        (pollaczekR p K i ^ (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val ^ (p - 1 - i))) := by
  refine IsPthPowerModPrime.transfer_balanced ?_ hα hβ
  exact cyclotomicSigmaOfUnit_smul_pollaczekR_balanced (p := p) (K := K) a i

/-- **`IsPthPowerModPrime` transfer with Fermat-collapsed exponent.**
Composes `isPthPowerModPrime_sigma_smul_pollaczekR_iff` with
`IsPthPowerModPrime.pow_eq_of_modEq` and the Fermat reduction
`inv_val_pow_E_eq_pow_i (g⁻¹.val)^{p-1-i} ≡ g^i (mod p)` to give

  `IsPthPowerModPrime p 𝔩 (σ_g(R_i)) ↔
   IsPthPowerModPrime p 𝔩 (R_i ^ (g^i).val)`,

provided `pollaczekBalancedAlpha`, `pollaczekBalancedBeta`, and `R_i`
are all `∉ 𝔩`, and `i < p - 1`.

This is the Pollaczek-identity form ready for the LV004g final
assembly: combining with LV004e's half-range factorisation and LV004c's
residue substitution `ζ ≡ t^k (mod 𝔩)` will reach the certificate
`Q_i^k (mod ℓ)` of LV001/2. -/
theorem isPthPowerModPrime_sigma_smul_pollaczekR_pow_i_iff
    (g : (ZMod p)ˣ) (i : ℕ) (hi : i < p - 1)
    (hα : pollaczekBalancedAlpha (p := p) (K := K) g i ∉ 𝔩)
    (hβ : pollaczekBalancedBeta (p := p) (K := K) g i ∉ 𝔩)
    (hR : pollaczekR p K i ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩
        (cyclotomicSigmaOfUnit (p := p) K g • pollaczekR p K i) ↔
      IsPthPowerModPrime p 𝔩
        (pollaczekR p K i ^ (((g : (ZMod p)ˣ) : ZMod p) ^ i).val) := by
  rw [isPthPowerModPrime_sigma_smul_pollaczekR_iff (p := p) (K := K) g i hα hβ]
  apply IsPthPowerModPrime.pow_eq_of_modEq hR
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := inv_val_pow_E_eq_pow_i (p := p) g hi
  push_cast at h ⊢
  rw [ZMod.natCast_val, ZMod.cast_id] at h
  rw [sub_eq_zero, ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **`(ζ - 1) ∉ lehmerVandiverPrime`.** The cyclotomic-difference unit
`ζ - 1` is not in the prime `𝔩`. (Equivalently: `ζ ≢ 1 (mod 𝔩)`,
which holds because `ζ ≡ t^k (mod 𝔩)` and `t^k ≢ 1 (mod ℓ)` by the
hypothesis `ht_ne`.)

This is the residue-field non-degeneracy needed for the half-range
factorisation analysis: the `(ζ^a - 1)` factors of LV004e's main
product are nonzero modulo `𝔩`. -/
theorem zeta_sub_one_notMem_lehmerVandiverPrime
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger - 1 ∉
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  intro hmem
  have h_zeta_eq := lehmerVandiverPrime_zeta_sub_tk_mem p ℓ k hℓ ht_coprime ht_ne
  have h_diff : (((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ))) - 1 ∈
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
    have h_sub := (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).sub_mem hmem h_zeta_eq
    have hrw : (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger - 1 -
          ((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger -
            ((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ))) =
        ((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ)) - 1 := by ring
    rw [hrw] at h_sub; exact h_sub
  simp only [lehmerVandiverPrime] at h_diff
  rw [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.mem_ker, map_sub, map_natCast, map_one, map_sub, map_natCast,
    map_one] at h_diff
  rw [sub_eq_zero, ZMod.natCast_val, ZMod.cast_id] at h_diff
  exact ht_ne h_diff

set_option backward.isDefEq.respectTransparency false in
/-- **Residue substitution for ζ-powers.** Extension of
`lehmerVandiverPrime_zeta_sub_tk_mem` to powers: `ζ^a ≡ ((t^k).val)^a
(mod 𝔩)`. Equivalently,

  `ζ^a - ((t^k).val)^a ∈ lehmerVandiverPrime p ℓ k h`,

via the elementary fact `x - y ∣ x^a - y^a` (`sub_dvd_pow_sub_pow`)
applied inside the prime ideal `𝔩`. This is the "raw" substitution
step needed to convert `(ζ^a - 1)` factors of the LV004e half-range
product to `(t^{ka} - 1)` factors of the certificate
`lehmerVandiverProduct` from LV001/2. -/
theorem lehmerVandiverPrime_zeta_pow_sub_tk_pow_mem
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (a : ℕ) :
    (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a -
        ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a : 𝓞 (CyclotomicField p ℚ)) ∈
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  have h_base := lehmerVandiverPrime_zeta_sub_tk_mem p ℓ k hℓ ht_coprime ht_ne
  have hdvd := sub_dvd_pow_sub_pow
      ((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
        𝓞 (CyclotomicField p ℚ))
      ((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ)) a
  exact (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).mem_of_dvd hdvd h_base

set_option backward.isDefEq.respectTransparency false in
/-- **`(ζ^a - 1) ∉ lehmerVandiverPrime` (parameterised version).** Under
the hypothesis `(t : ZMod ℓ)^(k * a) ≠ 1`, we have
`(ζ^a - 1) ∉ 𝔩`.

Proof analogous to `zeta_sub_one_notMem_lehmerVandiverPrime`: if
`ζ^a - 1 ∈ 𝔩`, then via `lehmerVandiverPrime_zeta_pow_sub_tk_pow_mem`
(which gives `ζ^a ≡ ((t^k).val)^a (mod 𝔩)`), `((t^k).val)^a - 1 ∈ 𝔩`.
Applying `cyclotomicReduction` reveals `t^{ka} - 1 = 0` in `ZMod ℓ`,
contradicting the hypothesis.

For `a = 1` and `ka = k`, this recovers
`zeta_sub_one_notMem_lehmerVandiverPrime` (with `ht_ne` providing the
non-degeneracy hypothesis).

The hypothesis `(t : ZMod ℓ)^(k * a) ≠ 1` is what the LV001/2 certificate
verifies for the relevant range of `a`. For `a` in the half range
`[1, (p-1)/2]`, this holds iff `t` has order divisible by `p / gcd(p, a)`,
i.e., iff `p ∤ a` and `t^k ≠ 1` (since `(ZMod ℓ)ˣ` has order `kp` and
the only divisors not dividing `k` are multiples of `p`). -/
theorem zeta_pow_sub_one_notMem_lehmerVandiverPrime
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (a : ℕ)
    (ha : (t : ZMod ℓ) ^ (k * a) ≠ 1) :
    (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a - 1 ∉
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  intro hmem
  have h_pow := lehmerVandiverPrime_zeta_pow_sub_tk_pow_mem
    (p := p) ℓ k hℓ ht_coprime ht_ne a
  have h_diff : ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a : 𝓞 (CyclotomicField p ℚ)) - 1 ∈
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
    have h_sub := (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).sub_mem hmem h_pow
    have hrw : (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a - 1 -
          ((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a -
            ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a : 𝓞 (CyclotomicField p ℚ))) =
        ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a : 𝓞 (CyclotomicField p ℚ)) - 1 := by
      ring
    rw [hrw] at h_sub; exact h_sub
  simp only [lehmerVandiverPrime] at h_diff
  rw [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.mem_ker, map_sub, map_pow, map_natCast, map_one,
    map_sub, map_pow, map_natCast, map_one] at h_diff
  rw [sub_eq_zero, ZMod.natCast_val, ZMod.cast_id, ← pow_mul] at h_diff
  exact ha h_diff

/-- **`IsPthPower (half-range main) ↔ IsPthPower (cyclotomic-unit
half-range)` modulo `𝔩`.** Using LV004e's
`pollaczekR_half_range_main_zeta_form`,

  ∏_a F_a^{2 a^E} = (∏_a (ζ^{-a})^{a^E}) · (∏_a (ζ^a - 1)^{2 a^E}),

so when the ζ-prefactor `∏_a (ζ^{-a})^{a^E}` is `IsPthPower mod 𝔩` and
`∉ 𝔩`, applying `IsPthPowerModPrime.mul_iff` gives

  IsPthPower (∏ F_a^{2 a^E}) ↔ IsPthPower (∏ (ζ^a - 1)^{2 a^E}).

This is the cyclotomic-unit form ready for the LV004c residue
substitution `ζ ≡ t^k (mod 𝔩)`. -/
theorem isPthPowerModPrime_main_iff_zeta_form
    (hp_odd : p ≠ 2) (i : ℕ)
    (hpre_pth : IsPthPowerModPrime p 𝔩
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((zetaUnitR p K ^ (-(a : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) ^
          a ^ (p - 1 - i)))
    (hpre_ne : (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((zetaUnitR p K ^ (-(a : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) ^
          a ^ (p - 1 - i)) ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          pollaczekRFactor p K a ^ (2 * a ^ (p - 1 - i))) ↔
      IsPthPowerModPrime p 𝔩
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ a - 1) ^ (2 * a ^ (p - 1 - i))) := by
  rw [pollaczekR_half_range_main_zeta_form (p := p) (K := K) hp_odd i, mul_comm _ _]
  exact IsPthPowerModPrime.mul_iff hpre_ne hpre_pth

/-- **`IsPthPower R_i ↔ IsPthPower (half-range main)` modulo `𝔩`.**

Apply LV004e's `pollaczekR_half_range_factorisation` to express
`R_i = sign · main · γ^p`, then strip:
* `γ^p` via `IsPthPowerModPrime.mul_pow_iff` (`γ ∉ 𝔩`),
* `sign` via `IsPthPowerModPrime.mul_iff` (sign is `IsPthPower mod 𝔩`
  and `∉ 𝔩`).

The hypotheses `hsign_pth` and `hsign_ne` are needed because the sign
factor `∏ (-1)^{(p-a)^E}` may or may not be a `p`-th power mod `𝔩`
depending on the parity arithmetic; for the certificate setup
(`(p, i, ℓ) = (37, 32, 149)`, etc.), these can be verified
numerically. -/
theorem isPthPowerModPrime_pollaczekR_iff_main
    (hp_odd : p ≠ 2) (i : ℕ) (hE_even : Even (p - 1 - i))
    (hsign_pth : IsPthPowerModPrime p 𝔩
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((-1 : 𝓞 K) ^ (p - a) ^ (p - 1 - i))))
    (hsign_ne : (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((-1 : 𝓞 K) ^ (p - a) ^ (p - 1 - i))) ∉ 𝔩)
    (hgamma_ne : (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          pollaczekRFactor p K a ^
            (((p - a) ^ (p - 1 - i) - a ^ (p - 1 - i)) / p)) ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩 (pollaczekR p K i) ↔
      IsPthPowerModPrime p 𝔩
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          pollaczekRFactor p K a ^ (2 * a ^ (p - 1 - i))) := by
  rw [pollaczekR_half_range_factorisation p K hp_odd i hE_even]
  rw [IsPthPowerModPrime.mul_pow_iff (α := _) hgamma_ne]
  rw [mul_comm _ _]
  exact IsPthPowerModPrime.mul_iff hsign_ne hsign_pth

/-- **Quotient iso `𝓞 K / lehmerVandiverPrime ≃+* ZMod ℓ`.** Identifies
the residue field at `lehmerVandiverPrime` with `ZMod ℓ`, via the
composition

  𝓞 K / 𝔩 ≃+* CyclotomicIntegers p / ker(cyclotomicReduction) ≃+* ZMod ℓ.

The first iso comes from `Ideal.quotientEquiv` applied to the
flt-regular iso `equiv : CyclotomicIntegers p ≃+* 𝓞 K` (which sends the
kernel to `lehmerVandiverPrime` by construction). The second iso is
`RingHom.quotientKerEquivOfSurjective` applied to `cyclotomicReduction`,
which is surjective because every `n : ZMod ℓ` is the image of
`(n.val : CyclotomicIntegers p)`. -/
noncomputable def lehmerVandiverPrime_quotientEquiv
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    𝓞 (CyclotomicField p ℚ) ⧸ lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne ≃+*
      ZMod ℓ := by
  have hsurj : Function.Surjective (cyclotomicReduction p ℓ k hℓ ht_coprime ht_ne) := by
    intro x
    refine ⟨(x.val : CyclotomicIntegers p), ?_⟩
    rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  refine RingEquiv.trans ?_ (RingHom.quotientKerEquivOfSurjective hsurj)
  apply Ideal.quotientEquiv _ _ (CyclotomicIntegers.equiv p).symm
  simp only [lehmerVandiverPrime]
  exact (Ideal.map_comap_of_surjective
      ((CyclotomicIntegers.equiv p).symm.toRingHom)
      (CyclotomicIntegers.equiv p).symm.surjective _).symm

/-- **`Fintype` instance for `𝓞 K / lehmerVandiverPrime`.** Transferred
from `Fintype (ZMod ℓ)` via `lehmerVandiverPrime_quotientEquiv`. -/
@[reducible]
noncomputable def lehmerVandiverPrime_quotientFintype
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    Fintype (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :=
  Fintype.ofEquiv (ZMod ℓ)
    (lehmerVandiverPrime_quotientEquiv ℓ k hℓ ht_coprime ht_ne).symm.toEquiv

/-- **Cardinality of the residue field at `lehmerVandiverPrime` is `ℓ`.**
Direct consequence of the iso to `ZMod ℓ` (`Fintype.ofEquiv_card` +
`ZMod.card`). -/
theorem lehmerVandiverPrime_quotient_card
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    @Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
      (lehmerVandiverPrime_quotientFintype ℓ k hℓ ht_coprime ht_ne) = ℓ := by
  haveI : NeZero ℓ := ⟨(Fact.out (p := ℓ.Prime)).ne_zero⟩
  rw [Fintype.ofEquiv_card]
  exact ZMod.card ℓ

/-- **Cyclic-group `p`-th-power criterion at `lehmerVandiverPrime`.**
For `x ∉ 𝔩`,

  IsPthPowerModPrime p 𝔩 x ↔ Ideal.Quotient.mk 𝔩 (x ^ k) = 1.

This is the LV004f cyclic-group criterion specialised to
`lehmerVandiverPrime` using `lehmerVandiverPrime_quotient_card` (which
gives `Fintype.card (𝓞 K / 𝔩) = ℓ`) and the relation
`(ℓ - 1) / p = k` from `hℓ : ℓ = k * p + 1`.

This converts the residue test on `x` to a polynomial-time-checkable
condition on `Q(x^k)` in the residue field — the form consumed by the
LV001/2 certificate `lehmerVandiverNonTrivial`. -/
theorem isPthPowerModPrime_lehmerVandiverPrime_iff
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    {x : 𝓞 (CyclotomicField p ℚ)}
    (hx : x ∉ lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :
    IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) x ↔
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (x ^ k) = 1 := by
  letI : (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsMaximal := by
    have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
    exact Ideal.IsPrime.isMaximal hprime (by
      have h := lehmerVandiverPrime_natCast_ℓ_mem p ℓ k hℓ ht_coprime ht_ne
      intro h_zero
      rw [h_zero] at h
      have hℓ_zero := by
        simpa using h
      have hℓ_pos : 0 < ℓ := (Fact.out (p := ℓ.Prime)).pos
      omega)
  letI : Fintype (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :=
    lehmerVandiverPrime_quotientFintype ℓ k hℓ ht_coprime ht_ne
  have hcard : Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) = ℓ := by
    change @Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (lehmerVandiverPrime_quotientFintype ℓ k hℓ ht_coprime ht_ne) = ℓ
    exact lehmerVandiverPrime_quotient_card (p := p) ℓ k hℓ ht_coprime ht_ne
  have hp_pos : 0 < p := hp.out.pos
  have hcard_sub : Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) - 1 = k * p := by
    rw [hcard, hℓ]; omega
  have hp_dvd : p ∣ Fintype.card
      (𝓞 (CyclotomicField p ℚ) ⧸ lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) - 1 := by
    rw [hcard_sub]; exact ⟨k, by ring⟩
  have h_div_eq : (Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) - 1) / p = k := by
    rw [hcard_sub, Nat.mul_div_cancel _ hp_pos]
  rw [isPthPowerModPrime_iff_pow_card_div_p_eq_one hp_pos hp_dvd hx, h_div_eq]

set_option backward.isDefEq.respectTransparency false in
/-- **Quotient-level residue substitution: `Q(ζ^a - 1) = Q(((t^k).val)^a - 1)`.**
The LV004c residue substitution applied to the cyclotomic-unit factor:
in `𝓞 K / lehmerVandiverPrime`, the image of `ζ^a - 1` equals the image
of `((t^k).val)^a - 1`. Direct from
`lehmerVandiverPrime_zeta_pow_sub_tk_pow_mem` via `Ideal.Quotient.eq`. -/
theorem lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (a : ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a - 1) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a - 1 : 𝓞 (CyclotomicField p ℚ)) := by
  rw [Ideal.Quotient.eq]
  have h_pow := lehmerVandiverPrime_zeta_pow_sub_tk_pow_mem
    (p := p) ℓ k hℓ ht_coprime ht_ne a
  have hrw : (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a - 1 -
        ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a - 1 : 𝓞 (CyclotomicField p ℚ)) =
      (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a -
        ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a : 𝓞 (CyclotomicField p ℚ)) := by ring
  rw [hrw]
  exact h_pow

set_option backward.isDefEq.respectTransparency false in
/-- **Product-level residue substitution:
`Q(∏ (ζ^a - 1)^{...}) = Q(∏ (((t^k).val)^a - 1)^{...})`.**
The half-range cyclotomic-unit product, when evaluated in
`𝓞 K / lehmerVandiverPrime`, equals the corresponding certificate-side
product after substituting `ζ ≡ (t^k).val (mod 𝔩)` term-wise. Proof:
apply `Finset.prod_congr` with the per-term substitution from
`lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq`. -/
theorem lehmerVandiverPrime_quotient_half_range_eq
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a - 1) ^
            (2 * a ^ (p - 1 - i))) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a - 1 : 𝓞 (CyclotomicField p ℚ)) ^
            (2 * a ^ (p - 1 - i))) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl ?_
  intro a _
  rw [map_pow, map_pow]
  congr 1
  exact lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
    (p := p) ℓ k hℓ ht_coprime ht_ne a

/-- **Squaring lemma at `lehmerVandiverPrime` (LV004g-2).** For `p` an
odd prime and `x ∉ lehmerVandiverPrime`,

  IsPthPowerModPrime p 𝔩 (x^2) ↔ IsPthPowerModPrime p 𝔩 x.

This is the LV004g-2 step bridging `R_i ≡ E_i^2 · units (mod p-th
powers)` to `IsPthPower R_i ↔ IsPthPower E_i`.

Proof: by the cyclic criterion `isPthPowerModPrime_lehmerVandiverPrime_iff`,
this reduces to `Q(x^{2k}) = 1 ↔ Q(x^k) = 1` in `𝓞 K / 𝔩`.

The forward direction is the substantive one. By Fermat's little
theorem in the residue field of size `ℓ` (`FiniteField.pow_card_sub_one_eq_one`),
`Q(x)^{ℓ-1} = 1` for `Q(x) ≠ 0`. Since `ℓ - 1 = k · p`, this gives
`Q(x^k)^p = 1`, so `orderOf (Q(x^k))` divides `p`.

Combined with `Q(x^k)^2 = 1` (the hypothesis), `orderOf` divides
`gcd(p, 2) = 1` (using `p` odd prime), so `Q(x^k) = 1`. -/
theorem isPthPowerModPrime_lehmerVandiverPrime_sq_iff
    (hp_odd : p ≠ 2) (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    {x : 𝓞 (CyclotomicField p ℚ)}
    (hx : x ∉ lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :
    IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) (x ^ 2) ↔
      IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) x := by
  letI : (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsMaximal := by
    have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
    exact Ideal.IsPrime.isMaximal hprime (by
      have h := lehmerVandiverPrime_natCast_ℓ_mem p ℓ k hℓ ht_coprime ht_ne
      intro h_zero
      rw [h_zero] at h
      have hℓ_zero := by
        simpa using h
      have hℓ_pos : 0 < ℓ := (Fact.out (p := ℓ.Prime)).pos
      omega)
  have hx2 : x ^ 2 ∉ lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne :=
    pow_notMem_of_notMem hx 2
  rw [isPthPowerModPrime_lehmerVandiverPrime_iff (p := p) ℓ k hℓ ht_coprime ht_ne hx2,
    isPthPowerModPrime_lehmerVandiverPrime_iff (p := p) ℓ k hℓ ht_coprime ht_ne hx,
    show (x ^ 2) ^ k = (x ^ k) ^ 2 from by rw [← pow_mul, mul_comm, pow_mul], map_pow]
  refine ⟨?_, fun h => by rw [h]; ring⟩
  intro hsq
  letI : Field (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :=
    Ideal.Quotient.field _
  letI : Fintype (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :=
    lehmerVandiverPrime_quotientFintype ℓ k hℓ ht_coprime ht_ne
  have hxk_ne : Ideal.Quotient.mk
      (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) (x ^ k) ≠ 0 :=
    fun h => pow_notMem_of_notMem hx k (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let yu : (𝓞 (CyclotomicField p ℚ) ⧸
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)ˣ := Units.mk0 _ hxk_ne
  have hyu_p : yu ^ p = 1 := by
    apply Units.ext
    change (Ideal.Quotient.mk _ (x ^ k)) ^ p = 1
    rw [← map_pow, ← pow_mul, show k * p = ℓ - 1 from by omega, map_pow]
    have hcard : Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) = ℓ := by
      change @Fintype.card _
          (lehmerVandiverPrime_quotientFintype ℓ k hℓ ht_coprime ht_ne) = ℓ
      exact lehmerVandiverPrime_quotient_card (p := p) ℓ k hℓ ht_coprime ht_ne
    have hQx_ne : Ideal.Quotient.mk
        (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) x ≠ 0 :=
      fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h)
    rw [show (ℓ - 1 : ℕ) = Fintype.card (𝓞 (CyclotomicField p ℚ) ⧸
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) - 1 from by rw [hcard]]
    exact FiniteField.pow_card_sub_one_eq_one _ hQx_ne
  have hyu_2 : yu ^ 2 = 1 := by
    apply Units.ext
    change (Ideal.Quotient.mk _ (x ^ k)) ^ 2 = 1
    exact hsq
  have h_coprime : Nat.Coprime p 2 := by
    rcases Nat.coprime_or_dvd_of_prime hp.out 2 with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h) hp_odd
  -- `yu ^ p = 1` and `yu ^ 2 = 1` with `p, 2` coprime force `yu = 1`
  -- (mathlib's `pow_eq_one_iff_of_coprime`).
  have hyu_eq : yu = 1 := (pow_eq_one_iff_of_coprime h_coprime).mp ⟨hyu_p, hyu_2⟩
  exact congr_arg Units.val hyu_eq

/-- **`x² = y² ↔ x = ±y` in `ZMod ℓ` for `ℓ` prime.** Standard field
algebra: `x² = y² ↔ (x - y)(x + y) = 0`, and `ZMod ℓ` is an integral
domain for `ℓ` prime.

Used in LV004g-3 to convert the chain endpoint
`lehmerVandiverProduct² = lehmerVandiverPrefactor²` to a disjunction
`lehmerVandiverProduct = ±lehmerVandiverPrefactor` matching the
certificate predicate. -/
theorem ZMod_sq_eq_sq_iff_eq_or_neg_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (x y : ZMod ℓ) :
    x ^ 2 = y ^ 2 ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have hfact : (x - y) * (x + y) = 0 := by ring_nf; linear_combination h
    rcases mul_eq_zero.mp hfact with hxy | hxy
    · left; linear_combination hxy
    · right; linear_combination hxy
  · rintro (h | h)
    · rw [h]
    · rw [h]; ring

set_option backward.isDefEq.respectTransparency false in
/-- **`IsPthPower (cyclotomic-half-range) ↔ IsPthPower pollaczekUnit` at
`lehmerVandiverPrime`** — the LV004g composition step.

Combining LV004g-1's bridge identity (which gives
`∏ (ζ^a - 1)^{2 a^E} = (ζ - 1)^{2S} · pollaczekUnit²`) with the
LV004g-2 squaring lemma (`IsPthPower x² ↔ IsPthPower x` for `p` odd
and `x ∉ 𝔩`), we strip the squaring + the `(ζ-1)^{2S}` prefactor
provided the latter is `IsPthPower mod 𝔩` and `∉ 𝔩`.

The `(ζ-1) ∉ 𝔩` part is automatic from
`zeta_sub_one_notMem_lehmerVandiverPrime` (so `(ζ-1)^N ∉ 𝔩` by
`pow_notMem_of_notMem`); `IsPthPower (ζ-1)^{2S} mod 𝔩` is an auxiliary
condition the LV001/2 setup verifies for the relevant `(p, i)`. -/
theorem isPthPowerModPrime_zeta_form_iff_pollaczekUnit
    (hp_odd : p ≠ 2) (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1)
    {t : ℕ} (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (i : ℕ)
    (hpoll_ne : (pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
    (hzm1_pth : IsPthPowerModPrime p
        (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) - 1) ^
          (2 * ∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))))
    (hzm1_ne : ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) - 1) ^
          (2 * ∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :
    IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) ^ a - 1) ^
            (2 * a ^ (p - 1 - i))) ↔
      IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) := by
  letI : (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsMaximal := by
    have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
    exact Ideal.IsPrime.isMaximal hprime (by
      have h := lehmerVandiverPrime_natCast_ℓ_mem p ℓ k hℓ ht_coprime ht_ne
      intro h_zero
      rw [h_zero] at h
      have hℓ_zero := by
        simpa using h
      have hℓ_pos : 0 < ℓ := (Fact.out (p := ℓ.Prime)).pos
      omega)
  rw [zeta_pow_sub_one_prod_eq_pollaczekUnit_sq_mul_zeta_sub_one_pow
      p (CyclotomicField p ℚ) hp_odd i, mul_comm]
  rw [IsPthPowerModPrime.mul_iff hzm1_ne hzm1_pth]
  exact isPthPowerModPrime_lehmerVandiverPrime_sq_iff
    hp_odd ℓ k hℓ ht_coprime ht_ne hpoll_ne

set_option backward.isDefEq.respectTransparency false in
/-- **LV004g main theorem: `IsPthPower R_i ↔ IsPthPower pollaczekUnit`
at `lehmerVandiverPrime`.** The full LV004g chain composition:

  IsPthPower R_i mod 𝔩
  ↔ [pollaczekR_half_range_factorisation: strip γ^p and sign]
  IsPthPower (∏ F_a^{2 a^E}) mod 𝔩
  ↔ [pollaczekR_half_range_main_zeta_form: strip ζ-prefactor]
  IsPthPower (∏ (ζ^a - 1)^{2 a^E}) mod 𝔩
  ↔ [zeta_form_iff_pollaczekUnit: bridge + squaring]
  IsPthPower (pollaczekUnit p K i) mod 𝔩.

Bundles all auxiliary `IsPthPower mod 𝔩` and `∉ 𝔩` hypotheses on:
* the LV004e sign and γ factors,
* the LV004e ζ-prefactor `∏ (ζ^{-a})^{a^E}`,
* the LV004g-1 bridge prefactor `(ζ-1)^{2S}`,
* the test elements `R_i`, `pollaczekUnit p K i`. -/
theorem isPthPowerModPrime_pollaczekR_iff_pollaczekUnit
    (hp_odd : p ≠ 2) (i : ℕ) (hE_even : Even (p - 1 - i))
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1)
    {t : ℕ} (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (hsign_pth : IsPthPowerModPrime p
        (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((-1 : 𝓞 (CyclotomicField p ℚ)) ^ (p - a) ^ (p - 1 - i))))
    (hsign_ne : (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((-1 : 𝓞 (CyclotomicField p ℚ)) ^ (p - a) ^ (p - 1 - i))) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
    (hgamma_ne : (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          pollaczekRFactor p (CyclotomicField p ℚ) a ^
            (((p - a) ^ (p - 1 - i) - a ^ (p - 1 - i)) / p)) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
    (hpre_pth : IsPthPowerModPrime p
        (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((zetaUnitR p (CyclotomicField p ℚ) ^ (-(a : ℤ)) :
              (𝓞 (CyclotomicField p ℚ))ˣ) :
            𝓞 (CyclotomicField p ℚ)) ^ a ^ (p - 1 - i)))
    (hpre_ne : (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((zetaUnitR p (CyclotomicField p ℚ) ^ (-(a : ℤ)) :
              (𝓞 (CyclotomicField p ℚ))ˣ) :
            𝓞 (CyclotomicField p ℚ)) ^ a ^ (p - 1 - i)) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
    (hpoll_ne : (pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
    (hzm1_pth : IsPthPowerModPrime p
        (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) - 1) ^
          (2 * ∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))))
    (hzm1_ne : ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) - 1) ^
          (2 * ∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :
    IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (pollaczekR p (CyclotomicField p ℚ) i) ↔
      IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) := by
  letI : (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsMaximal := by
    have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
    exact Ideal.IsPrime.isMaximal hprime (by
      have h := lehmerVandiverPrime_natCast_ℓ_mem p ℓ k hℓ ht_coprime ht_ne
      intro h_zero
      rw [h_zero] at h
      have hℓ_zero := by
        simpa using h
      have hℓ_pos : 0 < ℓ := (Fact.out (p := ℓ.Prime)).pos
      omega)
  rw [isPthPowerModPrime_pollaczekR_iff_main (p := p) (K := CyclotomicField p ℚ)
      hp_odd i hE_even hsign_pth hsign_ne hgamma_ne]
  rw [isPthPowerModPrime_main_iff_zeta_form (p := p) (K := CyclotomicField p ℚ)
      hp_odd i hpre_pth hpre_ne]
  exact isPthPowerModPrime_zeta_form_iff_pollaczekUnit
    (p := p) hp_odd ℓ k hℓ ht_coprime ht_ne i hpoll_ne hzm1_pth hzm1_ne

set_option backward.isDefEq.respectTransparency false in
/-- **`IsPthPower pollaczekUnit` cyclic-criterion form.** Specialises
`isPthPowerModPrime_lehmerVandiverPrime_iff` to `x = pollaczekUnit p K i`,
giving the residue test `Q(pollaczekUnit^k) = 1`.

For `pollaczekUnit ∉ 𝔩` (a numerical hypothesis the LV001/2 setup
verifies),

  IsPthPower (pollaczekUnit p K i) mod 𝔩
    ↔ Q((pollaczekUnit p K i : 𝓞 K)^k) = 1 in 𝓞 K / 𝔩.

Combined with `isPthPowerModPrime_pollaczekR_iff_pollaczekUnit`, this
converts the residue test on `R_i` (the auxiliary Pollaczek element)
to a polynomial equation in the residue field at `lehmerVandiverPrime`. -/
theorem isPthPowerModPrime_pollaczekUnit_iff_quotient_pow_eq_one
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1)
    {t : ℕ} (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (i : ℕ)
    (hpoll_ne : (pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ∉
        lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne) :
    IsPthPowerModPrime p (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ↔
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ^ k) = 1 := by
  letI : (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsMaximal := by
    have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
    exact Ideal.IsPrime.isMaximal hprime (by
      have h := lehmerVandiverPrime_natCast_ℓ_mem p ℓ k hℓ ht_coprime ht_ne
      intro h_zero
      rw [h_zero] at h
      have hℓ_zero := by
        simpa using h
      have hℓ_pos : 0 < ℓ := (Fact.out (p := ℓ.Prime)).pos
      omega)
  exact isPthPowerModPrime_lehmerVandiverPrime_iff
    (p := p) ℓ k hℓ ht_coprime ht_ne hpoll_ne

end FLT37

end PollaczekLogTransfer

end BernoulliRegular
