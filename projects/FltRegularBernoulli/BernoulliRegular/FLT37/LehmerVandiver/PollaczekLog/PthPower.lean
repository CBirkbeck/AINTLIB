module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.FieldTheory.Finite.Basic

/-!
# `p`-th powers modulo a prime ideal

For an odd prime `p`, a commutative ring `R`, an ideal `𝔩 ⊂ R`, and an
element `x : R`, we say `x` is a **`p`-th power modulo `𝔩`** if its
image in `R ⧸ 𝔩` is a `p`-th power, that is

  `∃ y : R ⧸ 𝔩, (Ideal.Quotient.mk 𝔩 x) = y ^ p`.

This is the predicate used in Washington's Proposition 8.18 (Pollaczek's
log identity, Washington p. 158) and is the central residue test in the
Lehmer–Vandiver certificate of Theorem 9.5 (p. 176).

This file provides:

* `BernoulliRegular.IsPthPowerModPrime` — the predicate.
* `IsPthPowerModPrime.one`, `.mul`, `.pow_self` — basic closure
  properties: `1` is a `p`-th power, products of `p`-th powers are
  `p`-th powers, and `x ^ p` is always a `p`-th power.
* `IsPthPowerModPrime.pow` — the image of a `p`-th power under any
  natural-number power is again a `p`-th power.
* `BernoulliRegular.isPthPowerModPrime_iff_pow_card_div_p_eq_one` —
  the **cyclic-group criterion**: when `R ⧸ 𝔩` is a finite field and
  `p ∣ Fintype.card (R ⧸ 𝔩) - 1` and `x ∉ 𝔩`, then `x` is a `p`-th
  power modulo `𝔩` iff `x ^ ((Fintype.card (R ⧸ 𝔩) - 1) / p) ≡ 1
  (mod 𝔩)`.

## Mathlib infrastructure reused

The cyclic-group criterion is proved by combining:

* `IsCyclic` instance for `Rˣ` of a finite integral domain
  (`Mathlib.RingTheory.IntegralDomain`).
* `IsCyclic.card_powMonoidHom_range` (cyclic group / `powMonoidHom`
  cardinalities; `Mathlib.GroupTheory.SpecificGroups.Cyclic`).
* `Fintype.card_units` (`Mathlib.Data.Fintype.Units`) and
  `FiniteField.pow_card_sub_one_eq_one`
  (`Mathlib.FieldTheory.Finite.Basic`) to translate between
  cardinalities of `R ⧸ 𝔩` and `(R ⧸ 𝔩)ˣ`.
* `Ideal.Quotient.field` to upgrade a quotient by a prime / maximal
  ideal to a `Field` instance for the unit-group analysis.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM
  83, §8.3 (Pollaczek units, p. 158) and §9 (Theorem 9.5, p. 176).
* Vandiver, "Fermat's last theorem and the second factor in the
  cyclotomic class number," Bull. AMS 40 (1934) 118–126.
-/

@[expose] public section

namespace BernoulliRegular

open Ideal

variable {R : Type*} [CommRing R]

/-- An element `x : R` is a **`p`-th power modulo the ideal `𝔩`** when
its image in `R ⧸ 𝔩` is a `p`-th power. -/
def IsPthPowerModPrime (p : ℕ) (𝔩 : Ideal R) (x : R) : Prop :=
  ∃ y : R ⧸ 𝔩, Ideal.Quotient.mk 𝔩 x = y ^ p

namespace IsPthPowerModPrime

variable {p : ℕ} {𝔩 : Ideal R}

/-- `1` is always a `p`-th power modulo any ideal: `1 = 1 ^ p`. -/
theorem one : IsPthPowerModPrime p 𝔩 (1 : R) :=
  ⟨1, by simp⟩

/-- The product of two elements that are each `p`-th powers modulo `𝔩`
is again a `p`-th power modulo `𝔩`. -/
theorem mul {x y : R} (hx : IsPthPowerModPrime p 𝔩 x)
    (hy : IsPthPowerModPrime p 𝔩 y) : IsPthPowerModPrime p 𝔩 (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a * b, by rw [map_mul, ha, hb, mul_pow]⟩

/-- For any `x : R`, the element `x ^ p` is a `p`-th power modulo any
ideal `𝔩`. -/
theorem pow_self (x : R) : IsPthPowerModPrime p 𝔩 (x ^ p) :=
  ⟨Ideal.Quotient.mk 𝔩 x, by rw [map_pow]⟩

/-- The natural-number power `x ^ n` of a `p`-th power is again a
`p`-th power modulo `𝔩`. -/
theorem pow {x : R} (hx : IsPthPowerModPrime p 𝔩 x) (n : ℕ) :
    IsPthPowerModPrime p 𝔩 (x ^ n) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a ^ n, ?_⟩
  rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]

end IsPthPowerModPrime

section CyclicCriterion

/-- **Cyclic-group `p`-th-power criterion (unit form).**

In a finite commutative cyclic group `G` with `p ∣ Nat.card G`, an
element `u : G` is a `p`-th power iff `u ^ (Nat.card G / p) = 1`.

Proof: by `IsCyclic.card_powMonoidHom_range`, the image of the `p`-th
power map has cardinality `Nat.card G / Nat.gcd (Nat.card G) p`. When
`p ∣ Nat.card G` this gcd equals `p`, so the image has size
`Nat.card G / p`. The kernel of `(· ^ (Nat.card G / p))` is therefore
the same subgroup as the image of the `p`-th power map (both are the
unique subgroup of index `p` in the cyclic group), and the criterion
follows. -/
theorem isPthPower_iff_pow_card_div_eq_one {G : Type*} [CommGroup G]
    [Finite G] [IsCyclic G] {p : ℕ} (hp : p ∣ Nat.card G) (u : G) :
    (∃ v : G, u = v ^ p) ↔ u ^ (Nat.card G / p) = 1 := by
  -- Rephrase membership in the range of `powMonoidHom p`, and compare with the
  -- kernel of `(· ^ (Nat.card G / p))`.
  have hrange : (∃ v : G, u = v ^ p) ↔ u ∈ (powMonoidHom p : G →* G).range := by
    simp only [MonoidHom.mem_range, powMonoidHom_apply, eq_comm]
  rw [hrange, show u ^ (Nat.card G / p) = (powMonoidHom (Nat.card G / p) : G →* G) u from rfl,
    ← MonoidHom.mem_ker]
  -- Both subgroups have cardinality `Nat.card G / p`.
  have hcardR : Nat.card (powMonoidHom p : G →* G).range = Nat.card G / p := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right hp]
  have hcardK : Nat.card (powMonoidHom (Nat.card G / p) : G →* G).ker
      = Nat.card G / p := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hp)]
  -- The range of `(· ^ p)` is contained in the kernel of
  -- `(· ^ (Nat.card G / p))`: every `p`-th power, when raised to
  -- `Nat.card G / p`, gives a `Nat.card G`-th power, which is `1`.
  have hsubLE : (powMonoidHom p : G →* G).range
      ≤ (powMonoidHom (Nat.card G / p) : G →* G).ker := by
    rintro x ⟨w, rfl⟩
    simp only [MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul]
    rw [mul_comm, Nat.div_mul_cancel hp]
    exact pow_card_eq_one'
  -- In a cyclic finite group there is a unique subgroup of each
  -- divisor cardinality, so the range and kernel coincide.
  have hsub : (powMonoidHom p : G →* G).range = (powMonoidHom (Nat.card G / p) : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge hsubLE
    rw [hcardR, hcardK]
  rw [hsub]

end CyclicCriterion

section IdealCriterion

variable {𝔩 : Ideal R}

/-- **Cyclic-group `p`-th-power criterion (ideal form).**

For a maximal ideal `𝔩` of a commutative ring `R` with finite quotient
`R ⧸ 𝔩`, a prime `p` dividing `Fintype.card (R ⧸ 𝔩) - 1`, and an
element `x ∉ 𝔩`, the element `x` is a `p`-th power modulo `𝔩` iff
`x ^ ((Fintype.card (R ⧸ 𝔩) - 1) / p) ≡ 1 (mod 𝔩)`.

This is the residue test underlying Washington's Proposition 8.18 /
Theorem 9.5: when `𝔩` is a prime of `𝓞 K` over a rational prime
`ℓ ≡ 1 (mod p)` so that `R ⧸ 𝔩 ≅ 𝔽_ℓ`, the criterion becomes
`x ^ k ≡ 1 (mod 𝔩)` where `ℓ = kp + 1`. -/
theorem isPthPowerModPrime_iff_pow_card_div_p_eq_one
    [𝔩.IsMaximal] [Fintype (R ⧸ 𝔩)] {p : ℕ} (hp_pos : 0 < p)
    (hp : p ∣ Fintype.card (R ⧸ 𝔩) - 1) {x : R} (hx : x ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩 x ↔
      Ideal.Quotient.mk 𝔩 (x ^ ((Fintype.card (R ⧸ 𝔩) - 1) / p)) = 1 := by
  classical
  -- Equip `R ⧸ 𝔩` with the field instance from maximality of `𝔩`.
  letI : Field (R ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  -- The image of `x` in the quotient is non-zero, hence a unit.
  have hx0 : (Ideal.Quotient.mk 𝔩 x) ≠ 0 :=
    fun h => hx ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  set u : (R ⧸ 𝔩)ˣ := Units.mk0 _ hx0 with hu_def
  -- The unit group of a finite field is finite cyclic of size `q-1`.
  have hcardUnits : Nat.card (R ⧸ 𝔩)ˣ = Fintype.card (R ⧸ 𝔩) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  -- Apply the cyclic-group criterion to `u`.
  have hpdvd : p ∣ Nat.card (R ⧸ 𝔩)ˣ := hcardUnits ▸ hp
  have hcrit := isPthPower_iff_pow_card_div_eq_one (G := (R ⧸ 𝔩)ˣ) hpdvd u
  -- Translate the unit-group statement back to elements of `R ⧸ 𝔩`.
  rw [hcardUnits] at hcrit
  rw [map_pow]
  refine ⟨fun hxp => ?_, fun hpow => ?_⟩
  · -- `x` is a `p`-th power: extract a unit witness in `R ⧸ 𝔩`.
    obtain ⟨y, hy⟩ := hxp
    have hy0 : y ≠ 0 := fun h => hx0 (by rw [hy, h, zero_pow hp_pos.ne'])
    have heq : u = Units.mk0 y hy0 ^ p := Units.ext (by simp [hu_def, hy])
    have := congrArg Units.val (hcrit.mp ⟨Units.mk0 y hy0, heq⟩)
    simpa [hu_def] using this
  · -- The power equals `1` in `R ⧸ 𝔩`: lift to the unit group.
    have hupow : u ^ ((Fintype.card (R ⧸ 𝔩) - 1) / p) = 1 :=
      Units.ext (by simpa [hu_def] using hpow)
    obtain ⟨v, hv⟩ := hcrit.mpr hupow
    exact ⟨(v : R ⧸ 𝔩), by simpa [hu_def] using congrArg Units.val hv⟩

/-- Hypothesis-free statement: in the same setting, the `p`-th-power
predicate is equivalent to a single equation in `R ⧸ 𝔩` involving the
ring-level power `x ^ ((q - 1) / p)`. This restated form avoids the
`map_pow` rewrite and is convenient for downstream substitution. -/
theorem isPthPowerModPrime_iff_pow_card_div_p_eq_one'
    [𝔩.IsMaximal] [Fintype (R ⧸ 𝔩)] {p : ℕ} (hp_pos : 0 < p)
    (hp : p ∣ Fintype.card (R ⧸ 𝔩) - 1) {x : R} (hx : x ∉ 𝔩) :
    IsPthPowerModPrime p 𝔩 x ↔
      (Ideal.Quotient.mk 𝔩 x) ^ ((Fintype.card (R ⧸ 𝔩) - 1) / p) = 1 := by
  rw [isPthPowerModPrime_iff_pow_card_div_p_eq_one hp_pos hp hx, map_pow]

end IdealCriterion

end BernoulliRegular

end
