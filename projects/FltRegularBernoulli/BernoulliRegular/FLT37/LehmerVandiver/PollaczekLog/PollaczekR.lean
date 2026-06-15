module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit

/-!
# Auxiliary Pollaczek cyclotomic unit `pollaczekR`

For an odd prime `p` and a non-negative integer `i`, Washington defines
the auxiliary cyclotomic element

  `R_i := ∏_{a=1}^{p-1} (ζ^{a/2} - ζ^{-a/2})^{a^{p-1-i}} ∈ 𝓞 K`

inside `K = ℚ(ζ_p)` where `ζ = ζ_p` is the standard primitive `p`-th
root of unity. Here `a/2` denotes `a · 2⁻¹` viewed in `ZMod p`; this is
well-defined because `2 ∈ ZMod p` is invertible whenever `p` is odd.

`R_i` is related to the Pollaczek unit `E_i = pollaczekUnit p K i`
(developed in `BernoulliRegular/FLT37/LehmerVandiver/PollaczekUnit.lean`)
by Pollaczek's identity (Washington, p. 158, line 5)

  `R_i^{g^i - 1} = E_i · α^p`     for some `α ∈ K^×`

with `g` a primitive root mod `p`. This file only **defines** `R_i` and
gives the basic factorisation API; Pollaczek's identity itself is the
content of the companion ticket **LV004d**.

## Key factorisation

Since `(ζ^{a/2} - ζ^{-a/2}) = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`, the product
`R_i` factors term-wise into a `ζ`-power times the simpler product
`∏_{a=1}^{p-1} (ζ^{2·(a/2)} - 1)^{a^{p-1-i}}`. Together with the
`ZMod p`-identity `2 · (a/2) = a`, the second factor is
`∏_{a=1}^{p-1} (ζ^a - 1)^{a^{p-1-i}}` (after using `ζ^p = 1`).

* `pollaczekRFactor_eq_neg_half_mul_sub` exposes the term-wise unit-zpow
  factorisation `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`.
* `two_mul_pollaczekRExp` is the `ZMod p` identity `2 · (a/2) = a`.
* `zeta_unit_zpow_two_mul_pollaczekRExp_val_eq` lifts this to the
  unit-zpow identity `ζ^{2·(a/2).val} = ζ^a` using `ζ^p = 1`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units), p. 158 (line 1, defining `R_i`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The standard primitive `p`-th root `ζ_p`, packaged as a unit of `𝓞 K`.
This is `(zeta_spec p ℚ K).toInteger` viewed in `(𝓞 K)ˣ`; its value is
`zetaUnitR_coe`. -/
noncomputable def zetaUnitR : (𝓞 K)ˣ :=
  ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit

@[simp]
theorem zetaUnitR_coe : ((zetaUnitR p K : (𝓞 K)ˣ) : 𝓞 K) = (zeta_spec p ℚ K).toInteger :=
  IsUnit.unit_spec _

section PollaczekR

/-- The half-exponent `a/2 := a · 2⁻¹ ∈ ZMod p`. For odd `p`, this is
well-defined because `2 ∈ ZMod p` is invertible. -/
noncomputable def pollaczekRExp (a : ℕ) : ZMod p :=
  (a : ZMod p) * (2 : ZMod p)⁻¹

/-- The factor at index `a` in the auxiliary Pollaczek product:
`ζ^{a/2} - ζ^{-a/2} ∈ 𝓞 K`, viewed via the unit ζ raised to integer
exponents and coerced to `𝓞 K`. The integer exponent is the natural lift
of `(pollaczekRExp p a) : ZMod p` via `ZMod.val`. -/
noncomputable def pollaczekRFactor (a : ℕ) : 𝓞 K :=
  ((zetaUnitR p K ^
      ((pollaczekRExp p a).val : ℤ) : (𝓞 K)ˣ) : 𝓞 K) -
    ((zetaUnitR p K ^
      (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K)

/-- The **auxiliary Pollaczek cyclotomic element**

  `pollaczekR p K i = ∏_{a=1}^{p-1} (ζ^{a/2} - ζ^{-a/2})^{a^{p-1-i}}`

inside `𝓞 K`, where `K = ℚ(ζ_p)` and `a/2 := a · 2⁻¹ (mod p)`. This is
Washington's `R_i` (p. 158, line 1).

The product is over `Finset.Ico 1 p` (i.e. `a ∈ {1, …, p-1}`). For
`p = 1` (vacuous, not a prime) the product is the empty product, hence
`1`. For odd primes `p ≥ 3` this matches Washington's convention. -/
noncomputable def pollaczekR (i : ℕ) : 𝓞 K :=
  ∏ a ∈ Finset.Ico 1 p, pollaczekRFactor p K a ^ (a : ℕ) ^ (p - 1 - i)

end PollaczekR

section PollaczekRAPI

variable (i : ℕ)

/-- **`pollaczekR` at `p = 1` is `1`.** Vacuous case: `Finset.Ico 1 1`
is empty so the product is `1`. The genuinely interesting case is odd
primes `p ≥ 3`; the value at `p = 2` falls under the same definition
but the product `∏_{a ∈ {1}}` is non-trivial there (and `p = 2` is
excluded by the standing assumption that the Pollaczek index `i` is
even and positive). -/
theorem pollaczekR_one (h : p = 1) :
    pollaczekR p K i = 1 := by
  unfold pollaczekR
  subst h
  rw [show Finset.Ico (1 : ℕ) 1 = ∅ from Finset.Ico_self 1, Finset.prod_empty]

/-- **The integer exponent equality** `2 · (a/2) = a` in `ZMod p`,
using that `2` is invertible in `ZMod p` for odd `p`. -/
theorem two_mul_pollaczekRExp (hp_odd : p ≠ 2) (a : ℕ) :
    (2 : ZMod p) * pollaczekRExp p a = (a : ZMod p) := by
  unfold pollaczekRExp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_nat : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h_nat
    exact hp_odd ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp h_nat)
  rw [show (a : ZMod p) * (2 : ZMod p)⁻¹ =
        (2 : ZMod p)⁻¹ * (a : ZMod p) from by ring,
    ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- **Term-wise factorisation of the Pollaczek factor in unit-zpow form.**
Pulling out `ζ^{-a/2}` gives

  `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^{2·(a/2)} - 1)`,

stated using the unit zpow on `zetaUnitR p K`. The companion
lemma `two_mul_pollaczekRExp` rewrites `2 · (a/2) = a` in `ZMod p`, and
periodicity of `ζ` (order dividing `p`) then yields the simpler form
`ζ^{2·(a/2)} = ζ^a`. -/
theorem pollaczekRFactor_eq_neg_half_mul_sub (a : ℕ) :
    pollaczekRFactor p K a =
      ((zetaUnitR p K ^
          (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) *
        (((zetaUnitR p K ^
                (2 * ((pollaczekRExp p a).val : ℤ)) :
              (𝓞 K)ˣ) : 𝓞 K) - 1) := by
  unfold pollaczekRFactor
  set ζ : (𝓞 K)ˣ := zetaUnitR p K
  set m : ℤ := ((pollaczekRExp p a).val : ℤ)
  have hpow : ((ζ ^ (-m) : (𝓞 K)ˣ) : 𝓞 K) *
      ((ζ ^ (2 * m) : (𝓞 K)ˣ) : 𝓞 K) =
      ((ζ ^ m : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    ring
  rw [mul_sub, hpow, mul_one]

/-- The unit ζ has `ζ^p = 1`. -/
theorem zeta_unit_pow_p_eq_one : (zetaUnitR p K ^ (p : ℕ) : (𝓞 K)ˣ) = 1 :=
  (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit hp.1.ne_zero |>.pow_eq_one

/-- **Periodicity step**: `ζ^p = 1` as a unit, so any integer exponent
on `ζ` reduces mod `p`. In particular,
`(ζ_unit)^(2 · (a/2).val) = (ζ_unit)^a` because `2 · (a/2) ≡ a (mod p)`
and `ζ^p = 1`. -/
theorem zeta_unit_zpow_two_mul_pollaczekRExp_val_eq
    (hp_odd : p ≠ 2) (a : ℕ) :
    (zetaUnitR p K ^ (2 * ((pollaczekRExp p a).val : ℤ)) :
        (𝓞 K)ˣ) =
      (zetaUnitR p K ^ (a : ℤ) : (𝓞 K)ˣ) := by
  set ζ : (𝓞 K)ˣ := zetaUnitR p K
  have hζp_int : ζ ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]; exact zeta_unit_pow_p_eq_one p K
  -- 2 · (a/2).val ≡ a (mod p) as integers (lifted from ZMod p).
  have h_zmod : ((2 * ((pollaczekRExp p a).val : ℤ) : ℤ) : ZMod p) =
      ((a : ℤ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact two_mul_pollaczekRExp p hp_odd a
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ (2 * ((pollaczekRExp p a).val : ℤ) - (a : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Int.cast_sub]
    rw [h_zmod]
    ring
  have heq : (2 * ((pollaczekRExp p a).val : ℤ) : ℤ) = (a : ℤ) + (p : ℤ) * k := by
    linarith [hk]
  rw [heq, zpow_add, zpow_mul, hζp_int, one_zpow, mul_one]

/-- **Factorisation of the Pollaczek factor with the cleaned `ζ^a - 1`
form**: combining `pollaczekRFactor_eq_neg_half_mul_sub` with the
periodicity step gives

  `ζ^{a/2} - ζ^{-a/2} = ζ^{-a/2} · (ζ^a - 1)`,

stated entirely inside `𝓞 K`. -/
theorem pollaczekRFactor_eq_neg_half_mul_zeta_pow_sub_one
    (hp_odd : p ≠ 2) (a : ℕ) :
    pollaczekRFactor p K a =
      ((zetaUnitR p K ^
          (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) *
        ((zetaUnitR p K : 𝓞 K) ^ a - 1) := by
  rw [pollaczekRFactor_eq_neg_half_mul_sub p K a,
    zeta_unit_zpow_two_mul_pollaczekRExp_val_eq p K hp_odd a,
    zpow_natCast, Units.val_pow_eq_pow_val]

/-- **The full factorisation of `pollaczekR`.** Splitting the pull-out
factor `ζ^{-a/2}` from each term gives

  `pollaczekR p K i = ζ_pre · ∏_{a=1}^{p-1} (ζ^a - 1)^{a^{p-1-i}}`,

where `ζ_pre := ∏_{a=1}^{p-1} (ζ^{-a/2})^{a^{p-1-i}}` is the unit
prefactor. This is the connection to the cyclotomic-unit infrastructure
of `BernoulliRegular/FLT37/PrimaryUnits.lean`: the second factor's
cyclotomic terms `(ζ^a - 1)` are associates of `(ζ - 1)`. -/
theorem pollaczekR_factorisation (hp_odd : p ≠ 2) :
    pollaczekR p K i =
      (∏ a ∈ Finset.Ico 1 p,
          ((zetaUnitR p K ^
            (-((pollaczekRExp p a).val : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) ^
              (a : ℕ) ^ (p - 1 - i)) *
        ∏ a ∈ Finset.Ico 1 p,
          ((zetaUnitR p K : 𝓞 K) ^ a - 1) ^
            (a : ℕ) ^ (p - 1 - i) := by
  unfold pollaczekR
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [pollaczekRFactor_eq_neg_half_mul_zeta_pow_sub_one p K hp_odd a, mul_pow]

end PollaczekRAPI

section PairUp

variable (i : ℕ)

/-- **Half-exponent symmetry:** `pollaczekRExp p (p - a) = -pollaczekRExp p a`
in `ZMod p`. Consequence of `((p - a : ℕ) : ZMod p) = -(a : ZMod p)` for
`a ≤ p`, since `(p : ZMod p) = 0`. -/
theorem pollaczekRExp_p_sub {a : ℕ} (ha : a ≤ p) :
    pollaczekRExp p (p - a) = -pollaczekRExp p a := by
  unfold pollaczekRExp
  have h_sub : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]
  rw [h_sub, neg_mul]

/-- **Pair-up sign:** `pollaczekRFactor p K (p - a) = -pollaczekRFactor p K a`
for `a ≤ p`. The proof uses `pollaczekRExp p (p - a) = -pollaczekRExp p a`,
the integer-cast identity `(-x).val ≡ -x.val (mod p)`, and `ζ^p = 1` to
swap the two ζ-exponents. -/
theorem pollaczekRFactor_p_sub_eq_neg {a : ℕ} (ha : a ≤ p) :
    pollaczekRFactor p K (p - a) = -pollaczekRFactor p K a := by
  unfold pollaczekRFactor
  set ζ : (𝓞 K)ˣ := zetaUnitR p K
  have hζp : ζ ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]; exact zeta_unit_pow_p_eq_one p K
  -- m' ≡ -m (mod p), as integers, where m = (a/2).val and m' = ((p-a)/2).val.
  have h_zmod : (((pollaczekRExp p (p - a)).val : ℤ) : ZMod p)
      = ((-((pollaczekRExp p a).val : ℤ) : ℤ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
    exact pollaczekRExp_p_sub p ha
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ ((pollaczekRExp p (p - a)).val : ℤ)
        - (-((pollaczekRExp p a).val : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h_zmod, sub_self]
  set m : ℤ := ((pollaczekRExp p a).val : ℤ)
  set m' : ℤ := ((pollaczekRExp p (p - a)).val : ℤ)
  have heq : m' = -m + (p : ℤ) * k := by linarith
  have h1 : (ζ ^ m' : (𝓞 K)ˣ) = (ζ ^ (-m) : (𝓞 K)ˣ) := by
    rw [heq, zpow_add, zpow_mul, hζp, one_zpow, mul_one]
  have h2 : (ζ ^ (-m') : (𝓞 K)ˣ) = (ζ ^ m : (𝓞 K)ˣ) := by
    rw [show (-m' : ℤ) = m + (p : ℤ) * (-k) from by linarith, zpow_add, zpow_mul,
      hζp, one_zpow, mul_one]
  rw [h1, h2, neg_sub]

/-- **Modular identity for the natural-number exponent.** For an odd
prime `p`, `a ≤ p`, and even exponent `E`, the difference
`(p - a) ^ E - a ^ E` is divisible by `p` (as an integer).

Proof: `(p - a)^E ≡ (-a)^E = a^E (mod p)` in `ZMod p`, using `E` even
so `(-1)^E = 1`. Lift to `ℤ` via `ZMod.intCast_zmod_eq_zero_iff_dvd`. -/
theorem pollaczekR_pair_exp_dvd {a E : ℕ} (ha : a ≤ p) (hE : Even E) :
    (p : ℤ) ∣ ((p - a : ℕ) : ℤ) ^ E - (a : ℤ) ^ E := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]
  rw [show ((-(a : ZMod p))^E - (a : ZMod p)^E : ZMod p)
        = ((-1)^E - 1) * (a : ZMod p)^E from by ring]
  rw [hE.neg_one_pow, sub_self, zero_mul]

/-- **Concrete witness for the modular identity** as a natural-number
inequality: when `a ≤ (p - 1) / 2`, `(p - a) ≥ a`, so
`(p - a) ^ E ≥ a ^ E`, and the difference is `p · m` for `m : ℕ`. -/
theorem pollaczekR_pair_exp_eq {a E : ℕ} (hp_pos : 0 < p)
    (ha_le : a ≤ (p - 1) / 2) (hE : Even E) :
    ∃ m : ℕ, (p - a) ^ E = a ^ E + p * m := by
  have ha_le_p : a ≤ p := ha_le.trans (Nat.div_le_self _ _ |>.trans (Nat.sub_le _ _))
  -- (p - a) ≥ a since a ≤ (p-1)/2 < p/2 ≤ p - a.
  have h_ge : a ≤ p - a := by omega
  have h_ge_pow : a ^ E ≤ (p - a) ^ E := Nat.pow_le_pow_left h_ge E
  -- Use the integer divisibility result.
  have h_dvd := pollaczekR_pair_exp_dvd p ha_le_p hE
  have h_pos_diff : (0 : ℤ) ≤ ((p - a : ℕ) : ℤ) ^ E - (a : ℤ) ^ E := by
    have : (a : ℤ) ^ E ≤ ((p - a : ℕ) : ℤ) ^ E := by exact_mod_cast h_ge_pow
    linarith
  obtain ⟨m, hm⟩ := h_dvd
  -- m ≥ 0 because the difference is non-negative and p > 0.
  have hm_nn : 0 ≤ m := by
    rcases (mul_nonneg_iff_of_pos_left (by exact_mod_cast hp_pos)).mp (hm ▸ h_pos_diff) with h
    exact h
  refine ⟨m.toNat, ?_⟩
  have hm_eq : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_nn
  zify
  rw [hm_eq]
  linarith [hm]

/-- **Pair-product factorisation**: combining the `a` and `p - a` factors of
`pollaczekR`. Using the sign swap `pollaczekRFactor p K (p - a) =
-pollaczekRFactor p K a`, the product
`F_a ^ a^E · F_{p-a} ^ (p - a)^E` collapses to a sign times a single
power of `F_a`. -/
theorem pollaczekRFactor_pair_pow_mul {a : ℕ} (ha : a ≤ p) (E : ℕ) :
    pollaczekRFactor p K a ^ a ^ E *
        pollaczekRFactor p K (p - a) ^ (p - a) ^ E =
      (-1) ^ (p - a) ^ E *
        pollaczekRFactor p K a ^ (a ^ E + (p - a) ^ E) := by
  rw [pollaczekRFactor_p_sub_eq_neg p K ha, neg_pow]
  ring

/-- **Pair-product factorisation with modular witness.** Combining the
pair-up sign swap with the modular identity `(p - a)^E = a^E + p · m`
(for `a ≤ (p-1)/2` and `E` even) gives a clean separation of the pair
contribution into

  `F_a ^ a^E · F_{p-a} ^ (p - a)^E = (-1)^{(p-a)^E} · F_a^{2·a^E} · F_a^{p·m}`,

where the last factor is a `p`-th power and disappears modulo `p`-th
powers in subsequent steps of the LV004e argument. -/
theorem pollaczekRFactor_pair_pow_split {a E : ℕ} (hp_pos : 0 < p)
    (ha_le : a ≤ (p - 1) / 2) (hE : Even E) :
    ∃ m : ℕ,
      pollaczekRFactor p K a ^ a ^ E *
          pollaczekRFactor p K (p - a) ^ (p - a) ^ E =
        (-1) ^ (p - a) ^ E *
          (pollaczekRFactor p K a ^ (2 * a ^ E) *
            pollaczekRFactor p K a ^ (p * m)) := by
  have ha_le_p : a ≤ p := ha_le.trans (Nat.div_le_self _ _ |>.trans (Nat.sub_le _ _))
  obtain ⟨m, hm⟩ := pollaczekR_pair_exp_eq p hp_pos ha_le hE
  refine ⟨m, ?_⟩
  rw [pollaczekRFactor_pair_pow_mul p K ha_le_p E, hm, ← pow_add]
  congr 2; ring

/-- **Squared-factor identity**: `(ζ^{a/2} - ζ^{-a/2})^2 = ζ^{-a} · (ζ^a - 1)^2`
inside `𝓞 K`. This is the polynomial identity that bridges the
`pollaczekRFactor` (with half-exponents) to the cyclotomic-unit form
`(ζ^a - 1)`. Proof: square the factorisation
`pollaczekRFactor p K a = ζ^{-(a/2).val} · (ζ^a - 1)` and use
`(ζ^{-(a/2).val})^2 = ζ^{-2·(a/2).val} = ζ^{-a}` (the latter by
periodicity, since `2 · (a/2) ≡ a (mod p)`). -/
theorem pollaczekRFactor_sq (hp_odd : p ≠ 2) (a : ℕ) :
    (pollaczekRFactor p K a) ^ 2 =
      ((zetaUnitR p K ^ (-(a : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) *
        ((zetaUnitR p K : 𝓞 K) ^ a - 1) ^ 2 := by
  rw [pollaczekRFactor_eq_neg_half_mul_zeta_pow_sub_one p K hp_odd a, mul_pow]
  congr 1
  set ζ : (𝓞 K)ˣ := zetaUnitR p K
  set m : ℤ := ((pollaczekRExp p a).val : ℤ)
  have h : (ζ ^ (-m) : (𝓞 K)ˣ) ^ 2 = ζ ^ (-(a : ℤ)) := by
    rw [← zpow_natCast (G := (𝓞 K)ˣ), ← zpow_mul]
    change ζ ^ (-m * (2 : ℕ)) = ζ ^ (-(a : ℤ))
    have h_eq := zeta_unit_zpow_two_mul_pollaczekRExp_val_eq p K hp_odd a
    rw [show (-m * (2 : ℕ) : ℤ) = -(2 * m) from by push_cast; ring, zpow_neg, h_eq,
      ← zpow_neg]
  rw [← Units.val_pow_eq_pow_val, h]

/-- **Split-and-reindex form of `pollaczekR`.** The full product `R_i` over
`Finset.Ico 1 p` decomposes into a lower-half product `a ∈ {1, …, (p-1)/2}`
times an upper-half product `a ∈ {(p-1)/2+1, …, p-1}`; reindexing the upper
half via the involution `a ↔ p - a` gives a paired form over the same
lower-half index set. This is the structural step preceding the pair-up
factorisation. -/
theorem pollaczekR_split_reindex (hp_odd : p ≠ 2) (i : ℕ) :
    pollaczekR p K i =
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        pollaczekRFactor p K a ^ a ^ (p - 1 - i)) *
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        pollaczekRFactor p K (p - a) ^ (p - a) ^ (p - 1 - i)) := by
  have hp_ge3 : 3 ≤ p := by have := hp.out.one_lt; omega
  obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp_odd
  have hk_pos : 1 ≤ k := by omega
  have hp_div2 : (p - 1) / 2 = k := by omega
  unfold pollaczekR
  simp only [hp_div2]
  clear hp_div2
  rw [show Finset.Ico (1 : ℕ) p = Finset.Ico 1 (k + 1) ∪ Finset.Ico (k + 1) p from
      (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm,
    Finset.prod_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
  congr 1
  refine Finset.prod_nbij' (fun a => p - a) (fun a => p - a) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; constructor <;> omega
  · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; constructor <;> omega
  · intro a ha; simp only [Finset.mem_Ico] at ha
    omega
  · intro a ha; simp only [Finset.mem_Ico] at ha
    omega
  · intro a ha; simp only [Finset.mem_Ico] at ha
    have heq : p - (p - a) = a := by omega
    rw [heq]

/-- **Half-range factorisation of `pollaczekR` (LV004e main statement).**
For an odd prime `p` and an index `i` with `Even (p - 1 - i)` (which is
automatic for odd `p` and `Even i` — the standard Pollaczek setup), the
Pollaczek auxiliary `R_i` decomposes as

  `R_i = (sign factor) · (half-range main product) · γ^p`

where:
* the **sign factor** is `∏_{a=1}^{(p-1)/2} (-1)^{(p-a)^{p-1-i}}`,
* the **main product** is `∏_{a=1}^{(p-1)/2} F_a^{2·a^{p-1-i}}` over the
  `pollaczekRFactor`s `F_a := pollaczekRFactor p K a`,
* the explicit **`p`-th-power witness** is
  `γ := ∏_{a=1}^{(p-1)/2} F_a^{((p-a)^{p-1-i} - a^{p-1-i}) / p}`.

This is the equality form of the LV004e half-range factorisation. The
extra `2` in the exponent and the explicit `(ζ^a - 1)`-form conversion
(via `pollaczekRFactor_sq`) are deferred to subsequent assembly. -/
theorem pollaczekR_half_range_factorisation (hp_odd : p ≠ 2) (i : ℕ)
    (hE_even : Even (p - 1 - i)) :
    pollaczekR p K i =
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1), (-1 : 𝓞 K) ^ (p - a) ^ (p - 1 - i)) *
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        pollaczekRFactor p K a ^ (2 * a ^ (p - 1 - i))) *
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        pollaczekRFactor p K a ^
          (((p - a) ^ (p - 1 - i) - a ^ (p - 1 - i)) / p)) ^ p := by
  set E := p - 1 - i
  have hp_pos : 0 < p := hp.out.pos
  rw [pollaczekR_split_reindex p K hp_odd i, ← Finset.prod_mul_distrib]
  have h_pair : ∀ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      pollaczekRFactor p K a ^ a ^ E *
        pollaczekRFactor p K (p - a) ^ (p - a) ^ E =
      (-1 : 𝓞 K) ^ (p - a) ^ E *
        pollaczekRFactor p K a ^ (a ^ E + (p - a) ^ E) := by
    intro a ha
    simp only [Finset.mem_Ico] at ha
    exact pollaczekRFactor_pair_pow_mul p K (by omega) E
  rw [Finset.prod_congr rfl h_pair, Finset.prod_mul_distrib, mul_assoc]
  congr 1
  have h_exp : ∀ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      pollaczekRFactor p K a ^ (a ^ E + (p - a) ^ E) =
      pollaczekRFactor p K a ^ (2 * a ^ E) *
        (pollaczekRFactor p K a ^
          (((p - a) ^ E - a ^ E) / p)) ^ p := by
    intro a ha
    simp only [Finset.mem_Ico] at ha
    have ha_le : a ≤ (p - 1) / 2 := by omega
    obtain ⟨m, hm⟩ := pollaczekR_pair_exp_eq p hp_pos ha_le hE_even
    have hwitness : (p - a) ^ E = a ^ E + p * (((p - a) ^ E - a ^ E) / p) := by
      have hsub : (p - a) ^ E - a ^ E = p * m := by omega
      rw [hsub, Nat.mul_div_cancel_left _ hp_pos]
      exact hm
    rw [show a ^ E + (p - a) ^ E =
          2 * a ^ E + p * (((p - a) ^ E - a ^ E) / p) from by omega,
      pow_add, pow_mul (pollaczekRFactor p K a) p,
      pow_right_comm (pollaczekRFactor p K a) p _]
  rw [Finset.prod_congr rfl h_exp, Finset.prod_mul_distrib, ← Finset.prod_pow]

/-- **Cyclotomic-unit form of the half-range main product.** Using
`pollaczekRFactor_sq` term-wise, the half-range main product
`∏_a F_a^{2·a^E}` (with E = p - 1 - i) splits as the product of a
ζ-prefactor and the cyclotomic-unit form `∏_a (ζ^a - 1)^{2·a^E}`:

  ∏_a F_a^{2·a^E} = (∏_a (ζ^{-a})^{a^E}) · (∏_a (ζ^a - 1)^{2·a^E}).

The first product is the ζ-prefactor (a unit, generated by the chosen
primitive `p`-th root of unity); the second matches the half-range
form expected by Washington Cor 8.19 (up to absorbing the exponent
`2·a^E` modulo `p`-th powers in subsequent steps). -/
theorem pollaczekR_half_range_main_zeta_form (hp_odd : p ≠ 2) (i : ℕ) :
    (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        pollaczekRFactor p K a ^ (2 * a ^ (p - 1 - i))) =
      (∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((zetaUnitR p K ^ (-(a : ℤ)) : (𝓞 K)ˣ) : 𝓞 K) ^
          a ^ (p - 1 - i)) *
      ∏ a ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((zetaUnitR p K : 𝓞 K) ^ a - 1) ^ (2 * a ^ (p - 1 - i)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro a _
  rw [pow_mul, pollaczekRFactor_sq p K hp_odd a, mul_pow, ← pow_mul]

end PairUp

end FLT37

end BernoulliRegular

end
