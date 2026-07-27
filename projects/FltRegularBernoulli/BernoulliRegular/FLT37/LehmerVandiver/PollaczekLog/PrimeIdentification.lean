/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import FltRegular.NumberTheory.CyclotomicRing
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Frobenius identification of a prime above `ℓ` in `𝓞 (ℚ(ζ_p))`

For an odd prime `p`, a rational prime `ℓ` with `ℓ ≡ 1 (mod p)` (write
`ℓ = k · p + 1`), and a natural number `t` satisfying `gcd(t, ℓ) = 1`
and `t^k ≢ 1 (mod ℓ)`, this file constructs a prime ideal
`𝔩 ⊂ 𝓞 (CyclotomicField p ℚ)` over `ℓ` such that `ζ_p ≡ t^k (mod 𝔩)`.

This is **Washington's Proposition 2.14** (the Kummer–Dedekind theorem)
specialised to `B = ℤ[ζ_p]`, `α = ζ_p`, `f = Φ_p`, `𝒫 = (ℓ)`: the prime
ideal `𝔩` corresponds to the linear factor `X - t^k` of
`Φ_p(X) (mod ℓ)`.

## Strategy via flt-regular's `CyclotomicIntegers`

flt-regular's `FltRegular.NumberTheory.CyclotomicRing` provides
`CyclotomicIntegers p := AdjoinRoot (cyclotomic p ℤ)` together with the
ring isomorphism `equiv : CyclotomicIntegers p ≃+* 𝓞 (CyclotomicField p ℚ)`
(sending `zeta := AdjoinRoot.root _` to `(zeta_spec p ℚ K).toInteger`).

Combined with mathlib's `AdjoinRoot.lift`, the cyclotomic-to-`ZMod ℓ`
ring hom `CyclotomicIntegers p →+* ZMod ℓ` sending `ζ ↦ (t : ZMod ℓ)^k`
is well-defined precisely when `Φ_p((t : ZMod ℓ)^k) = 0` in `ZMod ℓ`.

That cyclotomic equation follows from the geometric-series identity
`(X - 1) · Φ_p(X) = X^p - 1` in `ℤ[X]` (mathlib's
`Polynomial.cyclotomic_prime_mul_X_sub_one`) plus Fermat's little
theorem `t^{ℓ-1} ≡ 1 (mod ℓ)` (mathlib's
`ZMod.pow_card_sub_one_eq_one`): in `ZMod ℓ`, with `x = (t : ZMod ℓ)^k`,
`x^p = t^{k·p} = t^{ℓ-1} = 1`, so `(x - 1) · Φ_p(x) = x^p - 1 = 0`, and
since `x - 1 ≠ 0` (the hypothesis `t^k ≢ 1 (mod ℓ)`), `Φ_p(x) = 0`
because `ZMod ℓ` is an integral domain.

## API

* `cyclotomic_p_eval_eq_zero_of_ne_one` — the cyclotomic equation
  `Φ_p((t : ZMod ℓ)^k) = 0` in `ZMod ℓ`.
* `cyclotomicReduction` — the ring hom `CyclotomicIntegers p →+* ZMod ℓ`
  sending `ζ ↦ (t : ZMod ℓ)^k`.
* `lehmerVandiverPrime` — the prime ideal of `𝓞 (CyclotomicField p ℚ)`
  obtained as the kernel transported via `equiv`.
* `lehmerVandiverPrime_isPrime` — the kernel of a hom to a field is
  prime.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), Proposition 2.14, p. 15.
* flt-regular `FltRegular.NumberTheory.CyclotomicRing`.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section CyclotomicEval

variable {p ℓ k : ℕ} [Fact p.Prime] [Fact ℓ.Prime]

/-- **Helper lemma: the cyclotomic polynomial vanishes at `t^k`.**

For an odd prime `p`, a prime `ℓ` with `ℓ = k · p + 1`, and `t : ℕ` with
`gcd(t, ℓ) = 1` and `t^k ≢ 1 (mod ℓ)`, the cyclotomic polynomial
`Φ_p` evaluated at `(t : ZMod ℓ)^k` (via `eval₂` along
`Int.castRingHom (ZMod ℓ)`) is zero in `ZMod ℓ`.

Proof: in `ZMod ℓ` we have the geometric-series identity
`(X - 1) · Φ_p = X^p - 1` (`cyclotomic_prime_mul_X_sub_one`). Setting
`x = (t : ZMod ℓ)^k`, Fermat's little theorem gives
`x^p = t^{k·p} = t^{ℓ-1} = 1` (since `gcd(t, ℓ) = 1`), so
`(x - 1) · Φ_p(x) = 0`. As `ZMod ℓ` is a field and `x - 1 ≠ 0` by the
hypothesis `t^k ≢ 1 (mod ℓ)`, we conclude `Φ_p(x) = 0`. -/
theorem cyclotomic_p_eval_eq_zero_of_ne_one
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    Polynomial.eval₂ (Int.castRingHom (ZMod ℓ)) ((t : ZMod ℓ) ^ k)
        (Polynomial.cyclotomic p ℤ) = 0 := by
  -- Let `x = (t : ZMod ℓ)^k` for brevity.
  set x : ZMod ℓ := (t : ZMod ℓ) ^ k with hx_def
  -- Convert `eval₂` into `eval` after mapping coefficients to `ZMod ℓ`.
  rw [eval₂_eq_eval_map, map_cyclotomic]
  -- The geometric-series factorisation in `ZMod ℓ[X]`.
  have hfact : (Polynomial.cyclotomic p (ZMod ℓ)) * (X - 1) =
      X ^ p - 1 := cyclotomic_prime_mul_X_sub_one (ZMod ℓ) p
  -- Evaluate the factorisation at `x`.
  have heval : (Polynomial.cyclotomic p (ZMod ℓ)).eval x * (x - 1) =
      x ^ p - 1 := by
    have := congrArg (Polynomial.eval x) hfact
    simpa [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] using this
  -- Compute `x ^ p = 1` via Fermat: `x^p = t^{k·p} = t^{ℓ-1}`.
  have hxp : x ^ p = 1 := by
    rw [hx_def, ← pow_mul, show k * p = ℓ - 1 by omega]
    -- `(t : ZMod ℓ) ^ (ℓ - 1) = 1` by Fermat (gcd(t, ℓ) = 1).
    exact ZMod.pow_card_sub_one_eq_one
      ((ZMod.isUnit_iff_coprime t ℓ).mpr ht_coprime).ne_zero
  -- Hence `(x - 1) * Φ_p(x) = 0`. Since `x - 1 ≠ 0`, `Φ_p(x) = 0`.
  have hx_ne : x - 1 ≠ 0 := sub_ne_zero.mpr ht_ne
  refine (mul_eq_zero.mp ?_).resolve_right hx_ne
  rw [heval, hxp, sub_self]

end CyclotomicEval

section CyclotomicReduction

variable (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime]

/-- **The cyclotomic reduction map** `CyclotomicIntegers p →+* ZMod ℓ`.

Under the hypotheses `ℓ = k · p + 1`, `gcd(t, ℓ) = 1`, and
`t^k ≢ 1 (mod ℓ)`, this ring hom sends `zeta p ↦ (t : ZMod ℓ)^k`. It is
the unique such hom out of `CyclotomicIntegers p = AdjoinRoot Φ_p`,
guaranteed by mathlib's `AdjoinRoot.lift` together with the cyclotomic
vanishing equation `cyclotomic_p_eval_eq_zero_of_ne_one`. -/
noncomputable def cyclotomicReduction
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    CyclotomicIntegers p →+* ZMod ℓ :=
  AdjoinRoot.lift (Int.castRingHom (ZMod ℓ)) ((t : ZMod ℓ) ^ k)
    (cyclotomic_p_eval_eq_zero_of_ne_one hℓ ht_coprime ht_ne)

/-- **Behaviour of `cyclotomicReduction` at `zeta p`.** The defining
property of the lift: `zeta p ↦ (t : ZMod ℓ)^k`. -/
@[simp]
theorem cyclotomicReduction_zeta
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    cyclotomicReduction p ℓ k hℓ ht_coprime ht_ne (CyclotomicIntegers.zeta p) =
      (t : ZMod ℓ) ^ k := by
  simp only [cyclotomicReduction, CyclotomicIntegers.zeta]
  exact AdjoinRoot.lift_root _

end CyclotomicReduction

section LehmerVandiverPrime

variable (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime]

/-- **The Lehmer–Vandiver prime ideal** `𝔩 ⊂ 𝓞 (CyclotomicField p ℚ)`.

Under the hypotheses `ℓ = k · p + 1`, `gcd(t, ℓ) = 1`, and
`t^k ≢ 1 (mod ℓ)`, this is the prime ideal corresponding (via Kummer–
Dedekind / Washington Proposition 2.14) to the linear factor `X - t^k`
of `Φ_p` modulo `ℓ`. Concretely, it is the comap of the kernel of
`cyclotomicReduction` along `CyclotomicIntegers.equiv`. -/
noncomputable def lehmerVandiverPrime
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    Ideal (𝓞 (CyclotomicField p ℚ)) :=
  Ideal.comap (CyclotomicIntegers.equiv p).symm.toRingHom
    (RingHom.ker (cyclotomicReduction p ℓ k hℓ ht_coprime ht_ne))

/-- **`lehmerVandiverPrime` is a prime ideal.** Since the target
`ZMod ℓ` of `cyclotomicReduction` is a field (because `ℓ` is prime), its
kernel is a prime ideal of `CyclotomicIntegers p`; primality is then
preserved under `Ideal.comap` along the inverse ring iso. -/
theorem lehmerVandiverPrime_isPrime
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsPrime := by
  simp only [lehmerVandiverPrime]
  -- The kernel of the cyclotomic reduction (target is the field `ZMod ℓ`,
  -- hence an integral domain) is prime, and primality is preserved under
  -- `Ideal.comap`.
  exact (RingHom.ker_isPrime _).comap _

set_option backward.isDefEq.respectTransparency false in
/-- **Witness equation modulo `lehmerVandiverPrime`.** Inside
`𝓞 (CyclotomicField p ℚ)`, the difference between the chosen primitive
`p`-th root of unity `(zeta_spec p ℚ K).toInteger` and the integer
`(((t : ZMod ℓ) ^ k).val : ℕ)` lies in `lehmerVandiverPrime`, i.e.
`ζ_p ≡ t^k (mod 𝔩)`. -/
theorem lehmerVandiverPrime_zeta_sub_tk_mem
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger -
        ((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∈
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  -- The element is in `lehmerVandiverPrime` iff its image under
  -- `equiv⁻¹` is in `RingHom.ker cyclotomicReduction`, i.e. the
  -- cyclotomic reduction of that image is `0` in `ZMod ℓ`.
  simp only [lehmerVandiverPrime]
  rw [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.mem_ker, map_sub]
  -- Compute each summand.
  have h1 : (CyclotomicIntegers.equiv p).symm
        (zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger =
      CyclotomicIntegers.zeta p := by
    apply (CyclotomicIntegers.equiv p).injective
    rw [RingEquiv.apply_symm_apply, CyclotomicIntegers.equiv_zeta]
  have h2 : (CyclotomicIntegers.equiv p).symm
        ((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ)) =
      ((((t : ZMod ℓ) ^ k).val : ℕ) : CyclotomicIntegers p) := by
    rw [map_natCast]
  rw [h1, h2, map_sub, cyclotomicReduction_zeta, map_natCast,
    ZMod.natCast_val, ZMod.cast_id, sub_self]

/-- **`lehmerVandiverPrime` lies over `(ℓ) ⊂ ℤ`.** The natural number
`ℓ`, viewed in `𝓞 (CyclotomicField p ℚ)`, lies in `lehmerVandiverPrime`.
Equivalently, the prime `𝔩` lies over the rational prime `(ℓ)`. The
proof reduces via `equiv⁻¹` to the trivial fact `(ℓ : ZMod ℓ) = 0`. -/
theorem lehmerVandiverPrime_natCast_ℓ_mem
    (hℓ : ℓ = k * p + 1) {t : ℕ} (ht_coprime : t.Coprime ℓ)
    (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∈
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  simp only [lehmerVandiverPrime]
  rw [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.mem_ker, map_natCast, map_natCast, ZMod.natCast_self]

end LehmerVandiverPrime

end FLT37

end BernoulliRegular

end
