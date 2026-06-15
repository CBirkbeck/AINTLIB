module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekLog
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.RPollaczekUnitBridge
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.FLT37NumericalFacts

/-!
# FLT37 closure: `¬IsPthPower pollaczekUnit` (LV004g-7)

This file ships the FLT37-specific closure of the LV004g chain: combining
the LV004g-1 bridge `∏_b (ζ^b - 1)^{2 b^E} = (ζ - 1)^{2S} · pollaczekUnit²`
in `𝓞 K`, the LV004g cyclic criterion, and the LV004g-6 numerical facts
(`(1 - 2^4)^{4·432345} = 1` and `lehmerVandiverProduct ≠ 1` in `ZMod 149`),
to deduce `¬IsPthPowerModPrime pollaczekUnit` for the FLT37 certificate
tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`.

## Closure path

1. LV004g-1 bridge (in `𝓞 K`):
   `∏_b (ζ^b - 1)^{2 b^E} = (ζ - 1)^{2S} · pollaczekUnit²`.

2. Square (still in `𝓞 K`):
   `∏_b (ζ^b - 1)^{4 b^E} = (ζ - 1)^{4S} · pollaczekUnit⁴`.

3. Apply `Q = Ideal.Quotient.mk lehmerVandiverPrime` and use the
   residue substitution `ζ ≡ ((t^k).val) (mod 𝔩)` (LV004c) term-wise.

4. Transport via `lehmerVandiverPrime_quotientEquiv : 𝓞 K / 𝔩 ≃+* ZMod ℓ`.
   In `ZMod 149` we get
     `(t^k - 1)^{4S} · Φ(Q(pollaczekUnit⁴)) =
       ∏ (t^{kb} - 1)^{4 b^E} = lehmerVandiverProduct`.

5. FLT37-specific Fermat reduction (LV004g-6):
   `(t^k - 1)^{4S} = 1` in `ZMod 149`, since `4S = 4·432345 = 148·11685`
   and `(1 - 16)^{148} = 1` by Fermat (the sign is squared away).

6. So `Φ(Q(pollaczekUnit⁴)) = lehmerVandiverProduct = 107 ≠ 1` in `ZMod 149`.

7. By the cyclic criterion `IsPthPower pollaczekUnit ↔
   Q(pollaczekUnit^k) = 1` (LV004g main theorem), `¬IsPthPower pollaczekUnit`.

## Main result

* `not_isPthPowerModPrime_pollaczekUnit_thirtyseven`:
  `¬IsPthPowerModPrime 37 (lehmerVandiverPrime 37 149 4 …)
    (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 : 𝓞 _)`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer GTM 83),
  §8.3 (Pollaczek units), Theorem 9.5 (p. 176).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

section FLT37Closure

set_option backward.isDefEq.respectTransparency false in
/-- **`pollaczekUnit ∉ lehmerVandiverPrime`** (auxiliary). Since
`pollaczekUnit p K i : (𝓞 K)ˣ` is a unit in `𝓞 K`, its underlying element
is not in any proper ideal — in particular, not in `lehmerVandiverPrime`. -/
theorem pollaczekUnit_notMem_lehmerVandiverPrime
    (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ) :
    ((pollaczekUnit p (CyclotomicField p ℚ) i : (𝓞 (CyclotomicField p ℚ))ˣ) :
        𝓞 (CyclotomicField p ℚ)) ∉
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  intro hmem
  -- A unit in a ring cannot lie in a proper ideal.
  have hunit : IsUnit ((pollaczekUnit p (CyclotomicField p ℚ) i :
      (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) :=
    ⟨pollaczekUnit p (CyclotomicField p ℚ) i, rfl⟩
  -- Thus the ideal must be the unit ideal.
  have htop := (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).eq_top_of_isUnit_mem
    hmem hunit
  -- But `lehmerVandiverPrime` is a prime ideal (nontrivial).
  have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
  exact hprime.ne_top htop

end FLT37Closure

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000

/-- **Squared LV004g-1 bridge: `∏_b (ζ^b - 1)^{4 b^E} = (ζ-1)^{4S} ·
pollaczekUnit⁴`** in `𝓞 K`. Direct square of
`zeta_pow_sub_one_prod_eq_pollaczekUnit_sq_mul_zeta_sub_one_pow`. -/
theorem zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hp_odd : p ≠ 2) (i : ℕ) :
    (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) =
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      ((pollaczekUnit p K i : 𝓞 K) ^ 4) := by
  -- Square the LV004g-1 bridge: (∏ x^{2 e})² = ∏ x^{4 e} = ((ζ-1)^{2S})² · (E²)²
  have h := zeta_pow_sub_one_prod_eq_pollaczekUnit_sq_mul_zeta_sub_one_pow
    p K hp_odd i
  -- Square both sides.
  have hsq : _ ^ 2 = _ ^ 2 := congrArg (· ^ 2) h
  -- LHS²: ∏ x^{2e})² = ∏ x^{4e}
  rw [show ((∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (2 * b ^ (p - 1 - i))) ^ 2 =
        ∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) from ?_]
    at hsq
  -- RHS²: ((ζ-1)^{2S} · E²)² = (ζ-1)^{4S} · E⁴
  · rw [show ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
        (2 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) *
        ((pollaczekUnit p K i : 𝓞 K) ^ 2)) ^ 2 =
        ((((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
        ((pollaczekUnit p K i : 𝓞 K) ^ 4) from ?_] at hsq
    · exact hsq
    · rw [mul_pow, ← pow_mul, ← pow_mul]
      ring_nf
  · rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [← pow_mul]
    ring_nf

set_option backward.isDefEq.respectTransparency false in
/-- **Quotient form of the squared LV004g-1 bridge.** Apply
`Ideal.Quotient.mk lehmerVandiverPrime` to
`zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow`,
yielding the identity in `𝓞 K / 𝔩`:

  Q(∏_b (ζ^b - 1)^{4 b^E}) = Q((ζ-1)^{4S}) · Q(pollaczekUnit^4).

The hypothesis structure mirrors the cyclic-criterion machinery in
`PollaczekLog.lean` so the hypothesis flow chains cleanly downstream. -/
theorem lehmerVandiverPrime_quotient_squared_bridge
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          (((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
              𝓞 (CyclotomicField p ℚ)) ^ b - 1) ^
            (4 * b ^ (p - 1 - i))) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger :
            𝓞 (CyclotomicField p ℚ)) - 1) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ^ 4) := by
  rw [← map_mul]
  exact congrArg (Ideal.Quotient.mk
    (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne))
    (zeta_pow_sub_one_prod_eq_pollaczekUnit_pow_four_mul_zeta_sub_one_pow
      p (CyclotomicField p ℚ) hp_odd i)

set_option backward.isDefEq.respectTransparency false in
/-- **Generalised half-range residue substitution.** For any natural-number
exponent function `f : ℕ → ℕ`, the residue substitution `ζ ≡ ((t^k).val)
(mod 𝔩)` extends to half-range products of `(ζ^a - 1)^{f a}`. -/
theorem lehmerVandiverPrime_quotient_half_range_eq_of_exp
    (p : ℕ) [Fact p.Prime]
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (f : ℕ → ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Ico 1 ((p - 1) / 2 + 1),
          ((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger ^ a - 1) ^ f a) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ a ∈ Ico 1 ((p - 1) / 2 + 1),
          ((((t : ZMod ℓ) ^ k).val : ℕ) ^ a - 1 :
            𝓞 (CyclotomicField p ℚ)) ^ f a) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl ?_
  intro a _
  rw [map_pow, map_pow]
  congr 1
  exact lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
    (p := p) ℓ k hℓ ht_coprime ht_ne a

set_option backward.isDefEq.respectTransparency false in
/-- **Residue substitution at `(ζ - 1)`.** For any natural exponent `n`,
`Q((ζ - 1)^n) = Q((((t^k).val) - 1)^n)` in `𝓞 K / 𝔩`. -/
theorem lehmerVandiverPrime_quotient_zeta_sub_one_pow_eq
    (p : ℕ) [Fact p.Prime]
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (n : ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (((zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger - 1) ^ n) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (((((t : ZMod ℓ) ^ k).val : ℕ) - 1 : 𝓞 (CyclotomicField p ℚ)) ^ n) := by
  rw [map_pow, map_pow]
  congr 1
  -- Use the a=1 case of `lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq`.
  have h := lehmerVandiverPrime_quotient_zeta_pow_sub_one_eq
    (p := p) ℓ k hℓ ht_coprime ht_ne 1
  simpa using h

set_option backward.isDefEq.respectTransparency false in
/-- **Residue-substituted squared bridge.** Combines
`lehmerVandiverPrime_quotient_squared_bridge` (squared LV004g-1 in
quotient form) with the residue substitution lemmas to express both sides
in `((t^k).val)`-form:

  Q(∏_b (((t^k).val)^b - 1)^{4 b^E}) =
    Q((((t^k).val) - 1)^{4S}) · Q(pollaczekUnit^4)

in `𝓞 K / 𝔩`. -/
theorem lehmerVandiverPrime_quotient_squared_bridge_substituted
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ) :
    Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
          ((((t : ZMod ℓ) ^ k).val : ℕ) ^ b - 1 :
            𝓞 (CyclotomicField p ℚ)) ^ (4 * b ^ (p - 1 - i))) =
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (((((t : ZMod ℓ) ^ k).val : ℕ) - 1 : 𝓞 (CyclotomicField p ℚ)) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((pollaczekUnit p (CyclotomicField p ℚ) i :
          𝓞 (CyclotomicField p ℚ)) ^ 4) := by
  have h_bridge := lehmerVandiverPrime_quotient_squared_bridge
    p hp_odd ℓ k hℓ ht_coprime ht_ne i
  -- Convert ζ-form on LHS to (t^k).val-form via half-range substitution.
  have h_lhs := lehmerVandiverPrime_quotient_half_range_eq_of_exp
    p ℓ k hℓ ht_coprime ht_ne (fun b => 4 * b ^ (p - 1 - i))
  -- Convert (ζ - 1) prefactor to (t^k).val - 1 form.
  have h_pre := lehmerVandiverPrime_quotient_zeta_sub_one_pow_eq
    p ℓ k hℓ ht_coprime ht_ne
    (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))
  rw [← h_lhs, ← h_pre]
  exact h_bridge

set_option backward.isDefEq.respectTransparency false in
/-- **Helper: `Φ((((t^k).val : ℕ) : 𝓞 K / 𝔩)) = (t : ZMod ℓ)^k`.** Direct
computation via `RingEquiv.map_natCast` and `ZMod.natCast_val`. -/
theorem lehmerVandiverPrime_quotientEquiv_apply_natCast_tk
    (p : ℕ) [Fact p.Prime]
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    (lehmerVandiverPrime_quotientEquiv (p := p) ℓ k hℓ ht_coprime ht_ne
        ((((((t : ZMod ℓ) ^ k).val : ℕ)) :
          𝓞 (CyclotomicField p ℚ) ⧸ lehmerVandiverPrime p ℓ k hℓ
            ht_coprime ht_ne))) =
      (t : ZMod ℓ) ^ k := by
  haveI : NeZero ℓ := ⟨(Fact.out (p := ℓ.Prime)).ne_zero⟩
  exact ((map_natCast (lehmerVandiverPrime_quotientEquiv (p := p) ℓ k hℓ
    ht_coprime ht_ne) _).trans (ZMod.natCast_val _)).trans (ZMod.cast_id _ _)

set_option backward.isDefEq.respectTransparency false in
/-- **Combined helper: `Φ(Q((((t^k).val : ℕ) : 𝓞 K))) = (t : ZMod ℓ)^k`.**
The composition `Φ ∘ Q : 𝓞 K → ZMod ℓ` evaluated on the natural cast
`(((t^k).val : ℕ) : 𝓞 K)` simplifies to `(t : ZMod ℓ)^k`. Bridges the
syntactic gap between `Q((n : 𝓞 K))` and `((n : 𝓞 K / 𝔩))` for use in
the iso-transport step. -/
theorem lehmerVandiverPrime_quotientEquiv_quotient_apply_natCast_tk
    (p : ℕ) [Fact p.Prime]
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) :
    (lehmerVandiverPrime_quotientEquiv (p := p) ℓ k hℓ ht_coprime ht_ne
        (Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
          (((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ))))) =
      (t : ZMod ℓ) ^ k := by
  haveI : NeZero ℓ := ⟨(Fact.out (p := ℓ.Prime)).ne_zero⟩
  rw [show (Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
      (((((t : ZMod ℓ) ^ k).val : ℕ) : 𝓞 (CyclotomicField p ℚ))) =
      (((((t : ZMod ℓ) ^ k).val : ℕ)) :
        𝓞 (CyclotomicField p ℚ) ⧸ lehmerVandiverPrime p ℓ k hℓ
          ht_coprime ht_ne)) from
    map_natCast (Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ
      ht_coprime ht_ne)) _]
  exact lehmerVandiverPrime_quotientEquiv_apply_natCast_tk p ℓ k hℓ
    ht_coprime ht_ne

set_option backward.isDefEq.respectTransparency false in
/-- **ZMod ℓ form of the squared bridge.** Apply
`lehmerVandiverPrime_quotientEquiv` to
`lehmerVandiverPrime_quotient_squared_bridge_substituted`, transporting
the residue identity from `𝓞 K / 𝔩` to `ZMod ℓ`:

  ∏_b ((t^k)^b - 1)^{4 b^E} =
    (t^k - 1)^{4S} · Φ(Q(pollaczekUnit))^4   in ZMod ℓ. -/
theorem lehmerVandiverPrime_squared_bridge_zmod
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (ℓ k : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ) :
    (∏ b ∈ Ico 1 ((p - 1) / 2 + 1),
        (((t : ZMod ℓ) ^ k) ^ b - 1) ^ (4 * b ^ (p - 1 - i))) =
      ((t : ZMod ℓ) ^ k - 1) ^
          (4 * ∑ b ∈ Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) *
      (lehmerVandiverPrime_quotientEquiv (p := p) ℓ k hℓ ht_coprime ht_ne
        (Ideal.Quotient.mk (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
          ((pollaczekUnit p (CyclotomicField p ℚ) i :
            𝓞 (CyclotomicField p ℚ))))) ^ 4 := by
  have h := lehmerVandiverPrime_quotient_squared_bridge_substituted
    p hp_odd ℓ k hℓ ht_coprime ht_ne i
  have hΦ_tk := lehmerVandiverPrime_quotientEquiv_quotient_apply_natCast_tk
    p ℓ k hℓ ht_coprime ht_ne
  have h_eq := congrArg (lehmerVandiverPrime_quotientEquiv (p := p)
    ℓ k hℓ ht_coprime ht_ne) h
  simp only [map_mul, map_prod, map_pow, map_sub, map_one, hΦ_tk] at h_eq
  exact h_eq

section FLT37Closure

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000

/-- **Fermat exponent reduction for `ZMod p`.** For `x : ZMod p` with
`x ≠ 0` and `m : ℕ`, `x^m = x^(m % (p - 1))`. Standard Fermat trick. -/
private theorem ZMod.pow_eq_pow_mod_card_sub_one
    {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) (m : ℕ) :
    x ^ m = x ^ (m % (p - 1)) := by
  conv_lhs => rw [← Nat.mod_add_div m (p - 1)]
  rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

/-- **FLT37 squared-bridge product equals `lehmerVandiverProduct`.**
For the FLT37 certificate tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`,
the LHS of `lehmerVandiverPrime_squared_bridge_zmod` equals
`lehmerVandiverProduct 37 32 149 2 4` in `ZMod 149`. The proof rewrites
each factor's outer exponent via Fermat (`x^m = x^(m % 148)` for `x ≠ 0`)
and uses `pow_mul` for the base, leaving a per-term equality that
`decide` finishes for each `b ∈ {1, …, 18}`. -/
theorem flt37_squared_bridge_lhs_eq_lehmerVandiverProduct :
    (∏ b ∈ Ico 1 ((37 - 1) / 2 + 1),
        (((2 : ZMod 149) ^ 4) ^ b - 1) ^ (4 * b ^ (37 - 1 - 32))) =
      lehmerVandiverProduct 37 32 149 2 4 := by
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  unfold lehmerVandiverProduct
  refine Finset.prod_congr rfl fun b hb => ?_
  obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
  -- LHS factor: ((2^4)^b - 1)^(4*b^4)
  -- RHS factor: ((2^((4*b) % 148)) - 1)^((4*b^4) % 148)
  -- Step 1: bases match: (2^4)^b = 2^(4*b) and (4*b) % 148 = 4*b for b < 37.
  rw [show (((2 : ZMod 149) ^ 4) ^ b) = (2 : ZMod 149) ^ (4 * b) by rw [pow_mul],
      show ((4 * b) % (149 - 1)) = 4 * b from
        Nat.mod_eq_of_lt (by omega : 4 * b < 149 - 1)]
  -- Step 2: exponents differ by Fermat reduction (mod 148). The base is
  -- nonzero for b ∈ {1, …, 18} because the order of `(2 : ZMod 149)^4 = 16`
  -- is `37`, which does not divide any such `b`.
  have h_base_ne : ∀ b' ∈ Finset.Ico 1 19,
      ((2 : ZMod 149) ^ (4 * b') - 1) ≠ 0 := by decide +revert
  have hb_old : b ∈ Finset.Ico 1 19 := Finset.mem_Ico.mpr ⟨hb1, hb2⟩
  exact ZMod.pow_eq_pow_mod_card_sub_one (h_base_ne b hb_old) _

end FLT37Closure

set_option backward.isDefEq.respectTransparency false in
/-- **FLT37 closure: `Φ(Q(pollaczekUnit 37 K 32))^4 = 107` in `ZMod 149`.**
Combines:
- `lehmerVandiverPrime_squared_bridge_zmod` (general iso-transported squared
  bridge),
- `flt37_squared_bridge_lhs_eq_lehmerVandiverProduct` (numerical
  identification of LHS with `lehmerVandiverProduct`),
- LV004g-6's `one_sub_two_pow_four_pow_kS_eq_one` (the `(t^k - 1)^{4S}`
  prefactor is `1`, since `(1 - 2^4)^{4·432345} = 1` in `ZMod 149` and
  `(-1)^{4·432345} = 1`).

The result drops the prefactor and equates `Φ(Q(pollaczekUnit))^4` with
`lehmerVandiverProduct 37 32 149 2 4`. -/
theorem flt37_pollaczekUnit_residue_pow_four_eq_lehmerVandiverProduct
    [Fact (Nat.Prime 37)] [Fact (Nat.Prime 149)]
    (k : ℕ) (hℓ : 149 = k * 37 + 1) {t : ℕ}
    (ht_coprime : t.Coprime 149) (ht_ne : (t : ZMod 149) ^ k ≠ 1)
    (hkt : k = 4) (htval : t = 2) :
    (lehmerVandiverPrime_quotientEquiv (p := 37) 149 k hℓ ht_coprime ht_ne
      (Ideal.Quotient.mk
        (lehmerVandiverPrime 37 149 k hℓ ht_coprime ht_ne)
        ((pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
          𝓞 (CyclotomicField 37 ℚ))))) ^ 4 =
      lehmerVandiverProduct 37 32 149 2 4 := by
  subst hkt htval
  have h_bridge := lehmerVandiverPrime_squared_bridge_zmod 37 (by decide)
    149 4 hℓ ht_coprime ht_ne 32
  have h_lhs := flt37_squared_bridge_lhs_eq_lehmerVandiverProduct
  have h_pre : ((2 : ZMod 149) ^ 4 - 1) ^
      (4 * ∑ b ∈ Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) = 1 := by
    have hsum : ∑ b ∈ Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32) = 432345 := by decide
    rw [hsum]
    -- Goal: ((2^4 : ZMod 149) - 1)^(4 * 432345) = 1
    -- LV004g-6 gives ((1 - 2^4)^(4*432345) = 1; both equal since exponent is even.
    have h_lv6 : ((1 : ZMod 149) - 2 ^ 4) ^ (4 * 432345) = 1 :=
      one_sub_two_pow_four_pow_kS_eq_one
    have hflip : ((2 : ZMod 149) ^ 4 - 1) = -((1 : ZMod 149) - 2 ^ 4) := by ring
    have h_even : Even (4 * 432345) := ⟨2 * 432345, by ring⟩
    rw [hflip, h_even.neg_pow, h_lv6]
  -- The squared-bridge LHS uses `↑(2 : ℕ)` (natCast), while `h_lhs` uses
  -- the OfNat literal `2 : ZMod 149`; norm_cast unifies them.
  have h_bridge_norm := h_bridge
  push_cast at h_bridge_norm
  rw [h_lhs] at h_bridge_norm
  rw [h_bridge_norm, h_pre, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **FLT37 main closure: `¬IsPthPowerModPrime pollaczekUnit` for the
FLT37 certificate.** For `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`,
`pollaczekUnit 37 K 32` is **not** a `p`-th power modulo
`lehmerVandiverPrime`.

Combines:
- `isPthPowerModPrime_pollaczekUnit_iff_quotient_pow_eq_one` (cyclic
  criterion, LV004g main, already shipped),
- `flt37_pollaczekUnit_residue_pow_four_eq_lehmerVandiverProduct` (FLT37
  closure of the residue chain via the squared bridge),
- `lehmerVandiverProduct_thirtyseven_ne_one` (LV004g-6 numerical fact).

Auxiliary: `pollaczekUnit_notMem_lehmerVandiverPrime` discharges the
`hpoll_ne` hypothesis of the cyclic criterion (units of `𝓞 K` are not in
proper ideals).

This is the main consequence of the LV004g chain, feeding the LV005
algebraic step (`E_i not p-th power ⇒ p ∤ h⁺`). -/
theorem flt37_not_isPthPowerModPrime_pollaczekUnit
    [Fact (Nat.Prime 37)] [Fact (Nat.Prime 149)]
    (k : ℕ) (hℓ : 149 = k * 37 + 1) {t : ℕ}
    (ht_coprime : t.Coprime 149) (ht_ne : (t : ZMod 149) ^ k ≠ 1)
    (hkt : k = 4) (htval : t = 2) :
    ¬ IsPthPowerModPrime 37
      (lehmerVandiverPrime 37 149 k hℓ ht_coprime ht_ne)
      ((pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
        𝓞 (CyclotomicField 37 ℚ))) := by
  subst hkt htval
  -- Auxiliary: pollaczekUnit ∉ 𝔩.
  have hpoll_ne : ((pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
      (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ∉
      lehmerVandiverPrime 37 149 4 hℓ ht_coprime ht_ne :=
    pollaczekUnit_notMem_lehmerVandiverPrime 37 149 4 hℓ ht_coprime ht_ne 32
  -- Cyclic criterion: IsPthPower ↔ Q(pollaczekUnit^k) = 1.
  rw [isPthPowerModPrime_pollaczekUnit_iff_quotient_pow_eq_one
    (p := 37) 149 4 hℓ ht_coprime ht_ne 32 hpoll_ne]
  intro h_one
  -- Apply map_pow to h_one to expose Q(pollaczek)^4 = 1.
  rw [map_pow] at h_one
  -- Apply Φ: (Φ(Q(pollaczek)))^4 = 1.
  have h_phi := congrArg (lehmerVandiverPrime_quotientEquiv (p := 37)
    149 4 hℓ ht_coprime ht_ne) h_one
  rw [map_pow, map_one] at h_phi
  -- Use the FLT37 closure: (Φ(Q(pollaczek)))^4 = lehmerVandiverProduct.
  rw [flt37_pollaczekUnit_residue_pow_four_eq_lehmerVandiverProduct
    4 hℓ ht_coprime ht_ne rfl rfl] at h_phi
  -- Combined: lehmerVandiverProduct = 1, contradicting LV004g-6.
  exact lehmerVandiverProduct_thirtyseven_ne_one h_phi

/-- Local instances for the FLT37 certificate primes. -/
instance flt37_factPrime_thirtyseven : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- Local instance for the auxiliary prime 149. -/
instance flt37_factPrime_oneFortyNine : Fact (Nat.Prime 149) := ⟨by decide⟩

set_option backward.isDefEq.respectTransparency false in
/-- **FLT37 closure (concrete form).** The fully-instantiated version of
`flt37_not_isPthPowerModPrime_pollaczekUnit`: with all parameters fixed
to the FLT37 certificate tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`,
`pollaczekUnit 37 K 32` is not a `p`-th power modulo
`lehmerVandiverPrime`. -/
theorem flt37_not_isPthPowerModPrime_pollaczekUnit_concrete :
    ¬ IsPthPowerModPrime 37
      (lehmerVandiverPrime 37 149 4
        (by decide : (149 : ℕ) = 4 * 37 + 1)
        (by decide : (2 : ℕ).Coprime 149)
        (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
      ((pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
        𝓞 (CyclotomicField 37 ℚ))) :=
  flt37_not_isPthPowerModPrime_pollaczekUnit 4
    (by decide : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1) rfl rfl

end LehmerVandiver

end FLT37

end BernoulliRegular

end
