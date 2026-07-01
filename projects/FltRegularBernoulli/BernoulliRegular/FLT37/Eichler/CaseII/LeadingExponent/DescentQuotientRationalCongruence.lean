import FltRegular.CaseII.InductionStep

/-!
# Case-II descent quotient is congruent to a rational integer mod `37`

This file proves a self-contained cyclotomic-arithmetic lemma feeding Washington's §9.1 Case-II
descent (the *primarity* input of Lemma 9.2): in the Case-II Fermat configuration the descent
quotient unit `ε₁/ε₂` is congruent to a **rational integer** modulo `37`.

## Statement

For `K = ℚ(ζ₃₇)`, a primitive `37`-th root of unity `ζ`, and a Case-II Fermat descent equation

`ε₁ x'^37 + ε₂ y'^37 = ε₃ ((ζ-1)^m z')^37`

with `¬ (ζ-1) ∣ x'` and `1 ≤ m`, the descent quotient satisfies

`∃ c : ℤ, (37 : 𝓞 K) ∣ (↑(ε₁/ε₂) - c)`.

That is, `ε₁/ε₂ ≡ c (mod 37)` in `𝓞 K`.

## Why this is true (Washington, GTM 83, §9.1; the proof sketch)

1. **The RHS is divisible by `(ζ-1)^{37·m}`.**  Expanding the cube on the right,
   `ε₃ ((ζ-1)^m z')^37 = ε₃ (ζ-1)^{37m} z'^37`, and `ε₃` is a unit; hence
   `(ζ-1)^{37m} ∣ ε₁ x'^37 + ε₂ y'^37`.

2. **`(ζ-1)^{37m}` divisibility ⟹ `37` divisibility.**  The prime `37` is totally ramified in
   `K = ℚ(ζ₃₇)`: `37 ∼ (ζ-1)^{36}` (ramification index `e = p - 1 = 36`), the fact
   `associated_zeta_sub_one_pow_prime`.  Since `m ≥ 1`, `37·m ≥ 37 > 36`, so `(ζ-1)^{36}` already
   divides `(ζ-1)^{37m}`, whence `37 ∣ ε₁ x'^37 + ε₂ y'^37`.

3. **Move `ε₂ y'^37` over.**  Then `ε₁ x'^37 ≡ -ε₂ y'^37 (mod 37)`, i.e. multiplying by the unit
   `ε₂⁻¹` gives `(ε₁/ε₂) x'^37 ≡ -y'^37 (mod 37)`.

4. **Freshman's dream (Lemma 1.8 / Frobenius in char `37`).**  Every `α ∈ 𝓞 K` satisfies
   `α^37 ≡ (rational integer) (mod 37)`: writing `α` in the `(ζ-1)`-power basis with `ℤ`
   coefficients, `(∑ⱼ bⱼ (ζ-1)^j)^37 ≡ ∑ⱼ bⱼ^37 (ζ-1)^{37 j}`, and `bⱼ^37 ≡ bⱼ (mod 37)` (Fermat),
   collapsing to a rational integer.  This is `exists_dvd_pow_sub_Int_pow` (proved via
   `exists_add_pow_prime_eq` over the `(ζ-1)`-power basis `exists_zeta_sub_one_dvd_sub_Int`).

5. **`x'` is a unit mod `37`.**  Since `¬ (ζ-1) ∣ x'` and `(ζ-1)` is the only prime above `37`,
   `x'` is coprime to `37` (`isCoprime_of_not_zeta_sub_one_dvd`), so `x'^37` is invertible mod `37`.

6. **Combine.**  In `R = 𝓞 K / (37)`, `(ε₁/ε₂) = -y'^37 · (x'^37)⁻¹`, and by step 4 both `y'^37`
   and `x'^37` reduce to rational integers, so `ε₁/ε₂` reduces to a rational integer `c`.

Steps 3–6 are packaged in flt-regular as `exists_solution'_aux` (it produces `a : 𝓞 K` with
`37 ∣ ↑(ε₁/ε₂) - a^37`), and the final reduction of `a^37` to a rational `(b : ℤ)^37 = (b^37 : ℤ)`
is `exists_dvd_pow_sub_Int_pow`.

## What this file does *not* do

It imports only from `flt-regular` and `mathlib`; it does **not** depend on any other
`BernoulliRegular` file, and it modifies nothing.  The conclusion shape
`∃ c : ℤ, (37 : 𝓞 K) ∣ (↑(ε₁/ε₂) - c)` is exactly the primarity hypothesis consumed by
`caseII_discharge_unit_is_real` (Lemma 9.2 endpoint) and by Washington's §9.1 descent.

The lemma is stated for a general `K` with `[IsCyclotomicExtension {37} ℚ K]` (so it applies to
`CyclotomicField 37 ℚ` and to any concrete `ℚ(ζ₃₇)`).
-/

open scoped NumberField

namespace BernoulliRegular.FLT37.Eichler

/-- **The Case-II descent quotient is congruent to a rational integer mod `37`.**

In the Case-II Fermat configuration `ε₁ x'^37 + ε₂ y'^37 = ε₃ ((ζ-1)^m z')^37` with
`¬ (ζ-1) ∣ x'` and `1 ≤ m`, there is a rational integer `c` with `(37 : 𝓞 K) ∣ (↑(ε₁/ε₂) - c)`,
i.e. `ε₁/ε₂ ≡ c (mod 37)`.

This is the *primarity* input of Washington's Lemma 9.2; in Case II it is unconditional, since
`m ≥ 1` forces `(ζ-1)^{37 m}` — hence `37 ∼ (ζ-1)^{36}` — to divide the right-hand side.  The
upgrade to a **rational-integer** congruence is the freshman's-dream / Fermat step
`exists_dvd_pow_sub_Int_pow` combined with the coprimality of `x'` to `37`
(`exists_solution'_aux`). -/
theorem caseII_quotient_sub_intCast_mem_37
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {m : ℕ} (hm : 1 ≤ m)
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hx' : ¬ (hζ.toInteger - 1) ∣ x')
    (heq : (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
      (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ c : ℤ, (37 : 𝓞 K) ∣ ((↑(ε₁ / ε₂) : 𝓞 K) - (c : 𝓞 K)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  -- Step 2 prep: `(ζ-1)^{37-1}` divides the RHS because `37·m ≥ 37 ≥ 37 - 1`.
  have hp_le : 37 - 1 ≤ m * 37 := by
    refine (Nat.sub_le _ _).trans ?_
    calc 37 = 1 * 37 := (one_mul _).symm
      _ ≤ m * 37 := Nat.mul_le_mul_right 37 hm
  -- Step 1: rewrite the RHS to expose the `(ζ-1)^{37-1}` factor: collapse the cube, reorder,
  -- and split `(ζ-1)^{m·37} = (ζ-1)^{(37-1)} · (ζ-1)^{m·37-(37-1)}`.
  rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc,
    ← Nat.sub_add_cancel hp_le, add_comm _ (37 - 1), pow_add, mul_assoc] at heq
  -- Step 2: pass to `𝓞 K / (37)`; the RHS vanishes (since `(ζ-1)^{37-1} ∼ 37`), so `37 ∣ LHS`.
  apply_fun Ideal.Quotient.mk (Ideal.span <| singleton ((37 : ℕ) : 𝓞 K)) at heq
  rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime hζ).symm.dvd, zero_mul,
    Ideal.Quotient.eq_zero_iff_dvd] at heq
  -- Steps 3, 5, 6 (`exists_solution'_aux`): `37 ∣ ε₁ x'^37 + ε₂ y'^37` ⟹ `37 ∣ ↑(ε₁/ε₂) - a^37`.
  obtain ⟨a, ha⟩ :=
    exists_solution'_aux (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2) hζ hx' heq
  -- Step 4 (`exists_dvd_pow_sub_Int_pow`): the freshman's dream collapses `a^37` to a rational
  -- `(b : ℤ)^37 = ((b^37 : ℤ) : 𝓞 K)`.
  obtain ⟨b, hb⟩ :=
    exists_dvd_pow_sub_Int_pow (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2) a
  -- Add the two congruences: `↑(ε₁/ε₂) - a^37` and `a^37 - (b:ℤ)^37`.
  have hcong := dvd_add ha hb
  rw [sub_add_sub_cancel, ← Int.cast_pow] at hcong
  exact ⟨b ^ 37, hcong⟩

end BernoulliRegular.FLT37.Eichler
