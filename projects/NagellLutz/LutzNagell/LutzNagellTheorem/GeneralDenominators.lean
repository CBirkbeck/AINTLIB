import LutzNagell.LutzNagellTheorem.GeneralCurve
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Int

/-!
# Denominators on general Weierstrass curves

For a rational point on a general Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
with `aᵢ ∈ ℤ`, if `x.den` equals a prime `p`, then we reach a contradiction.

The key argument: clearing denominators and reducing mod `p` three times shows that `p` divides
both `y.num` and `y.den`, contradicting `gcd(|y.num|, y.den) = 1`.

This is the generalized version of the denominator lemma from `Denominators.lean` and suffices
for the Lutz–Nagell integrality argument: when the rational root theorem gives `x.den | p` for
a prime `p`, we conclude `x.den ≠ p` and hence `x.den = 1`.

## Main results

* `LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`: if `(x, y)` is on the
  general Weierstrass curve and `x.den = p` (prime), then `False`.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

variable (W : WeierstrassCurve ℤ)

/-! ### Helper: p ∤ (α³ + stuff·p) when p ∤ α -/

private lemma not_dvd_sum_of_not_dvd_cube {p α : ℤ} (hp : Prime p) (hpa : ¬ p ∣ α)
    (c₂ c₄ c₆ : ℤ) :
    ¬ p ∣ (α ^ 3 + c₂ * α ^ 2 * p + c₄ * α * p ^ 2 + c₆ * p ^ 3) := by
  intro hdvd
  have hp_dvd_tail : p ∣ c₂ * α ^ 2 * p + c₄ * α * p ^ 2 + c₆ * p ^ 3 :=
    ⟨c₂ * α ^ 2 + c₄ * α * p + c₆ * p ^ 2, by ring⟩
  have hp_dvd_cube : p ∣ α ^ 3 := by
    obtain ⟨k₁, hk₁⟩ := hdvd
    obtain ⟨k₂, hk₂⟩ := hp_dvd_tail
    exact ⟨k₁ - k₂, by linarith⟩
  exact hpa (hp.dvd_of_dvd_pow hp_dvd_cube)

/-! ### The key denominator lemma for general Weierstrass curves -/


/-- If `(x, y)` lies on a general Weierstrass curve with integral coefficients and `x.den = p`
for a prime `p`, then we reach a contradiction.

**Proof outline:** Write `x = α/p` and `y = γ/δ` in lowest terms.
1. Clear denominators: `γ²p³ + a₁αγp²δ + a₃γp³δ = δ²(α³ + a₂α²p + a₄αp² + a₆p³)`.
2. Mod `p`: `0 ≡ δ²α³`, and since `gcd(α,p) = 1`, we get `p | δ`.
3. Write `δ = pδ₁`, substitute, divide by `p²`. Mod `p`: `0 ≡ δ₁²α³`, so `p | δ₁`.
4. Write `δ₁ = pδ₂`, substitute, divide by `p`. Mod `p`: `γ² ≡ 0`, so `p | γ`.
5. But `p | γ` and `p | δ` contradicts `gcd(|γ|, δ) = 1`. -/
theorem den_ne_prime_of_on_general_curve {x y : ℚ}
    (heq : y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
      x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ))
    {p : ℕ} (hp : p.Prime) (hden : x.den = p) : False := by
  -- Setup: write x = α/p, y = γ/δ in lowest terms
  set α := x.num
  set γ := y.num
  -- Key facts
  have hcop_x : Nat.Coprime α.natAbs p := hden ▸ x.reduced
  have hp_pos : (0 : ℤ) < p := Nat.cast_pos.mpr hp.pos
  have hp_ne : (p : ℤ) ≠ 0 := hp_pos.ne'
  have hd_pos : (0 : ℤ) < y.den := Nat.cast_pos.mpr y.pos
  have hd_ne : (y.den : ℤ) ≠ 0 := hd_pos.ne'
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp_not_dvd_α : ¬ (p : ℤ) ∣ α := by
    intro ⟨k, hk⟩
    have h2 : p ∣ Nat.gcd α.natAbs p :=
      Nat.dvd_gcd ⟨k.natAbs, by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩ dvd_rfl
    exact absurd (Nat.le_of_dvd one_pos (hcop_x ▸ h2)) (not_le.mpr hp.one_lt)
  -- Step 1: Clear denominators. x = α/p, y = γ/y.den. Multiply by p³ · y.den².
  have hQ : (γ : ℚ) ^ 2 * (p : ℚ) ^ 3 +
      (W.a₁ : ℚ) * α * γ * (p : ℚ) ^ 2 * y.den +
      (W.a₃ : ℚ) * γ * (p : ℚ) ^ 3 * y.den =
    (y.den : ℚ) ^ 2 * ((α : ℚ) ^ 3 + (W.a₂ : ℚ) * α ^ 2 * p +
      (W.a₄ : ℚ) * α * (p : ℚ) ^ 2 + (W.a₆ : ℚ) * (p : ℚ) ^ 3) := by
    have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hdQ : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.pos.ne'
    rw [show (x : ℚ) = x.num / x.den from (Rat.num_div_den x).symm,
        show (y : ℚ) = y.num / y.den from (Rat.num_div_den y).symm] at heq
    simp only [hden] at heq
    field_simp at heq
    linarith
  -- Lift to ℤ
  have hZ : γ ^ 2 * (p : ℤ) ^ 3 + W.a₁ * α * γ * (p : ℤ) ^ 2 * y.den +
      W.a₃ * γ * (p : ℤ) ^ 3 * y.den =
    (y.den : ℤ) ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
      W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) := by exact_mod_cast hQ
  -- Step 2: p divides everything on LHS, so p | δ²·(sum). Since p ∤ sum, p | δ².
  have hlhs_dvd : (p : ℤ) ∣ γ ^ 2 * (p : ℤ) ^ 3 + W.a₁ * α * γ * (p : ℤ) ^ 2 * y.den +
      W.a₃ * γ * (p : ℤ) ^ 3 * y.den := by
    apply dvd_add
    · apply dvd_add
      · exact dvd_mul_of_dvd_right (dvd_pow_self _ (by norm_num : 3 ≠ 0)) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by norm_num : 2 ≠ 0)) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by norm_num : 3 ≠ 0)) _) _
  have hrhs_dvd : (p : ℤ) ∣ (y.den : ℤ) ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
      W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) := hZ ▸ hlhs_dvd
  have hsum_not : ¬ (p : ℤ) ∣ (α ^ 3 + W.a₂ * α ^ 2 * p +
      W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) :=
    not_dvd_sum_of_not_dvd_cube hp_int hp_not_dvd_α _ _ _
  have hp_dvd_dsq : (p : ℤ) ∣ (y.den : ℤ) ^ 2 :=
    (hp_int.dvd_or_dvd hrhs_dvd).resolve_right hsum_not
  have hp_dvd_d : (p : ℤ) ∣ (y.den : ℤ) := hp_int.dvd_of_dvd_pow hp_dvd_dsq
  -- Step 3: Write y.den = p · δ₁, substitute, divide by p². Get p | δ₁.
  obtain ⟨δ₁, hδ₁⟩ := hp_dvd_d
  have hZ2 : (p : ℤ) * (γ ^ 2 + W.a₁ * α * γ * δ₁ + W.a₃ * γ * (p : ℤ) * δ₁) =
    δ₁ ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
      W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) := by
    have hp2_ne : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp_ne
    have hZ' := hZ
    rw [hδ₁] at hZ'
    have : (p : ℤ) ^ 2 * ((p : ℤ) * (γ ^ 2 + W.a₁ * α * γ * δ₁ +
        W.a₃ * γ * (p : ℤ) * δ₁)) =
      (p : ℤ) ^ 2 * (δ₁ ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
        W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3)) := by ring_nf; linarith
    exact mul_left_cancel₀ hp2_ne this
  have hp_dvd_rhs2 : (p : ℤ) ∣ δ₁ ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
      W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) :=
    ⟨γ ^ 2 + W.a₁ * α * γ * δ₁ + W.a₃ * γ * (p : ℤ) * δ₁, hZ2.symm⟩
  have hp_dvd_δ₁ : (p : ℤ) ∣ δ₁ :=
    hp_int.dvd_of_dvd_pow ((hp_int.dvd_or_dvd hp_dvd_rhs2).resolve_right hsum_not)
  -- Step 4: Write δ₁ = p · δ₂, substitute, divide by p. Get p | γ.
  obtain ⟨δ₂, hδ₂⟩ := hp_dvd_δ₁
  have hZ3 : γ ^ 2 + W.a₁ * α * γ * (p : ℤ) * δ₂ +
      W.a₃ * γ * (p : ℤ) ^ 2 * δ₂ =
    (p : ℤ) * δ₂ ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
      W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) := by
    rw [hδ₂] at hZ2
    exact mul_left_cancel₀ hp_ne (by linarith)
  have hp_dvd_γsq : (p : ℤ) ∣ γ ^ 2 := by
    have hp_dvd_mid : (p : ℤ) ∣ W.a₁ * α * γ * (p : ℤ) * δ₂ +
        W.a₃ * γ * (p : ℤ) ^ 2 * δ₂ :=
      ⟨W.a₁ * α * γ * δ₂ + W.a₃ * γ * (p : ℤ) * δ₂, by ring⟩
    have hp_dvd_rhs3 : (p : ℤ) ∣ (p : ℤ) * δ₂ ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * p +
        W.a₄ * α * (p : ℤ) ^ 2 + W.a₆ * (p : ℤ) ^ 3) :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _
    obtain ⟨k₁, hk₁⟩ := hp_dvd_rhs3
    obtain ⟨k₂, hk₂⟩ := hp_dvd_mid
    exact ⟨k₁ - k₂, by linarith⟩
  have hp_dvd_γ : (p : ℤ) ∣ γ := hp_int.dvd_of_dvd_pow hp_dvd_γsq
  -- Step 5: Contradiction. p | γ and p | y.den, but gcd(|γ|, y.den) = 1.
  have : p ∣ Nat.gcd γ.natAbs y.den := by
    apply Nat.dvd_gcd
    · have := Int.natAbs_dvd_natAbs.mpr hp_dvd_γ
      rwa [Int.natAbs_natCast] at this
    · exact Int.natCast_dvd_natCast.mp ⟨δ₁, hδ₁⟩
  rw [y.reduced] at this
  exact absurd (Nat.le_of_dvd one_pos this) (not_le.mpr hp.one_lt)

end LutzNagellTheorem
end LutzNagell
