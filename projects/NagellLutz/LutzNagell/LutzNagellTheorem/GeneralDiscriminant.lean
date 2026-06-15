import LutzNagell.LutzNagellTheorem.GeneralMain
import LutzNagell.LutzNagellTheorem.GeneralIntegralMultiple

/-!
# General discriminant divisibility for Weierstrass curves

For a nonzero torsion point `(x₀, y₀) ∈ ℤ²` on a general Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ`, define
`κ₀ = 2y₀ + a₁x₀ + a₃`. Then either `κ₀ = 0` or `κ₀² | 4Δ`.

## Main results

* `lutz_nagell_discriminant_general`: the general discriminant divisibility theorem.

## Proof outline

1. From the curve equation, `κ₀² = Ψ₂Sq(x₀) = 4x₀³ + b₂x₀² + 2b₄x₀ + b₆`.
2. Using the coordinate formula for `2•P` and integrality of the doubled point,
   derive `κ₀² | 4·Ψ₃(x₀)`.
3. A polynomial identity gives `h(x₀)² ≡ 0 (mod κ₀²)` where `h = 6x² + b₂x + b₄`.
4. A Bézout identity `d₁·Ψ₂Sq + d₂·h² = 4Δ` yields `κ₀² | 4Δ`.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve Polynomial

variable (W : WeierstrassCurve ℤ)

/-! ### Algebraic identities -/

/-- κ₀² = Ψ₂Sq(x₀): the square-completed curve equation. -/
private lemma kappa_sq_eq_Psi2Sq_eval_general
    {x₀ y₀ : ℤ}
    (hcurve : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 =
      4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  nlinarith

/-- The key polynomial identity: h(x)² + 4·Ψ₃(x) = (12x + b₂)·Ψ₂Sq(x).
Uses the relation `b₂b₆ - b₄² = 4b₈` which holds after unfolding to `aᵢ`. -/
private lemma h_sq_add_four_prePsi3_eq_general (x₀ : ℤ) :
    (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 +
      4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
           3 * W.b₆ * x₀ + W.b₈) =
    (12 * x₀ + W.b₂) * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Bézout identity: d₁·Ψ₂Sq(x) + d₂·h(x)² = 4Δ. -/
private lemma bezout_general (x₀ : ℤ) :
    (432 * x₀ ^ 3 + 108 * W.b₂ * x₀ ^ 2 + 216 * W.b₄ * x₀ +
      (-W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 108 * W.b₆)) *
      (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) +
    (-48 * x₀ ^ 2 - 8 * W.b₂ * x₀ + (W.b₂ ^ 2 - 32 * W.b₄)) *
      (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 = 4 * W.Δ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.Δ]
  ring

/-! ### Pure algebra: κ² | Ψ₂Sq(x₀) and κ² | 4·Ψ₃(x₀) imply κ² | 4Δ -/

/-- From κ₀² = Ψ₂Sq(x₀) and κ₀² | 4·Ψ₃(x₀), deduce κ₀² | 4Δ. -/
private lemma kappa_sq_dvd_four_delta_of_coord_identity
    (x₀ : ℤ) (κ₀ : ℤ)
    (hkappa : κ₀ ^ 2 = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆)
    (hdvd_prePsi : κ₀ ^ 2 ∣ 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
        3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈)) :
    κ₀ ^ 2 ∣ 4 * W.Δ := by
  set Ψ₂Sq_val := 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆
  set h_val := 6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄
  set Ψ₃_val := 3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
      3 * W.b₆ * x₀ + W.b₈
  have hdvd_h_sq : κ₀ ^ 2 ∣ h_val ^ 2 := by
    have : h_val ^ 2 = (12 * x₀ + W.b₂) * Ψ₂Sq_val - 4 * Ψ₃_val := by
      linarith [h_sq_add_four_prePsi3_eq_general W x₀]
    rw [this]; exact dvd_sub (dvd_mul_of_dvd_right ⟨1, by linarith [hkappa]⟩ _) hdvd_prePsi
  rw [← bezout_general W x₀]
  exact dvd_add (dvd_mul_of_dvd_right ⟨1, by linarith [hkappa]⟩ _) (dvd_mul_of_dvd_right hdvd_h_sq _)

/-! ### Helpers for the main theorem -/

/-- The curve equation over ℤ, derived from integrality of coordinates. -/
private lemma curveZ_equation_of_integral
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y) :
    y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ := by
  have : (y₀ : ℚ) ^ 2 + (W.a₁ : ℚ) * x₀ * y₀ + (W.a₃ : ℚ) * y₀ =
      (x₀ : ℚ) ^ 3 + (W.a₂ : ℚ) * x₀ ^ 2 + (W.a₄ : ℚ) * x₀ + (W.a₆ : ℚ) := by
    have hQ := (curveQ_equation_iff W x y).mp hpt.left; subst hx; subst hy; linarith
  exact_mod_cast this

/-- If `κ₀ = 2y₀ + a₁x₀ + a₃ ≠ 0`, then the point does not have order 2. -/
private lemma addOrderOf_ne_two_of_kappa_ne_zero
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y)
    (hκ : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    addOrderOf (Affine.Point.some _ _ hns) ≠ 2 := by
  intro h2
  have h2P : (2 : ℕ) • Affine.Point.some _ _ hns = 0 := by
    convert addOrderOf_nsmul_eq_zero (x := Affine.Point.some _ _ hns) using 2; exact h2.symm
  have h2Jac := nsmul_eq_zero_affine_to_jac W h2P
  have hψ₂ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns 2 h2Jac
  rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂,
      WeierstrassCurve.Affine.evalEval_polynomialY] at hψ₂
  simp only [curveQ_a₁, curveQ_a₃] at hψ₂
  apply hκ
  have : (2 * (y₀ : ℚ) + (W.a₁ : ℚ) * x₀ + (W.a₃ : ℚ)) = 0 := by
    rw [← hx, ← hy] at hψ₂; linarith
  exact_mod_cast this

/-! ### Evaluation lemmas connecting Mathlib polynomials to integer values -/

/-- The coordinate formula for `Φ 2` evaluated at `x`:
`Φ₂(x) = x · Ψ₂Sq(x) - Ψ₃(x)`. -/
private lemma Phi2_eval_eq (x : ℚ) :
    eval x ((curveQ W).Φ 2) =
      x * eval x (curveQ W).Ψ₂Sq - eval x (curveQ W).Ψ₃ := by
  conv_lhs =>
    rw [show (curveQ W).Φ 2 = X * (curveQ W).Ψ₂Sq - (curveQ W).Ψ₃ from by
      rw [WeierstrassCurve.Φ, WeierstrassCurve.ΨSq_two]
      simp [even_two, WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_one]]
  simp only [eval_sub, eval_mul, eval_X]

/-- Evaluate `ΨSq 2` = `Ψ₂Sq`. -/
private lemma PsiSq_two_eval_eq (x : ℚ) :
    eval x ((curveQ W).ΨSq 2) = eval x (curveQ W).Ψ₂Sq := by
  rw [WeierstrassCurve.ΨSq_two]

/-- Evaluate `Ψ₂Sq` at `x` for `curveQ W`. -/
private lemma Psi2Sq_eval_eq (x : ℚ) :
    eval x (curveQ W).Ψ₂Sq =
      4 * x ^ 3 + (W.b₂ : ℚ) * x ^ 2 + 2 * (W.b₄ : ℚ) * x + (W.b₆ : ℚ) := by
  have hmap : (curveQ W).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap ℤ ℚ) := by
    change (W.map (algebraMap ℤ ℚ)).Ψ₂Sq = _; rw [WeierstrassCurve.map_Ψ₂Sq]
  rw [hmap, eval_map, WeierstrassCurve.Ψ₂Sq]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, algebraMap_int_eq,
             Int.coe_castRingHom]
  push_cast
  ring

/-- Evaluate `Ψ₃` at `x` for `curveQ W`. -/
private lemma Psi3_eval_eq (x : ℚ) :
    eval x (curveQ W).Ψ₃ =
      3 * x ^ 4 + (W.b₂ : ℚ) * x ^ 3 + 3 * (W.b₄ : ℚ) * x ^ 2 +
        3 * (W.b₆ : ℚ) * x + (W.b₈ : ℚ) := by
  have hmap : (curveQ W).Ψ₃ = W.Ψ₃.map (algebraMap ℤ ℚ) := by
    change (W.map (algebraMap ℤ ℚ)).Ψ₃ = _; rw [WeierstrassCurve.map_Ψ₃]
  rw [hmap, eval_map, WeierstrassCurve.Ψ₃]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, eval₂_ofNat,
             algebraMap_int_eq, Int.coe_castRingHom]

/-! ### The Ψ₃ divisibility argument -/

/-- The core divisibility: from the coordinate formula for `2•P` and integrality of the
doubled point, derive `κ₀² | 4·Ψ₃(x₀)`. -/
private lemma kappa_sq_dvd_four_Psi3
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y)
    {κ₀ : ℤ} (hκ₀ : κ₀ = 2 * y₀ + W.a₁ * x₀ + W.a₃)
    (hkappa_sq : κ₀ ^ 2 = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆)
    (hκ : κ₀ ≠ 0) :
    κ₀ ^ 2 ∣ 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
      3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈) := by
  set P := Affine.Point.some _ _ hpt
  have hm_pos := htor.addOrderOf_pos
  have hord_ne1 : addOrderOf P ≠ 1 :=
    fun h => Affine.Point.some_ne_zero hpt (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hord_ne2 : addOrderOf P ≠ 2 :=
    addOrderOf_ne_two_of_kappa_ne_zero W hpt hx hy (by rwa [← hκ₀])
  have hord_gt2 : 2 < addOrderOf P := by omega
  have h2P_ne : (2 : ℕ) • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr hord_gt2)
  obtain ⟨x', y', hns', h2P_eq⟩ := exists_some_of_ne_zero W h2P_ne
  have h2P_tor : IsOfFinAddOrder (Affine.Point.some _ _ hns') := h2P_eq ▸ htor.nsmul
  have h2P_zsmul : (2 : ℤ) • P = Affine.Point.some _ _ hns' := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, natCast_zsmul]; exact h2P_eq
  have hcoord := x_coord_nsmul_eq_general W hpt
    (show (2 : ℤ) ≠ 0 by norm_num) hns' h2P_zsmul
  rw [PsiSq_two_eval_eq, Phi2_eval_eq] at hcoord
  have hPsi3_eq : eval x (curveQ W).Ψ₃ =
      (x - x') * eval x (curveQ W).Ψ₂Sq := by linarith
  rw [Psi2Sq_eval_eq, Psi3_eval_eq] at hPsi3_eq
  have hkappa_sq_Q : (4 * (x₀ : ℚ) ^ 3 + (W.b₂ : ℚ) * (x₀ : ℚ) ^ 2 +
    2 * (W.b₄ : ℚ) * (x₀ : ℚ) + (W.b₆ : ℚ)) = (κ₀ : ℚ) ^ 2 := by
    exact_mod_cast hkappa_sq.symm
  have hPsi3_sub : (3 * (x₀ : ℚ) ^ 4 + (W.b₂ : ℚ) * (x₀ : ℚ) ^ 3 +
      3 * (W.b₄ : ℚ) * (x₀ : ℚ) ^ 2 + 3 * (W.b₆ : ℚ) * (x₀ : ℚ) + (W.b₈ : ℚ)) =
    ((x₀ : ℚ) - x') * ((κ₀ : ℚ) ^ 2) := by
    rw [← hx] at hPsi3_eq; rw [← hkappa_sq_Q]; linarith
  rcases lutz_nagell_integrality_general W hns' h2P_tor with
    ⟨⟨x'₀, hx'⟩, _⟩ | ⟨_, h4x', _⟩
  · have hPsi3_Z : 3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
        3 * W.b₆ * x₀ + W.b₈ = κ₀ ^ 2 * (x₀ - x'₀) := by
      have : (3 * (x₀ : ℚ) ^ 4 + (W.b₂ : ℚ) * x₀ ^ 3 + 3 * (W.b₄ : ℚ) * x₀ ^ 2 +
          3 * (W.b₆ : ℚ) * x₀ + (W.b₈ : ℚ)) =
        ((κ₀ : ℚ) ^ 2) * ((x₀ : ℚ) - x'₀) := by rw [← hx'] at hPsi3_sub; linarith
      exact_mod_cast this
    exact dvd_mul_of_dvd_right ⟨x₀ - x'₀, hPsi3_Z⟩ 4
  · obtain ⟨n₀, hn₀⟩ := h4x'
    have h4x'_eq : 4 * x' = (n₀ : ℚ) := by linarith
    have h4Psi3_Z : 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
        3 * W.b₆ * x₀ + W.b₈) = κ₀ ^ 2 * (4 * x₀ - n₀) := by
      have : 4 * (3 * (x₀ : ℚ) ^ 4 + (W.b₂ : ℚ) * x₀ ^ 3 + 3 * (W.b₄ : ℚ) * x₀ ^ 2 +
          3 * (W.b₆ : ℚ) * x₀ + (W.b₈ : ℚ)) =
        ((κ₀ : ℚ) ^ 2) * (4 * (x₀ : ℚ) - (n₀ : ℚ)) := by
        have : 4 * ((x₀ : ℚ) - x') * ((κ₀ : ℚ) ^ 2) =
          ((κ₀ : ℚ) ^ 2) * (4 * (x₀ : ℚ) - (n₀ : ℚ)) := by rw [← h4x'_eq]; ring
        linarith [hPsi3_sub]
      exact_mod_cast this
    exact ⟨4 * x₀ - n₀, h4Psi3_Z⟩

/-! ### The main theorem -/

/-- **General discriminant divisibility.** For a nonzero torsion point with integral
coordinates on a general Weierstrass curve, either `κ₀ = 0` or `κ₀² | 4Δ`,
where `κ₀ = 2y₀ + a₁x₀ + a₃`. -/
theorem lutz_nagell_discriminant_general
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  set κ₀ := 2 * y₀ + W.a₁ * x₀ + W.a₃
  by_cases hκ : κ₀ = 0
  · exact Or.inl hκ
  · right
    have hkappa_sq := kappa_sq_eq_Psi2Sq_eval_general W
      (curveZ_equation_of_integral W hpt hx hy)
    exact kappa_sq_dvd_four_delta_of_coord_identity W x₀ κ₀ hkappa_sq
      (kappa_sq_dvd_four_Psi3 W hpt htor hx hy rfl hkappa_sq hκ)

/-- **Combined Lutz–Nagell theorem for general Weierstrass curves.**

For a nonzero torsion point on `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over `ℚ`
with `aᵢ ∈ ℤ`, either:
1. the coordinates are integers `x = x₀, y = y₀`, and either `κ₀ = 0` or `κ₀² | 4Δ`
   where `κ₀ = 2y₀ + a₁x₀ + a₃`, or
2. the point has order exactly 2 and `4x, 8y ∈ ℤ`. -/
theorem lutz_nagell_general
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ (x₀ y₀ : ℤ), (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧
      (2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 ∨
       (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ))
    ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
        (∃ n : ℤ, (n : ℚ) = 4 * x) ∧ ∃ m : ℤ, (m : ℚ) = 8 * y) := by
  rcases lutz_nagell_integrality_general W hpt htor with
    ⟨⟨x₀, hx⟩, ⟨y₀, hy⟩⟩ | hord2
  · exact Or.inl ⟨x₀, y₀, hx, hy,
      lutz_nagell_discriminant_general W hpt htor hx hy⟩
  · exact Or.inr hord2

end LutzNagellTheorem
end LutzNagell
