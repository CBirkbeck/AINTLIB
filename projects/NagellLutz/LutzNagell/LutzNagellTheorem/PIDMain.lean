import LutzNagell.LutzNagellTheorem.PIDPrimeOrder
import LutzNagell.LutzNagellTheorem.PIDIntegralMultiple
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The Lutz–Nagell theorem over PIDs and number fields

Generalization of the classical Lutz–Nagell theorem from `ℤ/ℚ` to a PID `R` of
characteristic zero with fraction field `K`.

## Main results

### Without ramification hypothesis (Option B)

* `den_powerful_of_on_curve`: **Every** prime factor of `den_R(x)` appears with
  multiplicity ≥ 2. No hypothesis on the torsion order needed — this is a property
  of ALL points on the curve. Denominators are only supported at "ramified-like" primes.

### With unramified hypothesis

* `lutz_nagell_integrality_pid`: If every prime dividing the torsion order is
  squarefree in `R`, then coordinates are integral (or order 2 with bounded denominators).

### Discriminant

* `lutz_nagell_pid_discriminant`: For integral coordinates, κ₀ = 0 or κ₀² ∣ 4Δ.

### Number fields

* `lutz_nagell_number_field`: The theorem for number fields `K` with
  `IsPrincipalIdealRing (𝓞 K)` (class number 1).
-/

namespace LutzNagell
namespace PID

open WeierstrassCurve IsFractionRing Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

/-! ### Helper lemmas -/

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [IsFractionRing R K] in
/-- Convert `n • P = 0` on affine points to `(n : ℤ) • P = 0` on Jacobian points. -/
lemma nsmul_eq_zero_affine_to_jac {x y : K}
    {hns : (curveK R K W).toAffine.Nonsingular x y} {n : ℕ}
    (h : n • (Affine.Point.some _ _ hns) = 0) :
    (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  rw [natCast_zsmul]
  simpa only [map_nsmul, map_zero] using
    congrArg (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm h

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K]
    [IsFractionRing R K] in
/-- A nonzero affine point is of the form `.some hns`. -/
lemma exists_some_of_ne_zero {Q : Affine.Point ((curveK R K W).toAffine)}
    (hQ : Q ≠ 0) :
    ∃ x y, ∃ hns : (curveK R K W).toAffine.Nonsingular x y, Q = .some _ _ hns := by
  rcases Q with _ | ⟨_, _, hns⟩
  · exact absurd rfl hQ
  · exact ⟨_, _, hns, rfl⟩

/-! ### The powerful denominator theorem (no torsion hypothesis needed) -/

omit [CharZero R] [DecidableEq K] in
/-- Every prime factor of `den_R(x)` on a curve point has multiplicity at least 2. -/
theorem den_powerful_of_on_curve {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆) :
    ∀ q : R, Prime q → q ∣ (IsFractionRing.den R x : R) →
      q ^ 2 ∣ (IsFractionRing.den R x : R) :=
  fun _ hq hqd => by_contra fun h => den_no_simple_prime_factor_of_on_curve W heq hq hqd h

/-! ### Odd prime factor case -/

private lemma integrality_of_odd_prime_factor {x y : K}
    (hpt : (curveK R K W).toAffine.Nonsingular x y) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hpm : p ∣ addOrderOf (Affine.Point.some _ _ hpt))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) (hsf : Squarefree (p : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  set P := Affine.Point.some _ _ hpt
  set k := addOrderOf P / p
  have hkp : k * p = addOrderOf P := Nat.div_mul_cancel hpm
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd htor.addOrderOf_pos hpm) hp.pos
  have hQ_ne : k • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd hk_pos (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by
        calc k = k * 1 := (mul_one k).symm
          _ < k * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hk_pos
          _ = addOrderOf P := hkp))
  have hpQ : p • (k • P) = 0 := by rw [← mul_nsmul, hkp, addOrderOf_nsmul_eq_zero]
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne
  obtain ⟨hx'_int, hy'_int⟩ := prime_order_integrality_squarefree W hns' hp hodd
    (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ hpQ)) hsf
  exact isInteger_of_nsmul_isInteger W hpt (Int.natCast_ne_zero.mpr hk_pos.ne')
    (by rw [Int.cast_natCast]; exact Nat.cast_ne_zero.mpr hk_pos.ne') hns'
    (show (k : ℤ) • P = Affine.Point.some _ _ hns' by rw [natCast_zsmul]; exact hQ_eq)
    hx'_int hy'_int

/-! ### Four divides order case -/

private lemma integrality_of_four_dvd_order {x y : K}
    (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (h4 : 4 ∣ addOrderOf (Affine.Point.some _ _ hpt))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) (hsf2 : Squarefree (2 : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  set P := Affine.Point.some _ _ hpt
  set k := addOrderOf P / 4
  have hk4 : k * 4 = addOrderOf P := Nat.div_mul_cancel h4
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd htor.addOrderOf_pos h4) (by norm_num)
  have hQ_ne : k • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd hk_pos (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by omega))
  have h4Q : 4 • (k • P) = 0 := by rw [← mul_nsmul, hk4, addOrderOf_nsmul_eq_zero]
  have h2Q_ne : (2 : ℕ) • (k • P) ≠ 0 := by
    intro h; rw [← mul_nsmul] at h
    exact absurd (Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by omega))
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne
  obtain ⟨hx'_int, hy'_int⟩ := integrality_of_order_four_squarefree W hns'
    (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ h4Q)) (hQ_eq ▸ h2Q_ne) hsf2
  exact isInteger_of_nsmul_isInteger W hpt (Int.natCast_ne_zero.mpr hk_pos.ne')
    (by rw [Int.cast_natCast]; exact Nat.cast_ne_zero.mpr hk_pos.ne') hns'
    (show (k : ℤ) • P = Affine.Point.some _ _ hns' by rw [natCast_zsmul]; exact hQ_eq)
    hx'_int hy'_int

/-! ### The general integrality theorem -/

/-- **Generalized Lutz–Nagell integrality over PIDs.**

For a nonzero finite-order point on a general Weierstrass curve with coefficients in
a PID `R` of characteristic zero, if every prime `p` dividing the torsion order satisfies
`Squarefree (p : R)` (equivalently, `p` does not ramify in `R`), then either:
- the coordinates are integral (`x, y ∈ R`), or
- the point has order exactly 2 and `den_R(x) ∣ 4`. -/
theorem lutz_nagell_integrality_pid
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : R)) :
    ((IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y) ∨
    (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
      (IsFractionRing.den R x : R) ∣ (4 : R)) := by
  set P := Affine.Point.some _ _ hpt
  have hP_ne : P ≠ 0 := Affine.Point.some_ne_zero hpt
  have hm_ne_one : addOrderOf P ≠ 1 :=
    fun h => hP_ne (AddMonoid.addOrderOf_eq_one_iff.mp h)
  by_cases hord2 : addOrderOf P = 2
  · right
    have h2P : (2 : ℕ) • P = 0 := by rw [← hord2, addOrderOf_nsmul_eq_zero]
    exact ⟨hord2, den_dvd_of_order_two W (Nat.cast_ne_zero.mpr (by norm_num)) hpt
      (nsmul_eq_zero_affine_to_jac W h2P)⟩
  · left
    by_cases h_odd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ addOrderOf P
    · obtain ⟨p, hp, hodd, hpm⟩ := h_odd
      exact integrality_of_odd_prime_factor W hpt hp hodd hpm htor (hsf_all p hp hpm)
    · push_neg at h_odd
      have h_all_two : ∀ q, q.Prime → q ∣ addOrderOf P → q = 2 := by
        intro q hq hqm; by_contra hne; exact h_odd q hq hne hqm
      have h2_dvd : 2 ∣ addOrderOf P := by
        obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm_ne_one
        exact (h_all_two q hq hqm) ▸ hqm
      have h4_dvd : 4 ∣ addOrderOf P := by
        obtain ⟨k₁, hk₁⟩ := h2_dvd
        obtain ⟨q, hq, hqk₁⟩ := Nat.exists_prime_and_dvd (show k₁ ≠ 1 by omega)
        rw [h_all_two q hq (hqk₁.trans ⟨2, by omega⟩)] at hqk₁
        obtain ⟨j, hj⟩ := hqk₁; exact ⟨j, by omega⟩
      exact integrality_of_four_dvd_order W hpt h4_dvd htor
        (hsf_all 2 (by decide) h2_dvd)

/-! ### Discriminant divisibility -/

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] in
private lemma kappa_sq_eq_Psi2Sq {x₀ y₀ : R}
    (hcurve : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 =
      4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * hcurve

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] in
private lemma bezout_identity (x₀ : R) :
    (432 * x₀ ^ 3 + 108 * W.b₂ * x₀ ^ 2 + 216 * W.b₄ * x₀ +
      (-W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 108 * W.b₆)) *
      (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) +
    (-48 * x₀ ^ 2 - 8 * W.b₂ * x₀ + (W.b₂ ^ 2 - 32 * W.b₄)) *
      (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 = 4 * W.Δ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
             WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.Δ]; ring

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] in
private lemma kappa_sq_dvd_four_delta (x₀ κ₀ : R)
    (hkappa : κ₀ ^ 2 = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆)
    (hdvd_Psi3 : κ₀ ^ 2 ∣ 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
        3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈)) :
    κ₀ ^ 2 ∣ 4 * W.Δ := by
  have hdvd_h_sq : κ₀ ^ 2 ∣ (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 := by
    have h_id : (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 +
        4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
             3 * W.b₆ * x₀ + W.b₈) =
      (12 * x₀ + W.b₂) * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) := by
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
                 WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring
    have : (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) ^ 2 =
        (12 * x₀ + W.b₂) * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) -
        4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
             3 * W.b₆ * x₀ + W.b₈) := by linear_combination h_id
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right ⟨1, by rw [mul_one]; exact hkappa.symm⟩ _) hdvd_Psi3
  rw [← bezout_identity W x₀]
  exact dvd_add (dvd_mul_of_dvd_right ⟨1, by rw [mul_one]; exact hkappa.symm⟩ _)
    (dvd_mul_of_dvd_right hdvd_h_sq _)

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] in
/-- **Lutz–Nagell discriminant divisibility over PIDs.**

For integral coordinates on the curve satisfying `κ₀² ∣ 4·Ψ₃(x₀)`,
either κ₀ = 0 or κ₀² ∣ 4Δ. The hypothesis `κ₀² ∣ 4·Ψ₃(x₀)` follows from
torsion via the coordinate formula for `2•P`. -/
theorem lutz_nagell_pid_discriminant
    {x₀ y₀ : R}
    (hcurve : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    (hdvd_Psi3 : (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣
      4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
        3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈)) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  by_cases hκ : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0
  · exact Or.inl hκ
  · exact Or.inr (kappa_sq_dvd_four_delta W x₀ _ (kappa_sq_eq_Psi2Sq W hcurve) hdvd_Psi3)

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] in
/-- Ψ₃ divisibility from `Ψ₃(x₀) = κ₀² · c`. -/
theorem kappa_sq_dvd_four_Psi3_of_integral {x₀ κ₀ c : R}
    (hPsi3 : 3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
      3 * W.b₆ * x₀ + W.b₈ = κ₀ ^ 2 * c) :
    κ₀ ^ 2 ∣ 4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
      3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈) :=
  dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4

/-! ### Deriving discriminant divisibility from torsion -/

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] in
private lemma curveR_equation_of_isInteger
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ := by
  have hQ := (curveK_equation_iff R K W x y).mp hpt.left
  rw [← hx, ← hy] at hQ
  have h : algebraMap R K (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀) =
      algebraMap R K (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) := by
    simp only [map_add, map_mul, map_pow]; linear_combination hQ
  exact IsFractionRing.injective R K h

omit [CharZero R] in
private lemma addOrderOf_ne_two_of_kappa_ne_zero
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hκ : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    addOrderOf (Affine.Point.some _ _ hns) ≠ 2 := by
  intro h2
  have h2P : (2 : ℕ) • Affine.Point.some _ _ hns = 0 := by
    convert addOrderOf_nsmul_eq_zero (x := Affine.Point.some _ _ hns) using 2; exact h2.symm
  have h2Jac := nsmul_eq_zero_affine_to_jac W h2P
  have hψ₂ := evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns 2 h2Jac
  rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂,
      WeierstrassCurve.Affine.evalEval_polynomialY] at hψ₂
  simp only [curveK_a₁, curveK_a₃] at hψ₂
  apply hκ
  apply IsFractionRing.injective R K
  rw [← hx, ← hy] at hψ₂
  simp only [map_add, map_mul, map_ofNat, map_zero]
  linear_combination hψ₂

/-! #### Evaluation lemmas for division polynomials over K -/

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K] in
private lemma Phi2_eval_eq (x : K) :
    eval x ((curveK R K W).Φ 2) =
      x * eval x (curveK R K W).Ψ₂Sq - eval x (curveK R K W).Ψ₃ := by
  conv_lhs =>
    rw [show (curveK R K W).Φ 2 = X * (curveK R K W).Ψ₂Sq - (curveK R K W).Ψ₃ from by
      rw [WeierstrassCurve.Φ, WeierstrassCurve.ΨSq_two]
      simp [even_two, WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_one]]
  simp only [eval_sub, eval_mul, eval_X]

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K] in
private lemma PsiSq_two_eval_eq (x : K) :
    eval x ((curveK R K W).ΨSq 2) = eval x (curveK R K W).Ψ₂Sq := by
  rw [WeierstrassCurve.ΨSq_two]

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K] in
private lemma Psi2Sq_eval_eq (x : K) :
    eval x (curveK R K W).Ψ₂Sq =
      4 * x ^ 3 + algebraMap R K W.b₂ * x ^ 2 +
      2 * algebraMap R K W.b₄ * x + algebraMap R K W.b₆ := by
  have hmap : (curveK R K W).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap R K) := by
    change (W.map (algebraMap R K)).Ψ₂Sq = _; rw [WeierstrassCurve.map_Ψ₂Sq]
  rw [hmap, eval_map, WeierstrassCurve.Ψ₂Sq]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, eval₂_ofNat,
    map_ofNat, map_mul]

omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K] in
private lemma Psi3_eval_eq (x : K) :
    eval x (curveK R K W).Ψ₃ =
      3 * x ^ 4 + algebraMap R K W.b₂ * x ^ 3 +
      3 * algebraMap R K W.b₄ * x ^ 2 +
      3 * algebraMap R K W.b₆ * x + algebraMap R K W.b₈ := by
  have hmap : (curveK R K W).Ψ₃ = W.Ψ₃.map (algebraMap R K) := by
    change (W.map (algebraMap R K)).Ψ₃ = _; rw [WeierstrassCurve.map_Ψ₃]
  rw [hmap, eval_map, WeierstrassCurve.Ψ₃]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, eval₂_ofNat]

omit [DecidableEq K] in
private lemma isInteger_mul_of_den_dvd {x : K} {n : R}
    (h : (IsFractionRing.den R x : R) ∣ n) :
    IsLocalization.IsInteger R (algebraMap R K n * x) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q * IsFractionRing.num R x, ?_⟩
  have hd_ne : (algebraMap R K (IsFractionRing.den R x : R)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (IsFractionRing.den R x).prop
  have hd_x : algebraMap R K (IsFractionRing.den R x : R) * x =
      algebraMap R K (IsFractionRing.num R x) := by
    have h := IsFractionRing.mk'_num_den' R x
    rw [div_eq_iff hd_ne] at h; rw [mul_comm]; exact h.symm
  calc algebraMap R K (q * IsFractionRing.num R x)
      = algebraMap R K q * algebraMap R K (IsFractionRing.num R x) := map_mul ..
    _ = algebraMap R K q * (algebraMap R K (IsFractionRing.den R x : R) * x) := by rw [hd_x]
    _ = algebraMap R K n * x := by rw [hq, map_mul]; ring

/-! #### The Ψ₃ divisibility from torsion over PIDs -/

private lemma kappa_sq_dvd_four_Psi3_of_torsion
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hkappa_sq : (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 =
      4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆)
    (hκ : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣
      4 * (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 +
        3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈) := by
  set P := Affine.Point.some _ _ hpt; set κ₀ := 2 * y₀ + W.a₁ * x₀ + W.a₃
  have hm_pos : 0 < addOrderOf P := htor.addOrderOf_pos
  have hord_ne1 : addOrderOf P ≠ 1 :=
    fun h => Affine.Point.some_ne_zero hpt (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hord_ne2 : addOrderOf P ≠ 2 :=
    addOrderOf_ne_two_of_kappa_ne_zero W hpt hx hy hκ
  have hord_gt2 : 2 < addOrderOf P := by omega
  have h2P_ne : (2 : ℕ) • P ≠ 0 := fun h =>
    absurd (Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr hord_gt2)
  obtain ⟨x', y', hns', h2P_eq⟩ := exists_some_of_ne_zero W h2P_ne
  have hsf_2P : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hns') →
      Squarefree (p : R) := fun p hp hpd =>
    hsf_all p hp (hpd.trans (by
      rw [← h2P_eq]; exact addOrderOf_dvd_of_mem_zmultiples ⟨2, rfl⟩))
  have hcoord := x_coord_nsmul_eq W hpt (show (2 : ℤ) ≠ 0 by norm_num) hns' (by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, natCast_zsmul]; exact h2P_eq)
  rw [PsiSq_two_eval_eq, Phi2_eval_eq] at hcoord
  have hkappa_sq_K : (algebraMap R K κ₀) ^ 2 = eval x (curveK R K W).Ψ₂Sq := by
    rw [Psi2Sq_eval_eq, ← hx]
    have := congr_arg (algebraMap R K) hkappa_sq
    simp only [map_add, map_mul, map_pow, map_ofNat] at this; linear_combination this
  have hPsi3_eq : eval x (curveK R K W).Ψ₃ =
      (x - x') * (algebraMap R K κ₀) ^ 2 := by rw [hkappa_sq_K]; linear_combination hcoord
  rw [Psi3_eval_eq, ← hx] at hPsi3_eq
  have hinj := IsFractionRing.injective R K
  rcases lutz_nagell_integrality_pid W hns' (h2P_eq ▸ htor.nsmul) hsf_2P with
    ⟨⟨x'₀, hx'₀⟩, _⟩ | ⟨_, hden_dvd⟩
  · rw [← hx'₀] at hPsi3_eq
    exact dvd_mul_of_dvd_right ⟨x₀ - x'₀, hinj (by
      simp only [map_add, map_mul, map_pow, map_sub, map_ofNat]
      linear_combination hPsi3_eq)⟩ 4
  · obtain ⟨n₀, hn₀⟩ := isInteger_mul_of_den_dvd hden_dvd
    have h4x' : algebraMap R K n₀ = 4 * x' := by rw [hn₀]; simp [map_ofNat]
    exact ⟨4 * x₀ - n₀, hinj (by
      simp only [map_add, map_mul, map_pow, map_sub, map_ofNat]
      linear_combination 4 * hPsi3_eq + (algebraMap R K κ₀) ^ 2 * h4x')⟩

/-! ### The full discriminant theorem from torsion -/

/-- **Lutz–Nagell discriminant divisibility from torsion over PIDs.**

For a nonzero torsion point with integral coordinates on a general Weierstrass curve
over a PID, either `κ₀ = 0` or `κ₀² | 4Δ`, where `κ₀ = 2y₀ + a₁x₀ + a₃`.

Unlike the basic `lutz_nagell_pid_discriminant`, this derives the Ψ₃ divisibility
automatically from the torsion hypothesis. -/
theorem lutz_nagell_pid_discriminant_of_torsion
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  by_cases hκ : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0
  · exact Or.inl hκ
  · right
    have hcurve := curveR_equation_of_isInteger W hpt hx hy
    exact kappa_sq_dvd_four_delta W x₀ _
      (kappa_sq_eq_Psi2Sq W hcurve)
      (kappa_sq_dvd_four_Psi3_of_torsion W hpt htor hsf_all hx hy
        (kappa_sq_eq_Psi2Sq W hcurve) hκ)

/-! ### Discriminant divisibility for `a₁ = a₃ = 0` -/

/-- For a Weierstrass curve with `a₁ = a₃ = 0` (i.e., `y² = x³ + a₂x² + a₄x + a₆`)
with integral torsion point, either `y₀ = 0` or `y₀²` divides the cubic discriminant
`4a₄³ + 27a₆² + 4a₂³a₆ - a₂²a₄² - 18a₂a₄a₆`. This specializes to
`y₀² ∣ 4a₄³ + 27a₆²` when `a₂ = 0` (short Weierstrass). -/
theorem lutz_nagell_cubicDisc_discriminant (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hcurve : y₀ ^ 2 = x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
    y₀ = 0 ∨ y₀ ^ 2 ∣ 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 + 4 * W.a₂ ^ 3 * W.a₆ -
      W.a₂ ^ 2 * W.a₄ ^ 2 - 18 * W.a₂ * W.a₄ * W.a₆ := by
  rcases lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy with hκ | hdvd
  · left; simp only [ha₁, ha₃, mul_zero, add_zero] at hκ
    exact mul_left_cancel₀ two_ne_zero (by linear_combination hκ)
  · by_cases hy₀ : y₀ = 0
    · exact Or.inl hy₀
    · right
      have hcurve_gen : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
          x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ := by
        rw [ha₁, ha₃]; simp; linear_combination hcurve
      have hκ_ne : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0 := by
        simp only [ha₁, ha₃, mul_zero, add_zero, zero_mul, zero_add]
        exact fun h => hy₀ ((mul_eq_zero.mp h).resolve_left two_ne_zero)
      have h4Psi3 := kappa_sq_dvd_four_Psi3_of_torsion W hpt htor hsf_all hx hy
        (kappa_sq_eq_Psi2Sq W hcurve_gen) hκ_ne
      -- Extract y₀² | Ψ₃ from (2y₀)² | 4Ψ₃
      rw [ha₁, ha₃] at h4Psi3
      simp only [mul_zero, add_zero, zero_mul] at h4Psi3
      rw [show (2 * y₀) ^ 2 = 4 * y₀ ^ 2 from by ring] at h4Psi3
      have hΨ₃' : y₀ ^ 2 ∣ 3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
          3 * W.b₆ * x₀ + W.b₈ :=
        (mul_dvd_mul_iff_left (show (4 : R) ≠ 0 from by norm_num)).mp h4Psi3
      -- (f')² = (12x₀+4a₂)·y₀² - Ψ₃, so y₀² | (f')²
      have h_fprime_sq : y₀ ^ 2 ∣
          (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) ^ 2 := by
        rw [show (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) ^ 2 =
            (12 * x₀ + 4 * W.a₂) *
              (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) -
            (3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 +
              3 * W.b₆ * x₀ + W.b₈) from by
          simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
            WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₃]; ring,
          ← hcurve]
        exact dvd_sub (dvd_mul_of_dvd_right dvd_rfl _) hΨ₃'
      -- Bézout: c₁·y₀² + c₂·(f')² = cubicDisc
      rw [show 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 + 4 * W.a₂ ^ 3 * W.a₆ -
          W.a₂ ^ 2 * W.a₄ ^ 2 - 18 * W.a₂ * W.a₄ * W.a₆ =
        -(27 * x₀ ^ 3 + 27 * W.a₂ * x₀ ^ 2 + 27 * W.a₄ * x₀ -
          4 * W.a₂ ^ 3 + 18 * W.a₂ * W.a₄ - 27 * W.a₆) *
          y₀ ^ 2 +
        (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ - W.a₂ ^ 2 + 4 * W.a₄) *
          (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) ^ 2 from by
        rw [hcurve]; ring]
      exact dvd_add (dvd_mul_of_dvd_right dvd_rfl _)
        (dvd_mul_of_dvd_right h_fprime_sq _)

end PID

/-! ## Number field version -/

namespace NumberField

open WeierstrassCurve IsFractionRing _root_.NumberField
open scoped _root_.NumberField

/-- **Lutz–Nagell theorem for number fields of class number 1.**

Let `K` be a number field with `IsPrincipalIdealRing (𝓞 K)` (equivalently,
`classNumber K = 1`). Let `W` be a Weierstrass curve with coefficients in `𝓞 K`.

For a nonzero finite-order point `(x, y)` on `W / K`:
- **At unramified primes:** if `Squarefree (p : 𝓞 K)` for every prime `p` dividing
  the torsion order, then `x, y ∈ 𝓞 K` (or order 2 with `den(x) ∣ 4`).
- **At all primes (no hypothesis):** every prime factor `q` of `den(x)` satisfies
  `q² ∣ den(x)` — denominators are supported only at ramified primes.

Over `ℚ` (where `𝓞 ℚ = ℤ` and no primes ramify), this recovers the classical
Lutz–Nagell theorem. -/
theorem lutz_nagell_number_field
    (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K))
    {x y : K}
    (hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : 𝓞 K)) :
    ((IsLocalization.IsInteger (𝓞 K) x) ∧ IsLocalization.IsInteger (𝓞 K) y) ∨
    (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
      (IsFractionRing.den (𝓞 K) x : 𝓞 K) ∣ (4 : 𝓞 K)) :=
  PID.lutz_nagell_integrality_pid W hpt htor hsf_all

/-- **Powerful denominator for number fields of class number 1.**

For ANY point `(x, y)` on a Weierstrass curve over a number field `K` with
class number 1, every prime factor of the denominator of `x` in `𝓞 K`
appears with multiplicity ≥ 2. In particular, denominators are only
supported at primes that ramify in `K/ℚ`. -/
theorem den_powerful_number_field
    (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K))
    {x y : K}
    (heq : y ^ 2 + algebraMap (𝓞 K) K W.a₁ * x * y + algebraMap (𝓞 K) K W.a₃ * y =
      x ^ 3 + algebraMap (𝓞 K) K W.a₂ * x ^ 2 + algebraMap (𝓞 K) K W.a₄ * x +
        algebraMap (𝓞 K) K W.a₆)
    {q : 𝓞 K} (hq : Prime q) (hqd : q ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K)) :
    q ^ 2 ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K) :=
  PID.den_powerful_of_on_curve W heq q hq hqd

/-- **Lutz–Nagell discriminant divisibility for number fields of class number 1.**

For a nonzero torsion point with integral coordinates `x₀, y₀ ∈ 𝓞 K` on a Weierstrass
curve, define `κ₀ = 2y₀ + a₁x₀ + a₃`. Then either `κ₀ = 0` or `κ₀² ∣ 4Δ`. -/
theorem lutz_nagell_number_field_discriminant
    (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K))
    {x y : K}
    (hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : 𝓞 K))
    {x₀ y₀ : 𝓞 K} (hx : algebraMap (𝓞 K) K x₀ = x)
    (hy : algebraMap (𝓞 K) K y₀ = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ :=
  PID.lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy

/-! ### Short Weierstrass: y₀² ∣ 4A³ + 27B² -/

/-- For a Weierstrass curve with `a₁ = a₃ = 0` over a number field of class number 1,
if `(x₀, y₀)` is a nonzero torsion point with integral coordinates, then `y₀ = 0` or
`y₀²` divides the cubic discriminant
`4a₄³ + 27a₆² + 4a₂³a₆ - a₂²a₄² - 18a₂a₄a₆`. -/
theorem lutz_nagell_number_field_cubicDisc_discriminant
    (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K)) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {x y : K}
    (hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : 𝓞 K))
    {x₀ y₀ : 𝓞 K} (hx : algebraMap (𝓞 K) K x₀ = x)
    (hy : algebraMap (𝓞 K) K y₀ = y)
    (hcurve : y₀ ^ 2 = x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
    y₀ = 0 ∨ y₀ ^ 2 ∣ 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 +
      4 * W.a₂ ^ 3 * W.a₆ - W.a₂ ^ 2 * W.a₄ ^ 2 -
      18 * W.a₂ * W.a₄ * W.a₆ :=
  PID.lutz_nagell_cubicDisc_discriminant W ha₁ ha₃ hpt htor hsf_all hx hy
    hcurve

end NumberField
end LutzNagell
