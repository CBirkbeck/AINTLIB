import LutzNagell.LutzNagellTheorem.PIDCurve
import Mathlib.RingTheory.Localization.NumDen

/-!
# Denominators on general Weierstrass curves over UFDs

For a point on a general Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ R` (a UFD with fraction
field `K`),
if a prime `q ∈ R` divides `den_R(x)` exactly once (i.e., `q | den` but `q² ∤ den`),
we reach a contradiction.

## Main results

* `LutzNagell.PID.den_no_simple_prime_factor_of_on_curve`: if `(x, y)` is on the
  curve, `q` is prime, `q ∣ den(x)`, and `q² ∤ den(x)`, then `False`.
-/

namespace LutzNagell
namespace PID

open WeierstrassCurve IsFractionRing

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Helper: q ∤ (α³ + stuff·q) when q ∤ α -/

omit [IsDomain R] [UniqueFactorizationMonoid R] in
private lemma not_dvd_sum_of_not_dvd_cube {q α : R} (hq : Prime q) (hpa : ¬ q ∣ α)
    (c₂ c₄ c₆ : R) :
    ¬ q ∣ (α ^ 3 + c₂ * α ^ 2 * q + c₄ * α * q ^ 2 + c₆ * q ^ 3) := by
  intro hdvd
  have hq_dvd_tail : q ∣ c₂ * α ^ 2 * q + c₄ * α * q ^ 2 + c₆ * q ^ 3 :=
    ⟨c₂ * α ^ 2 + c₄ * α * q + c₆ * q ^ 2, by ring⟩
  have hq_dvd_cube : q ∣ α ^ 3 := by
    obtain ⟨k₁, hk₁⟩ := hdvd
    obtain ⟨k₂, hk₂⟩ := hq_dvd_tail
    exact ⟨k₁ - k₂, by linear_combination hk₁ - hk₂⟩
  exact hpa (hq.dvd_of_dvd_pow hq_dvd_cube)

/-! ### Clearing denominators -/

omit [UniqueFactorizationMonoid R] in
/-- The clearing-denominators equation for a point on a Weierstrass curve.

If `x = α/d` and `y = γ/e` lie on the curve, then after multiplying
by `d³ · e²` we obtain an equation in `R`. -/
private lemma clearing_denominators (W : WeierstrassCurve R)
    {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {α d γ e : R} (hd_ne : d ≠ 0) (he_ne : e ≠ 0)
    (hx : x = algebraMap R K α / algebraMap R K d)
    (hy : y = algebraMap R K γ / algebraMap R K e) :
    γ ^ 2 * d ^ 3 + W.a₁ * α * γ * d ^ 2 * e + W.a₃ * γ * d ^ 3 * e =
      e ^ 2 * (α ^ 3 + W.a₂ * α ^ 2 * d + W.a₄ * α * d ^ 2 + W.a₆ * d ^ 3) := by
  apply IsFractionRing.injective R K
  have hd' : (algebraMap R K d) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd_ne)
  have he' : (algebraMap R K e) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero he_ne)
  simp only [map_add, map_mul, map_pow]
  rw [hx, hy] at heq
  have key := congr_arg (· * (algebraMap R K d ^ 3 * algebraMap R K e ^ 2)) heq
  simp only [add_mul] at key
  have goal_eq : algebraMap R K d ^ 3 * algebraMap R K e ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hd') (pow_ne_zero 2 he')
  -- Both sides are polynomial expressions; after field_simp and ring they match
  field_simp at key ⊢
  linear_combination key

/-! ### The key denominator lemma for general Weierstrass curves over UFDs -/

/-- If `(x, y)` lies on a Weierstrass curve with coefficients in a UFD `R`, and `q` is a
prime of `R` that divides `den_R(x)` exactly once (i.e., `q ∣ den` but `q² ∤ den`), then
we reach a contradiction.

**Proof outline:** Write `x = α/d` and `y = γ/e` in reduced form.
1. Clear denominators to get an equation in `R`.
2. Since `q ∣ d` but `q² ∤ d`, write `d = q · u` with `q ∤ u`.
3. Mod `q`: `0 ≡ e²α³`, and since `gcd(α,d) = 1` gives `q ∤ α`, we get `q ∣ e`.
4. Write `e = q · e₁`, substitute, divide by `q²`. Mod `q`: `0 ≡ e₁²α³`, so `q ∣ e₁`.
5. Write `e₁ = q · e₂`, substitute, divide by `q`. Now `γ²u³ ≡ 0 (mod q)`,
   and since `q ∤ u` we get `q ∣ γ`.
6. But `q ∣ γ` and `q ∣ e` contradicts `IsRelPrime γ e`. -/
theorem den_no_simple_prime_factor_of_on_curve (W : WeierstrassCurve R)
    {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {q : R} (hq : Prime q)
    (hqd : q ∣ (IsFractionRing.den R x : R))
    (hq2 : ¬ q ^ 2 ∣ (IsFractionRing.den R x : R)) : False := by
  set α := IsFractionRing.num R x
  set d_sub := IsFractionRing.den R x
  set d := (d_sub : R)
  set γ := IsFractionRing.num R y
  set e_sub := IsFractionRing.den R y
  set e := (e_sub : R)
  have hcop_x : IsRelPrime α d := IsFractionRing.num_den_reduced R x
  have hcop_y : IsRelPrime γ e := IsFractionRing.num_den_reduced R y
  have hd_ne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d_sub.2
  have he_ne : e ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp e_sub.2
  have hq_not_dvd_α : ¬ q ∣ α := fun h => hq.not_unit (hcop_x h hqd)
  -- Factor d = q * u with q ∤ u
  obtain ⟨u, hu⟩ := hqd
  have hq_not_dvd_u : ¬ q ∣ u := by
    intro ⟨v, hv⟩; exact hq2 ⟨v, by rw [hu, hv]; ring⟩
  -- Clearing denominators equation in R
  have hx_eq : x = algebraMap R K α / algebraMap R K d := by
    rw [← IsFractionRing.mk'_num_den' R x]
  have hy_eq : y = algebraMap R K γ / algebraMap R K e := by
    rw [← IsFractionRing.mk'_num_den' R y]
  have hZ := clearing_denominators W heq hd_ne he_ne hx_eq hy_eq
  -- Set S = α³ + a₂α²d + a₄αd² + a₆d³ and rewrite using d = q·u
  set S := α ^ 3 + W.a₂ * α ^ 2 * d + W.a₄ * α * d ^ 2 + W.a₆ * d ^ 3 with hS_def
  have hS_rw : S = α ^ 3 + (W.a₂ * u) * α ^ 2 * q +
      (W.a₄ * u ^ 2) * α * q ^ 2 + (W.a₆ * u ^ 3) * q ^ 3 := by
    rw [hS_def, hu]; ring
  -- q ∤ S
  have hq_not_dvd_S : ¬ q ∣ S := by
    rw [hS_rw]; exact not_dvd_sum_of_not_dvd_cube hq hq_not_dvd_α _ _ _
  -- Round 1: q ∣ LHS, so q ∣ e²S, so q ∣ e
  have hlhs_dvd : q ∣ (γ ^ 2 * d ^ 3 + W.a₁ * α * γ * d ^ 2 * e +
      W.a₃ * γ * d ^ 3 * e) := by
    rw [hu]
    exact ⟨γ ^ 2 * (q ^ 2 * u ^ 3) + W.a₁ * α * γ * (q * u ^ 2) * e +
      W.a₃ * γ * (q ^ 2 * u ^ 3) * e, by ring⟩
  have hrhs_dvd : q ∣ e ^ 2 * S := hZ ▸ hlhs_dvd
  have hq_dvd_esq : q ∣ e ^ 2 := (hq.dvd_or_dvd hrhs_dvd).resolve_right hq_not_dvd_S
  have hq_dvd_e : q ∣ e := hq.dvd_of_dvd_pow hq_dvd_esq
  obtain ⟨e₁, he₁⟩ := hq_dvd_e
  -- Round 2: substitute d = q·u, e = q·e₁, divide by q², show q ∣ e₁
  -- After clearing and dividing by q²:
  -- q·(u³γ² + a₁αγu²e₁ + q·a₃γu³e₁) = e₁²·S
  have hZ2 : q * (γ ^ 2 * u ^ 3 + W.a₁ * α * γ * u ^ 2 * e₁ +
      W.a₃ * γ * q * u ^ 3 * e₁) = e₁ ^ 2 * S := by
    have hq2_ne : q ^ 2 ≠ 0 := pow_ne_zero 2 hq.ne_zero
    rw [hu, he₁] at hZ
    apply mul_left_cancel₀ hq2_ne
    linear_combination hZ
  have hq_dvd_e1sq_S : q ∣ e₁ ^ 2 * S :=
    ⟨γ ^ 2 * u ^ 3 + W.a₁ * α * γ * u ^ 2 * e₁ +
      W.a₃ * γ * q * u ^ 3 * e₁, hZ2.symm⟩
  have hq_dvd_e₁ : q ∣ e₁ :=
    hq.dvd_of_dvd_pow ((hq.dvd_or_dvd hq_dvd_e1sq_S).resolve_right hq_not_dvd_S)
  obtain ⟨e₂, he₂⟩ := hq_dvd_e₁
  -- Round 3: substitute e₁ = q·e₂, divide by q, derive q ∣ γ
  -- After dividing by q: u³γ² + q·a₁αγu²e₂ + q²·a₃γu³e₂ = q·e₂²·S
  have hZ3 : γ ^ 2 * u ^ 3 + W.a₁ * α * γ * q * u ^ 2 * e₂ +
      W.a₃ * γ * q ^ 2 * u ^ 3 * e₂ =
    q * e₂ ^ 2 * S := by
    rw [he₂] at hZ2
    apply mul_left_cancel₀ hq.ne_zero
    linear_combination hZ2
  have hq_dvd_γsq : q ∣ γ ^ 2 := by
    have hq_dvd_mid : q ∣ W.a₁ * α * γ * q * u ^ 2 * e₂ +
        W.a₃ * γ * q ^ 2 * u ^ 3 * e₂ :=
      ⟨W.a₁ * α * γ * u ^ 2 * e₂ + W.a₃ * γ * q * u ^ 3 * e₂, by ring⟩
    have hq_dvd_rhs : q ∣ q * e₂ ^ 2 * S :=
      dvd_mul_of_dvd_left (dvd_mul_right q _) _
    obtain ⟨k₁, hk₁⟩ := hq_dvd_rhs
    obtain ⟨k₂, hk₂⟩ := hq_dvd_mid
    have hq_dvd_γu : q ∣ γ ^ 2 * u ^ 3 :=
      ⟨k₁ - k₂, by linear_combination hZ3 - hk₂ + hk₁⟩
    exact (hq.dvd_or_dvd hq_dvd_γu).resolve_right
      (fun h => hq_not_dvd_u (hq.dvd_of_dvd_pow h))
  have hq_dvd_γ : q ∣ γ := hq.dvd_of_dvd_pow hq_dvd_γsq
  -- Contradiction: q ∣ γ and q ∣ e violates IsRelPrime γ e
  exact hq.not_unit (hcop_y hq_dvd_γ ⟨e₁, he₁⟩)

/-- Corollary: if the denominator of `x` is prime, we get a contradiction.

This is a special case of `den_no_simple_prime_factor_of_on_curve` where
`q = den(x)` — a prime element trivially has `q² ∤ q`. -/
theorem den_not_prime_of_on_curve (W : WeierstrassCurve R)
    {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    (hp : Prime (IsFractionRing.den R x : R)) : False :=
  den_no_simple_prime_factor_of_on_curve W heq hp dvd_rfl (fun h => by
    obtain ⟨c, hc⟩ := h
    rw [sq, mul_assoc] at hc
    have h1 : (1 : R) = (IsFractionRing.den R x : R) * c :=
      mul_left_cancel₀ hp.ne_zero (by rw [mul_one]; exact hc)
    exact hp.not_unit (isUnit_of_dvd_one ⟨c, h1⟩))

end PID
end LutzNagell
