import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# B-C1.3 — `p`-adic valuation exactness micro-facts

This is the foundation layer for the `p`-adic `L`-function development behind
Washington **Proposition 8.12** (FLT for `p = 37`, Case II / Assumption II).
It collects the purely arithmetic `p`-adic valuation facts that the Prop 8.12
assembly (`B-C1.4`) needs.  They are all proved unconditionally over the
concrete `p`-adic numbers `ℚ_[p]` / `ℤ_[p]` — this concreteness is deliberate:
it side-steps the `adicCompletionIntegers` ring-transport whnf wall documented
for the abstract `samePrimeFiniteLog` route.

## Main results

* `PadicInt.valuation_sub_eq_of_lt`: the **exactness lemma**
  `x ≡ y mod p^N ∧ v_p(y) < N ⟹ v_p(x) = v_p(y)` over `ℤ_[p]`.
  This is the key "the congruence is sharp enough" tool used to read off the
  valuation of `log_p E_i` from the mod-`p^N` congruence in Prop 8.12.
* `Padic.valuation_sub_eq_of_lt`: the same exactness over `ℚ_[p]`.
* `PadicInt.valuation_eq_zero_of_isUnit` / `…_of_not_dvd`: a `p`-adic integer
  that is a unit (equivalently not divisible by `p`) has valuation `0`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §5.4, §8.4.
-/

namespace BernoulliRegular.FLT37.PadicL

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `ℚ_[p]`-valuation is invariant under negation. -/
theorem Padic.valuation_neg (x : ℚ_[p]) : (-x).valuation = x.valuation := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  have hp_ne_one : (p : ℝ) ≠ 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : ℝ) < p := mod_cast NeZero.pos _
  have h_norm : ‖-x‖ = ‖x‖ := norm_neg x
  rwa [_root_.Padic.norm_eq_zpow_neg_valuation hnx, _root_.Padic.norm_eq_zpow_neg_valuation hx,
    zpow_right_inj₀ hp_pos hp_ne_one, neg_inj] at h_norm

/-- The `ℤ_[p]`-valuation is invariant under negation. -/
theorem PadicInt.valuation_neg (x : ℤ_[p]) : (-x).valuation = x.valuation := by
  unfold _root_.PadicInt.valuation
  rw [_root_.PadicInt.coe_neg, Padic.valuation_neg]

/-- A `p`-adic integer with valuation `0` is a unit. -/
theorem PadicInt.isUnit_of_valuation_eq_zero {x : ℤ_[p]} (hx : x ≠ 0)
    (hv : x.valuation = 0) : IsUnit x := by
  rw [_root_.PadicInt.isUnit_iff, _root_.PadicInt.norm_eq_zpow_neg_valuation hx, hv]
  simp

/-- A `p`-adic integer that is **not** divisible by `p` has valuation `0`. -/
theorem PadicInt.valuation_eq_zero_of_not_dvd {x : ℤ_[p]} (hx : ¬ (p : ℤ_[p]) ∣ x) :
    x.valuation = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (dvd_zero _)
  by_contra hne
  have h1 : 1 ≤ x.valuation := Nat.one_le_iff_ne_zero.mpr hne
  have hmem : x ∈ (Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p]) :=
    (_root_.PadicInt.mem_span_pow_iff_le_valuation x hx0 1).mpr h1
  rw [pow_one, Ideal.mem_span_singleton] at hmem
  exact hx hmem

/-- A `p`-adic **unit** has valuation `0`. -/
theorem PadicInt.valuation_eq_zero_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) :
    x.valuation = 0 := by
  apply PadicInt.valuation_eq_zero_of_not_dvd
  intro hdvd
  rcases hdvd with ⟨c, rfl⟩
  rw [_root_.PadicInt.isUnit_iff, norm_mul, _root_.PadicInt.norm_p] at hx
  have hcle : ‖c‖ ≤ 1 := _root_.PadicInt.norm_le_one c
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr hppos
  have hmul : (p : ℝ)⁻¹ * ‖c‖ ≤ (p : ℝ)⁻¹ * 1 :=
    mul_le_mul_of_nonneg_left hcle hp_pos.le
  rw [mul_one, hx] at hmul
  have hp1 : (1 : ℝ) < (p : ℝ) := mod_cast hp.out.one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

/-- **The exactness lemma over `ℤ_[p]`** (B-C1.3): if `x` and `y` are congruent
modulo `p^N` and `v_p(y) < N`, then `v_p(x) = v_p(y)`.

This is the sharpness criterion used in the Prop 8.12 assembly: a congruence
`log_p E_i^{(N)} ≡ (explicit) mod p^N` with the explicit side of valuation `< N`
pins down the valuation of `log_p E_i^{(N)}` exactly. -/
theorem PadicInt.valuation_sub_eq_of_lt {x y : ℤ_[p]} {N : ℕ} (hy0 : y ≠ 0)
    (hcong : x - y ∈ (Ideal.span {(p : ℤ_[p]) ^ N} : Ideal ℤ_[p]))
    (hy : y.valuation < N) : x.valuation = y.valuation := by
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hdiff : N ≤ (x - y).valuation :=
    (_root_.PadicInt.mem_span_pow_iff_le_valuation (x - y) hxy0 N).mp hcong
  have hgt : y.valuation < (x - y).valuation := lt_of_lt_of_le hy hdiff
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [zero_sub, PadicInt.valuation_neg] at hgt
    exact absurd hgt (lt_irrefl _)
  have hsum : y + (x - y) = x := by ring
  have hle1 : y.valuation ≤ x.valuation := by
    have := _root_.PadicInt.le_valuation_add (x := y) (y := x - y) (by rw [hsum]; exact hxne)
    rw [hsum, min_eq_left hgt.le] at this
    exact this
  have hle2 : x.valuation ≤ y.valuation := by
    by_contra hlt
    rw [not_le] at hlt
    have hsum2 : x + (-(x - y)) = y := by ring
    have hne2 : x + (-(x - y)) ≠ 0 := by rw [hsum2]; exact hy0
    have := _root_.PadicInt.le_valuation_add (x := x) (y := -(x - y)) hne2
    rw [hsum2, PadicInt.valuation_neg] at this
    have hmin : min x.valuation (x - y).valuation = x.valuation ∨
        min x.valuation (x - y).valuation = (x - y).valuation := min_choice _ _
    rcases hmin with h | h
    · rw [h] at this; omega
    · rw [h] at this; exact absurd (lt_of_lt_of_le hgt this) (lt_irrefl _)
  omega

/-- **The exactness lemma over `ℚ_[p]`** (B-C1.3): if `x - y` has `p`-adic
valuation `≥ N` and `v_p(y) < N`, then `v_p(x) = v_p(y)`. -/
theorem Padic.valuation_sub_eq_of_lt {x y : ℚ_[p]} {N : ℤ} (hy0 : y ≠ 0)
    (hcong : N ≤ (x - y).valuation) (hy : y.valuation < N) :
    x.valuation = y.valuation := by
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hgt : y.valuation < (x - y).valuation := lt_of_lt_of_le hy hcong
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [zero_sub, Padic.valuation_neg] at hgt
    exact absurd hgt (lt_irrefl _)
  have hsum : y + (x - y) = x := by ring
  have hle1 : y.valuation ≤ x.valuation := by
    have := _root_.Padic.le_valuation_add (x := y) (y := x - y) (by rw [hsum]; exact hxne)
    rw [hsum, min_eq_left hgt.le] at this
    exact this
  have hle2 : x.valuation ≤ y.valuation := by
    by_contra hlt
    rw [not_le] at hlt
    have hsum2 : x + (-(x - y)) = y := by ring
    have hne2 : x + (-(x - y)) ≠ 0 := by rw [hsum2]; exact hy0
    have := _root_.Padic.le_valuation_add (x := x) (y := -(x - y)) hne2
    rw [hsum2, Padic.valuation_neg] at this
    have hmin : min x.valuation (x - y).valuation = x.valuation ∨
        min x.valuation (x - y).valuation = (x - y).valuation := min_choice _ _
    rcases hmin with h | h
    · rw [h] at this; omega
    · rw [h] at this; omega
  omega

end BernoulliRegular.FLT37.PadicL
