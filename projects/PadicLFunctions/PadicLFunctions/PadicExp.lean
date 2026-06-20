/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coefficients
import PadicLFunctions.Interpolation.Branches
import Mathlib.RingTheory.PowerSeries.Log

/-!
# The p-adic exponential and logarithm (RJW Lem 5.14)

`exp(x) = ∑ x^n/n!` converges on the open ball `‖x‖ < p^{−1/(p−1)}` of a
nonarchimedean complete normed `ℚ_[p]`-algebra field (Legendre:
`v_p(n!) = (n − s_p(n))/(p−1)`), and is an isometry there; for odd `p` the
ball contains `pℤ_p`. The logarithm `log(1+y) = ∑ (−1)^{n+1} y^n/n` converges
for `‖y‖ < 1` and inverts `exp` on the matched balls. This realises RJW
Lemma 5.14 (TeX 1892–1897, citing Cassels §12; cross-reference Washington,
*Introduction to Cyclotomic Fields* §5.1) **as stated**: for `s ∈ ℤ_p` and
`x ∈ 1 + pℤ_p`, `x^s := exp(s·log x)` — and this agrees with the character
construction `PadicInt.onePAdicPow` by uniqueness of continuous characters.

Decomposition: `.mathlib-quality/decomposition.md` §5, cluster R5.E
(E1–E5; user-requested at board approval 2026-06-10).
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- An ultrametric normed field is a nonarchimedean (topological) ring — the
ring upgrade of mathlib's `IsUltrametricDist.nonarchimedeanAddGroup`
(MATHLIB-PR candidate). -/
instance : NonarchimedeanRing L where
  toIsTopologicalRing := inferInstance
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

omit [NormedAlgebra ℚ_[p] L] in
/-- E1: in a complete ultrametric normed field, a family is summable iff it
tends to `0` along the cofinite filter. -/
theorem summable_iff_tendsto_cofinite_zero {ι : Type*} (f : ι → L) :
    Summable f ↔ Tendsto f Filter.cofinite (𝓝 0) :=
  NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f

/-- E2: the norm of `n!` in `ℚ_[p]`, via Legendre's formula
`v_p(n!) ≤ (n−1)/(p−1)` — stated rpow-free as
`p^{-(n−1)} ≤ ‖n!‖^{p−1}`. -/
theorem norm_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    (p : ℝ) ^ (-((n : ℤ) - 1)) ≤ ‖(n.factorial : ℚ_[p])‖ ^ (p - 1) := by
  have hf0 : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [Padic.norm_eq_zpow_neg_valuation hf0, Padic.valuation_natCast,
    ← zpow_natCast _ (p - 1), ← zpow_mul]
  refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) ?_
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : n ≠ 0)
  have hcast : ((p - 1 : ℕ) : ℤ) * (padicValNat p n.factorial : ℤ) < (n : ℤ) := by
    exact_mod_cast hlt
  linarith [hcast]

/-- Membership in the open convergence ball `‖x‖ < p^{−1/(p−1)}` of the
`p`-adic exponential, stated rpow-free: `‖x‖^{p−1} < p⁻¹`. -/
def InExpBall (p : ℕ) {L : Type*} [NormedField L] (x : L) : Prop :=
  ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹

/-- The inverted Legendre bound: `‖n!‖^{-(p−1)} ≤ p^{n−1}` for `n ≥ 1`. -/
theorem norm_factorial_inv_pow_le {n : ℕ} (hn : 1 ≤ n) :
    (‖(n.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1) := by
  rw [show ((p : ℝ)) ^ (n - 1) = (((p : ℝ)) ^ (-((n : ℤ) - 1)))⁻¹ by
    rw [← zpow_neg, neg_neg, show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) by
      omega, zpow_natCast]]
  exact inv_anti₀ (zpow_pos (by exact_mod_cast hp.out.pos) _)
    (norm_factorial_le p hn)

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The exponential terms decay geometrically at the `(p−1)`-th power level:
`‖(n!)⁻¹•x^n‖^{p−1} ≤ ‖x‖^{p−1}·(p‖x‖^{p−1})^{n−1}` for `n ≥ 1` (Legendre
through `norm_factorial_le`; rpow-free). -/
theorem norm_factorial_inv_smul_pow_le (x : L) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n.factorial : ℚ_[p])⁻¹ • x ^ n‖ ^ (p - 1)
      ≤ ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ (n - 1) := by
  rw [norm_smul, norm_inv, norm_pow, mul_pow, inv_pow]
  have hfac := norm_factorial_inv_pow_le p hn
  calc (‖(n.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ * (‖x‖ ^ n) ^ (p - 1)
      ≤ (p : ℝ) ^ (n - 1) * (‖x‖ ^ n) ^ (p - 1) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ (n - 1) := by
        rw [mul_pow, ← pow_mul, ← pow_mul,
          show n * (p - 1) = (p - 1) + (n - 1) * (p - 1) by
            cases n with
            | zero => omega
            | succ m => rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.add_comm],
          pow_add, pow_mul]
        ring

/-- On the open ball, the exponential terms are summable (E1 + the geometric
bound). -/
theorem summable_padicExp_terms {x : L} (hx : InExpBall p x) :
    Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • x ^ n := by
  rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    tendsto_zero_iff_norm_tendsto_zero]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hT0 : 0 ≤ (p : ℝ) * ‖x‖ ^ (p - 1) := by positivity
  have hT1 : (p : ℝ) * ‖x‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖x‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hx hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpow : Tendsto (fun n : ℕ => ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hT0 hT1).const_mul
      (‖x‖ ^ (p - 1))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε1 : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpow ((min ε 1) ^ (p - 1))
    (pow_pos hε1 _)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hsmall := hN (n - 1) (by omega)
  rw [Real.dist_eq, sub_zero] at hsmall ⊢
  rw [abs_of_nonneg (by positivity)] at hsmall ⊢
  have hlt : ‖(n.factorial : ℚ_[p])⁻¹ • x ^ n‖ ^ (p - 1) < (min ε 1) ^ (p - 1) :=
    lt_of_le_of_lt (norm_factorial_inv_smul_pow_le p x (by omega)) hsmall
  exact lt_of_lt_of_le
    (lt_of_pow_lt_pow_left₀ _ hε1.le hlt) (min_le_left _ _)

/-- E3: the `p`-adic exponential, defined as a junk-total function (the series
`∑ x^n/n!`, meaningful on `‖x‖ < expRadius p`). -/
noncomputable def padicExp (x : L) : L := ∑' n : ℕ, (n.factorial : ℚ_[p])⁻¹ • x ^ n

omit [IsUltrametricDist L] [CompleteSpace L] in
@[simp] theorem padicExp_zero : padicExp p (0 : L) = 1 := by
  rw [padicExp, tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp

omit [CompleteSpace L] in
/-- The tail terms of the difference series are strictly dominated by the
linear term: `‖(m!)⁻¹•(x^m − y^m)‖ < ‖x − y‖` for `m ≥ 2` on the open ball
(strictness needs the OPEN ball; decomposition E3 attack [3]). -/
theorem norm_factorial_inv_smul_pow_sub_lt {x y : L} (hx : InExpBall p x)
    (hy : InExpBall p y) (hxy : x ≠ y) {m : ℕ} (hm : 2 ≤ m) :
    ‖(m.factorial : ℚ_[p])⁻¹ • x ^ m - (m.factorial : ℚ_[p])⁻¹ • y ^ m‖
      < ‖x - y‖ := by
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hd0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  set r : ℝ := max ‖x‖ ‖y‖ with hr
  have hr0 : 0 ≤ r := le_trans (norm_nonneg x) (le_max_left _ _)
  have hrp : r ^ (p - 1) < (p : ℝ)⁻¹ := by
    rcases max_cases ‖x‖ ‖y‖ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [hr, h1]
    exacts [hx, hy]
  have hT1 : (p : ℝ) * r ^ (p - 1) < 1 :=
    calc (p : ℝ) * r ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hrp hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hgeom : ‖x ^ m - y ^ m‖ ≤ ‖x - y‖ * r ^ (m - 1) := by
    rw [← geom_sum₂_mul, mul_comm]
    rw [show ‖x - y‖ * r ^ (m - 1)
        = ‖x - y‖ * ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖
          + ‖x - y‖ * (r ^ (m - 1)
            - ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖) by ring]
    refine le_add_of_le_of_nonneg (norm_mul_le _ _) ?_
    refine mul_nonneg hd0.le (sub_nonneg.mpr ?_)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖x‖ ^ i * ‖y‖ ^ (m - 1 - i)
        ≤ r ^ i * r ^ (m - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
            (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _)
            (by positivity) (by positivity)
      _ = r ^ (m - 1) := by
          rw [← pow_add]
          congr 1
          have := Finset.mem_range.mp hi
          omega
  have hpow : ‖(m.factorial : ℚ_[p])⁻¹ • x ^ m
        - (m.factorial : ℚ_[p])⁻¹ • y ^ m‖ ^ (p - 1)
      < ‖x - y‖ ^ (p - 1) := by
    rw [← smul_sub, norm_smul, norm_inv, mul_pow, inv_pow]
    calc (‖(m.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ * ‖x ^ m - y ^ m‖ ^ (p - 1)
        ≤ (p : ℝ) ^ (m - 1) * (‖x - y‖ * r ^ (m - 1)) ^ (p - 1) := by
          refine mul_le_mul (norm_factorial_inv_pow_le p (by omega)) ?_
            (by positivity) (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg _) hgeom _
      _ = ‖x - y‖ ^ (p - 1) * ((p : ℝ) * r ^ (p - 1)) ^ (m - 1) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (m - 1) (p - 1),
            pow_mul]
          ring
      _ ≤ ‖x - y‖ ^ (p - 1) * ((p : ℝ) * r ^ (p - 1)) ^ 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_of_le_one (by positivity) hT1.le (by omega)
      _ < ‖x - y‖ ^ (p - 1) := by
          rw [pow_one]
          exact mul_lt_of_lt_one_right (by positivity) hT1
  exact lt_of_pow_lt_pow_left₀ _ hd0.le hpow

/-- E3: `exp` is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}` — every
term beyond the linear one is strictly smaller (strictness needs the OPEN
ball; decomposition E3 attack [3]). -/
theorem norm_padicExp_sub_padicExp {x y : L} (hx : InExpBall p x)
    (hy : InExpBall p y) :
    ‖padicExp p x - padicExp p y‖ = ‖x - y‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hd0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsx := summable_padicExp_terms p hx
  have hsy := summable_padicExp_terms p hy
  have hsd : Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • x ^ n
      - (n.factorial : ℚ_[p])⁻¹ • y ^ n := hsx.sub hsy
  have hdiff : padicExp p x - padicExp p y
      = ∑' n : ℕ, ((n.factorial : ℚ_[p])⁻¹ • x ^ n
          - (n.factorial : ℚ_[p])⁻¹ • y ^ n) := (hsx.tsum_sub hsy).symm
  rw [hdiff, hsd.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).mpr hsd).tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    sub_self, zero_add, Nat.factorial_one, pow_one]
  have htail : ‖∑' n : ℕ, ((((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹
        • x ^ (n + 1 + 1)
      - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1))‖
      < ‖x - y‖ := by
    have hterm : ∀ n : ℕ, ‖(((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹
          • x ^ (n + 1 + 1)
        - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1)‖
        < ‖x - y‖ := fun n =>
      norm_factorial_inv_smul_pow_sub_lt p hx hy hxy (by omega)
    have htend : Tendsto (fun n : ℕ => ‖(((n + 1 + 1 : ℕ).factorial
          : ℚ_[p]))⁻¹ • x ^ (n + 1 + 1)
        - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1)‖)
        atTop (𝓝 0) := by
      have h2 : Summable fun n : ℕ => (((n + 1 + 1 : ℕ).factorial
            : ℚ_[p]))⁻¹ • x ^ (n + 1 + 1)
          - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1) :=
        (summable_nat_add_iff 1).mpr ((summable_nat_add_iff 1).mpr hsd)
      simpa using h2.tendsto_atTop_zero.norm
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually_lt_const (half_pos hd0))
    set C : ℝ := max ((Finset.range (N + 1)).sup' (by simp)
        fun n => ‖(((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • x ^ (n + 1 + 1)
          - (((n + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (n + 1 + 1)‖)
      (‖x - y‖ / 2) with hC
    have hCd : C < ‖x - y‖ := by
      rw [hC]
      refine max_lt ((Finset.sup'_lt_iff _).mpr fun n _ => hterm n) ?_
      linarith
    refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le
      fun n => ?_) hCd
    rcases le_or_gt n N with hn | hn
    · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      exact le_trans (Finset.le_sup'
        (fun k => ‖(((k + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • x ^ (k + 1 + 1)
          - (((k + 1 + 1 : ℕ).factorial : ℚ_[p]))⁻¹ • y ^ (k + 1 + 1)‖) hmem)
        (le_max_left _ _)
    · exact le_trans (hN n hn.le).le (le_max_right _ _)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm htail.ne']
  exact max_eq_left htail.le

theorem norm_padicExp_sub_one {x : L} (hx : InExpBall p x) :
    ‖padicExp p x - 1‖ = ‖x‖ := by
  have h0 : InExpBall p (0 : L) := by
    rw [InExpBall, norm_zero, zero_pow (by have := hp.out.one_lt; omega)]
    exact inv_pos.mpr (by exact_mod_cast hp.out.pos)
  simpa using norm_padicExp_sub_padicExp p hx h0

/-- E3: the functional equation `exp(x+y) = exp(x)·exp(y)` on the ball
(double-series rearrangement; unconditional/nonarchimedean summability of the
product family via `HasSum.mul_of_nonarchimedean` + the antidiagonal Cauchy
formula — NOT norm-summable Cauchy products). -/
theorem padicExp_add {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) :
    padicExp p (x + y) = padicExp p x * padicExp p y := by
  have hsx := summable_padicExp_terms p hx
  have hsy := summable_padicExp_terms p hy
  have hprod : Summable fun ij : ℕ × ℕ =>
      ((ij.1.factorial : ℚ_[p])⁻¹ • x ^ ij.1)
        * ((ij.2.factorial : ℚ_[p])⁻¹ • y ^ ij.2) :=
    (hsx.hasSum.mul_of_nonarchimedean hsy.hasSum).summable
  rw [padicExp, padicExp, padicExp,
    hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hprod]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => ((k.factorial : ℚ_[p])⁻¹ • x ^ k)
        * ((l.factorial : ℚ_[p])⁻¹ • y ^ l)),
    add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hchoose : ((n.factorial : ℚ_[p]))⁻¹ * (n.choose k : ℚ_[p])
      = (k.factorial : ℚ_[p])⁻¹ * ((n - k).factorial : ℚ_[p])⁻¹ := by
    have hfk : (k.factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hfnk : ((n - k).factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
    have hfn : (n.factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hid : ((n.choose k : ℚ_[p])) * (k.factorial : ℚ_[p])
        * ((n - k).factorial : ℚ_[p]) = (n.factorial : ℚ_[p]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℚ_[p])
        (Nat.choose_mul_factorial_mul_factorial hkn)
    field_simp
    linear_combination hid
  rw [smul_mul_smul_comm,
    show (x ^ k * y ^ (n - k) * (n.choose k : L))
      = (n.choose k : ℚ_[p]) • (x ^ k * y ^ (n - k)) by
      rw [Algebra.smul_def, map_natCast, mul_comm],
    smul_smul, hchoose]

/-- `(p−1)·v_p(n+1) ≤ n`: the valuation growth of the logarithm denominators
(`p^v ∣ n+1` and Bernoulli `1 + v(p−1) ≤ p^v`). -/
theorem sub_one_mul_padicValNat_succ_le (n : ℕ) :
    (p - 1) * padicValNat p (n + 1) ≤ n := by
  set v : ℕ := padicValNat p (n + 1)
  have hle : p ^ v ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) pow_padicValNat_dvd
  have hbern : 1 + (v : ℤ) * ((p : ℤ) - 1) ≤ (p : ℤ) ^ v := by
    have h2 : (-2 : ℤ) ≤ (p : ℤ) - 1 := by have := hp.out.pos; omega
    simpa using one_add_mul_le_pow h2 v
  have hgoal : ((p - 1 : ℕ) : ℤ) * (v : ℤ) ≤ (n : ℤ) := by
    have hps : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by have := hp.out.one_le; omega
    have hle' : ((p : ℤ)) ^ v ≤ (n : ℤ) + 1 := by exact_mod_cast hle
    rw [hps]
    linarith [hbern, hle']
  exact_mod_cast hgoal

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The logarithm terms decay geometrically at the `(p−1)`-th power level:
`‖(−1)^n·(n+1)⁻¹•y^{n+1}‖^{p−1} ≤ ‖y‖^{p−1}·(p‖y‖^{p−1})^n`. -/
theorem norm_succ_inv_smul_pow_le (y : L) (n : ℕ) :
    ‖(-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1))‖ ^ (p - 1)
      ≤ ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ n := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_smul,
    norm_inv, norm_pow, mul_pow, inv_pow]
  have hval : ‖((n : ℚ_[p]) + 1)‖ = (p : ℝ) ^ (-(padicValNat p (n + 1) : ℤ)) := by
    rw [show ((n : ℚ_[p]) + 1) = ((n + 1 : ℕ) : ℚ_[p]) by push_cast; ring,
      Padic.norm_eq_zpow_neg_valuation
        (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)),
      Padic.valuation_natCast]
  have hfac : (‖((n : ℚ_[p]) + 1)‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ n := by
    rw [hval, ← zpow_natCast _ (p - 1), ← zpow_mul, ← zpow_neg,
      ← zpow_natCast (p : ℝ) n]
    refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) ?_
    push_cast
    nlinarith [sub_one_mul_padicValNat_succ_le p n]
  calc (‖((n : ℚ_[p]) + 1)‖ ^ (p - 1))⁻¹ * (‖y‖ ^ (n + 1)) ^ (p - 1)
      ≤ (p : ℝ) ^ n * (‖y‖ ^ (n + 1)) ^ (p - 1) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ n := by
        rw [mul_pow, ← pow_mul, ← pow_mul,
          show (n + 1) * (p - 1) = (p - 1) + n * (p - 1) by
            rw [Nat.succ_mul, Nat.add_comm],
          pow_add, pow_mul]
        ring

/-- On the open exponential ball, the logarithm terms are summable. -/
theorem summable_padicLog_terms {y : L} (hy : InExpBall p y) :
    Summable fun n : ℕ => (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1)) := by
  rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    tendsto_zero_iff_norm_tendsto_zero]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hT0 : 0 ≤ (p : ℝ) * ‖y‖ ^ (p - 1) := by positivity
  have hT1 : (p : ℝ) * ‖y‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖y‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hy hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpow : Tendsto (fun n : ℕ => ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hT0 hT1).const_mul
      (‖y‖ ^ (p - 1))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε1 : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpow ((min ε 1) ^ (p - 1))
    (pow_pos hε1 _)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero] at hsmall ⊢
  rw [abs_of_nonneg (by positivity)] at hsmall ⊢
  have hlt : ‖(-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1))‖ ^ (p - 1)
      < (min ε 1) ^ (p - 1) :=
    lt_of_le_of_lt (norm_succ_inv_smul_pow_le p y n) hsmall
  exact lt_of_lt_of_le
    (lt_of_pow_lt_pow_left₀ _ hε1.le hlt) (min_le_left _ _)

/-- E4: the `p`-adic logarithm `log(x) = ∑ (−1)^{n+1}(x−1)^n/n`, junk-total
(meaningful for `‖x − 1‖ < 1`). -/
noncomputable def padicLog (x : L) : L :=
  ∑' n : ℕ, (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1))

omit [IsUltrametricDist L] [CompleteSpace L] in
@[simp] theorem padicLog_one : padicLog p (1 : L) = 0 := by
  rw [padicLog]
  simp

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The tail terms of the logarithm are strictly dominated by the linear
term on the open exponential ball: `‖(−1)^m(m+1)⁻¹•y^{m+1}‖ < ‖y‖` for
`m ≥ 1`. -/
theorem norm_succ_inv_smul_pow_lt {y : L} (hy : InExpBall p y) (hy0 : y ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖(-1 : L) ^ m * (((m : ℚ_[p]) + 1)⁻¹ • y ^ (m + 1))‖ < ‖y‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hd0 : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hT1 : (p : ℝ) * ‖y‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖y‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hy hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpow : ‖(-1 : L) ^ m * (((m : ℚ_[p]) + 1)⁻¹ • y ^ (m + 1))‖ ^ (p - 1)
      < ‖y‖ ^ (p - 1) := by
    refine lt_of_le_of_lt (norm_succ_inv_smul_pow_le p y m) ?_
    calc ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ m
        ≤ ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_of_le_one (by positivity) hT1.le hm
      _ < ‖y‖ ^ (p - 1) := by
          rw [pow_one]
          exact mul_lt_of_lt_one_right (by positivity) hT1
  exact lt_of_pow_lt_pow_left₀ _ hd0.le hpow

theorem norm_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    ‖padicLog p x‖ = ‖x - 1‖ := by
  rcases eq_or_ne x 1 with rfl | hx1
  · simp
  have hy0 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hd0 : 0 < ‖x - 1‖ := norm_pos_iff.mpr hy0
  have hsum := summable_padicLog_terms p hx
  rw [padicLog, hsum.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, inv_one, one_smul,
    pow_one]
  have htail : ‖∑' n : ℕ, (-1 : L) ^ (n + 1)
      * ((((n + 1 : ℕ) : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1 + 1))‖ < ‖x - 1‖ := by
    have hterm : ∀ n : ℕ, ‖(-1 : L) ^ (n + 1)
        * ((((n + 1 : ℕ) : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1 + 1))‖ < ‖x - 1‖ :=
      fun n => norm_succ_inv_smul_pow_lt p hx hy0 (by omega)
    have htend : Tendsto (fun n : ℕ => ‖(-1 : L) ^ (n + 1)
        * ((((n + 1 : ℕ) : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1 + 1))‖)
        atTop (𝓝 0) := by
      have h2 : Summable fun n : ℕ => (-1 : L) ^ (n + 1)
          * ((((n + 1 : ℕ) : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1 + 1)) :=
        (summable_nat_add_iff 1).mpr hsum
      simpa using h2.tendsto_atTop_zero.norm
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (htend.eventually_lt_const (half_pos hd0))
    set C : ℝ := max ((Finset.range (N + 1)).sup' (by simp)
        fun n => ‖(-1 : L) ^ (n + 1)
          * ((((n + 1 : ℕ) : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1 + 1))‖)
      (‖x - 1‖ / 2) with hC
    have hCd : C < ‖x - 1‖ := by
      rw [hC]
      refine max_lt ((Finset.sup'_lt_iff _).mpr fun n _ => hterm n) ?_
      linarith
    refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le
      fun n => ?_) hCd
    rcases le_or_gt n N with hn | hn
    · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      exact le_trans (Finset.le_sup'
        (fun k => ‖(-1 : L) ^ (k + 1)
          * ((((k + 1 : ℕ) : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (k + 1 + 1))‖) hmem)
        (le_max_left _ _)
    · exact le_trans (hN n hn.le).le (le_max_right _ _)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm htail.ne']
  exact max_eq_left htail.le

section Inversion

open PowerSeries

variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- `(1 + X)·D(log) = 1` over any `ℚ`-algebra: the formal geometric identity
`D(log(1+X)) = 1/(1+X)`. -/
theorem oneAddX_mul_derivative_log (A : Type*) [CommRing A] [Algebra ℚ A] :
    (1 + PowerSeries.X) * (d⁄dX A (PowerSeries.log A)) = 1 := by
  rw [deriv_log]
  ext n
  rw [coeff_one]
  match n with
  | 0 => simp
  | (k + 1) =>
    rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk,
      if_neg (Nat.succ_ne_zero k)]
    simp only [map_pow, map_neg, map_one]
    rw [pow_succ]
    ring

/-- **Formal identity (i)** (RJW Lem 5.14 / decomposition E4, Washington Prop 5.3 route):
`exp(log(1 + X)) = 1 + X` as formal power series over `ℚ_[p]`. Proved from
`(1 + X)·D F = F` with `F(0) = 1` by coefficient recursion. -/
theorem exp_subst_log :
    (exp ℚ_[p]).subst (PowerSeries.log ℚ_[p]) = 1 + PowerSeries.X := by
  have hg : HasSubst (PowerSeries.log ℚ_[p]) := HasSubst.log
  set F := (exp ℚ_[p]).subst (PowerSeries.log ℚ_[p]) with hF
  have hDF : d⁄dX ℚ_[p] F = F * d⁄dX ℚ_[p] (PowerSeries.log ℚ_[p]) := by
    rw [hF, derivative_subst ℚ_[p] hg, derivative_exp]
  have hrec : (1 + PowerSeries.X) * d⁄dX ℚ_[p] F = F := by
    rw [hDF, ← mul_assoc, mul_comm (1 + PowerSeries.X) F, mul_assoc,
      oneAddX_mul_derivative_log, mul_one]
  have hc0 : constantCoeff F = 1 := by
    rw [hF, show (constantCoeff ((exp ℚ_[p]).subst (PowerSeries.log ℚ_[p])))
        = MvPowerSeries.constantCoeff ((exp ℚ_[p]).subst (PowerSeries.log ℚ_[p])) from rfl,
      constantCoeff_subst hg, finsum_eq_single _ 0 fun d hd => by
        have h0 : MvPowerSeries.constantCoeff (PowerSeries.log ℚ_[p]) = (0 : ℚ_[p]) :=
          constantCoeff_log
        rw [map_pow, h0, zero_pow hd, smul_zero]]
    simp
  have hc1 : coeff 1 F = 1 := by
    have e0 := congrArg (coeff 0) hrec
    rw [add_mul, one_mul, map_add, coeff_zero_X_mul, add_zero, coeff_derivative] at e0
    simp only [Nat.cast_zero, zero_add, mul_one] at e0
    rw [e0, coeff_zero_eq_constantCoeff, hc0]
  have hrecn : ∀ m : ℕ,
      coeff (m + 2) F * ((m : ℚ_[p]) + 2) = -(m : ℚ_[p]) * coeff (m + 1) F := by
    intro m
    have e := congrArg (coeff (m + 1)) hrec
    rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_derivative, coeff_derivative] at e
    push_cast at e ⊢
    linear_combination e
  have hzero : ∀ k : ℕ, coeff (k + 2) F = 0 := by
    intro k
    induction k with
    | zero =>
      have h := hrecn 0
      simp only [Nat.cast_zero, neg_zero, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right (by norm_num)
    | succ k ih =>
      have h := hrecn (k + 1)
      rw [ih, mul_zero] at h
      have hne : ((k : ℚ_[p]) + 1 + 2) ≠ 0 := by
        rw [show ((k : ℚ_[p]) + 1 + 2) = ((k + 3 : ℕ) : ℚ_[p]) by push_cast; ring]
        exact Nat.cast_ne_zero.mpr (by omega)
      push_cast at h
      exact (mul_eq_zero.mp h).resolve_right hne
  ext n
  match n with
  | 0 => rw [coeff_zero_eq_constantCoeff, hc0]; simp
  | 1 => rw [hc1, map_add, coeff_one, coeff_X]; simp
  | (k + 2) => rw [hzero k, map_add, coeff_one, coeff_X]; simp

/-- **Formal identity (ii)** (RJW Lem 5.14 / decomposition E4, Washington Prop 5.3 route):
`log(1 + (exp − 1)) = X` as formal power series over `ℚ_[p]`. Proved by `derivative.ext`
from `D(log.subst(exp−1)) = 1` and matching constant coefficients. -/
theorem log_subst_exp_sub_one :
    (PowerSeries.log ℚ_[p]).subst (exp ℚ_[p] - 1) = PowerSeries.X := by
  have hg : HasSubst (exp ℚ_[p] - 1) := HasSubst.exp_sub_one
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [derivative_subst ℚ_[p] hg, map_sub, derivative_exp, Derivation.map_one_eq_zero,
      sub_zero, derivative_X]
    have key : ((1 + PowerSeries.X) * d⁄dX ℚ_[p] (PowerSeries.log ℚ_[p])).subst
        (exp ℚ_[p] - 1) = 1 := by
      rw [oneAddX_mul_derivative_log, ← coe_substAlgHom hg, map_one]
    have hone : (1 : PowerSeries ℚ_[p]).subst (exp ℚ_[p] - 1) = 1 := by
      rw [← coe_substAlgHom hg, map_one]
    rw [subst_mul hg, subst_add hg, hone, subst_X hg,
      show (1 : PowerSeries ℚ_[p]) + (exp ℚ_[p] - 1) = exp ℚ_[p] by ring] at key
    rw [mul_comm]
    exact key
  · rw [PowerSeries.constantCoeff_X]
    refine constantCoeff_subst_eq_zero ?_ _ constantCoeff_log
    have h : PowerSeries.constantCoeff (exp ℚ_[p] - 1) = (0 : ℚ_[p]) := by
      rw [map_sub, map_one, constantCoeff_exp, sub_self]
    exact h

omit [CompleteSpace L] in
/-- The `n`-th power of an (unconditionally) summable family, as a `HasSum` over tuples
`Fin n → ℕ` — the iterated nonarchimedean Cauchy product. -/
theorem hasSum_pow_fin {f : ℕ → L} {a : L} (hf : HasSum f a) (n : ℕ) :
    HasSum (fun φ : Fin n → ℕ => ∏ i, f (φ i)) (a ^ n) := by
  induction n with
  | zero =>
    have h : (fun φ : Fin 0 → ℕ => ∏ i, f (φ i)) = fun _ => (1 : L) := by funext φ; simp
    rw [h, pow_zero]
    exact hasSum_unique _
  | succ n ih =>
    have hmul := hf.mul_of_nonarchimedean ih
    rw [pow_succ, mul_comm (a ^ n) a]
    refine ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff).mp ?_
    have heq : (fun φ : Fin (n + 1) → ℕ => ∏ i, f (φ i)) ∘ (Fin.consEquiv (fun _ => ℕ))
        = fun mψ : ℕ × (Fin n → ℕ) => f mψ.1 * ∏ i, f (mψ.2 i) := by
      funext mψ
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
    rw [heq]
    exact hmul

omit [CompleteSpace L] [NormedAlgebra ℚ_[p] L] in
/-- Evaluating `G ^ n` at `y` is the `n`-th power of evaluating `G` at `y`: the summability
half (by induction via the nonarchimedean Cauchy product). -/
theorem summable_eval_pow [Algebra ℚ_[p] L] (G : PowerSeries ℚ_[p]) (y : L)
    (hG : Summable fun m : ℕ => (coeff m G : ℚ_[p]) • y ^ m) (n : ℕ) :
    Summable fun k : ℕ => (coeff k (G ^ n) : ℚ_[p]) • y ^ k := by
  induction n with
  | zero =>
    refine Summable.congr (f := fun k : ℕ => if k = 0 then (1 : L) else 0)
      (summable_of_ne_finset_zero (s := {0}) fun k hk => ?_) (fun k => ?_)
    · simp only [Finset.mem_singleton] at hk
      rw [if_neg hk]
    · rw [pow_zero, coeff_one]
      split_ifs with h <;> simp [h]
  | succ n ih =>
    set f : ℕ → L := fun m => (coeff m G : ℚ_[p]) • y ^ m with hf
    set g : ℕ → L := fun k => (coeff k (G ^ n) : ℚ_[p]) • y ^ k with hg
    have hfg : Summable fun ab : ℕ × ℕ => f ab.1 * g ab.2 := hG.mul_of_nonarchimedean ih
    refine (summable_sum_mul_antidiagonal_of_summable_mul (f := f) (g := g) hfg).congr
      fun j => ?_
    rw [pow_succ', coeff_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun ab hab => ?_
    simp only [hf, hg]
    rw [smul_mul_smul_comm,
      show y ^ ab.1 * y ^ ab.2 = y ^ j by rw [← pow_add, Finset.mem_antidiagonal.mp hab]]

omit [CompleteSpace L] in
/-- Evaluating `G ^ n` at `y` is the `n`-th power of evaluating `G` at `y`: the value
identity (by induction via the nonarchimedean Cauchy product). -/
theorem tsum_eval_pow (G : PowerSeries ℚ_[p]) (y : L)
    (hG : Summable fun m : ℕ => (coeff m G : ℚ_[p]) • y ^ m) (n : ℕ) :
    (∑' m : ℕ, (coeff m G : ℚ_[p]) • y ^ m) ^ n
      = ∑' k : ℕ, (coeff k (G ^ n) : ℚ_[p]) • y ^ k := by
  induction n with
  | zero =>
    rw [pow_zero, tsum_eq_single 0 fun k hk => by rw [pow_zero, coeff_one, if_neg hk, zero_smul]]
    simp
  | succ n ih =>
    have hGn : Summable fun k : ℕ => (coeff k (G ^ n) : ℚ_[p]) • y ^ k :=
      summable_eval_pow p G y hG n
    rw [pow_succ', ih]
    set f : ℕ → L := fun m => (coeff m G : ℚ_[p]) • y ^ m with hf
    set g : ℕ → L := fun k => (coeff k (G ^ n) : ℚ_[p]) • y ^ k with hg
    have hfg : Summable fun ab : ℕ × ℕ => f ab.1 * g ab.2 := hG.mul_of_nonarchimedean hGn
    rw [hG.tsum_mul_tsum_eq_tsum_sum_antidiagonal hGn hfg]
    refine tsum_congr fun j => ?_
    rw [pow_succ', coeff_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun ab hab => ?_
    simp only [hf, hg]
    rw [smul_mul_smul_comm,
      show y ^ ab.1 * y ^ ab.2 = y ^ j by rw [← pow_add, Finset.mem_antidiagonal.mp hab]]

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- The scalar family `n ↦ [Xⁿ]F · [Xᵏ](Gⁿ)` has finite support (for `HasSubst G`),
hence is summable. -/
theorem summable_coeff_pow_scalar (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) :
    Summable fun n : ℕ => (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p]) := by
  obtain ⟨N, hN⟩ := (hG.eventually_coeff_pow_eq_zero k).exists_forall_of_atTop
  refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
  simp only [Finset.mem_range, not_lt] at hn
  rw [hN n hn k le_rfl, mul_zero]

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- The inner identity matching `PowerSeries.coeff_subst`: `∑ₙ [Xⁿ]F · [Xᵏ](Gⁿ) = [Xᵏ](F∘G)`
(the `tsum` is a finite sum since `[Xᵏ](Gⁿ) = 0` for `n > k`). -/
theorem tsum_coeff_pow_eq_coeff_subst (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) :
    (∑' n : ℕ, (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p]))
      = (coeff k (F.subst G) : ℚ_[p]) := by
  obtain ⟨N, hN⟩ := (hG.eventually_coeff_pow_eq_zero k).exists_forall_of_atTop
  rw [tsum_eq_sum (s := Finset.range N) fun n hn => by
    rw [hN n (by simpa [Finset.mem_range] using hn) k le_rfl, mul_zero],
    show (coeff k (F.subst G) : ℚ_[p]) = PowerSeries.coeff k (F.subst G) from rfl,
    coeff_subst' hG F k, finsum_eq_finsetSum_of_support_subset _ (s := Finset.range N) ?_]
  · exact Finset.sum_congr rfl fun n _ => by rw [smul_eq_mul]
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hle
    rw [not_lt] at hle
    exact hn (by rw [hN n hle k le_rfl, smul_zero])

/-- **Evaluation bridge** (RJW Lem 5.14 / decomposition E4, Washington Prop 5.3 route):
the evaluation at `y` of a formal substitution `F.subst G` equals the composed convergent
sum, provided the total product family over `ℕ × ℕ` is summable. The proof regroups the
double sum by ultrametric Fubini (`Summable.tsum_comm`), using `tsum_eval_pow` for the inner
power and `tsum_coeff_pow_eq_coeff_subst` for the formal coefficients. -/
theorem master_bridge (F G : PowerSeries ℚ_[p]) (y : L) (hG : HasSubst G)
    (hGsum : Summable fun m : ℕ => (coeff m G : ℚ_[p]) • y ^ m)
    (hprod : Summable fun nk : ℕ × ℕ =>
      ((coeff nk.1 F : ℚ_[p]) * (coeff nk.2 (G ^ nk.1) : ℚ_[p])) • y ^ nk.2) :
    (∑' n : ℕ, (coeff n F : ℚ_[p]) • (∑' m : ℕ, (coeff m G : ℚ_[p]) • y ^ m) ^ n)
      = ∑' k : ℕ, (coeff k (F.subst G) : ℚ_[p]) • y ^ k := by
  have hL : (∑' n : ℕ, (coeff n F : ℚ_[p]) • (∑' m : ℕ, (coeff m G : ℚ_[p]) • y ^ m) ^ n)
      = ∑' (n : ℕ) (k : ℕ), ((coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p])) • y ^ k :=
    tsum_congr fun n => by
      rw [tsum_eval_pow p G y hGsum n,
        ← (summable_eval_pow p G y hGsum n).tsum_const_smul ((coeff n F : ℚ_[p]))]
      exact tsum_congr fun k => smul_smul _ _ _
  have hR : (∑' k : ℕ, (coeff k (F.subst G) : ℚ_[p]) • y ^ k)
      = ∑' (k : ℕ) (n : ℕ), ((coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p])) • y ^ k :=
    tsum_congr fun k => by
      rw [← tsum_coeff_pow_eq_coeff_subst p F G hG k,
        ← (summable_coeff_pow_scalar p F G hG k).tsum_smul_const (y ^ k)]
  rw [hL, hR]
  exact (hprod.tsum_comm (f := fun n k =>
    ((coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p])) • y ^ k)).symm

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- Ultrametric power bound: `‖∑ f i‖ᵐ ≤ C` whenever every term satisfies `‖f i‖ᵐ ≤ C`. -/
theorem pow_norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → L) {m : ℕ} (hm : 1 ≤ m)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i ∈ s, ‖f i‖ ^ m ≤ C) :
    ‖∑ i ∈ s, f i‖ ^ m ≤ C := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, norm_zero]
    rw [zero_pow (by omega)]
    exact hC
  · obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup' hne fun i => ‖f i‖
    have hle : ‖∑ i ∈ s, f i‖ ≤ ‖f i₀‖ := by
      rw [← hsup]
      exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (le_trans (norm_nonneg _) (Finset.le_sup' (fun i => ‖f i‖) hi₀))
        (fun i hi => Finset.le_sup' (fun i => ‖f i‖) hi)
    calc ‖∑ i ∈ s, f i‖ ^ m ≤ ‖f i₀‖ ^ m := pow_le_pow_left₀ (norm_nonneg _) hle m
      _ ≤ C := hf i₀ hi₀

/-- Legendre-type bound on a single multinomial term of `[Xᵏ](Gⁿ)`: if `[Xʲ]G` obeys
`‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` and `[X⁰]G = 0`, then each tuple product is bounded by `p^{k−n}`
(telescoping `(p−1)·v_p(lᵢ) ≤ lᵢ − 1`). -/
theorem norm_coeff_prod_le (G : PowerSeries ℚ_[p])
    (hcoeff : ∀ j : ℕ, 1 ≤ j → ‖(coeff j G : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (j - 1))
    (hc0 : (coeff 0 G : ℚ_[p]) = 0) (n k : ℕ) (l : ℕ →₀ ℕ)
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range n) k) :
    ‖∏ i ∈ Finset.range n, (coeff (l i) G : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (k - n) := by
  by_cases hex : ∃ i ∈ Finset.range n, l i = 0
  · obtain ⟨i, hi, hi0⟩ := hex
    rw [Finset.prod_eq_zero hi (by rw [hi0, hc0]), norm_zero,
      zero_pow (by have := hp.out.one_lt; omega)]
    positivity
  · simp only [not_exists, not_and] at hex
    have hpos : ∀ i ∈ Finset.range n, 1 ≤ l i :=
      fun i hi => Nat.one_le_iff_ne_zero.mpr (hex i hi)
    rw [norm_prod, Finset.mem_finsuppAntidiag] at *
    obtain ⟨hsum, _⟩ := hl
    rw [← Finset.prod_pow]
    refine le_trans (Finset.prod_le_prod (fun i _ => by positivity)
      fun i hi => hcoeff (l i) (hpos i hi)) ?_
    rw [Finset.prod_pow_eq_pow_sum]
    have hsumeq : ∑ i ∈ Finset.range n, (l i - 1) = k - n := by
      have hd : ∑ i ∈ Finset.range n, (l i - 1)
          = (∑ i ∈ Finset.range n, l i) - (∑ i ∈ Finset.range n, 1) := by
        rw [← Finset.sum_tsub_distrib]
        exact hpos
      rw [hd, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
        show (∑ i ∈ Finset.range n, l i) = k from hsum]
    rw [hsumeq]

/-- Legendre-type bound on the substituted-power coefficients: `‖[Xᵏ](Gⁿ)‖^{p−1} ≤ p^{k−n}`
for `G` with `[X⁰]G = 0` and `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` (the multinomial expansion bounded
termwise by `norm_coeff_prod_le`). -/
theorem norm_coeff_pow_le (G : PowerSeries ℚ_[p])
    (hcoeff : ∀ j : ℕ, 1 ≤ j → ‖(coeff j G : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (j - 1))
    (hc0 : (coeff 0 G : ℚ_[p]) = 0) (n k : ℕ) :
    ‖(coeff k (G ^ n) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (k - n) := by
  rw [coeff_pow]
  refine pow_norm_sum_le (L := ℚ_[p]) _ _ (by have := hp.out.one_lt; omega) (by positivity)
    fun l hl => norm_coeff_prod_le p G hcoeff hc0 n k l hl

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- `[Xᵏ](Gⁿ) = 0` for `k < n` when `[X⁰]G = 0` (order of `Gⁿ` is `≥ n`). -/
theorem coeff_pow_eq_zero_of_lt (G : PowerSeries ℚ_[p]) (hc0 : constantCoeff G = 0)
    {n k : ℕ} (hkn : k < n) : (coeff k (G ^ n) : ℚ_[p]) = 0 :=
  coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast hkn)
    (le_order_pow_of_constantCoeff_eq_zero n hc0))

/-- The product family of the evaluation bridge is summable, by the uniform geometric bound
`‖[Xⁿ]F · [Xᵏ](Gⁿ) · yᵏ‖^{p−1} ≤ p⁻¹·(p‖y‖^{p−1})ᵏ` (decaying since `‖y‖^{p−1} < p⁻¹`),
plus the support condition `n ≤ k`. -/
theorem summable_prod_family (F G : PowerSeries ℚ_[p]) (y : L) (hy : InExpBall p y)
    (hF : ∀ n : ℕ, 1 ≤ n → ‖(coeff n F : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1))
    (hGc : ∀ j : ℕ, 1 ≤ j → ‖(coeff j G : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (j - 1))
    (hG0 : constantCoeff G = 0) :
    Summable fun nk : ℕ × ℕ =>
      ((coeff nk.1 F : ℚ_[p]) * (coeff nk.2 (G ^ nk.1) : ℚ_[p])) • y ^ nk.2 := by
  have hGc0 : (coeff 0 G : ℚ_[p]) = 0 := by rw [coeff_zero_eq_constantCoeff]; exact hG0
  rw [summable_iff_tendsto_cofinite_zero, NormedAddGroup.tendsto_nhds_zero]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ p - 1 := by have := hp.out.one_lt; omega
  have hρ1 : (p : ℝ) * ‖y‖ ^ (p - 1) < 1 :=
    calc (p : ℝ) * ‖y‖ ^ (p - 1) < (p : ℝ) * (p : ℝ)⁻¹ := mul_lt_mul_of_pos_left hy hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hρ0 : 0 ≤ (p : ℝ) * ‖y‖ ^ (p - 1) := by positivity
  intro ε hε
  rw [Filter.eventually_cofinite]
  have htend : Tendsto (fun k : ℕ => (p : ℝ)⁻¹ * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul ((p : ℝ)⁻¹)
  obtain ⟨K, hK⟩ := (htend.eventually_lt_const
    (by positivity : (0 : ℝ) < ε ^ (p - 1))).exists_forall_of_atTop
  apply Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (K + 1)) (Set.finite_Iio (K + 1)))
  intro x hx
  simp only [Set.mem_setOf_eq, not_lt] at hx
  have hTne : ((coeff x.1 F : ℚ_[p]) * (coeff x.2 (G ^ x.1) : ℚ_[p])) • y ^ x.2 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    linarith [hx, hε]
  have hle : x.1 ≤ x.2 := by
    by_contra hlt
    rw [not_le] at hlt
    exact hTne (by rw [coeff_pow_eq_zero_of_lt p G hG0 hlt, mul_zero, zero_smul])
  simp only [Set.mem_prod, Set.mem_Iio]
  rcases Nat.eq_zero_or_pos x.1 with h0 | h1n
  · rw [h0, pow_zero] at hTne
    have hx20 : x.2 = 0 := by
      by_contra hx2
      exact hTne (by rw [coeff_one, if_neg hx2, mul_zero, zero_smul])
    exact ⟨by omega, by omega⟩
  · have hk : x.2 ≤ K := by
      by_contra hgt
      rw [not_le] at hgt
      have hb : ‖((coeff x.1 F : ℚ_[p]) * (coeff x.2 (G ^ x.1) : ℚ_[p])) • y ^ x.2‖ ^ (p - 1)
          ≤ ‖y‖ ^ (x.2 * (p - 1)) * (p : ℝ) ^ (x.2 - 1) := by
        rw [norm_smul, mul_pow, norm_mul, mul_pow, norm_pow, ← pow_mul]
        calc (‖(coeff x.1 F : ℚ_[p])‖ ^ (p - 1) * ‖(coeff x.2 (G ^ x.1) : ℚ_[p])‖ ^ (p - 1))
              * ‖y‖ ^ (x.2 * (p - 1))
            ≤ ((p : ℝ) ^ (x.1 - 1) * (p : ℝ) ^ (x.2 - x.1)) * ‖y‖ ^ (x.2 * (p - 1)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul (hF x.1 h1n) (norm_coeff_pow_le p G hGc hGc0 x.1 x.2)
                (by positivity) (by positivity)
          _ = ‖y‖ ^ (x.2 * (p - 1)) * (p : ℝ) ^ (x.2 - 1) := by
              rw [← pow_add, show (x.1 - 1) + (x.2 - x.1) = x.2 - 1 by omega]
              ring
      have hb2 : ‖y‖ ^ (x.2 * (p - 1)) * (p : ℝ) ^ (x.2 - 1)
          = (p : ℝ)⁻¹ * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ x.2 := by
        rw [mul_pow, ← pow_mul, mul_comm x.2 (p - 1),
          show (p : ℝ) ^ x.2 = (p : ℝ) * (p : ℝ) ^ (x.2 - 1) by
            rw [← pow_succ']; congr 1; omega]
        field_simp
      rw [hb2] at hb
      have hεb : ε ^ (p - 1)
          ≤ ‖((coeff x.1 F : ℚ_[p]) * (coeff x.2 (G ^ x.1) : ℚ_[p])) • y ^ x.2‖ ^ (p - 1) :=
        pow_le_pow_left₀ hε.le hx _
      linarith [le_trans hεb hb, hK x.2 hgt.le]
    exact ⟨by omega, by omega⟩

/-- `(‖(n : ℚ_[p])‖^{p−1})⁻¹ ≤ p^{n−1}` for `n ≥ 1` (the inverted Legendre bound for the
plain integer `n`, used for the `log` coefficients). -/
theorem norm_natCast_inv_pow_le (n : ℕ) (hn : 1 ≤ n) :
    (‖(n : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1) := by
  have hval : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.2 (by omega : n ≠ 0)),
      Padic.valuation_natCast]
  rw [hval, ← zpow_natCast _ (p - 1), ← zpow_mul, ← zpow_neg, ← zpow_natCast (p : ℝ) (n - 1)]
  refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) ?_
  have hkey : (p - 1) * padicValNat p ((n - 1) + 1) ≤ n - 1 :=
    sub_one_mul_padicValNat_succ_le p (n - 1)
  rw [show (n - 1) + 1 = n by omega] at hkey
  push_cast
  have hZ : ((p : ℤ) - 1) * (padicValNat p n : ℤ) ≤ (n : ℤ) - 1 := by
    have h2 : ((p - 1 : ℕ) : ℤ) * (padicValNat p n : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
      exact_mod_cast hkey
    rwa [show ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 by have := hp.out.one_le; omega,
      show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by omega] at h2
  linarith [hZ]

/-- The `exp` coefficients obey the Legendre bound `‖[Xⁿ]exp‖^{p−1} ≤ p^{n−1}`. -/
theorem norm_coeff_exp_le (n : ℕ) (hn : 1 ≤ n) :
    ‖(coeff n (exp ℚ_[p]) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1) := by
  rw [coeff_exp, one_div, map_inv₀, map_natCast, norm_inv, inv_pow]
  exact norm_factorial_inv_pow_le p hn

/-- The `log` coefficients obey the Legendre bound `‖[Xⁿ]log‖^{p−1} ≤ p^{n−1}`. -/
theorem norm_coeff_log_le (n : ℕ) (hn : 1 ≤ n) :
    ‖(coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1) := by
  rw [coeff_log, if_neg (by omega : n ≠ 0), map_div₀, map_pow, map_neg, map_one, map_natCast,
    norm_div, norm_pow, norm_neg, norm_one, one_pow, div_pow, one_pow]
  rw [← inv_eq_one_div]
  exact norm_natCast_inv_pow_le p n hn

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- `padicExp z = ∑ₙ [Xⁿ]exp · zⁿ`: the exponential as the evaluation of `PowerSeries.exp`. -/
theorem padicExp_eq_tsum_coeff (z : L) :
    padicExp p z = ∑' n : ℕ, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n := by
  rw [padicExp]
  exact tsum_congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- Termwise match of the `padicLog` series with the `PowerSeries.log` coefficients. -/
theorem padicLog_term_eq (x : L) (n : ℕ) :
    (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1))
      = (coeff (n + 1) (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ (n + 1) := by
  have hneg : (-1 : L) ^ n = (algebraMap ℚ_[p] L) ((-1 : ℚ_[p]) ^ n) := by
    rw [map_pow, map_neg, map_one]
  rw [Algebra.smul_def, Algebra.smul_def, hneg, ← mul_assoc, ← map_mul, coeff_log,
    if_neg (Nat.succ_ne_zero n)]
  congr 2
  rw [map_div₀, map_pow, map_neg, map_one, map_natCast]
  push_cast
  rw [pow_succ, pow_succ, mul_comm ((-1 : ℚ_[p]) ^ n) _]
  ring

/-- `padicLog x = ∑ₙ [Xⁿ]log · (x − 1)ⁿ`: the logarithm as the evaluation of
`PowerSeries.log` at `x − 1`. -/
theorem padicLog_eq_tsum_coeff {x : L} (hx : InExpBall p (x - 1)) :
    padicLog p x = ∑' n : ℕ, (coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ n := by
  have hsum0 : Summable fun n : ℕ =>
      (coeff (n + 1) (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ (n + 1) :=
    (summable_padicLog_terms p hx).congr fun n => padicLog_term_eq p x n
  have hsum : Summable fun n : ℕ =>
      (coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ n :=
    (summable_nat_add_iff 1).mp hsum0
  rw [padicLog, hsum.tsum_eq_zero_add, coeff_log, if_pos rfl, zero_smul, zero_add]
  exact tsum_congr fun n => padicLog_term_eq p x n

/-- `∑ₘ [Xᵐ](exp − 1) · yᵐ = padicExp y − 1`: peeling the (vanishing) constant term. -/
theorem tsum_coeff_exp_sub_one (y : L) (hy : InExpBall p y) :
    (∑' m : ℕ, (coeff m (exp ℚ_[p] - 1) : ℚ_[p]) • y ^ m) = padicExp p y - 1 := by
  have hexp : Summable fun n : ℕ => (coeff n (exp ℚ_[p]) : ℚ_[p]) • y ^ n := by
    refine (summable_padicExp_terms p hy).congr fun n => ?_
    rw [coeff_exp, one_div, map_inv₀, map_natCast]
  have hsub : Summable fun n : ℕ => (coeff n (exp ℚ_[p] - 1) : ℚ_[p]) • y ^ n := by
    refine (summable_nat_add_iff 1).mp (((summable_nat_add_iff 1).mpr hexp).congr fun n => ?_)
    rw [map_sub, coeff_one, if_neg (Nat.succ_ne_zero n), sub_zero]
  rw [padicExp_eq_tsum_coeff, hsub.tsum_eq_zero_add, hexp.tsum_eq_zero_add]
  have h0 : (coeff 0 (exp ℚ_[p] - 1) : ℚ_[p]) • y ^ 0 = 0 := by
    rw [map_sub, coeff_one, if_pos rfl, coeff_zero_eq_constantCoeff, constantCoeff_exp,
      sub_self, zero_smul]
  have h1 : (coeff 0 (exp ℚ_[p]) : ℚ_[p]) • y ^ 0 = 1 := by
    rw [coeff_zero_eq_constantCoeff, constantCoeff_exp, pow_zero, one_smul]
  rw [h0, h1, zero_add, add_comm (1 : L) _, add_sub_assoc, sub_self, add_zero]
  exact tsum_congr fun m => by rw [map_sub, coeff_one, if_neg (Nat.succ_ne_zero m), sub_zero]

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem eval_oneAddX (y : L) :
    (∑' k : ℕ, (coeff k (1 + PowerSeries.X : PowerSeries ℚ_[p]) : ℚ_[p]) • y ^ k) = 1 + y := by
  have hsupp : ∀ k : ℕ, 2 ≤ k →
      (coeff k (1 + PowerSeries.X : PowerSeries ℚ_[p]) : ℚ_[p]) • y ^ k = 0 := fun k hk => by
    rw [map_add, coeff_one, coeff_X, if_neg (by omega : k ≠ 0), if_neg (by omega : k ≠ 1),
      add_zero, zero_smul]
  rw [tsum_eq_sum (s := {0, 1}) fun k hk => hsupp k (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega),
    Finset.sum_insert (by simp), Finset.sum_singleton,
    map_add, coeff_one, coeff_X, if_pos rfl, if_neg (by omega : (0 : ℕ) ≠ 1), add_zero,
    map_add, coeff_one, coeff_X, if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl, zero_add,
    pow_zero, one_smul, pow_one, one_smul]

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem eval_X (y : L) :
    (∑' k : ℕ, (coeff k (PowerSeries.X : PowerSeries ℚ_[p]) : ℚ_[p]) • y ^ k) = y := by
  rw [tsum_eq_single 1 fun k hk => by rw [coeff_X, if_neg (by omega : k ≠ 1), zero_smul],
    coeff_X, if_pos rfl, pow_one, one_smul]

/-- E4: `exp` inverts `log` on the matched balls (series composition with
ultrametric Fubini; Washington Prop 5.3 route — decomposition E4). -/
theorem padicExp_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    padicExp p (padicLog p x) = x := by
  have hGsum : Summable fun m : ℕ =>
      (coeff m (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ m :=
    (summable_nat_add_iff 1).mp
      ((summable_padicLog_terms p hx).congr fun n => padicLog_term_eq p x n)
  rw [padicExp_eq_tsum_coeff, padicLog_eq_tsum_coeff p hx,
    master_bridge p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x - 1) HasSubst.log hGsum
      (summable_prod_family p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x - 1) hx
        (norm_coeff_exp_le p) (norm_coeff_log_le p) constantCoeff_log),
    exp_subst_log, eval_oneAddX]
  ring

/-- E4: `log` inverts `exp` on the matched balls (series composition with
ultrametric Fubini; Washington Prop 5.3 route — decomposition E4). -/
theorem padicLog_padicExp {x : L} (hx : InExpBall p x) :
    padicLog p (padicExp p x) = x := by
  have hb : InExpBall p (padicExp p x - 1) := by
    rw [InExpBall, norm_padicExp_sub_one p hx]; exact hx
  have hexp : Summable fun n : ℕ => (coeff n (exp ℚ_[p]) : ℚ_[p]) • x ^ n :=
    (summable_padicExp_terms p hx).congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast]
  have hGsum : Summable fun m : ℕ => (coeff m (exp ℚ_[p] - 1) : ℚ_[p]) • x ^ m :=
    (summable_nat_add_iff 1).mp (((summable_nat_add_iff 1).mpr hexp).congr fun n => by
      rw [map_sub, coeff_one, if_neg (Nat.succ_ne_zero n), sub_zero])
  have hG0 : constantCoeff (exp ℚ_[p] - 1) = 0 := by
    rw [map_sub, map_one, constantCoeff_exp, sub_self]
  have hGc : ∀ j : ℕ, 1 ≤ j →
      ‖(coeff j (exp ℚ_[p] - 1) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (j - 1) := fun j hj => by
    rw [map_sub, coeff_one, if_neg (by omega : j ≠ 0), sub_zero]
    exact norm_coeff_exp_le p j hj
  rw [padicLog_eq_tsum_coeff p hb, ← tsum_coeff_exp_sub_one p x hx,
    master_bridge p (PowerSeries.log ℚ_[p]) (exp ℚ_[p] - 1) x HasSubst.exp_sub_one hGsum
      (summable_prod_family p (PowerSeries.log ℚ_[p]) (exp ℚ_[p] - 1) x hx
        (norm_coeff_log_le p) hGc hG0),
    log_subst_exp_sub_one, eval_X]

/-- E4 / RJW Lem 5.14: the logarithm is multiplicative on `1 + 𝔪` — derived from the two
inversions and the exponential functional equation (decomposition E4, Step C). -/
theorem padicLog_mul {x y : L} (hx : InExpBall p (x - 1))
    (hy : InExpBall p (y - 1)) :
    padicLog p (x * y) = padicLog p x + padicLog p y := by
  set a := padicLog p x with ha
  set b := padicLog p y with hb
  have hballa : InExpBall p a := by rw [InExpBall, ha, norm_padicLog p hx]; exact hx
  have hballb : InExpBall p b := by rw [InExpBall, hb, norm_padicLog p hy]; exact hy
  have hballab : InExpBall p (a + b) := by
    have hmax : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max a b
    rw [InExpBall]
    rcases le_total ‖a‖ ‖b‖ with h | h
    · exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _)
        (le_trans hmax (by rw [max_eq_right h])) _) hballb
    · exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _)
        (le_trans hmax (by rw [max_eq_left h])) _) hballa
  have hea : padicExp p a = x := padicExp_padicLog p hx
  have heb : padicExp p b = y := padicExp_padicLog p hy
  rw [show x * y = padicExp p (a + b) by rw [padicExp_add p hballa hballb, hea, heb],
    padicLog_padicExp p hballab]

end Inversion

section pZp

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: an element of `pℤ_p` has `ℚ_[p]`-norm at most `p⁻¹` (the coe-norm of
`PadicInt.norm_le_pow_iff_mem_span_pow` at exponent `1`; RJW Lem 5.14). -/
theorem coe_norm_le_inv_of_mem_span {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [← PadicInt.norm_def, show ((p : ℝ)⁻¹) = (p : ℝ) ^ (-((1 : ℕ) : ℤ)) by
    rw [zpow_neg, Nat.cast_one, zpow_one]]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x 1).2 (by simpa using hx)

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: for odd `p`, `pℤ_p` lies strictly inside the exponential convergence
ball: `‖x‖^{p−1} ≤ p^{−(p−1)} < p⁻¹` since `p − 1 ≥ 2` (where `hp2` enters;
RJW Lem 5.14, TeX 1892–1893). -/
theorem inExpBall_of_mem_span (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : InExpBall p ((x : ℚ_[p])) := by
  have hp3 : 3 ≤ p := by
    rcases hp.out.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := hp.out.two_le; omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnorm := coe_norm_le_inv_of_mem_span p hx
  rw [InExpBall]
  calc ‖(x : ℚ_[p])‖ ^ (p - 1)
      ≤ ((p : ℝ)⁻¹) ^ (p - 1) := pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ < ((p : ℝ)⁻¹) ^ 1 := by
        refine pow_lt_pow_right_of_lt_one₀ (inv_pos.mpr hppos) ?_ (by omega)
        rw [inv_lt_one_iff₀]; exact .inr (by exact_mod_cast hp.out.one_lt)
    _ = (p : ℝ)⁻¹ := pow_one _

/-- **RJW Lemma 5.14, first half** (TeX 1892–1893): "The p-adic exponential
map converges on `pℤ_p`" — for odd `p`, `pℤ_[p]` lies in the convergence ball
(`‖x‖ ≤ p⁻¹ < p^{−1/(p−1)}`). Stated on `ℤ_[p]` (the `L = ℚ_[p]`-instance
restricted to integers; `exp` of a multiple of `p` is again integral by the
isometry). -/
theorem padicExp_converges_on_pZp (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • ((x : ℚ_[p]) ^ n) :=
  summable_padicExp_terms (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)

/-- The integral exponential on `pℤ_p` (odd `p`), valued in `1 + pℤ_p`.
Junk-total: defined via the integrality certificate `‖exp x‖ ≤ 1`, with junk
value `1` (the exponential's value at the degenerate point `0`); RJW Lem 5.14,
decomposition E5. -/
noncomputable def pZpExp (x : ℤ_[p]) : ℤ_[p] :=
  if h : ‖padicExp p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicExp p ((x : ℚ_[p])), h⟩ else 1

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: on `pℤ_p` (odd `p`) the analytic exponential is integral, so `pZpExp`
takes its true branch: `(pZpExp x : ℚ_[p]) = exp x`. -/
theorem pZpExp_coe (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ((pZpExp p x : ℤ_[p]) : ℚ_[p]) = padicExp p ((x : ℚ_[p])) := by
  have hle : ‖padicExp p ((x : ℚ_[p]))‖ ≤ 1 := by
    have hball := inExpBall_of_mem_span p hp2 hx
    have hsub : ‖padicExp p ((x : ℚ_[p])) - 1‖ = ‖(x : ℚ_[p])‖ :=
      norm_padicExp_sub_one (L := ℚ_[p]) p hball
    have hx1 : ‖(x : ℚ_[p])‖ ≤ 1 :=
      (coe_norm_le_inv_of_mem_span p hx).trans
        (by rw [inv_le_one_iff₀]; exact .inr (by exact_mod_cast hp.out.one_le))
    calc ‖padicExp p ((x : ℚ_[p]))‖
        = ‖(1 : ℚ_[p]) + (padicExp p ((x : ℚ_[p])) - 1)‖ := by ring_nf
      _ ≤ max ‖(1 : ℚ_[p])‖ ‖padicExp p ((x : ℚ_[p])) - 1‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hsub, norm_one]; exact max_le le_rfl hx1
  rw [pZpExp, dif_pos hle]

theorem pZpExp_sub_one_mem (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpExp p x - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [← pow_one (p : ℤ_[p]), ← PadicInt.norm_le_pow_iff_mem_span_pow _ 1,
    PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, pZpExp_coe p hp2 hx,
    norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx),
    zpow_neg, Nat.cast_one, zpow_one]
  exact coe_norm_le_inv_of_mem_span p hx

/-- The integral logarithm on `1 + pℤ_p` (odd `p`), valued in `pℤ_p`.
Junk-total: defined via the integrality certificate `‖log x‖ ≤ 1`, with junk
value `0` (the logarithm's value at the degenerate point `1`); RJW Lem 5.14,
decomposition E5. -/
noncomputable def pZpLog (x : ℤ_[p]) : ℤ_[p] :=
  if h : ‖padicLog p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicLog p ((x : ℚ_[p])), h⟩ else 0

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: on `1 + pℤ_p` (odd `p`) the analytic logarithm is integral, so `pZpLog`
takes its true branch: `(pZpLog x : ℚ_[p]) = log x`. -/
theorem pZpLog_coe (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    ((pZpLog p x : ℤ_[p]) : ℚ_[p]) = padicLog p ((x : ℚ_[p])) := by
  have hxsub : ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) := by
    rw [PadicInt.coe_sub, PadicInt.coe_one]
  have hball : InExpBall p ((x : ℚ_[p]) - 1) := by
    rw [hxsub]; exact inExpBall_of_mem_span p hp2 hx
  have hle : ‖padicLog p ((x : ℚ_[p]))‖ ≤ 1 := by
    rw [norm_padicLog (L := ℚ_[p]) p hball, hxsub]
    exact (coe_norm_le_inv_of_mem_span p hx).trans
      (by rw [inv_le_one_iff₀]; exact .inr (by exact_mod_cast hp.out.one_le))
  rw [pZpLog, dif_pos hle]

theorem pZpLog_mem (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpLog p x ∈ Ideal.span {(p : ℤ_[p])} := by
  have hxsub : ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) := by
    rw [PadicInt.coe_sub, PadicInt.coe_one]
  have hball : InExpBall p ((x : ℚ_[p]) - 1) := by
    rw [hxsub]; exact inExpBall_of_mem_span p hp2 hx
  rw [← pow_one (p : ℤ_[p]), ← PadicInt.norm_le_pow_iff_mem_span_pow _ 1,
    PadicInt.norm_def, pZpLog_coe p hp2 hx, norm_padicLog (L := ℚ_[p]) p hball,
    hxsub, zpow_neg, Nat.cast_one, zpow_one]
  exact coe_norm_le_inv_of_mem_span p hx

/-- **RJW Lemma 5.14, second half** (TeX 1893–1894): "for any `s ∈ ℤ_p`, the
function `1+pℤ_p → ℤ_p` given by `x ↦ x^s := exp(s·log(x))` is well-defined"
— and it agrees with the character construction `PadicInt.onePAdicPow`
(uniqueness of continuous additive characters with a given value at `1`;
decomposition E5). -/
theorem padicExp_smul_padicLog_eq_onePAdicPow (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) :
    pZpExp p (s * pZpLog p x) = PadicInt.onePAdicPow p x hx s := by
  set ℓ := pZpLog p x with hℓ
  have hℓmem : ℓ ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hx
  have hargmem : ∀ t : ℤ_[p], t * ℓ ∈ Ideal.span {(p : ℤ_[p])} :=
    fun t => Ideal.mul_mem_left _ _ hℓmem
  have hexpcoe : ∀ t : ℤ_[p],
      ((pZpExp p (t * ℓ) : ℤ_[p]) : ℚ_[p]) = padicExp p ((t * ℓ : ℤ_[p]) : ℚ_[p]) :=
    fun t => pZpExp_coe p hp2 (hargmem t)
  let κ : AddChar ℤ_[p] ℤ_[p] :=
    { toFun := fun t => pZpExp p (t * ℓ)
      map_zero_eq_one' := by
        refine PadicInt.ext ?_
        rw [zero_mul, PadicInt.coe_one, pZpExp_coe p hp2 (Ideal.zero_mem _),
          PadicInt.coe_zero, padicExp_zero]
      map_add_eq_mul' := fun a b => by
        refine PadicInt.ext ?_
        rw [PadicInt.coe_mul, hexpcoe a, hexpcoe b, hexpcoe (a + b),
          show ((a + b) * ℓ : ℤ_[p]) = a * ℓ + b * ℓ by ring,
          PadicInt.coe_add,
          padicExp_add (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 (hargmem a))
            (inExpBall_of_mem_span p hp2 (hargmem b))] }
  have hℓnorm : ‖ℓ‖ ≤ 1 := by
    rw [PadicInt.norm_def]
    exact (coe_norm_le_inv_of_mem_span p hℓmem).trans
      (by rw [inv_le_one_iff₀]; exact .inr (by exact_mod_cast hp.out.one_le))
  have hκcont : Continuous κ := by
    refine LipschitzWith.continuous (K := 1)
      (lipschitzWith_iff_dist_le_mul.2 fun a b => ?_)
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    change ‖pZpExp p (a * ℓ) - pZpExp p (b * ℓ)‖ ≤ ‖a - b‖
    rw [PadicInt.norm_def, PadicInt.coe_sub, hexpcoe a, hexpcoe b,
      norm_padicExp_sub_padicExp (L := ℚ_[p]) p
        (inExpBall_of_mem_span p hp2 (hargmem a))
        (inExpBall_of_mem_span p hp2 (hargmem b)),
      ← PadicInt.coe_sub,
      show (a * ℓ - b * ℓ : ℤ_[p]) = (a - b) * ℓ by ring,
      PadicInt.coe_mul, norm_mul, ← PadicInt.norm_def, ← PadicInt.norm_def]
    calc ‖a - b‖ * ‖ℓ‖ ≤ ‖a - b‖ * 1 := by gcongr
      _ = ‖a - b‖ := mul_one _
  have hκone : κ 1 = 1 + (x - 1) := by
    rw [add_sub_cancel]
    refine PadicInt.ext ?_
    change ((pZpExp p (1 * ℓ) : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p])
    rw [one_mul, hℓ, pZpExp_coe p hp2 hℓmem, pZpLog_coe p hp2 hx]
    refine padicExp_padicLog (L := ℚ_[p]) p ?_
    rw [show ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) by
      rw [PadicInt.coe_sub, PadicInt.coe_one]]
    exact inExpBall_of_mem_span p hp2 hx
  have heq : κ = PadicInt.onePAdicPow p x hx :=
    PadicInt.eq_addChar_of_value_at_one
      (PadicInt.tendsto_pow_atTop_nhds_zero_of_mem_span p hx) hκcont hκone
  exact DFunLike.congr_fun heq s

end pZp

end PadicLFunctions
