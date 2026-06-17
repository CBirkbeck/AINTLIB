/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.PadicExp
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)

RJW Thm 6.1(ii) (TeX 1992–1995) evaluates `log_p` at the elements
`1 − ε_N^c`, which lie OUTSIDE the convergence ball of `padicLog`. This file
extends the logarithm to the rational-valuation domain: `x` with
`x^m = p^k·y` for some `m > 0`, `k : ℤ` and `y` in the open exponential
ball, setting `extLog x := m⁻¹·padicLog y` (junk value `0` outside;
Iwasawa's branch `log_p(p) = 0`). Construction cross-reference: Washington,
*Introduction to Cyclotomic Fields*, §5.1. The domain-membership engine for
the theorem's arguments is `extLogDomain_of_integral_norm_one`: a norm-one
element integral over `ℤ` has a power within distance `p⁻¹` of `1`
(pigeonhole in the finite ring `ℤ[z]/p`), and `p`-power iteration then
lands inside the exponential ball.

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster W6a.
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- Members of the exponential ball have norm less than one. -/
theorem norm_lt_one_of_inExpBall {w : L} (hw : InExpBall p w) : ‖w‖ < 1 := by
  by_contra h
  exact absurd hw (not_lt.mpr (le_trans
    (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
    (one_le_pow₀ (not_lt.mp h))))

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- W6a-a1: the translated exponential ball `1 + B` is closed under
multiplication (ultrametric). -/
theorem mul_mem_expBall {y z : L} (hy : InExpBall p (y - 1))
    (hz : InExpBall p (z - 1)) : InExpBall p (y * z - 1) := by
  have key : ‖y * z - 1‖ ≤ max ‖y - 1‖ ‖z - 1‖ := by
    rw [show y * z - 1 = (y - 1) * z + (z - 1) by ring]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le_max ?_ le_rfl)
    rw [norm_mul]
    have hz1 : ‖z‖ ≤ 1 := by
      rw [show z = (z - 1) + 1 by ring]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
        (max_le (norm_lt_one_of_inExpBall p hz).le norm_one.le)
    exact mul_le_of_le_one_right (norm_nonneg _) hz1
  calc ‖y * z - 1‖ ^ (p - 1) ≤ (max ‖y - 1‖ ‖z - 1‖) ^ (p - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) key _
    _ < (p : ℝ)⁻¹ := by
        rcases max_cases ‖y - 1‖ ‖z - 1‖ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
        exacts [hy, hz]

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- The exponential ball is closed under powers. -/
theorem pow_mem_expBall {y : L} (hy : InExpBall p (y - 1)) (n : ℕ) :
    InExpBall p (y ^ n - 1) := by
  induction n with
  | zero =>
    rw [pow_zero, sub_self, InExpBall, norm_zero,
      zero_pow (by have := hp.out.one_lt; omega)]
    exact inv_pos.mpr (by exact_mod_cast hp.out.pos)
  | succ k ih =>
    rw [pow_succ]
    exact mul_mem_expBall p ih hy

/-- W6a-a2: the logarithm of a power on the ball. -/
theorem padicLog_pow {y : L} (hy : InExpBall p (y - 1)) (n : ℕ) :
    padicLog p (y ^ n) = n • padicLog p y := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicLog_mul p (pow_mem_expBall p hy k) hy, ih, succ_nsmul]

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The `p`-adic norm of `p` in `L`. -/
theorem norm_natCast_p : ‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) from
      (map_natCast _ p).symm,
    norm_algebraMap', Padic.norm_p]

omit [CompleteSpace L] in
/-- W6a-a3: one `p`-th-power step contracts towards `1`
(`p ∣ (p choose i)` for `0 < i < p`). -/
theorem norm_pow_p_sub_one_le {w : L} (hw : ‖w - 1‖ < 1) :
    ‖w ^ p - 1‖ ≤ max (‖w - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w - 1‖) := by
  set t : L := w - 1 with ht
  have hexp : w ^ p - 1
      = ∑ i ∈ Finset.range p, t ^ (i + 1) * (p.choose (i + 1) : L) := by
    rw [show w ^ p = (t + 1) ^ p by rw [ht]; ring_nf, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one]
    ring
  rw [hexp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_max_of_le_left (by positivity)) fun i hi => ?_
  rw [norm_mul, norm_pow]
  rcases eq_or_ne (i + 1) p with hip | hip
  · -- top term `t^p`
    rw [hip, Nat.choose_self, Nat.cast_one, norm_one, mul_one]
    exact le_max_left _ _
  · -- interior terms carry `p ∣ choose`
    have hlt : i + 1 < p := lt_of_le_of_ne (Finset.mem_range.mp hi) hip
    obtain ⟨m, hm⟩ := hp.out.dvd_choose_self (Nat.succ_ne_zero i) hlt
    refine le_max_of_le_right ?_
    calc ‖t‖ ^ (i + 1) * ‖((p.choose (i + 1) : ℕ) : L)‖
        ≤ ‖t‖ * (p : ℝ)⁻¹ := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
          · exact pow_le_of_le_one (norm_nonneg _) hw.le (Nat.succ_ne_zero i)
          · rw [hm, Nat.cast_mul, norm_mul, norm_natCast_p p]
            exact mul_le_of_le_one_right (by positivity)
              (IsUltrametricDist.norm_natCast_le_one L m)
      _ = (p : ℝ)⁻¹ * ‖t‖ := mul_comm _ _

omit [CompleteSpace L] in
/-- W6a-a4: from the open unit ball, some `p`-power iterate lands in the
exponential ball (geometric contraction with ratio
`max (‖w−1‖^(p−1)) p⁻¹ < 1`). -/
theorem exists_pPow_pow_inExpBall {w : L} (hw : ‖w - 1‖ < 1) :
    ∃ j : ℕ, InExpBall p (w ^ p ^ j - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set t0 : ℝ := max (‖w - 1‖ ^ (p - 1)) (p : ℝ)⁻¹ with ht0
  have ht00 : 0 ≤ t0 := le_max_of_le_right (by positivity)
  have ht01 : t0 < 1 := max_lt
    (pow_lt_one₀ (norm_nonneg _) hw (by have := hp.out.one_lt; omega))
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hdecay : ∀ j : ℕ, ‖w ^ p ^ j - 1‖ ≤ t0 ^ j * ‖w - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      have hrw : ‖w ^ p ^ k - 1‖ ≤ ‖w - 1‖ := le_trans ih
        (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht00 ht01.le))
      have hk1 : ‖w ^ p ^ k - 1‖ < 1 := lt_of_le_of_lt hrw hw
      have hstep := norm_pow_p_sub_one_le p hk1
      rw [← pow_mul, ← pow_succ] at hstep
      have hbound : max (‖w ^ p ^ k - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w ^ p ^ k - 1‖)
          ≤ t0 * ‖w ^ p ^ k - 1‖ := by
        refine max_le ?_
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
        calc ‖w ^ p ^ k - 1‖ ^ p
            = ‖w ^ p ^ k - 1‖ ^ (p - 1) * ‖w ^ p ^ k - 1‖ := by
              rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
          _ ≤ t0 * ‖w ^ p ^ k - 1‖ :=
              mul_le_mul_of_nonneg_right
                (le_trans (pow_le_pow_left₀ (norm_nonneg _) hrw _)
                  (le_max_left _ _)) (norm_nonneg _)
      refine le_trans hstep (le_trans hbound ?_)
      calc t0 * ‖w ^ p ^ k - 1‖ ≤ t0 * (t0 ^ k * ‖w - 1‖) :=
            mul_le_mul_of_nonneg_left ih ht00
        _ = t0 ^ (k + 1) * ‖w - 1‖ := by ring
  have hgeo : Filter.Tendsto
      (fun j : ℕ => (t0 ^ j * ‖w - 1‖) ^ (p - 1)) Filter.atTop (nhds 0) := by
    have hfun : (fun j : ℕ => (t0 ^ j * ‖w - 1‖) ^ (p - 1))
        = fun j => ‖w - 1‖ ^ (p - 1) * ((t0 ^ (p - 1)) ^ j) := by
      funext j
      rw [mul_pow, ← pow_mul, mul_comm j (p - 1), pow_mul]
      ring
    rw [hfun]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (pow_lt_one₀ ht00 ht01 (by have := hp.out.one_lt; omega))).const_mul
      (‖w - 1‖ ^ (p - 1))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hgeo ((p : ℝ)⁻¹) (inv_pos.mpr hp0)
  refine ⟨N, ?_⟩
  have hsmall := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  change ‖w ^ p ^ N - 1‖ ^ (p - 1) < (p : ℝ)⁻¹
  calc ‖w ^ p ^ N - 1‖ ^ (p - 1) ≤ (t0 ^ N * ‖w - 1‖) ^ (p - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) (hdecay N) _
    _ < (p : ℝ)⁻¹ := hsmall

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- Members of the translated exponential ball `1 + B` have norm exactly `1`
(ultrametric isoceles: `‖y‖ = ‖(y−1) + 1‖ = 1` since `‖y−1‖ < 1 = ‖1‖`).
Decomposition R6 cluster W6a / Washington §5.1. -/
theorem norm_eq_one_of_inExpBall_sub_one {y : L} (hy : InExpBall p (y - 1)) :
    ‖y‖ = 1 := by
  have hlt := norm_lt_one_of_inExpBall p hy
  have hne : ‖y - 1‖ ≠ ‖(1 : L)‖ := by rw [norm_one]; exact ne_of_lt hlt
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rwa [show y - 1 + 1 = y by ring, norm_one, max_eq_right hlt.le] at this

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- Every element of the `ℤ`-subalgebra generated by a norm-one element has
norm at most `1` (ultrametric: integers are bounded by `1`, products and sums
stay inside the unit ball). Decomposition R6 cluster W6a / Washington §5.1. -/
theorem norm_le_one_of_mem_adjoin_int {z : L} (hz1 : ‖z‖ ≤ 1)
    {s : L} (hs : s ∈ Algebra.adjoin ℤ ({z} : Set L)) : ‖s‖ ≤ 1 := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hz1
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ L) r]; exact IsUltrametricDist.norm_intCast_le_one L r
  | add x y _ _ hx hy =>
    exact le_trans (IsUltrametricDist.norm_add_le_max x y) (max_le hx hy)
  | mul x y _ _ hx hy =>
    rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- The quotient `ℤ[z] ⧸ p·ℤ[z]` of the subalgebra generated by an integral
element by the ideal `(p)` is finite: it is `ℤ`-module-finite (integrality)
and killed by `p`, hence a finitely generated torsion abelian group.
Decomposition R6 cluster W6a / Washington §5.1. -/
theorem finite_adjoin_int_quotient {z : L} (hz : IsIntegral ℤ z) :
    Finite ((Algebra.adjoin ℤ ({z} : Set L)) ⧸
      Ideal.span {(p : Algebra.adjoin ℤ ({z} : Set L))}) := by
  haveI : Module.Finite ℤ (Algebra.adjoin ℤ ({z} : Set L)) :=
    Module.Finite.of_fg hz.fg_adjoin_singleton
  haveI : Module.Finite ℤ
      ((Algebra.adjoin ℤ ({z} : Set L)) ⧸
        Ideal.span {(p : Algebra.adjoin ℤ ({z} : Set L))}) :=
    Module.Finite.quotient ℤ _
  haveI : Module.IsTorsion ℤ
      ((Algebra.adjoin ℤ ({z} : Set L)) ⧸
        Ideal.span {(p : Algebra.adjoin ℤ ({z} : Set L))}) := by
    intro x
    refine ⟨⟨(p : ℤ),
      mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hp.out.ne_zero)⟩, ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Submonoid.smul_def, zsmul_eq_mul]
    have hcast : ((p : ℤ) : (Algebra.adjoin ℤ ({z} : Set L)) ⧸
        Ideal.span {(p : Algebra.adjoin ℤ ({z} : Set L))})
        = Ideal.Quotient.mk _ (p : Algebra.adjoin ℤ ({z} : Set L)) := by
      push_cast; rw [map_natCast]
    rw [hcast, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  exact Module.finite_of_fg_torsion _ this

omit [CompleteSpace L] in
/-- W6a-a5 (pigeonhole): a norm-one element integral over `ℤ` has a power
within `p⁻¹` of `1` — `ℤ[z]/p` is finite, so `z^i(z^m − 1) ∈ p·ℤ[z]` for
some `i, m`, and `‖z^i‖ = 1` cancels.
Decomposition R6 cluster W6a / Washington §5.1. -/
theorem exists_pow_sub_one_norm_le {z : L} (hz : IsIntegral ℤ z)
    (hz1 : ‖z‖ = 1) : ∃ m : ℕ, 0 < m ∧ ‖z ^ m - 1‖ ≤ (p : ℝ)⁻¹ := by
  -- The `ℤ`-subalgebra `R = ℤ[z]` and the quotient `R ⧸ p·R`, which is finite.
  let R := Algebra.adjoin ℤ ({z} : Set L)
  let I : Ideal R := Ideal.span {(p : R)}
  haveI : Finite (R ⧸ I) := finite_adjoin_int_quotient p hz
  -- Pigeonhole `ℕ → R ⧸ p·R`, `n ↦ z^n`.
  have hzmem : z ∈ R := Algebra.subset_adjoin (Set.mem_singleton z)
  set f : ℕ → R ⧸ I := fun n => Ideal.Quotient.mk I (⟨z, hzmem⟩ ^ n)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
  -- WLOG `i < j`; set `m = j − i`.
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) hfij.symm (by omega)
  refine ⟨j - i, by omega, ?_⟩
  -- From `f i = f j`: the difference lies in `p·R`, i.e. `= p·s` for some `s ∈ R`.
  have hsub : (⟨z, hzmem⟩ ^ j - ⟨z, hzmem⟩ ^ i : R) ∈ I :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hfij.symm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hsub
  -- Push to `L`: `‖z^j − z^i‖ = ‖p‖·‖s‖ ≤ p⁻¹`.
  have hbound : ‖z ^ j - z ^ i‖ ≤ (p : ℝ)⁻¹ := by
    have hcoe : (z : L) ^ j - z ^ i = (p : L) * (s : L) := by
      have hval := congrArg (Subtype.val : R → L) hs
      push_cast at hval
      rw [← hval]; ring
    rw [hcoe, norm_mul, norm_natCast_p p]
    exact mul_le_of_le_one_right (by positivity)
      (norm_le_one_of_mem_adjoin_int hz1.le s.2)
  -- Factor `z^j − z^i = z^i (z^{j−i} − 1)`; `‖z^i‖ = 1`.
  have hfactor : z ^ j - z ^ i = z ^ i * (z ^ (j - i) - 1) := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
  have hnormi : ‖z ^ i‖ = 1 := by rw [norm_pow, hz1, one_pow]
  rwa [hfactor, norm_mul, hnormi, one_mul] at hbound

/-- The domain of the extended logarithm: rational-valuation elements, i.e.
`x^m = p^k·y` with `y` in the translated exponential ball. -/
def ExtLogDomain (x : L) : Prop :=
  ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y
    ∧ InExpBall p (y - 1)

open Classical in
/-- W6a-a6: the extended (Iwasawa-branch, `log_p p = 0`) logarithm,
junk-total: `extLog x = m⁻¹ • padicLog y` for a witness `x^m = p^k·y`,
and `0` off the domain. -/
noncomputable def extLog (x : L) : L :=
  if h : ExtLogDomain p x
  then ((h.choose : ℚ_[p]))⁻¹
    • padicLog p h.choose_spec.choose_spec.choose
  else 0

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- `(p : L) ≠ 0` (its norm is `p⁻¹ > 0`). Decomposition R6 cluster W6a. -/
theorem natCast_p_ne_zero : (p : L) ≠ 0 :=
  norm_ne_zero_iff.mp <| by
    rw [norm_natCast_p p]; have := hp.out.pos; positivity

/-- Two `extLog`-witnesses of the same element produce the same `ℚ_p`-scaled
logarithm. Raising `x^m = p^k·y` and `x^{m'} = p^{k'}·y'` to each other's
powers and matching `p`-valuations (norm-one of `y, y'`, injectivity of
`n ↦ (p⁻¹)^n`) forces `y^{m'} = y'^m`, whence `m'·log y = m·log y'`; dividing
by `m·m'` gives the claim. Decomposition R6 cluster W6a / Washington §5.1. -/
theorem extLog_witness_smul_eq {x : L} {m m' : ℕ} {k k' : ℤ} {y y' : L}
    (hm : 0 < m) (hm' : 0 < m') (hxy : x ^ m = (p : L) ^ k * y)
    (hxy' : x ^ m' = (p : L) ^ k' * y') (hy : InExpBall p (y - 1))
    (hy' : InExpBall p (y' - 1)) :
    ((m : ℚ_[p]))⁻¹ • padicLog p y = ((m' : ℚ_[p]))⁻¹ • padicLog p y' := by
  have hny : ‖y‖ = 1 := norm_eq_one_of_inExpBall_sub_one p hy
  have hny' : ‖y'‖ = 1 := norm_eq_one_of_inExpBall_sub_one p hy'
  have e1 : x ^ (m * m') = (p : L) ^ (k * m') * y ^ m' := by
    rw [pow_mul, hxy, mul_pow, ← zpow_natCast ((p : L) ^ k) m', ← zpow_mul]
  have e2 : x ^ (m * m') = (p : L) ^ (k' * m) * y' ^ m := by
    rw [mul_comm m m', pow_mul, hxy', mul_pow, ← zpow_natCast ((p : L) ^ k') m, ← zpow_mul]
  have ekey : (p : L) ^ (k * m') * y ^ m' = (p : L) ^ (k' * m) * y' ^ m := by
    rw [← e1, ← e2]
  have hnorm : ((p : ℝ)⁻¹) ^ (k * m') = ((p : ℝ)⁻¹) ^ (k' * m) := by
    have hc := congrArg norm ekey
    rwa [norm_mul, norm_mul, norm_zpow, norm_zpow, norm_natCast_p p, norm_pow,
      norm_pow, hny, hny', one_pow, one_pow, mul_one, mul_one] at hc
  have hpinv0 : (0 : ℝ) < (p : ℝ)⁻¹ := by have := hp.out.pos; positivity
  have hpinv1 : (p : ℝ)⁻¹ ≠ 1 :=
    ne_of_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hexp : k * m' = k' * m := zpow_right_injective₀ hpinv0 hpinv1 hnorm
  have hyeq : y ^ m' = y' ^ m :=
    mul_left_cancel₀ (zpow_ne_zero _ (natCast_p_ne_zero p)) (hexp ▸ ekey)
  have hlog := congrArg (padicLog p) hyeq
  rw [padicLog_pow p hy, padicLog_pow p hy'] at hlog
  have hmne : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm.ne'
  have hm'ne : (m' : ℚ_[p]) ≠ 0 := by exact_mod_cast hm'.ne'
  have hcast : (m' : ℚ_[p]) • padicLog p y = (m : ℚ_[p]) • padicLog p y' := by
    simpa only [Nat.cast_smul_eq_nsmul] using hlog
  rw [inv_smul_eq_iff₀ hmne, smul_comm, ← hcast, inv_smul_smul₀ hm'ne]

/-- W6a-a7 (well-definedness): every witness computes `extLog`. -/
theorem extLog_eq_of_witness {x : L} {m : ℕ} {k : ℤ} {y : L} (hm : 0 < m)
    (hxy : x ^ m = (p : L) ^ k * y) (hy : InExpBall p (y - 1)) :
    extLog p x = ((m : ℚ_[p]))⁻¹ • padicLog p y := by
  have hdom : ExtLogDomain p x := ⟨m, k, y, hm, hxy, hy⟩
  rw [extLog, dif_pos hdom]
  obtain ⟨hm₀, hxy₀, hy₀⟩ := hdom.choose_spec.choose_spec.choose_spec
  exact extLog_witness_smul_eq p hm₀ hm hxy₀ hxy hy₀ hy

omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- The centre `1` of the translated exponential ball is a member
(`‖0‖^{p−1} = 0 < p⁻¹`). Decomposition R6 cluster W6a. -/
theorem inExpBall_one_sub_one : InExpBall p ((1 : L) - 1) := by
  rw [sub_self, InExpBall, norm_zero, zero_pow (by have := hp.out.one_lt; omega)]
  exact inv_pos.mpr (by exact_mod_cast hp.out.pos)

/-- W6a-a8: `extLog` agrees with `padicLog` on the ball. -/
theorem extLog_eq_padicLog {x : L} (hx : InExpBall p (x - 1)) :
    extLog p x = padicLog p x := by
  rw [extLog_eq_of_witness p one_pos (by rw [pow_one, zpow_zero, one_mul]) hx,
    Nat.cast_one, inv_one, one_smul]

/-- W6a-a9: additivity on the domain. -/
theorem extLog_mul {x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) :
    extLog p (x * y) = extLog p x + extLog p y := by
  obtain ⟨m, k, a, hm, hxy, ha⟩ := hx
  obtain ⟨m', k', b, hm', hxy', hb⟩ := hy
  have hpL : (p : L) ≠ 0 := natCast_p_ne_zero p
  -- product witness `(x·y)^(m·m') = p^(k m' + k' m)·(a^{m'}·b^m)`
  have hball : InExpBall p (a ^ m' * b ^ m - 1) :=
    mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)
  have hprod : (x * y) ^ (m * m')
      = (p : L) ^ (k * m' + k' * m) * (a ^ m' * b ^ m) := by
    rw [mul_pow, pow_mul x m m', hxy, mul_pow, mul_comm m m', pow_mul y m' m, hxy',
      mul_pow, ← zpow_natCast ((p : L) ^ k) m', ← zpow_mul,
      ← zpow_natCast ((p : L) ^ k') m, ← zpow_mul, zpow_add₀ hpL]
    ring
  -- evaluate the three logarithms and expand `log(a^{m'}·b^m)`
  rw [extLog_eq_of_witness p hm hxy ha, extLog_eq_of_witness p hm' hxy' hb,
    extLog_eq_of_witness p (Nat.mul_pos hm hm') hprod hball,
    padicLog_mul p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m),
    padicLog_pow p ha, padicLog_pow p hb]
  -- `ℚ_p`-scalar algebra
  have hmne : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm.ne'
  have hm'ne : (m' : ℚ_[p]) ≠ 0 := by exact_mod_cast hm'.ne'
  rw [Nat.cast_mul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ_[p] m' (padicLog p a),
    ← Nat.cast_smul_eq_nsmul ℚ_[p] m (padicLog p b), smul_smul, smul_smul, mul_inv]
  congr 1 <;> congr 1 <;> field_simp

omit [CompleteSpace L] in
/-- The extended-log domain is closed under multiplication (the product witness of
`extLog_mul`). -/
theorem ExtLogDomain.mul {x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) :
    ExtLogDomain p (x * y) := by
  obtain ⟨m, k, a, hm, hxy, ha⟩ := hx
  obtain ⟨m', k', b, hm', hxy', hb⟩ := hy
  have hpL : (p : L) ≠ 0 := natCast_p_ne_zero p
  refine ⟨m * m', k * m' + k' * m, a ^ m' * b ^ m, Nat.mul_pos hm hm', ?_,
    mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)⟩
  rw [mul_pow, pow_mul x m m', hxy, mul_pow, mul_comm m m', pow_mul y m' m, hxy',
    mul_pow, ← zpow_natCast ((p : L) ^ k) m', ← zpow_mul,
    ← zpow_natCast ((p : L) ^ k') m, ← zpow_mul, zpow_add₀ hpL]
  ring

omit [CompleteSpace L] in
/-- The extended-log domain is closed under finite products. -/
theorem ExtLogDomain.prod {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i ∈ s, ExtLogDomain p (f i)) : ExtLogDomain p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, 0, 1, one_pos, by rw [Finset.prod_empty, one_pow, zpow_zero, one_mul],
      inExpBall_one_sub_one p⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact ExtLogDomain.mul p (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- W6a-a9 (Finset form): additivity over a finite product of domain elements
(`extLog (∏ f) = ∑ extLog ∘ f`). Drives the `μ_p`-collapse
`Σ_{i<p} extLog(ξ^i w − 1) = extLog(w^p − 1)` in the trace. -/
theorem extLog_prod {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i ∈ s, ExtLogDomain p (f i)) :
    extLog p (∏ i ∈ s, f i) = ∑ i ∈ s, extLog p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty,
      extLog_eq_padicLog p (inExpBall_one_sub_one p), padicLog_one]
  | insert i s hi ih =>
    have hdom : ∀ j ∈ s, ExtLogDomain p (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      extLog_mul p (hf i (Finset.mem_insert_self i s)) (ExtLogDomain.prod p s f hdom), ih hdom]

/-- W6a-a10: roots of unity have extended logarithm `0`. -/
theorem extLog_eq_zero_of_pow_eq_one {x : L} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n = 1) : extLog p x = 0 := by
  rw [extLog_eq_of_witness p hn (by rw [hx, zpow_zero, one_mul])
      (inExpBall_one_sub_one p), padicLog_one, smul_zero]

/-- W6a-a10 (continued): `log_p(x) = log_p(−x)` (RJW's final step,
TeX 2150). -/
theorem extLog_neg {x : L} (hx : ExtLogDomain p x) :
    extLog p (-x) = extLog p x := by
  -- `−1` lies in the domain: `(−1)^2 = 1 = p^0·1`.
  have hneg1 : ExtLogDomain p (-1 : L) :=
    ⟨2, 0, 1, two_pos, by rw [neg_one_sq, zpow_zero, one_mul], inExpBall_one_sub_one p⟩
  rw [show (-x : L) = (-1) * x by rw [neg_one_mul], extLog_mul p hneg1 hx,
    extLog_eq_zero_of_pow_eq_one p two_pos (neg_one_sq (R := L)), zero_add]

omit [CompleteSpace L] in
/-- W6a-a11 (the domain engine): norm-one elements integral over `ℤ` lie in
the extended-log domain — covers all the arguments `1 − ε_N^c` of RJW
Thm 6.1(ii) for tame conductor `D > 1`. -/
theorem extLogDomain_of_integral_norm_one {z : L} (hz : IsIntegral ℤ z)
    (hz1 : ‖z‖ = 1) : ExtLogDomain p z := by
  obtain ⟨m, hm, hmle⟩ := exists_pow_sub_one_norm_le p hz hz1
  have hlt : ‖z ^ m - 1‖ < 1 :=
    lt_of_le_of_lt hmle (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall p hlt
  refine ⟨m * p ^ j, 0, z ^ (m * p ^ j),
    Nat.mul_pos hm (pow_pos hp.out.pos j), ?_, ?_⟩
  · rw [zpow_zero, one_mul]
  · rwa [pow_mul]

end PadicLFunctions
