/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.NumberTheory.Padics.AddChar
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Topology.Algebra.LinearTopology

/-!
# Coefficient rings for §5: the integer ring of a nonarchimedean field

RJW fix once and for all a finite extension `L/ℚ_p` with ring of integers `𝒪_L`
(§3.1, TeX 680–690; the requirement becomes essential in §5, TeX 1781: "the
relevant Iwasawa algebra is defined over a (fixed) finite extension L/Q_p
containing the values of η"). We work with the maximal natural generality the
§3 measure theory supports: a normed field `L` that is a nonarchimedean complete
normed `ℚ_[p]`-algebra, and its norm-unit ball `integerRing L`. Finite
extensions of `ℚ_p` and `ℂ_p` are both instances.

Main declarations:
* `PadicLFunctions.integerRing L` — the unit ball `{x : L | ‖x‖ ≤ 1}` as a
  subring (W1 in `.mathlib-quality/decomposition.md` §5).
* `IsPrimitiveRoot.norm_sub_one_lt` — `‖ζ − 1‖ < 1` for `ζ` a primitive
  `p^n`-th root of unity (W2); hence `ζ − 1` is topologically nilpotent.
* `IsPrimitiveRoot.norm_pow_sub_one_eq_one` — `‖ζ^c − 1‖ = 1` for `ζ` a
  primitive `D`-th root, `p ∤ D`, `D ∤ c` (W3; TeX 1798).
-/

open Filter Topology

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

/-- The integer ring (norm-unit ball) of a nonarchimedean normed field. For a
finite extension `L/ℚ_p` this is `𝒪_L` (RJW §3.1, TeX 690). -/
def integerRing : Subring L where
  carrier := {x : L | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by simpa using mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by simp
  add_mem' {x y} hx hy := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx

namespace integerRing

instance : IsUltrametricDist (integerRing L) :=
  ⟨fun x y z => by simpa [Subtype.dist_eq] using IsUltrametricDist.dist_triangle_max (x : L) y z⟩

instance : CompleteSpace (integerRing L) :=
  completeSpace_coe_iff_isComplete.2 <|
    IsClosed.isComplete (by
      simpa [integerRing] using isClosed_le (by fun_prop) continuous_const)

/-- `ℤ_[p]` maps into the unit ball: `‖algebraMap ℚ_[p] L x‖ = ‖x‖ ≤ 1`. -/
noncomputable instance : Algebra ℤ_[p] (integerRing L) :=
  RingHom.toAlgebra <|
    ((algebraMap ℚ_[p] L).comp PadicInt.Coe.ringHom).codRestrict (integerRing L) fun x =>
      show ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ ≤ 1 by rw [norm_algebraMap']; exact x.norm_le_one

/-- The closed ball of radius `ε` in the integer ring, as an ideal — the norm
is ultrametric and multiplicative, so the balls absorb multiplication by the
unit ball. -/
noncomputable def ballIdeal (ε : ℝ) : Ideal (integerRing L) where
  carrier := {x : integerRing L | ‖(x : L)‖ ≤ max ε 0}
  add_mem' {x y} hx hy := (IsUltrametricDist.norm_add_le_max (x : L) y).trans (max_le hx hy)
  zero_mem' := by simp
  smul_mem' r x hx := by
    change ‖((r * x : integerRing L) : L)‖ ≤ max ε 0
    rw [MulMemClass.coe_mul, norm_mul]
    exact (mul_le_mul r.2 hx (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- The norm topology on the integer ring is linear: the balls
`{x | ‖x‖ ≤ ε}` are ideals (ultrametric + multiplicative norm). Needed for
`PowerSeries.eval₂`-substitution into `(integerRing L)⟦T⟧` (L5.1.6a). -/
instance : IsLinearTopology (integerRing L) (integerRing L) := by
  refine IsLinearTopology.mk_of_hasBasis' (integerRing L)
    (S := Ideal (integerRing L)) (p := fun ε : ℝ => 0 < ε)
    (s := fun ε => ballIdeal L ε) ?_ fun s r m hm => s.smul_mem r hm
  refine (Metric.nhds_basis_closedBall (α := integerRing L) (x := 0)).congr
    (fun ε => Iff.rfl) fun ε hε => ?_
  ext x
  simp [ballIdeal, Metric.mem_closedBall, dist_zero_right, max_eq_left hε.le,
    AddSubgroupClass.coe_norm]

omit [CompleteSpace L] in
/-- The algebra map `ℤ_[p] → integerRing L` is an isometry (it is the
restriction of the scalar embedding `ℚ_[p] → L`). -/
lemma norm_algebraMap_eq (x : ℤ_[p]) :
    ‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖ := by
  change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖
  rw [norm_algebraMap', PadicInt.norm_def]

omit [CompleteSpace L] in
lemma isometry_algebraMap : Isometry (algebraMap ℤ_[p] (integerRing L)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)

omit [CompleteSpace L] in
instance : IsBoundedSMul ℤ_[p] (integerRing L) :=
  .of_norm_smul_le fun r x => by
    rw [Algebra.smul_def]
    exact (norm_mul_le _ _).trans_eq (by rw [norm_algebraMap_eq])

end integerRing

variable {p L}

/-- A normed `ℚ_[p]`-algebra field has characteristic zero (not an instance:
`p` is not determined by the goal — cite per use site). -/
lemma charZero_of_qpAlgebra (q : ℕ) [Fact q.Prime] {M : Type*} [NormedField M]
    [NormedAlgebra ℚ_[q] M] : CharZero M :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[q] M).injective

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- Elements of norm `< 1` are not units of the integer ring. -/
theorem integerRing.not_isUnit_of_norm_lt_one {x : integerRing L}
    (hx : ‖(x : L)‖ < 1) : ¬ IsUnit x := fun h => by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  have h1 : (x : L) * (y : L) = 1 := by exact_mod_cast congrArg Subtype.val hy
  have h2 : ‖(x : L)‖ * ‖(y : L)‖ = 1 := by rw [← norm_mul, h1, norm_one]
  nlinarith [mul_le_of_le_one_right (norm_nonneg (x : L)) y.2]

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- An element of the integer ring of norm one is a unit: its field inverse
again has norm one, hence lies in the integer ring. -/
theorem integerRing.isUnit_of_norm_eq_one {x : integerRing L}
    (hx : ‖(x : L)‖ = 1) : IsUnit x := by
  have hx0 : (x : L) ≠ 0 := norm_ne_zero_iff.1 (by rw [hx]; exact one_ne_zero)
  refine IsUnit.of_mul_eq_one
    ⟨(x : L)⁻¹, show ‖(x : L)⁻¹‖ ≤ 1 by rw [norm_inv, hx, inv_one]⟩ ?_
  exact Subtype.ext (mul_inv_cancel₀ hx0)

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- In a normed `ℚ_[p]`-algebra, `‖p‖ = p⁻¹ < 1` (the algebra map is an
isometry on scalars). -/
theorem norm_natCast_self_lt_one : ‖((p : ℕ) : L)‖ < 1 := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) by simp [map_natCast],
    norm_algebraMap']
  simpa using Padic.norm_p_lt_one (p := p)

omit [CompleteSpace L] in
/-- W2: a primitive `p^n`-th root of unity satisfies `‖ζ − 1‖ < 1`; in
particular `ζ − 1` is topologically nilpotent and `x ↦ ζ^x` extends to a
continuous additive character of `ℤ_[p]` (mathlib
`PadicInt.addChar_of_value_at_one`). Classical; cf. RJW's use of `μ_{p^n}`
throughout §5.1 (TeX 1647–1692). -/
theorem _root_.IsPrimitiveRoot.norm_sub_one_lt {ζ : L} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) : ‖ζ - 1‖ < 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `IsPrimitiveRoot ζ (p ^ 0) = IsPrimitiveRoot ζ 1`, so `ζ = 1`.
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    simp [hζ]
  by_contra hcon
  push Not at hcon
  set x : L := ζ - 1 with hxdef
  set N : ℕ := p ^ n
  have hN2 : 2 ≤ N := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
  -- binomial expansion of `1 = ζ^N = (x+1)^N`, with the `k = 0` term peeled off
  have hpow : ∑ k ∈ Finset.range N, x ^ (k + 1) * ((N.choose (k + 1) : ℕ) : L) = 0 := by
    have h1 : (x + 1) ^ N = 1 := by simpa [hxdef] using hζ.pow_eq_one
    have hexp := add_pow x 1 N
    rw [h1, Finset.sum_range_succ'] at hexp
    simpa using hexp.symm
  -- isolate the top term `x^N`
  have htop : x ^ N
      = -∑ k ∈ Finset.range (N - 1), x ^ (k + 1) * ((N.choose (k + 1) : ℕ) : L) := by
    have hsplit := Finset.sum_range_succ
      (fun k => x ^ (k + 1) * ((N.choose (k + 1) : ℕ) : L)) (N - 1)
    rw [show N - 1 + 1 = N by omega, hpow] at hsplit
    simp only [Nat.choose_self, Nat.cast_one, mul_one] at hsplit
    exact eq_neg_of_add_eq_zero_right hsplit.symm
  -- ultrametric bound: the sum is dominated by one of its terms
  obtain ⟨i, hi, hile⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := Finset.range (N - 1)) ⟨0, Finset.mem_range.2 (by omega)⟩
    (fun k => x ^ (k + 1) * ((N.choose (k + 1) : ℕ) : L))
  -- each coefficient is divisible by `p`
  have hilt := Finset.mem_range.1 hi
  obtain ⟨m, hm⟩ : (p : ℕ) ∣ N.choose (i + 1) := hp.out.dvd_choose_pow (by omega) (by omega)
  have hcoeff : ‖((N.choose (i + 1) : ℕ) : L)‖ ≤ ‖((p : ℕ) : L)‖ := by
    rw [hm, Nat.cast_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one L m)
  -- assemble the contradiction `‖x‖^N ≤ ‖p‖·‖x‖^N < ‖x‖^N`
  have hxpos : (0 : ℝ) < ‖x‖ ^ N := pow_pos (one_pos.trans_le hcon) N
  have hbound : ‖x‖ ^ N ≤ ‖((p : ℕ) : L)‖ * ‖x‖ ^ N := by
    calc ‖x‖ ^ N = ‖x ^ N‖ := (norm_pow x N).symm
      _ ≤ ‖x ^ (i + 1) * ((N.choose (i + 1) : ℕ) : L)‖ := by
          rw [htop, norm_neg]; exact hile
      _ = ‖x‖ ^ (i + 1) * ‖((N.choose (i + 1) : ℕ) : L)‖ := by
          rw [norm_mul, norm_pow]
      _ ≤ ‖x‖ ^ N * ‖((p : ℕ) : L)‖ :=
          mul_le_mul (pow_le_pow_right₀ hcon (by omega)) hcoeff (norm_nonneg _) (by positivity)
      _ = ‖((p : ℕ) : L)‖ * ‖x‖ ^ N := mul_comm _ _
  have hple : (1 : ℝ) ≤ ‖((p : ℕ) : L)‖ :=
    le_of_mul_le_mul_right (by simpa using hbound) hxpos
  exact (hple.trans_lt norm_natCast_self_lt_one).false

omit [CompleteSpace L] in
/-- W2': hence `ζ - 1` is topologically nilpotent (powers tend to `0`). -/
theorem _root_.IsPrimitiveRoot.tendsto_pow_sub_one {ζ : L} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    Tendsto ((ζ - 1) ^ ·) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt)

omit [CompleteSpace L] in
/-- W3: for `ζ` a primitive `D`-th root of unity with `p ∤ D` and `D ∤ c`,
the element `ζ^c − 1` has norm one (hence is a unit of the integer ring).

Source (TeX 1798): "and `ε_D^c − 1 ∈ 𝒪_L^×` (since it has norm dividing
`D`)". -/
theorem _root_.IsPrimitiveRoot.norm_pow_sub_one_eq_one {ζ : L} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    ‖ζ ^ c - 1‖ = 1 := by
  have hD0 : D ≠ 0 := fun h => hD (h ▸ dvd_zero _)
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  -- all the factors `1 - ζ^(k+1)` have norm at most one
  have hζ1 : ‖ζ‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg ζ) (Nat.succ_ne_zero n), ← norm_pow,
      hζ.pow_eq_one, norm_one]
  have hfac : ∀ k, ‖1 - ζ ^ (k + 1)‖ ≤ 1 := fun k => by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max 1 _).trans (by simp [norm_pow, hζ1])
  -- the product of the factors is `D`, whose norm is one since `p ∤ D`
  have hprodD : ‖∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))‖ = 1 := by
    rw [hζ.prod_one_sub_pow_eq_order,
      show ((n : L) + 1) = algebraMap ℚ_[p] L ((n + 1 : ℕ) : ℚ_[p]) by push_cast [map_natCast]; ring,
      norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hD
  -- hence every individual factor has norm exactly one
  have hone : ∀ i ∈ Finset.range n, ‖1 - ζ ^ (i + 1)‖ = 1 := by
    intro i hi
    refine le_antisymm (hfac i) ?_
    have hP : ∏ k ∈ Finset.range n, ‖1 - ζ ^ (k + 1)‖ = 1 := by rw [← norm_prod]; exact hprodD
    have hsplit : ‖1 - ζ ^ (i + 1)‖ *
        ∏ k ∈ (Finset.range n).erase i, ‖1 - ζ ^ (k + 1)‖ = 1 :=
      (Finset.mul_prod_erase _ (fun k => ‖1 - ζ ^ (k + 1)‖) hi).trans hP
    nlinarith [hsplit, norm_nonneg (1 - ζ ^ (i + 1)),
      Finset.prod_le_one (s := (Finset.range n).erase i)
        (fun k _ => norm_nonneg (1 - ζ ^ (k + 1))) (fun k _ => hfac k),
      Finset.prod_nonneg
        (fun k (_ : k ∈ (Finset.range n).erase i) => norm_nonneg (1 - ζ ^ (k + 1)))]
  -- reduce the exponent mod `D` and read off the factor
  have hred : ζ ^ c = ζ ^ (c % (n + 1)) := by
    nth_rewrite 1 [← Nat.div_add_mod c (n + 1)]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hr0 : c % (n + 1) ≠ 0 := fun h => hc (Nat.dvd_of_mod_eq_zero h)
  have hrlt : c % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
  obtain ⟨r, hr⟩ : ∃ r, c % (n + 1) = r + 1 := ⟨c % (n + 1) - 1, by omega⟩
  rw [hred, hr, ← norm_neg, neg_sub]
  exact hone r (Finset.mem_range.2 (by omega))

end PadicLFunctions
