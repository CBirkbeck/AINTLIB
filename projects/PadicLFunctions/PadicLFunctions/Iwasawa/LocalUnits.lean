/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Theorem
import Mathlib.NumberTheory.Padics.AddChar

/-!
# Local unit groups of the cyclotomic tower (RJW §9, TeX 2471–2505)

The §9 notation that comes due at §11 (plan.md deferral): the local unit groups
`𝒰_n = 𝒪_{K_n}^×` and the principal units `𝒰_{n,1} = {u ∈ 𝒰_n : u ≡ 1 mod 𝔭_n}`
as subgroups of `ℂ_[p]ˣ` (the tower lives inside `ℂ_p`, decomposition R10.1/R11.7);
the `+`-subfield `K_n⁺ = ℚ_p(ξ + ξ⁻¹)` and the `⁺`-variants; the `ℤ_p`-power
structure `u^a` on principal units (RJW TeX 2494–2496: "`u^a = Σ (a choose k)(u−1)^k`
converges"); the group structure on the norm-compatible systems `𝒰_∞`
(`NormCompatUnits`, upgraded from `Mul`/`One` to `CommGroup`); and the towers
`𝒰_{∞,1} = lim←_{n≥1} 𝒰_{n,1}` and `𝒰⁺_{∞,1}` (RJW TeX 2503–2505).

The congruence `u ≡ 1 (mod 𝔭_n)` is rendered as `‖u − 1‖ < 1` (replan R11.6:
`𝔭_n` is the open unit ball of the unit-ball ring `O_n`). The `ℤ_p`-power is
mathlib's `PadicInt.addChar_of_value_at_one` applied to `r = u − 1` — literally the
source's binomial series.
-/

open scoped IntermediateField Topology

open Filter

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The unit groups 𝒰_n and 𝒰_{n,1} (RJW TeX 2474, 2494) -/

/-- `𝒰_n = 𝒪_{K_n}^×`: the units of the integer ring of `K_n`, as a subgroup of
`ℂ_[p]ˣ` (a unit together with its inverse lies in `O_n`). RJW TeX 2474. -/
def localUnits (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n}
  mul_mem' {u v} hu hv := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact mul_mem hu.1 hv.1
    · rw [mul_inv_rev, Units.val_mul]
      exact mul_mem hv.2 hu.2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]; exact one_mem _
    · rw [inv_one, Units.val_one]; exact one_mem _
  inv_mem' {u} hu := by
    refine ⟨hu.2, ?_⟩
    rw [inv_inv]; exact hu.1

lemma mem_localUnits_iff {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnits p n
      ↔ (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n :=
  Iff.rfl

/-- Units of `O_n` have norm exactly `1` (and conversely for elements of `K_n`). -/
lemma norm_eq_one_of_mem_localUnits {n : ℕ} {u : ℂ_[p]ˣ} (hu : u ∈ localUnits p n) :
    ‖(u : ℂ_[p])‖ = 1 := by
  have hu1 : ‖(u : ℂ_[p])‖ ≤ 1 := (Subring.mem_inf.1 hu.1).2
  have hu2 : ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ ≤ 1 := (Subring.mem_inf.1 hu.2).2
  have hprod : ‖(u : ℂ_[p])‖ * ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  nlinarith [norm_nonneg (u : ℂ_[p]), norm_nonneg ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])]

/-- `𝒰_{n,1} = {u ∈ 𝒰_n : u ≡ 1 (mod 𝔭_n)}`: the principal units, with the
congruence rendered as `‖u − 1‖ < 1` (replan R11.6). RJW Eq. (`eq:U1`), TeX 2494. -/
def localUnitsOne (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1}
  mul_mem' {u v} hu hv := by
    refine ⟨mul_mem hu.1 hv.1, ?_⟩
    -- `uv − 1 = u·(v − 1) + (u − 1)`, dominated by the max of the two norms `< 1`
    have hkey : (↑(u * v) : ℂ_[p]) - 1 = (u : ℂ_[p]) * ((v : ℂ_[p]) - 1) + ((u : ℂ_[p]) - 1) := by
      rw [Units.val_mul]; ring
    rw [hkey]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hu.2)
    rw [norm_mul, norm_eq_one_of_mem_localUnits p hu.1, one_mul]
    exact hv.2
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    rw [Units.val_one, sub_self, norm_zero]
    exact one_pos
  inv_mem' {u} hu := by
    refine ⟨(localUnits p n).inv_mem hu.1, ?_⟩
    -- `u⁻¹ − 1 = u⁻¹·(1 − u)`, and `‖u⁻¹‖ = 1`, so the norm equals `‖u − 1‖ < 1`
    have hu0 : (u : ℂ_[p]) ≠ 0 := u.ne_zero
    have hkey : ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) - 1
        = ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (1 - (u : ℂ_[p])) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
    rw [hkey, norm_mul,
      norm_eq_one_of_mem_localUnits p ((localUnits p n).inv_mem hu.1), one_mul, norm_sub_rev]
    exact hu.2

lemma mem_localUnitsOne_iff {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnitsOne p n ↔ u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) - 1‖ < 1 :=
  Iff.rfl

/-! ## The maximal totally real subfield K_n⁺ and the ⁺-variants (RJW TeX 2473–2475) -/

/-- `K_n⁺ = ℚ_p(ξ_{p^n} + ξ_{p^n}⁻¹)`: the "+"-subfield, rendered by its standard
concrete generator (the fixed points of `ξ ↦ ξ⁻¹`). The Galois characterisation
`K_n⁺ = (K_n)^{⟨σ_{-1}⟩}` (§12 material) is now proved as `KPlus_eq_fixedField`
(`IwasawaProof/GaloisAction.lean`), with the unit-level form
`mem_localUnitsOnePlus_iff_galAut_fixed`. RJW TeX 2473. -/
noncomputable def KPlus (n : ℕ) : IntermediateField ℚ_[p] ℂ_[p] :=
  ℚ_[p]⟮zetaSys p n + (zetaSys p n)⁻¹⟯

lemma KPlus_le_K (n : ℕ) : KPlus p n ≤ K p n := by
  rw [KPlus, IntermediateField.adjoin_simple_le_iff]
  exact add_mem (zetaSys_mem_K p n) ((K p n).inv_mem (zetaSys_mem_K p n))

/-- `𝒰_n⁺ = 𝒪_{K_n⁺}^×`, realised as the `K_n⁺`-valued local units (a unit of `O_n`
lying in `K_n⁺` is a unit of `𝒪_{K_n⁺}`). RJW TeX 2474 with the X⁺-convention of
TeX 2498. -/
noncomputable def localUnitsPlus (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | u ∈ localUnits p n ∧ (u : ℂ_[p]) ∈ KPlus p n}
  mul_mem' {u v} hu hv := by
    refine ⟨mul_mem hu.1 hv.1, ?_⟩
    rw [Units.val_mul]
    exact mul_mem hu.2 hv.2
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    rw [Units.val_one]
    exact one_mem _
  inv_mem' {u} hu := by
    refine ⟨(localUnits p n).inv_mem hu.1, ?_⟩
    rw [Units.val_inv_eq_inv_val]
    exact (KPlus p n).inv_mem hu.2

/-- `𝒰⁺_{n,1} = 𝒰_{n,1} ∩ 𝒰_n⁺` (RJW TeX 2494). -/
noncomputable def localUnitsOnePlus (n : ℕ) : Subgroup ℂ_[p]ˣ :=
  localUnitsOne p n ⊓ localUnitsPlus p n

/-! ## The ℤ_p-power structure on principal units (RJW TeX 2494–2496)

"The subsets `𝒰_{n,1}` and `𝒰⁺_{n,1}` are important as they have the structure of
`ℤ_p`-modules (indeed, if `u ∈ 𝒰_{n,1}` … and `a ∈ ℤ_p`, then
`u^a = Σ_{k≥0} (a choose k)(u−1)^k` converges)."

File-local infrastructure for `zpPow` (T1109): `ℂ_[p]` is `Completion (PadicAlgCl p)`,
on which the `ℤ_[p]`-scalar action exists (the `ℚ_[p]`-action restricted along
`ℤ_[p] → ℚ_[p]`, definitionally) but is not registered as a `Module`. The single
missing piece is `UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p)`; supplying it
unlocks mathlib's `Module`/`Algebra ℤ_[p] ℂ_[p]` (the Completion instances) so that
`PadicInt.addChar_of_value_at_one` applies. The induced scalar multiplication is
`c • x = toCp p c * x` (`smul_cp_eq`), giving the bounded-action instance via
`norm_toCp`. (Cleanup ticket: these are globally useful — promote to `Coleman` or a
suitable mathlib home.) -/

/-- File-local: the `ℤ_[p]`-scalar action on `PadicAlgCl p` (the
`ℚ_[p]`-action restricted along `ℤ_[p] → ℚ_[p]`) is uniformly continuous, the one
fact mathlib needs to build `Module`/`Algebra ℤ_[p] ℂ_[p]` on the completion. -/
instance instUCCSMulZpAlgCl : UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) :=
  ⟨fun c => uniformContinuous_const_smul (c : ℚ_[p])⟩

/-- The induced `ℤ_[p]`-scalar action on `ℂ_[p]` is multiplication by `toCp p c`. -/
theorem smul_cp_eq (c : ℤ_[p]) (x : ℂ_[p]) : c • x = toCp p c * x := by
  rw [Algebra.smul_def]; congr 1

/-- File-local: the `ℤ_[p]`-action on `ℂ_[p]` is bounded (`‖c • x‖ = ‖c‖·‖x‖`,
since `toCp` is isometric), the last instance `addChar_of_value_at_one` needs. -/
noncomputable instance instBddSMulZpCp : IsBoundedSMul ℤ_[p] ℂ_[p] :=
  IsBoundedSMul.of_norm_smul_le fun c x => by rw [smul_cp_eq, norm_mul, norm_toCp]

/-- The `ℤ_p`-power `y^a` of a `1`-unit `y` of `ℂ_[p]` (junk value `1` when
`‖y − 1‖ ≥ 1`): mathlib's continuous additive character `a ↦ (1 + (y−1))^a`
(`PadicInt.addChar_of_value_at_one`) — the source's binomial series. -/
noncomputable def zpPow (y : ℂ_[p]) (a : ℤ_[p]) : ℂ_[p] :=
  open Classical in
  if h : Filter.Tendsto ((y - 1) ^ ·) Filter.atTop (nhds 0) then
    PadicInt.addChar_of_value_at_one (y - 1) h a
  else 1

/-- For a `1`-unit `y`, the powers `(y − 1)^k → 0` (`‖y − 1‖ < 1`), so the
`dif_pos` branch of `zpPow` fires. -/
private theorem tendsto_pow_of_norm_lt_one {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) :
    Tendsto ((y - 1) ^ ·) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hy

/-- For `‖y − 1‖ < 1`, `zpPow` unfolds to the additive character (no junk branch). -/
private theorem zpPow_def {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    zpPow p y a
      = PadicInt.addChar_of_value_at_one (y - 1) (tendsto_pow_of_norm_lt_one p hy) a := by
  rw [zpPow, dif_pos (tendsto_pow_of_norm_lt_one p hy)]

/-- On natural exponents, `zpPow` is the usual power (the source's
"`u^a` extends `u^k`"). -/
theorem zpPow_natCast {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (k : ℕ) :
    zpPow p y (k : ℤ_[p]) = y ^ k := by
  rw [zpPow_def p hy]
  change PadicInt.mahlerSeries ((y - 1) ^ ·) (k : ℤ_[p]) = _
  rw [show y ^ k = ((y - 1) + 1) ^ k by rw [sub_add_cancel],
    PadicInt.mahlerSeries_apply_nat (tendsto_pow_of_norm_lt_one p hy) le_rfl,
    (Commute.one_right (y - 1)).add_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [one_pow, mul_one, nsmul_eq_mul, Nat.cast_comm]

/-- The character law `y^{a+b} = y^a·y^b`. -/
theorem zpPow_add {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow p y (a + b) = zpPow p y a * zpPow p y b := by
  rw [zpPow_def p hy, zpPow_def p hy, zpPow_def p hy]
  exact AddChar.map_add_eq_mul _ a b

/-- `zpPow p y` is continuous in the exponent (it is the continuous additive
character). -/
private theorem continuous_zpPow {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) :
    Continuous (zpPow p y) := by
  have h : zpPow p y =
      (PadicInt.addChar_of_value_at_one (y - 1) (tendsto_pow_of_norm_lt_one p hy) :
        ℤ_[p] → ℂ_[p]) :=
    funext (zpPow_def p hy)
  rw [h]
  exact PadicInt.continuous_addChar_of_value_at_one _

/-- Density transfer: a closed set containing every natural power `y^k` contains
every `ℤ_p`-power `y^a` (the naturals are dense in `ℤ_[p]` and `zpPow p y` is
continuous). Used for the norm bound, the subfield-stability, and the unit-ball
membership. -/
private theorem zpPow_mem_of_closed {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) {S : Set ℂ_[p]}
    (hS : IsClosed S) (hnat : ∀ k : ℕ, y ^ k ∈ S) (a : ℤ_[p]) : zpPow p y a ∈ S := by
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[p]) ⊆ zpPow p y ⁻¹' S := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_preimage, zpPow_natCast p hy]
    exact hnat k
  have huniv : zpPow p y ⁻¹' S = Set.univ := by
    rw [← Set.univ_subset_iff, ← PadicInt.denseRange_natCast.closure_range]
    exact (hS.preimage (continuous_zpPow p hy)).closure_subset_iff.mpr hsub
  have : a ∈ zpPow p y ⁻¹' S := by rw [huniv]; trivial
  exact this

/-- `zpPow` stays in the `1`-unit ball: `‖y^a − 1‖ ≤ ‖y − 1‖ < 1`. -/
theorem norm_zpPow_sub_one_lt_one {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow p y a - 1‖ < 1 := by
  have hyle : ‖y‖ ≤ 1 := by
    rw [show y = (y - 1) + 1 by ring]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (by simp [hy.le])
  -- `y^a` lies in the closed ball `{z : ‖z − 1‖ ≤ ‖y − 1‖}`, by the telescope
  -- `‖y^k − 1‖ ≤ ‖y − 1‖` (ultrametric, `‖y‖ ≤ 1`).
  have hball : zpPow p y a ∈ {z : ℂ_[p] | ‖z - 1‖ ≤ ‖y - 1‖} := by
    refine zpPow_mem_of_closed p hy (isClosed_le (by fun_prop) continuous_const)
      (fun k => ?_) a
    simp only [Set.mem_setOf_eq]
    induction k with
    | zero => simp
    | succ m ih =>
      rw [show y ^ (m + 1) - 1 = y * (y ^ m - 1) + (y - 1) by ring]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ le_rfl)
      rw [norm_mul]
      calc ‖y‖ * ‖y ^ m - 1‖ ≤ 1 * ‖y - 1‖ := mul_le_mul hyle ih (norm_nonneg _) zero_le_one
        _ = ‖y - 1‖ := one_mul _
  exact lt_of_le_of_lt hball hy

/-- The power law `(y^a)^b = y^{ab}` (so the action is a `ℤ_[p]`-module action). -/
theorem zpPow_mul {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow p y (a * b) = zpPow p (zpPow p y a) b := by
  have hya : ‖zpPow p y a - 1‖ < 1 := norm_zpPow_sub_one_lt_one p hy a
  -- Both sides are continuous in `b` and agree on `b ∈ ℕ`; conclude by density.
  have hnat : ∀ k : ℕ, zpPow p y (a * (k : ℤ_[p])) = zpPow p (zpPow p y a) (k : ℤ_[p]) := by
    intro k
    rw [zpPow_natCast p hya]
    induction k with
    | zero =>
      rw [Nat.cast_zero, mul_zero, pow_zero, ← Nat.cast_zero (R := ℤ_[p]),
        zpPow_natCast p hy, pow_zero]
    | succ m ih => rw [Nat.cast_succ, mul_add, mul_one, zpPow_add p hy, ih, pow_succ]
  have hcont1 : Continuous (fun b => zpPow p y (a * b)) :=
    (continuous_zpPow p hy).comp (continuous_const.mul continuous_id)
  have heq : (fun b => zpPow p y (a * b)) = (fun b => zpPow p (zpPow p y a) b) :=
    PadicInt.denseRange_natCast.equalizer hcont1 (continuous_zpPow p hya) (funext hnat)
  exact congrFun heq b

/-- `y^0 = 1` (the character maps `0 ↦ 1`). -/
private theorem zpPow_zero {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) : zpPow p y 0 = 1 := by
  simpa using zpPow_natCast p hy 0

/-- `1^a = 1` (multiplicativity in the base; density in the exponent). -/
private theorem zpPow_one_base (a : ℤ_[p]) : zpPow p (1 : ℂ_[p]) a = 1 := by
  have h1 : ‖(1 : ℂ_[p]) - 1‖ < 1 := by simp
  have hnat : ∀ k : ℕ, zpPow p (1 : ℂ_[p]) (k : ℤ_[p]) = (1 : ℂ_[p]) :=
    fun k => by rw [zpPow_natCast p h1, one_pow]
  have heq : (fun a => zpPow p (1 : ℂ_[p]) a) = (fun _ => (1 : ℂ_[p])) :=
    PadicInt.denseRange_natCast.equalizer (continuous_zpPow p h1) continuous_const (funext hnat)
  exact congrFun heq a

/-- The `ℤ_p`-power of a `1`-unit is nonzero (`y^a · y^{−a} = 1`). -/
private theorem zpPow_ne_zero {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    zpPow p y a ≠ 0 := by
  intro h
  have h1 : zpPow p y a * zpPow p y (-a) = 1 := by
    rw [← zpPow_add p hy, add_neg_cancel, zpPow_zero p hy]
  rw [h, zero_mul] at h1
  exact one_ne_zero h1.symm

/-- For `‖y − 1‖, ‖z − 1‖ < 1`, also `‖yz − 1‖ < 1` (`yz − 1 = y(z − 1) + (y − 1)`,
ultrametric, `‖y‖ ≤ 1`). -/
private theorem norm_mul_sub_one_lt_one {y z : ℂ_[p]} (hy : ‖y - 1‖ < 1)
    (hz : ‖z - 1‖ < 1) : ‖y * z - 1‖ < 1 := by
  have hyle : ‖y‖ ≤ 1 := by
    rw [show y = (y - 1) + 1 by ring]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (by simp [hy.le])
  rw [show y * z - 1 = y * (z - 1) + (y - 1) by ring]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hy)
  rw [norm_mul]
  calc ‖y‖ * ‖z - 1‖ ≤ 1 * ‖z - 1‖ := mul_le_mul hyle le_rfl (norm_nonneg _) zero_le_one
    _ = ‖z - 1‖ := one_mul _
    _ < 1 := hz

/-- Multiplicativity in the base: `(yz)^a = y^a · z^a` (density in the exponent;
`(yz)^k = y^k z^k`). -/
private theorem zpPow_mul_base {y z : ℂ_[p]} (hy : ‖y - 1‖ < 1) (hz : ‖z - 1‖ < 1)
    (a : ℤ_[p]) : zpPow p (y * z) a = zpPow p y a * zpPow p z a := by
  have hyz : ‖y * z - 1‖ < 1 := norm_mul_sub_one_lt_one p hy hz
  have hnat : ∀ k : ℕ,
      zpPow p (y * z) (k : ℤ_[p]) = zpPow p y (k : ℤ_[p]) * zpPow p z (k : ℤ_[p]) :=
    fun k => by rw [zpPow_natCast p hyz, zpPow_natCast p hy, zpPow_natCast p hz, mul_pow]
  have heq : (fun a => zpPow p (y * z) a) = (fun a => zpPow p y a * zpPow p z a) :=
    PadicInt.denseRange_natCast.equalizer (continuous_zpPow p hyz)
      ((continuous_zpPow p hy).mul (continuous_zpPow p hz)) (funext hnat)
  exact congrFun heq a

/-- `K_n` is finite-dimensional over `ℚ_p` (`[K_n:ℚ_p] = φ(p^n) > 0`), hence closed
in `ℂ_p` (`ℚ_p` complete). Used to keep `zpPow` inside `K_n` by density. -/
private theorem isClosed_K (n : ℕ) : IsClosed ((K p n : Set ℂ_[p])) := by
  haveI : FiniteDimensional ℚ_[p] (K p n) := Module.finite_of_finrank_pos (R := ℚ_[p])
    (by rw [finrank_K]; exact Nat.totient_pos.2 (pow_pos hp.out.pos n))
  have h := Submodule.closed_of_finiteDimensional ((K p n).toSubalgebra.toSubmodule)
  convert h using 1
  rw [Subalgebra.coe_toSubmodule, IntermediateField.coe_toSubalgebra]

/-- The integral coefficient image `toCp p c` lies in `K_n` (it is in the
`algebraMap ℚ_[p] ℂ_[p]` image, which `K_n ⊇ ℚ_p` contains). -/
private theorem toCp_mem_K (n : ℕ) (c : ℤ_[p]) : toCp p c ∈ K p n := by
  rw [toCp, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]
  exact (K p n).algebraMap_mem _

/-- Principal units are stable under `ℤ_p`-powers: membership in `𝒰_{n,1}` is
preserved (the limit stays in the closed subfield `K_n` and in the unit ball). -/
theorem zpPow_mem_localUnitsOne {n : ℕ} {u : ℂ_[p]ˣ} (hu : u ∈ localUnitsOne p n)
    (a : ℤ_[p]) :
    ∃ v : ℂ_[p]ˣ, (v : ℂ_[p]) = zpPow p (u : ℂ_[p]) a ∧ v ∈ localUnitsOne p n := by
  obtain ⟨huU, hy⟩ := hu
  set y : ℂ_[p] := (u : ℂ_[p]) with hyeq
  have hyK : y ∈ K p n := (Subring.mem_inf.1 huU.1).1
  -- The unit `y^a`, with explicit inverse `y^{−a}`.
  have hmul : zpPow p y a * zpPow p y (-a) = 1 := by
    rw [← zpPow_add p hy, add_neg_cancel, zpPow_zero p hy]
  refine ⟨Units.mkOfMulEqOne (zpPow p y a) (zpPow p y (-a)) hmul, rfl, ?_⟩
  -- `y^{a'} ∈ K_n` for every exponent (density: `y^k ∈ K_n`).
  have hmemK : ∀ a' : ℤ_[p], zpPow p y a' ∈ K p n :=
    fun a' => zpPow_mem_of_closed p hy (isClosed_K p n) (fun k => pow_mem hyK k) a'
  -- `‖y^{a'}‖ ≤ 1` for every exponent (ultrametric, `‖y^{a'} − 1‖ < 1`).
  have hnle : ∀ a' : ℤ_[p], ‖zpPow p y a'‖ ≤ 1 := fun a' => by
    rw [show zpPow p y a' = (zpPow p y a' - 1) + 1 by ring]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (by simp [(norm_zpPow_sub_one_lt_one p hy a').le])
  have hmemO : ∀ a' : ℤ_[p], zpPow p y a' ∈ O p n := fun a' => by
    rw [O, Subring.mem_inf]; exact ⟨hmemK a', hnle a'⟩
  have hinvval : (((Units.mkOfMulEqOne (zpPow p y a) (zpPow p y (-a)) hmul)⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
      = zpPow p y (-a) := by
    rw [Units.val_inv_eq_inv_val, Units.val_mkOfMulEqOne]
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Units.val_mkOfMulEqOne]; exact hmemO a
  · rw [hinvval]; exact hmemO (-a)
  · rw [Units.val_mkOfMulEqOne]; exact norm_zpPow_sub_one_lt_one p hy a

/-- The `1`-unit underlying an element of `𝒰_{n,1}`, and its norm bound. -/
private theorem norm_localUnitsOne_sub_one_lt_one {n : ℕ} (g : localUnitsOne p n) :
    ‖((g : ℂ_[p]ˣ) : ℂ_[p]) - 1‖ < 1 :=
  ((mem_localUnitsOne_iff p).1 g.2).2

/-- The `ℤ_p`-power of a member of `𝒰_{n,1}`, as a member of `𝒰_{n,1}` (the unit
from `zpPow_mem_localUnitsOne`, packaged with its membership). -/
private noncomputable def zpPowUnit {n : ℕ} (a : ℤ_[p]) (g : localUnitsOne p n) :
    localUnitsOne p n :=
  ⟨(zpPow_mem_localUnitsOne p g.2 a).choose, (zpPow_mem_localUnitsOne p g.2 a).choose_spec.2⟩

/-- The underlying `ℂ_[p]`-value of `zpPowUnit` is `zpPow`. -/
private theorem coe_zpPowUnit {n : ℕ} (a : ℤ_[p]) (g : localUnitsOne p n) :
    (((zpPowUnit p a g : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])
      = zpPow p ((g : ℂ_[p]ˣ) : ℂ_[p]) a :=
  (zpPow_mem_localUnitsOne p g.2 a).choose_spec.1

/-- Two members of `𝒰_{n,1}` are equal iff their underlying `ℂ_[p]`-values agree
(units are determined by their values, subgroup elements by their units). -/
private theorem localUnitsOne_ext {n : ℕ} {g h : localUnitsOne p n}
    (hgh : ((g : ℂ_[p]ˣ) : ℂ_[p]) = ((h : ℂ_[p]ˣ) : ℂ_[p])) : g = h :=
  Subtype.ext (Units.ext hgh)

/-- Two members of `Additive 𝒰_{n,1}` are equal iff their underlying `ℂ_[p]`-values
agree. -/
private theorem additive_localUnitsOne_ext {n : ℕ} {u v : Additive (localUnitsOne p n)}
    (huv : (((Additive.toMul u : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])
      = (((Additive.toMul v : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])) : u = v :=
  Additive.ext_iff.mpr (localUnitsOne_ext p huv)

noncomputable instance localUnitsOneSMul (n : ℕ) :
    SMul ℤ_[p] (Additive (localUnitsOne p n)) :=
  ⟨fun a u => Additive.ofMul (zpPowUnit p a (Additive.toMul u))⟩

/-- The underlying `ℂ_[p]`-value of the `ℤ_p`-scalar action on `𝒰_{n,1}`. -/
private theorem coe_localUnitsOne_smul {n : ℕ} (a : ℤ_[p])
    (u : Additive (localUnitsOne p n)) :
    (((Additive.toMul (a • u) : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])
      = zpPow p (((Additive.toMul u : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p]) a :=
  coe_zpPowUnit p a (Additive.toMul u)

/-- The `ℂ_[p]`-value of an `Additive`-sum is the product of the values. -/
private theorem coe_additive_add {n : ℕ} (u v : Additive (localUnitsOne p n)) :
    (((Additive.toMul (u + v) : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])
      = (((Additive.toMul u : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])
        * (((Additive.toMul v : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p]) := rfl

/-- The `ℂ_[p]`-value of the `Additive`-zero is `1`. -/
private theorem coe_additive_zero {n : ℕ} :
    (((Additive.toMul (0 : Additive (localUnitsOne p n)) : localUnitsOne p n) : ℂ_[p]ˣ) : ℂ_[p])
      = 1 := rfl

/-- **RJW TeX 2494–2496**: the `ℤ_p`-module structure on the (additivised)
principal-unit group `𝒰_{n,1}`. The action is `a • u = u^a` (`zpPow`); the module
laws transport the character laws (`zpPow_natCast`/`add`/`mul`) and the base
multiplicativity (`zpPow_mul_base`/`one_base`) through the `Additive`/subgroup
coercions. -/
noncomputable instance localUnitsOneModule (n : ℕ) :
    Module ℤ_[p] (Additive (localUnitsOne p n)) where
  one_smul u := by
    apply additive_localUnitsOne_ext
    rw [coe_localUnitsOne_smul, show (1 : ℤ_[p]) = ((1 : ℕ) : ℤ_[p]) by norm_cast,
      zpPow_natCast p (norm_localUnitsOne_sub_one_lt_one p _), pow_one]
  mul_smul a b u := by
    apply additive_localUnitsOne_ext
    rw [coe_localUnitsOne_smul, coe_localUnitsOne_smul, coe_localUnitsOne_smul, mul_comm a b,
      zpPow_mul p (norm_localUnitsOne_sub_one_lt_one p (Additive.toMul u)) b a]
  smul_zero a := by
    apply additive_localUnitsOne_ext
    rw [coe_localUnitsOne_smul, coe_additive_zero, zpPow_one_base]
  smul_add a u v := by
    apply additive_localUnitsOne_ext
    rw [coe_localUnitsOne_smul, coe_additive_add, coe_additive_add, coe_localUnitsOne_smul,
      coe_localUnitsOne_smul,
      zpPow_mul_base p (norm_localUnitsOne_sub_one_lt_one p _)
        (norm_localUnitsOne_sub_one_lt_one p _)]
  add_smul a b u := by
    apply additive_localUnitsOne_ext
    rw [coe_localUnitsOne_smul, coe_additive_add, coe_localUnitsOne_smul, coe_localUnitsOne_smul,
      zpPow_add p (norm_localUnitsOne_sub_one_lt_one p _)]
  zero_smul u := by
    apply additive_localUnitsOne_ext
    rw [coe_localUnitsOne_smul, coe_additive_zero,
      zpPow_zero p (norm_localUnitsOne_sub_one_lt_one p _)]

/-! ## The group 𝒰_∞ and the towers 𝒰_{∞,1}, 𝒰⁺_{∞,1} (RJW TeX 2503–2505) -/

/-- The level norm inverts: for nonzero `x ∈ K_{n+1}`,
`N_{n+1,n}(x⁻¹) = N_{n+1,n}(x)⁻¹` (`levelNorm_mul` + `levelNorm_one` give
`N(x)·N(x⁻¹) = 1`). -/
private theorem levelNorm_inv' (n : ℕ) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) (hx0 : x ≠ 0) :
    levelNorm p n x⁻¹ = (levelNorm p n x)⁻¹ := by
  have hxinv : x⁻¹ ∈ K p (n + 1) := (K p (n + 1)).inv_mem hx
  have hprod : levelNorm p n x * levelNorm p n x⁻¹ = 1 := by
    rw [← levelNorm_mul p n hx hxinv, mul_inv_cancel₀ hx0, levelNorm_one]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)

namespace NormCompatUnits

variable {p}

/-- The inverse of a norm-compatible system: pointwise inverses (norm
compatibility from multiplicativity of the level norm). -/
noncomputable def inv (u : NormCompatUnits p) : NormCompatUnits p where
  elems n := (u.elems n)⁻¹
  mem n := by rw [Units.val_inv_eq_inv_val]; exact u.inv_mem n
  inv_mem n := by rw [Units.val_inv_eq_inv_val, inv_inv]; exact u.mem n
  compat n hn := by
    have hxK : (u.elems (n + 1) : ℂ_[p]) ∈ K p (n + 1) := (Subring.mem_inf.1 (u.mem _)).1
    have hx0 : (u.elems (n + 1) : ℂ_[p]) ≠ 0 := (u.elems (n + 1)).ne_zero
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, levelNorm_inv' p n hxK hx0,
      u.compat n hn]

noncomputable instance : Inv (NormCompatUnits p) := ⟨inv⟩

/-- `𝒰_∞` is a commutative group (RJW TeX 2503: the inverse limit of the unit
*groups*; the existing structure carried only `Mul`/`One`). -/
noncomputable instance : CommGroup (NormCompatUnits p) where
  mul_assoc u v w := NormCompatUnits.ext (funext fun n => mul_assoc _ _ _)
  one_mul u := NormCompatUnits.ext (funext fun n => one_mul _)
  mul_one u := NormCompatUnits.ext (funext fun n => mul_one _)
  inv_mul_cancel u := NormCompatUnits.ext (funext fun n => inv_mul_cancel _)
  mul_comm u v := NormCompatUnits.ext (funext fun n => mul_comm _ _)

end NormCompatUnits

/-- `𝒰_{∞,1} = lim←_{n≥1} 𝒰_{n,1}`: the norm-compatible systems through the
principal units (RJW Eq. (`eq:Uinfty 1`), TeX 2503; the `n ≥ 1` convention matches
the `compat` field's). -/
def unitsTower1 : Subgroup (NormCompatUnits p) where
  carrier := {u | ∀ n, 1 ≤ n → u.elems n ∈ localUnitsOne p n}
  mul_mem' hu hv n hn := mul_mem (hu n hn) (hv n hn)
  one_mem' _ _ := one_mem _
  inv_mem' hu n hn := (localUnitsOne p n).inv_mem (hu n hn)

/-- `𝒰⁺_{∞,1} = lim←_{n≥1} 𝒰⁺_{n,1}` (RJW TeX 2504). -/
noncomputable def unitsTower1Plus : Subgroup (NormCompatUnits p) where
  carrier := {u | ∀ n, 1 ≤ n → u.elems n ∈ localUnitsOnePlus p n}
  mul_mem' hu hv n hn := mul_mem (hu n hn) (hv n hn)
  one_mem' _ _ := one_mem _
  inv_mem' hu n hn := (localUnitsOnePlus p n).inv_mem (hu n hn)

lemma unitsTower1Plus_le_unitsTower1 : unitsTower1Plus p ≤ unitsTower1 p :=
  fun _ hu n hn => (Subgroup.mem_inf.1 (hu n hn)).1

end Coleman

end PadicLFunctions
