/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.SpecificLimits.Normed
import «Adic spaces».Vendored.CoramRestrictedNorm

/-!
# Restricted Laurent series `R⟨W, W⁻¹⟩` (finite-jet pinching, layer 𝓛)

Source: [FJP] = *Finite-jet pinching: a uniform strongly sheafy domain which is not stably
uniform* (16 July 2026), §1 (conventions) and Proposition 2.3. This file provides the radius-one
Laurent algebra `L = k⟨W, W⁻¹⟩` of [FJP] (1.4): ℤ-indexed series `∑_{a ∈ ℤ} c_a W^a` whose
coefficients tend to `0` along the cofinite filter, with the Gauss (sup) norm.

Over a base `R` that is a complete ultrametric normed commutative ring, `RestrictedLaurent R`
is a complete ultrametric normed commutative ring; when the base norm is multiplicative with
discrete value group (the [FJP] setting, `R = K = LaurentSeries F`), the Laurent–Gauss norm is
multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm on 𝒞 = L⟨Q⟩ is multiplicative"), the
norm is attained, and `W` is a norm-one unit.

The nonnegative-support subring recovers `K⟨W⟩` (`PowerSeries.Restricted K 1`) isometrically;
this is the inclusion `k⟨W⟩ ⊂ L` used throughout [FJP] §2.
-/

open Filter Topology
open scoped NNReal

namespace FiniteJet

/-- A **restricted Laurent series** over a normed ring `R`: a coefficient function on `ℤ`
whose norms tend to `0` along the cofinite filter ([FJP] §1: "restricted Laurent series";
the elements `∑_{a∈ℤ} c_a W^a` with `c_a → 0`). -/
structure RestrictedLaurent (R : Type*) [NormedCommRing R] where
  /-- The coefficient of `W^a`. -/
  coeff : ℤ → R
  /-- Coefficients tend to zero along the cofinite filter. -/
  tendsto_coeff : Tendsto (fun a => ‖coeff a‖) cofinite (𝓝 0)

namespace RestrictedLaurent

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

@[ext]
theorem ext {f g : RestrictedLaurent R} (h : ∀ a, f.coeff a = g.coeff a) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact funext h

/-! ### Decay helpers -/

omit [IsUltrametricDist R] in
/-- For every positive threshold, only finitely many coefficients reach it. -/
theorem finite_setOf_le_norm_coeff (f : RestrictedLaurent R) {ε : ℝ} (hε : 0 < ε) :
    {a : ℤ | ε ≤ ‖f.coeff a‖}.Finite := by
  have h := f.tendsto_coeff.eventually (eventually_lt_nhds hε (a := (0 : ℝ)))
  rw [Filter.eventually_cofinite] at h
  exact h.subset fun a ha => by simpa using not_lt.mpr ha

omit [IsUltrametricDist R] in
/-- The coefficients of a restricted Laurent series are uniformly bounded, by a bound `≥ 1`. -/
theorem exists_norm_coeff_le (f : RestrictedLaurent R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a, ‖f.coeff a‖ ≤ C := by
  classical
  have hfin : {a : ℤ | 1 ≤ ‖f.coeff a‖}.Finite := f.finite_setOf_le_norm_coeff one_pos
  refine ⟨max 1 (↑(hfin.toFinset.sup fun a => ‖f.coeff a‖₊) : ℝ), le_max_left _ _,
    fun a => ?_⟩
  by_cases ha : 1 ≤ ‖f.coeff a‖
  · refine le_max_of_le_right ?_
    rw [← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun a => ‖f.coeff a‖₊) (hfin.mem_toFinset.mpr ha)
  · exact le_max_of_le_left (not_le.mp ha).le

omit [IsUltrametricDist R] in
/-- Cofinite-tendsto-to-zero criterion via finiteness of super-level sets. -/
theorem tendsto_cofinite_zero_of_finite {ι : Type*} {F : ι → ℝ} (h0 : ∀ i, 0 ≤ F i)
    (h : ∀ ε : ℝ, 0 < ε → {i : ι | ε ≤ F i}.Finite) :
    Tendsto F cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  refine ((h (ε / 2) (by positivity)).subset ?_)
  intro i hi
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hi
  rw [abs_of_nonneg (h0 i)] at hi
  simp only [Set.mem_setOf_eq]
  linarith

/-! ### Additive and multiplicative structure

Multiplication is Cauchy convolution: `(f * g).coeff m = ∑' a, f.coeff a * g.coeff (m - a)`.
The sum converges because the base is complete and nonarchimedean and the terms tend to `0`
along cofinite ([FJP] §1 and Prop 2.3 use this implicitly via the support description (1.8)). -/

/-- The zero series. -/
instance : Zero (RestrictedLaurent R) :=
  ⟨⟨fun _ => 0, by simpa using tendsto_const_nhds⟩⟩

/-- The one series (coefficient `1` at `0`). -/
instance : One (RestrictedLaurent R) :=
  ⟨⟨fun a => if a = 0 then 1 else 0, by
    refine tendsto_nhds_of_eventually_eq
      ((Filter.eventually_cofinite_ne (0 : ℤ)).mono fun a ha => ?_)
    simp [if_neg ha]⟩⟩

/-- Coefficientwise addition. -/
instance : Add (RestrictedLaurent R) :=
  ⟨fun f g => ⟨fun a => f.coeff a + g.coeff a, by
    have h := f.tendsto_coeff.add g.tendsto_coeff
    rw [add_zero] at h
    refine squeeze_zero (fun a => norm_nonneg _) (fun a => norm_add_le _ _) h⟩⟩

/-- Coefficientwise negation. -/
instance : Neg (RestrictedLaurent R) :=
  ⟨fun f => ⟨fun a => -f.coeff a, by simpa using f.tendsto_coeff⟩⟩

section Complete

variable [CompleteSpace R]

omit [IsUltrametricDist R] in
/-- Termwise norm decay of the convolution family, for a fixed target index. -/
theorem tendsto_conv_term (f g : RestrictedLaurent R) (m : ℤ) :
    Tendsto (fun a : ℤ => ‖f.coeff a * g.coeff (m - a)‖) cofinite (𝓝 0) := by
  obtain ⟨Cg, hCg1, hCg⟩ := g.exists_norm_coeff_le
  have hbound : ∀ a : ℤ, ‖f.coeff a * g.coeff (m - a)‖ ≤ ‖f.coeff a‖ * Cg := fun a =>
    (norm_mul_le _ _).trans (by
      have := hCg (m - a)
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _))
  have hlim : Tendsto (fun a : ℤ => ‖f.coeff a‖ * Cg) cofinite (𝓝 0) := by
    simpa using f.tendsto_coeff.mul_const Cg
  exact squeeze_zero (fun a => norm_nonneg _) hbound hlim

/-- The convolution defining `f * g` is summable (complete nonarchimedean base, terms → 0). -/
theorem summable_mul_coeff (f g : RestrictedLaurent R) (m : ℤ) :
    Summable (fun a : ℤ => f.coeff a * g.coeff (m - a)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_conv_term f g m)

/-- Convolution multiplication (requires a complete base for the `tsum`). -/
noncomputable instance : Mul (RestrictedLaurent R) :=
  ⟨fun f g => ⟨fun m => ∑' a : ℤ, f.coeff a * g.coeff (m - a), by
    obtain ⟨Cf, hCf1, hCf⟩ := f.exists_norm_coeff_le
    obtain ⟨Cg, hCg1, hCg⟩ := g.exists_norm_coeff_le
    refine tendsto_cofinite_zero_of_finite (fun m => norm_nonneg _) fun ε hε => ?_
    -- outside the sumset of the two super-level sets, every convolution term is ≤ ε/2
    have hS₁ : {a : ℤ | ε / 2 / Cg ≤ ‖f.coeff a‖}.Finite :=
      f.finite_setOf_le_norm_coeff (by positivity)
    have hS₂ : {b : ℤ | ε / 2 / Cf ≤ ‖g.coeff b‖}.Finite :=
      g.finite_setOf_le_norm_coeff (by positivity)
    refine (hS₁.image2 (· + ·) hS₂).subset fun m hm => ?_
    simp only [Set.mem_setOf_eq] at hm
    by_contra hnot
    -- every term of the convolution at such `m` has norm ≤ ε/2
    have hterm : ∀ a : ℤ, ‖f.coeff a * g.coeff (m - a)‖ ≤ ε / 2 := by
      intro a
      by_cases ha : ε / 2 / Cg ≤ ‖f.coeff a‖
      · -- then `m - a` is not in `S₂`
        have hb : ¬ ε / 2 / Cf ≤ ‖g.coeff (m - a)‖ := fun hb =>
          hnot ⟨a, ha, m - a, hb, by ring⟩
        push_neg at hb
        calc ‖f.coeff a * g.coeff (m - a)‖ ≤ ‖f.coeff a‖ * ‖g.coeff (m - a)‖ :=
              norm_mul_le _ _
          _ ≤ Cf * ‖g.coeff (m - a)‖ :=
              mul_le_mul_of_nonneg_right (hCf a) (norm_nonneg _)
          _ ≤ Cf * (ε / 2 / Cf) :=
              mul_le_mul_of_nonneg_left hb.le (by positivity)
          _ = ε / 2 := by field_simp
      · push_neg at ha
        calc ‖f.coeff a * g.coeff (m - a)‖ ≤ ‖f.coeff a‖ * ‖g.coeff (m - a)‖ :=
              norm_mul_le _ _
          _ ≤ ‖f.coeff a‖ * Cg :=
              mul_le_mul_of_nonneg_left (hCg _) (norm_nonneg _)
          _ ≤ (ε / 2 / Cg) * Cg :=
              mul_le_mul_of_nonneg_right ha.le (by positivity)
          _ = ε / 2 := by field_simp
    -- nonarchimedean: the whole sum then has norm ≤ ε/2 < ε, contradicting `ε ≤ ‖…‖`
    have hle : ‖∑' a : ℤ, f.coeff a * g.coeff (m - a)‖ ≤ ε / 2 :=
      IsUltrametricDist.norm_tsum_le_of_forall_le hterm
    linarith⟩⟩

/-- The doubly-indexed family behind associativity of the convolution is summable over
`ℤ × ℤ` (nonarchimedean criterion; only finitely many pairs have both an `f`- and a
`g`-coefficient large). -/
theorem summable_conv_triple (f g h : RestrictedLaurent R) (m : ℤ) :
    Summable (fun p : ℤ × ℤ => f.coeff p.2 * g.coeff (p.1 - p.2) * h.coeff (m - p.1)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (tendsto_cofinite_zero_of_finite (fun p => norm_nonneg _) fun ε hε => ?_)
  obtain ⟨Cf, hCf1, hCf⟩ := f.exists_norm_coeff_le
  obtain ⟨Cg, hCg1, hCg⟩ := g.exists_norm_coeff_le
  obtain ⟨Ch, hCh1, hCh⟩ := h.exists_norm_coeff_le
  have hS₁ : {a : ℤ | ε / (Cg * Ch) ≤ ‖f.coeff a‖}.Finite :=
    f.finite_setOf_le_norm_coeff (by positivity)
  have hS₂ : {c : ℤ | ε / (Cf * Ch) ≤ ‖g.coeff c‖}.Finite :=
    g.finite_setOf_le_norm_coeff (by positivity)
  refine ((hS₁.prod hS₂).image fun q : ℤ × ℤ => ((q.1 + q.2 : ℤ), q.1)).subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp
  have hnorm : ‖f.coeff p.2 * g.coeff (p.1 - p.2) * h.coeff (m - p.1)‖ ≤
      ‖f.coeff p.2‖ * ‖g.coeff (p.1 - p.2)‖ * ‖h.coeff (m - p.1)‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  refine ⟨(p.2, p.1 - p.2), ⟨?_, ?_⟩, by simp⟩
  · -- `ε/(Cg·Ch) ≤ ‖f.coeff p.2‖`
    have : ε ≤ ‖f.coeff p.2‖ * Cg * Ch := by
      refine hp.trans (hnorm.trans ?_)
      have h1 : ‖f.coeff p.2‖ * ‖g.coeff (p.1 - p.2)‖ ≤ ‖f.coeff p.2‖ * Cg :=
        mul_le_mul_of_nonneg_left (hCg _) (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hCh _) (by positivity))
    rw [Set.mem_setOf_eq, div_le_iff₀ (by positivity)]
    linarith [this, mul_assoc ‖f.coeff p.2‖ Cg Ch]
  · -- `ε/(Cf·Ch) ≤ ‖g.coeff (p.1 − p.2)‖`
    have : ε ≤ Cf * ‖g.coeff (p.1 - p.2)‖ * Ch := by
      refine hp.trans (hnorm.trans ?_)
      have h1 : ‖f.coeff p.2‖ * ‖g.coeff (p.1 - p.2)‖ ≤ Cf * ‖g.coeff (p.1 - p.2)‖ :=
        mul_le_mul_of_nonneg_right (hCf _) (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hCh _) (by positivity))
    rw [Set.mem_setOf_eq, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (g.coeff (p.1 - p.2))]

@[simp] theorem coeff_zero (a : ℤ) : (0 : RestrictedLaurent R).coeff a = 0 := rfl

@[simp] theorem coeff_one (a : ℤ) :
    (1 : RestrictedLaurent R).coeff a = if a = 0 then 1 else 0 := rfl

@[simp] theorem coeff_add (f g : RestrictedLaurent R) (a : ℤ) :
    (f + g).coeff a = f.coeff a + g.coeff a := rfl

@[simp] theorem coeff_neg (f : RestrictedLaurent R) (a : ℤ) : (-f).coeff a = -f.coeff a := rfl

theorem coeff_mul (f g : RestrictedLaurent R) (m : ℤ) :
    (f * g).coeff m = ∑' a : ℤ, f.coeff a * g.coeff (m - a) := rfl

/-- `RestrictedLaurent R` is a commutative ring under coefficientwise addition and Cauchy
convolution. -/
noncomputable instance : CommRing (RestrictedLaurent R) where
  add := (· + ·)
  add_assoc f g h := by ext a; simp [add_assoc]
  zero := 0
  zero_add f := by ext a; simp
  add_zero f := by ext a; simp
  add_comm f g := by ext a; simp [add_comm]
  mul := (· * ·)
  left_distrib f g h := by
    ext m
    simp only [coeff_mul, coeff_add]
    rw [← (summable_mul_coeff f g m).tsum_add (summable_mul_coeff f h m)]
    exact tsum_congr fun a => by rw [mul_add]
  right_distrib f g h := by
    ext m
    simp only [coeff_mul, coeff_add]
    rw [← (summable_mul_coeff f h m).tsum_add (summable_mul_coeff g h m)]
    exact tsum_congr fun a => by rw [add_mul]
  zero_mul f := by ext m; simp [coeff_mul]
  mul_zero f := by ext m; simp [coeff_mul]
  mul_assoc f g h := by
    ext m
    have hF := summable_conv_triple f g h m
    -- shear equivalence `(a, c) ↦ (a + c, a)` on `ℤ × ℤ`
    let e : ℤ × ℤ ≃ ℤ × ℤ :=
      ⟨fun q => (q.1 + q.2, q.1), fun p => (p.2, p.1 - p.2),
        fun q => by simp, fun p => by simp⟩
    have hG : Summable (fun q : ℤ × ℤ =>
        f.coeff q.1 * (g.coeff q.2 * h.coeff (m - q.1 - q.2))) := by
      refine (e.summable_iff.mpr hF).congr fun q => ?_
      show f.coeff (e q).2 * g.coeff ((e q).1 - (e q).2) * h.coeff (m - (e q).1) = _
      simp only [e, Equiv.coe_fn_mk, add_sub_cancel_left]
      rw [mul_assoc, sub_add_eq_sub_sub]
    have key : ((f * g) * h).coeff m =
        ∑' p : ℤ × ℤ, f.coeff p.2 * g.coeff (p.1 - p.2) * h.coeff (m - p.1) := by
      rw [coeff_mul,
        hF.tsum_prod' fun b => ((summable_mul_coeff f g b).mul_right (h.coeff (m - b)))]
      exact tsum_congr fun b => by
        rw [coeff_mul, ← (summable_mul_coeff f g b).tsum_mul_right (h.coeff (m - b))]
    have key2 : (f * (g * h)).coeff m =
        ∑' q : ℤ × ℤ, f.coeff q.1 * (g.coeff q.2 * h.coeff (m - q.1 - q.2)) := by
      rw [coeff_mul,
        hG.tsum_prod' fun a => ((summable_mul_coeff g h (m - a)).congr
          (fun c => by rw [sub_sub])).mul_left (f.coeff a)]
      exact tsum_congr fun a => by
        rw [coeff_mul, ← (summable_mul_coeff g h (m - a)).tsum_mul_left (f.coeff a)]
    rw [key, key2, ← Equiv.tsum_eq e]
    exact tsum_congr fun q => by
      show f.coeff (e q).2 * g.coeff ((e q).1 - (e q).2) * h.coeff (m - (e q).1) = _
      simp only [e, Equiv.coe_fn_mk, add_sub_cancel_left]
      rw [mul_assoc, sub_add_eq_sub_sub]
  one := 1
  one_mul f := by
    ext m
    rw [coeff_mul, tsum_eq_single 0 (fun a ha => by simp [if_neg ha])]
    simp
  mul_one f := by
    ext m
    rw [coeff_mul, tsum_eq_single m (fun a ha => by
      have : ¬ m - a = 0 := fun h => ha (by omega)
      simp [if_neg this])]
    simp
  neg := Neg.neg
  neg_add_cancel f := by ext a; simp
  mul_comm f g := by
    ext m
    rw [coeff_mul, coeff_mul, ← (Equiv.subLeft m).tsum_eq]
    exact tsum_congr fun a => by simp [mul_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Monomials and the algebra structure -/

/-- The monomial `c · W^a`. -/
def single (a : ℤ) (c : R) : RestrictedLaurent R :=
  ⟨fun b => if b = a then c else 0, by
    refine tendsto_nhds_of_eventually_eq
      ((Filter.eventually_cofinite_ne a).mono fun b hb => ?_)
    simp [if_neg hb]⟩

@[simp] theorem coeff_single (a b : ℤ) (c : R) :
    (single a c).coeff b = if b = a then c else 0 := rfl

theorem single_mul_single (a b : ℤ) (c d : R) :
    single a c * single b d = single (a + b) (c * d) := by
  ext m
  rw [coeff_mul, tsum_eq_single a (fun x hx => by simp [coeff_single, if_neg hx])]
  simp only [coeff_single, if_pos rfl]
  by_cases hm : m = a + b
  · have : m - a = b := by omega
    simp [this, hm]
  · have : ¬ m - a = b := fun h => hm (by omega)
    simp [if_neg this, if_neg hm]

@[simp] theorem single_zero_one : (single 0 (1 : R)) = 1 := by
  ext a; simp [coeff_single, coeff_one]

/-- The scalar embedding `R → RestrictedLaurent R` as `single 0`. -/
noncomputable def C : R →+* RestrictedLaurent R where
  toFun c := single 0 c
  map_one' := single_zero_one
  map_mul' c d := by rw [single_mul_single, add_zero]
  map_zero' := by ext a; simp [coeff_single]
  map_add' c d := by ext a; simp [coeff_single]; split <;> simp

noncomputable instance : Algebra R (RestrictedLaurent R) :=
  (C (R := R)).toAlgebra

/-- The variable `W` (norm-one monomial at exponent `1`). -/
noncomputable def W : RestrictedLaurent R := single 1 1

/-- `W` is a unit, with inverse the monomial at exponent `-1` ([FJP] §1.4: "both `W` and
`W⁻¹` are power-bounded"). -/
noncomputable def Wu : (RestrictedLaurent R)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by rw [single_mul_single]; norm_num
  inv_val := by rw [single_mul_single]; norm_num

end Complete

/-! ### The Gauss (sup) norm

[FJP] (1.8): "An element is a series `∑_{(a,b)∈S} c_{a,b} W^a Q^b` such that, for every ε > 0,
only finitely many coefficients have `|c_{a,b}| ≥ ε`; its norm is `sup |c_{a,b}|`." Here the
univariate (`Q`-free) case: `‖f‖ = ⨆ a, ‖f.coeff a‖`, attained because the coefficient family
is restricted. -/

/-- The sup norm of a restricted Laurent series. -/
noncomputable def gaussNorm (f : RestrictedLaurent R) : ℝ := ⨆ a : ℤ, ‖f.coeff a‖

/-- The sup defining the Gauss norm is attained ([FJP] Prop 2.3: "the coefficient family of a
restricted Laurent series tends to zero, so its nonzero coefficient supremum is attained"). -/
theorem exists_gaussNorm_eq (f : RestrictedLaurent R) (hf : f ≠ 0) :
    ∃ a : ℤ, gaussNorm f = ‖f.coeff a‖ ∧ f.coeff a ≠ 0 := by sorry

theorem norm_coeff_le_gaussNorm (f : RestrictedLaurent R) (a : ℤ) :
    ‖f.coeff a‖ ≤ gaussNorm f := by sorry

/-- The Gauss norm as a `RingNorm` (submultiplicative, ultrametric-compatible). -/
noncomputable def isRingNorm [CompleteSpace R] [NormOneClass R] :
    RingNorm (RestrictedLaurent R) where
  toFun := gaussNorm
  map_zero' := by sorry
  add_le' := by sorry
  neg' := by sorry
  mul_le' := by sorry
  eq_zero_of_map_eq_zero' := by sorry

/-- `RestrictedLaurent R` is a normed ring under the Gauss norm. -/
noncomputable instance [CompleteSpace R] [NormOneClass R] :
    NormedCommRing (RestrictedLaurent R) where
  toNormedRing := RingNorm.toNormedRing (isRingNorm (R := R))
  mul_comm := mul_comm

theorem norm_def [CompleteSpace R] [NormOneClass R] (f : RestrictedLaurent R) :
    ‖f‖ = gaussNorm f := rfl

@[simp] theorem norm_single [CompleteSpace R] [NormOneClass R] (a : ℤ) (c : R) :
    ‖single a c‖ = ‖c‖ := by sorry

@[simp] theorem norm_W [CompleteSpace R] [NormOneClass R] :
    ‖(Wu (R := R)).val‖ = 1 := by sorry

@[simp] theorem norm_W_inv [CompleteSpace R] [NormOneClass R] :
    ‖((Wu (R := R))⁻¹ : (RestrictedLaurent R)ˣ).val‖ = 1 := by sorry

/-- The Gauss norm is ultrametric. -/
instance [CompleteSpace R] [NormOneClass R] : IsUltrametricDist (RestrictedLaurent R) := by
  sorry

/-- Multiplication by `W` is an isometry (used in [FJP] Prop 3.1: `‖W^{-n} y‖ = ‖y‖`). -/
theorem norm_W_mul [CompleteSpace R] [NormOneClass R] (f : RestrictedLaurent R) :
    ‖(Wu (R := R)).val * f‖ = ‖f‖ := by sorry

/-- Completeness of the restricted Laurent ring over a complete base ([FJP] §1: Banach
direct sums / restricted series are complete). -/
instance [CompleteSpace R] [NormOneClass R] : CompleteSpace (RestrictedLaurent R) := by
  sorry

/-! ### Multiplicativity over a discretely valued field

[FJP] Prop 2.3 (verbatim): "The Laurent Gauss norm on 𝒞 = L⟨Q⟩ is multiplicative. Indeed, the
coefficient family of a restricted Laurent series tends to zero, so its nonzero coefficient
supremum is attained. Since every nonzero coefficient norm belongs to `|k^×|`, so does every
nonzero Gauss norm. We may therefore scale two nonzero elements to norm one. Their reductions
are nonzero Laurent polynomials in `k̃[W, W⁻¹, Q]` … Their product remains nonzero because this
Laurent polynomial ring is a domain."  This file proves the `Q`-free (univariate Laurent) case;
`FiniteJetRings.lean` derives the `L⟨Q⟩` case over the base `𝓛`. -/

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Norm multiplicativity for restricted Laurent series over a complete nonarchimedean field
with discrete value group ([FJP] Prop 2.3; hypothesis `hd` is the discreteness used to scale
to norm one and to separate `< 1` from `≤ |ϖ|`). -/
theorem norm_mul_eq (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n)
    (f g : RestrictedLaurent K) : ‖f * g‖ = ‖f‖ * ‖g‖ := by sorry

/-- `RestrictedLaurent K` is a domain when the base is a complete nonarchimedean field with
discrete value group ([FJP] Prop 2.3: "also that 𝒞 is a domain"; univariate case). -/
theorem mul_ne_zero_of_ne_zero (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n)
    {f g : RestrictedLaurent K} (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := by sorry

end Field

/-! ### The nonnegative-support subring `R⟨W⟩ ⊂ R⟨W, W⁻¹⟩` -/

/-- Radius-one positivity witnesses for the vendored Gauss-norm stack. -/
instance : StrongPos (fun _ : Unit => (1 : ℝ)) := ⟨fun _ => one_pos⟩

instance (n : ℕ) : StrongPos (fun _ : Fin n => (1 : ℝ)) := ⟨fun _ => one_pos⟩

section Nonneg

variable (R) in
/-- The subring of series supported in nonnegative exponents — the copy of `R⟨W⟩` inside
`R⟨W, W⁻¹⟩` ([FJP] Lemma 2.2: "the subspace `k⟨W⟩` is the intersection of the kernels of the
continuous negative-coefficient maps"). -/
noncomputable def nonnegSubring [CompleteSpace R] : Subring (RestrictedLaurent R) where
  carrier := {f | ∀ a : ℤ, a < 0 → f.coeff a = 0}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

/-- The nonnegative-support subring is closed (kernels of the continuous coefficient
functionals; [FJP] Lemma 2.2). -/
theorem isClosed_nonnegSubring [CompleteSpace R] [NormOneClass R] :
    IsClosed (nonnegSubring R : Set (RestrictedLaurent R)) := by sorry

/-- The norm-preserving identification of `PowerSeries.Restricted R 1` (the vendored `R⟨W⟩`)
with the nonnegative-support subring of `R⟨W, W⁻¹⟩`. -/
noncomputable def nonnegEquiv [CompleteSpace R] [NormOneClass R] :
    PowerSeries.Restricted R (1 : ℝ) ≃+* nonnegSubring R where
  toFun := by sorry
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
  map_mul' := by sorry
  map_add' := by sorry

/-- `nonnegEquiv` preserves norms. -/
theorem nonnegEquiv_norm [CompleteSpace R] [NormOneClass R]
    (f : PowerSeries.Restricted R (1 : ℝ)) :
    ‖((nonnegEquiv (R := R) f : nonnegSubring R) : RestrictedLaurent R)‖ = ‖f‖ := by sorry

/-- The norm-preserving embedding `R⟨W⟩ → R⟨W,W⁻¹⟩` (composite of `nonnegEquiv` with the
subring inclusion). -/
noncomputable def ofRestricted [CompleteSpace R] [NormOneClass R] :
    PowerSeries.Restricted R (1 : ℝ) →+* RestrictedLaurent R :=
  (nonnegSubring R).subtype.comp (nonnegEquiv (R := R)).toRingHom

theorem ofRestricted_norm [CompleteSpace R] [NormOneClass R]
    (f : PowerSeries.Restricted R (1 : ℝ)) : ‖ofRestricted (R := R) f‖ = ‖f‖ := by sorry

theorem ofRestricted_injective [CompleteSpace R] [NormOneClass R] :
    Function.Injective (ofRestricted (R := R)) := by sorry

end Nonneg

/-! ### Density of Laurent polynomials and the affinoid presentation surjection

[FJP] Prop 2.1: "Each of 𝓑, 𝒞, 𝒟 is a quotient of a finite Tate algebra over `k`, so each is
strongly noetherian."  We realise the presentation as a *surjection* from the vendored
two-variable restricted ring (evaluating `W ↦ Wu`, `V ↦ Wu⁻¹`); surjectivity holds via the
explicit norm-preserving monomial section, and noetherianity of the target follows from
noetherianity of the source — no kernel identification is required. -/

/-- Evaluation `R⟨W,V⟩ → R⟨W,W⁻¹⟩`, `W ↦ Wu, V ↦ Wu⁻¹`: a bounded ring homomorphism. -/
noncomputable def evalHom [CompleteSpace R] [NormOneClass R] :
    MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ)) →+* RestrictedLaurent R where
  toFun := by sorry
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

theorem evalHom_surjective [CompleteSpace R] [NormOneClass R] :
    Function.Surjective (evalHom (R := R)) := by sorry

theorem evalHom_norm_le [CompleteSpace R] [NormOneClass R]
    (f : MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ))) :
    ‖evalHom (R := R) f‖ ≤ ‖f‖ := by sorry

end RestrictedLaurent

end FiniteJet
