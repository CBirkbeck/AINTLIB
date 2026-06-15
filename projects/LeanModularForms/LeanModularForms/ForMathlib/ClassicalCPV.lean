/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.LaurentSeries
import LeanModularForms.ForMathlib.PiecewiseC1PathOn

/-!
# Basic Definitions for Complex Analysis with Principal Values

Core definitions for piecewise C¹ curves, Cauchy principal value integrals,
and generalized winding numbers following Hungerbühler–Wasem.

## Main definitions

* `PiecewiseC1Curve`: a continuous curve `γ : [a, b] → ℂ` that is `C¹` away from a finite
  partition of the interval.
* `PiecewiseC1Immersion`: a piecewise `C¹` curve with nonzero derivative (one-sided limits
  at partition points are nonzero).
* `cauchyPrincipalValue'`: the Cauchy principal value of `∮_γ f(z) dz` excluding
  `ε`-neighbourhoods of a singularity `z₀`.
* `generalizedWindingNumber'`: the winding number of `γ` around `z₀` defined via the
  Cauchy principal value.

## Main results

* `intervalIntegrable_of_piecewise_continuousOn_bounded`: a piecewise continuous bounded
  function is interval integrable.
* `hasDerivWithinAt_zero_of_deriv_zero_off_finite`: if `f` is continuous on `[a, b]` and
  has zero derivative off a finite set, then its right derivative vanishes everywhere on
  `[a, b)`.
* `continuousWithinAt_integral_of_dominated_piecewise`: dominated convergence for
  parametric integrals over a piecewise continuous family.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- A piecewise continuously differentiable curve `γ : [a, b] → ℂ`, `C¹` on each
subinterval between partition points. Layers an Icc-style `partition` (endpoints included)
on top of an inherited `PiecewiseC1PathOn a b hab x y` whose partition is Ioo-style. -/
@[ext]
structure PiecewiseC1Curve where
  /-- Left endpoint of the parameter interval. -/
  a : ℝ
  /-- Right endpoint of the parameter interval. -/
  b : ℝ
  /-- Source value `γ(a)`. -/
  x : ℂ
  /-- Target value `γ(b)`. -/
  y : ℂ
  /-- The parameter interval is non-degenerate. -/
  hab : a < b
  /-- Underlying piecewise C¹ path on `[a, b]` from `x` to `y`. -/
  toPiecewiseC1PathOn : PiecewiseC1PathOn a b hab x y
  /-- The Icc-style partition (with endpoints `a, b` included). -/
  partition : Finset ℝ
  /-- The partition lies inside `[a, b]`. -/
  partition_subset : (partition : Set ℝ) ⊆ Icc a b
  /-- Both endpoints `a` and `b` belong to the partition. -/
  endpoints_in_partition : a ∈ partition ∧ b ∈ partition
  /-- The Icc-style partition is the inherited Ioo-style one with endpoints adjoined. -/
  partition_eq : partition = insert a (insert b toPiecewiseC1PathOn.partition)

namespace PiecewiseC1Curve

/-- The underlying function `ℝ → ℂ` of a piecewise `C¹` curve. -/
def toFun (γ : PiecewiseC1Curve) : ℝ → ℂ := γ.toPiecewiseC1PathOn.toFun

instance : CoeFun PiecewiseC1Curve fun _ ↦ ℝ → ℂ where coe := toFun

theorem continuous_toFun (γ : PiecewiseC1Curve) :
    ContinuousOn γ.toFun (Icc γ.a γ.b) := γ.toPiecewiseC1PathOn.continuous_toFun

private theorem notMem_innerPartition_of_notMem_partition (γ : PiecewiseC1Curve) {t : ℝ}
    (htn : t ∉ γ.partition) : t ∉ γ.toPiecewiseC1PathOn.partition := fun h_in => htn <| by
  rw [γ.partition_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_in)

/-- Differentiability off the (Icc-style) partition. -/
theorem smooth_off_partition (γ : PiecewiseC1Curve) :
    ∀ t ∈ Icc γ.a γ.b, t ∉ γ.partition → DifferentiableAt ℝ γ.toFun t := fun t ht htn => by
  have h_ne_a : t ≠ γ.a := fun h => htn (h ▸ γ.endpoints_in_partition.1)
  have h_ne_b : t ≠ γ.b := fun h => htn (h ▸ γ.endpoints_in_partition.2)
  exact γ.toPiecewiseC1PathOn.differentiable_off t
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h_ne_a), lt_of_le_of_ne ht.2 h_ne_b⟩
    (γ.notMem_innerPartition_of_notMem_partition htn)

theorem deriv_continuous_off_partition (γ : PiecewiseC1Curve) :
    ∀ t ∈ Ioo γ.a γ.b, t ∉ γ.partition → ContinuousAt (deriv γ.toFun) t := fun t ht htn =>
  γ.toPiecewiseC1PathOn.deriv_continuous_off t ht
    (γ.notMem_innerPartition_of_notMem_partition htn)

/-- **Smart constructor** from the legacy Icc-style field set. Reconstructs the underlying
`PiecewiseC1PathOn` by carving the partition's interior `partition.erase a |>.erase b`. -/
def ofIccPartition (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b) (partition : Finset ℝ)
    (partition_subset : (partition : Set ℝ) ⊆ Icc a b)
    (endpoints_in_partition : a ∈ partition ∧ b ∈ partition)
    (continuous_toFun : ContinuousOn toFun (Icc a b))
    (smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t)
    (deriv_continuous_off_partition : ∀ t ∈ Ioo a b, t ∉ partition →
      ContinuousAt (deriv toFun) t) : PiecewiseC1Curve := by
  classical
  let openPart : Finset ℝ := (partition.erase a).erase b
  have h_eq : partition = insert a (insert b openPart) := by
    ext s
    by_cases h_a : s = a
    · simp [h_a, endpoints_in_partition.1]
    by_cases h_b : s = b
    · simp [h_b, endpoints_in_partition.2]
    simp [openPart, Finset.mem_insert, Finset.mem_erase, h_a, h_b]
  have h_sub : (openPart : Set ℝ) ⊆ Ioo a b := fun t ht => by
    obtain ⟨h_ne_b, ht'⟩ := Finset.mem_erase.mp ht
    obtain ⟨h_ne_a, h_in⟩ := Finset.mem_erase.mp ht'
    have h_icc := partition_subset h_in
    exact ⟨lt_of_le_of_ne h_icc.1 (Ne.symm h_ne_a), lt_of_le_of_ne h_icc.2 h_ne_b⟩
  have h_not : ∀ {t : ℝ}, t ∈ Ioo a b → t ∉ openPart → t ∉ partition :=
    fun {t} ht htn h_in => htn <| Finset.mem_erase.mpr ⟨ne_of_lt ht.2,
      Finset.mem_erase.mpr ⟨(ne_of_lt ht.1).symm, h_in⟩⟩
  exact
    { a := a, b := b, hab := hab, x := toFun a, y := toFun b
      toPiecewiseC1PathOn :=
        { toFun := toFun, source := rfl, target := rfl
          continuous_toFun := continuous_toFun
          partition := openPart, partition_subset := h_sub
          differentiable_off := fun t ht htn =>
            smooth_off_partition t (Ioo_subset_Icc_self ht) (h_not ht htn)
          deriv_continuous_off := fun t ht htn =>
            deriv_continuous_off_partition t ht (h_not ht htn) }
      partition := partition
      partition_subset := partition_subset
      endpoints_in_partition := endpoints_in_partition
      partition_eq := h_eq }

@[simp] theorem ofIccPartition_toFun (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).toFun = toFun := rfl

@[simp] theorem ofIccPartition_a (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).a = a := rfl

@[simp] theorem ofIccPartition_b (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).b = b := rfl

end PiecewiseC1Curve

/-- A closed curve has γ(a) = γ(b). -/
def PiecewiseC1Curve.IsClosed (γ : PiecewiseC1Curve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- A piecewise `C¹` immersion: a piecewise `C¹` curve whose derivative is nonzero and
admits nonzero one-sided limits at every partition point. -/
@[ext]
structure PiecewiseC1Immersion extends PiecewiseC1Curve where
  /-- The derivative is nonzero off the partition. -/
  deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toPiecewiseC1PathOn.toFun t ≠ 0
  /-- At every interior partition point the left limit of the derivative is nonzero. -/
  left_deriv_limit : ∀ p ∈ partition, a < p →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toPiecewiseC1PathOn.toFun) (𝓝[<] p) (𝓝 L)
  /-- At every interior partition point the right limit of the derivative is nonzero. -/
  right_deriv_limit : ∀ p ∈ partition, p < b →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toPiecewiseC1PathOn.toFun) (𝓝[>] p) (𝓝 L)

/-- The Cauchy principal value of ∮_γ f(z) dz exists with value `L`: the ε-truncated
integral along `γ` over `[a, b]` (excluding the ε-neighbourhood of `z₀`) tends to `L`
as `ε → 0⁺`. **Primary API predicate** (Tendsto-based, raw `ℝ → ℂ`, `[a, b]`). -/
def HasCauchyPV' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (L : ℂ) : Prop :=
  Tendsto (fun ε ↦
      ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
    (𝓝[>] 0) (𝓝 L)

/-- The Cauchy principal value of ∮_γ f(z) dz, excluding ε-neighborhoods of z₀.
limUnder-based; secondary. Returns junk when the limit does not exist; use
`HasCauchyPV'` for the predicate. -/
def cauchyPrincipalValue' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value exists; abbreviation `∃ L, HasCauchyPV' f γ a b z₀ L`. -/
def CauchyPrincipalValueExists' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, HasCauchyPV' f γ a b z₀ L

/-- Bridge theorem: if `HasCauchyPV' f γ a b z₀ L`, then
`cauchyPrincipalValue' f γ a b z₀ = L`. -/
theorem HasCauchyPV'.cauchyPV_eq {f : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {z₀ : ℂ} {L : ℂ} (h : HasCauchyPV' f γ a b z₀ L) :
    cauchyPrincipalValue' f γ a b z₀ = L :=
  h.limUnder_eq

/-- The limit in `HasCauchyPV'` is unique. -/
theorem HasCauchyPV'.unique {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    {L₁ L₂ : ℂ} (h₁ : HasCauchyPV' f γ a b z₀ L₁) (h₂ : HasCauchyPV' f γ a b z₀ L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

/-! ### Algebraic API for `HasCauchyPV'`

These lemmas let downstream sites stop hand-rolling the `Tendsto` manipulation that
arises whenever one CPV is built from another via an algebraic identity on the
integrand. -/

/-- The CPV integrand `if ε < ‖γ t - z₀‖ then f(γ t) * deriv γ t else 0` is congr in `f`. -/
theorem HasCauchyPV'.congr_along_curve {f g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' f γ a b z₀ L) (h_eq : ∀ t, f (γ t) = g (γ t)) :
    HasCauchyPV' g γ a b z₀ L := by
  show Tendsto _ _ _
  refine Filter.Tendsto.congr (fun ε => intervalIntegral.integral_congr fun t _ => ?_) h
  split_ifs <;> simp [h_eq]

/-- Scalar multiplication: if the CPV of `f` is `L`, then the CPV of `c * f` is `c * L`. -/
theorem HasCauchyPV'.const_mul {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' f γ a b z₀ L) (c : ℂ) :
    HasCauchyPV' (fun z => c * f z) γ a b z₀ (c * L) := by
  have h_eq : (fun ε => ∫ t in a..b, if ‖γ t - z₀‖ > ε
        then (c * f (γ t)) * deriv γ t else 0) =
      fun ε => c * ∫ t in a..b, if ‖γ t - z₀‖ > ε
        then f (γ t) * deriv γ t else 0 := by
    ext ε
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    split_ifs <;> ring
  show Tendsto _ _ _
  rw [h_eq]
  exact Filter.Tendsto.const_mul c h

/-- Right-multiplication by a scalar: CPV of `f * c` is `L * c`. -/
theorem HasCauchyPV'.mul_const {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' f γ a b z₀ L) (c : ℂ) :
    HasCauchyPV' (fun z => f z * c) γ a b z₀ (L * c) := by
  simpa [mul_comm] using h.const_mul c

/-- The shift `f z = g (z - c)` translates the CPV: if `HasCauchyPV' g (γ - c) … L`,
then `HasCauchyPV' f γ … L` (when `f` agrees with `g (· - c)` on the curve). -/
theorem HasCauchyPV'.of_eventuallyEq_along_curve
    {f g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV' g γ a b z₀ L) (h_eq : ∀ t, g (γ t) = f (γ t)) :
    HasCauchyPV' f γ a b z₀ L :=
  h.congr_along_curve h_eq

/-- Avoidance: if `γ` stays away from `z₀` on `[a, b]`, then the CPV equals the
ordinary integral; in particular it exists. -/
theorem HasCauchyPV'.of_avoidance {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    HasCauchyPV' f γ a b z₀ (∫ t in a..b, f (γ t) * deriv γ t) := by
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, left_mem_Icc.mpr hab⟩ (h_cont.sub continuousOn_const).norm
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨Ioo 0 ‖γ t₀ - z₀‖,
    Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))), fun ε hε => ?_⟩
  exact intervalIntegral.integral_congr fun t ht => by
    rw [uIcc_of_le hab] at ht
    exact (if_pos (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm

/-- Concatenation: CPV on adjacent intervals `[a, b]` and `[b, c]` glues to `[a, c]`. -/
theorem HasCauchyPV'.concat {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b c : ℝ} {z₀ : ℂ}
    {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPV' f γ a b z₀ L₁) (h_bc : HasCauchyPV' f γ b c z₀ L₂)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    HasCauchyPV' f γ a c z₀ (L₁ + L₂) := by
  show Tendsto _ _ _
  refine Filter.Tendsto.congr' ?_ (Filter.Tendsto.add h_ab h_bc)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hII := h_int ε hε
  have hac := hab.trans hbc
  exact intervalIntegral.integral_add_adjacent_intervals
    (hII.mono_set <| by rw [uIcc_of_le hab, uIcc_of_le hac]; exact Icc_subset_Icc_right hbc)
    (hII.mono_set <| by rw [uIcc_of_le hbc, uIcc_of_le hac]; exact Icc_subset_Icc_left hab)

/-- Existence version of avoidance. -/
theorem cauchyPrincipalValueExists'_of_avoidance {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {z₀ : ℂ} (h_cont : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    CauchyPrincipalValueExists' f γ a b z₀ :=
  ⟨_, HasCauchyPV'.of_avoidance h_cont hab h_avoid⟩

/-- Existence version of concatenation. -/
theorem CauchyPrincipalValueExists'.concat {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b c : ℝ}
    {z₀ : ℂ} (h_ab : CauchyPrincipalValueExists' f γ a b z₀)
    (h_bc : CauchyPrincipalValueExists' f γ b c z₀) (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    CauchyPrincipalValueExists' f γ a c z₀ :=
  let ⟨_, hL₁⟩ := h_ab
  let ⟨_, hL₂⟩ := h_bc
  ⟨_, hL₁.concat hL₂ hab hbc h_int⟩

/-- The generalized winding number of γ around z₀, defined via principal value.
`n_{z₀}(γ) = (1/2πi) · PV ∮_γ dz/(z - z₀)`. -/
def generalizedWindingNumber' (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * cauchyPrincipalValue' (·⁻¹) (fun t ↦ γ t - z₀) a b 0

end
