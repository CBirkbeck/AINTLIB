/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coefficients
import PadicLFunctions.Measure.Fubini

/-!
# Measures with values in the integer ring of a nonarchimedean field

The coefficient-general layer of the measure theory of RJW §3 (the §5
widening pass, decomposition cluster W): for a nonarchimedean normed field
`K` with integer ring `R := integerRing K`, an `R`-valued measure on a
compact space `X` is an `R`-linear functional on `C(X, R)` (RJW Def 3.6 with
the `𝒪_L`-valuedness convention of TeX 765). Boundedness is automatic
exactly as in the `ℤ_p` case — the norm of a nonzero `f` is attained and is
realised by a scalar, and dividing by it keeps the values integral because
the ambient field is available.

The `ℤ_p`-instance of this theory is `PadicLFunctions/Measure/*` (kept
separate: `ℤ_[p]` is definitionally but not syntactically the unit ball of
`ℚ_[p]`, and §4 builds on the `PadicMeasure` spelling — see the TW2 replan
note in `.mathlib-quality/tickets.md`). The two layers are linked by the
base-change map of ticket TW6.

## Main definitions

* `PadicLFunctions.MeasureR K X` — `R`-valued measures on `X`.
* `MeasureR.dirac`, `MeasureR.pushforward` — Dirac measures and pushforward.

## Main results

* `MeasureR.norm_apply_le` — automatic boundedness `‖μ f‖ ≤ ‖f‖`.
* `MeasureR.ext_locallyConstant` — measures agree if they agree on locally
  constant functions.
-/

open Filter Topology

namespace PadicLFunctions

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

/-- An `integerRing K`-valued measure on `X`: an `integerRing K`-linear
functional on the continuous `integerRing K`-valued functions (RJW Def 3.6 +
the `𝒪_L`-integrality convention, TeX 755–765). As in the `ℤ_p` case this is
an `abbrev`, so the `LinearMap` API applies transparently. -/
abbrev MeasureR := C(X, integerRing K) →ₗ[integerRing K] integerRing K

namespace MeasureR

/-- The Dirac measure at `x : X` (RJW Ex. 3.7, TeX 774–779). -/
def dirac (x : X) : MeasureR K X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma dirac_apply (x : X) (f : C(X, integerRing K)) : dirac K X x f = f x := rfl

/-- Precomposition with a continuous map, auxiliary for `pushforward`. -/
def compRight (m : C(X, Y)) :
    C(Y, integerRing K) →ₗ[integerRing K] C(X, integerRing K) where
  toFun f := f.comp m
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma compRight_apply (m : C(X, Y)) (f : C(Y, integerRing K)) :
    compRight K X Y m f = f.comp m := rfl

/-- Pushforward of a measure along a continuous map (RJW §3.5.4 / Rem 3.33
specialise this). -/
def pushforward (m : C(X, Y)) : MeasureR K X →ₗ[integerRing K] MeasureR K Y where
  toFun μ := μ.comp (compRight K X Y m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma pushforward_apply (m : C(X, Y)) (μ : MeasureR K X) (f : C(Y, integerRing K)) :
    pushforward K X Y m μ f = μ (f.comp m) := rfl

@[simp]
lemma pushforward_dirac (m : C(X, Y)) (x : X) :
    pushforward K X Y m (dirac K X x) = dirac K Y (m x) := rfl

/-- The indicator function of a clopen subset, valued in `integerRing K`
(mathlib's `LocallyConstant.charFn` is parametric in the value ring). -/
noncomputable def charFnCM {U : Set X} (hU : IsClopen U) : C(X, integerRing K) :=
  (LocallyConstant.charFn (integerRing K) hU : C(X, integerRing K))

@[simp]
lemma charFnCM_apply {U : Set X} (hU : IsClopen U) (x : X) :
    charFnCM K X hU x = U.indicator 1 x := rfl

section compact

variable {K X} [CompactSpace X]

/-- **Automatic boundedness** (RJW Def 3.6 footnote, TeX 759 + 765): every
`integerRing K`-linear functional on `C(X, integerRing K)` has norm at most
one. The norm of a nonzero `f` is attained at some `x₀`; dividing by the
scalar `f x₀` (in the ambient field `K`) keeps values integral, so
`μ f = f x₀ • μ (f / f x₀)` with the second factor integral. -/
theorem norm_apply_le (μ : MeasureR K X) (f : C(X, integerRing K)) :
    ‖μ f‖ ≤ ‖f‖ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have hf : f = 0 := by ext x; exact (IsEmpty.false x).elim
    simp [hf]
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  -- the sup norm is attained
  obtain ⟨x₀, -, hx₀'⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    ((map_continuous f).norm.continuousOn)
  have hx₀ : ∀ x, ‖f x‖ ≤ ‖f x₀‖ := fun x => hx₀' (Set.mem_univ x)
  have hfx₀ : f x₀ ≠ 0 := by
    intro h
    refine hf (ContinuousMap.ext fun x => norm_le_zero_iff.1 ?_)
    simpa [h] using hx₀ x
  have hnorm : ‖f‖ = ‖f x₀‖ :=
    le_antisymm ((f.norm_le (norm_nonneg _)).2 hx₀) (f.norm_coe_le_norm x₀)
  have hfx₀K : ((f x₀ : K)) ≠ 0 := by
    simpa using Subtype.coe_injective.ne hfx₀
  -- divide by the attained value inside the field `K`
  have hbound : ∀ x : X, ‖(f x : K) / (f x₀ : K)‖ ≤ 1 := fun x => by
    rw [norm_div, div_le_one (by simpa [norm_pos_iff] using hfx₀K)]
    simpa [AddSubgroupClass.coe_norm] using hx₀ x
  set g : C(X, integerRing K) :=
    ⟨fun x => ⟨(f x : K) / (f x₀ : K), hbound x⟩,
      Continuous.subtype_mk
        ((continuous_subtype_val.comp (map_continuous f)).div_const _) hbound⟩ with hg
  have hfg : f = f x₀ • g := by
    ext x
    simp only [hg, ContinuousMap.smul_apply, smul_eq_mul, MulMemClass.coe_mul,
      ContinuousMap.coe_mk]
    field_simp
  have hμf : μ f = f x₀ * μ g := by
    conv_lhs => rw [hfg]
    rw [map_smul, smul_eq_mul]
  have hgle : ‖μ g‖ ≤ 1 := (μ g).2
  rw [hμf, hnorm, norm_mul]
  simpa using mul_le_mul_of_nonneg_left hgle (norm_nonneg (f x₀))

/-- Measures are automatically continuous (TeX 765). -/
theorem continuous (μ : MeasureR K X) : Continuous μ :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f g => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub]
    exact norm_apply_le μ (f - g)).continuous

/-- Measures agreeing on locally constant functions agree (the density
half of RJW Rem 3.8; via the general ultrametric approximation lemma). -/
theorem ext_locallyConstant {μ ν : MeasureR K X}
    (h : ∀ Φ : LocallyConstant X (integerRing K),
      μ Φ.toContinuousMap = ν Φ.toContinuousMap) :
    μ = ν := by
  refine LinearMap.ext fun f => eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨Φ, hΦ⟩ := PadicMeasure.exists_locallyConstant_norm_sub_le' f hε
  have hΦn : ‖f - Φ.toContinuousMap‖ ≤ ε :=
    (ContinuousMap.norm_le _ hε.le).2 fun x => by simpa using hΦ x
  have key : μ f - ν f = μ (f - Φ.toContinuousMap) + -(ν (f - Φ.toContinuousMap)) := by
    simp only [map_sub, h Φ]
    ring
  rw [dist_eq_norm, key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact (max_le (norm_apply_le μ _) (norm_apply_le ν _)).trans hΦn

end compact

end MeasureR

end PadicLFunctions
