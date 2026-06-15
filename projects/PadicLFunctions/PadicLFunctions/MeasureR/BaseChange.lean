/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.UnitsRing

/-!
# Base change of p-adic measures along `ℤ_p → integerRing K`

The bridge between the `ℤ_p`-layer (`PadicMeasure`, §3/§4) and the
coefficient-general layer (`MeasureR`, the §5 widening): a measure
`μ ∈ Λ(ℤ_p)` extends to `Λ_R(ℤ_p)` by mapping its Mahler transform
coefficientwise through the algebra map (decomposition W4 — "the
scalar-extension map is the power-series inclusion under Mahler").

The characterising property is `baseChange_algCM`: on functions of the form
`algebraMap ∘ f` with `f` a `ℤ_p`-valued continuous function, the extended
measure integrates to the image of the original integral. Naturality with
respect to the toolbox operators follows by checking on locally constant
functions (`ext_locallyConstant`).
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

/-- Base change `Λ(ℤ_p) → Λ_R(ℤ_p)`: coefficientwise inclusion of Mahler
transforms (decomposition W4). -/
def baseChange : PadicMeasure p ℤ_[p] →+* MeasureR K ℤ_[p] :=
  ((mahlerRingEquiv p K).symm.toRingHom.comp
    ((PowerSeries.map (algebraMap ℤ_[p] (integerRing K))).comp
      (PadicMeasure.mahlerRingEquiv p).toRingHom))

variable {p K}

@[simp]
lemma mahlerTransform_baseChange (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p K (baseChange p K μ)
      = PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
          (PadicMeasure.mahlerTransform p μ) := by
  have h := (mahlerRingEquiv p K).apply_symm_apply
    (PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
      (PadicMeasure.mahlerTransform p μ))
  exact h

/-- `baseChange` sends Dirac measures to Dirac measures. -/
@[simp]
lemma baseChange_dirac (a : ℤ_[p]) :
    baseChange p K (PadicMeasure.dirac p a) = dirac K ℤ_[p] a := by
  apply mahlerTransform_injective
  rw [mahlerTransform_baseChange, PadicMeasure.mahlerTransform_dirac,
    mahlerTransform_dirac]

variable (K)

/-- The `R`-valued inclusion of a `ℤ_p`-valued continuous function. -/
def algCM (f : C(ℤ_[p], ℤ_[p])) : C(ℤ_[p], integerRing K) :=
  ⟨fun x => algebraMap ℤ_[p] (integerRing K) (f x),
    ((integerRing.isometry_algebraMap p K).continuous).comp (map_continuous f)⟩

omit [CompleteSpace K] in
@[simp]
lemma algCM_apply (f : C(ℤ_[p], ℤ_[p])) (x : ℤ_[p]) :
    algCM K f x = algebraMap ℤ_[p] (integerRing K) (f x) := rfl

omit [CompleteSpace K] in
lemma algCM_mahler (n : ℕ) : algCM K (mahler n) = mahlerCM p K n := rfl

variable {K}

/-- **The characterising property of base change**: integrating the inclusion
of a `ℤ_p`-valued function gives the inclusion of the integral. -/
theorem baseChange_algCM (μ : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    baseChange p K μ (algCM K f)
      = algebraMap ℤ_[p] (integerRing K) (μ f) := by
  rw [apply_eq_tsum (baseChange p K μ) (algCM K f),
    PadicMeasure.apply_eq_tsum p μ f]
  have hΔ : ∀ n, Δ_[1]^[n] (⇑(algCM K f)) 0
      = algebraMap ℤ_[p] (integerRing K) (Δ_[1]^[n] (⇑f) 0) := by
    intro n
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp []
  have hcoeff : ∀ n, baseChange p K μ (mahlerCM p K n)
      = algebraMap ℤ_[p] (integerRing K) (μ (mahler n)) := by
    intro n
    rw [← coeff_mahlerTransform, mahlerTransform_baseChange, PowerSeries.coeff_map,
      PadicMeasure.coeff_mahlerTransform]
  have hsum : Summable fun n =>
      Δ_[1]^[n] (⇑f) 0 * PadicMeasure.mahlerCoeff p μ n := by
    have h := (PadicInt.hasSum_mahler f).map μ.toAddMonoidHom (PadicMeasure.continuous p μ)
    have h2 := h.summable
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [show (PadicInt.mahlerTerm (Δ_[1]^[n] (⇑f) 0) n : C(ℤ_[p], ℤ_[p]))
        = (Δ_[1]^[n] (⇑f) 0) • mahler n from ContinuousMap.ext fun x => by
      simp [PadicInt.mahlerTerm_apply, smul_eq_mul, mul_comm], map_smul, smul_eq_mul]
    rfl
  calc ∑' n, Δ_[1]^[n] (⇑(algCM K f)) 0 * baseChange p K μ (mahlerCM p K n)
      = ∑' n, algebraMap ℤ_[p] (integerRing K)
          (Δ_[1]^[n] (⇑f) 0 * PadicMeasure.mahlerCoeff p μ n) := by
        refine tsum_congr fun n => ?_
        rw [hΔ n, hcoeff n, map_mul]
        rfl
    _ = algebraMap ℤ_[p] (integerRing K)
          (∑' n, Δ_[1]^[n] (⇑f) 0 * PadicMeasure.mahlerCoeff p μ n) :=
        (hsum.map_tsum (algebraMap ℤ_[p] (integerRing K))
          (integerRing.isometry_algebraMap p K).continuous).symm

omit [CompleteSpace K] in
/-- `algCM` is multiplicative. -/
lemma algCM_mul (f g : C(ℤ_[p], ℤ_[p])) :
    algCM K (f * g) = algCM K f * algCM K g :=
  ContinuousMap.ext fun x => by simp [algCM_apply]

omit [CompleteSpace K] in
/-- The inclusion of a `ℤ_p`-valued indicator is the `R`-valued indicator. -/
lemma algCM_charFn {U : Set ℤ_[p]} (hU : IsClopen U) :
    algCM K (LocallyConstant.charFn ℤ_[p] hU : C(ℤ_[p], ℤ_[p]))
      = charFnCM K ℤ_[p] hU := by
  refine ContinuousMap.ext fun x => ?_
  rw [algCM_apply, charFnCM_apply]
  change algebraMap ℤ_[p] (integerRing K) (U.indicator 1 x) = U.indicator 1 x
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply,
      map_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, map_zero]

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- A locally constant `R`-valued function is an `R`-linear combination of
indicators of its (clopen) fibres. -/
lemma locallyConstant_eq_sum_smul_charFn (Φ : LocallyConstant ℤ_[p] (integerRing K)) :
    (Φ.toContinuousMap : C(ℤ_[p], integerRing K))
      = ∑ v ∈ Φ.range_finite.toFinset,
          v • charFnCM K ℤ_[p] (Φ.isLocallyConstant.isClopen_fiber v) := by
  refine ContinuousMap.ext fun x => ?_
  rw [ContinuousMap.sum_apply, Finset.sum_eq_single (Φ x)]
  · have hx : x ∈ {x' | Φ.toFun x' = Φ x} := rfl
    rw [ContinuousMap.smul_apply, charFnCM_apply, Set.indicator_of_mem hx,
      Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  · intro v _ hv
    have hx : x ∉ {x' | Φ.toFun x' = v} :=
      fun hmem => hv (show Φ x = v from hmem).symm
    rw [ContinuousMap.smul_apply, charFnCM_apply, Set.indicator_of_notMem hx,
      smul_zero]
  · intro hx
    exact absurd (Φ.range_finite.mem_toFinset.mpr (Set.mem_range_self x)) hx

/-- **Base change commutes with multiplication by `ℤ_p`-valued functions**
(the W4 naturality leaf for the toolbox operators): checked on locally
constant functions through the fibre-indicator decomposition. -/
theorem baseChange_cmul (g : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) :
    baseChange p K (PadicMeasure.cmul p g μ)
      = cmul p K (algCM K g) (baseChange p K μ) := by
  refine ext_locallyConstant fun Φ => ?_
  rw [locallyConstant_eq_sum_smul_charFn (K := K) Φ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rw [← algCM_charFn (K := K) (Φ.isLocallyConstant.isClopen_fiber v),
    show cmul p K (algCM K g) (baseChange p K μ)
        (algCM K (LocallyConstant.charFn ℤ_[p]
          (Φ.isLocallyConstant.isClopen_fiber v) : C(ℤ_[p], ℤ_[p])))
      = baseChange p K μ (algCM K g
        * algCM K (LocallyConstant.charFn ℤ_[p]
          (Φ.isLocallyConstant.isClopen_fiber v) : C(ℤ_[p], ℤ_[p])))
    from rfl,
    ← algCM_mul, baseChange_algCM, baseChange_algCM]
  rfl

/-- Base change commutes with clopen restriction. -/
theorem baseChange_res {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) :
    baseChange p K (PadicMeasure.res p hU μ)
      = res p K hU (baseChange p K μ) := by
  rw [PadicMeasure.res, baseChange_cmul, algCM_charFn]
  rfl

end MeasureR

end

end PadicLFunctions
