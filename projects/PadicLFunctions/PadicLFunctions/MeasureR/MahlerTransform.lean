/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Measure.MahlerTransform
import PadicLFunctions.MeasureR.Basic
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The Mahler transform over the integer ring of a nonarchimedean field

The coefficient-general Mahler/Amice transform (RJW §3.4, Thm 3.20) for
measures valued in `R := integerRing K`: `𝓐_μ(T) = ∑_n (∫ binom(x,n) dμ) Tⁿ ∈
R⟦T⟧`, a linear equivalence `MeasureR K ℤ_[p] ≃ R⟦T⟧`. The analytic input is
mathlib's coefficient-general Mahler theory (`PadicInt.hasSum_mahler` over any
complete ultrametric normed `ℤ_[p]`-module). This is the `R`-coefficient layer
of `PadicLFunctions/Measure/MahlerTransform.lean` (see the TW2 replan note).

## Main definitions

* `MeasureR.mahlerCM` — the Mahler basis as `R`-valued continuous functions.
* `MeasureR.mahlerTransform` — the Amice transform `𝓐_μ ∈ R⟦T⟧`.
* `MeasureR.ofPowerSeries` — the inverse.
* `MeasureR.mahlerLinearEquiv` — RJW Thm 3.20 over `R`, linear part.
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

/-- The Mahler basis function `binom(x, n)`, viewed in `C(ℤ_[p], integerRing K)`
through the (isometric) algebra map. -/
def mahlerCM (n : ℕ) : C(ℤ_[p], integerRing K) :=
  ⟨fun x => algebraMap ℤ_[p] (integerRing K) (mahler n x),
    ((integerRing.isometry_algebraMap p K).continuous).comp (map_continuous _)⟩

omit [CompleteSpace K] in
@[simp]
lemma mahlerCM_apply (n : ℕ) (x : ℤ_[p]) :
    mahlerCM p K n x = algebraMap ℤ_[p] (integerRing K) (mahler n x) := rfl

variable {p K}

omit [CompleteSpace K] in
/-- mathlib's `mahlerTerm a n` (the summand of the Mahler expansion) is the
`R`-scalar multiple `a • mahlerCM n`. -/
private lemma mahlerTerm_eq (a : integerRing K) (n : ℕ) :
    (PadicInt.mahlerTerm a n : C(ℤ_[p], integerRing K)) = a • mahlerCM p K n := by
  ext x
  rw [PadicInt.mahlerTerm_apply, ContinuousMap.smul_apply, smul_eq_mul, mahlerCM_apply,
    Algebra.smul_def, mul_comm]

variable (p K)

/-- The Mahler transform `𝓐_μ(T) = ∑_n (∫ binom(x,n) dμ) Tⁿ` (RJW Def 3.15,
TeX 962–965, over `R`). -/
def mahlerTransform (μ : MeasureR K ℤ_[p]) : PowerSeries (integerRing K) :=
  PowerSeries.mk fun n => μ (mahlerCM p K n)

omit [CompleteSpace K] in
@[simp]
lemma coeff_mahlerTransform (μ : MeasureR K ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (mahlerTransform p K μ) = μ (mahlerCM p K n) := by
  simp [mahlerTransform]

/-- The Mahler transform as a linear map. -/
def mahlerTransformₗ :
    MeasureR K ℤ_[p] →ₗ[integerRing K] PowerSeries (integerRing K) where
  toFun := mahlerTransform p K
  map_add' _ _ := by ext n; simp [mahlerTransform]
  map_smul' _ _ := by ext n; simp [mahlerTransform]

variable {p K}

/-- **Evaluation formula** (RJW Thm 3.20 proof, TeX 995–998, over `R`):
`μ f = ∑' n, Δⁿf(0) * ∫ binom(x,n) dμ`. -/
theorem apply_eq_tsum (μ : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) :
    μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * μ (mahlerCM p K n) := by
  have h2 : HasSum (fun n => μ (PadicInt.mahlerTerm (Δ_[1]^[n] (⇑f) 0) n)) (μ f) :=
    (PadicInt.hasSum_mahler f).map μ.toAddMonoidHom (MeasureR.continuous μ)
  refine h2.tsum_eq.symm.trans (tsum_congr fun n => ?_)
  rw [mahlerTerm_eq, map_smul, smul_eq_mul]

variable (p K)

omit [CompleteSpace K] in
/-- The Mahler transform of a Dirac measure is the binomial series `(1+T)^a`,
pushed through the algebra map (RJW Ex 3.16, TeX 968–973). -/
@[simp]
theorem mahlerTransform_dirac (a : ℤ_[p]) :
    mahlerTransform p K (dirac K ℤ_[p] a)
      = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) (binomialSeries ℤ_[p] a) := by
  ext n
  rw [coeff_mahlerTransform, PowerSeries.coeff_map, binomialSeries_coeff, dirac_apply,
    mahlerCM_apply, mahler_apply]
  rw [smul_eq_mul, map_mul, map_one, mul_one]

variable {p K}

/-- Injectivity of the Mahler transform (RJW Thm 3.20 proof, "uniquely
determined", TeX 995–998). -/
theorem mahlerTransform_injective : Function.Injective (mahlerTransform p K) := by
  intro μ ν h
  refine LinearMap.ext fun f => ?_
  rw [apply_eq_tsum μ f, apply_eq_tsum ν f]
  refine tsum_congr fun n => ?_
  have hn : μ (mahlerCM p K n) = ν (mahlerCM p K n) := by
    simpa using congrArg (PowerSeries.coeff n) h
  rw [hn]

/-- Summability of the pairing series: Mahler coefficients tend to zero and
power-series coefficients are bounded (by integrality). -/
private lemma summable_fwdDiff_mul (f : C(ℤ_[p], integerRing K))
    (g : PowerSeries (integerRing K)) :
    Summable fun n => Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  have h := PadicInt.fwdDiff_tendsto_zero f
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
  calc ‖Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g‖
      ≤ ‖Δ_[1]^[n] (⇑f) 0‖ * ‖PowerSeries.coeff n g‖ := norm_mul_le _ _
    _ ≤ ‖Δ_[1]^[n] (⇑f) 0‖ * 1 :=
        mul_le_mul_of_nonneg_left (PowerSeries.coeff n g).2 (norm_nonneg _)
    _ = ‖Δ_[1]^[n] (⇑f) 0‖ := mul_one _

variable (p K)

/-- The measure attached to a power series `g`: `φ ↦ ∑' n, Δⁿφ(0) * g_n`
(RJW Thm 3.20 proof, converse direction, TeX 1000–1004). -/
def ofPowerSeries (g : PowerSeries (integerRing K)) : MeasureR K ℤ_[p] where
  toFun f := ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g
  map_add' f₁ f₂ := by
    simp only [ContinuousMap.coe_add, fwdDiff_iter_add, Pi.add_apply, add_mul]
    exact (summable_fwdDiff_mul f₁ g).tsum_add (summable_fwdDiff_mul f₂ g)
  map_smul' c f := by
    simp only [ContinuousMap.coe_smul, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact (summable_fwdDiff_mul f g).tsum_mul_left c

variable {p K}

omit [CompleteSpace K] in
/-- `Δⁿ(binom(·,k))(0) = δ_{nk}` over `R`, by pushing the `ℤ_p`-statement
through the algebra map. -/
private lemma fwdDiff_iter_mahlerCM_zero (n k : ℕ) :
    Δ_[1]^[n] (⇑(mahlerCM p K k)) 0 = if n = k then 1 else 0 := by
  have key : Δ_[1]^[n] (⇑(mahlerCM p K k)) 0
      = algebraMap ℤ_[p] (integerRing K)
          (Δ_[1]^[n] (⇑(mahler k : C(ℤ_[p], ℤ_[p]))) 0) := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mahlerCM_apply]
  rw [key, PadicMeasure.fwdDiff_iter_mahler_zero]
  split <;> simp

/-- The Mahler transform of `ofPowerSeries g` is `g` ("Visibly we have
𝓐_{μ_g} = g", TeX 1004). -/
@[simp]
theorem mahlerTransform_ofPowerSeries (g : PowerSeries (integerRing K)) :
    mahlerTransform p K (ofPowerSeries p K g) = g := by
  refine PowerSeries.ext fun k => ?_
  rw [coeff_mahlerTransform]
  change ∑' n, Δ_[1]^[n] (⇑(mahlerCM p K k)) 0 * PowerSeries.coeff n g
      = PowerSeries.coeff k g
  simp_rw [fwdDiff_iter_mahlerCM_zero, ite_mul, one_mul, zero_mul]
  exact tsum_ite_eq k _

variable (p K)

/-- **RJW Theorem 3.20 over `R`, linear part**: the Mahler transform is a
linear equivalence `ℳ(ℤ_p, R) ≃ R⟦T⟧`. -/
def mahlerLinearEquiv :
    MeasureR K ℤ_[p] ≃ₗ[integerRing K] PowerSeries (integerRing K) :=
  { mahlerTransformₗ p K with
    invFun := ofPowerSeries p K
    left_inv := fun μ => by
      refine LinearMap.ext fun f => ?_
      change ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n (mahlerTransform p K μ) = μ f
      simp_rw [coeff_mahlerTransform]
      exact (apply_eq_tsum μ f).symm
    right_inv := mahlerTransform_ofPowerSeries (p := p) (K := K) }

omit [CompleteSpace K] in
@[simp]
lemma mahlerTransform_smul (w : integerRing K) (μ : MeasureR K ℤ_[p]) :
    mahlerTransform p K (w • μ)
      = PowerSeries.C w * mahlerTransform p K μ := by
  rw [← PowerSeries.smul_eq_C_mul]
  exact map_smul (mahlerTransformₗ p K) w μ

omit [CompleteSpace K] in
@[simp]
lemma mahlerTransform_sub (μ ν : MeasureR K ℤ_[p]) :
    mahlerTransform p K (μ - ν)
      = mahlerTransform p K μ - mahlerTransform p K ν :=
  map_sub (mahlerTransformₗ p K) μ ν

@[simp]
lemma mahlerLinearEquiv_apply (μ : MeasureR K ℤ_[p]) :
    mahlerLinearEquiv p K μ = mahlerTransform p K μ := rfl

@[simp]
lemma mahlerLinearEquiv_symm_apply (g : PowerSeries (integerRing K)) :
    (mahlerLinearEquiv p K).symm g = ofPowerSeries p K g := rfl

end MeasureR

end

end PadicLFunctions
