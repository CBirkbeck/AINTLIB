/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.MahlerTransform

/-!
# The convolution algebra structure over the integer ring of a field

RJW §3.3 over `R := integerRing K`: the Iwasawa algebra `Λ_R(ℤ_p) =
ℳ(ℤ_p, R)`, with multiplication transported from `R⟦T⟧` along the Mahler
equivalence ("by transport of structure", Rem 3.11, TeX 908) and the
convolution formula proved on the Mahler basis via Chu–Vandermonde, exactly
as in the `ℤ_p`-layer `PadicLFunctions/Measure/Convolution.lean`.

## Main results

* `CommRing (MeasureR K ℤ_[p])` — the Iwasawa algebra `Λ_R(ℤ_p)`.
* `MeasureR.mahlerRingEquiv : MeasureR K ℤ_[p] ≃+* R⟦T⟧` — RJW Thm 3.20.
* `MeasureR.mul_apply` — the convolution formula (RJW Rem 3.11).
* `MeasureR.dirac_mul_dirac` — `[a]·[b] = [a+b]`.
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

instance : Mul (MeasureR K ℤ_[p]) :=
  ⟨fun μ ν => (mahlerLinearEquiv p K).symm
    (mahlerLinearEquiv p K μ * mahlerLinearEquiv p K ν)⟩

instance : One (MeasureR K ℤ_[p]) := ⟨dirac K ℤ_[p] 0⟩

variable {p K}

lemma mul_def (μ ν : MeasureR K ℤ_[p]) :
    μ * ν = (mahlerLinearEquiv p K).symm (mahlerLinearEquiv p K μ * mahlerLinearEquiv p K ν) :=
  rfl

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
lemma one_def : (1 : MeasureR K ℤ_[p]) = dirac K ℤ_[p] 0 := rfl

/-- The Mahler transform is multiplicative. -/
@[simp]
theorem mahlerTransform_mul (μ ν : MeasureR K ℤ_[p]) :
    mahlerTransform p K (μ * ν) = mahlerTransform p K μ * mahlerTransform p K ν := by
  rw [mul_def, ← mahlerLinearEquiv_apply, LinearEquiv.apply_symm_apply,
    mahlerLinearEquiv_apply, mahlerLinearEquiv_apply]

omit [CompleteSpace K] in
@[simp]
theorem mahlerTransform_one : mahlerTransform p K (1 : MeasureR K ℤ_[p]) = 1 := by
  rw [one_def, mahlerTransform_dirac, binomialSeries_zero, map_one]

omit [CompleteSpace K] in
@[simp]
theorem mahlerTransform_add (μ ν : MeasureR K ℤ_[p]) :
    mahlerTransform p K (μ + ν) = mahlerTransform p K μ + mahlerTransform p K ν := by
  ext n
  simp

omit [CompleteSpace K] in
@[simp]
theorem mahlerTransform_zero : mahlerTransform p K (0 : MeasureR K ℤ_[p]) = 0 := by
  ext n
  simp

variable (p K)

/-- The Iwasawa algebra `Λ_R(ℤ_p)` as a commutative ring (RJW Rem 3.11,
TeX 907–911; laws inherited from `R⟦T⟧` through the Mahler bijection). -/
instance : CommRing (MeasureR K ℤ_[p]) where
  mul_assoc a b c := mahlerTransform_injective (by simp [mul_assoc])
  one_mul a := mahlerTransform_injective (by simp)
  mul_one a := mahlerTransform_injective (by simp)
  left_distrib a b c := mahlerTransform_injective (by simp [mul_add])
  right_distrib a b c := mahlerTransform_injective (by simp [add_mul])
  zero_mul a := mahlerTransform_injective (by simp)
  mul_zero a := mahlerTransform_injective (by simp)
  mul_comm a b := mahlerTransform_injective (by simp [mul_comm])

/-- **RJW Theorem 3.20 over `R`**: the Mahler transform as a ring isomorphism
`ℳ(ℤ_p, 𝒪_L) ≅ 𝒪_L⟦T⟧`. -/
def mahlerRingEquiv : MeasureR K ℤ_[p] ≃+* PowerSeries (integerRing K) :=
  { mahlerLinearEquiv p K with
    map_mul' := mahlerTransform_mul }

/-- The inner convolution integrand `x ↦ ∫ f(x+y) dν(y)`. -/
def convInner (ν : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) :
    C(ℤ_[p], integerRing K) where
  toFun x := ν (f.comp ⟨fun y => x + y, by fun_prop⟩)
  continuous_toFun := by
    have key : ∀ x : ℤ_[p], f.comp (⟨fun y => x + y, by fun_prop⟩ : C(ℤ_[p], ℤ_[p]))
        = (ContinuousMap.curry ⟨fun q : ℤ_[p] × ℤ_[p] => f (q.1 + q.2), by fun_prop⟩) x :=
      fun x => ContinuousMap.ext fun y => rfl
    simp only [key]
    exact (MeasureR.continuous ν).comp (map_continuous _)

variable {p K}

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
@[simp]
lemma convInner_apply (ν : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) (x : ℤ_[p]) :
    convInner p K ν f x = ν (f.comp ⟨fun y => x + y, by fun_prop⟩) := rfl

/-- **The convolution formula** over `R` (RJW Rem 3.11, TeX 909):
`∫ φ d(μ*ν) = ∫ (∫ φ(x+y) dν(y)) dμ(x)`, by Chu–Vandermonde on the Mahler
basis + injectivity of the transform. -/
theorem mul_apply (μ ν : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) :
    (μ * ν) f = μ (convInner p K ν f) := by
  set ρ : MeasureR K ℤ_[p] :=
    { toFun := fun f => μ (convInner p K ν f)
      map_add' := fun f g => by
        rw [show convInner p K ν (f + g) = convInner p K ν f + convInner p K ν g from
          ContinuousMap.ext fun x => by simp [ContinuousMap.add_comp], map_add]
      map_smul' := fun c f => by
        rw [show convInner p K ν (c • f) = c • convInner p K ν f from
          ContinuousMap.ext fun x => by simp [ContinuousMap.smul_comp], map_smul,
          RingHom.id_apply] }
  suffices h : μ * ν = ρ by rw [h]; rfl
  apply mahlerTransform_injective
  refine PowerSeries.ext fun n => ?_
  rw [mahlerTransform_mul, PowerSeries.coeff_mul, coeff_mahlerTransform]
  change _ = μ (convInner p K ν (mahlerCM p K n))
  -- Chu–Vandermonde on the Mahler basis, mapped through the algebra map
  have hcomp : ∀ x : ℤ_[p],
      (mahlerCM p K n).comp (⟨fun y => x + y, by fun_prop⟩ : C(ℤ_[p], ℤ_[p]))
        = ∑ ij ∈ Finset.antidiagonal n,
            Ring.choose x ij.1 • (mahlerCM p K ij.2) := by
    intro x
    ext y
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, mahlerCM_apply,
      mahler_apply, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
      Pi.smul_apply]
    refine congrArg Subtype.val ?_
    rw [Ring.add_choose_eq n (Commute.all x y), map_sum]
    exact Finset.sum_congr rfl fun ij _ => by rw [map_mul, Algebra.smul_def]
  have key : convInner p K ν (mahlerCM p K n)
      = ∑ ij ∈ Finset.antidiagonal n,
          ν (mahlerCM p K ij.2) • (mahlerCM p K ij.1) := by
    ext x
    simp only [convInner_apply, hcomp x, map_sum, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    refine congrArg Subtype.val (Finset.sum_congr rfl fun ij _ => ?_)
    rw [← algebraMap_smul (integerRing K) (Ring.choose x ij.1), map_smul, smul_eq_mul,
      mahlerCM_apply, mahler_apply]
    ring
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_smul, smul_eq_mul, coeff_mahlerTransform, coeff_mahlerTransform, mul_comm]

/-- `δ_a * δ_b = δ_{a+b}` (`[a]·[b] = [a+b]`, RJW Ex 3.12/3.16). -/
@[simp]
theorem dirac_mul_dirac (a b : ℤ_[p]) :
    dirac K ℤ_[p] a * dirac K ℤ_[p] b = dirac K ℤ_[p] (a + b) := by
  apply mahlerTransform_injective
  rw [mahlerTransform_mul, mahlerTransform_dirac, mahlerTransform_dirac,
    mahlerTransform_dirac, ← map_mul, binomialSeries_add]

end MeasureR

end

end PadicLFunctions
