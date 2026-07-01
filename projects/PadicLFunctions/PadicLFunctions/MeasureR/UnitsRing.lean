/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.MeasureR.Fubini
import PadicLFunctions.MeasureR.UnitsZp

/-!
# The Iwasawa algebra of the units over the integer ring of a field

RJW Eq 3.11 / Rem 3.33 over `R := integerRing K`: the convolution ring
`Λ_R(ℤ_p^×)` (commutativity via Fubini, associativity by the triple-integral
computation), Dirac multiplicativity `[u]·[v] = [uv]`, and the degree
(augmentation) map. This is the §5-needed part of the `ℤ_p`-layer
`PadicLFunctions/Measure/PseudoMeasure.lean`; the pseudo-measure theory
itself stays at `ℤ_p` coefficients (decomposition W-r4 scope note).
-/

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

/-- Convolution on `Λ_R(ℤ_p^×)` (RJW Eq 3.11, TeX 1173–1175):
`∫ f d(μ⋆ν) = ∫∫ f(xy) dν(y) dμ(x)`. -/
def unitsConv (μ ν : MeasureR K ℤ_[p]ˣ) : MeasureR K ℤ_[p]ˣ where
  toFun f := μ (innerInt K ν (f.comp (PadicMeasure.unitsMulCM₂ p)))
  map_add' f g := by rw [ContinuousMap.add_comp, innerInt_add, map_add]
  map_smul' c f := by rw [ContinuousMap.smul_comp, innerInt_smul, map_smul, RingHom.id_apply]

instance : Mul (MeasureR K ℤ_[p]ˣ) := ⟨unitsConv p K⟩

instance : One (MeasureR K ℤ_[p]ˣ) := ⟨dirac K ℤ_[p]ˣ 1⟩

variable {p K}

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
lemma units_mul_def (μ ν : MeasureR K ℤ_[p]ˣ) : μ * ν = unitsConv p K μ ν := rfl

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
@[simp]
lemma units_mul_apply (μ ν : MeasureR K ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, integerRing K)) :
    (μ * ν) f = μ (innerInt K ν (f.comp (PadicMeasure.unitsMulCM₂ p))) := rfl

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
lemma units_one_def : (1 : MeasureR K ℤ_[p]ˣ) = dirac K ℤ_[p]ˣ 1 := rfl

variable (p K)

/-- The Iwasawa algebra `Λ_R(ℤ_p^×)` as a commutative ring under convolution
(RJW Rem 3.11 "One checks that this does give an algebra structure" +
Rem 3.33). Commutativity is the Fubini swap. -/
instance : CommRing (MeasureR K ℤ_[p]ˣ) where
  mul_assoc a b c := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt K b ((innerInt K c (f.comp (PadicMeasure.unitsMulCM₂ p))).comp
        (PadicMeasure.unitsMulCM₂ p)))
      = a (innerInt K (unitsConv p K b c) (f.comp (PadicMeasure.unitsMulCM₂ p)))
    congr 1
    ext x
    refine congrArg Subtype.val ?_
    change b _ = b _
    congr 1
    ext y
    refine congrArg Subtype.val ?_
    change c _ = c _
    congr 1
    ext z
    exact congrArg Subtype.val (congrArg f (mul_assoc x y z))
  one_mul a := by
    refine LinearMap.ext fun f => ?_
    change a ((f.comp (PadicMeasure.unitsMulCM₂ p)).curry 1) = a f
    congr 1
    ext y
    exact congrArg Subtype.val (congrArg f (one_mul y))
  mul_one a := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt K (dirac K ℤ_[p]ˣ 1) (f.comp (PadicMeasure.unitsMulCM₂ p))) = a f
    congr 1
    ext x
    exact congrArg Subtype.val (congrArg f (mul_one x))
  left_distrib a b c := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt K (b + c) (f.comp (PadicMeasure.unitsMulCM₂ p))) = _
    rw [innerInt_measure_add, map_add]
    rfl
  right_distrib a b c := by
    refine LinearMap.ext fun f => ?_
    change (a + b) (innerInt K c (f.comp (PadicMeasure.unitsMulCM₂ p))) = _
    rw [LinearMap.add_apply]
    rfl
  zero_mul a := LinearMap.ext fun f => rfl
  mul_zero a := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt K (0 : MeasureR K ℤ_[p]ˣ) (f.comp (PadicMeasure.unitsMulCM₂ p))) = 0
    rw [innerInt_measure_zero, map_zero]
  mul_comm a b := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt K b (f.comp (PadicMeasure.unitsMulCM₂ p)))
      = b (innerInt K a (f.comp (PadicMeasure.unitsMulCM₂ p)))
    rw [integral_swap]
    congr 1
    ext y
    refine congrArg Subtype.val ?_
    change a _ = a _
    congr 1
    ext x
    exact congrArg Subtype.val (congrArg f (mul_comm x y))

variable {p K}

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- `[u]·[v] = [uv]` in `Λ_R(ℤ_p^×)`. -/
@[simp]
theorem units_dirac_mul_dirac (u v : ℤ_[p]ˣ) :
    (dirac K ℤ_[p]ˣ u : MeasureR K ℤ_[p]ˣ) * dirac K ℤ_[p]ˣ v
      = dirac K ℤ_[p]ˣ (u * v) :=
  LinearMap.ext fun _f => rfl

variable (p K)

/-- The degree (augmentation) map `Λ_R(ℤ_p^×) → R`, `μ ↦ ∫ 1 dμ`
(RJW Def 3.37, TeX 1245–1253). -/
def deg : MeasureR K ℤ_[p]ˣ →+* integerRing K where
  toFun μ := μ 1
  map_one' := rfl
  map_mul' μ ν := by
    change μ (innerInt K ν ((1 : C(ℤ_[p]ˣ, integerRing K)).comp
      (PadicMeasure.unitsMulCM₂ p))) = μ 1 * ν 1
    have h1 : innerInt K ν ((1 : C(ℤ_[p]ˣ, integerRing K)).comp (PadicMeasure.unitsMulCM₂ p))
        = ν 1 • (1 : C(ℤ_[p]ˣ, integerRing K)) := by
      ext x
      refine congrArg Subtype.val ?_
      change ν (1 : C(ℤ_[p]ˣ, integerRing K)) = _
      simp [smul_eq_mul]
    rw [h1, map_smul, smul_eq_mul, mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl

end MeasureR

end

end PadicLFunctions
