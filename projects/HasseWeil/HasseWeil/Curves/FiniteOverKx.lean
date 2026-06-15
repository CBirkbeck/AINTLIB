import HasseWeil.Auxiliary.Universal
import HasseWeil.Curves.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Localization.Finiteness

/-!
# `K(C)` as a finite extension of `K(x)`

For a smooth plane curve `C` over a field `F`, the coordinate ring `F[C]`
is a free module of rank `2` over `F[X]` with basis `{1, Y}`, and
consequently the function field `F(C)` is a degree-`2` extension of
`Frac(F[X]) = F(x)`.

This is a partial step toward ticket `T-II-1-005` (Silverman II.1.4); the
full statement additionally requires separability, which is handled in
`HasseWeil/Curves/Separable.lean`.

The existing file `HasseWeil/Basic.lean` proves essentially the same facts
but under `[W.toAffine.IsElliptic]`; this file drops that hypothesis so
that every smooth plane curve — elliptic or otherwise — has the result.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1.4
* [Silverman, III.3.1.1] (elliptic-curve specialization)
-/

open WeierstrassCurve

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

noncomputable instance coordinateRing_module_over_polynomialX :
    Module (Polynomial F) C.CoordinateRing :=
  Algebra.toModule

/-- The coordinate ring of a smooth plane curve is a free module over `F[X]`
with basis `{1, Y}`, hence finite.
Reference: `WeierstrassCurve.Affine.CoordinateRing.basis`. -/
instance coordinateRing_finite_over_polynomialX :
    Module.Finite (Polynomial F) C.CoordinateRing :=
  Module.Finite.of_basis (Affine.CoordinateRing.basis C.toAffine)

/-- The coordinate ring `F[C]` of a smooth plane curve has rank `2` over
`F[X]`.
Reference: Silverman III.3.1.1. -/
theorem finrank_coordinateRing_over_polynomialX :
    Module.finrank (Polynomial F) C.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (Affine.CoordinateRing.basis C.toAffine)).trans
    (Fintype.card_fin 2)

/-! ### Base change to `Frac F[X]` -/

set_option synthInstance.maxHeartbeats 40000 in
-- Instance synthesis climbs through the `F[X] → F[C] → F(C)` tower with
-- multiple `Algebra`/`IsScalarTower` steps, requiring extra heartbeats.
noncomputable instance faithfulSMul_polynomialX_functionField :
    FaithfulSMul (Polynomial F) C.FunctionField where
  eq_of_smul_eq_smul h := by
    have hinj : Function.Injective (algebraMap (Polynomial F) C.FunctionField) :=
      (IsFractionRing.injective C.CoordinateRing C.FunctionField).comp
        Affine.CoordinateRing.algebraMap_poly_injective
    refine hinj ?_
    have := h 1
    rwa [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at this

noncomputable instance algebra_fracRing_polynomialX_functionField :
    Algebra (FractionRing (Polynomial F)) C.FunctionField :=
  FractionRing.liftAlgebra (Polynomial F) C.FunctionField

noncomputable instance scalarTower_fracRing_polynomialX :
    IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) C.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra (Polynomial F) C.FunctionField

noncomputable instance isIntegral_polynomialX_coordinateRing :
    Algebra.IsIntegral (Polynomial F) C.CoordinateRing :=
  Algebra.IsIntegral.of_finite (Polynomial F) C.CoordinateRing

/-- **T-INFRA-IC-001**: `F[C]` is a Noetherian ring. `F[X]` is Noetherian, and
`F[C]` is module-finite over `F[X]`, so `F[C]` is a finitely-generated algebra
over a Noetherian ring, hence Noetherian. -/
instance isNoetherianRing_coordinateRing :
    IsNoetherianRing C.CoordinateRing :=
  Algebra.FiniteType.isNoetherianRing (Polynomial F) C.CoordinateRing

noncomputable instance faithfulSMul_polynomialX_coordinateRing :
    FaithfulSMul (Polynomial F) C.CoordinateRing where
  eq_of_smul_eq_smul h := by
    apply Affine.CoordinateRing.algebraMap_poly_injective (W' := C.toAffine)
    have := h 1
    rwa [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at this

noncomputable instance isLocalization_coordinateRing_functionField :
    IsLocalization
      (Algebra.algebraMapSubmonoid C.CoordinateRing (nonZeroDivisors (Polynomial F)))
      C.FunctionField := by
  have : Algebra.IsAlgebraic (Polynomial F) C.CoordinateRing :=
    Algebra.IsIntegral.isAlgebraic
  have := (FaithfulSMul.algebraMap_injective
    (Polynomial F) C.CoordinateRing).noZeroDivisors _
    (map_zero _) (map_mul _)
  exact (IsLocalization.iff_of_le_of_exists_dvd _
    (nonZeroDivisors C.CoordinateRing)
    (map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective (Polynomial F) C.CoordinateRing) le_rfl)
    fun s hs ↦
      have ⟨r, ne, eq⟩ :=
        (Algebra.IsAlgebraic.isAlgebraic (R := Polynomial F) s).exists_nonzero_dvd hs
      ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

noncomputable instance isLocalizedModule_functionField :
    IsLocalizedModule (nonZeroDivisors (Polynomial F))
      (IsScalarTower.toAlgHom (Polynomial F) C.CoordinateRing C.FunctionField).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

theorem isBaseChange_coordinateRing_functionField :
    IsBaseChange (FractionRing (Polynomial F))
      (IsScalarTower.toAlgHom (Polynomial F) C.CoordinateRing C.FunctionField).toLinearMap :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (Polynomial F)) ..).mp inferInstance

/-- `K(C)` is a finite module over `Frac F[X]`: since `F[C]` is finite over
`F[X]` and localizing preserves finiteness. -/
noncomputable instance finite_fracPolynomialX_functionField :
    Module.Finite (FractionRing (Polynomial F)) C.FunctionField :=
  @Module.Finite.of_isLocalization (Polynomial F) C.CoordinateRing
    (FractionRing (Polynomial F)) C.FunctionField _ _ _ _
    _ _ _ _ _ _ _ (nonZeroDivisors (Polynomial F))
    _ _ (C.coordinateRing_finite_over_polynomialX)

/-- **Silverman III.3.1.1** (without `IsElliptic` hypothesis): the function
field `F(C)` of a smooth plane curve is a degree-`2` extension of the
rational function field `F(x) = FractionRing F[X]`.
Reference: Silverman III.3.1.1. -/
theorem finrank_functionField_over_fracPolynomialX :
    Module.finrank (FractionRing (Polynomial F)) C.FunctionField = 2 := by
  rw [(isBaseChange_coordinateRing_functionField C).finrank_eq,
    finrank_coordinateRing_over_polynomialX]

/-! ### The coordinate function is transcendental -/

/-- The coordinate function `x ∈ F(C)`, i.e., the image of the formal
indeterminate `X : F[X]` under the composite
`F[X] → F[C] → F(C)`. Reference: Silverman II.1 discussion. -/
noncomputable def coordX : C.FunctionField :=
  algebraMap (Polynomial F) C.FunctionField Polynomial.X

/-- The composite algebra map `F[X] → F[C] → F(C)` is injective. -/
theorem algebraMap_polynomialX_functionField_injective :
    Function.Injective (algebraMap (Polynomial F) C.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq (Polynomial F) C.CoordinateRing C.FunctionField]
  exact (IsFractionRing.injective C.CoordinateRing C.FunctionField).comp
    Affine.CoordinateRing.algebraMap_poly_injective

/-- The coordinate function `x` is nonzero — it is the image of the formal
indeterminate under an injective algebra map. -/
theorem coordX_ne_zero : C.coordX ≠ 0 := by
  intro h
  rw [coordX, show (0 : C.FunctionField) =
    algebraMap (Polynomial F) C.FunctionField 0 from (map_zero _).symm] at h
  exact Polynomial.X_ne_zero (C.algebraMap_polynomialX_functionField_injective h)

/-- The coordinate function `y ∈ K(C)`, i.e., the image of the second
coordinate basis vector under the chain
`F[X][Y] ⧸ ⟨W⟩ → Frac(...)`. Defined via `CoordinateRing.basis` at index 1.
Together with `coordX`, generates `K(C)` as an `F`-algebra.
Reference: Silverman II.1 / III.3 discussion. -/
noncomputable def coordY : C.FunctionField :=
  algebraMap C.CoordinateRing C.FunctionField
    (Affine.CoordinateRing.basis C.toAffine 1)

/-- The coordinate function `y` is nonzero. -/
theorem coordY_ne_zero : C.coordY ≠ 0 := by
  unfold coordY
  have hinj : Function.Injective (algebraMap C.CoordinateRing C.FunctionField) :=
    IsFractionRing.injective _ _
  intro h
  have h2 : (Affine.CoordinateRing.basis C.toAffine 1 : C.CoordinateRing) = 0 := by
    apply hinj; rw [h, map_zero]
  exact (Affine.CoordinateRing.basis C.toAffine).ne_zero 1 h2

/-- The coordinate function `x` is transcendental over `F`.
Reference: Silverman II.1 (implicit in II.1.4 proof). -/
theorem transcendental_coordX : Transcendental F C.coordX := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have key : ∀ r : Polynomial F,
      Polynomial.aeval C.coordX r = algebraMap (Polynomial F) C.FunctionField r := by
    intro r
    induction r using Polynomial.induction_on' with
    | monomial n a =>
        rw [Polynomial.aeval_monomial, coordX, ← map_pow,
          ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          IsScalarTower.algebraMap_apply F (Polynomial F) C.FunctionField,
          Polynomial.algebraMap_eq]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  apply C.algebraMap_polynomialX_functionField_injective
  rw [← key p, ← key q, hpq]

end SmoothPlaneCurve

end HasseWeil.Curves
