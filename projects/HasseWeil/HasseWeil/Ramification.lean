import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.GaussLemma

import HasseWeil.Isogeny
import HasseWeil.Valuation

/-!
# Ramification Theory for Elliptic Curve Isogenies

We connect mathlib's `Ideal.ramificationIdx` and `Ideal.inertiaDeg` to the
theory of elliptic curve isogenies, specializing the general framework from
`Mathlib.NumberTheory.RamificationInertia` to coordinate ring extensions.

For an isogeny `φ : E₁ → E₂`, the pullback `φ* : K(E₂) →ₐ[F] K(E₁)` restricts to
a ring homomorphism on coordinate rings. The ramification index `e_P(φ)` at a
prime `P` of `R₁ = K[E₁]` is `Ideal.ramificationIdx (φ*.restrict) p P` where
`p = φ*⁻¹(P)` is the prime of `R₂ = K[E₂]` below `P`.

## Main results

* `HasseWeil.coordinateRing_isDedekindDomain`: the coordinate ring of an elliptic curve
  is a Dedekind domain. Proved via `IsIntegralClosure.isDedekindDomain`: the coordinate
  ring `R = F[X][Y]/(W)` is the integral closure of the PID `F[X]` in the function field
  `K(E) = Frac(R)`, and `K(E)/F(X)` is a finite separable extension of degree 2.
* `HasseWeil.coordinateRing_isIntegrallyClosed`: the coordinate ring is integrally closed
  in its fraction field, via `IsIntegrallyClosed.of_localization_maximal` together with
  principality of the maximal ideal at every localization.
* `HasseWeil.coordinateRing_dimensionLEOne`: the coordinate ring has Krull dimension at
  most 1 (every nonzero prime is maximal), from the principal ideal theorem.

## Strategy

The `IsIntegralClosure.isDedekindDomain` route shows that `CoordinateRing` is the integral
closure of the PID `F[X]` in the function field. The key steps:

1. **`F[X]` is Dedekind**: it is a PID, hence Dedekind (automatic from mathlib).
2. **`CoordinateRing` is integrally closed**: via `IsIntegrallyClosed.of_localization_maximal`,
   each localization at a nonzero maximal ideal `P` is a DVR (hence integrally closed). The
   DVR property follows from the TFAE for Noetherian local domains of dimension `≤ 1` with a
   principal maximal ideal; principality (`maximalIdeal_isPrincipal_of_nonsingular`) uses
   nonsingularity at each closed point (`Δ ≠ 0`), via the Jacobian identity and a case split
   on the characteristic.
3. **`CoordinateRing` is the integral closure of `F[X]` in `FunctionField`**: elements
   integral over `F[X]` are integral over `CoordinateRing` (by `tower_top`), hence lie in
   `CoordinateRing` (by step 2 and `isIntegrallyClosed_iff`).
4. **`FunctionField / FractionRing(F[X])` is finite** of degree 2.
5. **`FunctionField / FractionRing(F[X])` is separable**: from `finSepDegree` dividing 2 and
   the existence of a separable root (the Weierstrass polynomial has nonzero Y-derivative).
6. **Apply `IsIntegralClosure.isDedekindDomain`**: combines all the above.

## Implementation notes

This file is open infrastructure for the full isogeny ramification theory (the degree-sum
formula `deg φ = Σ e_P · f_P`, unramifiedness of separable isogenies, and equal fibre sizes
from translation invariance are not yet formalised here). The Dedekind-domain results it
provides are complete and axiom-clean.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2, III.4.10
-/

open WeierstrassCurve Polynomial Ideal IntermediateField
open scoped Polynomial.Bivariate nonZeroDivisors IntermediateField

namespace HasseWeil

variable {F : Type*} [Field F]

-- The coordinate ring `F[X][Y]/(W)` is Noetherian as a quotient of `F[X][Y]`; this is the
-- mathlib instance `AdjoinRoot.instIsNoetherianRing`.
example (E : Affine F) : IsNoetherianRing E.CoordinateRing := inferInstance

private theorem polynomial_mem_nonZeroDivisors (E : Affine F) [E.IsElliptic] :
    E.polynomial ∈ (F[X][Y])⁰ :=
  mem_nonZeroDivisors_of_ne_zero (Irreducible.ne_zero Affine.irreducible_polynomial)

private theorem coordinateRing_krullDimLE_one (E : Affine F) [E.IsElliptic] :
    Ring.KrullDimLE 1 E.CoordinateRing := by
  rw [Ring.krullDimLE_iff]
  have h1 : ringKrullDim E.CoordinateRing + 1 ≤ ringKrullDim (F[X][Y]) :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor (polynomial_mem_nonZeroDivisors E)
  have h2 : ringKrullDim (F[X][Y]) = (1 : ℕ) + 1 := by
    simp [Polynomial.ringKrullDim_of_isNoetherianRing]
  rw [h2] at h1
  rwa [ENat.WithBot.add_le_add_one_right_iff] at h1

/-- Every nonzero prime ideal of the coordinate ring of an elliptic curve is maximal.
This is `Ring.DimensionLEOne`, which follows from Krull dimension ≤ 1. -/
instance coordinateRing_dimensionLEOne (E : Affine F) [E.IsElliptic] :
    Ring.DimensionLEOne E.CoordinateRing where
  maximalOfPrime hp hp' :=
    ((Ring.krullDimLE_one_iff_of_noZeroDivisors (R := E.CoordinateRing)).mp
      (coordinateRing_krullDimLE_one E)) _ hp hp'

private lemma quotient_comp_of_eq {E : Affine F}
    (P : Ideal E.CoordinateRing) :
    let π : E.CoordinateRing →+* (E.CoordinateRing ⧸ P) := Ideal.Quotient.mk P
    let φ : F →+* (E.CoordinateRing ⧸ P) := π.comp ((AdjoinRoot.of E.polynomial).comp C)
    let x₀ := π (AdjoinRoot.mk E.polynomial (C X))
    π.comp (AdjoinRoot.of E.polynomial) =
      (Polynomial.evalRingHom x₀).comp (Polynomial.mapRingHom φ) := by
  intro π φ x₀; apply RingHom.ext; intro p
  change π ((AdjoinRoot.mk E.polynomial) (C p)) = (Polynomial.map φ p).eval x₀
  rw [Polynomial.eval_map]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add] at *; rw [hp, hq]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, show (Polynomial.monomial n a : F[X]) = C a * X ^ n from by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]]
    simp only [map_mul, map_pow]; rfl

private lemma quotient_mk_eq_base_evalEval {E : Affine F}
    (P : Ideal E.CoordinateRing) (g : F[X][Y]) :
    let π : E.CoordinateRing →+* (E.CoordinateRing ⧸ P) := Ideal.Quotient.mk P
    let φ : F →+* (E.CoordinateRing ⧸ P) := π.comp ((AdjoinRoot.of E.polynomial).comp C)
    let x₀ := π (AdjoinRoot.mk E.polynomial (C X))
    let y₀ := π (AdjoinRoot.root E.polynomial)
    π (AdjoinRoot.mk E.polynomial g) =
      (g.map (Polynomial.mapRingHom φ)).evalEval x₀ y₀ := by
  intro π φ x₀ y₀
  -- mk(g) = aeval root g = eval₂ of root g, and π preserves eval₂ by hom_eval₂.
  have : AdjoinRoot.mk E.polynomial g =
      g.eval₂ (AdjoinRoot.of E.polynomial) (AdjoinRoot.root E.polynomial) :=
    (AdjoinRoot.aeval_eq g).symm
  rw [this, Polynomial.hom_eval₂ g (AdjoinRoot.of E.polynomial) π
    (AdjoinRoot.root E.polynomial)]
  change g.eval₂ (π.comp (AdjoinRoot.of E.polynomial)) y₀ =
    (g.map (Polynomial.mapRingHom φ)).evalEval x₀ y₀
  conv_rhs => rw [show (g.map (Polynomial.mapRingHom φ)).evalEval x₀ y₀ =
    (g.map (Polynomial.mapRingHom φ)).eval₂ (Polynomial.evalRingHom x₀) y₀ from by
      rw [← Polynomial.eval₂_evalRingHom]]
  rw [Polynomial.eval₂_map]; congr 1; exact quotient_comp_of_eq P

private lemma nonsingular_at_maximal (E : Affine F) [E.IsElliptic]
    (P : Ideal E.CoordinateRing) (hPmax : P.IsMaximal) :
    AdjoinRoot.mk E.polynomial E.polynomialX ∉ P ∨
    AdjoinRoot.mk E.polynomial E.polynomialY ∉ P := by
  letI : P.IsPrime := hPmax.isPrime
  haveI : Field (E.CoordinateRing ⧸ P) := Ideal.Quotient.field P
  let φ : F →+* (E.CoordinateRing ⧸ P) :=
    (Ideal.Quotient.mk P).comp ((AdjoinRoot.of E.polynomial).comp C)
  let x₀ := (Ideal.Quotient.mk P) (AdjoinRoot.mk E.polynomial (C X))
  let y₀ := (Ideal.Quotient.mk P) (AdjoinRoot.root E.polynomial)
  have hΔ : E.Δ ≠ 0 := fun h ↦ not_isUnit_zero (h ▸ IsElliptic.isUnit (W := E))
  have hΔk : (E.map φ).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]; exact fun h ↦ hΔ (φ.injective (by rw [h, map_zero]))
  have hEq : (E.map φ).toAffine.Equation x₀ y₀ := by
    rw [Affine.Equation, Affine.map_polynomial,
      ← quotient_mk_eq_base_evalEval P E.polynomial, AdjoinRoot.mk_self]; rfl
  rcases ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔk).mp hEq).2 with hX | hY
  · left; intro hmem; exact hX (by
      rw [Affine.map_polynomialX, ← quotient_mk_eq_base_evalEval P E.polynomialX]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  · right; intro hmem; exact hY (by
      rw [Affine.map_polynomialY, ← quotient_mk_eq_base_evalEval P E.polynomialY]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

-- The mathlib `Algebra (Polynomial F) E.CoordinateRing` instance is `noncomputable`, so the
-- synthesizer cannot derive `Module` within `maxSynthPendingDepth = 3`. These explicit `Module`,
-- `Module.Finite`, and `Module.IsTorsionFree` instances let downstream synthesis find them.
noncomputable instance instModulePolynomialCoordinateRing (E : Affine F) :
    Module (Polynomial F) E.CoordinateRing :=
  @Algebra.toModule _ _ _ _ (Affine.CoordinateRing.instAlgebraPolynomial)

noncomputable instance instModuleFinitePolynomialCoordinateRing (E : Affine F) :
    Module.Finite (Polynomial F) E.CoordinateRing :=
  Affine.monic_polynomial.finite_adjoinRoot

noncomputable instance instIsTorsionFreePolynomialCoordinateRing (E : Affine F) [E.IsElliptic] :
    Module.IsTorsionFree (Polynomial F) E.CoordinateRing :=
  @AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero (Polynomial F) _ E.polynomial _
    (Irreducible.prime Affine.irreducible_polynomial)
    (by rw [Affine.degree_polynomial]; exact two_ne_zero)

/-- The algebra map `F[X] → E.CoordinateRing` is injective (the Weierstrass polynomial has
degree `> 0`, so the quotient map restricted to `F[X]` is an embedding). -/
theorem coordinateRing_algebraMap_injective (E : Affine F) :
    Function.Injective (algebraMap (Polynomial F) E.CoordinateRing) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [Affine.degree_polynomial]; exact two_ne_zero)

/-- `F[X]` acts faithfully on `E.CoordinateRing` (from the injective algebra map). -/
noncomputable instance coordinateRing_faithfulSMul (E : Affine F) [E.IsElliptic] :
    FaithfulSMul (Polynomial F) E.CoordinateRing := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact coordinateRing_algebraMap_injective E

/-- `F[X]` acts faithfully on `E.FunctionField` (lifts from `CoordinateRing` via fraction ring). -/
noncomputable instance functionField_faithfulSMul (E : Affine F) [E.IsElliptic] :
    FaithfulSMul (Polynomial F) E.FunctionField :=
  @FractionRing.instFaithfulSMul (Polynomial F) _ E.CoordinateRing _ _ _

/-- `FractionRing(F[X])` has an algebra structure on `E.FunctionField`. -/
noncomputable instance functionField_algebra_fractionRing (E : Affine F) [E.IsElliptic] :
    Algebra (FractionRing (Polynomial F)) E.FunctionField :=
  @FractionRing.liftAlgebra (Polynomial F) _ E.FunctionField _ _ (functionField_faithfulSMul E)

/-- The scalar tower `F[X] → FractionRing(F[X]) → FunctionField`. -/
noncomputable instance functionField_isScalarTower (E : Affine F) [E.IsElliptic] :
    IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) E.FunctionField :=
  @FractionRing.isScalarTower_liftAlgebra (Polynomial F) _ E.FunctionField _ _
    (functionField_faithfulSMul E)

attribute [local instance] FractionRing.liftAlgebra

-- Typeclass synthesis for FiniteDimensional over the tower FractionRing F[X] → K(E)
-- needs extra heartbeats.
/-- `E.FunctionField` is a finite-dimensional extension of `FractionRing(F[X])`. -/
noncomputable instance functionField_finiteDimensional (E : Affine F) [E.IsElliptic] :
    FiniteDimensional (FractionRing (Polynomial F)) E.FunctionField :=
  inferInstance

private theorem derivative_polynomial_eq_polynomialY (E : Affine F) :
    Polynomial.derivative E.polynomial = E.polynomialY := by
  simp only [Affine.polynomial, Affine.polynomialY, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X,
    zero_mul, zero_add, sub_zero, Nat.add_one_sub_one, pow_one, mul_one]; congr 1

-- Large `ring` over F[X][Y] needs extra heartbeats.
private lemma polynomialY_sq_eq_disc (E : Affine F) :
    E.polynomialY * E.polynomialY -
    C ((C E.a₁ * X + C E.a₃) ^ 2 + C 4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) =
    E.polynomial * C (C 4) := by
  simp only [Affine.polynomialY, Affine.polynomial, map_add, map_mul, map_pow, map_ofNat]; ring

-- AdjoinRoot rewriting over the bivariate polynomial ring needs extra heartbeats.
private lemma mk_polynomialY_sq (E : Affine F) :
    let d : F[X] := (C E.a₁ * X + C E.a₃) ^ 2 +
      C 4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)
    (AdjoinRoot.mk E.polynomial E.polynomialY) ^ 2 =
      AdjoinRoot.mk E.polynomial (C d) := by
  intro d; rw [sq, ← map_mul, AdjoinRoot.mk_eq_mk]
  exact ⟨C (C 4), polynomialY_sq_eq_disc E⟩

private lemma disc_not_in_P (E : Affine F)
    (P : Ideal E.CoordinateRing) [P.IsPrime]
    (hY : AdjoinRoot.mk E.polynomial E.polynomialY ∉ P) :
    let d : F[X] := (C E.a₁ * X + C E.a₃) ^ 2 +
      C 4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)
    AdjoinRoot.mk E.polynomial (C d) ∉ P := by
  intro d hd; apply hY
  have hmem : (AdjoinRoot.mk E.polynomial E.polynomialY) ^ 2 ∈ P := mk_polynomialY_sq E ▸ hd
  exact IsPrime.mem_of_pow_mem inferInstance 2 hmem

-- Large `ring` over `F[X][Y]` needs extra heartbeats.
private lemma four_polynomialX_eq_jacobi (E : Affine F) :
    C (C (4 : F)) * E.polynomialX =
      C (C (2 * E.a₁)) * E.polynomialY -
      C (C 2 * C E.a₁ * (C E.a₁ * X + C E.a₃) +
         C 4 * (C 3 * X ^ 2 + C (2 * E.a₂) * X + C E.a₄)) := by
  simp only [Affine.polynomialX, Affine.polynomialY, map_add, map_mul, map_pow, map_ofNat]
  ring

private lemma dprime_not_in_p (E : Affine F)
    (P : Ideal E.CoordinateRing) [P.IsPrime]
    (hY : AdjoinRoot.mk E.polynomial E.polynomialY ∈ P)
    (hX : AdjoinRoot.mk E.polynomial E.polynomialX ∉ P)
    (h4 : (4 : F) ≠ 0) :
    (C 2 * C E.a₁ * (C E.a₁ * X + C E.a₃) +
      C 4 * (C 3 * X ^ 2 + C (2 * E.a₂) * X + C E.a₄) : F[X]) ∉
    P.comap (algebraMap (Polynomial F) E.CoordinateRing) := by
  intro hd
  have hmk_dprime : AdjoinRoot.mk E.polynomial
      (C (C 2 * C E.a₁ * (C E.a₁ * X + C E.a₃) +
          C 4 * (C 3 * X ^ 2 + C (2 * E.a₂) * X + C E.a₄))) ∈ P := hd
  have hjac := congr_arg (AdjoinRoot.mk E.polynomial) (four_polynomialX_eq_jacobi E)
  simp only [map_mul, map_sub] at hjac
  have hmk_dprime' : AdjoinRoot.mk E.polynomial
      (C (C 2 * C E.a₁ * (C E.a₁ * X + C E.a₃) +
          C 4 * (C 3 * X ^ 2 + C 2 * C E.a₂ * X + C E.a₄))) ∈ P := by
    convert hmk_dprime using 2
    simp only [map_mul]
  have hlhs_in_P : AdjoinRoot.mk E.polynomial (C (C (4 : F))) *
      AdjoinRoot.mk E.polynomial E.polynomialX ∈ P := by
    rw [hjac]; exact sub_mem (Ideal.mul_mem_left _ _ hY) hmk_dprime'
  have h4inP : AdjoinRoot.mk E.polynomial (C (C (4 : F))) ∈ P :=
    ((Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance).mp hlhs_in_P).resolve_right hX
  -- `(4 : F)` is a unit (char ≠ 2), so its image in `R` is a unit, forcing `P = ⊤`.
  have h4unit_R : IsUnit (AdjoinRoot.mk E.polynomial (C (C (4 : F)))) := by
    have : C (C (4 : F)) = algebraMap F F[X][Y] 4 := by
      rw [show (4 : F) = ((4 : ℕ) : F) by norm_num]; simp
    rw [this]
    exact ((isUnit_iff_ne_zero.mpr h4).map (algebraMap F F[X][Y])).map (AdjoinRoot.mk E.polynomial)
  exact (IsPrime.ne_top inferInstance)
    (Ideal.eq_top_of_isUnit_mem P h4inP h4unit_R)

private lemma maximalIdeal_le_of_isField_quotient {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) (hField : IsField (R ⧸ J)) :
    IsLocalRing.maximalIdeal R ≤ J :=
  (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField J hField)).ge

-- Large polynomial manipulations plus AdjoinRoot pushes need extra heartbeats.
private lemma exists_coeffs_via_polynomialY (E : Affine F)
    (h2 : (2 : F) ≠ 0) (x : E.CoordinateRing) :
    ∃ a' b' : F[X],
      x = AdjoinRoot.mk E.polynomial (C a') +
          AdjoinRoot.mk E.polynomial (C b') * AdjoinRoot.mk E.polynomial E.polynomialY := by
  obtain ⟨a, b, hx⟩ := Affine.CoordinateRing.exists_smul_basis_eq x
  set inv2 : F := 2⁻¹
  have hinv_eq : (2 : F) * inv2 = 1 := mul_inv_cancel₀ h2
  have smul1 : a • (1 : E.CoordinateRing) = AdjoinRoot.mk E.polynomial (C a) := by
    rw [Affine.CoordinateRing.smul]; simp
  have smulY : b • (AdjoinRoot.mk E.polynomial Y : E.CoordinateRing) =
      AdjoinRoot.mk E.polynomial (C b) * AdjoinRoot.mk E.polynomial Y := by
    rw [Affine.CoordinateRing.smul]
  rw [smul1, smulY] at hx
  -- Change of basis `{1, Y} → {1, polynomialY}` via `Y = (polynomialY - C(a₁X+a₃))/2`:
  --   `C b * Y = C(C inv2 * b) * polynomialY - C(C inv2 * b * (a₁X + a₃))`.
  have poly_id : (C b * Y : F[X][Y]) =
      C (C inv2 * b) * E.polynomialY - C (C inv2 * b * (C E.a₁ * X + C E.a₃)) := by
    unfold Affine.polynomialY
    rw [show (C (C inv2 * b * (C E.a₁ * X + C E.a₃)) : F[X][Y]) =
        C (C inv2 * b) * C (C E.a₁ * X + C E.a₃) from map_mul _ _ _]
    have cinv2 : (C (C inv2 * b) : F[X][Y]) * (2 : F[X][Y]) = C b := by
      have h2eq : (2 : F[X][Y]) = C (C (2 : F)) := by
        rw [show (2 : F[X][Y]) = 1 + 1 from by ring,
            show (2 : F) = 1 + 1 from by ring]
        rw [map_add, map_add, map_one, map_one]
      rw [h2eq, ← map_mul]
      have hFX : (C inv2 * b * C 2 : F[X]) = b := by
        rw [show (C 2 : F[X]) = (C (2 : F) : F[X]) from rfl]
        rw [mul_comm _ (C 2), ← mul_assoc, ← map_mul]
        rw [show (2 : F) * inv2 = 1 from hinv_eq]
        rw [map_one, one_mul]
      rw [hFX]
    calc (C b * Y : F[X][Y])
        = C (C inv2 * b) * 2 * Y := by rw [cinv2]
      _ = C (C inv2 * b) * (2 * Y + C (C E.a₁ * X + C E.a₃)) -
          C (C inv2 * b) * C (C E.a₁ * X + C E.a₃) := by ring
  have poly_id_R := congr_arg (AdjoinRoot.mk E.polynomial) poly_id
  rw [map_sub] at poly_id_R
  refine ⟨a - C inv2 * b * (C E.a₁ * X + C E.a₃), C inv2 * b, ?_⟩
  rw [← hx]
  rw [show (AdjoinRoot.mk E.polynomial) (C b) * (AdjoinRoot.mk E.polynomial) Y =
      (AdjoinRoot.mk E.polynomial) (C b * Y) from by rw [map_mul]]
  rw [poly_id_R]
  rw [show (C (a - C inv2 * b * (C E.a₁ * X + C E.a₃)) : F[X][Y]) =
      C a - C (C inv2 * b * (C E.a₁ * X + C E.a₃)) from by rw [C_sub]]
  rw [map_sub, map_mul, map_mul]
  ring

/-- Case `mk(polynomialY) ∉ P` of `maximalIdeal_isPrincipal_of_nonsingular`: the
Y-discriminant `d` satisfies `d ∉ p = P ∩ F[X]`, so `W mod p` is squarefree over the residue
field `k = F[X]/p`, the quotient `R_P/J` (with `J = (p·R).map f`) is a field, and the maximal
ideal `P.map f` equals `J`, which is principal. -/
private theorem maximalIdeal_isPrincipal_case_polyY_notMem (E : Affine F) [E.IsElliptic]
    (P : Ideal E.CoordinateRing) (hPbot : P ≠ ⊥) (hPmax : P.IsMaximal)
    (hY : AdjoinRoot.mk E.polynomial E.polynomialY ∉ P) :
    (Ideal.map (algebraMap E.CoordinateRing (Localization.AtPrime P)) P).IsPrincipal := by
  letI := hPmax.isPrime
  haveI := IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) inferInstance
  set g := algebraMap (Polynomial F) E.CoordinateRing with hg_def
  set p := P.comap g with hp_def
  haveI : Algebra.IsIntegral (Polynomial F) E.CoordinateRing :=
    Algebra.IsIntegral.of_finite (Polynomial F) E.CoordinateRing
  suffices h : Ideal.map (algebraMap E.CoordinateRing (Localization.AtPrime P)) P =
      Ideal.map (algebraMap E.CoordinateRing (Localization.AtPrime P)) (Ideal.map g p) by
    rw [h]; exact inferInstance
  set f := algebraMap E.CoordinateRing (Localization.AtPrime P) with hf_def
  set J := Ideal.map f (Ideal.map g p) with hJ_def
  apply le_antisymm
  · rw [Localization.AtPrime.map_eq_maximalIdeal]
    apply maximalIdeal_le_of_isField_quotient
    have hg_inj : Function.Injective g := coordinateRing_algebraMap_injective E
    have hp_ne_bot : p ≠ ⊥ := by
      intro hp_bot; rw [hp_def] at hp_bot
      exact hPbot (eq_bot_of_comap_eq_bot hp_bot)
    have hJ_ne_top : J ≠ ⊤ := by
      intro hJ_top
      have : Ideal.map f P = ⊤ :=
        le_antisymm le_top (hJ_top ▸ Ideal.map_mono Ideal.map_comap_le)
      rw [Localization.AtPrime.map_eq_maximalIdeal] at this
      exact (IsLocalRing.maximalIdeal.isMaximal
        (R := Localization.AtPrime P)).ne_top this
    haveI : Nontrivial (Localization.AtPrime P ⧸ J) :=
      Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
    haveI : IsLocalRing (Localization.AtPrime P ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    haveI : Ring.DimensionLEOne (Localization.AtPrime P) :=
      Ring.DimensionLEOne.localization (Localization.AtPrime P)
        P.primeCompl_le_nonZeroDivisors
    haveI : Ring.KrullDimLE 0 (Localization.AtPrime P ⧸ J) := by
      apply Ring.KrullDimLE.mk₀; intro I hI
      set I' := I.comap (Ideal.Quotient.mk J) with hI'_def
      have hI'_prime : I'.IsPrime := Ideal.IsPrime.comap _
      have hI'_J : J ≤ I' := by
        rw [hI'_def]; intro x hx
        exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hx ▸ I.zero_mem)
      obtain ⟨q, hq_mem, hq_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp_ne_bot
      have hf_inj : Function.Injective f :=
        IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
      have hfgq_ne : f (g q) ≠ 0 := by
        intro h0; apply hq_ne; apply hg_inj; apply hf_inj
        rw [h0, map_zero, map_zero]
      have hfgq_in_I' : f (g q) ∈ I' :=
        hI'_J (Ideal.mem_map_of_mem f (Ideal.mem_map_of_mem g hq_mem))
      have hI'_ne_bot : I' ≠ ⊥ :=
        fun h ↦ hfgq_ne (h ▸ hfgq_in_I' : f (g q) ∈ (⊥ : Ideal _))
      have hI'_max : I'.IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime hI'_ne_bot hI'_prime
      have hI_eq : I = Ideal.map (Ideal.Quotient.mk J) I' :=
        (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I).symm
      rw [hI_eq]
      exact (Ideal.map_eq_top_or_isMaximal_of_surjective
        (f := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (I := I')
        hI'_max).resolve_left (fun h ↦ hI.ne_top (hI_eq ▸ h))
    -- `J` is radical because `Ideal.map g p` is radical and localization preserves radical.
    haveI : IsReduced (Localization.AtPrime P ⧸ J) := by
      rw [← Ideal.isRadical_iff_quotient_reduced]
      suffices h_rad : (Ideal.map g p).IsRadical by
        change J.IsRadical; rw [hJ_def, show f = algebraMap _ _ from hf_def]
        have h := IsLocalization.map_radical P.primeCompl
          (Localization.AtPrime P) (Ideal.map g p)
        rw [h_rad.radical] at h; exact h ▸ Ideal.radical_isRadical _
      -- (Ideal.map g p).IsRadical: transfer through R/(p·R) ≅ k[Y]/(Wbar).
      -- Wbar is separable (from the discriminant identity + d ∉ p),
      -- hence squarefree, hence isRadical.
      rw [Ideal.isRadical_iff_quotient_reduced]
      haveI : p.IsMaximal := Ideal.IsPrime.isMaximal
        (Ideal.IsPrime.comap (algebraMap (Polynomial F) E.CoordinateRing)) hp_ne_bot
      haveI : Field (F[X] ⧸ p) := Ideal.Quotient.field p
      set φ : F[X] →+* (F[X] ⧸ p) := Ideal.Quotient.mk p
      set Wbar := E.polynomial.map φ with hWbar_def
      -- R/(p·R) ≃+* (F[X]/p)[Y]/(Wbar)
      have hequiv := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot p E.polynomial
      -- Wbar is separable: use the identity polynomialY² - C(d) = W * C(C 4).
      -- After mapping through φ: (derivative Wbar)² - C(φ d) = Wbar * C(φ(C 4)).
      -- Since d ∉ p (from disc_not_in_P), C(φ d) is a unit in k[Y],
      -- so any common factor of Wbar and derivative Wbar divides a unit.
      set d : F[X] := (C E.a₁ * X + C E.a₃) ^ 2 +
        C 4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)
      have hd_not_in_P : AdjoinRoot.mk E.polynomial (C d) ∉ P := disc_not_in_P E P hY
      have hd_not_in_p : d ∉ p := by
        intro hd; rw [hp_def] at hd; exact hd_not_in_P hd
      have hφd_ne : φ d ≠ 0 := fun h ↦ hd_not_in_p (Ideal.Quotient.eq_zero_iff_mem.mp h)
      -- The mapped identity: (polynomialY.map φ)² - C(φ d) = Wbar * C(φ (C 4))
      have mapped_id : E.polynomialY.map φ * (E.polynomialY.map φ) - C (φ d) =
          Wbar * C (φ (C 4)) := by
        have := congr_arg (Polynomial.map φ) (polynomialY_sq_eq_disc E)
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at this
        exact this
      -- derivative(Wbar) = polynomialY.map φ
      have hderiv : Polynomial.derivative Wbar = E.polynomialY.map φ := by
        rw [hWbar_def, Polynomial.derivative_map, derivative_polynomial_eq_polynomialY]
      -- Prove Wbar.Separable via coprimality
      have hWbar_sqf : Squarefree Wbar := by
        intro z hz
        -- z^2 | Wbar → z | derivative Wbar (from pow_sub_one_dvd_derivative_of_pow_dvd)
        have hz_dvd_W : z ∣ Wbar := dvd_trans (dvd_mul_left z z) hz
        have hz_dvd_deriv : z ∣ Polynomial.derivative Wbar := by
          have := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (n := 2)
            (show z ^ 2 ∣ Wbar from sq z ▸ hz)
          rwa [pow_one] at this
        rw [hderiv] at hz_dvd_deriv
        -- z divides both Wbar and polynomialY.map φ, hence divides C(φ d), a unit.
        have hz_dvd_sq : z ∣ E.polynomialY.map φ * (E.polynomialY.map φ) :=
          dvd_mul_of_dvd_left hz_dvd_deriv _
        have hz_dvd_WC : z ∣ Wbar * C (φ (C 4)) := dvd_mul_of_dvd_left hz_dvd_W _
        have hz_dvd_Cd : z ∣ C (φ d) := by
          have : E.polynomialY.map φ * (E.polynomialY.map φ) - C (φ d) =
              Wbar * C (φ (C 4)) := mapped_id
          rw [sub_eq_iff_eq_add.mp this] at hz_dvd_sq
          exact (dvd_add_right hz_dvd_WC).mp hz_dvd_sq
        have hF := (Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp ‹p.IsMaximal›
        obtain ⟨b, hb⟩ := hF.mul_inv_cancel hφd_ne
        exact isUnit_of_dvd_unit hz_dvd_Cd
          ⟨⟨C (φ d), C b,
            by rw [← map_mul, hb, map_one],
            by rw [← map_mul, show b * φ d = 1 from mul_comm b (φ d) ▸ hb, map_one]⟩, rfl⟩
      -- Separable → squarefree → isRadical → reduced quotient
      letI kfield : Field (F[X] ⧸ p) := Ideal.Quotient.field p
      haveI : IsDomain (F[X] ⧸ p) := kfield.isDomain
      -- Transfer IsReduced through the ring equivalence hequiv.
      -- The codomain (F[X]/p)[Y]/(Wbar) is reduced since Wbar is squarefree.
      refine ⟨fun x hnil ↦ hequiv.injective (show hequiv x = hequiv 0 from ?_)⟩
      have hred : IsReduced ((F[X] ⧸ p)[X] ⧸
          span ({Wbar} : Set (F[X] ⧸ p)[X])) := by
        classical
        rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
        exact hWbar_sqf.isRadical
      exact (hred.eq_zero _ (hnil.map hequiv)).trans (map_zero hequiv).symm
    exact @Ring.KrullDimLE.isField_of_isReduced _ _ ‹_› ‹_› ‹_›
  · -- `J ≤ P.map f` follows from `p.map g ≤ P` (`map_comap_le`).
    exact Ideal.map_mono Ideal.map_comap_le

-- Very large case analysis over char = 2 vs char ≠ 2 branches, plus nested AdjoinRoot
-- arguments. Needs increased heartbeat budget.
private theorem maximalIdeal_isPrincipal_of_nonsingular (E : Affine F) [E.IsElliptic]
    (P : Ideal E.CoordinateRing) (_ : P ≠ ⊥) (hPmax : P.IsMaximal) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
  letI := hPmax.isPrime
  haveI := IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) inferInstance
  -- The maximal ideal m = P.map f where f = algebraMap R R_P.
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  -- The contraction p = P ∩ F[X] is maximal in the PID F[X], hence principal.
  set g := algebraMap (Polynomial F) E.CoordinateRing with hg_def
  set p := P.comap g with hp_def
  haveI : Algebra.IsIntegral (Polynomial F) E.CoordinateRing :=
    Algebra.IsIntegral.of_finite (Polynomial F) E.CoordinateRing
  -- Split on whether mk(polynomialY) ∉ P. If so, the discriminant identity gives a
  -- squarefree quotient. Otherwise, mk(polynomialX) ∉ P (from nonsingularity), and we
  -- use Valuation.localRing_isDVR to get the DVR/principality directly.
  by_cases hY : AdjoinRoot.mk E.polynomial E.polynomialY ∉ P
  · -- Case `mk(polynomialY) ∉ P`: discharged by the squarefree-quotient leaf lemma.
    exact maximalIdeal_isPrincipal_case_polyY_notMem E P ‹P ≠ ⊥› hPmax hY
  · -- Case `mk(polynomialY) ∈ P` (so `mk(polynomialX) ∉ P` by nonsingularity). Here `W mod p`
    -- need not be squarefree, so the `IsReduced` route fails. In char ≠ 2 we use the Jacobian
    -- identity `four_polynomialX_eq_jacobi` to factor the Y-discriminant `d = π · d₀` with
    -- `π ∤ d₀`, giving `P.map f = span {f(mk polynomialY)}`. In char 2 we split on whether the
    -- constant `δ = x₀³ + a₂x₀² + a₄x₀ + a₆` (with `x₀ = -a₃/a₁`) is a square: if so the point
    -- `(x₀, δ^½)` is a smooth k-point and `localRing_isDVR` applies; otherwise
    -- `P = span {mk(C(a₁X+a₃))}`.
    push Not at hY
    have hX := (nonsingular_at_maximal E P hPmax).resolve_right (fun h ↦ h hY)
    set f := algebraMap E.CoordinateRing (Localization.AtPrime P) with hf_def
    have hg_inj : Function.Injective g := coordinateRing_algebraMap_injective E
    have hp_ne_bot : p ≠ ⊥ := by
      intro hp_bot
      exact ‹P ≠ ⊥› (eq_bot_of_comap_eq_bot hp_bot)
    have hp_prime : p.IsPrime := Ideal.IsPrime.comap _
    haveI hp_maximal : p.IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hp_ne_bot hp_prime
    haveI hp_principal : p.IsPrincipal := IsPrincipalIdealRing.principal p
    by_cases h4 : (4 : F) = 0
    · -- Char 2 case (h4 : (4 : F) = 0).
      -- We split on whether a₁ = 0 (supersingular) or not (ordinary).
      -- In char 2, polynomialY = 2Y + C(a₁X + a₃) = C(a₁X + a₃) (since 2 = 0).
      -- The supersingular sub-case is vacuous: a₁ = 0 forces a₃ ≠ 0 (from
      -- Δ ≠ 0 in char 2 supersingular), then mk(polyY) = mk(C(C a₃)) is a unit
      -- in R (image of a non-zero F-element), contradicting hY : mk(polyY) ∈ P
      -- with P proper (a maximal ideal).
      --
      -- The ordinary sub-case (a₁ ≠ 0) and the general char=2 treatment remain
      -- open work (ticket T-II-1-001 closure plan; see PROOF_WRITEUP.md §4.11
      -- for R1c local-normality route).
      have h2 : (2 : F) = 0 := by
        have h2sq : (2 : F) ^ 2 = 0 := by
          have h2sq_eq : (2 : F) ^ 2 = 4 := by ring
          rw [h2sq_eq]; exact h4
        exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h2sq
      haveI hCharP : CharP F 2 :=
        (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      by_cases h_a1 : E.a₁ = 0
      · -- Supersingular: a₁ = 0 forces a₃ ≠ 0 (from Δ ≠ 0).
        -- Then mk(polyY) = mk(C(C a₃)) is the image of a unit, contradicting hY.
        exfalso
        have hΔ : E.Δ ≠ 0 := fun h ↦ not_isUnit_zero (h ▸ IsElliptic.isUnit (W := E))
        have ha3_ne : E.a₃ ≠ 0 := by
          intro h_a3
          apply hΔ
          rw [WeierstrassCurve.Δ_of_char_two, h_a1, h_a3]
          ring
        -- In char 2 with `a₁ = 0`, `polynomialY = C (C a₃)`, the image of a nonzero `F`-element,
        -- hence a unit — contradicting `mk(polyY) ∈ P` for the proper ideal `P`.
        have h_polyY_eq : E.polynomialY = C (C E.a₃) := by
          rw [Affine.polynomialY, h_a1]; simp [show (2 : F) = 0 from h2]
        rw [h_polyY_eq] at hY
        -- mk(C(C a₃)) = (algebraMap F E.CoordinateRing) a₃ via the chain
        -- F →+* F[X] →+* F[X][Y] →+* E.CoordinateRing.
        have h_mk_eq : AdjoinRoot.mk E.polynomial (C (C E.a₃)) =
            (algebraMap F E.CoordinateRing) E.a₃ := rfl
        rw [h_mk_eq] at hY
        -- (algebraMap F R) a₃ is a unit (a₃ ∈ F^×).
        have h_unit : IsUnit ((algebraMap F E.CoordinateRing) E.a₃) := by
          have h_a3_unit : IsUnit E.a₃ := isUnit_iff_ne_zero.mpr ha3_ne
          exact h_a3_unit.map (algebraMap F E.CoordinateRing)
        exact (Ideal.IsPrime.ne_top (hPmax.isPrime))
          (Ideal.eq_top_of_isUnit_mem P hY h_unit)
      · -- Ordinary sub-case (`a₁ ≠ 0`): `polyY = C c` with `c = a₁X + a₃` in char 2.
        set c : F[X] := C E.a₁ * X + C E.a₃ with hc_def
        have h_polyY_eq : E.polynomialY = C c := by
          rw [Affine.polynomialY, hc_def]; simp [show (2 : F) = 0 from h2, map_add, map_mul]
        have hc_in_p : c ∈ p := by
          change AdjoinRoot.mk E.polynomial (C c) ∈ P
          rw [← h_polyY_eq]; exact hY
        -- c ≠ 0 (a₁ ≠ 0 ⟹ coeff 1 of c is a₁ ≠ 0).
        have hc_ne_zero : c ≠ 0 := by
          intro h_c
          have h_coeff_1 : c.coeff 1 = E.a₁ := by rw [hc_def]; simp
          rw [h_c, Polynomial.coeff_zero] at h_coeff_1
          exact h_a1 h_coeff_1.symm
        -- p = Ideal.span {c}: p is principal containing c, c irreducible degree 1.
        have hp_eq_span_c : p = Ideal.span {c} := by
          obtain ⟨π, hπ_gen⟩ : ∃ π : F[X], p = Ideal.span {π} :=
            ⟨Submodule.IsPrincipal.generator p,
             (Ideal.span_singleton_generator p).symm⟩
          have hπ_dvd_c : π ∣ c := by
            rw [hπ_gen, Ideal.mem_span_singleton] at hc_in_p
            exact hc_in_p
          have h_deg_c : c.natDegree = 1 := by
            rw [hc_def]; exact Polynomial.natDegree_linear h_a1
          have hπ_in_p : π ∈ p := by rw [hπ_gen]; exact Ideal.subset_span rfl
          have hπ_ne_zero : π ≠ 0 := by
            intro hπ_zero
            apply hp_ne_bot
            rw [hπ_gen, hπ_zero, Ideal.span_singleton_eq_bot]
          have hπ_nonunit : ¬ IsUnit π := by
            intro hπ_unit
            apply hp_maximal.ne_top
            rw [hπ_gen]; exact Ideal.span_singleton_eq_top.mpr hπ_unit
          have h_deg_π_pos : 0 < π.natDegree := by
            rcases Nat.eq_zero_or_pos π.natDegree with h0 | hpos
            · exfalso; apply hπ_nonunit
              rcases Polynomial.natDegree_eq_zero.mp h0 with ⟨a, ha⟩
              have ha_ne : a ≠ 0 := by
                intro h_a; apply hπ_ne_zero; rw [← ha, h_a, map_zero]
              rw [← ha]; exact (isUnit_iff_ne_zero.mpr ha_ne).map C
            · exact hpos
          have h_deg_π : π.natDegree = 1 := by
            have h_π_le : π.natDegree ≤ c.natDegree :=
              Polynomial.natDegree_le_of_dvd hπ_dvd_c hc_ne_zero
            rw [h_deg_c] at h_π_le; omega
          -- Get the unit factor: from π ∣ c and same degree, c = π · u for unit u.
          obtain ⟨q, hq⟩ := hπ_dvd_c
          have h_q_ne : q ≠ 0 := by
            intro h_q; apply hc_ne_zero; rw [hq, h_q, mul_zero]
          have h_deg_q : q.natDegree = 0 := by
            have := Polynomial.natDegree_mul hπ_ne_zero h_q_ne
            rw [← hq, h_deg_c, h_deg_π] at this; omega
          rcases Polynomial.natDegree_eq_zero.mp h_deg_q with ⟨a, ha⟩
          have h_a_ne : a ≠ 0 := by
            intro h_a; apply h_q_ne; rw [← ha, h_a, map_zero]
          have h_q_unit : IsUnit q := by
            rw [← ha]; exact (isUnit_iff_ne_zero.mpr h_a_ne).map C
          -- Associated π c via the unit q.
          have h_assoc : Associated π c := by
            refine ⟨h_q_unit.unit, ?_⟩
            change π * (h_q_unit.unit : F[X]) = c
            rw [IsUnit.unit_spec]
            exact hq.symm
          rw [hπ_gen, Ideal.span_singleton_eq_span_singleton.mpr h_assoc]
        -- x₀ := -a₃/a₁ (in char 2, sign is irrelevant).
        -- a₁ ≠ 0 ⟹ a₁ is a unit in F (a field).
        have h_a1_unit : IsUnit E.a₁ := isUnit_iff_ne_zero.mpr h_a1
        set x₀ : F := -E.a₃ / E.a₁ with hx0_def
        -- δ := x₀^3 + a₂·x₀^2 + a₄·x₀ + a₆.
        set δ : F := x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆ with hδ_def
        -- Key identity in char 2 ordinary: a₁·x₀ + a₃ = 0
        -- (since x₀ = -a₃/a₁, so a₁·x₀ = -a₃, and in char 2, -a₃ + a₃ = 0).
        have h_a1x0_eq : E.a₁ * x₀ = -E.a₃ := by
          rw [hx0_def, mul_div_cancel₀ _ h_a1]
        have h_a1x0_a3 : E.a₁ * x₀ + E.a₃ = 0 := by
          rw [h_a1x0_eq, neg_add_cancel]
        -- c = a₁ · (X - x₀) in F[X]: i.e., a₁X + a₃ = a₁(X - x₀).
        have hc_eq_a1_Xsub : c = C E.a₁ * (X - C x₀) := by
          rw [hc_def]
          have : -(E.a₁ * x₀) = E.a₃ := by rw [h_a1x0_eq]; ring
          calc C E.a₁ * X + C E.a₃
              = C E.a₁ * X - C (E.a₁ * x₀) := by rw [← this, map_neg]; ring
            _ = C E.a₁ * X - C E.a₁ * C x₀ := by rw [map_mul]
            _ = C E.a₁ * (X - C x₀) := by ring
        -- (X - x₀) ∈ p (since c = a₁(X - x₀) ∈ p and a₁ unit).
        have hX_sub_x0_in_p : X - C x₀ ∈ p := by
          rw [hp_eq_span_c, Ideal.mem_span_singleton]
          refine ⟨C E.a₁⁻¹, ?_⟩
          rw [hc_eq_a1_Xsub]
          rw [show C E.a₁ * (X - C x₀) * C E.a₁⁻¹ =
              C E.a₁ * C E.a₁⁻¹ * (X - C x₀) from by ring]
          rw [← map_mul, mul_inv_cancel₀ h_a1, map_one, one_mul]
        -- mk(C(X - x₀)) ∈ P (image of (X - x₀) ∈ p under g).
        have hmk_X_sub_x0 : AdjoinRoot.mk E.polynomial (C (X - C x₀)) ∈ P :=
          hX_sub_x0_in_p
        -- W = Y² + C c · Y - C(X³+a₂X²+a₄X+a₆) in char 2 (since 2Y = 0).
        have hW_char2 : E.polynomial =
            Y ^ 2 + C c * Y - C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) := by
          unfold Affine.polynomial
          rw [hc_def]
        -- mk(W) = 0 in R, so mk(Y²) = -mk(C c)·mk(Y) + mk(C(X³+a₂X²+a₄X+a₆)).
        have hmk_Ysq : AdjoinRoot.mk E.polynomial (Y ^ 2) =
            -(AdjoinRoot.mk E.polynomial (C c) * AdjoinRoot.mk E.polynomial Y) +
            AdjoinRoot.mk E.polynomial
              (C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) := by
          have hW_zero : AdjoinRoot.mk E.polynomial E.polynomial = 0 :=
            AdjoinRoot.mk_self
          rw [hW_char2] at hW_zero
          have heq : AdjoinRoot.mk E.polynomial (Y ^ 2) +
              AdjoinRoot.mk E.polynomial (C c) * AdjoinRoot.mk E.polynomial Y -
              AdjoinRoot.mk E.polynomial
                (C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := by
            rw [← map_mul, ← map_add, ← map_sub]; exact hW_zero
          linear_combination heq
        -- Polynomial identity: (X³+a₂X²+a₄X+a₆) - δ = (X - x₀) · w₃(X) where
        -- w₃(X) = X² + (x₀+a₂)X + (x₀² + a₂x₀ + a₄).
        set w₃ : F[X] := X ^ 2 + C (x₀ + E.a₂) * X + C (x₀ ^ 2 + E.a₂ * x₀ + E.a₄)
          with hw3_def
        have h_cubic_factor :
            X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆ - C δ =
              (X - C x₀) * w₃ := by
          rw [hw3_def, hδ_def]
          simp only [map_add, map_mul, map_pow]
          ring
        -- Case-split: δ a square in F, or not.
        by_cases h_sq : ∃ α : F, α ^ 2 = δ
        · -- SQUARE case: δ = α². (x₀, α) is on E and smooth, P = pointIdeal x₀ α.
          obtain ⟨α, hα⟩ := h_sq
          -- E.Equation x₀ α: α² + (a₁x₀+a₃)α = δ; LHS = α² + 0 = α² = δ.
          have h_eq : E.Equation x₀ α := by
            rw [Affine.equation_iff]
            show α ^ 2 + E.a₁ * x₀ * α + E.a₃ * α =
              x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆
            have : x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆ = δ := hδ_def.symm
            rw [this, ← hα]
            linear_combination α * h_a1x0_a3
          -- E.Nonsingular x₀ α via [IsElliptic] (Δ ≠ 0 implies any equation point is smooth).
          have h_ns : E.Nonsingular x₀ α := Affine.equation_iff_nonsingular.mp h_eq
          -- char 2 instances: F[X] and F[X][Y] inherit CharP 2 from F.
          haveI hCharP_FX : CharP F[X] 2 := Polynomial.charP
          haveI hCharP_FXY : CharP F[X][Y] 2 := Polynomial.charP
          -- 2 = 0 at every level (F[X], F[X][Y], R = AdjoinRoot _).
          have h_two_FX : (2 : F[X]) = 0 := by
            have := CharP.cast_eq_zero F[X] 2
            exact_mod_cast this
          have h_two_FXY : (2 : F[X][Y]) = 0 := by
            have := CharP.cast_eq_zero F[X][Y] 2
            exact_mod_cast this
          have h_two_R : (2 : E.CoordinateRing) = 0 := by
            have h1 : (2 : E.CoordinateRing) =
                AdjoinRoot.mk E.polynomial (2 : F[X][Y]) := by rw [map_ofNat]
            rw [h1, h_two_FXY, map_zero]
          -- Compute (mk(Y - C(C α)))² in R directly.
          -- Expand: (Y - C(C α))² = Y² - 2 C(C α) Y + (C(C α))² in F[X][Y].
          -- After applying mk and using h_two_R, the middle term vanishes.
          -- Then mk(Y²) reduces via hmk_Ysq, and (C(C α))² = C(C α²) = C(C δ).
          -- The result lies in (mk(C c)) ⊆ P.
          have h_YminusAlpha_sq_in_P :
              (AdjoinRoot.mk E.polynomial (Y - C (C α))) ^ 2 ∈ P := by
            -- Step A: (mk(Y - C(C α)))² = mk((Y - C(C α))²) = mk(Y²) + mk((C(C α))²) in R.
            have h_step : (AdjoinRoot.mk E.polynomial (Y - C (C α))) ^ 2 =
                AdjoinRoot.mk E.polynomial (Y ^ 2) +
                AdjoinRoot.mk E.polynomial ((C (C α)) ^ 2) := by
              rw [← map_pow]
              have h_expand : (Y - C (C α) : F[X][Y]) ^ 2 =
                  Y^2 - (2 : F[X][Y]) * C (C α) * Y + (C (C α))^2 := by ring
              rw [h_expand]
              rw [map_add, map_sub, map_pow, map_mul, map_mul]
              -- (2 : R) = 0 ⟹ 2 · mk(C(C α)) · mk Y = 0.
              have h_mk_two :
                  (AdjoinRoot.mk E.polynomial (2 : F[X][Y])) = 0 := by
                rw [h_two_FXY]; exact map_zero _
              rw [show (AdjoinRoot.mk E.polynomial 2 : E.CoordinateRing) =
                  AdjoinRoot.mk E.polynomial (2 : F[X][Y]) from rfl,
                  h_mk_two, zero_mul, zero_mul, sub_zero]
            rw [h_step, hmk_Ysq]
            -- Step B: simplify mk((C(C α))²) = mk(C(C α²)) = mk(C(C δ)).
            have h_Cα_sq : (C (C α) : F[X][Y]) ^ 2 = C (C (α ^ 2)) := by
              rw [← map_pow, ← map_pow]
            rw [h_Cα_sq, show (α ^ 2) = δ from hα]
            -- Step C: combine mk(C(X³+a₂X²+a₄X+a₆)) + mk(C(C δ))
            --                = mk(C(X³+a₂X²+a₄X+a₆ + C δ))
            --                = mk(C((X-x₀)·w₃)) (using h_cubic_factor + char 2)
            --                ∈ (mk(C c)).
            -- Combined goal: -mk(C c)·mk(Y) + mk(C(X³+...+a₆)) + mk(C(C δ)) ∈ P.
            -- Show this = mk(C c) · (something).
            -- (X³+a₂X²+a₄X+a₆) + C δ = (X-x₀)·w₃ + 2·C δ in F[X], using h_cubic_factor.
            -- In char 2, 2·C δ = 0.
            have h_inner : (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) + C δ =
                (X - C x₀) * w₃ := by
              have h_2_Cδ : (2 : F[X]) * C δ = 0 := by rw [h_two_FX, zero_mul]
              have h_2_Cδ_alt : C δ + C δ = 0 := by
                have : (2 : F[X]) * C δ = C δ + C δ := by ring
                rw [← this, h_2_Cδ]
              calc (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) + C δ
                  = (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆ - C δ) + (C δ + C δ) := by
                    ring
                _ = (X - C x₀) * w₃ + 0 := by rw [h_cubic_factor, h_2_Cδ_alt]
                _ = (X - C x₀) * w₃ := by ring
            -- Now (X - C x₀) = C E.a₁⁻¹ · c.
            have h_X_sub_x0_via_c : (X - C x₀ : F[X]) = C E.a₁⁻¹ * c := by
              rw [hc_eq_a1_Xsub, ← mul_assoc, ← map_mul,
                mul_comm E.a₁⁻¹ E.a₁, mul_inv_cancel₀ h_a1, map_one, one_mul]
            -- Combined: mk(C(X³+a₂X²+a₄X+a₆)) + mk(C(C δ))
            --   = mk(C((X³+a₂X²+a₄X+a₆) + C δ)) = mk(C((X - C x₀)·w₃))
            --   = mk(C(C E.a₁⁻¹·c·w₃)) = (algebraMap F R)(E.a₁⁻¹) · mk(C c) · mk(C w₃).
            have h_combine :
                AdjoinRoot.mk E.polynomial
                  (C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) +
                AdjoinRoot.mk E.polynomial (C (C δ)) =
                AdjoinRoot.mk E.polynomial (C c) *
                  (AdjoinRoot.mk E.polynomial (C (C E.a₁⁻¹)) *
                   AdjoinRoot.mk E.polynomial (C w₃)) := by
              rw [← map_add, ← map_add, h_inner, h_X_sub_x0_via_c]
              rw [show C (C E.a₁⁻¹ * c * w₃) = C c * (C (C E.a₁⁻¹) * C w₃) from by
                rw [map_mul, map_mul]; ring]
              rw [map_mul, map_mul]
            have h_final :
                -(AdjoinRoot.mk E.polynomial (C c) *
                  AdjoinRoot.mk E.polynomial Y) +
                AdjoinRoot.mk E.polynomial
                  (C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) +
                AdjoinRoot.mk E.polynomial (C (C δ)) =
                AdjoinRoot.mk E.polynomial (C c) *
                  (-AdjoinRoot.mk E.polynomial Y +
                   AdjoinRoot.mk E.polynomial (C (C E.a₁⁻¹)) *
                    AdjoinRoot.mk E.polynomial (C w₃)) := by
              rw [add_assoc, h_combine]; ring
            rw [h_final]
            exact Ideal.mul_mem_right _ _ hc_in_p
          -- P prime ⟹ mk(Y - C(C α)) ∈ P from (mk(Y - C(C α)))² ∈ P.
          have h_YminusAlpha_in_P :
              AdjoinRoot.mk E.polynomial (Y - C (C α)) ∈ P := by
            have h_sq : (AdjoinRoot.mk E.polynomial (Y - C (C α))) *
                (AdjoinRoot.mk E.polynomial (Y - C (C α))) ∈ P := by
              rw [← sq]; exact h_YminusAlpha_sq_in_P
            exact (hPmax.isPrime.mem_or_mem h_sq).elim id id
          -- pointIdeal E x₀ α ⊆ P.
          have h_pointIdeal_le : pointIdeal E x₀ α ≤ P := by
            unfold pointIdeal Affine.CoordinateRing.XYIdeal
            rw [Ideal.span_le]
            intro z hz
            rcases Set.mem_insert_iff.mp hz with hz | hz
            · -- z = XClass E x₀ = mk(C(X - C x₀)).
              rw [hz]
              change AdjoinRoot.mk E.polynomial (C (X - C x₀)) ∈ P
              exact hmk_X_sub_x0
            · -- z ∈ {YClass E (C α)} = {mk(Y - C(C α))}.
              rw [Set.mem_singleton_iff] at hz
              rw [hz]
              change AdjoinRoot.mk E.polynomial (Y - C (C α)) ∈ P
              exact h_YminusAlpha_in_P
          -- pointIdeal is maximal.
          have h_pointIdeal_max : (pointIdeal E x₀ α).IsMaximal :=
            pointIdeal_isMaximal E h_ns
          -- Both maximal, one contained ⟹ equal.
          have h_P_eq : P = pointIdeal E x₀ α :=
            (Ideal.IsMaximal.eq_of_le h_pointIdeal_max hPmax.ne_top h_pointIdeal_le).symm
          -- Apply localRing_isDVR via subst.
          subst h_P_eq
          haveI : IsDiscreteValuationRing
              (Localization.AtPrime (pointIdeal E x₀ α)) :=
            HasseWeil.localRing_isDVR E h_ns
          rw [Localization.AtPrime.map_eq_maximalIdeal]
          exact IsDiscreteValuationRing.toIsPrincipalIdealRing.principal _
        · -- NON-SQUARE case: δ not a square in F. P = (mk(C c)) principal in R.
          push Not at h_sq
          have h_gc_in_P : AdjoinRoot.mk E.polynomial (C c) ∈ P := hc_in_p
          -- K = R/P is a field. Set up the bar map.
          haveI hKfield : Field (E.CoordinateRing ⧸ P) := Ideal.Quotient.field P
          set bar : E.CoordinateRing →+* E.CoordinateRing ⧸ P :=
            Ideal.Quotient.mk P with hbar_def
          set Ybar : E.CoordinateRing ⧸ P :=
            bar (AdjoinRoot.mk E.polynomial Y) with hYbar_def
          -- bar(mk(C(X - x₀))) = 0 (since (X - x₀) ∈ p ⊆ P comap, so g(X - x₀) ∈ P).
          have h_bar_X_sub_x0 :
              bar (AdjoinRoot.mk E.polynomial (C (X - C x₀))) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr hmk_X_sub_x0
          -- (X - x₀) divides any q with q.eval x₀ = 0 (general polynomial fact).
          -- Key fact: c = a₁(X - x₀) with a₁ unit, so c | q iff (X - x₀) | q.
          have h_c_dvd : ∀ (q : F[X]), q.eval x₀ = 0 → c ∣ q := by
            intro q hq
            have h_X_sub_x0_dvd : (X - C x₀) ∣ q := dvd_iff_isRoot.mpr hq
            obtain ⟨q', hq_eq⟩ := h_X_sub_x0_dvd
            refine ⟨C E.a₁⁻¹ * q', ?_⟩
            rw [hc_eq_a1_Xsub]
            rw [show C E.a₁ * (X - C x₀) * (C E.a₁⁻¹ * q') =
                C E.a₁ * C E.a₁⁻¹ * ((X - C x₀) * q') from by ring]
            rw [← map_mul, mul_inv_cancel₀ h_a1, map_one, one_mul, ← hq_eq]
          -- Helper: bar(g(C q)) — for q ∈ F[X], this is the image of q under
          -- F[X] → R → R/P = K. Modulo P, X maps to x₀, so bar(g(q)) = ι(q.eval x₀).
          -- We use a direct algebra approach: bar ∘ g : F[X] → K is a ring hom, and
          -- under it X ↦ (image of mk(C X)), which equals bar(g(X)). And bar(g(X) - g(C x₀))
          -- = bar(g(X - C x₀)) = 0, so bar(g(X)) = bar(g(C x₀)).
          --
          -- For q ∈ F[X], bar(g(q)) under this hom equals q(bar(g(X))) = q(bar(g(C x₀)))
          --   = (q.eval x₀ applied through the F → R → K composition).
          --
          -- f_quad := X² + C δ : Polynomial F. Setup for AdjoinRoot f_quad iso.
          set f_quad : Polynomial F := (Polynomial.X : Polynomial F) ^ 2 + Polynomial.C δ
            with hf_quad_def
          have hf_quad_natDeg : f_quad.natDegree = 2 := by
            rw [hf_quad_def]; exact Polynomial.natDegree_X_pow_add_C
          have hf_quad_no_root : ∀ x : F, ¬ Polynomial.IsRoot f_quad x := by
            intro x hroot
            unfold Polynomial.IsRoot at hroot
            rw [hf_quad_def] at hroot
            rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
              Polynomial.eval_C] at hroot
            -- hroot : x^2 + δ = 0. In char 2, +δ = -δ, so x^2 = δ. Contradicts h_sq.
            have h_x_sq : x ^ 2 = δ := by
              have h_2δ : δ + δ = 0 := by
                have : (2 : F) * δ = δ + δ := by ring
                rw [← this, h2, zero_mul]
              linear_combination hroot - h_2δ
            exact h_sq x h_x_sq
          have hf_quad_irreducible : Irreducible f_quad := by
            apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
              (p := f_quad) (by rw [hf_quad_natDeg]; decide) hf_quad_no_root
          -- Build proj : R → AdjoinRoot f_quad via AdjoinRoot.lift (before adding Field
          -- instance to avoid typeclass diamond).
          set y_target : AdjoinRoot f_quad := AdjoinRoot.root f_quad with hy_target_def
          set i_hom : F[X] →+* AdjoinRoot f_quad :=
            (AdjoinRoot.of f_quad).comp (Polynomial.evalRingHom x₀) with hi_hom_def
          -- i_hom (C a₁ * X + C a₃) = AdjoinRoot.of f_quad (a₁·x₀ + a₃) = 0.
          have h_i_c_eval : i_hom (C E.a₁ * X + C E.a₃) = 0 := by
            rw [hi_hom_def, RingHom.comp_apply]
            -- (Polynomial.evalRingHom x₀) (C a₁ * X + C a₃) = a₁ * x₀ + a₃ = 0.
            have : (Polynomial.evalRingHom x₀) (C E.a₁ * X + C E.a₃) = 0 := by
              simp [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_X, Polynomial.eval_C, h_a1x0_a3]
            rw [this, map_zero]
          -- y_target² = -(AdjoinRoot.of f_quad) δ via eval₂_root.
          have h_y_target_sq :
              y_target ^ 2 = -((AdjoinRoot.of f_quad) δ) := by
            have h_eval2 := AdjoinRoot.eval₂_root f_quad
            -- h_eval2 : f_quad.eval₂ (AdjoinRoot.of f_quad) (AdjoinRoot.root f_quad) = 0.
            rw [hf_quad_def] at h_eval2
            rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
              Polynomial.eval₂_C] at h_eval2
            -- h_eval2 : y_target² + (of f_quad) δ = 0.
            -- Hence y_target² = -(of f_quad) δ.
            linear_combination h_eval2
          -- i_hom (X³+a₂X²+a₄X+a₆) = (AdjoinRoot.of f_quad) δ.
          have h_i_cubic_eval :
              i_hom (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) =
              (AdjoinRoot.of f_quad) δ := by
            rw [hi_hom_def, RingHom.comp_apply]
            have h_eval : (Polynomial.evalRingHom x₀)
                (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) = δ := by
              rw [hδ_def]
              simp [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
            rw [h_eval]
          -- E.polynomial.eval₂ i_hom y_target = 0.
          have h_eval_zero : E.polynomial.eval₂ i_hom y_target = 0 := by
            unfold Affine.polynomial
            rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
              Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_C]
            rw [h_i_c_eval, zero_mul, add_zero, h_i_cubic_eval, h_y_target_sq]
            have h_2δ_zero : (AdjoinRoot.of f_quad : F →+* AdjoinRoot f_quad) δ +
                (AdjoinRoot.of f_quad) δ = 0 := by
              rw [← map_add]
              have h_delta_sum : δ + δ = 0 := by
                have h_2δ : (2 : F) * δ = δ + δ := by ring
                rw [← h_2δ, h2, zero_mul]
              rw [h_delta_sum, map_zero]
            linear_combination -h_2δ_zero
          -- proj : R → AdjoinRoot f_quad.
          set proj : E.CoordinateRing →+* AdjoinRoot f_quad :=
            AdjoinRoot.lift i_hom y_target h_eval_zero with hproj_def
          -- proj(mk(C c)) = i_hom c = 0.
          have h_proj_gc : proj (AdjoinRoot.mk E.polynomial (C c)) = 0 := by
            rw [hproj_def]
            -- mk(C c) ∈ R. AdjoinRoot.lift_of: proj ((of E.polynomial) c) = i_hom c.
            -- (of E.polynomial) c = AdjoinRoot.mk E.polynomial (C c).
            change AdjoinRoot.lift i_hom y_target h_eval_zero
              ((AdjoinRoot.of E.polynomial) c) = 0
            rw [AdjoinRoot.lift_of]
            rw [hc_def]; exact h_i_c_eval
          -- Show ker proj = Ideal.span {mk(C c)} via linear independence in AdjoinRoot f_quad.
          have h_proj_mkY : proj (AdjoinRoot.mk E.polynomial Y) = y_target := by
            rw [hproj_def, show (AdjoinRoot.mk E.polynomial Y : E.CoordinateRing) =
                AdjoinRoot.root E.polynomial from rfl]
            exact AdjoinRoot.lift_root _
          -- Helper: proj(mk(C a)) = (of f_quad)(a.eval x₀) for any a ∈ F[X].
          have h_proj_C : ∀ (a : F[X]),
              proj (AdjoinRoot.mk E.polynomial (C a)) =
              (AdjoinRoot.of f_quad) (a.eval x₀) := by
            intro a
            rw [show AdjoinRoot.mk E.polynomial (C a) = AdjoinRoot.of E.polynomial a from rfl,
              hproj_def, AdjoinRoot.lift_of, hi_hom_def, RingHom.comp_apply,
              Polynomial.coe_evalRingHom]
          have h_proj_decomp : ∀ (a b : F[X]),
              proj (AdjoinRoot.mk E.polynomial (C a + C b * Y)) =
              (AdjoinRoot.of f_quad) (a.eval x₀) +
              (AdjoinRoot.of f_quad) (b.eval x₀) * y_target := by
            intro a b
            rw [show AdjoinRoot.mk E.polynomial (C a + C b * Y) =
                AdjoinRoot.mk E.polynomial (C a) +
                AdjoinRoot.mk E.polynomial (C b) * AdjoinRoot.mk E.polynomial Y from by
              rw [map_add, map_mul]]
            rw [map_add proj, map_mul proj, h_proj_C a, h_proj_C b, h_proj_mkY]
          -- f_quad is monic (needed for not_dvd_of_natDegree_lt).
          have hf_quad_monic : f_quad.Monic := by
            rw [hf_quad_def]
            exact Polynomial.monic_X_pow_add_C δ (by decide : (2 : ℕ) ≠ 0)
          have h_indep : ∀ lam mu : F,
              (AdjoinRoot.of f_quad) lam +
              (AdjoinRoot.of f_quad) mu * y_target = 0 →
              lam = 0 ∧ mu = 0 := by
            intro lam mu hrel
            set q : F[X] := Polynomial.C lam + Polynomial.C mu * Polynomial.X with hq_def
            have h_form : (AdjoinRoot.of f_quad) lam +
                (AdjoinRoot.of f_quad) mu * y_target = AdjoinRoot.mk f_quad q := by
              rw [hq_def, show (AdjoinRoot.of f_quad) lam =
                  AdjoinRoot.mk f_quad (Polynomial.C lam) from rfl,
                show (AdjoinRoot.of f_quad) mu =
                  AdjoinRoot.mk f_quad (Polynomial.C mu) from rfl,
                hy_target_def,
                show (AdjoinRoot.root f_quad : AdjoinRoot f_quad) =
                  AdjoinRoot.mk f_quad Polynomial.X from rfl,
                ← map_mul, ← map_add]
            rw [h_form, AdjoinRoot.mk_eq_zero] at hrel
            by_cases h_p_zero : q = 0
            · refine ⟨?_, ?_⟩
              · have h0 : q.coeff 0 = lam := by
                  simp [hq_def, Polynomial.coeff_add, Polynomial.coeff_C]
                rw [h_p_zero, Polynomial.coeff_zero] at h0
                exact h0.symm
              · have h1 : q.coeff 1 = mu := by
                  simp [hq_def, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul_X]
                rw [h_p_zero, Polynomial.coeff_zero] at h1
                exact h1.symm
            · exfalso
              have h_natDeg_le : q.natDegree ≤ 1 := by
                rw [hq_def]
                refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
                · rw [Polynomial.natDegree_C]; omega
                · calc (Polynomial.C mu * Polynomial.X : F[X]).natDegree
                      ≤ (Polynomial.C mu : F[X]).natDegree + Polynomial.X.natDegree :=
                        Polynomial.natDegree_mul_le
                    _ = 0 + 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
                    _ = 1 := by omega
              have h_lt : q.natDegree < f_quad.natDegree := by rw [hf_quad_natDeg]; omega
              exact Polynomial.Monic.not_dvd_of_natDegree_lt hf_quad_monic h_p_zero h_lt hrel
          -- Show ker proj = Ideal.span {mk(C c)}.
          have h_ker_proj_eq :
              RingHom.ker proj = Ideal.span ({AdjoinRoot.mk E.polynomial (C c)} :
                Set E.CoordinateRing) := by
            apply le_antisymm
            · -- Hard direction: ker proj ⊆ span{mk(C c)}.
              intro z hz_in_ker
              rw [RingHom.mem_ker] at hz_in_ker
              obtain ⟨a, b, hz_decomp⟩ := Affine.CoordinateRing.exists_smul_basis_eq z
              have hz_eq : z = AdjoinRoot.mk E.polynomial (C a + C b * Y) := by
                rw [← hz_decomp]
                rw [show a • (1 : E.CoordinateRing) =
                    AdjoinRoot.mk E.polynomial (C a) from by
                  rw [Affine.CoordinateRing.smul]; simp]
                rw [show b • (AdjoinRoot.mk E.polynomial Y : E.CoordinateRing) =
                    AdjoinRoot.mk E.polynomial (C b) * AdjoinRoot.mk E.polynomial Y from by
                  rw [Affine.CoordinateRing.smul]]
                rw [map_add, map_mul]
              rw [hz_eq] at hz_in_ker
              rw [h_proj_decomp] at hz_in_ker
              -- (of f_quad)(a(x₀)) + (of f_quad)(b(x₀)) * y_target = 0.
              -- By h_indep, a(x₀) = 0 and b(x₀) = 0.
              obtain ⟨h_ax0, h_bx0⟩ := h_indep _ _ hz_in_ker
              -- (X - x₀) | a and (X - x₀) | b in F[X], hence c | a, c | b.
              have h_c_dvd_q : ∀ (q : F[X]), q.eval x₀ = 0 → c ∣ q := by
                intro q hq
                have h_X_sub_x0_dvd : (X - C x₀) ∣ q := dvd_iff_isRoot.mpr hq
                obtain ⟨q', hq_eq⟩ := h_X_sub_x0_dvd
                refine ⟨C E.a₁⁻¹ * q', ?_⟩
                rw [hc_eq_a1_Xsub]
                rw [show C E.a₁ * (X - C x₀) * (C E.a₁⁻¹ * q') =
                    C E.a₁ * C E.a₁⁻¹ * ((X - C x₀) * q') from by ring]
                rw [← map_mul, mul_inv_cancel₀ h_a1, map_one, one_mul, ← hq_eq]
              obtain ⟨a'', ha''_eq⟩ := h_c_dvd_q a h_ax0
              obtain ⟨b'', hb''_eq⟩ := h_c_dvd_q b h_bx0
              -- z = mk(C c) · mk(C a'' + C b'' · Y) ∈ span{mk(C c)}.
              rw [hz_eq, ha''_eq, hb''_eq]
              rw [show C (c * a'') = C c * C a'' from map_mul _ _ _]
              rw [show C (c * b'') = C c * C b'' from map_mul _ _ _]
              rw [show C c * C a'' + C c * C b'' * Y =
                  C c * (C a'' + C b'' * Y) from by ring]
              rw [map_mul]
              exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
            · rw [Ideal.span_le, Set.singleton_subset_iff]
              change AdjoinRoot.mk E.polynomial (C c) ∈ RingHom.ker proj
              rw [RingHom.mem_ker]
              exact h_proj_gc
          -- proj is surjective via Polynomial.induction_on' (BEFORE Field instance,
          -- to avoid CommRing/Field semiring diamond).
          have h_proj_surj : Function.Surjective proj := by
            intro w
            obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective w
            induction p using Polynomial.induction_on' with
            | add q r hq hr =>
              obtain ⟨zq, hzq⟩ := hq
              obtain ⟨zr, hzr⟩ := hr
              refine ⟨zq + zr, ?_⟩
              rw [map_add, hzq, hzr, ← map_add]
            | monomial n a =>
              refine ⟨AdjoinRoot.mk E.polynomial (C (C a)) *
                  AdjoinRoot.mk E.polynomial Y ^ n, ?_⟩
              rw [map_mul, map_pow]
              rw [h_proj_C (C a), h_proj_mkY]
              simp only [Polynomial.eval_C]
              -- (of f_quad) a * y_target^n = mk f_quad (C a * X^n) = mk f_quad (monomial n a).
              rw [show AdjoinRoot.mk f_quad (Polynomial.monomial n a) =
                  AdjoinRoot.mk f_quad (Polynomial.C a * Polynomial.X ^ n) from by
                rw [Polynomial.C_mul_X_pow_eq_monomial]]
              rw [map_mul, map_pow]
              rfl
          -- Final piece: ker proj is maximal. Use IsField-Quotient route to dodge diamond:
          -- (1) span {f_quad} maximal in F[X] (via AdjoinRoot.span_maximal_of_irreducible).
          -- (2) Quotient by maximal ideal is a field (via maximal_ideal_iff_isField_quotient).
          -- (3) IsField transfers via the iso R/(ker proj) ≃+* AdjoinRoot f_quad.
          -- (4) Maximal-from-IsField via Ideal.Quotient.maximal_of_isField.
          haveI hFact : Fact (Irreducible f_quad) := ⟨hf_quad_irreducible⟩
          have h_span_max : (Ideal.span ({f_quad} : Set (Polynomial F))).IsMaximal :=
            AdjoinRoot.span_maximal_of_irreducible
          have h_AdjoinRoot_isField :
              IsField (Polynomial F ⧸ Ideal.span ({f_quad} : Set (Polynomial F))) :=
            (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp h_span_max
          have h_R_quot_isField :
              IsField (E.CoordinateRing ⧸ RingHom.ker proj) := by
            have h_iso : (E.CoordinateRing ⧸ RingHom.ker proj) ≃+* AdjoinRoot f_quad :=
              RingHom.quotientKerEquivOfSurjective h_proj_surj
            -- AdjoinRoot f_quad ≡ Polynomial F ⧸ Ideal.span {f_quad} definitionally,
            -- so h_AdjoinRoot_isField gives IsField (AdjoinRoot f_quad).
            exact MulEquiv.isField h_AdjoinRoot_isField h_iso.toMulEquiv
          have h_ker_max : (RingHom.ker proj).IsMaximal :=
            Ideal.Quotient.maximal_of_isField _ h_R_quot_isField
          have h_gc_max : (Ideal.span ({AdjoinRoot.mk E.polynomial (C c)} :
              Set E.CoordinateRing)).IsMaximal := by
            rw [← h_ker_proj_eq]; exact h_ker_max
          -- P = Ideal.span {mk(C c)}: both maximal, with mk(C c) ∈ P ⟹ span ⊆ P ⟹ =.
          have h_P_eq : P = Ideal.span ({AdjoinRoot.mk E.polynomial (C c)} :
              Set E.CoordinateRing) := by
            symm
            apply Ideal.IsMaximal.eq_of_le h_gc_max hPmax.ne_top
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact hc_in_p
          -- P principal in R, hence P.map f principal.
          subst h_P_eq
          rw [Ideal.map_span, Set.image_singleton]
          exact ⟨⟨_, rfl⟩⟩
    · -- Char ≠ 2 case.
      have h2 : (2 : F) ≠ 0 := fun h2zero ↦ h4 (by
        have : (4 : F) = 2 * 2 := by norm_num
        rw [this, h2zero]; ring)
      -- `d' ∉ p` from the Jacobian identity.
      have hd'_not_in_p := dprime_not_in_p E P hY hX h4
      -- Extract `d ∈ p`. Using `polynomialY_sq_eq_disc`, `mk(polynomialY)² = mk(C d)`.
      set d : F[X] := (C E.a₁ * X + C E.a₃) ^ 2 +
        C 4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) with hd_def
      have hmkCd_in_P : AdjoinRoot.mk E.polynomial (C d) ∈ P := by
        have h : (AdjoinRoot.mk E.polynomial E.polynomialY) ^ 2 =
            AdjoinRoot.mk E.polynomial (C d) := mk_polynomialY_sq E
        rw [← h]
        exact Ideal.pow_mem_of_mem P hY 2 (by norm_num)
      have hd_in_p : d ∈ p := hmkCd_in_P
      -- Get generator π of p.
      obtain ⟨π, hπ_gen⟩ : ∃ π : F[X], p = Ideal.span {π} :=
        ⟨Submodule.IsPrincipal.generator p, (Ideal.span_singleton_generator p).symm⟩
      have hπ_in_p : π ∈ p := by rw [hπ_gen]; exact Ideal.subset_span rfl
      -- d ∈ p = (π), so π | d.
      have hπ_dvd_d : π ∣ d := by
        have := hd_in_p
        rw [hπ_gen] at this
        exact Ideal.mem_span_singleton.mp this
      obtain ⟨d₀, hd_factored⟩ := hπ_dvd_d
      -- Show `d₀ ∉ p` via the multiplicity/derivative argument.
      have hd₀_not_in_p : d₀ ∉ p := by
        intro hd₀_mem
        rw [hπ_gen] at hd₀_mem
        obtain ⟨d₀', hd₀_eq⟩ := Ideal.mem_span_singleton.mp hd₀_mem
        have hd_full : d = π * π * d₀' := by rw [hd_factored, hd₀_eq]; ring
        have hd'_expr : Polynomial.derivative d =
            2 * π * (Polynomial.derivative π) * d₀' + π * π * (Polynomial.derivative d₀') := by
          rw [hd_full]
          simp only [Polynomial.derivative_mul]
          ring
        have hπ_dvd_d' : π ∣ Polynomial.derivative d := by
          rw [hd'_expr]
          exact dvd_add
            ⟨2 * (Polynomial.derivative π) * d₀', by ring⟩
            ⟨π * (Polynomial.derivative d₀'), by ring⟩
        have hd'_simp : Polynomial.derivative d =
            C 2 * C E.a₁ * (C E.a₁ * X + C E.a₃) +
              C 4 * (C 3 * X ^ 2 + C (2 * E.a₂) * X + C E.a₄) := by
          rw [hd_def]
          simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
            Polynomial.derivative_pow, Polynomial.derivative_C,
            Polynomial.derivative_X]
          simp only [zero_mul, zero_add, add_zero, mul_one, one_mul, pow_succ, pow_zero]
          push_cast
          rw [show C (2 * E.a₂) = C 2 * C E.a₂ from by rw [map_mul]]
          ring
        apply hd'_not_in_p
        change _ ∈ p
        rw [hπ_gen, Ideal.mem_span_singleton]
        rw [← hd'_simp]; exact hπ_dvd_d'
      have hmkCd₀_not_in_P : AdjoinRoot.mk E.polynomial (C d₀) ∉ P := hd₀_not_in_p
      -- f(mk(C π)) ∈ span{f(mk(polynomialY))} in R_P.
      have hu : IsUnit (f (AdjoinRoot.mk E.polynomial (C d₀))) :=
        IsLocalization.map_units (Localization.AtPrime P)
          (⟨AdjoinRoot.mk E.polynomial (C d₀), hmkCd₀_not_in_P⟩ : P.primeCompl)
      have hsq_identity : AdjoinRoot.mk E.polynomial E.polynomialY *
          AdjoinRoot.mk E.polynomial E.polynomialY =
          AdjoinRoot.mk E.polynomial (C π) * AdjoinRoot.mk E.polynomial (C d₀) := by
        have h : (AdjoinRoot.mk E.polynomial E.polynomialY) ^ 2 =
            AdjoinRoot.mk E.polynomial (C d) := mk_polynomialY_sq E
        rw [sq] at h
        rw [h]
        -- Rewrite mk(C d) = mk(C (π * d₀)) = mk(C π * C d₀) = mk(C π) * mk(C d₀).
        have : C d = C π * C d₀ := by rw [hd_factored, map_mul]
        rw [this, map_mul]
      have hmkCπ_in_span : f (AdjoinRoot.mk E.polynomial (C π)) ∈
          Ideal.span {f (AdjoinRoot.mk E.polynomial E.polynomialY)} := by
        -- f(polyY)² = f(C π) * f(C d₀), and f(C d₀) is a unit, so f(C π) ∈ span{f polyY}.
        have hfsq : f (AdjoinRoot.mk E.polynomial E.polynomialY) *
            f (AdjoinRoot.mk E.polynomial E.polynomialY) =
            f (AdjoinRoot.mk E.polynomial (C π)) * f (AdjoinRoot.mk E.polynomial (C d₀)) := by
          have := congr_arg f hsq_identity
          rw [map_mul, map_mul] at this
          exact this
        obtain ⟨u, hu_eq⟩ := hu
        rw [Ideal.mem_span_singleton]
        -- f(C π) = (f(polyY))² * (f(C d₀))⁻¹
        refine ⟨f (AdjoinRoot.mk E.polynomial E.polynomialY) *
            ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P), ?_⟩
        calc f (AdjoinRoot.mk E.polynomial (C π))
            = f (AdjoinRoot.mk E.polynomial (C π)) *
              ((u : Localization.AtPrime P) *
                ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P)) := by
              rw [Units.mul_inv u]; ring
          _ = (f (AdjoinRoot.mk E.polynomial (C π)) *
              f (AdjoinRoot.mk E.polynomial (C d₀))) *
              ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P) := by
              rw [hu_eq]; ring
          _ = (f (AdjoinRoot.mk E.polynomial E.polynomialY) *
               f (AdjoinRoot.mk E.polynomial E.polynomialY)) *
              ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P) := by rw [← hfsq]
          _ = f (AdjoinRoot.mk E.polynomial E.polynomialY) *
              (f (AdjoinRoot.mk E.polynomial E.polynomialY) *
               ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P)) := by ring
      -- P ⊆ span{mk(C π), mk(polynomialY)}.
      have hP_le_span : P ≤ Ideal.span
          ({AdjoinRoot.mk E.polynomial (C π),
            AdjoinRoot.mk E.polynomial E.polynomialY} : Set E.CoordinateRing) := by
        intro x hx_mem
        obtain ⟨a', b', hxdecomp⟩ := exists_coeffs_via_polynomialY E h2 x
        have hb'polyY_in_P : AdjoinRoot.mk E.polynomial (C b') *
            AdjoinRoot.mk E.polynomial E.polynomialY ∈ P :=
          Ideal.mul_mem_left _ _ hY
        have hmkCa'_in_P : AdjoinRoot.mk E.polynomial (C a') ∈ P := by
          have := sub_mem hx_mem hb'polyY_in_P
          simpa [hxdecomp] using this
        have ha'_in_p : a' ∈ p := hmkCa'_in_P
        rw [hπ_gen] at ha'_in_p
        obtain ⟨a'', ha''_eq⟩ := Ideal.mem_span_singleton.mp ha'_in_p
        have hmkCa'_eq : AdjoinRoot.mk E.polynomial (C a') =
            AdjoinRoot.mk E.polynomial (C π) * AdjoinRoot.mk E.polynomial (C a'') := by
          rw [ha''_eq]
          rw [show (C (π * a'') : F[X][Y]) = C π * C a'' from map_mul _ _ _]
          rw [map_mul]
        rw [hxdecomp, hmkCa'_eq]
        refine Ideal.add_mem _ ?_ ?_
        · exact Ideal.mul_mem_right _ _
            (Ideal.subset_span (Set.mem_insert _ _))
        · exact Ideal.mul_mem_left _ _
            (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      -- P.map f = span{f(mk(polynomialY))}.
      have hPmapf : Ideal.map f P = Ideal.span
          ({f (AdjoinRoot.mk E.polynomial E.polynomialY)} : Set (Localization.AtPrime P)) := by
        apply le_antisymm
        · rw [Ideal.map_le_iff_le_comap]
          intro x hx_mem
          have hx_in_span_R := hP_le_span hx_mem
          rw [Ideal.mem_comap]
          rw [Ideal.mem_span_pair] at hx_in_span_R
          obtain ⟨c₁, c₂, hxeq⟩ := hx_in_span_R
          rw [← hxeq, map_add, map_mul, map_mul]
          exact Ideal.add_mem _
            (Ideal.mul_mem_left _ _ hmkCπ_in_span)
            (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
        · rw [Ideal.span_le]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Ideal.mem_map_of_mem f hY
      rw [hPmapf]
      exact ⟨⟨_, rfl⟩⟩

/-- The coordinate ring of an elliptic curve is integrally closed in its fraction field. -/
instance coordinateRing_isIntegrallyClosed (E : Affine F) [E.IsElliptic] :
    IsIntegrallyClosed E.CoordinateRing := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P hP0 hPmax
  haveI := IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) inferInstance
  haveI : Ring.DimensionLEOne (Localization.AtPrime P) :=
    Ring.DimensionLEOne.localization (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  haveI : IsPrincipalIdealRing (Localization.AtPrime P) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime P)).out 4 0).mp
      (maximalIdeal_isPrincipal_of_nonsingular E P hP0 hPmax)
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

-- Typeclass synthesis over the tower F[X] → CoordinateRing → FunctionField needs more budget.
noncomputable instance coordinateRing_isIntegralClosure (E : Affine F) [E.IsElliptic] :
    IsIntegralClosure E.CoordinateRing (Polynomial F) E.FunctionField where
  algebraMap_injective _ _ h :=
    IsFractionRing.injective E.CoordinateRing E.FunctionField h
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact (isIntegrallyClosed_iff E.FunctionField).mp
        (coordinateRing_isIntegrallyClosed E) hx.tower_top
    · rintro ⟨y, rfl⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom (Polynomial F) E.CoordinateRing E.FunctionField)
        (IsIntegral.of_finite (Polynomial F) y)

open Classical in
private theorem polynomialY_ne_zero (E : Affine F) [E.IsElliptic] : E.polynomialY ≠ 0 := by
  intro h
  rw [Affine.polynomialY] at h
  have h2 : (2 : F) = 0 := by
    have := congr_arg (fun p ↦ (p.coeff 1).coeff 0) h; simpa using this
  have ha1 : E.a₁ = 0 := by
    have := congr_arg (fun p ↦ (p.coeff 0).coeff 1) h; simpa using this
  have ha3 : E.a₃ = 0 := by
    have := congr_arg (fun p ↦ (p.coeff 0).coeff 0) h; simpa using this
  have h4 : (4 : F) = 0 := by linear_combination 2 * h2
  have hΔ : WeierstrassCurve.Δ E = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, ha1, ha3]
    linear_combination
      (72 * E.a₂ * E.a₆ * E.a₄ + 4 * E.a₂ ^ 2 * E.a₄ ^ 2 - 16 * E.a₂ ^ 3 * E.a₆
        - 108 * E.a₆ ^ 2 - 16 * E.a₄ ^ 3) * h4
  exact absurd (hΔ ▸ E.isUnit_Δ) not_isUnit_zero

-- The image of AdjoinRoot.root in the function field is a root of W.map(algebraMap).
-- Polynomial.aeval_map_algebraMap rewriting needs extra heartbeats.
private theorem root_aeval_polynomial_map (E : Affine F) [E.IsElliptic] :
    Polynomial.aeval (algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial))
      (E.polynomial.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))) = 0 := by
  rw [Polynomial.aeval_map_algebraMap]
  exact AdjoinRoot.aeval_algHom_eq_zero E.polynomial
    { algebraMap E.CoordinateRing E.FunctionField with
      commutes' := fun r ↦ by
        simp [IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField] }

-- The separability proof reasons over two cases via finSepDegree; typeclass
-- synthesis for the tower through FractionRing F[X] needs more budget.
noncomputable instance functionField_isSeparable (E : Affine F) [E.IsElliptic] :
    Algebra.IsSeparable (FractionRing (Polynomial F)) E.FunctionField := by
  set K := FractionRing (Polynomial F)
  -- `finSepDegree K L ∣ finrank K L = 2` and `≠ 1` (as `y` is separable), so it equals `finrank`.
  have h_dvd := Field.finSepDegree_dvd_finrank K E.FunctionField
  haveI : FiniteDimensional K E.FunctionField := functionField_finiteDimensional E
  have h_fr : Module.finrank K E.FunctionField = 2 := by
    haveI : Algebra.IsAlgebraic (Polynomial F) E.CoordinateRing :=
      (Algebra.IsIntegral.of_finite (Polynomial F) E.CoordinateRing).isAlgebraic
    change Module.finrank (FractionRing (Polynomial F)) E.FunctionField = 2
    rw [Algebra.IsAlgebraic.finrank_of_isFractionRing (Polynomial F)
        (FractionRing (Polynomial F)) E.CoordinateRing E.FunctionField,
      Module.finrank_eq_card_basis (Affine.CoordinateRing.basis E), Fintype.card_fin]
  rw [h_fr] at h_dvd
  have h_not_1 : Field.finSepDegree K E.FunctionField ≠ 1 := by
    intro h1
    haveI := isPurelyInseparable_of_finSepDegree_eq_one h1
    set y : E.FunctionField :=
      algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)
    have hy_int : IsIntegral K y := IsIntegral.of_finite _ _
    set W' : K[X] := E.polynomial.map (algebraMap (Polynomial F) K) with hW'_def
    have hW'_irr : Irreducible W' :=
      (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
        Affine.monic_polynomial).mp Affine.irreducible_polynomial
    have h_dvd' : minpoly K y ∣ W' := minpoly.dvd K y (root_aeval_polynomial_map E)
    have h_eq : minpoly K y = W' :=
      Polynomial.eq_of_monic_of_associated (minpoly.monic hy_int) (Affine.monic_polynomial.map _)
        ((minpoly.irreducible hy_int).associated_of_dvd hW'_irr h_dvd')
    have hW'_sep : W'.Separable :=
      (separable_iff_derivative_ne_zero hW'_irr).mpr (by
        rw [hW'_def, Polynomial.derivative_map]
        exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective (Polynomial F) K)).mpr
          (derivative_polynomial_eq_polynomialY E ▸ polynomialY_ne_zero E))
    have h_sep_y : IsSeparable K y := by rw [IsSeparable, h_eq]; exact hW'_sep
    -- Purely inseparable + `y` separable forces `y ∈ K`, contradicting `deg (minpoly K y) = 2`.
    obtain ⟨z, hz⟩ := IsPurelyInseparable.inseparable K y h_sep_y
    have h_deg1 : (minpoly K y).natDegree ≤ 1 := by
      have hdvd : minpoly K y ∣ X - C z := minpoly.dvd K y (by simp [hz])
      have hne : X - C z ≠ (0 : K[X]) := X_sub_C_ne_zero z
      calc (minpoly K y).natDegree ≤ (X - C z).natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
        _ ≤ 1 := natDegree_X_sub_C_le z
    have h_deg2 : (minpoly K y).natDegree = 2 := by
      rw [h_eq, hW'_def, Affine.monic_polynomial.natDegree_map, Affine.natDegree_polynomial]
    omega
  have h_pos : 0 < Field.finSepDegree K E.FunctionField :=
    Nat.pos_of_ne_zero (fun h0 ↦ by simp [h0] at h_dvd)
  have h_eq : Field.finSepDegree K E.FunctionField = 2 := by
    have h_le : Field.finSepDegree K E.FunctionField ≤ 2 :=
      (Field.finSepDegree_le_finrank K E.FunctionField).trans (le_of_eq h_fr)
    omega
  exact (Field.finSepDegree_eq_finrank_iff K E.FunctionField).mp (by rw [h_eq, h_fr])

-- Assembling the Dedekind conclusion from integral closure + separability + Noetherian via
-- `IsIntegralClosure.isDedekindDomain` needs a heavy typeclass search.
/-- The coordinate ring of an elliptic curve is a Dedekind domain. -/
instance coordinateRing_isDedekindDomain (E : Affine F) [E.IsElliptic] :
    IsDedekindDomain E.CoordinateRing :=
  IsIntegralClosure.isDedekindDomain (Polynomial F) (FractionRing (Polynomial F))
    E.FunctionField E.CoordinateRing

/-- The coordinate ring of an elliptic curve is integrally closed (consequence of being
a Dedekind domain). -/
instance isIntegrallyClosed_coordinateRing (E : Affine F) [E.IsElliptic] :
    IsIntegrallyClosed E.CoordinateRing :=
  inferInstance

-- Downstream ramification theory builds on the Dedekind-domain structure above via mathlib's
-- `Ideal.ramificationIdx`, `Ideal.inertiaDeg`, and `Ideal.sum_ramification_inertia`, applied to
-- the coordinate-ring extension `R₂ → R₁` induced by the pullback of an isogeny.

end HasseWeil
