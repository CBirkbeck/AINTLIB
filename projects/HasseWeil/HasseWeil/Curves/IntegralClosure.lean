/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Tower

import HasseWeil.Curves.FiniteOverKx

/-!
# Integral closure infrastructure for smooth plane curves

This file develops the ring-theoretic infrastructure needed to conclude
`IsDedekindDomain C.CoordinateRing` (and hence `IsIntegrallyClosed`) under a
smoothness hypothesis — see `.mathlib-quality/integral-closure-plan.md`.

Current content:

- **T-INFRA-IC-002** `Ring.DimensionLEOne C.CoordinateRing`: every nonzero
  prime of `F[C]` is maximal. Proved via the integral extension `F[X] → F[C]`
  (going-up / going-down).

- **T-INFRA-IC-003i** `Algebra.IsSeparable (FractionRing (Polynomial F)) C.FunctionField`
  under `[NeZero (2 : F)]` (i.e. char ≠ 2). Key ingredient for the mathlib
  `IsIntegralClosure.isDedekindDomain` route.

Future content (see the plan):

- T-INFRA-IC-003ii DVR at every nonzero prime (requires smoothness predicate).
- T-INFRA-IC-004 `IsDedekindDomainDvr C.CoordinateRing` (glue).
- T-INFRA-IC-005 Bridge to `ord_P`-based hypotheses.

## References

- Silverman, *Arithmetic of Elliptic Curves*, II.1 (algebraic curves).
- Hartshorne, *Algebraic Geometry*, I.6.
-/

open scoped Polynomial.Bivariate

/-- **Squarefree extraction**: if `q ∈ FractionRing R` (R a UFD like F[X])
satisfies `q² · algebraMap D = algebraMap r` for some `r : R` and `D`
squarefree, then `q` itself is in the image of `algebraMap R (FractionRing R)`. -/
theorem Polynomial.fractionRing_mem_range_of_sq_mul_squarefree
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {q : K} {D r : R} (hD : Squarefree D)
    (h : q ^ 2 * algebraMap R K D = algebraMap R K r) :
    ∃ q' : R, algebraMap R K q' = q := by
  obtain ⟨s, t, hst_coprime, hmk'_eq⟩ :=
    IsFractionRing.exists_reduced_fraction (A := R) (K := K) q
  have ht_ne : (algebraMap R K t : K) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
  have hstD : s * s * D = t * t * r := by
    refine FaithfulSMul.algebraMap_injective R K ?_
    rw [← hmk'_eq, IsFractionRing.mk'_eq_div] at h
    field_simp at h
    push_cast
    linear_combination h
  have ht_unit : IsUnit (t : R) := by
    have h_rel_sym : IsRelPrime (t : R) s := hst_coprime.symm
    exact (h_rel_sym.mul_right h_rel_sym) dvd_rfl
      (hD.dvd_of_squarefree_of_mul_dvd_mul_left ⟨r, hstD⟩)
  obtain ⟨u, hu⟩ := ht_unit
  refine ⟨s * (u⁻¹ : Rˣ), ?_⟩
  rw [← hmk'_eq, IsFractionRing.mk'_eq_div, map_mul]
  have hinv : algebraMap R K ((u⁻¹ : Rˣ) : R) = (algebraMap R K ((u : Rˣ) : R))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    simp
  rw [show (t : R) = ((u : Rˣ) : R) from hu.symm, hinv, div_eq_mul_inv]

/-- **Helper lemma**: in char ≠ 2, every monic irreducible polynomial of
natDegree ≤ 2 over a field is separable. Covers the cases natDegree = 1 and
natDegree = 2; natDegree = 0 is impossible for irreducibles. -/
theorem Polynomial.separable_of_monic_irreducible_natDegree_le_two
    {K : Type*} [Field K] [NeZero (2 : K)] {p : Polynomial K}
    (hmonic : p.Monic) (hirr : Irreducible p) (hdeg : p.natDegree ≤ 2) :
    p.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hd
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  have hlead : p.coeff p.natDegree = 1 := hmonic
  have hsub : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel hpos
  have hcoeff_deriv : p.derivative.coeff (p.natDegree - 1) =
      (p.natDegree : K) := by
    rw [Polynomial.coeff_derivative, hsub, hlead, one_mul, ← Nat.cast_add_one,
      hsub]
  rw [hd, Polynomial.coeff_zero] at hcoeff_deriv
  interval_cases p.natDegree
  · simp at hcoeff_deriv
  · exact NeZero.ne (2 : K) hcoeff_deriv.symm

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- **T-INFRA-IC-002**: `F[C]` has Krull dimension ≤ 1 — every nonzero prime
ideal is maximal. -/
instance dimensionLEOne_coordinateRing :
    Ring.DimensionLEOne C.CoordinateRing where
  maximalOfPrime := by
    intro 𝔭 hp_ne hp_prime
    have : 𝔭.IsPrime := hp_prime
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Polynomial F)
      (S := C.CoordinateRing) 𝔭 ?_
    have hcomap_ne :
        𝔭.comap (algebraMap (Polynomial F) C.CoordinateRing) ≠ ⊥ := by
      obtain ⟨x, hx_mem, hx_ne⟩ := 𝔭.ne_bot_iff.mp hp_ne
      exact Ideal.comap_ne_bot_of_integral_mem hx_ne hx_mem
        (Algebra.IsIntegral.isIntegral x)
    have : (𝔭.comap (algebraMap (Polynomial F) C.CoordinateRing)).IsPrime :=
      Ideal.comap_isPrime _ _
    exact Ideal.IsPrime.isMaximal inferInstance hcomap_ne

/-- **IC-003i helper**: the image of `Y` (as `AdjoinRoot.root`) in the function
field `F(C)`. This element is a root of `W.polynomial` mapped into `F(X)[T]`. -/
noncomputable def coordYInFunctionField : C.FunctionField :=
  algebraMap C.CoordinateRing C.FunctionField
    (AdjoinRoot.root C.toAffine.polynomial)

/-- `coordYInFunctionField` is a root of the Weierstrass polynomial `W`
(evaluated as a polynomial over `F[X]`). -/
theorem aeval_coordYInFunctionField_polynomial :
    (Polynomial.aeval (R := Polynomial F) C.coordYInFunctionField)
      C.toAffine.polynomial = 0 := by
  have h : (Polynomial.aeval (R := Polynomial F)
      (AdjoinRoot.root C.toAffine.polynomial)) C.toAffine.polynomial = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [show C.coordYInFunctionField =
    (IsScalarTower.toAlgHom (Polynomial F) C.CoordinateRing C.FunctionField)
      (AdjoinRoot.root C.toAffine.polynomial) from rfl,
    Polynomial.aeval_algHom_apply, h, map_zero]

/-- `coordYInFunctionField` is integral over `F[X]` (since `W.polynomial` is
monic of degree 2 and annihilates it). -/
theorem isIntegral_coordYInFunctionField :
    IsIntegral (Polynomial F) C.coordYInFunctionField :=
  ⟨C.toAffine.polynomial, WeierstrassCurve.Affine.monic_polynomial,
    C.aeval_coordYInFunctionField_polynomial⟩

/-- The image of `Y` is also integral over `FractionRing F[X]` (by lifting
via the scalar tower; finite-dimensionality gives this directly). -/
theorem isIntegral_coordYInFunctionField_fracPoly :
    IsIntegral (FractionRing (Polynomial F)) C.coordYInFunctionField :=
  Algebra.IsIntegral.isIntegral _

/-- **T-INFRA-IC-003i**: In char ≠ 2, `F(C) / F(X)` is a separable extension. -/
instance algebra_isSeparable_functionField [NeZero (2 : F)] :
    Algebra.IsSeparable (FractionRing (Polynomial F)) C.FunctionField := by
  have : NeZero (2 : FractionRing (Polynomial F)) := by
    refine ⟨fun h => NeZero.ne (2 : F) ?_⟩
    refine FaithfulSMul.algebraMap_injective F (FractionRing (Polynomial F))
      (.trans ?_ (map_zero _).symm)
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F)) 2]
    simpa only [map_ofNat] using h
  refine ⟨fun α => ?_⟩
  have hint : IsIntegral (FractionRing (Polynomial F)) α :=
    Algebra.IsIntegral.isIntegral α
  refine Polynomial.separable_of_monic_irreducible_natDegree_le_two
    (minpoly.monic hint) (minpoly.irreducible hint) ?_
  calc (minpoly (FractionRing (Polynomial F)) α).natDegree
      ≤ Module.finrank (FractionRing (Polynomial F)) C.FunctionField :=
        minpoly.natDegree_le α
    _ = 2 := C.finrank_functionField_over_fracPolynomialX

/-- **IC-003ii (conditional)**: `F[C]` is the integral closure of `F[X]` in
`F(C)`, given that `F[C]` is integrally closed. -/
instance isIntegralClosure_coordinateRing_fracPolynomialX
    [IsIntegrallyClosed C.CoordinateRing] :
    IsIntegralClosure C.CoordinateRing (Polynomial F) C.FunctionField :=
  IsIntegralClosure.of_isIntegrallyClosed _ _ _

/-- **IC-004 (conditional)**: `F[C]` is a Dedekind ring (given `F[C]`
integrally closed). -/
instance isDedekindRing_coordinateRing
    [IsIntegrallyClosed C.CoordinateRing] :
    IsDedekindRing C.CoordinateRing := by
  rw [isDedekindRing_iff (A := C.CoordinateRing) C.FunctionField]
  refine ⟨inferInstance, inferInstance, fun {x} hx => ?_⟩
  exact IsIntegrallyClosed.isIntegral_iff.mp hx

/-- `IsDedekindDomain C.CoordinateRing` as a corollary (from `IsDedekindRing`
+ mathlib's `IsDomain C.CoordinateRing` instance). -/
instance isDedekindDomain_coordinateRing
    [IsIntegrallyClosed C.CoordinateRing] :
    IsDedekindDomain C.CoordinateRing := ⟨⟩

/-- **IC-005 (core bridge)**: if `f ∈ F(C)` is integral over `F[X]`, then `f`
is in the image of `C.CoordinateRing → C.FunctionField`. -/
theorem mem_coordinateRing_of_isIntegral_polynomialX
    [IsIntegrallyClosed C.CoordinateRing] {f : C.FunctionField}
    (hf : IsIntegral (Polynomial F) f) :
    ∃ u : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField u = f :=
  IsIntegralClosure.isIntegral_iff.mp hf

/-- **IC-006 (prime-based bridge)**: if every height-one-prime valuation of
`f ∈ F(C)` is at most 1 (i.e. `f` has no poles at any nonzero prime of
`C.CoordinateRing`), then `f ∈ C.CoordinateRing`. -/
theorem mem_coordinateRing_of_valuation_le_one
    [IsIntegrallyClosed C.CoordinateRing] (f : C.FunctionField)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing,
      v.valuation C.FunctionField f ≤ 1) :
    ∃ u : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField u = f :=
  IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    C.FunctionField f h

/-- `maximalIdealAt P` is nonzero: it contains the nonzero element
`XClass P.x` (the image of `X − P.x` in the coordinate ring). -/
theorem maximalIdealAt_ne_bot (P : C.SmoothPoint) :
    C.maximalIdealAt P ≠ ⊥ := by
  intro h
  have hmem : WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine P.x ∈
      C.maximalIdealAt P := by
    rw [maximalIdealAt, WeierstrassCurve.Affine.CoordinateRing.XYIdeal]
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [h, Submodule.mem_bot] at hmem
  exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := C.toAffine) P.x hmem

/-- The height-one spectrum element associated to a smooth point `P` of `C`
(requires `C.CoordinateRing` to be a Dedekind domain, e.g. under
`[IsIntegrallyClosed]`). -/
noncomputable def SmoothPoint.toHeightOneSpectrum
    [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) :
    IsDedekindDomain.HeightOneSpectrum C.CoordinateRing where
  asIdeal := C.maximalIdealAt P
  isPrime := (C.maximalIdealAt_isMaximal P).isPrime
  ne_bot := C.maximalIdealAt_ne_bot P

/-- The `F(X)`-basis of `F(C)` obtained by localizing the `F[X]`-basis `{1, Y}`
of `F[C]`. Reference: mathlib's `Basis.localizationLocalization`. -/
noncomputable def functionFieldBasis :
    Module.Basis (Fin 2) (FractionRing (Polynomial F)) C.FunctionField :=
  (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine).localizationLocalization
    (FractionRing (Polynomial F)) (nonZeroDivisors (Polynomial F))
    C.FunctionField

@[simp] theorem functionFieldBasis_zero :
    C.functionFieldBasis 0 = 1 := by
  simp only [functionFieldBasis, Module.Basis.localizationLocalization_apply]
  exact congrArg (algebraMap _ _) WeierstrassCurve.Affine.CoordinateRing.basis_zero
    |>.trans (map_one _)

@[simp] theorem functionFieldBasis_one :
    C.functionFieldBasis 1 = C.coordYInFunctionField := by
  simp only [functionFieldBasis, Module.Basis.localizationLocalization_apply]
  exact congrArg (algebraMap _ _) WeierstrassCurve.Affine.CoordinateRing.basis_one

/-- **IC-003ii Task A**: every element of `F(C)` decomposes as `p + q · Y`
with `p, q ∈ F(X)`. Obtained from `functionFieldBasis`. -/
theorem exists_decomp (x : C.FunctionField) :
    ∃ p q : FractionRing (Polynomial F),
      x = p • (1 : C.FunctionField) + q • C.coordYInFunctionField := by
  refine ⟨C.functionFieldBasis.repr x 0, C.functionFieldBasis.repr x 1, ?_⟩
  have hsum := C.functionFieldBasis.sum_repr x
  rw [Fin.sum_univ_two, C.functionFieldBasis_zero,
    C.functionFieldBasis_one] at hsum
  exact hsum.symm

/-- **IC-003ii Task B (base change)**: the `F(X)`-norm of an element of `F(C)`
in the image of `algebraMap F[C] F(C)` equals the `algebraMap` of its
`F[X]`-norm. Direct corollary of mathlib's `Algebra.norm_localization` using
our `IsLocalization` structure for `F[C] → F(C)` with `F[X]*` scalars. -/
theorem algebra_norm_fracPolyX_algebraMap (u : C.CoordinateRing) :
    (Algebra.norm (FractionRing (Polynomial F)))
        (algebraMap C.CoordinateRing C.FunctionField u) =
      algebraMap (Polynomial F) (FractionRing (Polynomial F))
        (Algebra.norm (Polynomial F) u) := by
  have : Module.Free (Polynomial F) C.CoordinateRing :=
    Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine)
  exact Algebra.norm_localization (Rₘ := FractionRing (Polynomial F))
    (Sₘ := C.FunctionField) (Polynomial F) (nonZeroDivisors (Polynomial F)) u

/-- The **polynomial discriminant** of a Weierstrass curve's affine polynomial
`W(X, Y) = Y² + (a₁ X + a₃) Y - (X³ + a₂ X² + a₄ X + a₆)`, viewed as a
quadratic in `Y`:

  `D := (a₁ X + a₃)² + 4 (X³ + a₂ X² + a₄ X + a₆) = 4 X³ + b₂ X² + 2 b₄ X + b₆`
       ∈ F[X].

This is (up to a factor of 16 depending on conventions) the discriminant of
the quadratic in `Y`. For a smooth Weierstrass curve (`[IsElliptic]`), `D` is
squarefree in `F[X]`, which is the key algebraic fact behind "smooth ⟹
integrally closed coordinate ring" (IC-003ii unconditional). -/
noncomputable def polynomialDiscriminant (C : SmoothPlaneCurve F) :
    Polynomial F :=
  4 * Polynomial.X ^ 3 + Polynomial.C C.toAffine.b₂ * Polynomial.X ^ 2 +
    Polynomial.C (2 * C.toAffine.b₄) * Polynomial.X +
    Polynomial.C C.toAffine.b₆

/-- In char ≠ 2, `C.polynomialDiscriminant` has degree 3 (its leading
coefficient is 4, which is nonzero iff char ≠ 2). -/
theorem polynomialDiscriminant_natDegree [NeZero (2 : F)] :
    C.polynomialDiscriminant.natDegree = 3 := by
  have h4 : (4 : F) ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := NeZero.ne _
    simpa [show (4 : F) = 2 * 2 by ring] using mul_ne_zero h2 h2
  unfold polynomialDiscriminant
  compute_degree!

/-- The polynomial discriminant is nonzero in char ≠ 2. -/
theorem polynomialDiscriminant_ne_zero [NeZero (2 : F)] :
    C.polynomialDiscriminant ≠ 0 := by
  intro h
  have := C.polynomialDiscriminant_natDegree
  rw [h, Polynomial.natDegree_zero] at this
  omega

/-- Coefficients of `C.polynomialDiscriminant`. -/
theorem polynomialDiscriminant_coeff_zero :
    C.polynomialDiscriminant.coeff 0 = C.toAffine.b₆ := by
  simp [polynomialDiscriminant]

theorem polynomialDiscriminant_coeff_one :
    C.polynomialDiscriminant.coeff 1 = 2 * C.toAffine.b₄ := by
  simp [polynomialDiscriminant]

theorem polynomialDiscriminant_coeff_two :
    C.polynomialDiscriminant.coeff 2 = C.toAffine.b₂ := by
  simp [polynomialDiscriminant]

theorem polynomialDiscriminant_coeff_three :
    C.polynomialDiscriminant.coeff 3 = 4 := by
  simp [polynomialDiscriminant]

/-- `C.polynomialDiscriminant.degree = 3` in char ≠ 2. -/
theorem polynomialDiscriminant_degree [NeZero (2 : F)] :
    C.polynomialDiscriminant.degree = 3 := by
  rw [Polynomial.degree_eq_natDegree C.polynomialDiscriminant_ne_zero,
    C.polynomialDiscriminant_natDegree]
  rfl

/-- **Task D key identity**: `Polynomial.discr C.polynomialDiscriminant =
16 * Δ` (using the standard cubic discriminant formula + the Weierstrass
`b₈` relation). -/
theorem polynomialDiscriminant_discr [NeZero (2 : F)] :
    C.polynomialDiscriminant.discr = 16 * C.toAffine.Δ := by
  rw [Polynomial.discr_of_degree_eq_three C.polynomialDiscriminant_degree]
  rw [polynomialDiscriminant_coeff_zero, polynomialDiscriminant_coeff_one,
    polynomialDiscriminant_coeff_two, polynomialDiscriminant_coeff_three]
  have hbrel : 4 * C.toAffine.b₈ = C.toAffine.b₂ * C.toAffine.b₆ -
      C.toAffine.b₄ ^ 2 := C.toAffine.b_relation
  simp only [WeierstrassCurve.Δ]
  linear_combination 4 * C.toAffine.b₂ ^ 2 * hbrel

/-- Under `[IsElliptic]` and char ≠ 2, the polynomial discriminant is nonzero. -/
theorem polynomialDiscriminant_discr_ne_zero [NeZero (2 : F)]
    [C.toAffine.IsElliptic] :
    C.polynomialDiscriminant.discr ≠ 0 := by
  rw [C.polynomialDiscriminant_discr]
  have h16 : (16 : F) ≠ 0 := by
    simpa [show (16 : F) = 2 ^ 4 by norm_num] using pow_ne_zero 4 (NeZero.ne (2 : F))
  exact mul_ne_zero h16 C.toAffine.isUnit_Δ.ne_zero

/-- Under char ≠ 2 and char ≠ 3, `C.polynomialDiscriminant.derivative` has
natDegree 2 (leading coefficient `12 = 3 · 4 ≠ 0`). -/
theorem polynomialDiscriminant_derivative_natDegree
    [NeZero (2 : F)] [NeZero (3 : F)] :
    C.polynomialDiscriminant.derivative.natDegree = 2 := by
  have h12 : (12 : F) ≠ 0 := by
    simpa [show (12 : F) = 2 ^ 2 * 3 by norm_num] using
      mul_ne_zero (pow_ne_zero 2 (NeZero.ne (2 : F))) (NeZero.ne (3 : F))
  have hcoeff_deriv2 : C.polynomialDiscriminant.derivative.coeff 2 = 12 := by
    rw [Polynomial.coeff_derivative, C.polynomialDiscriminant_coeff_three]
    norm_num
  apply le_antisymm
  · refine (Polynomial.natDegree_derivative_le _).trans ?_
    rw [C.polynomialDiscriminant_natDegree]
  · by_contra hlt
    push Not at hlt
    have := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hcoeff_deriv2] at this
    exact h12 this

/-- **Task D (main)**: under `[IsElliptic]` and char ≠ 2, char ≠ 3,
`C.polynomialDiscriminant` is squarefree. -/
theorem polynomialDiscriminant_squarefree [NeZero (2 : F)] [NeZero (3 : F)]
    [C.toAffine.IsElliptic] :
    Squarefree C.polynomialDiscriminant := by
  refine Polynomial.Separable.squarefree ?_
  have hf_ne : C.polynomialDiscriminant ≠ 0 := C.polynomialDiscriminant_ne_zero
  have hf_deg : 0 < C.polynomialDiscriminant.degree := by
    rw [C.polynomialDiscriminant_degree]; norm_num
  have h_res_formula := Polynomial.resultant_deriv hf_deg
  have hleadCoeff : C.polynomialDiscriminant.leadingCoeff = 4 := by
    rw [Polynomial.leadingCoeff, C.polynomialDiscriminant_natDegree]
    exact C.polynomialDiscriminant_coeff_three
  have hres_ne : Polynomial.resultant C.polynomialDiscriminant
      C.polynomialDiscriminant.derivative
      C.polynomialDiscriminant.natDegree
      (C.polynomialDiscriminant.natDegree - 1) ≠ 0 := by
    rw [h_res_formula, hleadCoeff]
    have h4 : (4 : F) ≠ 0 := by
      simpa [show (4 : F) = 2 ^ 2 by norm_num] using pow_ne_zero 2 (NeZero.ne (2 : F))
    have hsign : ((-1 : F) ^ (C.polynomialDiscriminant.natDegree *
        (C.polynomialDiscriminant.natDegree - 1) / 2)) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact mul_ne_zero (mul_ne_zero hsign h4) C.polynomialDiscriminant_discr_ne_zero
  rw [Polynomial.separable_def]
  have hderiv_natDeg : C.polynomialDiscriminant.derivative.natDegree =
      C.polynomialDiscriminant.natDegree - 1 := by
    rw [C.polynomialDiscriminant_derivative_natDegree,
      C.polynomialDiscriminant_natDegree]
  by_contra hnotcop
  apply hres_ne
  rw [show C.polynomialDiscriminant.natDegree - 1 =
    C.polynomialDiscriminant.derivative.natDegree from hderiv_natDeg.symm]
  rw [show Polynomial.resultant C.polynomialDiscriminant
    C.polynomialDiscriminant.derivative C.polynomialDiscriminant.natDegree
    C.polynomialDiscriminant.derivative.natDegree =
    Polynomial.resultant C.polynomialDiscriminant
      C.polynomialDiscriminant.derivative from rfl]
  rw [Polynomial.resultant_eq_zero_iff.mpr]
  exact ⟨Or.inl hf_ne, hnotcop⟩

/-- **Key algebraic identity**: for `x = p • 1 + q • coordY` in `F(C)` with
`p, q ∈ F(X)`, the element `x` satisfies `x² = α · x - γ` where
`α = 2p - qb`, `γ = p² - pqb - q²c` (with `b = a₁X + a₃`, `c = X³ + ... + a₆`
appearing via Weierstrass relations). This is the "minpoly of `x`" identity.

The key corollary: `α² - 4γ = q² · D` where `D = b² + 4c` is the polynomial
discriminant (`C.polynomialDiscriminant`). Used in Task F to extract `q ∈ F[X]`
from integrality. -/
theorem polynomialDiscriminant_eq_trace_sq_sub_four_norm
    (p q : FractionRing (Polynomial F)) :
    ∀ α γ : FractionRing (Polynomial F),
      α = 2 * p - q *
        algebraMap (Polynomial F) (FractionRing (Polynomial F))
          (Polynomial.C C.toAffine.a₁ * Polynomial.X +
            Polynomial.C C.toAffine.a₃) →
      γ = p ^ 2 - p * q *
        algebraMap (Polynomial F) (FractionRing (Polynomial F))
          (Polynomial.C C.toAffine.a₁ * Polynomial.X +
            Polynomial.C C.toAffine.a₃) -
        q ^ 2 *
        algebraMap (Polynomial F) (FractionRing (Polynomial F))
          (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
            Polynomial.C C.toAffine.a₄ * Polynomial.X +
            Polynomial.C C.toAffine.a₆) →
      α ^ 2 - 4 * γ = q ^ 2 *
        algebraMap (Polynomial F) (FractionRing (Polynomial F))
          C.polynomialDiscriminant := by
  intro α γ hα hγ
  rw [hα, hγ]
  simp only [polynomialDiscriminant, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The Weierstrass polynomial evaluated at `AdjoinRoot.root` yields zero in
the coordinate ring. Expanding this gives the Y² relation. -/
theorem coordY_sq_coord :
    (AdjoinRoot.root C.toAffine.polynomial) ^ 2 +
      algebraMap (Polynomial F) C.CoordinateRing
        (Polynomial.C C.toAffine.a₁ * Polynomial.X + Polynomial.C C.toAffine.a₃) *
      (AdjoinRoot.root C.toAffine.polynomial) -
    algebraMap (Polynomial F) C.CoordinateRing
      (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
        Polynomial.C C.toAffine.a₄ * Polynomial.X +
        Polynomial.C C.toAffine.a₆) = 0 := by
  have h_self : AdjoinRoot.mk C.toAffine.polynomial
      (Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C C.toAffine.a₁ * Polynomial.X +
          Polynomial.C C.toAffine.a₃) * Polynomial.X -
        Polynomial.C (Polynomial.X ^ 3 +
          Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C C.toAffine.a₄ * Polynomial.X +
          Polynomial.C C.toAffine.a₆)) = 0 :=
    AdjoinRoot.mk_self (f := C.toAffine.polynomial)
  rw [map_sub, map_add, map_mul, map_pow,
    show AdjoinRoot.mk C.toAffine.polynomial Polynomial.X =
      AdjoinRoot.root C.toAffine.polynomial from rfl, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
    show (AdjoinRoot.of C.toAffine.polynomial : Polynomial F →+* C.CoordinateRing) =
      algebraMap _ _ from (AdjoinRoot.algebraMap_eq _).symm] at h_self
  linear_combination h_self

/-- The Y² relation in F(C), image of the Coord-ring-level identity. -/
theorem coordYInFunctionField_sq :
    C.coordYInFunctionField ^ 2 = -algebraMap (Polynomial F) C.FunctionField
        (Polynomial.C C.toAffine.a₁ * Polynomial.X + Polynomial.C C.toAffine.a₃)
        * C.coordYInFunctionField +
      algebraMap (Polynomial F) C.FunctionField
        (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C C.toAffine.a₄ * Polynomial.X +
          Polynomial.C C.toAffine.a₆) := by
  have h_f := congrArg (algebraMap C.CoordinateRing C.FunctionField) C.coordY_sq_coord
  rw [map_sub, map_add, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing C.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing C.FunctionField,
    show algebraMap C.CoordinateRing C.FunctionField
      (AdjoinRoot.root C.toAffine.polynomial) = C.coordYInFunctionField from rfl] at h_f
  linear_combination h_f

/-- The Weierstrass linear coefficient `b = a₁ X + a₃` as an element of F(X). -/
noncomputable def bFracPoly : FractionRing (Polynomial F) :=
  algebraMap (Polynomial F) (FractionRing (Polynomial F))
    (Polynomial.C C.toAffine.a₁ * Polynomial.X + Polynomial.C C.toAffine.a₃)

/-- The Weierstrass cubic coefficient `c = X³ + a₂X² + a₄X + a₆` as an element of F(X). -/
noncomputable def cFracPoly : FractionRing (Polynomial F) :=
  algebraMap (Polynomial F) (FractionRing (Polynomial F))
    (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
      Polynomial.C C.toAffine.a₄ * Polynomial.X +
      Polynomial.C C.toAffine.a₆)

/-- The image of `bFracPoly` in `F(C)`. -/
theorem algebraMap_bFracPoly :
    algebraMap (FractionRing (Polynomial F)) C.FunctionField C.bFracPoly =
      algebraMap (Polynomial F) C.FunctionField
        (Polynomial.C C.toAffine.a₁ * Polynomial.X + Polynomial.C C.toAffine.a₃) := by
  unfold bFracPoly
  rw [← IsScalarTower.algebraMap_apply]

/-- The image of `cFracPoly` in `F(C)`. -/
theorem algebraMap_cFracPoly :
    algebraMap (FractionRing (Polynomial F)) C.FunctionField C.cFracPoly =
      algebraMap (Polynomial F) C.FunctionField
        (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C C.toAffine.a₄ * Polynomial.X +
          Polynomial.C C.toAffine.a₆) := by
  unfold cFracPoly
  rw [← IsScalarTower.algebraMap_apply]

/-- If `p • 1 + q • coordY = 0` in `F(C)` for `p, q ∈ F(X)`, then `p = q = 0`.
Consequence of `{1, coordY}` being an `F(X)`-basis of `F(C)`. -/
theorem decomp_zero_iff {p q : FractionRing (Polynomial F)}
    (h : p • (1 : C.FunctionField) + q • C.coordYInFunctionField = 0) :
    p = 0 ∧ q = 0 := by
  have hb := C.functionFieldBasis.linearIndependent
  rw [Fintype.linearIndependent_iff] at hb
  have heq : ∑ i : Fin 2, ![p, q] i • C.functionFieldBasis i = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      C.functionFieldBasis_zero, C.functionFieldBasis_one]
    exact h
  have := hb _ heq
  exact ⟨this 0, this 1⟩

/-- **Helper**: given `x = p • 1 + q • coordY`, if `x² - α · x + γ = 0` in F(C)
(with α, γ ∈ F(X) coerced), then
`(p² + q² · c - α · p + γ) = 0` and `(2 · p · q - q² · b - α · q) = 0`
in F(X). Uses `coordYInFunctionField_sq` + `decomp_zero_iff`. -/
theorem decomp_from_quadratic {p q : FractionRing (Polynomial F)}
    {α γ : FractionRing (Polynomial F)}
    (hx : (p • (1 : C.FunctionField) + q • C.coordYInFunctionField) ^ 2 -
        algebraMap (FractionRing (Polynomial F)) C.FunctionField α *
          (p • (1 : C.FunctionField) + q • C.coordYInFunctionField) +
        algebraMap (FractionRing (Polynomial F)) C.FunctionField γ = 0) :
    p ^ 2 + q ^ 2 * C.cFracPoly - α * p + γ = 0 ∧
    2 * p * q - q ^ 2 * C.bFracPoly - α * q = 0 := by
  have hcomp :
      ((p ^ 2 + q ^ 2 * C.cFracPoly - α * p + γ) •
          (1 : C.FunctionField) +
        (2 * p * q - q ^ 2 * C.bFracPoly - α * q) •
          C.coordYInFunctionField) = 0 := by
    have hx' : (algebraMap (FractionRing (Polynomial F)) C.FunctionField p +
        algebraMap (FractionRing (Polynomial F)) C.FunctionField q *
          C.coordYInFunctionField) ^ 2 -
        algebraMap (FractionRing (Polynomial F)) C.FunctionField α *
        (algebraMap (FractionRing (Polynomial F)) C.FunctionField p +
         algebraMap (FractionRing (Polynomial F)) C.FunctionField q *
          C.coordYInFunctionField) +
        algebraMap (FractionRing (Polynomial F)) C.FunctionField γ = 0 := by
      simpa only [Algebra.smul_def, mul_one] using hx
    have hYsq_alg :
        C.coordYInFunctionField ^ 2 =
        -(algebraMap (FractionRing (Polynomial F)) C.FunctionField C.bFracPoly) *
          C.coordYInFunctionField +
        algebraMap (FractionRing (Polynomial F)) C.FunctionField C.cFracPoly := by
      rw [C.algebraMap_bFracPoly, C.algebraMap_cFracPoly]
      exact C.coordYInFunctionField_sq
    simp only [Algebra.smul_def, mul_one, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    linear_combination hx' -
      (algebraMap (FractionRing (Polynomial F)) C.FunctionField q) ^ 2 * hYsq_alg
  exact C.decomp_zero_iff hcomp

/-- **Helper**: if `x ∈ F(C)` is integral over `F[X]` and its minpoly has
natDegree 1, then `x` is in the image of `F[C] → F(C)`. -/
theorem mem_coordinateRing_of_minpoly_natDegree_one
    {x : C.FunctionField} (hx_Fx : IsIntegral (Polynomial F) x)
    (hdeg : (minpoly (Polynomial F) x).natDegree = 1) :
    ∃ y : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField y = x := by
  have hm_monic := minpoly.monic hx_Fx
  have haeval_x := minpoly.aeval (Polynomial F) x
  rw [hm_monic.eq_X_add_C hdeg, map_add, Polynomial.aeval_X,
    Polynomial.aeval_C] at haeval_x
  refine ⟨-algebraMap (Polynomial F) C.CoordinateRing
    ((minpoly (Polynomial F) x).coeff 0), ?_⟩
  rw [map_neg,
    ← IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing
      C.FunctionField]
  linear_combination -haeval_x

/-- **Helper (Monic natDegree 2 form)**: a monic polynomial of natDegree 2 has
form `X² + C b · X + C c` for its coefficients. -/
theorem Polynomial.Monic.eq_X_sq_add_C_mul_X_add_C_of_natDegree_two
    {R : Type*} [Semiring R] [Nontrivial R] {p : Polynomial R}
    (hm : p.Monic) (hd : p.natDegree = 2) :
    p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X +
      Polynomial.C (p.coeff 0) := by
  refine Polynomial.ext fun n => ?_
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    · simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    · have hlead : p.coeff 2 = 1 := by rwa [← hd]
      simp [hlead, Polynomial.coeff_X_pow]
  · have hn_gt : p.natDegree < n := by rw [hd]; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn_gt]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    rw [if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 0),
      if_neg (by omega : n ≠ 1)]
    simp

-- Degree-2 case of `isIntegrallyClosed_coordinateRing_of_IsElliptic`, factored out:
-- squarefreeness of the discriminant extracts a degree-2-integral `x` into `F[C]`.
private theorem mem_coordinateRing_of_minpoly_natDegree_two
    [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic] {x : C.FunctionField}
    (hx_Fx : IsIntegral (Polynomial F) x) (hdeg2 : (minpoly (Polynomial F) x).natDegree = 2) :
    ∃ y : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField y = x := by
  obtain ⟨p, q, hpq⟩ := C.exists_decomp x
  have haeval_x := minpoly.aeval (Polynomial F) x
  rw [Polynomial.Monic.eq_X_sq_add_C_mul_X_add_C_of_natDegree_two (minpoly.monic hx_Fx) hdeg2,
    map_add, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Polynomial.aeval_C] at haeval_x
  set α : Polynomial F := -((minpoly (Polynomial F) x).coeff 1) with hα_def
  set γ : Polynomial F := (minpoly (Polynomial F) x).coeff 0 with hγ_def
  set αfx : FractionRing (Polynomial F) :=
    algebraMap (Polynomial F) (FractionRing (Polynomial F)) α with hαfx_def
  set γfx : FractionRing (Polynomial F) :=
    algebraMap (Polynomial F) (FractionRing (Polynomial F)) γ with hγfx_def
  have hx_quad :
      (p • (1 : C.FunctionField) + q • C.coordYInFunctionField) ^ 2 -
        algebraMap (FractionRing (Polynomial F)) C.FunctionField αfx *
          (p • (1 : C.FunctionField) + q • C.coordYInFunctionField) +
        algebraMap (FractionRing (Polynomial F)) C.FunctionField γfx = 0 := by
    have hα_img : algebraMap (FractionRing (Polynomial F)) C.FunctionField αfx =
        -algebraMap (Polynomial F) C.FunctionField
            ((minpoly (Polynomial F) x).coeff 1) := by
      change algebraMap (FractionRing (Polynomial F)) C.FunctionField
          (algebraMap (Polynomial F) (FractionRing (Polynomial F)) α) = _
      rw [← IsScalarTower.algebraMap_apply, map_neg]
    have hγ_img : algebraMap (FractionRing (Polynomial F)) C.FunctionField γfx =
        algebraMap (Polynomial F) C.FunctionField
            ((minpoly (Polynomial F) x).coeff 0) := by
      change algebraMap (FractionRing (Polynomial F)) C.FunctionField
          (algebraMap (Polynomial F) (FractionRing (Polynomial F)) γ) = _
      rw [← IsScalarTower.algebraMap_apply]
    rw [← hpq, hα_img, hγ_img]
    linear_combination haeval_x
  obtain ⟨hcomp1, hcomp2⟩ := C.decomp_from_quadratic hx_quad
  have hq_factor : q * (2 * p - q * C.bFracPoly - αfx) = 0 := by
    linear_combination hcomp2
  rcases mul_eq_zero.mp hq_factor with hq_zero | hα_val
  · exfalso
    have hx_fx : x = algebraMap (FractionRing (Polynomial F)) C.FunctionField p := by
      rw [hpq, hq_zero, zero_smul, add_zero, Algebra.smul_def, mul_one]
    have hmle1 : (minpoly (FractionRing (Polynomial F)) x).natDegree ≤ 1 := by
      have h_le : (minpoly (FractionRing (Polynomial F)) x).degree ≤
          (Polynomial.X - Polynomial.C p).degree :=
        minpoly.min _ _ (Polynomial.monic_X_sub_C p) (by
          rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hx_fx, sub_self])
      rw [Polynomial.degree_X_sub_C] at h_le
      exact Polynomial.natDegree_le_of_degree_le h_le
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' _ hx_Fx,
      Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F)))] at hmle1
    omega
  · have hα_formula : αfx = 2 * p - q * C.bFracPoly := by linear_combination -hα_val
    have hγ_formula : γfx = p ^ 2 - p * q * C.bFracPoly - q ^ 2 * C.cFracPoly := by
      linear_combination hcomp1 - p * hα_val
    have hDid :=
      C.polynomialDiscriminant_eq_trace_sq_sub_four_norm p q αfx γfx hα_formula hγ_formula
    have hq2D :
        q ^ 2 * algebraMap (Polynomial F) (FractionRing (Polynomial F))
          C.polynomialDiscriminant =
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (α ^ 2 - 4 * γ) := by
      rw [show algebraMap (Polynomial F) (FractionRing (Polynomial F)) (α ^ 2 - 4 * γ) =
        αfx ^ 2 - 4 * γfx by
        rw [hαfx_def, hγfx_def, map_sub, map_pow, map_mul, map_ofNat], ← hDid]
    obtain ⟨q', hq'⟩ := Polynomial.fractionRing_mem_range_of_sq_mul_squarefree
      (D := C.polynomialDiscriminant) (r := α ^ 2 - 4 * γ)
      C.polynomialDiscriminant_squarefree hq2D
    set bp : Polynomial F :=
      Polynomial.C C.toAffine.a₁ * Polynomial.X + Polynomial.C C.toAffine.a₃ with hbp_def
    have hbf_eq : C.bFracPoly =
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) bp := rfl
    have h2p : 2 * p = algebraMap (Polynomial F) (FractionRing (Polynomial F))
        (α + q' * bp) := by
      rw [map_add, map_mul, hq', ← hbf_eq, ← hαfx_def]
      linear_combination -hα_formula
    have h2_ne : (2 : F) ≠ 0 := NeZero.ne _
    set p' : Polynomial F := Polynomial.C ((2 : F)⁻¹) * (α + q' * bp) with hp'_def
    have h2p' : (2 : Polynomial F) * p' = α + q' * bp := by
      rw [hp'_def, show (2 : Polynomial F) = Polynomial.C 2 from (map_ofNat Polynomial.C 2).symm,
        ← mul_assoc, ← map_mul, mul_inv_cancel₀ h2_ne, map_one, one_mul]
    have hp_eq : p = algebraMap (Polynomial F) (FractionRing (Polynomial F)) p' := by
      have h2fx_map : (algebraMap (Polynomial F) (FractionRing (Polynomial F))) 2 =
          (2 : FractionRing (Polynomial F)) := map_ofNat _ 2
      have h2poly_ne : (2 : Polynomial F) ≠ 0 := by
        rw [show (2 : Polynomial F) = Polynomial.C 2 from (map_ofNat Polynomial.C 2).symm]
        exact (map_ne_zero_iff _ Polynomial.C_injective).mpr h2_ne
      have h2fx_ne : (2 : FractionRing (Polynomial F)) ≠ 0 := by
        rw [← h2fx_map]
        exact (map_ne_zero_iff _ (IsFractionRing.injective
          (Polynomial F) (FractionRing (Polynomial F)))).mpr h2poly_ne
      refine mul_left_cancel₀ h2fx_ne ?_
      rw [show (2 : FractionRing (Polynomial F)) *
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) p' =
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (α + q' * bp) by
          rw [← h2fx_map, ← map_mul, h2p'], ← h2p]
    have hp_img : (p : FractionRing (Polynomial F)) • (1 : C.FunctionField) =
        algebraMap C.CoordinateRing C.FunctionField
          (algebraMap (Polynomial F) C.CoordinateRing p') := by
      rw [Algebra.smul_def, mul_one, hp_eq,
        ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
          C.FunctionField,
        IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing C.FunctionField]
    have hq_img : (q : FractionRing (Polynomial F)) • C.coordYInFunctionField =
        algebraMap C.CoordinateRing C.FunctionField
          (algebraMap (Polynomial F) C.CoordinateRing q') *
            algebraMap C.CoordinateRing C.FunctionField
              (AdjoinRoot.root C.toAffine.polynomial) := by
      rw [Algebra.smul_def, ← hq',
        ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
          C.FunctionField,
        IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing C.FunctionField]
      rfl
    refine ⟨algebraMap (Polynomial F) C.CoordinateRing p' +
      algebraMap (Polynomial F) C.CoordinateRing q' * AdjoinRoot.root C.toAffine.polynomial, ?_⟩
    rw [(algebraMap C.CoordinateRing C.FunctionField).map_add,
      (algebraMap C.CoordinateRing C.FunctionField).map_mul, ← hp_img, ← hq_img, ← hpq]

/-- **Task F main theorem**: under `[NeZero 2]`, `[NeZero 3]`, `[IsElliptic]`,
`C.CoordinateRing` is integrally closed. -/
instance isIntegrallyClosed_coordinateRing_of_IsElliptic
    [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic] :
    IsIntegrallyClosed C.CoordinateRing := by
  rw [isIntegrallyClosed_iff C.FunctionField]
  intro x hx_Fcoord
  have hx_Fx : IsIntegral (Polynomial F) x := isIntegral_trans x hx_Fcoord
  have hdeg_pos : 0 < (minpoly (Polynomial F) x).natDegree := minpoly.natDegree_pos hx_Fx
  have hdeg_le : (minpoly (Polynomial F) x).natDegree ≤ 2 := by
    rw [← Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F))),
      ← minpoly.isIntegrallyClosed_eq_field_fractions' _ hx_Fx]
    calc _ ≤ Module.finrank (FractionRing (Polynomial F)) C.FunctionField :=
            minpoly.natDegree_le x
      _ = 2 := C.finrank_functionField_over_fracPolynomialX
  rcases Nat.lt_or_ge (minpoly (Polynomial F) x).natDegree 2 with hd1 | hd2
  · exact C.mem_coordinateRing_of_minpoly_natDegree_one hx_Fx (by omega)
  · exact C.mem_coordinateRing_of_minpoly_natDegree_two hx_Fx (by omega)

end SmoothPlaneCurve

end HasseWeil.Curves

