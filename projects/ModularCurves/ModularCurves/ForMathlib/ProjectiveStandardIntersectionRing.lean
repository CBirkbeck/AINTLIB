/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveSpaceChart
import ModularCurves.ForMathlib.LaurentMonomialBasis

/-!
# Coordinate intersections in projective space

The degree-zero homogeneous localization at a product of projective coordinates is identified with
an affine polynomial ring localized at a monomial. This gives its canonical Laurent-monomial basis.
-/

namespace MvPolynomial

open HomogeneousLocalization

noncomputable section

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra
local instance : DecidableEq σ := Classical.decEq σ

private noncomputable def homogeneousDegreeZeroCoeffHom :
    R →+* homogeneousSubmodule σ R 0 where
  toFun r := ⟨C r, by simp⟩
  map_one' := Subtype.ext (map_one C)
  map_mul' r s := Subtype.ext (map_mul C r s)
  map_zero' := Subtype.ext (map_zero C)
  map_add' r s := Subtype.ext (map_add C r s)

/-- The coefficient-ring map into a degree-zero homogeneous localization of a polynomial ring. -/
noncomputable def homogeneousAwayCoeffHom (f : MvPolynomial σ R) :
    R →+* Away (homogeneousSubmodule σ R) f :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
    (Submonoid.powers f)).comp homogeneousDegreeZeroCoeffHom

noncomputable instance homogeneousAwayAlgebra (f : MvPolynomial σ R) :
    Algebra R (Away (homogeneousSubmodule σ R) f) :=
  (homogeneousAwayCoeffHom f).toAlgebra

@[simp]
theorem val_algebraMap_homogeneousAway (f : MvPolynomial σ R) (r : R) :
    (algebraMap R (Away (homogeneousSubmodule σ R) f) r).val =
      Localization.mk (C r) 1 := by
  rfl

theorem algebraMap_homogeneousAway_X_eq_awayConst (i : σ) (r : R) :
    algebraMap R (Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)) r =
      awayConst R i r := by
  apply HomogeneousLocalization.val_injective
  rw [val_algebraMap_homogeneousAway, val_awayConst]

@[simp]
theorem chartRingEquiv_algebraMap (i : σ) (r : R) :
    chartRingEquiv R i
        (algebraMap R (Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)) r) =
      C r := by
  rw [algebraMap_homogeneousAway_X_eq_awayConst]
  change dehomogenizeAt R i (awayConst R i r) = C r
  have hconst : homogenizeAt R i (C r) = awayConst R i r := by
    rw [homogenizeAt, eval₂Hom_C]
    rfl
  rw [← hconst]
  simpa only [RingHom.comp_apply, RingHom.id_apply] using
    RingHom.congr_fun (dehomogenizeAt_comp_homogenizeAt R i) (C r)

/-- The product of the projective coordinates after the first entry of a tuple. -/
noncomputable def coordinateTailPolynomial {n : ℕ} (a : Fin (n + 1) → σ) :
    MvPolynomial σ R :=
  ∏ k : Fin n, X (a k.succ)

private noncomputable def coordinateTailExponentTerm {n : ℕ}
    (a : Fin (n + 1) → σ) (k : Fin n) : {j : σ // j ≠ a 0} →₀ ℕ := by
  classical
  exact if h : a k.succ ≠ a 0 then Finsupp.single ⟨a k.succ, h⟩ 1 else 0

/-- The affine-chart exponent vector obtained by dehomogenizing the tail coordinate product at
the first coordinate. -/
noncomputable def coordinateTailExponent {n : ℕ} (a : Fin (n + 1) → σ) :
    {j : σ // j ≠ a 0} →₀ ℕ :=
  ∑ k : Fin n, coordinateTailExponentTerm a k

/-- The tail coordinate product is homogeneous of degree `n`. -/
theorem coordinateTailPolynomial_mem {n : ℕ} (a : Fin (n + 1) → σ) :
    coordinateTailPolynomial (R := R) a ∈ homogeneousSubmodule σ R n := by
  classical
  have h := SetLike.prod_mem_graded (A := homogeneousSubmodule σ R)
    (F := Finset.univ) (g := fun k : Fin n => (X (a k.succ) : MvPolynomial σ R))
    (i := fun _ : Fin n => 1) (fun k _ => X_mem_homogeneousSubmodule_one R (a k.succ))
  simpa [coordinateTailPolynomial] using h

private lemma dehomogenizeAux_coordinateTailFactor {n : ℕ}
    (a : Fin (n + 1) → σ) (k : Fin n) :
    dehomogenizeAux R (a 0) (X (a k.succ)) =
      monomial (coordinateTailExponentTerm a k) 1 := by
  classical
  by_cases h : a k.succ = a 0
  · rw [h, dehomogenizeAux_X_self]
    have hterm : coordinateTailExponentTerm a k = 0 := by
      simp [coordinateTailExponentTerm, h]
    rw [hterm]
    rfl
  · rw [dehomogenizeAux_X_ne R (a 0) h]
    simp [coordinateTailExponentTerm, h, X]

private lemma prod_monomial_one {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]
    (s : Finset ι) (e : ι → τ →₀ ℕ) :
    (∏ i ∈ s, (monomial (e i) 1 : MvPolynomial τ R)) =
      monomial (∑ i ∈ s, e i) 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih, monomial_mul]

/-- Dehomogenizing the tail coordinate product gives its affine monomial. -/
theorem dehomogenizeAux_coordinateTailPolynomial {n : ℕ}
    (a : Fin (n + 1) → σ) :
    dehomogenizeAux R (a 0) (coordinateTailPolynomial (R := R) a) =
      monomial (coordinateTailExponent a) 1 := by
  classical
  rw [coordinateTailPolynomial, map_prod]
  calc
    (∏ k : Fin n, dehomogenizeAux R (a 0) (X (a k.succ))) =
        ∏ k : Fin n, monomial (coordinateTailExponentTerm a k) 1 := by
      apply Finset.prod_congr rfl
      intro k _
      exact dehomogenizeAux_coordinateTailFactor (R := R) a k
    _ = monomial (coordinateTailExponent a) 1 := by
      simpa [coordinateTailExponent] using
        prod_monomial_one (R := R) (Finset.univ : Finset (Fin n))
          (coordinateTailExponentTerm a)

/-- The homogeneous coordinate product attached to a tuple, split at its first entry. -/
noncomputable def coordinateProductPolynomial {n : ℕ} (a : Fin (n + 1) → σ) :
    MvPolynomial σ R :=
  X (a 0) * coordinateTailPolynomial (R := R) a

/-- The element of the first chart ring whose inversion gives the full tuple intersection. -/
noncomputable def coordinateTailLocalizationElement {n : ℕ} (a : Fin (n + 1) → σ) :
    Away (homogeneousSubmodule σ R) (X (a 0) : MvPolynomial σ R) :=
  Away.isLocalizationElem (X_mem_homogeneousSubmodule_one R (a 0))
    (coordinateTailPolynomial_mem (R := R) a)

/-- In affine coordinates on the first chart, the localization element is the tail monomial. -/
theorem chartRingEquiv_coordinateTailLocalizationElement {n : ℕ}
    (a : Fin (n + 1) → σ) :
    chartRingEquiv R (a 0) (coordinateTailLocalizationElement (R := R) a) =
      monomial (coordinateTailExponent a) 1 := by
  change dehomogenizeAt R (a 0)
    (Away.mk (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a 0)) n
      (coordinateTailPolynomial (R := R) a ^ 1) _) = _
  rw [dehomogenizeAt_mk, pow_one,
    dehomogenizeAux_coordinateTailPolynomial]

theorem coordinateTailAwayMap_algebraMap {n : ℕ}
    (a : Fin (n + 1) → σ) (r : R) :
    HomogeneousLocalization.awayMap
        (f := X (a 0)) (g := coordinateTailPolynomial (R := R) a)
        (x := coordinateProductPolynomial (R := R) a)
        (homogeneousSubmodule σ R) (coordinateTailPolynomial_mem (R := R) a) rfl
        (algebraMap R
          (Away (homogeneousSubmodule σ R) (X (a 0) : MvPolynomial σ R)) r) =
      algebraMap R
        (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) r := by
  change HomogeneousLocalization.awayMap
      (f := X (a 0)) (g := coordinateTailPolynomial (R := R) a)
      (x := coordinateProductPolynomial (R := R) a)
      (homogeneousSubmodule σ R) (coordinateTailPolynomial_mem (R := R) a) rfl
      (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
        (Submonoid.powers (X (a 0))) (homogeneousDegreeZeroCoeffHom r)) =
    HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ R)
      (Submonoid.powers (coordinateProductPolynomial (R := R) a))
      (homogeneousDegreeZeroCoeffHom r)
  exact HomogeneousLocalization.awayMap_fromZeroRingHom
    (homogeneousSubmodule σ R) (coordinateTailPolynomial_mem (R := R) a) rfl
    (homogeneousDegreeZeroCoeffHom r)

private theorem chartRingEquiv_map_coordinateTailPowers {n : ℕ}
    (a : Fin (n + 1) → σ) :
    (Submonoid.powers (coordinateTailLocalizationElement (R := R) a)).map
        (chartRingEquiv R (a 0)).toMonoidHom =
      Submonoid.powers (monomial (coordinateTailExponent a) (1 : R)) := by
  rw [Submonoid.map_powers]
  change Submonoid.powers
    (chartRingEquiv R (a 0) (coordinateTailLocalizationElement (R := R) a)) = _
  rw [chartRingEquiv_coordinateTailLocalizationElement]

/-- The degree-zero localization at a tuple coordinate product is the affine monomial
localization obtained by dehomogenizing at the first coordinate. -/
noncomputable def coordinateProductAwayRingEquiv {n : ℕ}
    (a : Fin (n + 1) → σ) :
    Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a) ≃+*
      Localization.Away (monomial (coordinateTailExponent a) (1 : R)) := by
  letI := (HomogeneousLocalization.awayMap
    (f := X (a 0)) (g := coordinateTailPolynomial (R := R) a)
    (x := coordinateProductPolynomial (R := R) a)
    (homogeneousSubmodule σ R) (coordinateTailPolynomial_mem (R := R) a) rfl).toAlgebra
  letI : IsLocalization.Away (coordinateTailLocalizationElement (R := R) a)
      (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) :=
    Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R (a 0))
      (coordinateTailPolynomial_mem (R := R) a) rfl one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coordinateTailLocalizationElement (R := R) a))
    (T := Submonoid.powers (monomial (coordinateTailExponent a) (1 : R)))
    (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a))
    (Localization.Away (monomial (coordinateTailExponent a) (1 : R)))
    (chartRingEquiv R (a 0)) (chartRingEquiv_map_coordinateTailPowers (R := R) a)

@[simp]
theorem coordinateProductAwayRingEquiv_algebraMap {n : ℕ}
    (a : Fin (n + 1) → σ) (r : R) :
    coordinateProductAwayRingEquiv (R := R) a
        (algebraMap R
          (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) r) =
      algebraMap R
        (Localization.Away (monomial (coordinateTailExponent a) (1 : R))) r := by
  letI := (HomogeneousLocalization.awayMap
    (f := X (a 0)) (g := coordinateTailPolynomial (R := R) a)
    (x := coordinateProductPolynomial (R := R) a)
    (homogeneousSubmodule σ R) (coordinateTailPolynomial_mem (R := R) a) rfl).toAlgebra
  letI : IsLocalization.Away (coordinateTailLocalizationElement (R := R) a)
      (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) :=
    Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R (a 0))
      (coordinateTailPolynomial_mem (R := R) a) rfl one_ne_zero
  rw [show algebraMap R
      (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) r =
      algebraMap
        (Away (homogeneousSubmodule σ R) (X (a 0) : MvPolynomial σ R))
        (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a))
        (algebraMap R
          (Away (homogeneousSubmodule σ R) (X (a 0) : MvPolynomial σ R)) r) by
    exact (coordinateTailAwayMap_algebraMap (R := R) a r).symm]
  change IsLocalization.ringEquivOfRingEquiv
      (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a))
      (Localization.Away (monomial (coordinateTailExponent a) (1 : R)))
      (chartRingEquiv R (a 0)) (chartRingEquiv_map_coordinateTailPowers (R := R) a)
      (algebraMap
        (Away (homogeneousSubmodule σ R) (X (a 0) : MvPolynomial σ R))
        (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a))
        (algebraMap R
          (Away (homogeneousSubmodule σ R) (X (a 0) : MvPolynomial σ R)) r)) = _
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  rw [chartRingEquiv_algebraMap]
  exact IsScalarTower.algebraMap_apply R
    (MvPolynomial {j : σ // j ≠ a 0} R)
    (Localization.Away (monomial (coordinateTailExponent a) (1 : R))) r

/-- The `R`-linear equivalence underlying `coordinateProductAwayRingEquiv`. -/
noncomputable def coordinateProductAwayLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → σ) :
    Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a) ≃ₗ[R]
      Localization.Away (monomial (coordinateTailExponent a) (1 : R)) :=
  { coordinateProductAwayRingEquiv (R := R) a with
    map_smul' := by
      intro r x
      simp only [Algebra.smul_def, RingHom.id_apply]
      change coordinateProductAwayRingEquiv (R := R) a
          (algebraMap R
            (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) r * x) =
        algebraMap R
            (Localization.Away (monomial (coordinateTailExponent a) (1 : R))) r *
          coordinateProductAwayRingEquiv (R := R) a x
      rw [map_mul, coordinateProductAwayRingEquiv_algebraMap] }

/-- The Laurent-monomial basis of the degree-zero homogeneous localization at a tuple of
projective coordinates. -/
noncomputable def coordinateProductAwayBasis {n : ℕ}
    (a : Fin (n + 1) → σ) :
    Module.Basis (laurentExponentSubmonoid (coordinateTailExponent a)) R
      (Away (homogeneousSubmodule σ R) (coordinateProductPolynomial (R := R) a)) :=
  (laurentMonomialBasis R (coordinateTailExponent a)).map
    (coordinateProductAwayLinearEquiv (R := R) a).symm

@[simp]
theorem coordinateProductAwayRingEquiv_basis_apply {n : ℕ}
    (a : Fin (n + 1) → σ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    coordinateProductAwayRingEquiv (R := R) a (coordinateProductAwayBasis (R := R) a e) =
      laurentMonomialBasis R (coordinateTailExponent a) e := by
  change coordinateProductAwayLinearEquiv (R := R) a
      ((coordinateProductAwayLinearEquiv (R := R) a).symm
        (laurentMonomialBasis R (coordinateTailExponent a) e)) = _
  rw [LinearEquiv.apply_symm_apply]

@[simp]
theorem coordinateProductAwayBasis_toLaurentMonomial {n : ℕ}
    (a : Fin (n + 1) → σ)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    laurentMonomialRingEquiv R (coordinateTailExponent a)
        (coordinateProductAwayRingEquiv (R := R) a
          (coordinateProductAwayBasis (R := R) a e)) =
      AddMonoidAlgebra.single e 1 := by
  rw [coordinateProductAwayRingEquiv_basis_apply,
    laurentMonomialRingEquiv_basis_apply]

end

end MvPolynomial
