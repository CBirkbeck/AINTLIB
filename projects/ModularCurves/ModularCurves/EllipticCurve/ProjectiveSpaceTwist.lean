/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveSpaceHyperplane
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.EllipticCurve.PoleSheaf

/-!
# Twists on polynomial projective space

This file starts the concrete construction of projective-space twists by showing
that the ideal module of a coordinate hyperplane is invertible. It is the model
of `O(-1)` used in the standard-cover cohomology calculation.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The ideal module of a coordinate hyperplane is invertible. This is the
concrete model of `O(-1)` on polynomial projective space. -/
theorem coordinateHyperplaneIdealModule_isInvertible (j : σ) :
    Scheme.Modules.IsInvertible
      (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) := by
  classical
  letI : IsClosedImmersion (coordinateHyperplaneι (R := R) j) :=
    coordinateHyperplaneι_isClosedImmersion j
  letI : QuasiCompact (coordinateHyperplaneι (R := R) j) := inferInstance
  apply ModularCurves.idealModule_isInvertible_of_locallyPrincipal
  intro y
  have hy : y ∈ ⨆ i : σ, coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  refine ⟨U, hyi, ?_⟩
  by_cases hji : j = i
  · subst i
    refine ⟨1, ?_, Submonoid.one_mem _⟩
    rw [coordinateHyperplaneι_ker_ideal_coordinateOpen_self,
      Ideal.span_singleton_one]
  · let r : Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) :=
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (awayVar R i ⟨j, hji⟩)
    refine ⟨r, ?_, ?_⟩
    · exact coordinateHyperplaneι_ker_ideal_coordinateOpen_of_ne i j hji
    · let e := (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
          (X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
      change e (awayVar R i ⟨j, hji⟩) ∈
        nonZeroDivisors Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i)
      rw [← MulEquivClass.map_nonZeroDivisors e]
      exact ⟨awayVar R i ⟨j, hji⟩, awayVar_mem_nonZeroDivisors R i ⟨j, hji⟩, rfl⟩

/-- The dual of the coordinate-hyperplane ideal module, giving the concrete
model of `O(1)` on polynomial projective space. -/
noncomputable def coordinateHyperplanePoleSheaf (j : σ) :
    (Proj (homogeneousSubmodule σ R)).Modules :=
  Scheme.Modules.dualObj
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j))

/-- The canonical coordinate section `O → O(1)`, obtained by dualizing the inclusion of
the coordinate-hyperplane ideal. -/
noncomputable def coordinateHyperplanePoleUnitHom (j : σ) :
    Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      coordinateHyperplanePoleSheaf (R := R) j :=
  (Scheme.Modules.dualUnitObjIso
      (X := Proj (homogeneousSubmodule σ R))).inv ≫
    Scheme.Modules.dualMapObj
      (ModularCurves.idealModuleToUnit
        (coordinateHyperplaneι (R := R) j))

/-- The canonical global coordinate section of the concrete `O(1)`. -/
noncomputable def coordinateHyperplanePoleSection (j : σ) :
    Γ(coordinateHyperplanePoleSheaf (R := R) j,
      (⊤ : (Proj (homogeneousSubmodule σ R)).Opens)) :=
  (coordinateHyperplanePoleUnitHom (R := R) j).val.app (.op ⊤)
    (show (Proj (homogeneousSubmodule σ R)).presheaf.obj (.op ⊤) from 1)

/-- The concrete `O(1)` on polynomial projective space is invertible. -/
theorem coordinateHyperplanePoleSheaf_isInvertible (j : σ) :
    Scheme.Modules.IsInvertible (coordinateHyperplanePoleSheaf (R := R) j) :=
  (coordinateHyperplaneIdealModule_isInvertible (R := R) j).dual

/-- The local equation of the coordinate hyperplane `X j = 0` on the standard
chart `D₊(X i)`: it is `1` on the `j`-chart and `X j / X i` otherwise. -/
noncomputable def coordinateHyperplaneLocalEquation (i j : σ) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) := by
  classical
  exact if hji : j = i then 1 else
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (awayVar R i ⟨j, hji⟩)

@[simp]
lemma coordinateHyperplaneLocalEquation_self (j : σ) :
    coordinateHyperplaneLocalEquation (R := R) j j = 1 := by
  simp [coordinateHyperplaneLocalEquation]

lemma coordinateHyperplaneLocalEquation_of_ne (i j : σ) (hji : j ≠ i) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (awayVar R i ⟨j, hji⟩) := by
  simp [coordinateHyperplaneLocalEquation, hji]

/-- The homogeneous-localization element defining the preimage of `D₊(X j)` on the
`X i`-chart maps to the local equation of the coordinate hyperplane. -/
lemma coordinateHyperplaneLocalEquation_eq_isLocalizationElem (i j : σ) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (HomogeneousLocalization.Away.isLocalizationElem
            (X_mem_homogeneousSubmodule_one R i)
            (X_mem_homogeneousSubmodule_one R j)) := by
  classical
  by_cases hji : j = i
  · subst j
    rw [coordinateHyperplaneLocalEquation_self]
    have hloc :
        HomogeneousLocalization.Away.isLocalizationElem
            (X_mem_homogeneousSubmodule_one R i)
            (X_mem_homogeneousSubmodule_one R i) = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.isLocalizationElem]
    rw [hloc, map_one]
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    have hloc :
        HomogeneousLocalization.Away.isLocalizationElem
            (X_mem_homogeneousSubmodule_one R i)
            (X_mem_homogeneousSubmodule_one R j) =
          awayVar R i ⟨j, hji⟩ := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.isLocalizationElem, awayVar]
    rw [hloc]

/-- The standard-chart local equation generates the coordinate-hyperplane
ideal. -/
lemma coordinateHyperplaneLocalEquation_span (i j : σ) :
    (coordinateHyperplaneι (R := R) j).ker.ideal
        ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩ =
      Ideal.span {coordinateHyperplaneLocalEquation (R := R) i j} := by
  by_cases hji : j = i
  · subst i
    rw [coordinateHyperplaneι_ker_ideal_coordinateOpen_self,
      coordinateHyperplaneLocalEquation_self, Ideal.span_singleton_one]
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    exact coordinateHyperplaneι_ker_ideal_coordinateOpen_of_ne i j hji

/-- The standard-chart local equation of a coordinate hyperplane is a
nonzerodivisor. -/
lemma coordinateHyperplaneLocalEquation_mem_nonZeroDivisors (i j : σ) :
    coordinateHyperplaneLocalEquation (R := R) i j ∈
      nonZeroDivisors
        Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) := by
  classical
  by_cases hji : j = i
  · subst i
    rw [coordinateHyperplaneLocalEquation_self]
    exact Submonoid.one_mem _
  · rw [coordinateHyperplaneLocalEquation_of_ne i j hji]
    let e := (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
      (X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
    change e (awayVar R i ⟨j, hji⟩) ∈
      nonZeroDivisors Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i)
    rw [← MulEquivClass.map_nonZeroDivisors e]
    exact ⟨awayVar R i ⟨j, hji⟩, awayVar_mem_nonZeroDivisors R i ⟨j, hji⟩, rfl⟩

private noncomputable def coordinateHyperplaneLocalEquationAway (i j : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i) := by
  classical
  exact if hji : j = i then 1 else awayVar R i ⟨j, hji⟩

private noncomputable def coordinateLeftAwayMap (i k : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i * X k) :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R k) rfl

private noncomputable def coordinateRightAwayMap (i k : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X k) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i * X k) :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R i) (mul_comm _ _)

private lemma coordinateHyperplaneLocalEquationAway_map (i k j : σ) :
    coordinateLeftAwayMap (R := R) i k
        (coordinateHyperplaneLocalEquationAway (R := R) i j) =
      coordinateLeftAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) i k) *
        coordinateRightAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) k j) := by
  classical
  by_cases hki : k = i
  · subst k
    have hmaps : coordinateLeftAwayMap (R := R) i i =
        coordinateRightAwayMap (R := R) i i := rfl
    rw [← hmaps]
    simp [coordinateHyperplaneLocalEquationAway]
  · by_cases hji : j = i
    · subst j
      rw [show coordinateHyperplaneLocalEquationAway (R := R) i i = 1 by
        simp [coordinateHyperplaneLocalEquationAway]]
      rw [show coordinateHyperplaneLocalEquationAway (R := R) i k =
          awayVar R i ⟨k, hki⟩ by
        simp [coordinateHyperplaneLocalEquationAway, hki]]
      rw [show coordinateHyperplaneLocalEquationAway (R := R) k i =
          awayVar R k ⟨i, Ne.symm hki⟩ by
        simp [coordinateHyperplaneLocalEquationAway, Ne.symm hki]]
      simp only [map_one]
      apply HomogeneousLocalization.val_injective
      simp only [coordinateLeftAwayMap, coordinateRightAwayMap, awayVar]
      rw [HomogeneousLocalization.awayMap_mk,
        HomogeneousLocalization.awayMap_mk,
        HomogeneousLocalization.val_mul,
        HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.Away.val_mk]
      rw [HomogeneousLocalization.val_one, Localization.mk_mul,
        ← Localization.mk_one, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      exact ⟨1, by simp; ring⟩
    · by_cases hjk : j = k
      · subst j
        simp [coordinateHyperplaneLocalEquationAway, hki]
      · rw [show coordinateHyperplaneLocalEquationAway (R := R) i j =
            awayVar R i ⟨j, hji⟩ by
          simp [coordinateHyperplaneLocalEquationAway, hji]]
        rw [show coordinateHyperplaneLocalEquationAway (R := R) i k =
            awayVar R i ⟨k, hki⟩ by
          simp [coordinateHyperplaneLocalEquationAway, hki]]
        rw [show coordinateHyperplaneLocalEquationAway (R := R) k j =
            awayVar R k ⟨j, hjk⟩ by
          simp [coordinateHyperplaneLocalEquationAway, hjk]]
        apply HomogeneousLocalization.val_injective
        simp only [coordinateLeftAwayMap, coordinateRightAwayMap, awayVar]
        rw [HomogeneousLocalization.awayMap_mk,
          HomogeneousLocalization.awayMap_mk,
          HomogeneousLocalization.awayMap_mk,
          HomogeneousLocalization.val_mul,
          HomogeneousLocalization.Away.val_mk,
          HomogeneousLocalization.Away.val_mk,
          HomogeneousLocalization.Away.val_mk]
        rw [Localization.mk_mul, Localization.mk_eq_mk_iff,
          Localization.r_iff_exists]
        exact ⟨1, by simp; ring⟩

private lemma coordinateHyperplaneLocalEquation_eq_awayToSection (i j : σ) :
    coordinateHyperplaneLocalEquation (R := R) i j =
      (Proj.awayToSection (homogeneousSubmodule σ R) (X i)).hom
        (coordinateHyperplaneLocalEquationAway (R := R) i j) := by
  classical
  by_cases hji : j = i
  · subst j
    simp [coordinateHyperplaneLocalEquation,
      coordinateHyperplaneLocalEquationAway]
  · simp [coordinateHyperplaneLocalEquation,
      coordinateHyperplaneLocalEquationAway, hji,
      Proj.basicOpenIsoAway]

/-- The canonical affine presentation of the overlap of two standard
coordinate opens. -/
abbrev coordinateOpenOverlap (i k : σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  Proj.basicOpen (homogeneousSubmodule σ R) (X i * X k)

/-- The canonical affine coordinate overlap is the intersection of the two
standard coordinate opens. -/
lemma coordinateOpenOverlap_eq (i k : σ) :
    coordinateOpenOverlap (R := R) i k =
      coordinateOpen (R := R) i ⊓ coordinateOpen (R := R) k :=
  Proj.basicOpen_mul (homogeneousSubmodule σ R) (X i) (X k)

/-- On the `i`-th standard chart, the principal open cut out by the `j`-th
coordinate ratio is the overlap with the `j`-th standard chart. -/
lemma coordinateHyperplaneLocalEquation_basicOpen (i j : σ) :
    (Proj (homogeneousSubmodule σ R)).basicOpen
        (coordinateHyperplaneLocalEquation (R := R) i j) =
      coordinateOpenOverlap (R := R) i j := by
  let A := homogeneousSubmodule σ R
  have hi : X i ∈ A 1 := X_mem_homogeneousSubmodule_one R i
  have hj : X j ∈ A 1 := X_mem_homogeneousSubmodule_one R j
  let U : (Proj A).Opens := coordinateOpen (R := R) i
  let e := Proj.basicOpenIsoSpec A (X i) hi one_pos
  let a : HomogeneousLocalization.Away A (X i) :=
    HomogeneousLocalization.Away.isLocalizationElem hi hj
  have hchart :
      U.toScheme.basicOpen
          (U.topIso.inv (coordinateHyperplaneLocalEquation (R := R) i j)) =
        U.ι ⁻¹ᵁ coordinateOpen (R := R) j := by
    calc
      _ = e.hom ⁻¹ᵁ
          (Spec (CommRingCat.of
            (HomogeneousLocalization.Away A (X i)))).basicOpen
              ((Scheme.ΓSpecIso _).inv a) := by
        rw [Scheme.preimage_basicOpen_top]
        apply congrArg U.toScheme.basicOpen
        change U.topIso.inv
            (coordinateHyperplaneLocalEquation (R := R) i j) =
          (Proj.basicOpenToSpec A (X i)).appTop
            ((Scheme.ΓSpecIso _).inv a)
        rw [show (Proj.basicOpenToSpec A (X i)).appTop =
            (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection A (X i) ≫
              U.topIso.inv from Proj.basicOpenToSpec_app_top A (X i)]
        simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
        rw [show Proj.awayToSection A (X i) =
            (Proj.basicOpenIsoAway A (X i)
              (X_mem_homogeneousSubmodule_one R i) one_pos).hom from rfl]
        exact congrArg U.topIso.inv
          (coordinateHyperplaneLocalEquation_eq_isLocalizationElem
            (R := R) i j)
      _ = e.hom ⁻¹ᵁ
          (Proj.awayι A (X i)
            hi one_pos ⁻¹ᵁ
              coordinateOpen (R := R) j) := by
        rw [basicOpen_eq_of_affine,
          Proj.awayι_preimage_basicOpen A
          hi one_pos hj one_pos]
      _ = U.ι ⁻¹ᵁ coordinateOpen (R := R) j := by
        rw [← Scheme.Hom.comp_preimage]
        rw [← Proj.basicOpenIsoSpec_inv_ι A (X i)
          hi one_pos]
        simp [e, U, A]
  calc
    _ = U.ι ''ᵁ U.toScheme.basicOpen
        (U.topIso.inv (coordinateHyperplaneLocalEquation (R := R) i j)) :=
      (U.ι_image_basicOpen_topIso_inv
        (coordinateHyperplaneLocalEquation (R := R) i j)).symm
    _ = U.ι ''ᵁ (U.ι ⁻¹ᵁ coordinateOpen (R := R) j) := by rw [hchart]
    _ = U ⊓ coordinateOpen (R := R) j := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      simp [U]
    _ = coordinateOpenOverlap (R := R) i j := by
      rw [coordinateOpenOverlap_eq]

/-- The canonical coordinate overlap is contained in its left chart. -/
lemma coordinateOpenOverlap_le_left (i k : σ) :
    coordinateOpenOverlap (R := R) i k ≤ coordinateOpen (R := R) i :=
  (coordinateOpenOverlap_eq (R := R) i k).trans_le inf_le_left

/-- The canonical coordinate overlap is contained in its right chart. -/
lemma coordinateOpenOverlap_le_right (i k : σ) :
    coordinateOpenOverlap (R := R) i k ≤ coordinateOpen (R := R) k :=
  (coordinateOpenOverlap_eq (R := R) i k).trans_le inf_le_right

/-- Within a standard-coordinate overlap, the basic open cut out by a third coordinate
ratio is its intersection with the third standard chart. -/
lemma coordinateOpenOverlap_basicOpen_localEquation (i k j : σ) :
    (Proj (homogeneousSubmodule σ R)).basicOpen
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) =
      coordinateOpenOverlap (R := R) i k ⊓ coordinateOpen (R := R) j := by
  rw [Scheme.basicOpen_res,
    coordinateHyperplaneLocalEquation_basicOpen,
    coordinateOpenOverlap_eq, coordinateOpenOverlap_eq]
  ac_rfl

/-- A section on one standard coordinate chart extends to any other chart after its overlap
restriction is multiplied by a power of the corresponding coordinate ratio. -/
lemma exists_coordinateChartExtension
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i j : σ) (s : Γ(M, coordinateOpen (R := R) j)) :
    ∃ (n : ℕ) (t : Γ(M, coordinateOpen (R := R) i)),
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op t =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s := by
  let X := Proj (homogeneousSubmodule σ R)
  let U : X.affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen (R := R) i⟩
  let f := coordinateHyperplaneLocalEquation (R := R) i j
  have hV : X.basicOpen f = coordinateOpenOverlap (R := R) i j :=
    coordinateHyperplaneLocalEquation_basicOpen (R := R) i j
  let e : Γ(M, coordinateOpenOverlap (R := R) i j) ≅
      Γ(M, X.basicOpen f) :=
    M.presheaf.mapIso (eqToIso hV).op
  let r : Γ(M, X.basicOpen f) :=
    e.hom (M.presheaf.map
      (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s)
  obtain ⟨n, t, ht⟩ :=
    Scheme.Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffineOpen
      M U f r
  refine ⟨n, t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have hleft :
      e.hom
          (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op t) =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op t := by
    simp only [e, Functor.mapIso_hom, ← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) _
  have hright :
      e.hom
          ((Proj (homogeneousSubmodule σ R)).presheaf.map
                (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
                (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s) =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • r := by
    have hmap := M.val.map_smul (eqToIso hV).op.hom
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
        (coordinateHyperplaneLocalEquation (R := R) i j ^ n))
      (M.presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s)
    refine hmap.trans ?_
    have hsection :
        M.val.map (eqToIso hV).op.hom
            (M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s) =
          r := by
      rfl
    rw [hsection]
    apply congrArg (fun a : Γ(X, X.basicOpen f) ↦ a • r)
    change X.ringCatSheaf.obj.map (eqToIso hV).op.hom
        (X.ringCatSheaf.obj.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
          (f ^ n)) =
      X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op (f ^ n)
    have hcomp :
        X.ringCatSheaf.obj.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op ≫
            X.ringCatSheaf.obj.map (eqToIso hV).op.hom =
          X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op := by
      rw [← Functor.map_comp]
      exact X.ringCatSheaf.obj.congr_map (Subsingleton.elim _ _)
    exact ConcreteCategory.congr_hom hcomp (f ^ n)
  exact hleft.trans (ht.trans hright.symm)

/-- Over a finite standard coordinate cover, the chart extensions of a section may all be
chosen with one common coordinate-ratio exponent. -/
lemma exists_coordinateChartExtension_forall [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (s : Γ(M, coordinateOpen (R := R) j)) :
    ∃ (n : ℕ) (t : ∀ i : σ, Γ(M, coordinateOpen (R := R) i)), ∀ i,
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op (t i) =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s := by
  classical
  choose n t ht using fun i ↦ exists_coordinateChartExtension M i j s
  let N := Finset.univ.sup n
  have hle (i : σ) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i ↦
    coordinateHyperplaneLocalEquation (R := R) i j ^ (N - n i) • t i,
    fun i ↦ ?_⟩
  rw [M.map_smul, ht i, ← mul_smul, ← map_mul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

/-- If a global section of a quasicoherent module vanishes on one standard
coordinate chart, then its restriction to any other chart is annihilated by
some power of the corresponding coordinate ratio. -/
lemma exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i j : σ) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (coordinateOpen (R := R) j).leTop.op t = 0) :
    ∃ n : ℕ,
      coordinateHyperplaneLocalEquation (R := R) i j ^ n •
        M.presheaf.map (coordinateOpen (R := R) i).leTop.op t = 0 := by
  let X := Proj (homogeneousSubmodule σ R)
  let U : X.affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen (R := R) i⟩
  let V : X.Opens :=
    X.basicOpen (coordinateHyperplaneLocalEquation (R := R) i j)
  have hVi : V ≤ U.1 := X.basicOpen_le _
  have hVj : V ≤ coordinateOpen (R := R) j := by
    change X.basicOpen (coordinateHyperplaneLocalEquation (R := R) i j) ≤
      coordinateOpen (R := R) j
    rw [coordinateHyperplaneLocalEquation_basicOpen]
    exact coordinateOpenOverlap_le_right (R := R) i j
  have hi :
      M.presheaf.map (homOfLE hVi).op
          (M.presheaf.map U.1.leTop.op t) =
        M.presheaf.map V.leTop.op t := by
    rw [← M.presheaf.map_comp_apply]
    congr 1
  have hj :
      M.presheaf.map (homOfLE hVj).op
          (M.presheaf.map (coordinateOpen (R := R) j).leTop.op t) =
        M.presheaf.map V.leTop.op t := by
    rw [← M.presheaf.map_comp_apply]
    congr 1
  apply
    Scheme.Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
      M U (coordinateHyperplaneLocalEquation (R := R) i j)
        (M.presheaf.map U.1.leTop.op t)
  change M.presheaf.map (homOfLE hVi).op
      (M.presheaf.map U.1.leTop.op t) = 0
  rw [hi, ← hj, ht, map_zero]

/-- For a finite standard coordinate cover, the chartwise annihilating powers
of a coordinate ratio may be replaced by one common exponent. -/
lemma exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero_forall
    [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (coordinateOpen (R := R) j).leTop.op t = 0) :
    ∃ n : ℕ, ∀ i : σ,
      coordinateHyperplaneLocalEquation (R := R) i j ^ n •
        M.presheaf.map (coordinateOpen (R := R) i).leTop.op t = 0 := by
  classical
  choose e he using fun i ↦
    exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero
      M i j t ht
  let n := Finset.univ.sup e
  refine ⟨n, fun i ↦ ?_⟩
  have hle : e i ≤ n := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_comm, mul_smul, he i, smul_zero]

private lemma coordinateHyperplaneLocalEquation_restrict_product
    (i k j : σ) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplaneLocalEquation (R := R) i j) =
      (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i k) *
        (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j) := by
  rw [coordinateHyperplaneLocalEquation_eq_awayToSection,
    coordinateHyperplaneLocalEquation_eq_awayToSection,
    coordinateHyperplaneLocalEquation_eq_awayToSection]
  have hleft := Proj.awayMap_awayToSection
    (homogeneousSubmodule σ R) (X_mem_homogeneousSubmodule_one R k)
      (rfl : X i * X k = X i * X k)
  have hleftApply := congrArg
    (fun q ↦ q.hom (coordinateHyperplaneLocalEquationAway (R := R) i j)) hleft
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hleftApply
  have htransitionApply := congrArg
    (fun q ↦ q.hom (coordinateHyperplaneLocalEquationAway (R := R) i k)) hleft
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at htransitionApply
  have hright := Proj.awayMap_awayToSection
    (homogeneousSubmodule σ R) (X_mem_homogeneousSubmodule_one R i)
      (mul_comm (X i) (X k))
  have hrightApply := congrArg
    (fun q ↦ q.hom (coordinateHyperplaneLocalEquationAway (R := R) k j)) hright
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hrightApply
  rw [← hleftApply, ← htransitionApply, ← hrightApply]
  change (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
      (coordinateLeftAwayMap (R := R) i k
        (coordinateHyperplaneLocalEquationAway (R := R) i j)) =
    (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
        (coordinateLeftAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) i k)) *
      (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
        (coordinateRightAwayMap (R := R) i k
          (coordinateHyperplaneLocalEquationAway (R := R) k j))
  rw [← map_mul]
  exact congrArg
    (Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k)).hom
    (coordinateHyperplaneLocalEquationAway_map (R := R) i k j)

/-- The unit `X_k / X_i` on the overlap of the `i`th and `k`th standard
coordinate opens. -/
noncomputable def coordinateOpenTransitionUnit (i k : σ) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)ˣ where
  val := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i k)
  inv := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) k i)
  val_inv := by
    simpa [coordinateHyperplaneLocalEquation_self] using
      (coordinateHyperplaneLocalEquation_restrict_product (R := R) i k i).symm
  inv_val := by
    calc
      _ = (Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
            (coordinateHyperplaneLocalEquation (R := R) i k) *
          (Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
            (coordinateHyperplaneLocalEquation (R := R) k i) := mul_comm _ _
      _ = 1 := by
        simpa [coordinateHyperplaneLocalEquation_self] using
          (coordinateHyperplaneLocalEquation_restrict_product (R := R) i k i).symm

/-- The standard-chart transition unit, transported to the top ring of the
overlap open subscheme. -/
noncomputable def coordinateOpenTransitionTopUnit (i k : σ) :
    Γ((coordinateOpenOverlap (R := R) i k).toScheme,
      (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ :=
  Units.map
    ((((coordinateOpenOverlap (R := R) i k).ι.appIso ⊤).hom.hom.comp
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (eqToHom (coordinateOpenOverlap (R := R) i k).ι_image_top).op).hom).toMonoidHom)
    (coordinateOpenTransitionUnit (R := R) i k)

@[simp]
lemma coordinateOpenTransitionTopUnit_coe (i k : σ) :
    (coordinateOpenTransitionTopUnit (R := R) i k :
      Γ((coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
      Scheme.Modules.openTopSection (coordinateOpenOverlap (R := R) i k)
        (coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R),
            coordinateOpenOverlap (R := R) i k)) :=
  rfl

/-- On a standard-coordinate overlap, every coordinate-hyperplane local
equation changes by the unit `X_k / X_i`. -/
lemma coordinateHyperplaneLocalEquation_restrict_eq_transition_mul (i k j : σ) :
    (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplaneLocalEquation (R := R) i j) =
      (coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)) *
        (Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j) :=
  coordinateHyperplaneLocalEquation_restrict_product (R := R) i k j

/-- Two common-degree chart extensions of the same section agree up to the standard
transition factor after multiplication by a power of the coordinate cutting out the
triple overlap. -/
lemma exists_pow_coordinateChartDifference_eq_zero
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (i k j : σ) (n : ℕ)
    (s : Γ(M, coordinateOpen (R := R) j))
    (tI : Γ(M, coordinateOpen (R := R) i))
    (tK : Γ(M, coordinateOpen (R := R) k))
    (hI : M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op tI =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s)
    (hK : M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) k j)).op tK =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) k j)).op
              (coordinateHyperplaneLocalEquation (R := R) k j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) k j)).op s) :
    ∃ m : ℕ,
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ m •
        (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI -
          (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k)) ^ n •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK) = 0 := by
  let Xp := Proj (homogeneousSubmodule σ R)
  let W := coordinateOpenOverlap (R := R) i k
  let r : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i j)
  let d : Γ(M, W) := M.presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI -
    (coordinateOpenTransitionUnit (R := R) i k : Γ(Xp, W)) ^ n •
      M.presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK
  have hW : IsAffineOpen W :=
    Proj.isAffineOpen_basicOpen (homogeneousSubmodule σ R) (X i * X k)
      (SetLike.mul_mem_graded
        (X_mem_homogeneousSubmodule_one R i)
        (X_mem_homogeneousSubmodule_one R k)) (by omega)
  let U : Xp.affineOpens := ⟨W, hW⟩
  apply
    Scheme.Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
      M U r d
  let V := Xp.basicOpen r
  have hV : V = W ⊓ coordinateOpen (R := R) j :=
    coordinateOpenOverlap_basicOpen_localEquation (R := R) i k j
  have hVI : V ≤ coordinateOpenOverlap (R := R) i j := by
    rw [hV]
    dsimp only [W]
    rw [coordinateOpenOverlap_eq, coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hVK : V ≤ coordinateOpenOverlap (R := R) k j := by
    rw [hV]
    dsimp only [W]
    rw [coordinateOpenOverlap_eq, coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hMcomp : ∀ {A B C : Xp.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
      (x : Γ(M, A)),
      M.presheaf.map (homOfLE hCB).op
          (M.presheaf.map (homOfLE hBA).op x) =
        M.presheaf.map (homOfLE (hCB.trans hBA)).op x := by
    intro A B C hBA hCB x
    rw [← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x
  have hXcomp : ∀ {A B C : Xp.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
      (x : Γ(Xp, A)),
      Xp.presheaf.map (homOfLE hCB).op
          (Xp.presheaf.map (homOfLE hBA).op x) =
        Xp.presheaf.map (homOfLE (hCB.trans hBA)).op x := by
    intro A B C hBA hCB x
    rw [← Xp.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (Xp.presheaf.congr_map (Subsingleton.elim _ _)) x
  have hI' := congrArg (M.presheaf.map (homOfLE hVI).op) hI
  rw [M.map_smul, hMcomp, hXcomp, hMcomp] at hI'
  have hK' := congrArg (M.presheaf.map (homOfLE hVK).op) hK
  rw [M.map_smul, hMcomp, hXcomp, hMcomp] at hK'
  change M.presheaf.map (homOfLE (Xp.basicOpen_le r)).op d = 0
  dsimp only [d]
  rw [map_sub, M.map_smul, hMcomp, map_pow, hMcomp]
  rw [hI', hK']
  have hr := congrArg
    (Xp.presheaf.map (homOfLE (Xp.basicOpen_le r)).op)
    (coordinateHyperplaneLocalEquation_restrict_eq_transition_mul
      (R := R) i k j)
  rw [map_mul, hXcomp, hXcomp] at hr
  rw [map_pow, map_pow]
  rw [hr, mul_pow, mul_smul, sub_self]

/-- Over a finite standard coordinate cover, all transition-adjusted differences between
common-degree chart extensions are annihilated by one common coordinate power. -/
lemma exists_pow_coordinateChartDifference_eq_zero_forall [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (n : ℕ)
    (s : Γ(M, coordinateOpen (R := R) j))
    (t : ∀ i : σ, Γ(M, coordinateOpen (R := R) i))
    (ht : ∀ i,
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op (t i) =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i j)).op
              (coordinateHyperplaneLocalEquation (R := R) i j ^ n) •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i j)).op s) :
    ∃ m : ℕ, ∀ i k : σ,
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ m •
        (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (t i) -
          (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k)) ^ n •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op (t k)) = 0 := by
  classical
  choose e he using fun p : σ × σ ↦
    exists_pow_coordinateChartDifference_eq_zero
      M p.1 p.2 j n s (t p.1) (t p.2) (ht p.1) (ht p.2)
  let m := Finset.univ.sup e
  refine ⟨m, fun i k ↦ ?_⟩
  have hle : e (i, k) ≤ m := Finset.le_sup (Finset.mem_univ (i, k))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_comm, mul_smul, he (i, k), smul_zero]

/-- Multiplying two chart extensions by the common annihilating coordinate power
turns their degree-`n` compatibility modulo torsion into exact degree-`n + m`
compatibility. -/
lemma coordinateChartExtensions_corrected_compatible
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (i k j : σ) (n m : ℕ)
    (tI : Γ(M, coordinateOpen (R := R) i))
    (tK : Γ(M, coordinateOpen (R := R) k))
    (h :
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ m •
        (M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI -
          (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k)) ^ n •
            M.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK) = 0) :
    M.presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplaneLocalEquation (R := R) i j ^ m • tI) =
      (coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R),
            coordinateOpenOverlap (R := R) i k)) ^ (n + m) •
        M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j ^ m • tK) := by
  let Xp := Proj (homogeneousSubmodule σ R)
  let W := coordinateOpenOverlap (R := R) i k
  let r : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i j)
  let q : Γ(Xp, W) := Xp.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) k j)
  let u : Γ(Xp, W) := coordinateOpenTransitionUnit (R := R) i k
  let a : Γ(M, W) := M.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI
  let b : Γ(M, W) := M.presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK
  have hr : r = u * q :=
    coordinateHyperplaneLocalEquation_restrict_eq_transition_mul
      (R := R) i k j
  have hab : r ^ m • a = r ^ m • (u ^ n • b) := by
    apply sub_eq_zero.mp
    rw [← smul_sub]
    exact h
  have hscalar : r ^ m * u ^ n = u ^ (n + m) * q ^ m := by
    rw [hr, mul_pow, pow_add]
    ring
  calc
    _ = r ^ m • a := by rw [M.map_smul, map_pow]
    _ = r ^ m • (u ^ n • b) := hab
    _ = (r ^ m * u ^ n) • b := by rw [mul_smul]
    _ = (u ^ (n + m) * q ^ m) • b := by rw [hscalar]
    _ = u ^ (n + m) • (q ^ m • b) := by rw [mul_smul]
    _ = _ := by rw [M.map_smul, map_pow]

/-- The explicit standard-chart trivialization of the coordinate-hyperplane
ideal module `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModuleTrivialization (i j : σ) :
    Scheme.Modules.unitObj
        (coordinateOpen (R := R) i).toScheme ≅
      (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)).restrict
        (coordinateOpen (R := R) i).ι := by
  letI : IsClosedImmersion (coordinateHyperplaneι (R := R) j) :=
    coordinateHyperplaneι_isClosedImmersion j
  letI : QuasiCompact (coordinateHyperplaneι (R := R) j) := inferInstance
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let r := coordinateHyperplaneLocalEquation (R := R) i j
  have hr : r ∈ (coordinateHyperplaneι (R := R) j).ker.ideal U := by
    rw [coordinateHyperplaneLocalEquation_span]
    exact Ideal.mem_span_singleton_self r
  exact ModularCurves.localIdealGeneratorIso
    (coordinateHyperplaneι (R := R) j) U r hr
      (coordinateHyperplaneLocalEquation_span i j)
      (coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j)

/-- The explicit standard-chart trivialization of the coordinate-hyperplane
pole sheaf `O(1)`. -/
noncomputable def coordinateHyperplanePoleSheafTrivialization (i j : σ) :
    (coordinateHyperplanePoleSheaf (R := R) j).restrict
        (coordinateOpen (R := R) i).ι ≅
      Scheme.Modules.unitObj (coordinateOpen (R := R) i).toScheme :=
  Scheme.Modules.dualRestrictIsoOfRestrictIso
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j))
    (coordinateOpen (R := R) i)
    (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

section

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

private noncomputable def coordinateHyperplaneIdealOverTrivialization
    (i j : σ) :
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)).over
        (coordinateOpen (R := R) i) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (coordinateOpen (R := R) i)) :=
  Scheme.Modules.overTrivializationOfRestrictIso _ _
    (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

private theorem coordinateHyperplaneIdealOverTrivialization_inv_comp
    (i j : σ) :
    (coordinateHyperplaneIdealOverTrivialization (R := R) i j).inv ≫
        (ModularCurves.idealModuleToUnit
          (coordinateHyperplaneι (R := R) j)).over
            (coordinateOpen (R := R) i) =
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpen (R := R) i)
        (coordinateHyperplaneLocalEquation (R := R) i j) := by
  letI : IsClosedImmersion (coordinateHyperplaneι (R := R) j) :=
    coordinateHyperplaneι_isClosedImmersion j
  letI : QuasiCompact (coordinateHyperplaneι (R := R) j) := inferInstance
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let r := coordinateHyperplaneLocalEquation (R := R) i j
  have hr : r ∈ (coordinateHyperplaneι (R := R) j).ker.ideal U := by
    rw [coordinateHyperplaneLocalEquation_span]
    exact Ideal.mem_span_singleton_self r
  simpa only [coordinateHyperplaneIdealOverTrivialization,
    coordinateHyperplaneIdealModuleTrivialization] using
      ModularCurves.localIdealGeneratorOverTrivialization_inv_comp
        (coordinateHyperplaneι (R := R) j) U r hr
          (coordinateHyperplaneLocalEquation_span i j)
          (coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j)

/-- In a standard-chart frame, the canonical coordinate section of `O(1)` is
multiplication by the local equation of the coordinate hyperplane. -/
theorem coordinateHyperplanePoleUnitHom_over_comp_trivialization
    (i j : σ) :
    ((coordinateHyperplanePoleUnitHom (R := R) j).over
        (coordinateOpen (R := R) i)) ≫
        (ModularCurves.SheafOfModules.dualOverIsoOfIso
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (ModularCurves.idealModule
            (coordinateHyperplaneι (R := R) j))
          (coordinateOpen (R := R) i)
          (Scheme.Modules.overTrivializationOfRestrictIso _ _
            (coordinateHyperplaneIdealModuleTrivialization
              (R := R) i j).symm)).hom =
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpen (R := R) i)
        (coordinateHyperplaneLocalEquation (R := R) i j) := by
  exact ModularCurves.dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    (ModularCurves.idealModuleToUnit
      (coordinateHyperplaneι (R := R) j))
    (coordinateOpen (R := R) i)
    (coordinateHyperplaneIdealOverTrivialization (R := R) i j)
    (coordinateHyperplaneLocalEquation (R := R) i j)
    (coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) i j)

/-- In the standard-chart frame, the canonical global section of `O(1)` has
coordinate equal to the local equation of the coordinate hyperplane. -/
theorem coordinateHyperplanePoleSection_localTrivializationTopSection
    (i j : σ) :
    ModularCurves.localTrivializationTopSection
        (coordinateHyperplanePoleSheaf (R := R) j)
        ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
        (coordinateHyperplanePoleSheafTrivialization (R := R) i j)
        (coordinateHyperplanePoleSection (R := R) j) =
      ModularCurves.affineOpenTopSection
        ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
        (coordinateHyperplaneLocalEquation (R := R) i j) := by
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) U.1
      (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  let ePole := ModularCurves.SheafOfModules.dualOverIsoOfIso
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) U.1 eIdeal
  have h := ModularCurves.localTrivializationTopSection_unitHom_apply_one
    (coordinateHyperplanePoleSheaf (R := R) j) U
    (coordinateHyperplanePoleUnitHom (R := R) j) ePole
    (coordinateHyperplaneLocalEquation (R := R) i j)
    (coordinateHyperplanePoleUnitHom_over_comp_trivialization
      (R := R) i j)
  have he : coordinateHyperplanePoleSheafTrivialization (R := R) i j =
      ModularCurves.restrictTrivializationOfOverIso
        (coordinateHyperplanePoleSheaf (R := R) j) U.1 ePole := by
    apply Iso.ext
    rfl
  rw [he]
  exact h

private noncomputable def coordinateHyperplaneIdealOverlapTrivializationLeft
    (i k j : σ) :
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)).over
        (coordinateOpenOverlap (R := R) i k) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (coordinateOpenOverlap (R := R) i k)) :=
  ModularCurves.SheafOfModules.restrictOverTrivialization
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j))
    (coordinateOpen (R := R) i)
    (coordinateHyperplaneIdealOverTrivialization (R := R) i j)
    (Over.mk (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)))

private noncomputable def coordinateHyperplaneIdealOverlapTrivializationRight
    (i k j : σ) :
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)).over
        (coordinateOpenOverlap (R := R) i k) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (coordinateOpenOverlap (R := R) i k)) :=
  ModularCurves.SheafOfModules.restrictOverTrivialization
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j))
    (coordinateOpen (R := R) k)
    (coordinateHyperplaneIdealOverTrivialization (R := R) k j)
    (Over.mk (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)))

private theorem coordinateHyperplaneIdealOverlapTrivializationLeft_inv_comp
    (i k j : σ) :
    (coordinateHyperplaneIdealOverlapTrivializationLeft
        (R := R) i k j).inv ≫
        (ModularCurves.idealModuleToUnit
          (coordinateHyperplaneι (R := R) j)).over
            (coordinateOpenOverlap (R := R) i k) =
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpenOverlap (R := R) i k)
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) i j)) := by
  simpa only [coordinateHyperplaneIdealOverlapTrivializationLeft] using
    ModularCurves.restrictOverTrivialization_inv_comp_over
      (ModularCurves.idealModuleToUnit
        (coordinateHyperplaneι (R := R) j))
      (coordinateOpen (R := R) i)
      (coordinateHyperplaneIdealOverTrivialization (R := R) i j)
      (coordinateHyperplaneLocalEquation (R := R) i j)
      (coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) i j)
      (coordinateOpenOverlap_le_left (R := R) i k)

private theorem coordinateHyperplaneIdealOverlapTrivializationRight_inv_comp
    (i k j : σ) :
    (coordinateHyperplaneIdealOverlapTrivializationRight
        (R := R) i k j).inv ≫
        (ModularCurves.idealModuleToUnit
          (coordinateHyperplaneι (R := R) j)).over
            (coordinateOpenOverlap (R := R) i k) =
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpenOverlap (R := R) i k)
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
          (coordinateHyperplaneLocalEquation (R := R) k j)) := by
  simpa only [coordinateHyperplaneIdealOverlapTrivializationRight] using
    ModularCurves.restrictOverTrivialization_inv_comp_over
      (ModularCurves.idealModuleToUnit
        (coordinateHyperplaneι (R := R) j))
      (coordinateOpen (R := R) k)
      (coordinateHyperplaneIdealOverTrivialization (R := R) k j)
      (coordinateHyperplaneLocalEquation (R := R) k j)
      (coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) k j)
      (coordinateOpenOverlap_le_right (R := R) i k)

private theorem coordinateHyperplaneIdealOverlap_transition (i k j : σ) :
    (coordinateHyperplaneIdealOverlapTrivializationRight
        (R := R) i k j).hom =
      (coordinateHyperplaneIdealOverlapTrivializationLeft
          (R := R) i k j).hom ≫
        ModularCurves.SheafOfModules.overUnitScalarEnd
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (coordinateOpenOverlap (R := R) i k)
          (coordinateOpenTransitionUnit (R := R) i k :
            Γ(Proj (homogeneousSubmodule σ R),
              coordinateOpenOverlap (R := R) i k)) := by
  let eI := coordinateHyperplaneIdealOverlapTrivializationLeft
    (R := R) i k j
  let eK := coordinateHyperplaneIdealOverlapTrivializationRight
    (R := R) i k j
  let inc :
      (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)).over
          (coordinateOpenOverlap (R := R) i k) ⟶
        SheafOfModules.unit
          ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
            (coordinateOpenOverlap (R := R) i k)) :=
    (ModularCurves.idealModuleToUnit
      (coordinateHyperplaneι (R := R) j)).over
        (coordinateOpenOverlap (R := R) i k)
  let rI := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) i j)
  let rK := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
    (coordinateHyperplaneLocalEquation (R := R) k j)
  let u : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenOverlap (R := R) i k) :=
    coordinateOpenTransitionUnit (R := R) i k
  let sI := ModularCurves.SheafOfModules.overUnitScalarEnd
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (coordinateOpenOverlap (R := R) i k) rI
  let sK := ModularCurves.SheafOfModules.overUnitScalarEnd
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (coordinateOpenOverlap (R := R) i k) rK
  let sU := ModularCurves.SheafOfModules.overUnitScalarEnd
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (coordinateOpenOverlap (R := R) i k) u
  change eK.hom = eI.hom ≫ sU
  have hI : eI.inv ≫ inc = sI :=
    coordinateHyperplaneIdealOverlapTrivializationLeft_inv_comp
      (R := R) i k j
  have hK : eK.inv ≫ inc = sK :=
    coordinateHyperplaneIdealOverlapTrivializationRight_inv_comp
      (R := R) i k j
  have hr : rI = u * rK :=
    coordinateHyperplaneLocalEquation_restrict_eq_transition_mul
      (R := R) i k j
  have hmul :=
    (ModularCurves.SheafOfModules.overUnitScalarEndRingHom
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf
      (coordinateOpenOverlap (R := R) i k)).map_mul rK u
  change ModularCurves.SheafOfModules.overUnitScalarEnd
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpenOverlap (R := R) i k) (rK * u) =
    ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (coordinateOpenOverlap (R := R) i k) u ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (coordinateOpenOverlap (R := R) i k) rK at hmul
  have hscalar : sI = sU ≫ sK := by
    dsimp only [sI, sU, sK]
    rw [hr, mul_comm u rK]
    exact hmul
  haveI : Mono inc := ModularCurves.sheafOfModules_mono_over
    (ModularCurves.idealModuleToUnit (coordinateHyperplaneι (R := R) j))
    (ModularCurves.idealModuleToUnit_mono
      (coordinateHyperplaneι (R := R) j))
    (coordinateOpenOverlap (R := R) i k)
  have hmonoComp : Mono (eK.inv ≫ inc) :=
    @mono_comp _ _ _ _ _ eK.inv inferInstance inc inferInstance
  haveI : Mono sK := by
    rw [← hK]
    exact hmonoComp
  apply (cancel_mono sK).1
  calc
    eK.hom ≫ sK = eK.hom ≫ (eK.inv ≫ inc) :=
      congrArg (fun q ↦ eK.hom ≫ q) hK.symm
    _ = inc := eK.hom_inv_id_assoc inc
    _ = eI.hom ≫ (eI.inv ≫ inc) := (eI.hom_inv_id_assoc inc).symm
    _ = eI.hom ≫ sI := congrArg (fun q ↦ eI.hom ≫ q) hI
    _ = eI.hom ≫ (sU ≫ sK) :=
      congrArg (fun q ↦ eI.hom ≫ q) hscalar
    _ = (eI.hom ≫ sU) ≫ sK := (Category.assoc _ _ _).symm

/-- On a coordinate overlap, the two `O(-1)` generator frames differ by
multiplication by `X_k / X_i`. -/
theorem coordinateHyperplaneIdealModuleTrivialization_restrict_transition
    (i k j : σ) :
    (Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenOverlap_le_right (R := R) i k)
        (coordinateHyperplaneIdealModuleTrivialization
          (R := R) k j).symm).hom =
      (Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_left (R := R) i k)
          (coordinateHyperplaneIdealModuleTrivialization
            (R := R) i j).symm).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection
            (coordinateOpenOverlap (R := R) i k)
            (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k))) := by
  let M := ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)
  let tI := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_left (R := R) i k)
    (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  let tK := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_right (R := R) i k)
    (coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  let eI := coordinateHyperplaneIdealOverlapTrivializationLeft
    (R := R) i k j
  let eK := coordinateHyperplaneIdealOverlapTrivializationRight
    (R := R) i k j
  let u : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenOverlap (R := R) i k) :=
    coordinateOpenTransitionUnit (R := R) i k
  change tK.hom = tI.hom ≫
    ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection
        (coordinateOpenOverlap (R := R) i k) u)
  have hOver : eK.hom = eI.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpenOverlap (R := R) i k) u :=
    coordinateHyperplaneIdealOverlap_transition (R := R) i k j
  have hScheme :=
    ModularCurves.restrictTrivializationOfOverIso_hom_eq_comp_scalar
      M (coordinateOpenOverlap (R := R) i k) eK eI u hOver
  have heI : Scheme.Modules.overTrivializationOfRestrictIso M
      (coordinateOpenOverlap (R := R) i k) tI = eI := by
    exact Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
      (coordinateOpenOverlap_le_left (R := R) i k)
      (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  have heK : Scheme.Modules.overTrivializationOfRestrictIso M
      (coordinateOpenOverlap (R := R) i k) tK = eK := by
    exact Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
      (coordinateOpenOverlap_le_right (R := R) i k)
      (coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  rw [← heK, ← heI] at hScheme
  simpa only [ModularCurves.restrictTrivializationOfOverTrivializationOfRestrictIso]
    using hScheme

/-- On a coordinate overlap, dualizing the two generator frames makes the
`O(1)` frames differ by multiplication by `X_k / X_i` in the reverse
direction. -/
theorem coordinateHyperplanePoleSheafTrivialization_restrict_transition
    (i k j : σ) :
    (Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenOverlap_le_left (R := R) i k)
        (coordinateHyperplanePoleSheafTrivialization
          (R := R) i j)).hom =
      (Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_right (R := R) i k)
          (coordinateHyperplanePoleSheafTrivialization
            (R := R) k j)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection
            (coordinateOpenOverlap (R := R) i k)
            (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k))) := by
  let M := ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)
  let tI := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_left (R := R) i k)
    (coordinateHyperplanePoleSheafTrivialization (R := R) i j)
  let tK := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_right (R := R) i k)
    (coordinateHyperplanePoleSheafTrivialization (R := R) k j)
  let eI := coordinateHyperplaneIdealOverlapTrivializationLeft
    (R := R) i k j
  let eK := coordinateHyperplaneIdealOverlapTrivializationRight
    (R := R) i k j
  let dI := ModularCurves.SheafOfModules.dualOverIsoOfIso
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf M
    (coordinateOpenOverlap (R := R) i k) eI
  let dK := ModularCurves.SheafOfModules.dualOverIsoOfIso
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf M
    (coordinateOpenOverlap (R := R) i k) eK
  let u : Γ(Proj (homogeneousSubmodule σ R),
      coordinateOpenOverlap (R := R) i k) :=
    coordinateOpenTransitionUnit (R := R) i k
  change tI.hom = tK.hom ≫
    ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection
        (coordinateOpenOverlap (R := R) i k) u)
  have hIdeal : eK.hom = eI.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpenOverlap (R := R) i k) u :=
    coordinateHyperplaneIdealOverlap_transition (R := R) i k j
  have hDual : dI.hom = dK.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpenOverlap (R := R) i k) u :=
    ModularCurves.dualOverIsoOfIso_hom_eq_comp_scalar M
      (coordinateOpenOverlap (R := R) i k) eI eK u hIdeal
  have hScheme :=
    ModularCurves.restrictTrivializationOfOverIso_hom_eq_comp_scalar
      (Scheme.Modules.dualObj M) (coordinateOpenOverlap (R := R) i k)
      dI dK u hDual
  have htI :=
    ModularCurves.restrictOpenTrivialization_dualRestrictIsoOfRestrictIso
      M (coordinateOpenOverlap_le_left (R := R) i k)
        (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  have htK :=
    ModularCurves.restrictOpenTrivialization_dualRestrictIsoOfRestrictIso
      M (coordinateOpenOverlap_le_right (R := R) i k)
        (coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  change tI = ModularCurves.restrictTrivializationOfOverIso
    (Scheme.Modules.dualObj M) (coordinateOpenOverlap (R := R) i k) dI at htI
  change tK = ModularCurves.restrictTrivializationOfOverIso
    (Scheme.Modules.dualObj M) (coordinateOpenOverlap (R := R) i k) dK at htK
  rw [← htI, ← htK] at hScheme
  exact hScheme

end

/-- The nonnegative twists `O(n)` obtained as monoidal powers of the concrete
coordinate-hyperplane `O(1)`. -/
noncomputable def coordinateHyperplanePoleSheafPower (j : σ) :
    ℕ → (Proj (homogeneousSubmodule σ R)).Modules
  | 0 => 𝟙_ (Proj (homogeneousSubmodule σ R)).Modules
  | n + 1 => coordinateHyperplanePoleSheafPower j n ⊗
      coordinateHyperplanePoleSheaf (R := R) j

@[simp]
lemma coordinateHyperplanePoleSheafPower_zero (j : σ) :
    coordinateHyperplanePoleSheafPower (R := R) j 0 =
      𝟙_ (Proj (homogeneousSubmodule σ R)).Modules :=
  rfl

@[simp]
lemma coordinateHyperplanePoleSheafPower_succ (j : σ) (n : ℕ) :
    coordinateHyperplanePoleSheafPower (R := R) j (n + 1) =
      coordinateHyperplanePoleSheafPower (R := R) j n ⊗
        coordinateHyperplanePoleSheaf (R := R) j :=
  rfl

/-- The canonical section of `O(n)`, obtained by starting with `1` in degree
zero and tensoring with the coordinate section in each successor degree. -/
noncomputable def coordinateHyperplanePoleSectionPower (j : σ) :
    ∀ n : ℕ,
      Γ(coordinateHyperplanePoleSheafPower (R := R) j n,
        (⊤ : (Proj (homogeneousSubmodule σ R)).Opens))
  | 0 => ModularCurves.monoidalUnitSection
      (Proj (homogeneousSubmodule σ R))
  | n + 1 => ModularCurves.tensorSection
      (coordinateHyperplanePoleSheafPower (R := R) j n)
      (coordinateHyperplanePoleSheaf (R := R) j) ⊤
      (coordinateHyperplanePoleSectionPower j n)
      (coordinateHyperplanePoleSection (R := R) j)

/-- A frame of `O(1)` on an open induces compatible frames of all nonnegative
twists on that open. -/
noncomputable def coordinateHyperplanePoleSheafPowerTrivializationOf
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (j : σ)
    (e : (coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
      (coordinateHyperplanePoleSheafPower (R := R) j n).restrict U.ι ≅
        Scheme.Modules.unitObj U.toScheme
  | 0 => ModularCurves.restrictMonoidalUnitIso U.ι ≪≫
      ModularCurves.monoidalUnitObjIso U.toScheme
  | n + 1 =>
      ModularCurves.restrictMonoidalTensorIso
          U.ι
          (coordinateHyperplanePoleSheafPower (R := R) j n)
          (coordinateHyperplanePoleSheaf (R := R) j) ≪≫
        (coordinateHyperplanePoleSheafPowerTrivializationOf U j e n ⊗ᵢ e) ≪≫
        ModularCurves.unitObjTensorIso U.toScheme

/-- Induced nonnegative-twist frames commute with restriction to a smaller
open. -/
theorem coordinateHyperplanePoleSheafPowerTrivializationOf_restrictOpen
    {U V : (Proj (homogeneousSubmodule σ R)).Opens} (hVU : V ≤ U) (j : σ)
    (e : (coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
    Scheme.Modules.restrictOpenTrivialization hVU
        (coordinateHyperplanePoleSheafPowerTrivializationOf U j e n) =
      coordinateHyperplanePoleSheafPowerTrivializationOf V j
        (Scheme.Modules.restrictOpenTrivialization hVU e) n := by
  intro n
  induction n with
  | zero =>
      exact ModularCurves.restrictMonoidalUnitTrivialization_restrictOpen hVU
  | succ n ih =>
      simp only [coordinateHyperplanePoleSheafPowerTrivializationOf,
        coordinateHyperplanePoleSheafPower]
      rw [ModularCurves.restrictMonoidalTensorTrivialization_restrictOpen]
      rw [ih]

/-- The compatible standard-chart frame of the nonnegative twist `O(n)`. -/
noncomputable def coordinateHyperplanePoleSheafPowerTrivialization
    (i j : σ) : ∀ n : ℕ,
      (coordinateHyperplanePoleSheafPower (R := R) j n).restrict
          (coordinateOpen (R := R) i).ι ≅
        Scheme.Modules.unitObj (coordinateOpen (R := R) i).toScheme :=
  coordinateHyperplanePoleSheafPowerTrivializationOf
    (coordinateOpen (R := R) i) j
      (coordinateHyperplanePoleSheafTrivialization (R := R) i j)

/-- In the standard-chart frame, the canonical section of `O(n)` has
coordinate equal to the `n`th power of the hyperplane's local equation. -/
theorem coordinateHyperplanePoleSectionPower_localTrivializationTopSection
    (i j : σ) (n : ℕ) :
    ModularCurves.localTrivializationTopSection
        (coordinateHyperplanePoleSheafPower (R := R) j n)
        ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
        (coordinateHyperplanePoleSheafPowerTrivialization
          (R := R) i j n)
        (coordinateHyperplanePoleSectionPower (R := R) j n) =
      (ModularCurves.affineOpenTopSection
        ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
        (coordinateHyperplaneLocalEquation (R := R) i j)) ^ n := by
  induction n with
  | zero =>
      simpa only [coordinateHyperplanePoleSectionPower,
        coordinateHyperplanePoleSheafPower,
        coordinateHyperplanePoleSheafPowerTrivialization,
        coordinateHyperplanePoleSheafPowerTrivializationOf, pow_zero] using
        ModularCurves.localTrivializationTopSection_monoidalUnitSection
          ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  | succ n ih =>
      change ModularCurves.localTrivializationTopSection
          (coordinateHyperplanePoleSheafPower (R := R) j n ⊗
            coordinateHyperplanePoleSheaf (R := R) j)
          ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
          (ModularCurves.restrictMonoidalTensorIso
              (coordinateOpen (R := R) i).ι
              (coordinateHyperplanePoleSheafPower (R := R) j n)
              (coordinateHyperplanePoleSheaf (R := R) j) ≪≫
            (coordinateHyperplanePoleSheafPowerTrivialization
                (R := R) i j n ⊗ᵢ
              coordinateHyperplanePoleSheafTrivialization (R := R) i j) ≪≫
            ModularCurves.unitObjTensorIso
              (coordinateOpen (R := R) i).toScheme)
          (ModularCurves.tensorSection
            (coordinateHyperplanePoleSheafPower (R := R) j n)
            (coordinateHyperplanePoleSheaf (R := R) j) ⊤
            (coordinateHyperplanePoleSectionPower (R := R) j n)
            (coordinateHyperplanePoleSection (R := R) j)) = _
      rw [ModularCurves.localTrivializationTopSection_tensorSection, ih,
        coordinateHyperplanePoleSection_localTrivializationTopSection]
      exact (pow_succ _ n).symm

/-- A quasicoherent section that vanishes on a standard coordinate open is
annihilated globally after tensoring with a sufficiently high power of the
corresponding coordinate-hyperplane section. This is the injective half of
the principal-open twisting argument of Stacks Project, Tag 01PW. -/
theorem exists_tensorSection_coordinateHyperplanePoleSectionPower_eq_zero_of_restrict_eq_zero
    [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (coordinateOpen (R := R) j).leTop.op t = 0) :
    ∃ n : ℕ,
      ModularCurves.tensorSection M
          (coordinateHyperplanePoleSheafPower (R := R) j n) ⊤ t
          (coordinateHyperplanePoleSectionPower (R := R) j n) = 0 := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_pow_coordinateHyperplaneLocalEquation_smul_restrict_eq_zero_forall
      M j t ht
  refine ⟨n, ?_⟩
  let X := Proj (homogeneousSubmodule σ R)
  let N := coordinateHyperplanePoleSheafPower (R := R) j n
  let s := coordinateHyperplanePoleSectionPower (R := R) j n
  let q := ModularCurves.tensorSection M N ⊤ t s
  change q = 0
  refine TopCat.Presheaf.IsSheaf.section_ext (M ⊗ N).2 fun x hx ↦ ?_
  have hxCover : x ∈ ⨆ i : σ, coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    exact hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxCover
  let U : X.affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen (R := R) i⟩
  refine ⟨U.1, le_top, hi, ?_⟩
  refine Eq.trans ?_ (map_zero _).symm
  apply (ModularCurves.localTrivializationRestriction_eq_zero_iff
    (M ⊗ N) U q).mp
  let P := (Scheme.Modules.restrictFunctor U.1.ι).obj M
  let Q := (Scheme.Modules.restrictFunctor U.1.ι).obj N
  let d := ModularCurves.restrictMonoidalTensorIso U.1.ι M N
  let e := coordinateHyperplanePoleSheafPowerTrivialization
    (R := R) i j n
  let k : P ⊗ Q ≅ P ⊗ Scheme.Modules.unitObj U.1.toScheme :=
    Iso.refl P ⊗ᵢ e
  let a : Γ(U.1.toScheme, ⊤) :=
    ModularCurves.affineOpenTopSection U
      (coordinateHyperplaneLocalEquation (R := R) i j ^ n)
  have hscalar :
      a • ModularCurves.localTrivializationRestriction M U t = 0 := by
    have htransport := congrArg
      (fun y ↦
        (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.1.ι_image_top).op y)) (hn i)
    rw [map_zero, map_zero] at htransport
    exact (ModularCurves.localTrivializationRestriction_smul_restrict
      M U (coordinateHyperplaneLocalEquation (R := R) i j ^ n) t).symm.trans
        htransport
  have hpow :
      ModularCurves.affineOpenTopSection U
          (coordinateHyperplaneLocalEquation (R := R) i j ^ n) =
        (ModularCurves.affineOpenTopSection U
          (coordinateHyperplaneLocalEquation (R := R) i j)) ^ n := by
    unfold ModularCurves.affineOpenTopSection
    rw [map_pow, map_pow]
  have hcoordinate :
      e.hom.val.app (.op (⊤ : U.1.toScheme.Opens))
          (ModularCurves.localTrivializationRestriction N U s) =
        (show Γ(Scheme.Modules.unitObj U.1.toScheme, ⊤) from a) := by
    exact (coordinateHyperplanePoleSectionPower_localTrivializationTopSection
      (R := R) i j n).trans hpow.symm
  have hzero :
      ModularCurves.tensorSection P (Scheme.Modules.unitObj U.1.toScheme) ⊤
          (ModularCurves.localTrivializationRestriction M U t)
          (show Γ(Scheme.Modules.unitObj U.1.toScheme, ⊤) from a) = 0 :=
    ModularCurves.tensorSection_eq_zero_of_smul_eq_zero P ⊤
      (ModularCurves.localTrivializationRestriction M U t)
      a hscalar
  have hd :
      d.hom.val.app (.op (⊤ : U.1.toScheme.Opens))
          (ModularCurves.localTrivializationRestriction (M ⊗ N) U q) =
        ModularCurves.tensorSection P Q ⊤
          (ModularCurves.localTrivializationRestriction M U t)
          (ModularCurves.localTrivializationRestriction N U s) := by
    exact ModularCurves.tensorSection_localTrivializationRestriction M N U t s
  have hk :
      k.hom.val.app (.op (⊤ : U.1.toScheme.Opens))
          (ModularCurves.tensorSection P Q ⊤
            (ModularCurves.localTrivializationRestriction M U t)
            (ModularCurves.localTrivializationRestriction N U s)) =
        ModularCurves.tensorSection P (Scheme.Modules.unitObj U.1.toScheme) ⊤
          (ModularCurves.localTrivializationRestriction M U t)
          (show Γ(Scheme.Modules.unitObj U.1.toScheme, ⊤) from a) := by
    rw [← hcoordinate]
    exact ModularCurves.tensorSection_map (𝟙 P) e.hom ⊤
      (ModularCurves.localTrivializationRestriction M U t)
      (ModularCurves.localTrivializationRestriction N U s)
  have hkzero :
      k.hom.val.app (.op (⊤ : U.1.toScheme.Opens))
          (ModularCurves.tensorSection P Q ⊤
            (ModularCurves.localTrivializationRestriction M U t)
            (ModularCurves.localTrivializationRestriction N U s)) = 0 :=
    hk.trans hzero
  have hlocalTensor :
      ModularCurves.tensorSection P Q ⊤
          (ModularCurves.localTrivializationRestriction M U t)
          (ModularCurves.localTrivializationRestriction N U s) = 0 := by
    have hback := congrArg
      (fun y ↦ k.inv.val.app (.op (⊤ : U.1.toScheme.Opens)) y) hkzero
    exact (Scheme.Modules.iso_hom_inv_app_applyT k
      (.op (⊤ : U.1.toScheme.Opens)) _).symm.trans
        (hback.trans (map_zero _))
  have hdzero :
      d.hom.val.app (.op (⊤ : U.1.toScheme.Opens))
          (ModularCurves.localTrivializationRestriction (M ⊗ N) U q) = 0 :=
    hd.trans hlocalTensor
  have hback := congrArg
    (fun y ↦ d.inv.val.app (.op (⊤ : U.1.toScheme.Opens)) y) hdzero
  exact (Scheme.Modules.iso_hom_inv_app_applyT d
    (.op (⊤ : U.1.toScheme.Opens)) _).symm.trans
      (hback.trans (map_zero _))

/-- Every nonnegative coordinate-hyperplane twist `O(n)` is invertible. -/
theorem coordinateHyperplanePoleSheafPower_isInvertible (j : σ) (n : ℕ) :
    Scheme.Modules.IsInvertible
      (coordinateHyperplanePoleSheafPower (R := R) j n) := by
  induction n with
  | zero =>
      exact Scheme.Modules.isInvertible_unit.of_iso
        (ModularCurves.monoidalUnitObjIso
          (Proj (homogeneousSubmodule σ R)))
  | succ n ih =>
      exact (ih.tensorObj
        (coordinateHyperplanePoleSheaf_isInvertible (R := R) j)).of_iso
          (ModularCurves.monoidalTensorObjIso _ _)

/-- On a coordinate overlap, the two `O(n)` frames differ by the `n`th power
of `X_k / X_i`. -/
theorem coordinateHyperplanePoleSheafPowerTrivialization_restrict_transition
    (i k j : σ) (n : ℕ) :
    (Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenOverlap_le_left (R := R) i k)
        (coordinateHyperplanePoleSheafPowerTrivialization
          (R := R) i j n)).hom =
      (Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_right (R := R) i k)
          (coordinateHyperplanePoleSheafPowerTrivialization
            (R := R) k j n)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((Scheme.Modules.openTopSection
            (coordinateOpenOverlap (R := R) i k)
            (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k))) ^ n) := by
  let U := coordinateOpenOverlap (R := R) i k
  let eI := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_left (R := R) i k)
    (coordinateHyperplanePoleSheafTrivialization (R := R) i j)
  let eK := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_right (R := R) i k)
    (coordinateHyperplanePoleSheafTrivialization (R := R) k j)
  let r := Scheme.Modules.openTopSection U
    (coordinateOpenTransitionUnit (R := R) i k :
      Γ(Proj (homogeneousSubmodule σ R), U))
  have hbase : eI.hom = eK.hom ≫
      ModularCurves.unitEndomorphismOfTopSection r := by
    exact coordinateHyperplanePoleSheafTrivialization_restrict_transition i k j
  have hpower := ModularCurves.recursiveTensorTrivialization_hom_eq_comp_scalar U
    (fun e n => coordinateHyperplanePoleSheafPowerTrivializationOf U j e n)
    (fun n => ModularCurves.restrictMonoidalTensorIso U.ι
      (coordinateHyperplanePoleSheafPower (R := R) j n)
      (coordinateHyperplanePoleSheaf (R := R) j))
    (fun _ _ => rfl) (fun _ _ => rfl) eI eK r hbase n
  have hI :
      Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_left (R := R) i k)
          (coordinateHyperplanePoleSheafPowerTrivialization
            (R := R) i j n) =
        coordinateHyperplanePoleSheafPowerTrivializationOf U j eI n := by
    exact coordinateHyperplanePoleSheafPowerTrivializationOf_restrictOpen
      (coordinateOpenOverlap_le_left (R := R) i k) j
        (coordinateHyperplanePoleSheafTrivialization (R := R) i j) n
  have hK :
      Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_right (R := R) i k)
          (coordinateHyperplanePoleSheafPowerTrivialization
            (R := R) k j n) =
        coordinateHyperplanePoleSheafPowerTrivializationOf U j eK n := by
    exact coordinateHyperplanePoleSheafPowerTrivializationOf_restrictOpen
      (coordinateOpenOverlap_le_right (R := R) i k) j
        (coordinateHyperplanePoleSheafTrivialization (R := R) k j) n
  rw [hI, hK]
  exact hpower

/-- The coefficient-one frame of `O(n)` on a standard coordinate chart. -/
noncomputable def coordinateHyperplanePoleSheafPowerFrameSection
    (i j : σ) (n : ℕ) :
    Γ(coordinateHyperplanePoleSheafPower (R := R) j n,
      coordinateOpen (R := R) i) :=
  ModularCurves.overTrivializationSection
    (coordinateHyperplanePoleSheafPower (R := R) j n)
    (coordinateOpen (R := R) i)
    (Scheme.Modules.overTrivializationOfRestrictIso
      (coordinateHyperplanePoleSheafPower (R := R) j n)
      (coordinateOpen (R := R) i)
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n)) 1

/-- On a coordinate overlap, multiplying the restricted `i`-frame of `O(n)`
by `(X_k / X_i)^n` gives the restricted `k`-frame. -/
theorem coordinateHyperplanePoleSheafPowerFrameSection_restrict_transition
    (i k j : σ) (n : ℕ) :
    (coordinateOpenTransitionUnit (R := R) i k :
        Γ(Proj (homogeneousSubmodule σ R),
          coordinateOpenOverlap (R := R) i k)) ^ n •
      (coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateHyperplanePoleSheafPowerFrameSection (R := R) i j n) =
      (coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
        (coordinateHyperplanePoleSheafPowerFrameSection (R := R) k j n) := by
  let X := Proj (homogeneousSubmodule σ R)
  let N := coordinateHyperplanePoleSheafPower (R := R) j n
  let UI := coordinateOpen (R := R) i
  let UK := coordinateOpen (R := R) k
  let W := coordinateOpenOverlap (R := R) i k
  let hI := coordinateOpenOverlap_le_left (R := R) i k
  let hK := coordinateOpenOverlap_le_right (R := R) i k
  let tI := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n
  let tK := coordinateHyperplanePoleSheafPowerTrivialization (R := R) k j n
  let eI := Scheme.Modules.overTrivializationOfRestrictIso N UI tI
  let eK := Scheme.Modules.overTrivializationOfRestrictIso N UK tK
  let eIR := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf N UI eI (Over.mk (homOfLE hI))
  let eKR := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf N UK eK (Over.mk (homOfLE hK))
  let u : Γ(X, W) := coordinateOpenTransitionUnit (R := R) i k
  have hsI := ModularCurves.overTrivializationSection_restrict N hI eI 1
  have hsK := ModularCurves.overTrivializationSection_restrict N hK eK 1
  have hTop : Scheme.Modules.openTopSection W (u ^ n) =
      (Scheme.Modules.openTopSection W u) ^ n := by
    unfold Scheme.Modules.openTopSection
    rw [map_pow, map_pow]
  have hOpen :
      (Scheme.Modules.restrictOpenTrivialization hI tI).hom =
        (Scheme.Modules.restrictOpenTrivialization hK tK).hom ≫
          ModularCurves.unitEndomorphismOfTopSection
            (Scheme.Modules.openTopSection W (u ^ n)) := by
    rw [hTop]
    exact coordinateHyperplanePoleSheafPowerTrivialization_restrict_transition
      (R := R) i k j n
  have hOver :=
    ModularCurves.overTrivializationOfRestrictIso_hom_eq_comp_scalar
      N W (Scheme.Modules.restrictOpenTrivialization hI tI)
        (Scheme.Modules.restrictOpenTrivialization hK tK) (u ^ n) hOpen
  have heIR : Scheme.Modules.overTrivializationOfRestrictIso N W
      (Scheme.Modules.restrictOpenTrivialization hI tI) = eIR :=
    Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hI tI
  have heKR : Scheme.Modules.overTrivializationOfRestrictIso N W
      (Scheme.Modules.restrictOpenTrivialization hK tK) = eKR :=
    Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hK tK
  rw [heIR, heKR] at hOver
  change u ^ n •
      N.presheaf.map (homOfLE hI).op
        (ModularCurves.overTrivializationSection N UI eI 1) =
    N.presheaf.map (homOfLE hK).op
      (ModularCurves.overTrivializationSection N UK eK 1)
  rw [hsI, hsK, map_one, map_one,
    ModularCurves.overTrivializationSection_smul, mul_one]
  exact ModularCurves.overTrivializationSection_eq_of_transition
    N W eIR eKR (u ^ n) (u ^ n) 1 hOver (by rw [one_mul])

/-- A module section on a standard chart, tensored with the standard local
frame of `O(n)`. -/
noncomputable def coordinateChartTwistedSection
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (i j : σ) (n : ℕ) (t : Γ(M, coordinateOpen (R := R) i)) :
    Γ(M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n,
      coordinateOpen (R := R) i) :=
  ModularCurves.tensorSection M
    (coordinateHyperplanePoleSheafPower (R := R) j n)
    (coordinateOpen (R := R) i) t
    (coordinateHyperplanePoleSheafPowerFrameSection (R := R) i j n)

/-- Coefficients related by the degree-`n` transition function determine equal
restricted sections of the twist `M ⊗ O(n)`. -/
theorem coordinateChartTwistedSection_restrict_eq
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (i k j : σ) (n : ℕ)
    (tI : Γ(M, coordinateOpen (R := R) i))
    (tK : Γ(M, coordinateOpen (R := R) k))
    (h :
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op tI =
        (coordinateOpenTransitionUnit (R := R) i k :
            Γ(Proj (homogeneousSubmodule σ R),
              coordinateOpenOverlap (R := R) i k)) ^ n •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op tK) :
    (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (coordinateChartTwistedSection (R := R) M i j n tI) =
      (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
        (coordinateChartTwistedSection (R := R) M k j n tK) := by
  let N := coordinateHyperplanePoleSheafPower (R := R) j n
  let W := coordinateOpenOverlap (R := R) i k
  let hI := coordinateOpenOverlap_le_left (R := R) i k
  let hK := coordinateOpenOverlap_le_right (R := R) i k
  let u : Γ(Proj (homogeneousSubmodule σ R), W) :=
    coordinateOpenTransitionUnit (R := R) i k
  let eI := coordinateHyperplanePoleSheafPowerFrameSection (R := R) i j n
  let eK := coordinateHyperplanePoleSheafPowerFrameSection (R := R) k j n
  calc
    (M ⊗ N).presheaf.map (homOfLE hI).op
          (ModularCurves.tensorSection M N _ tI eI) =
        ModularCurves.tensorSection M N W
          (M.presheaf.map (homOfLE hI).op tI)
          (N.presheaf.map (homOfLE hI).op eI) :=
      ModularCurves.tensorSection_restrict M N hI tI eI
    _ = ModularCurves.tensorSection M N W
          (u ^ n • M.presheaf.map (homOfLE hK).op tK)
          (N.presheaf.map (homOfLE hI).op eI) :=
      congrArg
        (fun q => ModularCurves.tensorSection M N W q
          (N.presheaf.map (homOfLE hI).op eI)) h
    _ = ModularCurves.tensorSection M N W
          (M.presheaf.map (homOfLE hK).op tK)
          (u ^ n • N.presheaf.map (homOfLE hI).op eI) :=
      ModularCurves.tensorSection_smul M N W (u ^ n)
        (M.presheaf.map (homOfLE hK).op tK)
        (N.presheaf.map (homOfLE hI).op eI)
    _ = ModularCurves.tensorSection M N W
          (M.presheaf.map (homOfLE hK).op tK)
          (N.presheaf.map (homOfLE hK).op eK) :=
      congrArg
        (ModularCurves.tensorSection M N W
          (M.presheaf.map (homOfLE hK).op tK))
        (coordinateHyperplanePoleSheafPowerFrameSection_restrict_transition
          (R := R) i k j n)
    _ = (M ⊗ N).presheaf.map (homOfLE hK).op
          (ModularCurves.tensorSection M N _ tK eK) :=
      (ModularCurves.tensorSection_restrict M N hK tK eK).symm

/-- Standard-chart coefficients satisfying the degree-`n` transition equations
glue to a global section of `M ⊗ O(n)`. -/
theorem exists_global_coordinateChartTwistedSection
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (n : ℕ)
    (t : ∀ i : σ, Γ(M, coordinateOpen (R := R) i))
    (ht : ∀ i k : σ,
      M.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op (t i) =
        (coordinateOpenTransitionUnit (R := R) i k :
            Γ(Proj (homogeneousSubmodule σ R),
              coordinateOpenOverlap (R := R) i k)) ^ n •
          M.presheaf.map
            (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
            (t k)) :
    ∃ q : Γ(M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n, ⊤),
      ∀ i : σ,
        (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
            (homOfLE (le_top : coordinateOpen (R := R) i ≤
              (⊤ : (Proj (homogeneousSubmodule σ R)).Opens))).op q =
          coordinateChartTwistedSection (R := R) M i j n (t i) := by
  let X := Proj (homogeneousSubmodule σ R)
  let N := coordinateHyperplanePoleSheafPower (R := R) j n
  let U : σ → X.Opens := fun i => coordinateOpen (R := R) i
  let sf : ∀ i, Γ(M ⊗ N, U i) := fun i =>
    coordinateChartTwistedSection (R := R) M i j n (t i)
  have hcpt : TopCat.Presheaf.IsCompatible (M ⊗ N).presheaf U sf := by
    intro i k
    dsimp only [U, sf]
    have h := coordinateChartTwistedSection_restrict_eq
      (R := R) M i k j n (t i) (t k) (ht i k)
    let P := M ⊗ N
    have hVW : coordinateOpen (R := R) i ⊓ coordinateOpen (R := R) k ≤
        coordinateOpenOverlap (R := R) i k := by
      rw [coordinateOpenOverlap_eq]
    have h' := congrArg (P.presheaf.map (homOfLE hVW).op) h
    have hleft :
        P.presheaf.map (homOfLE hVW).op
            (P.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
              (coordinateChartTwistedSection (R := R) M i j n (t i))) =
          P.presheaf.map
            (TopologicalSpace.Opens.infLELeft
              (coordinateOpen (R := R) i) (coordinateOpen (R := R) k)).op
            (coordinateChartTwistedSection (R := R) M i j n (t i)) := by
      change (P.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op ≫
        P.presheaf.map (homOfLE hVW).op)
          (coordinateChartTwistedSection (R := R) M i j n (t i)) = _
      have hMapComp := P.presheaf.map_comp
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
        (homOfLE hVW).op
      have hArrows :
          (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op ≫
              (homOfLE hVW).op =
            (TopologicalSpace.Opens.infLELeft
              (coordinateOpen (R := R) i) (coordinateOpen (R := R) k)).op :=
        Subsingleton.elim _ _
      exact ConcreteCategory.congr_hom
        (hMapComp.symm.trans (P.presheaf.congr_map hArrows)) _
    have hright :
        P.presheaf.map (homOfLE hVW).op
            (P.presheaf.map
              (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
              (coordinateChartTwistedSection (R := R) M k j n (t k))) =
          P.presheaf.map
            (TopologicalSpace.Opens.infLERight
              (coordinateOpen (R := R) i) (coordinateOpen (R := R) k)).op
            (coordinateChartTwistedSection (R := R) M k j n (t k)) := by
      change (P.presheaf.map
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op ≫
        P.presheaf.map (homOfLE hVW).op)
          (coordinateChartTwistedSection (R := R) M k j n (t k)) = _
      have hMapComp := P.presheaf.map_comp
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
        (homOfLE hVW).op
      have hArrows :
          (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op ≫
              (homOfLE hVW).op =
            (TopologicalSpace.Opens.infLERight
              (coordinateOpen (R := R) i) (coordinateOpen (R := R) k)).op :=
        Subsingleton.elim _ _
      exact ConcreteCategory.congr_hom
        (hMapComp.symm.trans (P.presheaf.congr_map hArrows)) _
    exact hleft.symm.trans (h'.trans hright)
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    change (⊤ : X.Opens) ≤ ⨆ i : σ, coordinateOpen (R := R) i
    rw [iSup_coordinateOpen_eq_top]
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(M ⊗ N).presheaf, (M ⊗ N).isSheaf⟩ U ⊤
      (fun _ => homOfLE le_top) hcover sf hcpt
  exact ⟨q, hq⟩

/-- The nonnegative powers of the concrete coordinate-hyperplane `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModulePower (j : σ) :
    ℕ → (Proj (homogeneousSubmodule σ R)).Modules
  | 0 => 𝟙_ (Proj (homogeneousSubmodule σ R)).Modules
  | n + 1 => coordinateHyperplaneIdealModulePower j n ⊗
      ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)

@[simp]
lemma coordinateHyperplaneIdealModulePower_zero (j : σ) :
    coordinateHyperplaneIdealModulePower (R := R) j 0 =
      𝟙_ (Proj (homogeneousSubmodule σ R)).Modules :=
  rfl

@[simp]
lemma coordinateHyperplaneIdealModulePower_succ (j : σ) (n : ℕ) :
    coordinateHyperplaneIdealModulePower (R := R) j (n + 1) =
      coordinateHyperplaneIdealModulePower (R := R) j n ⊗
        ModularCurves.idealModule (coordinateHyperplaneι (R := R) j) :=
  rfl

/-- A frame of `O(-1)` on an open induces compatible frames of all its
nonnegative powers on that open. -/
noncomputable def coordinateHyperplaneIdealModulePowerTrivializationOf
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (j : σ)
    (e : (ModularCurves.idealModule
        (coordinateHyperplaneι (R := R) j)).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
      (coordinateHyperplaneIdealModulePower (R := R) j n).restrict U.ι ≅
        Scheme.Modules.unitObj U.toScheme
  | 0 => ModularCurves.restrictMonoidalUnitIso U.ι ≪≫
      ModularCurves.monoidalUnitObjIso U.toScheme
  | n + 1 =>
      ModularCurves.restrictMonoidalTensorIso
          U.ι
          (coordinateHyperplaneIdealModulePower (R := R) j n)
          (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) ≪≫
        (coordinateHyperplaneIdealModulePowerTrivializationOf U j e n ⊗ᵢ e) ≪≫
        ModularCurves.unitObjTensorIso U.toScheme

/-- Induced nonnegative `O(-1)`-power frames commute with restriction to a
smaller open. -/
theorem coordinateHyperplaneIdealModulePowerTrivializationOf_restrictOpen
    {U V : (Proj (homogeneousSubmodule σ R)).Opens} (hVU : V ≤ U) (j : σ)
    (e : (ModularCurves.idealModule
        (coordinateHyperplaneι (R := R) j)).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
    Scheme.Modules.restrictOpenTrivialization hVU
        (coordinateHyperplaneIdealModulePowerTrivializationOf U j e n) =
      coordinateHyperplaneIdealModulePowerTrivializationOf V j
        (Scheme.Modules.restrictOpenTrivialization hVU e) n := by
  intro n
  induction n with
  | zero =>
      exact ModularCurves.restrictMonoidalUnitTrivialization_restrictOpen hVU
  | succ n ih =>
      simp only [coordinateHyperplaneIdealModulePowerTrivializationOf,
        coordinateHyperplaneIdealModulePower]
      rw [ModularCurves.restrictMonoidalTensorTrivialization_restrictOpen]
      rw [ih]

/-- The compatible standard-chart frame of the nonnegative power of `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModulePowerTrivialization
    (i j : σ) : ∀ n : ℕ,
      (coordinateHyperplaneIdealModulePower (R := R) j n).restrict
          (coordinateOpen (R := R) i).ι ≅
        Scheme.Modules.unitObj (coordinateOpen (R := R) i).toScheme :=
  coordinateHyperplaneIdealModulePowerTrivializationOf
    (coordinateOpen (R := R) i) j
      (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

/-- Every nonnegative power of the coordinate-hyperplane `O(-1)` is
invertible. -/
theorem coordinateHyperplaneIdealModulePower_isInvertible (j : σ) (n : ℕ) :
    Scheme.Modules.IsInvertible
      (coordinateHyperplaneIdealModulePower (R := R) j n) := by
  induction n with
  | zero =>
      exact Scheme.Modules.isInvertible_unit.of_iso
        (ModularCurves.monoidalUnitObjIso
          (Proj (homogeneousSubmodule σ R)))
  | succ n ih =>
      exact (ih.tensorObj
        (coordinateHyperplaneIdealModule_isInvertible (R := R) j)).of_iso
          (ModularCurves.monoidalTensorObjIso _ _)

/-- On a coordinate overlap, the two `O(-n)` frames differ by the `n`th power
of `X_k / X_i`, in the orientation of the `O(-1)` generator frames. -/
theorem coordinateHyperplaneIdealModulePowerTrivialization_restrict_transition
    (i k j : σ) (n : ℕ) :
    (Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenOverlap_le_right (R := R) i k)
        (coordinateHyperplaneIdealModulePowerTrivialization
          (R := R) k j n)).hom =
      (Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_left (R := R) i k)
          (coordinateHyperplaneIdealModulePowerTrivialization
            (R := R) i j n)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((Scheme.Modules.openTopSection
            (coordinateOpenOverlap (R := R) i k)
            (coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                coordinateOpenOverlap (R := R) i k))) ^ n) := by
  let U := coordinateOpenOverlap (R := R) i k
  let eI := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_left (R := R) i k)
    (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  let eK := Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenOverlap_le_right (R := R) i k)
    (coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  let r := Scheme.Modules.openTopSection U
    (coordinateOpenTransitionUnit (R := R) i k :
      Γ(Proj (homogeneousSubmodule σ R), U))
  have hbase : eK.hom = eI.hom ≫
      ModularCurves.unitEndomorphismOfTopSection r := by
    exact coordinateHyperplaneIdealModuleTrivialization_restrict_transition i k j
  have hpower := ModularCurves.recursiveTensorTrivialization_hom_eq_comp_scalar U
    (fun e n => coordinateHyperplaneIdealModulePowerTrivializationOf U j e n)
    (fun n => ModularCurves.restrictMonoidalTensorIso U.ι
      (coordinateHyperplaneIdealModulePower (R := R) j n)
      (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)))
    (fun _ _ => rfl) (fun _ _ => rfl) eK eI r hbase n
  have hI :
      Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_left (R := R) i k)
          (coordinateHyperplaneIdealModulePowerTrivialization
            (R := R) i j n) =
        coordinateHyperplaneIdealModulePowerTrivializationOf U j eI n := by
    exact coordinateHyperplaneIdealModulePowerTrivializationOf_restrictOpen
      (coordinateOpenOverlap_le_left (R := R) i k) j
        (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm n
  have hK :
      Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_right (R := R) i k)
          (coordinateHyperplaneIdealModulePowerTrivialization
            (R := R) k j n) =
        coordinateHyperplaneIdealModulePowerTrivializationOf U j eK n := by
    exact coordinateHyperplaneIdealModulePowerTrivializationOf_restrictOpen
      (coordinateOpenOverlap_le_right (R := R) i k) j
        (coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm n
  rw [hK, hI]
  exact hpower

/-- The integer twist `O(d)` on polynomial projective space, formed from the
concrete coordinate-hyperplane `O(1)` and `O(-1)`. -/
noncomputable def coordinateHyperplaneTwist (j : σ) :
    ℤ → (Proj (homogeneousSubmodule σ R)).Modules
  | .ofNat n => coordinateHyperplanePoleSheafPower (R := R) j n
  | .negSucc n => coordinateHyperplaneIdealModulePower (R := R) j (n + 1)

@[simp]
lemma coordinateHyperplaneTwist_ofNat (j : σ) (n : ℕ) :
    coordinateHyperplaneTwist (R := R) j (.ofNat n) =
      coordinateHyperplanePoleSheafPower (R := R) j n :=
  rfl

@[simp]
lemma coordinateHyperplaneTwist_negSucc (j : σ) (n : ℕ) :
    coordinateHyperplaneTwist (R := R) j (.negSucc n) =
      coordinateHyperplaneIdealModulePower (R := R) j (n + 1) :=
  rfl

/-- The standard-chart frame of the integer twist `O(d)`. -/
noncomputable def coordinateHyperplaneTwistTrivialization (i j : σ) :
    ∀ d : ℤ,
      (coordinateHyperplaneTwist (R := R) j d).restrict
          (coordinateOpen (R := R) i).ι ≅
        Scheme.Modules.unitObj (coordinateOpen (R := R) i).toScheme
  | .ofNat n => coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n
  | .negSucc n =>
      coordinateHyperplaneIdealModulePowerTrivialization i j (n + 1)

private lemma coordinateOpenTransitionTopUnit_zpow_ofNat_coe (i k : σ) (n : ℕ) :
    ((coordinateOpenTransitionTopUnit (R := R) i k ^ (.ofNat n : ℤ) :
        Γ((coordinateOpenOverlap (R := R) i k).toScheme,
          (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
      Γ((coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
      Scheme.Modules.openTopSection (coordinateOpenOverlap (R := R) i k)
        (coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R),
            coordinateOpenOverlap (R := R) i k)) ^ n := by
  change (((coordinateOpenTransitionTopUnit (R := R) i k) ^ n :
      Γ((coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
    Γ((coordinateOpenOverlap (R := R) i k).toScheme,
      (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))) = _
  rw [Units.val_pow_eq_pow_val]
  exact congrArg (fun q => q ^ n)
    (coordinateOpenTransitionTopUnit_coe (R := R) i k)

/-- On a coordinate overlap, the two standard frames of `O(d)` differ by the
integer power of `X_k / X_i`. -/
theorem coordinateHyperplaneTwistTrivialization_restrict_transition
    (i k j : σ) : ∀ d : ℤ,
    (Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenOverlap_le_left (R := R) i k)
        (coordinateHyperplaneTwistTrivialization (R := R) i j d)).hom =
      (Scheme.Modules.restrictOpenTrivialization
          (coordinateOpenOverlap_le_right (R := R) i k)
          (coordinateHyperplaneTwistTrivialization (R := R) k j d)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((coordinateOpenTransitionTopUnit (R := R) i k ^ d :
              Γ((coordinateOpenOverlap (R := R) i k).toScheme,
                (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
            Γ((coordinateOpenOverlap (R := R) i k).toScheme,
              (⊤ : (coordinateOpenOverlap (R := R) i k).toScheme.Opens))) := by
  intro d
  cases d with
  | ofNat n =>
      simpa only [coordinateHyperplaneTwistTrivialization,
        coordinateHyperplaneTwist_ofNat,
        coordinateOpenTransitionTopUnit_zpow_ofNat_coe] using
        coordinateHyperplanePoleSheafPowerTrivialization_restrict_transition
          (R := R) i k j n
  | negSucc n =>
      let U := coordinateOpenOverlap (R := R) i k
      let t := coordinateOpenTransitionTopUnit (R := R) i k
      let A := ModularCurves.unitAutomorphismOfTopUnit (t ^ (n + 1))
      have h := coordinateHyperplaneIdealModulePowerTrivialization_restrict_transition
        (R := R) i k j (n + 1)
      have htPow :
          ((t ^ (n + 1) : Γ(U.toScheme, (⊤ : U.toScheme.Opens))ˣ) :
              Γ(U.toScheme, (⊤ : U.toScheme.Opens))) =
            Scheme.Modules.openTopSection U
              (coordinateOpenTransitionUnit (R := R) i k :
                Γ(Proj (homogeneousSubmodule σ R), U)) ^ (n + 1) := by
        rw [Units.val_pow_eq_pow_val]
        exact congrArg (fun q => q ^ (n + 1))
          (coordinateOpenTransitionTopUnit_coe (R := R) i k)
      have hA :
          (Scheme.Modules.restrictOpenTrivialization
              (coordinateOpenOverlap_le_right (R := R) i k)
              (coordinateHyperplaneTwistTrivialization
                (R := R) k j (.negSucc n))).hom =
            (Scheme.Modules.restrictOpenTrivialization
                (coordinateOpenOverlap_le_left (R := R) i k)
                (coordinateHyperplaneTwistTrivialization
                  (R := R) i j (.negSucc n))).hom ≫ A.hom := by
        change _ = _ ≫ ModularCurves.unitEndomorphismOfTopSection
          ((t ^ (n + 1) : Γ(U.toScheme, (⊤ : U.toScheme.Opens))ˣ) :
            Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
        rw [htPow]
        exact h
      have hInv : A.inv =
          ModularCurves.unitEndomorphismOfTopSection
            ((coordinateOpenTransitionTopUnit (R := R) i k ^
                (.negSucc n : ℤ) :
              Γ(U.toScheme, (⊤ : U.toScheme.Opens))ˣ) :
                Γ(U.toScheme, (⊤ : U.toScheme.Opens))) := by
        simp only [A, t, ModularCurves.unitAutomorphismOfTopUnit_inv]
        rw [zpow_negSucc]
      rw [← hInv, hA]
      simp only [Category.assoc, A.hom_inv_id, Category.comp_id]

/-- Every integer twist `O(d)` is invertible. -/
theorem coordinateHyperplaneTwist_isInvertible (j : σ) (d : ℤ) :
    Scheme.Modules.IsInvertible (coordinateHyperplaneTwist (R := R) j d) := by
  cases d with
  | ofNat n => exact coordinateHyperplanePoleSheafPower_isInvertible j n
  | negSucc n => exact coordinateHyperplaneIdealModulePower_isInvertible j (n + 1)

end

end MvPolynomial
