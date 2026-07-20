/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveSpaceHyperplane
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

private lemma coordinateOpenOverlap_le_left (i k : σ) :
    coordinateOpenOverlap (R := R) i k ≤ coordinateOpen (R := R) i :=
  (coordinateOpenOverlap_eq (R := R) i k).trans_le inf_le_left

private lemma coordinateOpenOverlap_le_right (i k : σ) :
    coordinateOpenOverlap (R := R) i k ≤ coordinateOpen (R := R) k :=
  (coordinateOpenOverlap_eq (R := R) i k).trans_le inf_le_right

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

/-- The compatible standard-chart frame of the nonnegative twist `O(n)`. -/
noncomputable def coordinateHyperplanePoleSheafPowerTrivialization
    (i j : σ) : ∀ n : ℕ,
      (coordinateHyperplanePoleSheafPower (R := R) j n).restrict
          (coordinateOpen (R := R) i).ι ≅
        Scheme.Modules.unitObj (coordinateOpen (R := R) i).toScheme
  | 0 => ModularCurves.restrictMonoidalUnitIso
        (coordinateOpen (R := R) i).ι ≪≫
      ModularCurves.monoidalUnitObjIso (coordinateOpen (R := R) i).toScheme
  | n + 1 =>
      ModularCurves.restrictMonoidalTensorIso
          (coordinateOpen (R := R) i).ι
          (coordinateHyperplanePoleSheafPower (R := R) j n)
          (coordinateHyperplanePoleSheaf (R := R) j) ≪≫
        (coordinateHyperplanePoleSheafPowerTrivialization i j n ⊗ᵢ
          coordinateHyperplanePoleSheafTrivialization (R := R) i j) ≪≫
        ModularCurves.unitObjTensorIso (coordinateOpen (R := R) i).toScheme

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

/-- The compatible standard-chart frame of the nonnegative power of `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModulePowerTrivialization
    (i j : σ) : ∀ n : ℕ,
      (coordinateHyperplaneIdealModulePower (R := R) j n).restrict
          (coordinateOpen (R := R) i).ι ≅
        Scheme.Modules.unitObj (coordinateOpen (R := R) i).toScheme
  | 0 => ModularCurves.restrictMonoidalUnitIso
        (coordinateOpen (R := R) i).ι ≪≫
      ModularCurves.monoidalUnitObjIso (coordinateOpen (R := R) i).toScheme
  | n + 1 =>
      ModularCurves.restrictMonoidalTensorIso
          (coordinateOpen (R := R) i).ι
          (coordinateHyperplaneIdealModulePower (R := R) j n)
          (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) ≪≫
        (coordinateHyperplaneIdealModulePowerTrivialization i j n ⊗ᵢ
          (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm) ≪≫
        ModularCurves.unitObjTensorIso (coordinateOpen (R := R) i).toScheme

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

/-- Every integer twist `O(d)` is invertible. -/
theorem coordinateHyperplaneTwist_isInvertible (j : σ) (d : ℤ) :
    Scheme.Modules.IsInvertible (coordinateHyperplaneTwist (R := R) j d) := by
  cases d with
  | ofNat n => exact coordinateHyperplanePoleSheafPower_isInvertible j n
  | negSucc n => exact coordinateHyperplaneIdealModulePower_isInvertible j (n + 1)

end

end MvPolynomial
