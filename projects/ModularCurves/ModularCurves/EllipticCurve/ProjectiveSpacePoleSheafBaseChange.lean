/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.IdealModuleSquareBaseChange
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.ForMathlib.ProjectiveSpaceCoefficientBaseChange
import ModularCurves.ForMathlib.SchemeModuleOpenCoverIso
import ModularCurves.Picard.DualPullback.Iso

/-!
# Base change for the coordinate hyperplane pole sheaf

This file proves that coefficient extension preserves the coordinate hyperplane
and its associated ideal and pole modules.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open HomogeneousIdeal HomogeneousLocalization

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance projectiveSpacePoleSheafBaseChangeMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance (priority := 10000) {n : ℕ} : DecidableEq (Fin n) :=
  Classical.decEq _

private lemma coordinateHyperplaneIdeal_le_comap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    (coordinateHyperplaneIdeal (R := k) j).toIdeal ≤
      (coordinateHyperplaneIdeal (R := R) j).toIdeal.comap
        (coefficientGradedHom φ d) := by
  rw [← Ideal.map_le_iff_le_comap, coordinateHyperplaneIdeal_toIdeal,
    coordinateHyperplaneIdeal_toIdeal, Ideal.map_span, Set.image_singleton,
    coefficientGradedHom_X]

private noncomputable def coordinateHyperplaneQuotientGradedHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    quotientGrading (coordinateHyperplaneIdeal (R := k) j) →+*ᵍ
      quotientGrading (coordinateHyperplaneIdeal (R := R) j) :=
  quotientGradingMap (coefficientGradedHom φ d)
    (coordinateHyperplaneIdeal (R := k) j)
    (coordinateHyperplaneIdeal (R := R) j)
    (coordinateHyperplaneIdeal_le_comap φ d j)

private lemma coordinateHyperplaneQuotientIrrelevantLE
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    (quotientGrading (coordinateHyperplaneIdeal (R := R) j))₊ ≤
      (quotientGrading (coordinateHyperplaneIdeal (R := k) j))₊.map
        (coordinateHyperplaneQuotientGradedHom φ d j) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn p hp
  obtain ⟨a, ha, rfl⟩ := hp
  have haIrrelevant :
      a ∈ (homogeneousSubmodule (Fin (d + 1)) R)₊.toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Fin (d + 1)) R) hn ha
  have haSpan :
      a ∈ Ideal.span
        (Set.range
          (X : Fin (d + 1) → MvPolynomial (Fin (d + 1)) R)) :=
    irrelevant_toIdeal_le_span_range_X haIrrelevant
  change a ∈
    ((quotientGrading (coordinateHyperplaneIdeal (R := k) j))₊.map
      (coordinateHyperplaneQuotientGradedHom φ d j)).comap
        (quotientGradingHom (coordinateHyperplaneIdeal (R := R) j))
  refine (Ideal.span_le.2 ?_) haSpan
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [← coefficientGradedHom_X φ i]
  change
    (quotientGradingHom (coordinateHyperplaneIdeal (R := R) j))
        ((coefficientGradedHom φ d) (X i)) ∈
      (quotientGrading (coordinateHyperplaneIdeal (R := k) j))₊.map
        (coordinateHyperplaneQuotientGradedHom φ d j)
  rw [quotientGradingHom_apply, ← quotientGradingMap_mk]
  exact Ideal.mem_map_of_mem
    (coordinateHyperplaneQuotientGradedHom φ d j)
    (HomogeneousIdeal.mem_irrelevant_of_mem
      (quotientGrading (coordinateHyperplaneIdeal (R := k) j))
      Nat.zero_lt_one
      (mk_mem_quotientGrading
        (coordinateHyperplaneIdeal (R := k) j)
        (X_mem_homogeneousSubmodule_one k i)))

/-- Coefficient extension on a coordinate hyperplane. -/
def coordinateHyperplaneCoefficientMap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    coordinateHyperplane (R := R) j ⟶
      coordinateHyperplane (R := k) j :=
  Proj.map (coordinateHyperplaneQuotientGradedHom φ d j)
    (coordinateHyperplaneQuotientIrrelevantLE φ d j)

private lemma coordinateHyperplaneQuotientGradedHom_comp
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    (coordinateHyperplaneQuotientGradedHom φ d j).comp
        (quotientGradingHom
          (coordinateHyperplaneIdeal (R := k) j)) =
      (quotientGradingHom
        (coordinateHyperplaneIdeal (R := R) j)).comp
          (coefficientGradedHom φ d) := by
  ext a
  exact quotientGradingMap_mk
    (coefficientGradedHom φ d)
    (coordinateHyperplaneIdeal (R := k) j)
    (coordinateHyperplaneIdeal (R := R) j)
    (coordinateHyperplaneIdeal_le_comap φ d j) a

/-- The coordinate-hyperplane embedding commutes with coefficient extension. -/
theorem coordinateHyperplaneι_comp_coefficientMap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    coordinateHyperplaneι (R := R) j ≫ coefficientMap φ d =
      coordinateHyperplaneCoefficientMap φ d j ≫
        coordinateHyperplaneι (R := k) j := by
  unfold coordinateHyperplaneι coefficientMap
    coordinateHyperplaneCoefficientMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [coordinateHyperplaneQuotientGradedHom_comp]

private lemma coordinateAwayToSection_presheaf_awayCongr
    {R : Type u} [CommRing R] {d : ℕ}
    {s t : MvPolynomial (Fin (d + 1)) R} (h : s = t)
    (z : Away (homogeneousSubmodule (Fin (d + 1)) R) s) :
    ((Proj (homogeneousSubmodule (Fin (d + 1)) R)).presheaf.map
      (eqToHom
        (show
          Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) R) t =
            Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) R) s by
          rw [h])).op).hom
        ((Proj.awayToSection
          (homogeneousSubmodule (Fin (d + 1)) R) s).hom z) =
      (Proj.awayToSection
        (homogeneousSubmodule (Fin (d + 1)) R) t).hom
          (ModularCurves.awayCongr h z) := by
  subst h
  simp [ModularCurves.awayCongr_rfl]

private lemma coefficientChartRingHom_isLocalizationElem
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (i j : Fin (d + 1)) :
    coefficientChartRingHom φ i
        (Away.isLocalizationElem
          (X_mem_homogeneousSubmodule_one k i)
          (X_mem_homogeneousSubmodule_one k j)) =
      Away.isLocalizationElem
        (X_mem_homogeneousSubmodule_one R i)
        (X_mem_homogeneousSubmodule_one R j) := by
  change
    (ModularCurves.awayCongr
      (MvPolynomial.map_X φ i)).toRingHom
        ((Away.map (coefficientGradedHom φ d) (X i))
          (Away.mk (homogeneousSubmodule (Fin (d + 1)) k)
            _ 1 (X j ^ 1) _)) =
      Away.mk (homogeneousSubmodule (Fin (d + 1)) R)
        _ 1 (X j ^ 1) _
  rw [Away.map_mk]
  simp only [map_pow, coefficientGradedHom_X]
  change
    ModularCurves.awayCongr (MvPolynomial.map_X φ i)
        (Away.mk (homogeneousSubmodule (Fin (d + 1)) R)
          _ 1 (X j ^ 1) _) = _
  rw [ModularCurves.awayCongr_mk]

private lemma coefficientAwayMap_isLocalizationElem
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (i j : Fin (d + 1)) :
    let hX := coefficientGradedHom_X φ i
    (Away.map (coefficientGradedHom φ d) (X i))
        (Away.isLocalizationElem
          (X_mem_homogeneousSubmodule_one k i)
          (X_mem_homogeneousSubmodule_one k j)) =
      ModularCurves.awayCongr hX.symm
        (Away.isLocalizationElem
          (X_mem_homogeneousSubmodule_one R i)
          (X_mem_homogeneousSubmodule_one R j)) := by
  dsimp only
  apply (ModularCurves.awayCongr
    (coefficientGradedHom_X φ i)).injective
  change
    coefficientChartRingHom φ i
        (Away.isLocalizationElem
          (X_mem_homogeneousSubmodule_one k i)
          (X_mem_homogeneousSubmodule_one k j)) = _
  rw [coefficientChartRingHom_isLocalizationElem,
    ModularCurves.awayCongr_trans, ModularCurves.awayCongr_self]

/-- On standard projective charts, coefficient extension sends the coordinate
hyperplane's local equation to the corresponding local equation. -/
theorem coefficientMap_appLE_coordinateHyperplaneLocalEquation
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (i j : Fin (d + 1)) :
    ((coefficientMap φ d).appLE
      (coordinateOpen (R := k) i) (coordinateOpen (R := R) i)
        (coefficientMap_preimage_coordinateOpen φ d i).ge).hom
          (coordinateHyperplaneLocalEquation (R := k) i j) =
      coordinateHyperplaneLocalEquation (R := R) i j := by
  rw [coordinateHyperplaneLocalEquation_eq_isLocalizationElem,
    coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  let F := coefficientGradedHom φ d
  let hf := coefficientIrrelevantLE φ d
  let q := Proj.map F hf
  let U :=
    Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) k) (X i)
  let V :=
    Proj.basicOpen
      (homogeneousSubmodule (Fin (d + 1)) R) (F (X i))
  let V' :=
    Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) R) (X i)
  let w := Away.isLocalizationElem
    (X_mem_homogeneousSubmodule_one k i)
    (X_mem_homogeneousSubmodule_one k j)
  let z := Away.isLocalizationElem
    (X_mem_homogeneousSubmodule_one R i)
    (X_mem_homogeneousSubmodule_one R j)
  have hX : F (X i) = X i :=
    coefficientGradedHom_X φ i
  have hOpen : V = V' :=
    congrArg
      (Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) R)) hX
  let transport :=
    (Proj (homogeneousSubmodule (Fin (d + 1)) R)).presheaf.map
      (eqToHom hOpen).op
  haveI : IsIso transport := by
    dsimp only [transport]
    infer_instance
  apply ((ConcreteCategory.isIso_iff_bijective transport).mp
    (inferInstance : IsIso transport)).1
  have happ := q.appLE_map'
    (U := U) (V := V) (V' := V') (by rfl) hOpen
  have happApply := ConcreteCategory.congr_hom happ
    ((Proj.awayToSection
      (homogeneousSubmodule (Fin (d + 1)) k) (X i)).hom w)
  have hcomp := Proj.awayToSection_comp_appLE F hf
    (X_mem_homogeneousSubmodule_one k i)
  have hel := ConcreteCategory.congr_hom hcomp w
  simp only [CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at hel
  change
    transport.hom
        ((q.appLE U V' _).hom
          ((Proj.awayToSection
            (homogeneousSubmodule (Fin (d + 1)) k) (X i)).hom w)) =
      transport.hom
        ((Proj.awayToSection
          (homogeneousSubmodule (Fin (d + 1)) R) (X i)).hom z)
  calc
    _ = (q.appLE U V (by rfl)).hom
        ((Proj.awayToSection
          (homogeneousSubmodule (Fin (d + 1)) k) (X i)).hom w) :=
      happApply
    _ = (Proj.awayToSection
          (homogeneousSubmodule (Fin (d + 1)) R) (F (X i))).hom
        ((Away.map F (X i)) w) := hel
    _ = (Proj.awayToSection
          (homogeneousSubmodule (Fin (d + 1)) R) (F (X i))).hom
        (ModularCurves.awayCongr hX.symm z) := by
      rw [coefficientAwayMap_isLocalizationElem]
    _ = _ :=
      (coordinateAwayToSection_presheaf_awayCongr hX.symm z).symm

/-- The affine-chart pullback of a coordinate-hyperplane local equation is
the corresponding local equation after coefficient extension. -/
theorem affinePullbackSection_coordinateHyperplaneLocalEquation
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (i j : Fin (d + 1)) :
    let U :
        (Proj (homogeneousSubmodule (Fin (d + 1)) R)).affineOpens :=
      ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
    let V :
        (Proj (homogeneousSubmodule (Fin (d + 1)) k)).affineOpens :=
      ⟨coordinateOpen (R := k) i, coordinateOpen_isAffineOpen i⟩
    ModularCurves.affinePullbackSection
        (coefficientMap φ d) U V
        (coefficientMap_preimage_coordinateOpen φ d i).ge
        (coordinateHyperplaneLocalEquation (R := k) i j) =
      coordinateHyperplaneLocalEquation (R := R) i j := by
  dsimp only
  rw [ModularCurves.affinePullbackSection_eq_appLE]
  exact coefficientMap_appLE_coordinateHyperplaneLocalEquation φ d i j

/-- The canonical comparison from the pullback of a coordinate-hyperplane
ideal module to the corresponding ideal module after coefficient extension. -/
noncomputable def coordinateHyperplaneIdealModuleBaseChangeHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    (Scheme.Modules.pullback (coefficientMap φ d)).obj
        (ModularCurves.idealModule
          (coordinateHyperplaneι (R := k) j)) ⟶
      ModularCurves.idealModule
        (coordinateHyperplaneι (R := R) j) :=
  ModularCurves.idealModuleSquareBaseChangeHom
    (coordinateHyperplaneι (R := k) j)
    (coordinateHyperplaneι (R := R) j)
    (coefficientMap φ d)
    (coordinateHyperplaneCoefficientMap φ d j)
    (coordinateHyperplaneι_comp_coefficientMap φ d j)

/-- The coordinate-hyperplane ideal-module comparison is an isomorphism. -/
theorem coordinateHyperplaneIdealModuleBaseChangeHom_isIso
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    IsIso (coordinateHyperplaneIdealModuleBaseChangeHom φ d j) := by
  let f := coordinateHyperplaneι (R := k) j
  let f' := coordinateHyperplaneι (R := R) j
  let g := coefficientMap φ d
  let t := coordinateHyperplaneCoefficientMap φ d j
  let h := coordinateHyperplaneι_comp_coefficientMap φ d j
  let α := coordinateHyperplaneIdealModuleBaseChangeHom φ d j
  letI : IsClosedImmersion f :=
    coordinateHyperplaneι_isClosedImmersion j
  letI : IsClosedImmersion f' :=
    coordinateHyperplaneι_isClosedImmersion j
  letI (i : Fin (d + 1)) :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (coordinateOpen (R := R) i).ι).map α) := by
    let U :
        (Proj (homogeneousSubmodule (Fin (d + 1)) R)).affineOpens :=
      ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
    let V :
        (Proj (homogeneousSubmodule (Fin (d + 1)) k)).affineOpens :=
      ⟨coordinateOpen (R := k) i, coordinateOpen_isAffineOpen i⟩
    let r := coordinateHyperplaneLocalEquation (R := k) i j
    have hr : r ∈ f.ker.ideal V := by
      rw [coordinateHyperplaneLocalEquation_span]
      exact Ideal.mem_span_singleton_self r
    have hspan : f.ker.ideal V = Ideal.span {r} :=
      coordinateHyperplaneLocalEquation_span i j
    have hnzd :
        r ∈ nonZeroDivisors
          Γ(Proj (homogeneousSubmodule (Fin (d + 1)) k), V.1) :=
      coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j
    have hspan' :
        f'.ker.ideal U =
          Ideal.span
            {ModularCurves.affinePullbackSection g U V
              (coefficientMap_preimage_coordinateOpen φ d i).ge r} := by
      rw [affinePullbackSection_coordinateHyperplaneLocalEquation]
      exact coordinateHyperplaneLocalEquation_span i j
    have hnzd' :
        ModularCurves.affinePullbackSection g U V
            (coefficientMap_preimage_coordinateOpen φ d i).ge r ∈
          nonZeroDivisors
            Γ(Proj (homogeneousSubmodule (Fin (d + 1)) R), U.1) := by
      rw [affinePullbackSection_coordinateHyperplaneLocalEquation]
      exact coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j
    haveI hpull :
        IsIso ((Scheme.Modules.pullback U.1.ι).map α) := by
      dsimp only [α, coordinateHyperplaneIdealModuleBaseChangeHom]
      exact
        ModularCurves.idealModuleSquareBaseChangeHom_isIso_on_affine
          f f' g t h U V
          (coefficientMap_preimage_coordinateOpen φ d i).ge
          r hr hspan hnzd hspan' hnzd'
    let e := Scheme.Modules.restrictFunctorIsoPullback U.1.ι
    let N :=
      ModularCurves.idealModule
        (coordinateHyperplaneι (R := R) j)
    haveI hcomp :
        IsIso
          ((Scheme.Modules.restrictFunctor U.1.ι).map α ≫
            e.hom.app N) := by
      dsimp only [N]
      rw [e.hom.naturality α]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (e.hom.app N)
  apply Scheme.Modules.isIso_of_isIso_restrict_openCover α
    (fun i : Fin (d + 1) => coordinateOpen (R := R) i)
  intro x
  let C := coordinateAffineOpenCover R (Fin (d + 1))
  refine ⟨C.idx x, ?_⟩
  have hx : x ∈ (C.f (C.idx x)).opensRange :=
    Scheme.Hom.mem_opensRange.mpr (C.covers x)
  change
    x ∈
      (coordinateChartMap R (Fin (d + 1)) (C.idx x)).opensRange at hx
  rwa [coordinateAffineOpenCover_opensRange] at hx

/-- Pullback of the coordinate-hyperplane ideal module along coefficient
extension. -/
noncomputable def coordinateHyperplaneIdealModuleBaseChangeIso
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    (Scheme.Modules.pullback (coefficientMap φ d)).obj
        (ModularCurves.idealModule
          (coordinateHyperplaneι (R := k) j)) ≅
      ModularCurves.idealModule
        (coordinateHyperplaneι (R := R) j) := by
  letI :=
    coordinateHyperplaneIdealModuleBaseChangeHom_isIso φ d j
  exact asIso (coordinateHyperplaneIdealModuleBaseChangeHom φ d j)

/-- Pullback of the coordinate-hyperplane pole sheaf along coefficient
extension. -/
noncomputable def coordinateHyperplanePoleSheafBaseChangeIso
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    (Scheme.Modules.pullback (coefficientMap φ d)).obj
        (coordinateHyperplanePoleSheaf (R := k) j) ≅
      coordinateHyperplanePoleSheaf (R := R) j :=
  Scheme.Modules.dualPullbackIsoOfIsInvertible
      (coefficientMap φ d)
      (ModularCurves.idealModule
        (coordinateHyperplaneι (R := k) j))
      (coordinateHyperplaneIdealModule_isInvertible (R := k) j) ≪≫
    (Scheme.Modules.dualIsoObj
      (coordinateHyperplaneIdealModuleBaseChangeIso φ d j)).symm

/-- Pullback of every nonnegative coordinate-hyperplane pole-sheaf power
along coefficient extension. -/
noncomputable def coordinateHyperplanePoleSheafPowerBaseChangeIso
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (j : Fin (d + 1)) :
    ∀ n : ℕ,
      (Scheme.Modules.pullback (coefficientMap φ d)).obj
          (coordinateHyperplanePoleSheafPower (R := k) j n) ≅
        coordinateHyperplanePoleSheafPower (R := R) j n
  | 0 => by
      letI : (Scheme.Modules.pullback (coefficientMap φ d)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (coefficientMap φ d)
      exact
        (Functor.Monoidal.εIso
          (Scheme.Modules.pullback (coefficientMap φ d))).symm
  | n + 1 => by
      letI : (Scheme.Modules.pullback (coefficientMap φ d)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (coefficientMap φ d)
      exact
        (Functor.Monoidal.μIso
          (Scheme.Modules.pullback (coefficientMap φ d))
          (coordinateHyperplanePoleSheafPower (R := k) j n)
          (coordinateHyperplanePoleSheaf (R := k) j)).symm ≪≫
            (coordinateHyperplanePoleSheafPowerBaseChangeIso φ d j n ⊗ᵢ
              coordinateHyperplanePoleSheafBaseChangeIso φ d j)

end MvPolynomial
