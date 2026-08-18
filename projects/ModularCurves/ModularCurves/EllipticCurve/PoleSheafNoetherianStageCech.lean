/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafBaseCechHigher
import ModularCurves.EllipticCurve.PoleSheafIteratedBaseChange
import ModularCurves.ForMathlib.BaseChangeKerCoker
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechBaseChangeExact
import ModularCurves.Picard.InvertibleSheafProperCechResidueSpread

/-!
# Cech exactness for Noetherian-stage pole models

This file transfers fibrewise pole-sheaf exactness through an iterated base
change and reflects it from a field-valued point to its kernel residue field.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

/-- Relative-dimension-one smoothness of a base-changed family persists under any further
base change, expressed on the direct pullback. -/
theorem smoothOfRelativeDimension_pullback_snd_comp
    {Y S T U : Scheme.{u}} (π : Y ⟶ S) (t : T ⟶ S) (u : U ⟶ T)
    (hsm : SmoothOfRelativeDimension 1 (pullback.snd π t)) :
    SmoothOfRelativeDimension 1 (pullback.snd π (u ≫ t)) := by
  letI : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension 1) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd π t u,
    MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1)]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback (pullback.snd π t) u) hsm

/-- Fibrewise ellipticity of a base-changed family persists under any further base
change, expressed on the direct pullback with the transported section. -/
theorem fibrewiseElliptic_pullback_snd_comp
    {Y S T U : Scheme.{u}} (π : Y ⟶ S) (t : T ⟶ S)
    (zT : T ⟶ pullback π t)
    (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (hT : FibrewiseElliptic (pullback.snd π t) zT hzT)
    (u : U ⟶ T) :
    FibrewiseElliptic (pullback.snd π (u ≫ t))
      (sectionIteratedBaseChangeDirect π t zT hzT u)
      (sectionIteratedBaseChangeDirect_snd π t zT hzT u) := by
  exact (hT.baseChange u).of_iso_over
    (pullbackLeftPullbackSndIso π t u).symm
    (pullbackLeftPullbackSndIso_inv_snd_snd π t u)
    (sectionIteratedBaseChangeDirect_assoc_inv π t zT hzT u)

/-- A pole-sheaf model after one base change makes the stage ordered Cech
differentials exact after any further field-valued base change. -/
theorem FibrewiseElliptic.orderedBaseCech_baseChange_exact_of_poleSheafModel
    {Y S T U : Scheme.{u}} {π : Y ⟶ S} [IsProper π]
    [IsAffine S] [IsAffine U]
    (t : T ⟶ S) (zT : T ⟶ pullback π t)
    (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (hsmT : SmoothOfRelativeDimension 1 (pullback.snd π t))
    (hT : FibrewiseElliptic (pullback.snd π t) zT hzT)
    (M : Y.Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅
      sectionPoleSheafPower (pullback.snd π t) zT hzT 1)
    (u : U ⟶ T) (hField : IsField Γ(U, (⊤ : U.Opens)))
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (V : ι → Y.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i)) (q : ℕ) :
    let C := Scheme.Modules.orderedBaseCechComplex π M V
    let K := Γ(U, (⊤ : U.Opens))
    letI : Algebra Γ(S, (⊤ : S.Opens)) K :=
      (u ≫ t).appTop.hom.toAlgebra
    Function.Exact
      ((C.d q (q + 1)).hom.baseChange K)
      ((C.d (q + 1) (q + 2)).hom.baseChange K) := by
  dsimp only
  letI : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  let πD := pullback.snd π (u ≫ t)
  let zD := sectionIteratedBaseChangeDirect π t zT hzT u
  let hzD := sectionIteratedBaseChangeDirect_snd π t zT hzT u
  have hsmD : SmoothOfRelativeDimension 1 πD :=
    smoothOfRelativeDimension_pullback_snd_comp π t u hsmT
  have hD : FibrewiseElliptic πD zD hzD :=
    fibrewiseElliptic_pullback_snd_comp π t zT hzT hT u
  let VD : ι → (pullback π (u ≫ t)).Opens :=
    fun i ↦ pullback.fst π (u ≫ t) ⁻¹ᵁ V i
  have hVD : IsOpenCover VD :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst π (u ≫ t)) hV
  have hVDaff : ∀ i, IsAffineOpen (VD i) := by
    intro i
    exact IsAffineOpen.preimage_pullback_fst π (u ≫ t) (hVaff i)
  let P := sectionPoleSheafPower πD zD hzD 1
  let eD : (Scheme.Modules.pullback
      (pullback.fst π (u ≫ t))).obj M ≅ P :=
    sectionPoleSheafPowerDirectBaseChangeIso t zT hzT hsmT M e u
  have hExactD :
      let D := Scheme.Modules.orderedBaseCechComplex πD P VD
      Function.Exact (D.d q (q + 1)).hom
        (D.d (q + 1) (q + 2)).hom := by
    exact
      hD.sectionPoleSheafPower_orderedBaseCech_differential_exact_of_isField
        hField hsmD zD hzD VD hVD hVDaff (n := 1) (by omega) q
  exact
    (Scheme.Modules.orderedBaseCechComplex_baseChange_exact_iff_of_iso
      π (u ≫ t) M V hVaff P eD q).mpr hExactD

/-- The field-valued exactness supplied by a pole-sheaf model descends to the
residue field of the kernel prime on the stage base. -/
theorem FibrewiseElliptic.orderedBaseCech_residueField_exact_of_poleSheafModel
    {Y S T U : Scheme.{u}} {π : Y ⟶ S} [IsProper π]
    [IsAffine S] [IsAffine U]
    (t : T ⟶ S) (zT : T ⟶ pullback π t)
    (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (hsmT : SmoothOfRelativeDimension 1 (pullback.snd π t))
    (hT : FibrewiseElliptic (pullback.snd π t) zT hzT)
    (M : Y.Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅
      sectionPoleSheafPower (pullback.snd π t) zT hzT 1)
    (u : U ⟶ T) (hField : IsField Γ(U, (⊤ : U.Opens)))
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (V : ι → Y.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i)) (q : ℕ) :
    let B := Γ(S, (⊤ : S.Opens))
    let K := Γ(U, (⊤ : U.Opens))
    letI : Field K := hField.toField
    let p : Ideal B := RingHom.ker (u ≫ t).appTop.hom
    letI : p.IsPrime := RingHom.ker_isPrime (u ≫ t).appTop.hom
    let C := Scheme.Modules.orderedBaseCechComplex π M V
    Function.Exact
      ((C.d q (q + 1)).hom.baseChange p.ResidueField)
      ((C.d (q + 1) (q + 2)).hom.baseChange p.ResidueField) := by
  dsimp only
  let B := Γ(S, (⊤ : S.Opens))
  let K := Γ(U, (⊤ : U.Opens))
  letI : Field K := hField.toField
  letI : Algebra B K := (u ≫ t).appTop.hom.toAlgebra
  let p : Ideal B := RingHom.ker (u ≫ t).appTop.hom
  letI hp : p.IsPrime := RingHom.ker_isPrime (u ≫ t).appTop.hom
  have hp_le : p ≤ RingHom.ker (u ≫ t).appTop.hom := le_rfl
  have hp_unit : p.primeCompl ≤
      (IsUnit.submonoid K).comap (u ≫ t).appTop.hom := by
    intro r hr
    apply isUnit_iff_ne_zero.mpr
    intro hr_zero
    exact hr hr_zero
  let φ : p.ResidueField →+* K :=
    Ideal.ResidueField.lift p (u ≫ t).appTop.hom hp_le hp_unit
  letI : Algebra p.ResidueField K := φ.toAlgebra
  letI : IsScalarTower B p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      exact (Ideal.ResidueField.lift_algebraMap
        p (u ≫ t).appTop.hom hp_le hp_unit r).symm
  have hK :
      let C := Scheme.Modules.orderedBaseCechComplex π M V
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange K)
        ((C.d (q + 1) (q + 2)).hom.baseChange K) :=
    hT.orderedBaseCech_baseChange_exact_of_poleSheafModel
      t zT hzT hsmT M e u hField V hV hVaff q
  let C := Scheme.Modules.orderedBaseCechComplex π M V
  exact (LinearMap.baseChange_exact_iff_of_faithfullyFlat
    p.ResidueField K (C.d q (q + 1)).hom
      (C.d (q + 1) (q + 2)).hom).mpr hK

/-- Exactness at a field-valued point of a Noetherian-stage pole model spreads
to a principal neighborhood of the corresponding kernel prime. -/
theorem FibrewiseElliptic.exists_away_orderedBaseCech_exact_of_poleSheafModel
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Y T U : Scheme.{u}} {π : Y ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (t : T ⟶ Spec (.of R)) (zT : T ⟶ pullback π t)
    (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (hsmT : SmoothOfRelativeDimension 1 (pullback.snd π t))
    (hT : FibrewiseElliptic (pullback.snd π t) zT hzT)
    (e : (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅
      sectionPoleSheafPower (pullback.snd π t) zT hzT 1)
    (u : U ⟶ T) [IsAffine U]
    (hField : IsField Γ(U, (⊤ : U.Opens)))
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (V : ι → Y.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i)) :
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let p : Ideal B := RingHom.ker (u ≫ t).appTop.hom
    ∃ r : B, r ∉ p ∧
      let C := Scheme.Modules.orderedBaseCechComplex π M V
      ∀ q, q < Fintype.card ι →
        Function.Exact
          ((C.d q (q + 1)).hom.baseChange (Localization.Away r))
          ((C.d (q + 1) (q + 2)).hom.baseChange
            (Localization.Away r)) := by
  dsimp only
  letI : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : CompactSpace Y :=
    (quasiCompact_iff_compactSpace π).mp inferInstance
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsNoetherian Y := { }
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let K := Γ(U, (⊤ : U.Opens))
  letI : Field K := hField.toField
  let p : Ideal B := RingHom.ker (u ≫ t).appTop.hom
  letI hp : p.IsPrime := RingHom.ker_isPrime (u ≫ t).appTop.hom
  apply hM.exists_away_orderedBaseCech_exact_of_residueField_exact
    V hV hVaff p
  intro q _
  exact hT.orderedBaseCech_residueField_exact_of_poleSheafModel
    t zT hzT hsmT M e u hField V hV hVaff q

end ModularCurves
