/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.ProblemBaseChange
import Mathlib.CategoryTheory.Whiskering
import ModularCurves.Moduli.EngineWiring

/-!
# Base change along an isomorphism of base rings

**[T-YR-6-APP (i)]** When `ρ : R ⟶ R'` is an isomorphism, restriction of scalars
`EllObj R' ⥤ EllObj R` is fully faithful and essentially surjective, so
representability of `P.baseChange ρ` transports back to representability of `P` —
with the *same* base scheme. This is what lets the engine's affine `D(3)`-leg over
`ℚ[1/3]` produce an affine representing object for a problem over `ℚ`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace ModularCurves

variable {R R' : CommRingCat.{u}} (ρ : R ⟶ R') [IsIso ρ]

/-- Restriction of scalars along an isomorphism is full: the base-compatibility
square can be cancelled. -/
instance EllObj.restrictScalars_full : (EllObj.restrictScalars ρ).Full where
  map_surjective {X Y} f := by
    refine ⟨⟨f.baseHom, ?_, f.top, f.isPullback, f.zero_w⟩, rfl⟩
    have h := f.base_w
    simp only [EllObj.restrictScalars_obj_structMap, ← Category.assoc] at h
    exact (cancel_mono (Spec.map ρ)).mp h

/-- The `R'`-object underlying an `R`-object, when the base ring map is invertible. -/
@[simps] def EllObj.unrestrict (W : EllObj R) : EllObj R' where
  base := W.base
  structMap := W.structMap ≫ inv (Spec.map ρ)
  curve := W.curve

/-- Restricting an unrestricted object returns it. -/
@[simps] def EllObj.restrictScalarsUnrestrictIso (W : EllObj R) :
    (EllObj.restrictScalars ρ).obj (EllObj.unrestrict ρ W) ≅ W where
  hom :=
    { baseHom := 𝟙 _
      base_w := by
        show 𝟙 _ ≫ W.structMap = W.structMap ≫ inv (Spec.map ρ) ≫ Spec.map ρ
        simp
      top := 𝟙 _
      isPullback := EllHom.isPullback (𝟙 W)
      zero_w := EllHom.zero_w (𝟙 W) }
  inv :=
    { baseHom := 𝟙 _
      base_w := by
        show 𝟙 _ ≫ W.structMap ≫ inv (Spec.map ρ) ≫ Spec.map ρ = W.structMap
        simp
      top := 𝟙 _
      isPullback := EllHom.isPullback (𝟙 W)
      zero_w := EllHom.zero_w (𝟙 W) }
  hom_inv_id := EllHom.ext (Category.comp_id _) (Category.comp_id _)
  inv_hom_id := EllHom.ext (Category.comp_id _) (Category.comp_id _)

/-- Restriction of scalars along an isomorphism is essentially surjective. -/
instance EllObj.restrictScalars_essSurj : (EllObj.restrictScalars ρ).EssSurj where
  mem_essImage W := ⟨EllObj.unrestrict ρ W, ⟨EllObj.restrictScalarsUnrestrictIso ρ W⟩⟩

instance EllObj.restrictScalars_isEquivalence :
    (EllObj.restrictScalars ρ).IsEquivalence where

/-- **[T-YR-6-APP (i)]** Representability transports back along base change by a ring
isomorphism, keeping the representing object's base scheme: if `X₀` represents
`P.baseChange ρ`, then its restriction of scalars represents `P`. -/
noncomputable def ModuliProblem.representableByRestrictScalars {P : ModuliProblem R}
    {X₀ : EllObj R'} (r : (P.baseChange ρ).RepresentableBy X₀) :
    P.RepresentableBy ((EllObj.restrictScalars ρ).obj X₀) := by
  letI e : EllObj R' ≌ EllObj R := (EllObj.restrictScalars ρ).asEquivalence
  letI adj : e.inverse ⊣ e.functor := e.symm.toAdjunction
  have hiso : yoneda.obj X₀ ≅ (P.baseChange ρ) := r.toIso
  refine (Adjunction.representableBy adj X₀).ofIso ?_
  calc e.inverse.op ⋙ yoneda.obj X₀
      ≅ e.inverse.op ⋙ (P.baseChange ρ) := Functor.isoWhiskerLeft _ hiso
    _ = (e.inverse ⋙ e.functor).op ⋙ P := rfl
    _ ≅ (𝟭 (EllObj R)).op ⋙ P :=
        Functor.isoWhiskerRight (NatIso.op e.counitIso).symm P
    _ ≅ P := P.leftUnitor

/-- **[T-YR-6-APP (i)]** If base change along an isomorphism of base rings is
representable by an object with affine base, then so is the original problem. -/
theorem ModuliProblem.exists_representableBy_isAffine_of_isIso {P : ModuliProblem R}
    (h : ∃ X₀ : EllObj R', IsAffine X₀.base ∧
      Nonempty ((P.baseChange ρ).RepresentableBy X₀)) :
    ∃ Y : EllObj R, IsAffine Y.base ∧ Nonempty (P.RepresentableBy Y) := by
  obtain ⟨X₀, hX₀, ⟨r⟩⟩ := h
  exact ⟨(EllObj.restrictScalars ρ).obj X₀, hX₀,
    ⟨ModuliProblem.representableByRestrictScalars ρ r⟩⟩

/-- **[T-YR-6-APP (i)]** Any representing object of a problem with an affine
representative has affine base. -/
theorem ModuliProblem.isAffine_base_of_representableBy {P : ModuliProblem R}
    (h : ∃ Y : EllObj R, IsAffine Y.base ∧ Nonempty (P.RepresentableBy Y))
    {X : EllObj R} (r : P.RepresentableBy X) : IsAffine X.base := by
  obtain ⟨Y, hY, ⟨rY⟩⟩ := h
  haveI := hY
  let e : X ≅ Y := r.uniqueUpToIso rY
  haveI : IsIso e.hom.baseHom := ⟨e.inv.baseHom,
    congrArg EllHom.baseHom e.hom_inv_id, congrArg EllHom.baseHom e.inv_hom_id⟩
  exact IsAffine.of_isIso e.hom.baseHom

section AwayWire

open ModularCurves.ModuliProblem in

/-- Localizing away from a unit is an isomorphism of rings. -/
theorem isIso_awayHomWire_of_isUnit (R : CommRingCat.{u}) (a : R) (ha : IsUnit a) :
    IsIso (ModuliProblem.awayHomWire R a) := by
  have hle : Submonoid.powers a ≤ IsUnit.submonoid R := by
    rintro _ ⟨n, rfl⟩
    exact (IsUnit.mem_submonoid_iff _).mpr (ha.pow n)
  have hbij : Function.Bijective (algebraMap R (Localization.Away a)) :=
    (IsLocalization.atUnits R (Submonoid.powers a) hle).bijective
  exact (ConcreteCategory.isIso_iff_bijective
    (ModuliProblem.awayHomWire R a)).mpr hbij

end AwayWire

end ModularCurves

end
