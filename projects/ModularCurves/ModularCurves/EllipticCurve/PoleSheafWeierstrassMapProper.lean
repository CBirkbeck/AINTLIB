import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlue

/-!
# Properness of the pole-sheaf Weierstrass comparison

Over an affine base, a morphism from a proper family to a projective
Weierstrass model is proper as soon as it respects the structural morphisms.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u

namespace ModularCurves

noncomputable section

/-- A morphism from a proper family to a projective Weierstrass model over an
affine base is proper when it respects the structural morphisms. -/
theorem projModelMap_isProper_of_isAffine
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (f : C ⟶ projModel W)
    (hf : f ≫ projModelπ W = π ≫ S.toSpecΓ) :
    IsProper f := by
  haveI : IsIso S.toSpecΓ := IsAffine.affine
  haveI : IsProper (f ≫ projModelπ W) := by
    rw [hf]
    infer_instance
  exact IsProper.of_comp f (projModelπ W)

/-- Restricting a proper morphism to the exact preimage of a target open remains proper. -/
theorem resLE_isProper_of_preimage_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V) :
    IsProper (f.resLE U V (le_of_eq h.symm)) := by
  subst V
  rw [f.resLE_eq_morphismRestrict]
  infer_instance

/-- A fibre of `f` is affine if it embeds into an affine scalar extension of a fibre of
`f ≫ g`. -/
theorem fiber_isAffine_of_comp_fiber_isAffine
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsSeparated g]
    (h : ∀ s, IsAffine ((f ≫ g).fiber s)) (y : Y) :
    IsAffine (f.fiber y) := by
  let kMap : Spec (Y.residueField y) ⟶ Spec (S.residueField (g y)) :=
    Spec.map (g.residueFieldMap y)
  let e : pullback ((f ≫ g).fiberToSpecResidueField (g y)) kMap ≅
      pullback (f ≫ g) (Y.fromSpecResidueField y ≫ g) :=
    pullbackLeftPullbackSndIso (f ≫ g) (S.fromSpecResidueField (g y)) kMap ≪≫
      pullback.congrHom rfl (g.SpecMap_residueFieldMap_fromSpecResidueField y)
  letI : IsAffine ((f ≫ g).fiber (g y)) := h (g y)
  letI : IsAffine (pullback ((f ≫ g).fiberToSpecResidueField (g y)) kMap) :=
    inferInstance
  letI : IsAffine (pullback (f ≫ g) (Y.fromSpecResidueField y ≫ g)) :=
    IsAffine.of_isIso e.inv
  haveI hclosed : IsClosedImmersion (pullback.mapDesc f (Y.fromSpecResidueField y) g) :=
    MorphismProperty.of_isPullback
      (pullback_map_diagonal_isPullback f (Y.fromSpecResidueField y) g) inferInstance
  haveI haff : IsAffineHom (pullback.mapDesc f (Y.fromSpecResidueField y) g) :=
    @AlgebraicGeometry.IsClosedImmersion.instIsAffineHom _ _
      (pullback.mapDesc f (Y.fromSpecResidueField y) g) hclosed
  exact @isAffine_of_isAffineHom _ _
    (pullback.mapDesc f (Y.fromSpecResidueField y) g) haff inferInstance

/-- A proper map is locally quasi-finite when its fibres inside the fibres of a separated
composite are affine. -/
theorem locallyQuasiFinite_of_isProper_of_comp_fiber_isAffine
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsProper f] [IsSeparated g]
    (h : ∀ s, IsAffine ((f ≫ g).fiber s)) :
    LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_fiberToSpecResidueField f
  intro y
  letI : IsAffine (f.fiber y) :=
    fiber_isAffine_of_comp_fiber_isAffine f g h y
  have hAffine : IsAffineHom (f.fiberToSpecResidueField y) := by
    infer_instance
  have hProper : IsProper (f.fiberToSpecResidueField y) := by
    change IsProper (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  letI : IsFinite (f.fiberToSpecResidueField y) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hProper, hAffine⟩
  infer_instance

end

end ModularCurves
