import ModularCurves.GroupScheme.TranslationAction

/-!
# The action-pair is a closed immersion

Construction support for `[CHARTER-HOPF]` Wave C leaf `[HG-C2]`
(`.mathlib-quality/decomposition-hopf-crux.md`, appendix "Wave C — pin-map"): the graph
map `actPair G = ⟨act, pr⟩ : G ×_S E ⟶ E ×_S E` of the translation action decomposes as

  `actPair = (ι ⊗ 𝟙) ≫ shear`,

where `shear : E ×_S E ≅ E ×_S E`, `(y, x) ↦ (y + x, x)` is the **shear automorphism** of
the square — an isomorphism by pure group-object algebra (`Hom.commGroup`), with inverse
`(y, x) ↦ (y - x, x)`. Since `ι ⊗ 𝟙` is a base change of the closed immersion `ι`, the
whole `actPair` is a closed immersion; on a stable affine chart its `Γ`-dual is then
surjective, which is exactly the `precursorSurjective` field of `StableAffineChartData`
(the geometric input to the M5 Hopf–Galois theorem).

## Main definitions
* `EllipticCurve.shearAuto` — the shear automorphism of `E.asOver ⊗ E.asOver`.

## Main results
* `FiniteLocallyFreeSubgroup.actPair_eq_shear` — the decomposition.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

section Shear

variable (E)

/-- The shear map `(y, x) ↦ (y + x, x)` on the square `E ×_S E`, in hom-group form. -/
noncomputable def shearHom : E.asOver ⊗ E.asOver ⟶ E.asOver ⊗ E.asOver :=
  letI : CommGroup (E.asOver ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
  lift (fst E.asOver E.asOver * snd E.asOver E.asOver) (snd E.asOver E.asOver)

/-- The inverse shear `(y, x) ↦ (y - x, x)`. -/
noncomputable def unshearHom : E.asOver ⊗ E.asOver ⟶ E.asOver ⊗ E.asOver :=
  letI : CommGroup (E.asOver ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
  lift (fst E.asOver E.asOver * (snd E.asOver E.asOver)⁻¹) (snd E.asOver E.asOver)

@[reassoc (attr := simp)]
theorem shearHom_fst :
    letI : CommGroup (E.asOver ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    E.shearHom ≫ fst E.asOver E.asOver
      = fst E.asOver E.asOver * snd E.asOver E.asOver :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem shearHom_snd :
    E.shearHom ≫ snd E.asOver E.asOver = snd E.asOver E.asOver :=
  lift_snd _ _

@[reassoc (attr := simp)]
theorem unshearHom_fst :
    letI : CommGroup (E.asOver ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    E.unshearHom ≫ fst E.asOver E.asOver
      = fst E.asOver E.asOver * (snd E.asOver E.asOver)⁻¹ :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem unshearHom_snd :
    E.unshearHom ≫ snd E.asOver E.asOver = snd E.asOver E.asOver :=
  lift_snd _ _

/-- **The shear automorphism** of the square: `(y, x) ↦ (y + x, x)`, an isomorphism of
`E ×_S E` over `S` with inverse the unshear. The inverse laws are pure hom-group algebra:
precomposition is a group homomorphism into the pointwise group of maps to the group
object `E.asOver`. -/
noncomputable def shearAuto : E.asOver ⊗ E.asOver ≅ E.asOver ⊗ E.asOver where
  hom := E.shearHom
  inv := E.unshearHom
  hom_inv_id := by
    letI : CommGroup (E.asOver ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.id_comp, unshearHom_fst, MonObj.comp_mul,
        GrpObj.comp_inv, shearHom_fst, shearHom_snd, mul_inv_cancel_right]
    · rw [Category.assoc, Category.id_comp, unshearHom_snd, shearHom_snd]
  inv_hom_id := by
    letI : CommGroup (E.asOver ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.id_comp, shearHom_fst, MonObj.comp_mul,
        unshearHom_fst, unshearHom_snd, inv_mul_cancel_right]
    · rw [Category.assoc, Category.id_comp, shearHom_snd, unshearHom_snd]

end Shear

namespace FiniteLocallyFreeSubgroup

/-- **The shear decomposition of the action pair**: `⟨act, pr⟩ = (ι ⊗ 𝟙) ≫ shear`.
Both components are checked in the hom-group: the first is
`translationAction_eq_mul`, the second is the projection law. -/
theorem actPair_eq_shear (G : FiniteLocallyFreeSubgroup E) :
    G.actPair = (G.ιOver ⊗ₘ 𝟙 E.asOver) ≫ E.shearHom := by
  letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
  refine hom_ext _ _ ?_ ?_
  · rw [G.actPair_fst, Category.assoc, E.shearHom_fst, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd, Category.comp_id, G.translationAction_eq_mul]
  · rw [G.actPair_snd, Category.assoc, E.shearHom_snd, tensorHom_snd, Category.comp_id]
    rfl

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
