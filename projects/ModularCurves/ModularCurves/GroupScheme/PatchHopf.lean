import ModularCurves.GroupScheme.SubgroupGroupObject
import ModularCurves.GroupScheme.StableCharts
import ModularCurves.GroupScheme.PatchKunneth

/-!
# The Hopf algebra of a finite locally free subgroup over an affine patch

Construction support for `[CHARTER-HOPF]` Wave C, leaf `[HG-C1c-1]`
(`.mathlib-quality/decomposition-hopf-crux.md`): with the group-object structure of `G`
in hand (`SubgroupGroupObject.lean`), the section ring `A = Γ(G, G|_V)` over an affine
base patch `V` carries the dual structure — counit from the unit section, antipode from
inversion, comultiplication from the multiplication through the affine Künneth
identification (`PatchKunneth.lean`).

This file builds the *maps*; their coalgebra/bialgebra/Hopf axioms are the `Γ`-duals of
the group-object laws already proven (`mulOver_assoc`, `unitOver_mulOver_left`,
`invOver_mulOver_left`).

## Main definitions
* `groupPatchCounit` — `ε : A ⟶ R`, restriction along the unit section.
* `groupPatchAntipode` — `S : A ⟶ A`, restriction along inversion.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)

namespace AffineChartPatch

variable (P : G.AffineChartPatch)

/-- The base patch lies in the unit section's preimage of the group patch: the unit
section is a section of the structure morphism. -/
theorem le_preimage_groupOpen_unitHom : P.V ≤ G.unitHom ⁻¹ᵁ P.groupOpen := by
  rw [groupOpen, ← Scheme.Hom.comp_preimage, G.unitHom_π]
  exact le_of_eq (Scheme.Hom.id_preimage P.V).symm

/-- The group patch is inversion-stable: `inv⁻¹(G|_V) = G|_V`. -/
theorem le_preimage_groupOpen_invHom : P.groupOpen ≤ G.invHom ⁻¹ᵁ P.groupOpen := by
  rw [groupOpen, ← Scheme.Hom.comp_preimage, G.invHom_π]

/-- **The counit** `ε : A ⟶ R`: restriction of sections along the unit section. -/
noncomputable def groupPatchCounit : P.groupRing ⟶ P.baseRing :=
  G.unitHom.appLE P.groupOpen P.V P.le_preimage_groupOpen_unitHom

/-- **The antipode** `S : A ⟶ A`: restriction of sections along inversion. -/
noncomputable def groupPatchAntipode : P.groupRing ⟶ P.groupRing :=
  G.invHom.appLE P.groupOpen P.groupOpen P.le_preimage_groupOpen_invHom

/-! ### The comultiplication -/

/-- The `V`-level square `G|_V ×_V G|_V`. -/
noncomputable abbrev groupSquare : Scheme.{u} :=
  pullback (G.π.resLE P.V P.groupOpen le_rfl) (G.π.resLE P.V P.groupOpen le_rfl)

/-- The `V`-level square maps into the `S`-level square. -/
noncomputable def groupSquareToSquare :
    P.groupSquare ⟶ (Over.mk G.π ⊗ Over.mk G.π).left :=
  pullback.map _ _ G.π G.π P.groupOpen.ι P.groupOpen.ι P.V.ι
    (Scheme.Hom.resLE_comp_ι _ _) (Scheme.Hom.resLE_comp_ι _ _)

@[reassoc (attr := simp)]
theorem groupSquareToSquare_fst :
    P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left
      = pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
          (G.π.resLE P.V P.groupOpen le_rfl) ≫ P.groupOpen.ι :=
  pullback.lift_fst _ _ _

/-- Multiplication, restricted to the `V`-level square. -/
noncomputable def squareMul : P.groupSquare ⟶ G.G :=
  P.groupSquareToSquare ≫ G.mulHom

/-- **The restricted multiplication is a morphism over the base patch**: its composite
with the structure morphism is the square's projection to `V`. -/
@[reassoc]
theorem squareMul_π : P.squareMul ≫ G.π
    = pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      ≫ G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι := by
  rw [squareMul, Category.assoc, G.mulHom_π]
  rw [show ((Over.mk G.π ⊗ Over.mk G.π).hom)
      = (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.π from rfl]
  rw [P.groupSquareToSquare_fst_assoc, Scheme.Hom.resLE_comp_ι]
  exact Category.assoc _ _ _

/-- The restricted multiplication lands in the group patch. -/
theorem top_le_preimage_groupOpen_squareMul :
    (⊤ : P.groupSquare.Opens) ≤ P.squareMul ⁻¹ᵁ P.groupOpen := by
  have hπ := P.squareMul_π
  rw [groupOpen, ← Scheme.Hom.comp_preimage, hπ]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Scheme.Opens.ι_preimage_self]
  exact le_top

/-- **The comultiplication** `Δ : A ⟶ A ⊗[R] A`: sections restricted along the group
multiplication, transported along the affine Künneth identification of the `V`-level
square. -/
noncomputable def groupPatchComul :
    P.groupRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) :=
  P.squareMul.appLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul
    ≫ (patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen
        rfl rfl).inv.appTop
    ≫ (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.groupRing))).hom

/-! ### `R`-linearity of the structure maps

Each is the `Γ`-dual of the corresponding "is a morphism over `S`" fact, through
`Scheme.Hom.appLE_comp_appLE`. -/

/-- The `appLE` of an identity morphism is the identity. -/
theorem appLE_id {X : Scheme.{u}} {U : X.Opens} (e : U ≤ (𝟙 X) ⁻¹ᵁ U) :
    Scheme.Hom.appLE (𝟙 X) U U e = 𝟙 _ := by
  rw [Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- `appLE` between the top opens is `appTop`. -/
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Hom.appLE f ⊤ ⊤ le_top = f.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

/-- The `⊤`-restriction of an open immersion's sections is the section iso. -/
theorem ι_appLE_top {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/-- `appLE` transported along an equality of morphisms. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (W : X.Opens) (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

/-- **The counit is `R`-linear**: `ε ∘ (algebraMap R A) = 𝟙 R`, the `Γ`-dual of
`unitHom ≫ π = 𝟙 S`. -/
theorem algebraMap_comp_groupPatchCounit :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupPatchCounit = 𝟙 P.baseRing := by
  rw [groupPatchCounit, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom G.unitHom_π P.V P.V]
  exact appLE_id _

/-- **The antipode is `R`-linear**, the `Γ`-dual of `invHom ≫ π = π`. -/
theorem algebraMap_comp_groupPatchAntipode :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupPatchAntipode
      = G.π.appLE P.V P.groupOpen le_rfl := by
  rw [groupPatchAntipode, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom G.invHom_π P.V P.groupOpen]

/-- The comultiplication, expressed through the generic `Γ`-transport. -/
theorem groupPatchComul_eq :
    P.groupPatchComul
      = P.squareMul.appLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul
        ≫ patchKunnethΓ G.π G.π P.hV P.isAffineOpen_groupOpen
            P.isAffineOpen_groupOpen rfl rfl :=
  rfl

/-- **The comultiplication is `R`-linear**: `Δ ∘ algebraMap = algebraMap`, the `Γ`-dual of
`squareMul ≫ π = fst ≫ (structure map to V)`. -/
theorem algebraMap_comp_groupPatchComul :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupPatchComul
      = CommRingCat.ofHom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.groupRing)) := by
  have halg : CommRingCat.ofHom (algebraMap P.baseRing P.groupRing)
      = G.π.appLE P.V P.groupOpen le_rfl := rfl
  -- the target factors through the left inclusion
  rw [show CommRingCat.ofHom
        (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.groupRing))
      = G.π.appLE P.V P.groupOpen le_rfl
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)) from by
    rw [← halg, ← CommRingCat.ofHom_comp]]
  -- the left inclusion is the transported first projection
  rw [← topIso_inv_fst_appTop_patchKunnethΓ G.π G.π P.hV P.isAffineOpen_groupOpen
    P.isAffineOpen_groupOpen rfl rfl]
  rw [groupPatchComul_eq, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  -- both sides restrict `π` along the two routes around the square
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom P.squareMul_π P.V ⊤]
  rw [show (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
          (G.π.resLE P.V P.groupOpen le_rfl)
        ≫ G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι).appLE P.V ⊤ _
      = G.π.appLE P.V P.groupOpen le_rfl
        ≫ P.groupOpen.topIso.inv
        ≫ (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
            (G.π.resLE P.V P.groupOpen le_rfl)).appTop from ?_]
  · exact (Category.assoc _ _ _).symm
  -- the appLE of the composite, unwound
  rw [appLE_congr_hom (Category.assoc
      (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl))
      (G.π.resLE P.V P.groupOpen le_rfl) P.V.ι).symm P.V ⊤,
    ← Scheme.Hom.appLE_comp_appLE
      (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl) ≫ G.π.resLE P.V P.groupOpen le_rfl)
      P.V.ι P.V ⊤ ⊤ P.V.ι_preimage_self.ge le_top,
    ι_appLE_top]
  rw [show (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      ≫ G.π.resLE P.V P.groupOpen le_rfl).appLE ⊤ ⊤ le_top
      = (G.π.resLE P.V P.groupOpen le_rfl).appTop
        ≫ (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
            (G.π.resLE P.V P.groupOpen le_rfl)).appTop from
    (Scheme.Hom.appLE_comp_appLE
      (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl))
      (G.π.resLE P.V P.groupOpen le_rfl) ⊤ ⊤ ⊤ le_top le_top).symm.trans
      (by rw [appLE_top_top, appLE_top_top])]
  rw [show (G.π.resLE P.V P.groupOpen le_rfl).appTop
      = P.V.topIso.hom ≫ G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupOpen.topIso.inv from
    Scheme.Hom.resLE_app_top (f := G.π) (U := P.V) (V := P.groupOpen) le_rfl]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
