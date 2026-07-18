/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.SubgroupGroupObject
import ModularCurves.GroupScheme.StableCharts
import ModularCurves.GroupScheme.PatchKunneth
import ModularCurves.ForMathlib.SchemeAppLE

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
theorem groupSquareToSquare_snd :
    P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left
      = pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
          (G.π.resLE P.V P.groupOpen le_rfl) ≫ P.groupOpen.ι :=
  pullback.lift_snd _ _ _

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

/-! ### Algebra-map packaging -/

/-- The counit as an `R`-algebra map. -/
noncomputable def counitAlg : P.groupRing →ₐ[P.baseRing] P.baseRing where
  toRingHom := P.groupPatchCounit.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRing ⟶ P.baseRing => m.hom r)
      P.algebraMap_comp_groupPatchCounit
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at h
    exact h

/-- The antipode as an `R`-algebra map. -/
noncomputable def antipodeAlg : P.groupRing →ₐ[P.baseRing] P.groupRing where
  toRingHom := P.groupPatchAntipode.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRing ⟶ P.groupRing => m.hom r)
      P.algebraMap_comp_groupPatchAntipode
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h

/-- The comultiplication as an `R`-algebra map. -/
noncomputable def comulAlg :
    P.groupRing →ₐ[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing) where
  toRingHom := P.groupPatchComul.hom
  commutes' := fun r => by
    have h := congrArg
      (fun m : P.baseRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing)
        => m.hom r) P.algebraMap_comp_groupPatchComul
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h

/-! ### The counit laws, scheme-side -/

/-- The unit section, restricted to the patch. -/
noncomputable def unitSection : P.V.toScheme ⟶ P.groupOpen.toScheme :=
  G.unitHom.resLE P.groupOpen P.V P.le_preimage_groupOpen_unitHom

set_option backward.isDefEq.respectTransparency.types false in
/-- The restricted unit section is a section of the restricted structure map. -/
@[reassoc (attr := simp)]
theorem unitSection_comp_groupToBase :
    P.unitSection ≫ G.π.resLE P.V P.groupOpen le_rfl = 𝟙 P.V.toScheme := by
  rw [unitSection, Scheme.Hom.resLE_comp_resLE,
    appLE_congr_hom_resLE G.unitHom_π P.V P.V, Scheme.Hom.resLE_id,
    Scheme.homOfLE_rfl]

/-- The unit section, composed into `G`, is the zero section over the patch. -/
@[reassoc]
theorem unitSection_comp_ι :
    P.unitSection ≫ P.groupOpen.ι = P.V.ι ≫ G.unitHom :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The section `⟨e ∘ structure, 𝟙⟩ : G|_V ⟶ G|_V ×_V G|_V` of the left counit law. -/
noncomputable def leftUnitSection : P.groupOpen.toScheme ⟶ P.groupSquare :=
  pullback.lift (G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection)
    (𝟙 P.groupOpen.toScheme)
    (by rw [Category.assoc, P.unitSection_comp_groupToBase, Category.comp_id,
      Category.id_comp])

@[reassoc (attr := simp)]
theorem leftUnitSection_fst :
    P.leftUnitSection ≫ pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem leftUnitSection_snd :
    P.leftUnitSection ≫ pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = 𝟙 P.groupOpen.toScheme :=
  pullback.lift_snd _ _ _

/-- **The counit law, scheme side**: acting by the unit section on the left is the
identity — `⟨e ∘ structure, 𝟙⟩ ≫ μ = 𝟙` (as maps into `G`). Proved by `ι`-cancellation and
point-algebra: the first component restricts to the zero point. -/
theorem leftUnitSection_comp_squareMul :
    P.leftUnitSection ≫ P.squareMul = P.groupOpen.ι := by
  rw [← cancel_mono G.ι, squareMul]
  set k := P.leftUnitSection ≫ P.groupSquareToSquare with hk
  rw [show (P.leftUnitSection ≫ P.groupSquareToSquare ≫ G.mulHom) ≫ G.ι
      = k ≫ (G.mulHom ≫ G.ι) from by rw [hk]; simp only [Category.assoc]]
  rw [G.mulHom_ι]
  -- restrict the point sum along `k`
  have hsum : k ≫ ((G.sqFstPoint + G.sqSndPoint : E.Point _) : _ ⟶ E.E)
      = ((EllipticCurve.Point.restrict E k G.sqFstPoint +
            EllipticCurve.Point.restrict E k G.sqSndPoint : E.Point _) : _ ⟶ E.E) := by
    rw [← EllipticCurve.Point.restrict_add]
    rfl
  rw [hsum]
  -- the first restricted point is zero
  have hk1 : k ≫ (fst (Over.mk G.π) (Over.mk G.π)).left
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection ≫ P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_fst]
    exact leftUnitSection_fst_assoc G P P.groupOpen.ι
  have hk2 : k ≫ (snd (Over.mk G.π) (Over.mk G.π)).left = P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_snd]
    exact leftUnitSection_snd_assoc G P P.groupOpen.ι
  have hfst : EllipticCurve.Point.restrict E k G.sqFstPoint = 0 := by
    refine Subtype.ext ?_
    show k ≫ ((fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
    rw [E.point_zero_val,
      show ((Over.mk G.π ⊗ Over.mk G.π).hom)
        = (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.π from rfl,
      ← Category.assoc k, ← Category.assoc k, hk1]
    rw [P.unitSection_comp_ι]
    show ((G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι ≫ G.unitHom : _ ⟶ G.G) ≫ G.ι)
      = ((G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι ≫ G.unitHom : _ ⟶ G.G) ≫ G.π)
        ≫ E.zero
    simp only [Category.assoc, G.unitHom_ι, G.unitHom_π, Category.id_comp]
  rw [hfst, zero_add]
  -- the second restricted point is the inclusion
  show k ≫ ((snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
  rw [← Category.assoc k, hk2]

/-! ### The counit law, `Γ`-side -/

/-- `appTop` of the restricted unit section. -/
theorem unitSection_appTop :
    P.unitSection.appTop
      = P.groupOpen.topIso.hom ≫ P.groupPatchCounit ≫ P.V.topIso.inv :=
  Scheme.Hom.resLE_app_top (f := G.unitHom) (U := P.groupOpen) (V := P.V)
    P.le_preimage_groupOpen_unitHom

/-- `appTop` of the restricted structure map. -/
theorem groupToBase_appTop :
    (G.π.resLE P.V P.groupOpen le_rfl).appTop
      = P.V.topIso.hom ≫ G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupOpen.topIso.inv :=
  Scheme.Hom.resLE_app_top (f := G.π) (U := P.V) (V := P.groupOpen) le_rfl

/-- The Künneth transport for the group square. -/
noncomputable abbrev squareΓ :
    Γ(P.groupSquare, ⊤) ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) :=
  patchKunnethΓ G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl

/-- The `Γ`-dual of the left unit section. -/
noncomputable def counitLiftΓ :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) ⟶ P.groupRing :=
  inv P.squareΓ ≫ P.leftUnitSection.appTop ≫ P.groupOpen.topIso.hom

set_option backward.isDefEq.respectTransparency.types false in
/-- **The counit law, `Γ`-side, in transported form**: `Δ` followed by the dual of the
left unit section is the identity. -/
theorem groupPatchComul_comp_counitLiftΓ :
    P.groupPatchComul ≫ P.counitLiftΓ = 𝟙 P.groupRing := by
  rw [groupPatchComul_eq, counitLiftΓ, Category.assoc,
    ← Category.assoc P.squareΓ, IsIso.hom_inv_id, Category.id_comp]
  -- the `appLE`-composite of the scheme identity
  rw [show P.leftUnitSection.appTop
      = P.leftUnitSection.appLE ⊤ ⊤ le_top from (appLE_top_top _).symm]
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom P.leftUnitSection_comp_squareMul P.groupOpen ⊤,
    ι_appLE_top, Iso.inv_hom_id]

/-- The right inclusion, composed with the dual of the left unit section, is the
identity. -/
theorem includeRight_comp_counitLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.counitLiftΓ = 𝟙 P.groupRing := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ, ← hleg]
  -- cancel the transport
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  -- the two `appTop`s compose to the scheme identity
  have hcomp : (pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.leftUnitSection.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, P.leftUnitSection_snd,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [← Category.assoc ((pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl

/-- The left inclusion, composed with the dual of the left unit section, is the counit
followed by the structure map. -/
theorem includeLeft_comp_counitLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.counitLiftΓ
      = P.groupPatchCounit ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ, ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  -- the two `appTop`s compose to the dual of `leftUnitSection ≫ fst`
  have hcomp : (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.leftUnitSection.appTop
      = P.unitSection.appTop ≫ (G.π.resLE P.V P.groupOpen le_rfl).appTop := by
    rw [← Scheme.Hom.comp_appTop, P.leftUnitSection_fst, Scheme.Hom.comp_appTop]
  rw [← Category.assoc ((pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp]
  -- unwind the two restricted `appTop`s
  rw [P.unitSection_appTop, P.groupToBase_appTop]
  simp only [Category.assoc]
  rw [← Category.assoc P.V.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc P.groupOpen.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [Category.comp_id]

/-- The algebraic counit lift `A ⊗[R] A →ₐ[R] A`, `a ⊗ b ↦ ε(a) • b`. -/
noncomputable def counitLift :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing] P.groupRing :=
  Algebra.TensorProduct.lift ((Algebra.ofId P.baseRing P.groupRing).comp P.counitAlg)
    (AlgHom.id P.baseRing P.groupRing) (fun _ _ => Commute.all _ _)

/-- **The counit lift is the `Γ`-dual of the left unit section.** -/
theorem counitLift_eq_counitLiftΓ :
    CommRingCat.ofHom P.counitLift.toRingHom = P.counitLiftΓ := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_counitLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift G P (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = _
    rw [counitLift, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_counitLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift G P ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = _
    rw [counitLift, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl

/-- **The left counit law**: `(ε ⊗ id) ∘ Δ = id`, in `AlgHom` form. -/
theorem counitLift_comp_comulAlg :
    P.counitLift.comp P.comulAlg = AlgHom.id P.baseRing P.groupRing := by
  have h := P.groupPatchComul_comp_counitLiftΓ
  rw [← P.counitLift_eq_counitLiftΓ] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] at h2
  exact h2

/-! ### The right counit law -/

/-- The section `⟨𝟙, e ∘ structure⟩ : G|_V ⟶ G|_V ×_V G|_V`. -/
noncomputable def rightUnitSection : P.groupOpen.toScheme ⟶ P.groupSquare :=
  pullback.lift (𝟙 P.groupOpen.toScheme)
    (G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection)
    (by rw [Category.assoc, P.unitSection_comp_groupToBase, Category.comp_id,
      Category.id_comp])

@[reassoc (attr := simp)]
theorem rightUnitSection_fst :
    P.rightUnitSection ≫ pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = 𝟙 P.groupOpen.toScheme :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rightUnitSection_snd :
    P.rightUnitSection ≫ pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection :=
  pullback.lift_snd _ _ _

/-- **The right counit law, scheme side**. -/
theorem rightUnitSection_comp_squareMul :
    P.rightUnitSection ≫ P.squareMul = P.groupOpen.ι := by
  rw [← cancel_mono G.ι, squareMul]
  set k := P.rightUnitSection ≫ P.groupSquareToSquare with hk
  rw [show (P.rightUnitSection ≫ P.groupSquareToSquare ≫ G.mulHom) ≫ G.ι
      = k ≫ (G.mulHom ≫ G.ι) from by rw [hk]; simp only [Category.assoc]]
  rw [G.mulHom_ι]
  have hsum : k ≫ ((G.sqFstPoint + G.sqSndPoint : E.Point _) : _ ⟶ E.E)
      = ((EllipticCurve.Point.restrict E k G.sqFstPoint
          + EllipticCurve.Point.restrict E k G.sqSndPoint : E.Point _) : _ ⟶ E.E) := by
    rw [← EllipticCurve.Point.restrict_add]
    rfl
  rw [hsum]
  have hk1 : k ≫ (fst (Over.mk G.π) (Over.mk G.π)).left = P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_fst]
    exact rightUnitSection_fst_assoc G P P.groupOpen.ι
  have hk2 : k ≫ (snd (Over.mk G.π) (Over.mk G.π)).left
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection ≫ P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_snd]
    exact rightUnitSection_snd_assoc G P P.groupOpen.ι
  have hsnd : EllipticCurve.Point.restrict E k G.sqSndPoint = 0 := by
    refine Subtype.ext ?_
    show k ≫ ((snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
    rw [E.point_zero_val,
      show ((Over.mk G.π ⊗ Over.mk G.π).hom)
        = (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.π from rfl,
      ← Category.assoc k, ← Category.assoc k, hk1, hk2]
    rw [P.unitSection_comp_ι]
    show ((G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι ≫ G.unitHom : _ ⟶ G.G) ≫ G.ι)
      = (P.groupOpen.ι ≫ G.π) ≫ E.zero
    rw [← Scheme.Hom.resLE_comp_ι G.π (le_rfl : P.groupOpen ≤ G.π ⁻¹ᵁ P.V)]
    simp only [Category.assoc, G.unitHom_ι]
  rw [hsnd, add_zero]
  show k ≫ ((fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
  rw [← Category.assoc k, hk1]

/-- The `Γ`-dual of the right unit section. -/
noncomputable def counitLiftΓ' :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) ⟶ P.groupRing :=
  inv P.squareΓ ≫ P.rightUnitSection.appTop ≫ P.groupOpen.topIso.hom

set_option backward.isDefEq.respectTransparency.types false in
theorem groupPatchComul_comp_counitLiftΓ' :
    P.groupPatchComul ≫ P.counitLiftΓ' = 𝟙 P.groupRing := by
  rw [groupPatchComul_eq, counitLiftΓ', Category.assoc,
    ← Category.assoc P.squareΓ, IsIso.hom_inv_id, Category.id_comp]
  rw [show P.rightUnitSection.appTop
      = P.rightUnitSection.appLE ⊤ ⊤ le_top from (appLE_top_top _).symm]
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom P.rightUnitSection_comp_squareMul P.groupOpen ⊤,
    ι_appLE_top, Iso.inv_hom_id]

theorem includeLeft_comp_counitLiftΓ' :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.counitLiftΓ' = 𝟙 P.groupRing := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ', ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.rightUnitSection.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, P.rightUnitSection_fst,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [← Category.assoc ((pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl

theorem includeRight_comp_counitLiftΓ' :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.counitLiftΓ'
      = P.groupPatchCounit ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ', ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.rightUnitSection.appTop
      = P.unitSection.appTop ≫ (G.π.resLE P.V P.groupOpen le_rfl).appTop := by
    rw [← Scheme.Hom.comp_appTop, P.rightUnitSection_snd, Scheme.Hom.comp_appTop]
  rw [← Category.assoc ((pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp]
  rw [P.unitSection_appTop, P.groupToBase_appTop]
  simp only [Category.assoc]
  rw [← Category.assoc P.V.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc P.groupOpen.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [Category.comp_id]

/-- The algebraic right counit lift `A ⊗[R] A →ₐ[R] A`, `a ⊗ b ↦ a • ε(b)`. -/
noncomputable def counitLift' :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing] P.groupRing :=
  Algebra.TensorProduct.lift (AlgHom.id P.baseRing P.groupRing)
    ((Algebra.ofId P.baseRing P.groupRing).comp P.counitAlg)
    (fun _ _ => Commute.all _ _)

theorem counitLift'_eq_counitLiftΓ' :
    CommRingCat.ofHom P.counitLift'.toRingHom = P.counitLiftΓ' := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_counitLiftΓ']
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift' G P (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = _
    rw [counitLift', Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_counitLiftΓ']
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift' G P ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = _
    rw [counitLift', Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl

/-- **The right counit law**: `(id ⊗ ε) ∘ Δ = id`, in `AlgHom` form. -/
theorem counitLift'_comp_comulAlg :
    P.counitLift'.comp P.comulAlg = AlgHom.id P.baseRing P.groupRing := by
  have h := P.groupPatchComul_comp_counitLiftΓ'
  rw [← P.counitLift'_eq_counitLiftΓ'] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] at h2
  exact h2

/-! ### Towards coassociativity: the `⊤`-level presentation

We restate the Hopf structure with `R' := Γ(V.toScheme, ⊤)` and `A' := Γ(G|_V, ⊤)`, where
the group structure maps dualise directly (as `appTop`, no `topIso` conjugation). The
opens-level maps are recovered by conjugating with `topIso`. -/

/-- The `⊤`-level base ring `R' = Γ(V.toScheme, ⊤)`. -/
noncomputable abbrev baseRingTop : CommRingCat := Γ(P.V.toScheme, ⊤)

/-- The `⊤`-level group ring `A' = Γ(G|_V.toScheme, ⊤)`. -/
noncomputable abbrev groupRingTop : CommRingCat := Γ(P.groupOpen.toScheme, ⊤)

/-- The structure map of the group patch, in the spelling used by `groupSquare`. -/
noncomputable abbrev groupToBaseRes : P.groupOpen.toScheme ⟶ P.V.toScheme :=
  G.π.resLE P.V P.groupOpen le_rfl

/-- `R'` is `R` transported by `topIso`. -/
noncomputable instance : Algebra P.baseRingTop P.groupRingTop :=
  P.groupToBaseRes.appTop.hom.toAlgebra

instance : IsAffine P.V.toScheme := P.hV
instance : IsAffine P.groupOpen.toScheme := P.isAffineOpen_groupOpen

/-! #### The `⊤`-level structure maps -/

/-- The `⊤`-level counit `ε' : A' ⟶ R'`. -/
noncomputable def counitTop : P.groupRingTop ⟶ P.baseRingTop :=
  P.unitSection.appTop

/-- The group square is affine (it is the `Spec` of `A ⊗[R] A`). -/
theorem isAffine_groupSquare : IsAffine P.groupSquare := by
  haveI : IsIso (patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen
      P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl).hom :=
    inferInstance
  exact IsAffine.of_isIso (patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen
    P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl).hom

/-- The restricted multiplication, corestricted to the group patch:
`G|_V ×_V G|_V ⟶ G|_V`. -/
noncomputable def squareMulRes : P.groupSquare ⟶ P.groupOpen.toScheme :=
  P.groupSquare.topIso.inv
    ≫ P.squareMul.resLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul

/-- The corestricted multiplication recovers `squareMul` after including the patch. -/
@[reassoc]
theorem squareMulRes_comp_ι : P.squareMulRes ≫ P.groupOpen.ι = P.squareMul := by
  rw [squareMulRes, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [show (⊤ : P.groupSquare.Opens).ι = P.groupSquare.topIso.hom from rfl,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The affine Künneth transport for the group square, `⊤`-level. -/
noncomputable abbrev squareΓTop :
    Γ(P.groupSquare, ⊤) ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) :=
  affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl

/-- **The `⊤`-level comultiplication** `Δ' : A' ⟶ A' ⊗[R'] A'`. -/
noncomputable def comulTop :
    P.groupRingTop ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) :=
  P.squareMulRes.appTop ≫ P.squareΓTop

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
