/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.SubgroupQuotientConstruction

/-!
# The subgroup-scheme quotient glue: the equalizer-subring model (`[HG-C4c-2]`)

Design v10.190-G0. For **any** stable open `W ⊆ E` the quotient functions are the equalizer
subring of the two restricted-leg section maps — no affineness, no Künneth:
`quotientRing W := eqLocus Γ(act|_W) Γ(pr|_W)`, glued via restriction-descended transitions
on the `ForMathlib/SchemeQuotient` pattern. The Hopf layer (C4a/C4b, proven) enters only
through the per-affine-patch comparison `quotientRing P.U = coinvariants P.chartCoaction`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)

/-- The action-side section map of a stable open: sections of `W` pulled back along the
translation action (the `appLE` of the action into the stability window). -/
noncomputable def actRing {W : E.E.Opens} (hW : G.IsStableOpen W) :
    Γ(E.E, W) ⟶ Γ((Over.mk G.π ⊗ E.asOver).left, G.actionProj.left ⁻¹ᵁ W) :=
  G.translationAction.left.appLE W (G.actionProj.left ⁻¹ᵁ W) hW

/-- The projection-side section map of a stable open. -/
noncomputable def prRing (W : E.E.Opens) :
    Γ(E.E, W) ⟶ Γ((Over.mk G.π ⊗ E.asOver).left, G.actionProj.left ⁻¹ᵁ W) :=
  G.actionProj.left.appLE W (G.actionProj.left ⁻¹ᵁ W) le_rfl

/-- **The quotient ring of a stable open**: the subring of sections on which the translated
and projected pullbacks agree — the invariant functions. -/
noncomputable def quotientRing {W : E.E.Opens} (hW : G.IsStableOpen W) : Subring Γ(E.E, W) :=
  RingHom.eqLocus (G.actRing hW).hom (G.prRing W).hom

/-- **The local quotient of a stable open**: the spectrum of its invariant functions. -/
noncomputable def localQuotientOpen {W : E.E.Opens} (hW : G.IsStableOpen W) : Scheme.{u} :=
  Spec (CommRingCat.of (G.quotientRing hW))

/-- **Restriction preserves invariance** (`[HG-C4c-2]` step 2, membership): for nested
stable opens the restriction of an invariant section is invariant — the two legs commute
with restrictions (`appLE` exchange). -/
theorem mem_quotientRing_of_res {W W' : E.E.Opens} (hW : G.IsStableOpen W)
    (hW' : G.IsStableOpen W') (hle : W ≤ W') {b : Γ(E.E, W')}
    (hb : b ∈ G.quotientRing hW') :
    (E.E.presheaf.map (homOfLE hle).op).hom b ∈ G.quotientRing hW := by
  have hact : (G.translationAction.left.appLE W' (G.actionProj.left ⁻¹ᵁ W') hW') ≫
      ((Over.mk G.π ⊗ E.asOver).left.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono G.actionProj.left hle)).op)
      = (E.E.presheaf.map (homOfLE hle).op) ≫
        G.translationAction.left.appLE W (G.actionProj.left ⁻¹ᵁ W) hW :=
    (Scheme.Hom.appLE_map G.translationAction.left hW'
        (homOfLE (Scheme.Hom.preimage_mono G.actionProj.left hle)).op).trans
      (Scheme.Hom.map_appLE G.translationAction.left hW (homOfLE hle).op).symm
  have hpr : (G.actionProj.left.appLE W' (G.actionProj.left ⁻¹ᵁ W') le_rfl) ≫
      ((Over.mk G.π ⊗ E.asOver).left.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono G.actionProj.left hle)).op)
      = (E.E.presheaf.map (homOfLE hle).op) ≫
        G.actionProj.left.appLE W (G.actionProj.left ⁻¹ᵁ W) le_rfl :=
    (Scheme.Hom.appLE_map G.actionProj.left le_rfl
        (homOfLE (Scheme.Hom.preimage_mono G.actionProj.left hle)).op).trans
      (Scheme.Hom.map_appLE G.actionProj.left le_rfl (homOfLE hle).op).symm
  have h1 := congrArg (fun m => (CommRingCat.Hom.hom m) b) hact
  have h2 := congrArg (fun m => (CommRingCat.Hom.hom m) b) hpr
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
  show (G.actRing hW).hom _ = (G.prRing W).hom _
  rw [actRing, prRing, ← h1, ← h2]
  exact congrArg _ hb

/-- **The transition map of local quotients** (`[HG-C4c-2]` step 2): restriction of
invariants, on spectra. -/
noncomputable def localQuotientMapW {W W' : E.E.Opens} (hW : G.IsStableOpen W)
    (hW' : G.IsStableOpen W') (hle : W ≤ W') :
    G.localQuotientOpen hW ⟶ G.localQuotientOpen hW' :=
  Spec.map (CommRingCat.ofHom
    { toFun := fun b => ⟨(E.E.presheaf.map (homOfLE hle).op).hom b.1,
        G.mem_quotientRing_of_res hW hW' hle b.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) })

/-! ### Step 3 — the per-patch comparison with the Hopf model -/

namespace AffineChartPatch

variable {G} (P : G.AffineChartPatch)

/-- The chart Künneth comparison on sections: `Γ(pr⁻¹U) ≅ B ⊗ A` (group-first). -/
noncomputable def kappa :
    Γ((Over.mk G.π ⊗ E.asOver).left, G.actionProj.left ⁻¹ᵁ P.U) ⟶
      CommRingCat.of (P.groupRing ⊗[P.baseRing] P.chartRing) :=
  (G.actionProj.left ⁻¹ᵁ P.U).topIso.inv ≫ (G.chartPullbackIso P.U).inv.appTop ≫
    P.chartSpecIso.inv.appTop ≫
    (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom

/-- The action-side `appLE` in `topIso`-conjugated form (`resLE_app_top`). -/
theorem actRing_eq_topIso :
    G.actRing P.hstable
      = P.U.topIso.inv ≫ (G.restrictedAction P.hstable).appTop ≫
        (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom := by
  have h := Scheme.Hom.resLE_app_top (f := G.translationAction.left) (U := P.U)
    (V := G.actionProj.left ⁻¹ᵁ P.U) (e := P.hstable)
  rw [actRing, show (G.restrictedAction P.hstable).appTop
      = (G.translationAction.left.resLE P.U (G.actionProj.left ⁻¹ᵁ P.U) P.hstable).app ⊤
      from rfl, h]
  have e1 : (P.U.topIso.hom ≫
      G.translationAction.left.appLE P.U (G.actionProj.left ⁻¹ᵁ P.U) P.hstable ≫
      (G.actionProj.left ⁻¹ᵁ P.U).topIso.inv) ≫ (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom
      = P.U.topIso.hom ≫
        G.translationAction.left.appLE P.U (G.actionProj.left ⁻¹ᵁ P.U) P.hstable :=
    (Category.assoc _ _ _).trans <|
      congrArg (P.U.topIso.hom ≫ ·) <|
        (Category.assoc _ _ _).trans <|
          (congrArg (G.translationAction.left.appLE P.U
              (G.actionProj.left ⁻¹ᵁ P.U) P.hstable ≫ ·)
            (G.actionProj.left ⁻¹ᵁ P.U).topIso.inv_hom_id).trans (Category.comp_id _)
  exact ((congrArg (P.U.topIso.inv ≫ ·) e1).trans
    (P.U.topIso.inv_hom_id_assoc _)).symm

/-- The action leg under `kappa` is the chart co-action ring. -/
theorem actRing_kappa :
    G.actRing P.hstable ≫ P.kappa = P.coactionRing := by
  rw [kappa, coactionRing, coactionToPullback, actRing_eq_topIso]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The projection-side `appLE` in `topIso`-conjugated form. -/
theorem prRing_eq_topIso :
    G.prRing P.U
      = P.U.topIso.inv ≫ (G.restrictedProj P.U).appTop ≫
        (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom := by
  have h := Scheme.Hom.resLE_app_top (f := G.actionProj.left) (U := P.U)
    (V := G.actionProj.left ⁻¹ᵁ P.U) (e := le_rfl)
  rw [prRing, show (G.restrictedProj P.U).appTop
      = (G.actionProj.left.resLE P.U (G.actionProj.left ⁻¹ᵁ P.U) le_rfl).app ⊤
      from rfl, h]
  have e1 : (P.U.topIso.hom ≫
      G.actionProj.left.appLE P.U (G.actionProj.left ⁻¹ᵁ P.U) le_rfl ≫
      (G.actionProj.left ⁻¹ᵁ P.U).topIso.inv) ≫ (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom
      = P.U.topIso.hom ≫
        G.actionProj.left.appLE P.U (G.actionProj.left ⁻¹ᵁ P.U) le_rfl :=
    (Category.assoc _ _ _).trans <|
      congrArg (P.U.topIso.hom ≫ ·) <|
        (Category.assoc _ _ _).trans <|
          (congrArg (G.actionProj.left.appLE P.U
              (G.actionProj.left ⁻¹ᵁ P.U) le_rfl ≫ ·)
            (G.actionProj.left ⁻¹ᵁ P.U).topIso.inv_hom_id).trans (Category.comp_id _)
  exact ((congrArg (P.U.topIso.inv ≫ ·) e1).trans
    (P.U.topIso.inv_hom_id_assoc _)).symm

/-- The `isoSpec` round trip on sections is the identity. -/
theorem topIso_isoSpec_appTop_ΓSpecIso :
    P.U.topIso.inv ≫ P.hU.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(E.E, P.U)).hom
      = 𝟙 Γ(E.E, P.U) := by
  haveI : IsAffine P.U.toScheme := P.hU
  have hcomp : P.hU.isoSpec.inv.appTop ≫ P.hU.isoSpec.hom.appTop
      = 𝟙 Γ(P.U.toScheme, ⊤) := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  have hhom : P.hU.isoSpec.hom.appTop
      = (Scheme.ΓSpecIso Γ(E.E, P.U)).hom ≫ P.U.topIso.inv := by
    rw [P.hU.isoSpec_hom]
    exact Scheme.Opens.toSpecΓ_appTop P.U
  have h1 : P.hU.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(E.E, P.U)).hom
      = P.U.topIso.hom := by
    rw [hhom] at hcomp
    have h2 := congrArg (· ≫ P.U.topIso.hom) hcomp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp] at h2
    exact h2
  exact (congrArg (P.U.topIso.inv ≫ ·) h1).trans P.U.topIso.inv_hom_id

/-- **The projection leg under `kappa` is `includeRight`** — the Γ-dual of the raw
second-projection bridge (`chartSpecIso_inv_snd` + `chartPullbackIso_inv_restrictedProj`),
descended through the `ΓSpecIso` adjunction. -/
theorem prRing_kappa :
    G.prRing P.U ≫ P.kappa
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom := by
  -- the scheme-level identification, from the proven bridges
  have hgeo : P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ G.restrictedProj P.U
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫
        P.hU.isoSpec.inv :=
    (congrArg (P.chartSpecIso.inv ≫ ·) P.chartPullbackIso_inv_restrictedProj).trans
      P.chartSpecIso_inv_snd
  -- take sections of the identification
  have hΓ := congrArg Scheme.Hom.appTop hgeo
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    Category.assoc] at hΓ
  -- assemble
  rw [prRing_eq_topIso, kappa]
  have hstep1 : (P.U.topIso.inv ≫ (G.restrictedProj P.U).appTop ≫
        (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom) ≫
        ((G.actionProj.left ⁻¹ᵁ P.U).topIso.inv ≫ (G.chartPullbackIso P.U).inv.appTop ≫
          P.chartSpecIso.inv.appTop ≫
          (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom)
      = P.U.topIso.inv ≫ ((G.restrictedProj P.U).appTop ≫
          (G.chartPullbackIso P.U).inv.appTop ≫ P.chartSpecIso.inv.appTop) ≫
          (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom := by
    have t3 : (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom ≫
        ((G.actionProj.left ⁻¹ᵁ P.U).topIso.inv ≫ (G.chartPullbackIso P.U).inv.appTop ≫
          P.chartSpecIso.inv.appTop ≫
          (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom)
        = (G.chartPullbackIso P.U).inv.appTop ≫ P.chartSpecIso.inv.appTop ≫
          (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom :=
      (G.actionProj.left ⁻¹ᵁ P.U).topIso.hom_inv_id_assoc _
    calc _ = P.U.topIso.inv ≫ ((G.restrictedProj P.U).appTop ≫
            ((G.actionProj.left ⁻¹ᵁ P.U).topIso.hom ≫
              ((G.actionProj.left ⁻¹ᵁ P.U).topIso.inv ≫
                (G.chartPullbackIso P.U).inv.appTop ≫ P.chartSpecIso.inv.appTop ≫
                (Scheme.ΓSpecIso (.of
                  (P.groupRing ⊗[P.baseRing] P.chartRing))).hom))) := by
          simp only [Category.assoc]
      _ = P.U.topIso.inv ≫ ((G.restrictedProj P.U).appTop ≫
            ((G.chartPullbackIso P.U).inv.appTop ≫ P.chartSpecIso.inv.appTop ≫
              (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom)) :=
          congrArg (fun m => P.U.topIso.inv ≫ (G.restrictedProj P.U).appTop ≫ m) t3
      _ = _ := by simp only [Category.assoc]
  calc _ = P.U.topIso.inv ≫ ((G.restrictedProj P.U).appTop ≫
          (G.chartPullbackIso P.U).inv.appTop ≫ P.chartSpecIso.inv.appTop) ≫
          (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom := hstep1
    _ = P.U.topIso.inv ≫ (P.hU.isoSpec.inv.appTop ≫
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            P.chartRing →ₐ[P.baseRing]
              P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom)).appTop) ≫
          (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom := by
        rw [← hΓ]
    _ = P.U.topIso.inv ≫ P.hU.isoSpec.inv.appTop ≫
          (Scheme.ΓSpecIso Γ(E.E, P.U)).hom ≫
          CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            P.chartRing →ₐ[P.baseRing]
              P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom := by
        rw [Category.assoc, Scheme.ΓSpecIso_naturality]
        rfl
    _ = CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom := by
        rw [← Category.assoc, ← Category.assoc,
          show (P.U.topIso.inv ≫ P.hU.isoSpec.inv.appTop) ≫
              (Scheme.ΓSpecIso Γ(E.E, P.U)).hom = 𝟙 _ from
            (Category.assoc _ _ _).trans P.topIso_isoSpec_appTop_ΓSpecIso,
          Category.id_comp]

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
