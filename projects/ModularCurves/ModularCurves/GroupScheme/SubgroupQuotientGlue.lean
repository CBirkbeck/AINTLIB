/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.SubgroupQuotientConstruction
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The subgroup-scheme quotient glue: the equalizer-subring model (`[HG-C4c-2]`)

Design v10.190-G0. For **any** stable open `W ⊆ E` the quotient functions are the equalizer
subring of the two restricted-leg section maps — no affineness, no Künneth:
`quotientRing W := eqLocus Γ(act|_W) Γ(pr|_W)`, glued via restriction-descended transitions
on the `ForMathlib/SchemeQuotient` pattern. The Hopf layer (C4a/C4b, proven) enters only
through the per-affine-patch comparison `quotientRing P.U = coinvariants P.chartCoaction`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

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

/-- **The quotient projection of a stable open** (`[HG-C4c-2]` step 4b): the scheme of `W`
maps to the spectrum of its invariant functions through the section inclusion. -/
noncomputable def localQuotientOpenπ {W : E.E.Opens} (hW : G.IsStableOpen W) :
    W.toScheme ⟶ G.localQuotientOpen hW :=
  W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)

/-- The quotient projections commute with the window inclusions and transitions. -/
theorem homOfLE_localQuotientOpenπ {W W' : E.E.Opens} (hW : G.IsStableOpen W)
    (hW' : G.IsStableOpen W') (hle : W ≤ W') :
    E.E.homOfLE hle ≫ G.localQuotientOpenπ hW'
      = G.localQuotientOpenπ hW ≫ G.localQuotientMapW hW hW' hle := by
  rw [localQuotientOpenπ, localQuotientOpenπ, localQuotientMapW]
  -- the ring square: restriction commutes with the subring inclusions
  have hring : CommRingCat.ofHom (G.quotientRing hW').subtype ≫
      E.E.presheaf.map (homOfLE hle).op
      = CommRingCat.ofHom
          { toFun := fun b => ⟨(E.E.presheaf.map (homOfLE hle).op).hom b.1,
              G.mem_quotientRing_of_res hW hW' hle b.2⟩
            map_one' := Subtype.ext (map_one _)
            map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
            map_zero' := Subtype.ext (map_zero _)
            map_add' := fun x y => Subtype.ext (map_add _ _ _) } ≫
        CommRingCat.ofHom (G.quotientRing hW).subtype := by
    ext b
    rfl
  calc E.E.homOfLE hle ≫ W'.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (G.quotientRing hW').subtype)
      = (E.E.homOfLE hle ≫ W'.toSpecΓ) ≫
        Spec.map (CommRingCat.ofHom (G.quotientRing hW').subtype) :=
        (Category.assoc _ _ _).symm
    _ = (W.toSpecΓ ≫ Spec.map (E.E.presheaf.map (homOfLE hle).op)) ≫
        Spec.map (CommRingCat.ofHom (G.quotientRing hW').subtype) :=
        congrArg (· ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW').subtype))
          (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map W W' hle).symm
    _ = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW').subtype ≫
          E.E.presheaf.map (homOfLE hle).op) := by
        rw [Category.assoc, ← Spec.map_comp]
    _ = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
          { toFun := fun b => ⟨(E.E.presheaf.map (homOfLE hle).op).hom b.1,
              G.mem_quotientRing_of_res hW hW' hle b.2⟩
            map_one' := Subtype.ext (map_one _)
            map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
            map_zero' := Subtype.ext (map_zero _)
            map_add' := fun x y => Subtype.ext (map_add _ _ _) } ≫
          CommRingCat.ofHom (G.quotientRing hW).subtype) := by
        rw [hring]
    _ = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype) ≫
          Spec.map (CommRingCat.ofHom
          { toFun := fun b => ⟨(E.E.presheaf.map (homOfLE hle).op).hom b.1,
              G.mem_quotientRing_of_res hW hW' hle b.2⟩
            map_one' := Subtype.ext (map_one _)
            map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
            map_zero' := Subtype.ext (map_zero _)
            map_add' := fun x y => Subtype.ext (map_add _ _ _) }) := by
        rw [Spec.map_comp]
    _ = (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)) ≫
          Spec.map (CommRingCat.ofHom
          { toFun := fun b => ⟨(E.E.presheaf.map (homOfLE hle).op).hom b.1,
              G.mem_quotientRing_of_res hW hW' hle b.2⟩
            map_one' := Subtype.ext (map_one _)
            map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
            map_zero' := Subtype.ext (map_zero _)
            map_add' := fun x y => Subtype.ext (map_add _ _ _) }) :=
        (Category.assoc _ _ _).symm

/-- **The quotient projection coequalizes the restricted action pair** — the eqLocus does
so by definition, transported to schemes by `toSpecΓ` naturality (`toSpecΓ_SpecMap_appLE`). -/
theorem restrictedAction_localQuotientOpenπ {W : E.E.Opens} (hW : G.IsStableOpen W) :
    G.restrictedAction hW ≫ G.localQuotientOpenπ hW
      = G.restrictedProj W ≫ G.localQuotientOpenπ hW := by
  have hring : CommRingCat.ofHom (G.quotientRing hW).subtype ≫ G.actRing hW
      = CommRingCat.ofHom (G.quotientRing hW).subtype ≫ G.prRing W := by
    ext x
    exact x.2
  have hactnat := Scheme.Opens.toSpecΓ_SpecMap_appLE G.translationAction.left W
    (G.actionProj.left ⁻¹ᵁ W) hW
  have hprnat := Scheme.Opens.toSpecΓ_SpecMap_appLE G.actionProj.left W
    (G.actionProj.left ⁻¹ᵁ W) le_rfl
  show G.restrictedAction hW ≫ W.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)
    = G.restrictedProj W ≫ W.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)
  calc G.restrictedAction hW ≫ W.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)
      = (G.restrictedAction hW ≫ W.toSpecΓ) ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype) :=
        (Category.assoc _ _ _).symm
    _ = ((G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (G.actRing hW)) ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype) :=
        congrArg (· ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)) hactnat.symm
    _ = (G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype ≫ G.actRing hW) :=
        (Category.assoc _ _ _).trans
          (congrArg ((G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫ ·) (Spec.map_comp _ _).symm)
    _ = (G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype ≫ G.prRing W) :=
        congrArg (fun m => (G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫ Spec.map m) hring
    _ = ((G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (G.prRing W)) ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype) :=
        (congrArg ((G.actionProj.left ⁻¹ᵁ W).toSpecΓ ≫ ·) (Spec.map_comp _ _)).trans
          (Category.assoc _ _ _).symm
    _ = (G.restrictedProj W ≫ W.toSpecΓ) ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype) :=
        congrArg (· ≫ Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype)) hprnat
    _ = G.restrictedProj W ≫ W.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (G.quotientRing hW).subtype) :=
        Category.assoc _ _ _

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

/-- `kappa` is an isomorphism (a composite of section isomorphisms). -/
instance : IsIso P.kappa := by
  haveI h1 : IsIso ((G.chartPullbackIso P.U).inv.appTop) :=
    inferInstanceAs (IsIso (Scheme.Γ.map (G.chartPullbackIso P.U).inv.op))
  haveI h2 : IsIso (P.chartSpecIso.inv.appTop) :=
    inferInstanceAs (IsIso (Scheme.Γ.map P.chartSpecIso.inv.op))
  rw [kappa]
  infer_instance

/-- **The per-patch comparison** (`[HG-C4c-2]` step 3c): on an affine chart patch the
equalizer-subring quotient model agrees with the Hopf co-invariants. Elementwise: both
legs of the equalizer are pinned under the (injective) Künneth comparison `kappa` by
`actRing_kappa`/`prRing_kappa`, and the comodule-convention swap is definitional. -/
theorem quotientRing_eq_coinvariants :
    G.quotientRing P.hstable = (coinvariants P.chartCoaction).toSubring := by
  ext b
  constructor
  · intro hb
    show b ∈ coinvariants P.chartCoaction
    rw [mem_coinvariants]
    -- from `actRing b = prRing b`, apply `kappa` and the two leg identifications
    have h1 : P.kappa.hom ((G.actRing P.hstable).hom b)
        = P.kappa.hom ((G.prRing P.U).hom b) := congrArg P.kappa.hom hb
    have h2 : P.coactionRing.hom b
        = (Algebra.TensorProduct.includeRight :
            P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing) b := by
      have hA := congrArg (fun m => (CommRingCat.Hom.hom m) b) (P.actRing_kappa)
      have hB := congrArg (fun m => (CommRingCat.Hom.hom m) b) (P.prRing_kappa)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hA hB
      exact hA.symm.trans (h1.trans hB)
    -- flip the group-first identity to the comodule convention
    have h3 : P.chartCoaction b
        = (Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing)
          (P.coactionRing.hom b) := rfl
    rw [h3, h2]
    rfl
  · intro hb
    have hb' : P.chartCoaction b = b ⊗ₜ[P.baseRing] 1 := mem_coinvariants.mp hb
    -- flip to the group-first co-action ring
    have hP : P.coactionRing.hom b = (1 : P.groupRing) ⊗ₜ[P.baseRing] b :=
      (Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).injective hb'
    show (G.actRing P.hstable).hom b = (G.prRing P.U).hom b
    -- both sides agree after the (injective) `kappa`
    have hA := congrArg (fun m => (CommRingCat.Hom.hom m) b) (P.actRing_kappa)
    have hB := congrArg (fun m => (CommRingCat.Hom.hom m) b) (P.prRing_kappa)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hA hB
    have hκ : P.kappa.hom ((G.actRing P.hstable).hom b)
        = P.kappa.hom ((G.prRing P.U).hom b) := by
      rw [hA, hB, hP]
      rfl
    haveI : IsIso P.kappa := inferInstance
    exact ((ConcreteCategory.isIso_iff_bijective P.kappa).mp inferInstance).injective hκ

/-- The carrier equivalence between the subalgebra-as-subring and the subalgebra. -/
def coinvSubringEquiv :
    (coinvariants P.chartCoaction).toSubring ≃+* coinvariants P.chartCoaction where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The glue-model local quotient of a patch is the Hopf-model one (from the subring
equality, as an honest ring equivalence — no `eqToHom`). -/
noncomputable def localQuotientOpenIso [Module.Free P.baseRing P.groupRing] :
    G.localQuotientOpen P.hstable ≅ P.localQuotient where
  hom := Spec.map (CommRingCat.ofHom
    (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
      P.coinvSubringEquiv).symm.toRingHom))
  inv := Spec.map (CommRingCat.ofHom
    (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
      P.coinvSubringEquiv).toRingHom))
  hom_inv_id :=
    (Spec.map_comp (CommRingCat.ofHom
        (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
          P.coinvSubringEquiv).toRingHom))
      (CommRingCat.ofHom
        (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
          P.coinvSubringEquiv).symm.toRingHom))).symm.trans (by
      rw [show (CommRingCat.ofHom
            (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
              P.coinvSubringEquiv).toRingHom) ≫
          CommRingCat.ofHom
            (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
              P.coinvSubringEquiv).symm.toRingHom)) = 𝟙 _ from by
        ext x
        exact congrArg Subtype.val
          (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
            P.coinvSubringEquiv).symm_apply_apply x)]
      exact Spec.map_id _)
  inv_hom_id :=
    (Spec.map_comp (CommRingCat.ofHom
        (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
          P.coinvSubringEquiv).symm.toRingHom))
      (CommRingCat.ofHom
        (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
          P.coinvSubringEquiv).toRingHom))).symm.trans (by
      rw [show (CommRingCat.ofHom
            (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
              P.coinvSubringEquiv).symm.toRingHom) ≫
          CommRingCat.ofHom
            (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
              P.coinvSubringEquiv).toRingHom)) = 𝟙 _ from by
        ext x
        exact congrArg Subtype.val
          (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
            P.coinvSubringEquiv).apply_symm_apply x)]
      exact Spec.map_id _)

/-- **`S1` — the patch quotient projection is flat and surjective**: the invariants
inclusion is faithfully flat (the Hopf–Galois property, through the step-3 comparison),
and the affine identification is an isomorphism. -/
theorem flat_and_surjective_localQuotientOpenπ [Module.Free P.baseRing P.groupRing] :
    Flat (G.localQuotientOpenπ P.hstable) ∧
      AlgebraicGeometry.Surjective (G.localQuotientOpenπ P.hstable) := by
  -- faithful flatness of the invariants inclusion, in the glue spelling
  have h1 : Flat (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)) ∧
      AlgebraicGeometry.Surjective
        (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)) := by
    rw [P.quotientRing_eq_coinvariants]
    have hff : (CommRingCat.ofHom (algebraMap (coinvariants P.chartCoaction)
        P.chartRing)).hom.FaithfullyFlat := by
      rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
      exact P.isHopfGalois_chartCoaction.faithfullyFlat
    exact (flat_and_surjective_SpecMap_iff _).mpr hff
  obtain ⟨hflat, hsurj⟩ := h1
  haveI : IsAffine P.U.toScheme := P.hU
  haveI := P.isIso_toSpecΓ_U
  haveI : IsOpenImmersion P.U.toSpecΓ := inferInstance
  haveI : Flat P.U.toSpecΓ := inferInstance
  haveI : AlgebraicGeometry.Surjective P.U.toSpecΓ := inferInstance
  haveI := hflat
  haveI := hsurj
  constructor
  · rw [FiniteLocallyFreeSubgroup.localQuotientOpenπ]
    exact @Flat.comp _ _ _ P.U.toSpecΓ
      (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype))
      inferInstance hflat
  · rw [FiniteLocallyFreeSubgroup.localQuotientOpenπ]
    exact ⟨((Spec.map (CommRingCat.ofHom
      (G.quotientRing P.hstable).subtype)).surjective).comp P.U.toSpecΓ.surjective⟩

/-- **`S2`-alignment: the glue projection is the Hopf projection under the patch
identification** — `eqToHom` naturality across the subring equality. -/
theorem localQuotientOpenπ_iso [Module.Free P.baseRing P.groupRing] :
    G.localQuotientOpenπ P.hstable ≫ P.localQuotientOpenIso.hom = P.localQuotientπ := by
  have hmid : Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype) ≫
      Spec.map (CommRingCat.ofHom
        (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
          P.coinvSubringEquiv).symm.toRingHom))
      = specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft := by
    refine (Spec.map_comp _ _).symm.trans ?_
    show Spec.map _ = Spec.map (CommRingCat.ofHom
      (AlgHom.equalizer P.chartCoaction
        (Algebra.TensorProduct.includeLeft :
          P.chartRing →ₐ[P.baseRing]
            P.chartRing ⊗[P.baseRing] P.groupRing)).val.toRingHom)
    congr 1
  show P.U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype) ≫
      Spec.map (CommRingCat.ofHom
        (((RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans
          P.coinvSubringEquiv).symm.toRingHom))
    = P.hU.isoSpec.hom ≫ specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft
  exact (congrArg (P.U.toSpecΓ ≫ ·) hmid).trans
    (congrArg (· ≫ specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft)
      P.hU.isoSpec_hom.symm)

/-- **`S2`-⟹ — the orbit lemma**: points of a free patch identified by the quotient
projection lie in a common translation orbit. Kernel-pair transport: the fibre product of
`specEqualizerπ` against itself is the chart groupoid (`isKernelPair_specEqualizerπ`),
points of pullbacks surject onto compatible pairs, the tensor-swap re-orders the apex, and
the two C4b bridge legs identify the kernel-pair legs with the restricted action pair. -/
theorem exists_orbit_of_localQuotientOpenπ_eq [Module.Free P.baseRing P.groupRing]
    {x y : ↥P.U.toScheme}
    (h : (G.localQuotientOpenπ P.hstable).base x
      = (G.localQuotientOpenπ P.hstable).base y) :
    ∃ p : ↥((G.actionProj.left ⁻¹ᵁ P.U).toScheme),
      (G.restrictedAction P.hstable).base p = x ∧ (G.restrictedProj P.U).base p = y := by
  -- (1) move to the Hopf projection through the alignment
  have hHopf : P.localQuotientπ.base x = P.localQuotientπ.base y := by
    have hx := congrArg (fun m : P.U.toScheme ⟶ P.localQuotient => m.base x)
      P.localQuotientOpenπ_iso
    have hy := congrArg (fun m : P.U.toScheme ⟶ P.localQuotient => m.base y)
      P.localQuotientOpenπ_iso
    simp only [Scheme.Hom.comp_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg P.localQuotientOpenIso.hom.base h
  -- (2) the `Spec`-side points
  have hEq : (specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft).base
        (P.hU.isoSpec.hom.base x)
      = (specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft).base
        (P.hU.isoSpec.hom.base y) := by
    have hx : P.localQuotientπ.base x
        = (specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft).base
          (P.hU.isoSpec.hom.base x) := by
      rw [localQuotientπ]
      exact Scheme.Hom.comp_apply _ _ _
    have hy : P.localQuotientπ.base y
        = (specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft).base
          (P.hU.isoSpec.hom.base y) := by
      rw [localQuotientπ]
      exact Scheme.Hom.comp_apply _ _ _
    rw [← hx, ← hy]
    exact hHopf
  -- point-application helper (typed, to avoid metavariable field projections)
  have happ : ∀ {X Y : Scheme.{u}} {f g : X ⟶ Y}, f = g → ∀ t, f.base t = g.base t :=
    fun h t => by rw [h]
  -- (3) a kernel-pair point above the pair
  have KP := isKernelPair_specEqualizerπ P.chartCoaction P.isHopfGalois_chartCoaction
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft)
    (g := specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft)
    (P.hU.isoSpec.hom.base x) (P.hU.isoSpec.hom.base y) hEq
  set q := KP.isoPullback.inv.base z with hqdef
  have hcancel : KP.isoPullback.hom.base q = z := by
    rw [hqdef, ← Scheme.Hom.comp_apply]
    have := happ KP.isoPullback.inv_hom_id z
    simpa using this
  have hq1 : (Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom)).base q
      = P.hU.isoSpec.hom.base x := by
    have h := happ KP.isoPullback_hom_fst q
    simp only [Scheme.Hom.comp_apply] at h
    rw [hcancel] at h
    exact h.symm.trans hz1
  have hq2 : (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        P.chartRing →ₐ[P.baseRing]
          P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom)).base q
      = P.hU.isoSpec.hom.base y := by
    have h := happ KP.isoPullback_hom_snd q
    simp only [Scheme.Hom.comp_apply] at h
    rw [hcancel] at h
    exact h.symm.trans hz2
  -- (4) re-order the apex through the tensor swap
  have hswap₁ : Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom)
      = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.comm P.baseRing P.groupRing
            P.chartRing).toAlgHom.toRingHom)) ≫ Spec.map P.coactionRing := by
    rw [← Spec.map_comp]
    rfl
  have hswap₂ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        P.chartRing →ₐ[P.baseRing]
          P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom)
      = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.comm P.baseRing P.groupRing
            P.chartRing).toAlgHom.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
  set q' := (Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.comm P.baseRing P.groupRing
      P.chartRing).toAlgHom.toRingHom))).base q with hq'def
  have hq1' : (Spec.map P.coactionRing).base q' = P.hU.isoSpec.hom.base x := by
    have h := happ hswap₁ q
    simp only [Scheme.Hom.comp_apply] at h
    rw [hq'def, ← h]
    exact hq1
  have hq2' : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom)).base q'
      = P.hU.isoSpec.hom.base y := by
    have h := happ hswap₂ q
    simp only [Scheme.Hom.comp_apply] at h
    rw [hq'def, ← h]
    exact hq2
  -- (5) the orbit point, through the Künneth identifications
  refine ⟨(G.chartPullbackIso P.U).inv.base (P.chartSpecIso.inv.base q'), ?_, ?_⟩
  · -- the action leg, through the coaction bridge
    have hbr := happ P.spec_coactionRing_isoSpec_inv q'
    simp only [Scheme.Hom.comp_apply] at hbr
    rw [hq1'] at hbr
    have hxx : P.hU.isoSpec.inv.base (P.hU.isoSpec.hom.base x) = x := by
      rw [← Scheme.Hom.comp_apply]
      have := happ P.hU.isoSpec.hom_inv_id x
      simpa using this
    rw [hxx] at hbr
    have hCCS : P.chartCoactionSpec.base q'
        = (G.restrictedAction P.hstable).base
          ((G.chartPullbackIso P.U).inv.base (P.chartSpecIso.inv.base q')) := by
      rw [chartCoactionSpec]
      simp only [Scheme.Hom.comp_apply]
    rw [← hCCS]
    exact hbr.symm
  · -- the projection leg, through the raw snd bridge
    have hbr := happ
      ((congrArg (P.chartSpecIso.inv ≫ ·) P.chartPullbackIso_inv_restrictedProj).trans
        P.chartSpecIso_inv_snd) q'
    simp only [Scheme.Hom.comp_apply] at hbr
    rw [hq2'] at hbr
    have hyy : P.hU.isoSpec.inv.base (P.hU.isoSpec.hom.base y) = y := by
      rw [← Scheme.Hom.comp_apply]
      have := happ P.hU.isoSpec.hom_inv_id y
      simpa using this
    rw [hyy] at hbr
    exact hbr

/-! ### Step S3 — the saturated image opens of the patch quotient -/

section ImageOpens

variable [Module.Free P.baseRing P.groupRing]

instance : Flat (G.localQuotientOpenπ P.hstable) :=
  P.flat_and_surjective_localQuotientOpenπ.1

instance : AlgebraicGeometry.Surjective (G.localQuotientOpenπ P.hstable) :=
  P.flat_and_surjective_localQuotientOpenπ.2

instance : QuasiCompact (G.localQuotientOpenπ P.hstable) := by
  haveI : IsAffine P.U.toScheme := P.hU
  haveI : IsAffine (G.localQuotientOpen P.hstable) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (G.quotientRing P.hstable))))
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

/-- Stability, at the level of groupoid points: if the projection of a point of the
restricted action object lands in a stable sub-open of the chart, so does its translate. -/
theorem restrictedAction_mem_of_restrictedProj_mem {W : E.E.Opens} (hW : G.IsStableOpen W)
    {p : ↥((G.actionProj.left ⁻¹ᵁ P.U).toScheme)}
    (hp : (G.restrictedProj P.U).base p ∈ P.U.ι ⁻¹ᵁ W) :
    (G.restrictedAction P.hstable).base p ∈ P.U.ι ⁻¹ᵁ W := by
  have hcpr : G.restrictedProj P.U ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcact : G.restrictedAction P.hstable ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hpr : P.U.ι.base ((G.restrictedProj P.U).base p)
      = G.actionProj.left.base ((G.actionProj.left ⁻¹ᵁ P.U).ι.base p) :=
    ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
      (fun m : (G.actionProj.left ⁻¹ᵁ P.U).toScheme ⟶ E.E => m.base p) hcpr)).trans
      (Scheme.Hom.comp_apply _ _ _)
  have hact : P.U.ι.base ((G.restrictedAction P.hstable).base p)
      = G.translationAction.left.base ((G.actionProj.left ⁻¹ᵁ P.U).ι.base p) :=
    ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
      (fun m : (G.actionProj.left ⁻¹ᵁ P.U).toScheme ⟶ E.E => m.base p) hcact)).trans
      (Scheme.Hom.comp_apply _ _ _)
  have hq : (G.actionProj.left ⁻¹ᵁ P.U).ι.base p ∈ G.actionProj.left ⁻¹ᵁ W := by
    show G.actionProj.left.base _ ∈ W
    rw [← hpr]
    exact hp
  have hq' := hW hq
  show P.U.ι.base _ ∈ W
  rw [hact]
  exact hq'

/-- **Saturation of the window** (`S3`): the `π`-preimage of the `π`-image of a stable
window is the window — the fibres of the patch quotient projection are the orbits
(`exists_orbit_of_localQuotientOpenπ_eq`) and the window is stable. -/
theorem preimage_image_window {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (G.localQuotientOpenπ P.hstable).base ⁻¹'
        ((G.localQuotientOpenπ P.hstable).base '' ((P.U.ι ⁻¹ᵁ W : P.U.toScheme.Opens) :
          Set ↥P.U.toScheme))
      = ((P.U.ι ⁻¹ᵁ W : P.U.toScheme.Opens) : Set ↥P.U.toScheme) := by
  apply Set.Subset.antisymm
  · rintro x ⟨w, hwmem, hww⟩
    obtain ⟨p, hact, hpr⟩ := P.exists_orbit_of_localQuotientOpenπ_eq hww.symm
    have := P.restrictedAction_mem_of_restrictedProj_mem hW (p := p) (by rw [hpr]; exact hwmem)
    rw [hact] at this
    exact this
  · intro w hw
    exact ⟨w, hw, rfl⟩

/-- **The saturated image open** (`S3`): the image in the patch quotient of a stable
sub-open of the chart. Open because the quotient projection is a topological quotient map
(flat + surjective + quasi-compact) and the window is saturated. -/
noncomputable def imageOpens {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (G.localQuotientOpen P.hstable).Opens :=
  ⟨(G.localQuotientOpenπ P.hstable).base '' ((P.U.ι ⁻¹ᵁ W : P.U.toScheme.Opens) :
      Set ↥P.U.toScheme), by
    rw [← (Flat.isQuotientMap_of_surjective
      (G.localQuotientOpenπ P.hstable)).isOpen_preimage]
    show IsOpen ((G.localQuotientOpenπ P.hstable).base ⁻¹' _)
    rw [P.preimage_image_window hW hWU]
    exact (P.U.ι ⁻¹ᵁ W).2⟩

/-- The underlying set of the image open. -/
theorem coe_imageOpens {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (P.imageOpens hW hWU : Set (G.localQuotientOpen P.hstable))
      = (G.localQuotientOpenπ P.hstable).base '' ((P.U.ι ⁻¹ᵁ W : P.U.toScheme.Opens) :
          Set ↥P.U.toScheme) :=
  rfl

/-- The window is the full `π`-preimage of its image open (`Opens` form of saturation). -/
theorem preimage_imageOpens {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    G.localQuotientOpenπ P.hstable ⁻¹ᵁ P.imageOpens hW hWU = P.U.ι ⁻¹ᵁ W :=
  TopologicalSpace.Opens.ext (P.preimage_image_window hW hWU)

/-- The range of the first projection of the window pullback is the window. -/
theorem range_fst_imageOpens {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    Set.range (pullback.fst (G.localQuotientOpenπ P.hstable)
        (P.imageOpens hW hWU).ι).base
      = ((P.U.ι ⁻¹ᵁ W : P.U.toScheme.Opens) : Set ↥P.U.toScheme) := by
  have h := Scheme.Pullback.range_fst (G.localQuotientOpenπ P.hstable)
    (P.imageOpens hW hWU).ι
  rw [Scheme.Opens.range_ι] at h
  rw [h]
  exact P.preimage_image_window hW hWU

/-- **The window is the pullback of its image open** (`S3` window comparison). -/
noncomputable def windowIso {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (P.U.ι ⁻¹ᵁ W).toScheme ≅
      pullback (G.localQuotientOpenπ P.hstable) (P.imageOpens hW hWU).ι :=
  IsOpenImmersion.isoOfRangeEq (P.U.ι ⁻¹ᵁ W).ι (pullback.fst _ _)
    (by rw [Scheme.Opens.range_ι, P.range_fst_imageOpens hW hWU])

theorem windowIso_hom_fst {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (P.windowIso hW hWU).hom ≫ pullback.fst _ _ = (P.U.ι ⁻¹ᵁ W).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem windowIso_inv_ι {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (P.windowIso hW hWU).inv ≫ (P.U.ι ⁻¹ᵁ W).ι = pullback.fst _ _ :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- **The restricted quotient projection** (`S3`): the window maps onto its image open —
the corestriction of `π` through the window pullback. -/
noncomputable def restrictedπ {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    (P.U.ι ⁻¹ᵁ W).toScheme ⟶ (P.imageOpens hW hWU).toScheme :=
  (P.windowIso hW hWU).hom ≫ pullback.snd _ _

/-- The restricted projection recovers `π` under the two open inclusions. -/
@[reassoc]
theorem restrictedπ_ι {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    P.restrictedπ hW hWU ≫ (P.imageOpens hW hWU).ι
      = (P.U.ι ⁻¹ᵁ W).ι ≫ G.localQuotientOpenπ P.hstable := by
  rw [restrictedπ, Category.assoc, ← pullback.condition, ← Category.assoc,
    P.windowIso_hom_fst hW hWU]

instance {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    Flat (P.restrictedπ hW hWU) := by
  rw [restrictedπ]
  haveI : Flat (pullback.snd (G.localQuotientOpenπ P.hstable)
      (P.imageOpens hW hWU).ι) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  infer_instance

instance {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    AlgebraicGeometry.Surjective (P.restrictedπ hW hWU) := by
  rw [restrictedπ]
  haveI : AlgebraicGeometry.Surjective (pullback.snd (G.localQuotientOpenπ P.hstable)
      (P.imageOpens hW hWU).ι) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  infer_instance

instance {W : E.E.Opens} (hW : G.IsStableOpen W) (hWU : W ≤ P.U) :
    QuasiCompact (P.restrictedπ hW hWU) := by
  rw [restrictedπ]
  haveI : QuasiCompact (pullback.snd (G.localQuotientOpenπ P.hstable)
      (P.imageOpens hW hWU).ι) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  infer_instance

end ImageOpens

/-! ### Step S4 — the kernel pair of the patch quotient projection -/

section KernelPair

variable [Module.Free P.baseRing P.groupRing]

/-- **`S4` keystone — the kernel pair of the glue quotient projection on a free patch is
the restricted translation groupoid**: transport of `isKernelPair_specEqualizerπ` along
the chart identifications (apex: the Künneth chart; sides: `isoSpec`; tip: the subring
comparison `localQuotientOpenIso`). -/
theorem isKernelPair_localQuotientOpenπ :
    IsKernelPair (G.localQuotientOpenπ P.hstable)
      (G.restrictedAction P.hstable) (G.restrictedProj P.U) :=
  (isKernelPair_specEqualizerπ P.chartCoaction P.isHopfGalois_chartCoaction).of_iso'
    P.chartTensorIso P.hU.isoSpec P.hU.isoSpec P.localQuotientOpenIso
    P.chartTensorIso_hom_specMap_chartCoaction
    P.chartTensorIso_hom_specMap_includeLeft
    P.localQuotientOpenπ_iso.symm
    P.localQuotientOpenπ_iso.symm

end KernelPair

/-! ### Step S4 — descent along the restricted projection -/

section Descent

variable [Module.Free P.baseRing P.groupRing] {W : E.E.Opens}

/-- Morphisms out of the window that identify all `restrictedπ`-equal pairs descend to
the image open: `restrictedπ` is flat, surjective and quasi-compact, hence an effective
epimorphism (fpqc descent). -/
noncomputable def descRestrictedπ (hW : G.IsStableOpen W) (hWU : W ≤ P.U) {Z : Scheme.{u}}
    (h : (P.U.ι ⁻¹ᵁ W).toScheme ⟶ Z)
    (hinv : ∀ {T : Scheme.{u}} (a b : T ⟶ (P.U.ι ⁻¹ᵁ W).toScheme),
      a ≫ P.restrictedπ hW hWU = b ≫ P.restrictedπ hW hWU → a ≫ h = b ≫ h) :
    (P.imageOpens hW hWU).toScheme ⟶ Z :=
  EffectiveEpi.desc (P.restrictedπ hW hWU) h fun g₁ g₂ hg => hinv g₁ g₂ hg

@[reassoc]
theorem restrictedπ_descRestrictedπ (hW : G.IsStableOpen W) (hWU : W ≤ P.U)
    {Z : Scheme.{u}} (h : (P.U.ι ⁻¹ᵁ W).toScheme ⟶ Z)
    (hinv : ∀ {T : Scheme.{u}} (a b : T ⟶ (P.U.ι ⁻¹ᵁ W).toScheme),
      a ≫ P.restrictedπ hW hWU = b ≫ P.restrictedπ hW hWU → a ≫ h = b ≫ h) :
    P.restrictedπ hW hWU ≫ P.descRestrictedπ hW hWU h hinv = h :=
  EffectiveEpi.fac _ _ _

/-- Morphisms out of the image open are determined by precomposition with the
restricted projection. -/
theorem restrictedπ_hom_ext (hW : G.IsStableOpen W) (hWU : W ≤ P.U) {Z : Scheme.{u}}
    {q₁ q₂ : (P.imageOpens hW hWU).toScheme ⟶ Z}
    (hq : P.restrictedπ hW hWU ≫ q₁ = P.restrictedπ hW hWU ≫ q₂) : q₁ = q₂ :=
  (cancel_epi (P.restrictedπ hW hWU)).mp hq

omit [Module.Free P.baseRing P.groupRing] in
/-- The window over a stable sub-open, embedded back into the curve: the range is the
sub-open itself. -/
theorem range_window_ι (hWU : W ≤ P.U) :
    Set.range ((P.U.ι ⁻¹ᵁ W).ι ≫ P.U.ι).base = (W : Set ↥E.E) := by
  show Set.range (⇑P.U.ι.base ∘ ⇑(P.U.ι ⁻¹ᵁ W).ι.base) = (W : Set ↥E.E)
  rw [Set.range_comp, Scheme.Opens.range_ι]
  show ⇑P.U.ι.base '' (⇑P.U.ι.base ⁻¹' (W : Set ↥E.E)) = (W : Set ↥E.E)
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  exact Set.inter_eq_left.mpr (SetLike.coe_subset_coe.mpr hWU)

omit [Module.Free P.baseRing P.groupRing] in
/-- **The cross-chart window comparison**: one stable open, seen inside two chart
patches, gives canonically isomorphic windows (both are open immersions onto `W`). -/
noncomputable def windowCrossIso (P' : G.AffineChartPatch) (h1 : W ≤ P.U) (h2 : W ≤ P'.U) :
    (P.U.ι ⁻¹ᵁ W).toScheme ≅ (P'.U.ι ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((P.U.ι ⁻¹ᵁ W).ι ≫ P.U.ι) ((P'.U.ι ⁻¹ᵁ W).ι ≫ P'.U.ι)
    ((P.range_window_ι h1).trans (P'.range_window_ι h2).symm)

omit [Module.Free P.baseRing P.groupRing] in
@[reassoc]
theorem windowCrossIso_hom_ι (P' : G.AffineChartPatch) (h1 : W ≤ P.U) (h2 : W ≤ P'.U) :
    (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι ≫ P'.U.ι
      = (P.U.ι ⁻¹ᵁ W).ι ≫ P.U.ι := by
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac ((P.U.ι ⁻¹ᵁ W).ι ≫ P.U.ι)
    ((P'.U.ι ⁻¹ᵁ W).ι ≫ P'.U.ι) ((P.range_window_ι h1).trans (P'.range_window_ι h2).symm)
  rw [← Category.assoc]
  exact h

/-- **The master descent condition** — pairs identified by one patch's restricted
projection are identified by any other patch's, across the window comparison. The pair
lifts to the translation groupoid (`isKernelPair_localQuotientOpenπ`), the groupoid
element transfers to the other chart through the ambient curve, and invariance
(`restrictedAction_localQuotientOpenπ`) collapses it there. -/
theorem cross_desc_condition (P' : G.AffineChartPatch)
    [Module.Free P'.baseRing P'.groupRing]
    (hW : G.IsStableOpen W) (h1 : W ≤ P.U) (h2 : W ≤ P'.U)
    {T : Scheme.{u}} (a b : T ⟶ (P.U.ι ⁻¹ᵁ W).toScheme)
    (hab : a ≫ P.restrictedπ hW h1 = b ≫ P.restrictedπ hW h1) :
    a ≫ (P.windowCrossIso P' h1 h2).hom ≫ P'.restrictedπ hW h2
      = b ≫ (P.windowCrossIso P' h1 h2).hom ≫ P'.restrictedπ hW h2 := by
  -- (0) the pair equalizes the full patch projection
  have h0 : (a ≫ (P.U.ι ⁻¹ᵁ W).ι) ≫ G.localQuotientOpenπ P.hstable
      = (b ≫ (P.U.ι ⁻¹ᵁ W).ι) ≫ G.localQuotientOpenπ P.hstable := by
    have h := congrArg (· ≫ (P.imageOpens hW h1).ι) hab
    simp only [Category.assoc] at h
    rw [P.restrictedπ_ι hW h1] at h
    simpa only [Category.assoc] using h
  -- (1) the groupoid element above the pair
  have KP := P.isKernelPair_localQuotientOpenπ
  set φ : T ⟶ (G.actionProj.left ⁻¹ᵁ P.U).toScheme :=
    KP.lift (a ≫ (P.U.ι ⁻¹ᵁ W).ι) (b ≫ (P.U.ι ⁻¹ᵁ W).ι) h0 with hφdef
  have hφa : φ ≫ G.restrictedAction P.hstable = a ≫ (P.U.ι ⁻¹ᵁ W).ι := KP.lift_fst _ _ _
  have hφb : φ ≫ G.restrictedProj P.U = b ≫ (P.U.ι ⁻¹ᵁ W).ι := KP.lift_snd _ _ _
  -- the two ambient-curve legs of the groupoid element
  have hcpr : G.restrictedProj P.U ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcact : G.restrictedAction P.hstable ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcpr' : G.restrictedProj P'.U ≫ P'.U.ι
      = (G.actionProj.left ⁻¹ᵁ P'.U).ι ≫ G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcact' : G.restrictedAction P'.hstable ≫ P'.U.ι
      = (G.actionProj.left ⁻¹ᵁ P'.U).ι ≫ G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  -- (2) transfer the groupoid element to the other chart
  have hrange : Set.range (φ ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι).base
      ⊆ Set.range (G.actionProj.left ⁻¹ᵁ P'.U).ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    show G.actionProj.left.base ((φ ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι).base t) ∈ P'.U
    rw [Scheme.Hom.comp_apply]
    have hpt : P.U.ι.base ((G.restrictedProj P.U).base (φ.base t))
        = G.actionProj.left.base ((G.actionProj.left ⁻¹ᵁ P.U).ι.base (φ.base t)) :=
      ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
        (fun m : (G.actionProj.left ⁻¹ᵁ P.U).toScheme ⟶ E.E =>
          m.base (φ.base t)) hcpr)).trans (Scheme.Hom.comp_apply _ _ _)
    rw [← hpt]
    have hmem : (G.restrictedProj P.U).base (φ.base t) ∈ P.U.ι ⁻¹ᵁ W := by
      have h : (G.restrictedProj P.U).base (φ.base t)
          = (P.U.ι ⁻¹ᵁ W).ι.base (b.base t) :=
        ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
          (fun m : T ⟶ P.U.toScheme => m.base t) hφb)).trans
          (Scheme.Hom.comp_apply _ _ _)
      rw [h]
      have hb : (P.U.ι ⁻¹ᵁ W).ι.base (b.base t)
          ∈ ((P.U.ι ⁻¹ᵁ W : P.U.toScheme.Opens) : Set ↥P.U.toScheme) :=
        (Scheme.Opens.range_ι _) ▸ ⟨b.base t, rfl⟩
      exact hb
    exact h2 hmem
  set ψ : T ⟶ (G.actionProj.left ⁻¹ᵁ P'.U).toScheme :=
    IsOpenImmersion.lift (G.actionProj.left ⁻¹ᵁ P'.U).ι
      (φ ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι) hrange with hψdef
  have hψ : ψ ≫ (G.actionProj.left ⁻¹ᵁ P'.U).ι
      = φ ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι :=
    IsOpenImmersion.lift_fac _ _ _
  -- (3) the transferred element covers the crossed pair
  have hψa : ψ ≫ G.restrictedAction P'.hstable
      = a ≫ (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι := by
    rw [← cancel_mono P'.U.ι]
    exact (Category.assoc _ _ _).trans ((congrArg (ψ ≫ ·) hcact').trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ G.translationAction.left) hψ)).trans
      ((Category.assoc _ _ _).trans ((congrArg (φ ≫ ·) hcact.symm).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.U.ι) hφa)).trans
      ((Category.assoc _ _ _).trans ((congrArg (a ≫ ·)
        (P.windowCrossIso_hom_ι P' h1 h2).symm).trans
      ((congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm))))))))
  have hψb : ψ ≫ G.restrictedProj P'.U
      = b ≫ (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι := by
    rw [← cancel_mono P'.U.ι]
    exact (Category.assoc _ _ _).trans ((congrArg (ψ ≫ ·) hcpr').trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ G.actionProj.left) hψ)).trans
      ((Category.assoc _ _ _).trans ((congrArg (φ ≫ ·) hcpr.symm).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.U.ι) hφb)).trans
      ((Category.assoc _ _ _).trans ((congrArg (b ≫ ·)
        (P.windowCrossIso_hom_ι P' h1 h2).symm).trans
      ((congrArg (b ≫ ·) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm))))))))
  -- (4) conclude by invariance on the other patch
  rw [← cancel_mono (P'.imageOpens hW h2).ι]
  simp only [Category.assoc]
  rw [P'.restrictedπ_ι hW h2]
  calc a ≫ (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι ≫
        G.localQuotientOpenπ P'.hstable
      = (a ≫ (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι) ≫
          G.localQuotientOpenπ P'.hstable := by simp only [Category.assoc]
    _ = (ψ ≫ G.restrictedAction P'.hstable) ≫ G.localQuotientOpenπ P'.hstable := by
        rw [hψa]
    _ = (ψ ≫ G.restrictedProj P'.U) ≫ G.localQuotientOpenπ P'.hstable := by
        rw [Category.assoc, Category.assoc,
          restrictedAction_localQuotientOpenπ (G := G) P'.hstable]
    _ = (b ≫ (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι) ≫
          G.localQuotientOpenπ P'.hstable := by rw [hψb]
    _ = b ≫ (P.windowCrossIso P' h1 h2).hom ≫ (P'.U.ι ⁻¹ᵁ W).ι ≫
          G.localQuotientOpenπ P'.hstable := by simp only [Category.assoc]

/-- **The generic glue transition**: cross to the other chart's window, widen along
`hle`, project. Descends along the source restricted projection by the master
condition. -/
noncomputable def glueTransition (P' : G.AffineChartPatch)
    [Module.Free P'.baseRing P'.groupRing] {W' : E.E.Opens}
    (hW : G.IsStableOpen W) (hW' : G.IsStableOpen W')
    (hWP : W ≤ P.U) (hWP' : W ≤ P'.U) (hle : W ≤ W') (hW'P' : W' ≤ P'.U) :
    (P.imageOpens hW hWP).toScheme ⟶ (P'.imageOpens hW' hW'P').toScheme :=
  P.descRestrictedπ hW hWP
    ((P.windowCrossIso P' hWP hWP').hom ≫
      P'.U.toScheme.homOfLE (Scheme.Hom.preimage_mono P'.U.ι hle) ≫
      P'.restrictedπ hW' hW'P')
    (fun a b hab => by
      rw [← cancel_mono (P'.imageOpens hW' hW'P').ι]
      have base := P.cross_desc_condition P' hW hWP hWP' a b hab
      have base' := congrArg (· ≫ (P'.imageOpens hW hWP').ι) base
      simp only [Category.assoc] at base' ⊢
      rw [P'.restrictedπ_ι hW hWP'] at base'
      rw [P'.restrictedπ_ι hW' hW'P', Scheme.homOfLE_ι_assoc]
      exact base')

@[reassoc]
theorem restrictedπ_glueTransition (P' : G.AffineChartPatch)
    [Module.Free P'.baseRing P'.groupRing] {W' : E.E.Opens}
    (hW : G.IsStableOpen W) (hW' : G.IsStableOpen W')
    (hWP : W ≤ P.U) (hWP' : W ≤ P'.U) (hle : W ≤ W') (hW'P' : W' ≤ P'.U) :
    P.restrictedπ hW hWP ≫ P.glueTransition P' hW hW' hWP hWP' hle hW'P'
      = (P.windowCrossIso P' hWP hWP').hom ≫
        P'.U.toScheme.homOfLE (Scheme.Hom.preimage_mono P'.U.ι hle) ≫
        P'.restrictedπ hW' hW'P' :=
  P.restrictedπ_descRestrictedπ hW hWP
    ((P.windowCrossIso P' hWP hWP').hom ≫
      P'.U.toScheme.homOfLE (Scheme.Hom.preimage_mono P'.U.ι hle) ≫
      P'.restrictedπ hW' hW'P')
    (fun a b hab => by
      rw [← cancel_mono (P'.imageOpens hW' hW'P').ι]
      have base := P.cross_desc_condition P' hW hWP hWP' a b hab
      have base' := congrArg (· ≫ (P'.imageOpens hW hWP').ι) base
      simp only [Category.assoc] at base' ⊢
      rw [P'.restrictedπ_ι hW hWP'] at base'
      rw [P'.restrictedπ_ι hW' hW'P', Scheme.homOfLE_ι_assoc]
      exact base')

/-- Pairs identified by the full patch projection are identified by anything
coequalizing the restricted translation pair (the kernel-pair transport of the
universal property). -/
theorem localQuotientOpenπ_desc_condition {Z : Scheme.{u}} (h : P.U.toScheme ⟶ Z)
    (hinv : G.restrictedAction P.hstable ≫ h = G.restrictedProj P.U ≫ h)
    {T : Scheme.{u}} (a b : T ⟶ P.U.toScheme)
    (hab : a ≫ G.localQuotientOpenπ P.hstable = b ≫ G.localQuotientOpenπ P.hstable) :
    a ≫ h = b ≫ h := by
  have KP := P.isKernelPair_localQuotientOpenπ
  calc a ≫ h = (KP.lift a b hab ≫ G.restrictedAction P.hstable) ≫ h := by
        rw [KP.lift_fst]
    _ = (KP.lift a b hab ≫ G.restrictedProj P.U) ≫ h := by
        rw [Category.assoc, hinv, ← Category.assoc]
    _ = b ≫ h := by rw [KP.lift_snd]

/-- **Descent through the patch quotient projection**: chart morphisms coequalizing the
restricted translation pair factor through the local quotient (fpqc effective epi). -/
noncomputable def descLocalQuotientOpenπ {Z : Scheme.{u}} (h : P.U.toScheme ⟶ Z)
    (hinv : G.restrictedAction P.hstable ≫ h = G.restrictedProj P.U ≫ h) :
    G.localQuotientOpen P.hstable ⟶ Z :=
  EffectiveEpi.desc (G.localQuotientOpenπ P.hstable) h
    (fun a b hab => P.localQuotientOpenπ_desc_condition h hinv a b hab)

@[reassoc]
theorem localQuotientOpenπ_descLocalQuotientOpenπ {Z : Scheme.{u}} (h : P.U.toScheme ⟶ Z)
    (hinv : G.restrictedAction P.hstable ≫ h = G.restrictedProj P.U ≫ h) :
    G.localQuotientOpenπ P.hstable ≫ P.descLocalQuotientOpenπ h hinv = h :=
  EffectiveEpi.fac _ _ _

/-- Morphisms out of the patch quotient are determined by precomposition with the
projection. -/
theorem localQuotientOpenπ_hom_ext {Z : Scheme.{u}}
    {q₁ q₂ : G.localQuotientOpen P.hstable ⟶ Z}
    (hq : G.localQuotientOpenπ P.hstable ≫ q₁ = G.localQuotientOpenπ P.hstable ≫ q₂) :
    q₁ = q₂ :=
  (cancel_epi (G.localQuotientOpenπ P.hstable)).mp hq

/-! ### Step S5 preliminaries — saturation arithmetic and the pullback comparison -/

omit [Module.Free P.baseRing P.groupRing] in
/-- Morphisms between windows are determined by their ambient-curve composites. -/
theorem window_hom_ext {P' : G.AffineChartPatch} {W W' : E.E.Opens}
    {g h : (P.U.ι ⁻¹ᵁ W).toScheme ⟶ (P'.U.ι ⁻¹ᵁ W').toScheme}
    (hgh : g ≫ (P'.U.ι ⁻¹ᵁ W').ι ≫ P'.U.ι = h ≫ (P'.U.ι ⁻¹ᵁ W').ι ≫ P'.U.ι) :
    g = h := by
  rw [← cancel_mono ((P'.U.ι ⁻¹ᵁ W').ι ≫ P'.U.ι)]
  simpa only [Category.assoc] using hgh

/-- **Saturation arithmetic**: the image of an intersection window is the intersection
of the images — fibres are orbits, and stable windows absorb orbit moves. -/
theorem imageOpens_inf {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) :
    P.imageOpens hW₁ h1 ⊓ P.imageOpens hW₂ h2
      = P.imageOpens (hW₁.inf G hW₂) (inf_le_left.trans h1) := by
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_inf, P.coe_imageOpens hW₁ h1, P.coe_imageOpens hW₂ h2,
    P.coe_imageOpens (hW₁.inf G hW₂) (inf_le_left.trans h1)]
  apply Set.Subset.antisymm
  · rintro p ⟨⟨x, hxA, hx⟩, ⟨y, hyB, hy⟩⟩
    obtain ⟨q, hact, hpr⟩ := P.exists_orbit_of_localQuotientOpenπ_eq
      (show (G.localQuotientOpenπ P.hstable).base y
        = (G.localQuotientOpenπ P.hstable).base x from by rw [hx, hy])
    have hyA : y ∈ P.U.ι ⁻¹ᵁ W₁ := by
      have := P.restrictedAction_mem_of_restrictedProj_mem hW₁ (p := q)
        (by rw [hpr]; exact hxA)
      rw [hact] at this
      exact this
    refine ⟨y, ?_, hy⟩
    show P.U.ι.base y ∈ W₁ ⊓ W₂
    exact ⟨hyA, hyB⟩
  · rintro p ⟨z, hz, hzp⟩
    have hz1 : P.U.ι.base z ∈ W₁ := hz.1
    have hz2 : P.U.ι.base z ∈ W₂ := hz.2
    exact ⟨⟨z, hz1, hzp⟩, ⟨z, hz2, hzp⟩⟩

/-- Image opens are monotone in the window. -/
theorem imageOpens_mono {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) (h12 : W₁ ≤ W₂) :
    P.imageOpens hW₁ h1 ≤ P.imageOpens hW₂ h2 := by
  intro p hp
  obtain ⟨x, hx, hxp⟩ := hp
  exact ⟨x, h12 hx, hxp⟩

/-- The restricted projections are natural in the window. -/
@[reassoc]
theorem homOfLE_restrictedπ {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) (h12 : W₁ ≤ W₂) :
    P.U.toScheme.homOfLE (Scheme.Hom.preimage_mono P.U.ι h12) ≫ P.restrictedπ hW₂ h2
      = P.restrictedπ hW₁ h1 ≫
        (G.localQuotientOpen P.hstable).homOfLE
          (P.imageOpens_mono hW₁ hW₂ h1 h2 h12) := by
  rw [← cancel_mono (P.imageOpens hW₂ h2).ι]
  rw [Category.assoc, P.restrictedπ_ι hW₂ h2, Category.assoc, Scheme.homOfLE_ι,
    P.restrictedπ_ι hW₁ h1, ← Category.assoc, Scheme.homOfLE_ι]

/-- **The intersection image open is the pullback of the two image opens** — the glue
model's triple comparison. -/
noncomputable def imageOpensPullbackIso {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) :
    (P.imageOpens (hW₁.inf G hW₂) (inf_le_left.trans h1)).toScheme
      ≅ pullback (P.imageOpens hW₁ h1).ι (P.imageOpens hW₂ h2).ι :=
  IsOpenImmersion.isoOfRangeEq
    (P.imageOpens (hW₁.inf G hW₂) (inf_le_left.trans h1)).ι
    (pullback.fst (P.imageOpens hW₁ h1).ι (P.imageOpens hW₂ h2).ι ≫
      (P.imageOpens hW₁ h1).ι) (by
      rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι, Scheme.Opens.range_ι, ← TopologicalSpace.Opens.coe_inf,
        P.imageOpens_inf hW₁ hW₂ h1 h2])

theorem imageOpensPullbackIso_hom_comp {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) :
    (P.imageOpensPullbackIso hW₁ hW₂ h1 h2).hom ≫
        pullback.fst (P.imageOpens hW₁ h1).ι (P.imageOpens hW₂ h2).ι ≫
          (P.imageOpens hW₁ h1).ι
      = (P.imageOpens (hW₁.inf G hW₂) (inf_le_left.trans h1)).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem imageOpensPullbackIso_hom_fst {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) :
    (P.imageOpensPullbackIso hW₁ hW₂ h1 h2).hom ≫
        pullback.fst (P.imageOpens hW₁ h1).ι (P.imageOpens hW₂ h2).ι
      = (G.localQuotientOpen P.hstable).homOfLE
          (P.imageOpens_mono (hW₁.inf G hW₂) hW₁ (inf_le_left.trans h1) h1
            inf_le_left) := by
  rw [← cancel_mono (P.imageOpens hW₁ h1).ι, Category.assoc,
    P.imageOpensPullbackIso_hom_comp hW₁ hW₂ h1 h2, Scheme.homOfLE_ι]


theorem imageOpensPullbackIso_hom_snd {W₁ W₂ : E.E.Opens} (hW₁ : G.IsStableOpen W₁)
    (hW₂ : G.IsStableOpen W₂) (h1 : W₁ ≤ P.U) (h2 : W₂ ≤ P.U) :
    (P.imageOpensPullbackIso hW₁ hW₂ h1 h2).hom ≫
        pullback.snd (P.imageOpens hW₁ h1).ι (P.imageOpens hW₂ h2).ι
      = (G.localQuotientOpen P.hstable).homOfLE
          (P.imageOpens_mono (hW₁.inf G hW₂) hW₂ (inf_le_left.trans h1) h2
            inf_le_right) := by
  rw [← cancel_mono (P.imageOpens hW₂ h2).ι, Category.assoc, ← pullback.condition,
    P.imageOpensPullbackIso_hom_comp hW₁ hW₂ h1 h2, Scheme.homOfLE_ι]

end Descent

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
