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

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
