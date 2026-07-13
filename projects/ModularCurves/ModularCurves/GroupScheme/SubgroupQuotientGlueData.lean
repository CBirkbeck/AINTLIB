/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.SubgroupQuotientGlue

/-!
# The subgroup-scheme quotient glue data (`[HG-C4c-2]` S5)

The option-γ glue: one free affine chart patch per point of `E` (the C3f cover
`exists_affineChartPatch_free`, parametrized by a killing integer `(N, hkill)`), one patch
quotient per point, glued along the saturated images of the pairwise stable windows
`U i ⊓ U j`. The transitions are `glueTransition`s (cross the window comparison, widen,
project, descend); every glue-data identity reduces along `restrictedπ_hom_ext` to a
window-level identity, which `window_hom_ext` closes because every window map in sight
fixes the ambient curve.
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
variable (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The chosen free affine chart patch around a point of the curve (option-γ cover). -/
noncomputable def gluePatch (x : ↥E.E) : G.AffineChartPatch :=
  (G.exists_affineChartPatch_free N hkill x).choose

theorem mem_gluePatch (x : ↥E.E) : x ∈ (G.gluePatch N hkill x).U :=
  (G.exists_affineChartPatch_free N hkill x).choose_spec.1

instance free_gluePatch (x : ↥E.E) :
    Module.Free (G.gluePatch N hkill x).baseRing (G.gluePatch N hkill x).groupRing :=
  (G.exists_affineChartPatch_free N hkill x).choose_spec.2

/-- The pairwise glue windows are stable. -/
theorem glueW_stable (i j : ↥E.E) :
    G.IsStableOpen ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U) :=
  ((G.gluePatch N hkill i).hstable).inf G ((G.gluePatch N hkill j).hstable)

/-- The triple-window shuffle inequality (cyclic re-bracketing of the triple overlap). -/
theorem glue_triple_le {A B C : E.E.Opens} : (A ⊓ B) ⊓ (A ⊓ C) ≤ (B ⊓ C) ⊓ (B ⊓ A) :=
  le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))

/-- The `(i, i)` image open is everything: the projection is surjective and the full
chart is its own window. -/
theorem imageOpens_glueW_self_eq_top (i : ↥E.E) :
    (G.gluePatch N hkill i).imageOpens (G.glueW_stable N hkill i i) inf_le_left = ⊤ := by
  refine TopologicalSpace.Opens.ext ?_
  rw [(G.gluePatch N hkill i).coe_imageOpens]
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨x, rfl⟩ :=
    (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable).surjective q
  refine ⟨x, ?_, rfl⟩
  show (G.gluePatch N hkill i).U.ι.base x
    ∈ (G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill i).U
  have hx : (G.gluePatch N hkill i).U.ι.base x ∈ (G.gluePatch N hkill i).U := by
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  exact ⟨hx, hx⟩

/-- The pairwise transition of the quotient glue data. -/
noncomputable def glueT (i j : ↥E.E) :
    ((G.gluePatch N hkill i).imageOpens (G.glueW_stable N hkill i j)
        inf_le_left).toScheme ⟶
      ((G.gluePatch N hkill j).imageOpens (G.glueW_stable N hkill j i)
        inf_le_left).toScheme :=
  (G.gluePatch N hkill i).glueTransition (G.gluePatch N hkill j)
    (G.glueW_stable N hkill i j) (G.glueW_stable N hkill j i)
    inf_le_left inf_le_right (le_inf inf_le_right inf_le_left) inf_le_left

/-- The triple transition of the quotient glue data, on intersection image opens. -/
noncomputable def glueT3 (i j k : ↥E.E) :
    ((G.gluePatch N hkill i).imageOpens
        ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
        (inf_le_left.trans inf_le_left)).toScheme ⟶
      ((G.gluePatch N hkill j).imageOpens
        ((G.glueW_stable N hkill j k).inf G (G.glueW_stable N hkill j i))
        (inf_le_left.trans inf_le_left)).toScheme :=
  (G.gluePatch N hkill i).glueTransition (G.gluePatch N hkill j)
    ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
    ((G.glueW_stable N hkill j k).inf G (G.glueW_stable N hkill j i))
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    glue_triple_le (inf_le_left.trans inf_le_left)

/-- **The quotient glue data**: one patch quotient per point, glued along the saturated
images of the pairwise windows. -/
noncomputable def quotientGlueData : Scheme.GlueData where
  J := ↥E.E
  U i := G.localQuotientOpen (G.gluePatch N hkill i).hstable
  V ij := ((G.gluePatch N hkill ij.1).imageOpens
    (G.glueW_stable N hkill ij.1 ij.2) inf_le_left).toScheme
  f i j := ((G.gluePatch N hkill i).imageOpens
    (G.glueW_stable N hkill i j) inf_le_left).ι
  f_id i := by
    rw [G.imageOpens_glueW_self_eq_top N hkill i, ← Scheme.topIso_hom]
    infer_instance
  t := G.glueT N hkill
  t_id i := by
    refine (G.gluePatch N hkill i).restrictedπ_hom_ext
      (G.glueW_stable N hkill i i) inf_le_left ?_
    rw [Category.comp_id, glueT,
      (G.gluePatch N hkill i).restrictedπ_glueTransition (G.gluePatch N hkill i)
        (G.glueW_stable N hkill i i) (G.glueW_stable N hkill i i)
        inf_le_left inf_le_right (le_inf inf_le_right inf_le_left) inf_le_left]
    have hwin : ((G.gluePatch N hkill i).windowCrossIso (G.gluePatch N hkill i)
          inf_le_left inf_le_right).hom ≫
        (G.gluePatch N hkill i).U.toScheme.homOfLE
          (Scheme.Hom.preimage_mono (G.gluePatch N hkill i).U.ι
            (le_inf inf_le_right inf_le_left)) = 𝟙 _ :=
      (G.gluePatch N hkill i).window_hom_ext (by
        simp only [Category.assoc, Category.id_comp, Scheme.homOfLE_ι_assoc,
          AffineChartPatch.windowCrossIso_hom_ι])
    rw [← Category.assoc, hwin, Category.id_comp]
  t' i j k :=
    ((G.gluePatch N hkill i).imageOpensPullbackIso
      (G.glueW_stable N hkill i j) (G.glueW_stable N hkill i k)
      inf_le_left inf_le_left).inv ≫
    G.glueT3 N hkill i j k ≫
    ((G.gluePatch N hkill j).imageOpensPullbackIso
      (G.glueW_stable N hkill j k) (G.glueW_stable N hkill j i)
      inf_le_left inf_le_left).hom
  t_fac i j k := by
    rw [Category.assoc, Category.assoc,
      (G.gluePatch N hkill j).imageOpensPullbackIso_hom_snd
        (G.glueW_stable N hkill j k) (G.glueW_stable N hkill j i)
        inf_le_left inf_le_left]
    rw [show pullback.fst ((G.gluePatch N hkill i).imageOpens
          (G.glueW_stable N hkill i j) inf_le_left).ι
          ((G.gluePatch N hkill i).imageOpens
          (G.glueW_stable N hkill i k) inf_le_left).ι
        = ((G.gluePatch N hkill i).imageOpensPullbackIso
            (G.glueW_stable N hkill i j) (G.glueW_stable N hkill i k)
            inf_le_left inf_le_left).inv ≫
          (G.localQuotientOpen (G.gluePatch N hkill i).hstable).homOfLE
            ((G.gluePatch N hkill i).imageOpens_mono _ _ _ _ inf_le_left) from by
      rw [Iso.eq_inv_comp]
      exact (G.gluePatch N hkill i).imageOpensPullbackIso_hom_fst
        (G.glueW_stable N hkill i j) (G.glueW_stable N hkill i k)
        inf_le_left inf_le_left]
    rw [Category.assoc, cancel_epi]
    -- both sides now live under the source triple image open
    refine (G.gluePatch N hkill i).restrictedπ_hom_ext
      ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
      (inf_le_left.trans inf_le_left) ?_
    simp only [Category.assoc]
    rw [glueT3, glueT]
    rw [(G.gluePatch N hkill i).restrictedπ_glueTransition_assoc (G.gluePatch N hkill j)
      ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
      ((G.glueW_stable N hkill j k).inf G (G.glueW_stable N hkill j i))
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      glue_triple_le (inf_le_left.trans inf_le_left)]
    rw [← (G.gluePatch N hkill j).homOfLE_restrictedπ
      ((G.glueW_stable N hkill j k).inf G (G.glueW_stable N hkill j i))
      (G.glueW_stable N hkill j i) (inf_le_left.trans inf_le_left) inf_le_left
      inf_le_right]
    rw [← (G.gluePatch N hkill i).homOfLE_restrictedπ_assoc
      ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
      (G.glueW_stable N hkill i j) (inf_le_left.trans inf_le_left) inf_le_left
      inf_le_left]
    rw [(G.gluePatch N hkill i).restrictedπ_glueTransition (G.gluePatch N hkill j)
      (G.glueW_stable N hkill i j) (G.glueW_stable N hkill j i)
      inf_le_left inf_le_right (le_inf inf_le_right inf_le_left) inf_le_left]
    simp only [← Category.assoc]
    congr 1
    refine (G.gluePatch N hkill i).window_hom_ext ?_
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc,
      AffineChartPatch.windowCrossIso_hom_ι_assoc,
      AffineChartPatch.windowCrossIso_hom_ι]
  cocycle i j k := by
    have hT : G.glueT3 N hkill i j k ≫ G.glueT3 N hkill j k i ≫
        G.glueT3 N hkill k i j = 𝟙 _ := by
      refine (G.gluePatch N hkill i).restrictedπ_hom_ext
        ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
        (inf_le_left.trans inf_le_left) ?_
      rw [Category.comp_id, glueT3, glueT3, glueT3]
      rw [(G.gluePatch N hkill i).restrictedπ_glueTransition_assoc]
      rw [(G.gluePatch N hkill j).restrictedπ_glueTransition_assoc]
      rw [(G.gluePatch N hkill k).restrictedπ_glueTransition]
      simp only [← Category.assoc]
      refine ((congrArg (· ≫ (G.gluePatch N hkill i).restrictedπ
        ((G.glueW_stable N hkill i j).inf G (G.glueW_stable N hkill i k))
        (inf_le_left.trans inf_le_left))
        ((G.gluePatch N hkill i).window_hom_ext (h := 𝟙 _) ?_)).trans
        (Category.id_comp _))
      simp only [Category.assoc, Category.id_comp, Scheme.homOfLE_ι_assoc,
        AffineChartPatch.windowCrossIso_hom_ι_assoc,
        AffineChartPatch.windowCrossIso_hom_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hT]
    exact Iso.inv_hom_id _
  f_open i j := inferInstance

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
