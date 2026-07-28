/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.SubgroupQuotientGlue
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

/-! ### The glued quotient and the quotient projection -/

/-- The option-γ patch cover of the curve. -/
noncomputable def glueCover : E.E.OpenCover :=
  Scheme.Cover.mkOfCovers (↥E.E) (fun i => (G.gluePatch N hkill i).U.toScheme)
    (fun i => (G.gluePatch N hkill i).U.ι)
    (fun x => ⟨x, by
      have hx : x ∈ Set.range ⇑(G.gluePatch N hkill x).U.ι := by
        rw [Scheme.Opens.range_ι]
        exact G.mem_gluePatch N hkill x
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, hy⟩⟩)

/-- **The glued quotient** (option-γ): the scheme glued from the patch quotients. -/
noncomputable def gluedQuotient : Scheme.{u} := (G.quotientGlueData N hkill).glued

/-- The patch-quotient inclusion into the glued quotient. -/
noncomputable def gluedQuotientι (i : ↥E.E) :
    G.localQuotientOpen (G.gluePatch N hkill i).hstable ⟶ G.gluedQuotient N hkill :=
  (G.quotientGlueData N hkill).ι i

/-- The per-patch leg of the quotient projection. -/
noncomputable def gluedQuotientLeg (i : ↥E.E) :
    (G.gluePatch N hkill i).U.toScheme ⟶ G.gluedQuotient N hkill :=
  G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫ G.gluedQuotientι N hkill i

/-- The chart-pullback factors through the first window. -/
noncomputable def pullbackWindowFst (i j : ↥E.E) :
    pullback (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι ⟶
      ((G.gluePatch N hkill i).U.ι ⁻¹ᵁ
        ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U)).toScheme :=
  IsOpenImmersion.lift
    ((G.gluePatch N hkill i).U.ι ⁻¹ᵁ
      ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U)).ι
    (pullback.fst _ _) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (G.gluePatch N hkill i).U.ι.base ((pullback.fst (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι).base p)
        ∈ (G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U
      constructor
      · rw [← Scheme.Opens.range_ι]
        exact ⟨_, rfl⟩
      · have hcond : (G.gluePatch N hkill i).U.ι.base ((pullback.fst (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι).base p)
            = (G.gluePatch N hkill j).U.ι.base ((pullback.snd (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι).base p) :=
          ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
            (fun m : pullback (G.gluePatch N hkill i).U.ι
                (G.gluePatch N hkill j).U.ι ⟶ E.E => m.base p)
            pullback.condition)).trans (Scheme.Hom.comp_apply _ _ _)
        rw [hcond, ← Scheme.Opens.range_ι]
        exact ⟨_, rfl⟩)

@[reassoc]
theorem pullbackWindowFst_ι (i j : ↥E.E) :
    G.pullbackWindowFst N hkill i j ≫
        ((G.gluePatch N hkill i).U.ι ⁻¹ᵁ
          ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U)).ι
      = pullback.fst _ _ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chart-pullback factors through the second window. -/
noncomputable def pullbackWindowSnd (i j : ↥E.E) :
    pullback (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι ⟶
      ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
        ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U)).toScheme :=
  IsOpenImmersion.lift
    ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
      ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U)).ι
    (pullback.snd _ _) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (G.gluePatch N hkill j).U.ι.base ((pullback.snd (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι).base p)
        ∈ (G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U
      constructor
      · rw [← Scheme.Opens.range_ι]
        exact ⟨_, rfl⟩
      · have hcond : (G.gluePatch N hkill i).U.ι.base ((pullback.fst (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι).base p)
            = (G.gluePatch N hkill j).U.ι.base ((pullback.snd (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι).base p) :=
          ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
            (fun m : pullback (G.gluePatch N hkill i).U.ι
                (G.gluePatch N hkill j).U.ι ⟶ E.E => m.base p)
            pullback.condition)).trans (Scheme.Hom.comp_apply _ _ _)
        rw [← hcond, ← Scheme.Opens.range_ι]
        exact ⟨_, rfl⟩)

@[reassoc]
theorem pullbackWindowSnd_ι (i j : ↥E.E) :
    G.pullbackWindowSnd N hkill i j ≫
        ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
          ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U)).ι
      = pullback.snd _ _ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The compatibility of the per-patch legs over chart overlaps: both factor through the
same window point of the ambient curve, and the glue condition matches the two quotient
images. -/
theorem gluedQuotientLeg_compat (i j : ↥E.E) :
    pullback.fst (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι ≫
        G.gluedQuotientLeg N hkill i
      = pullback.snd _ _ ≫ G.gluedQuotientLeg N hkill j := by
  have hkey : G.pullbackWindowFst N hkill i j ≫
      ((G.gluePatch N hkill i).windowCrossIso (G.gluePatch N hkill j)
        inf_le_left inf_le_right).hom ≫
      ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
        ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U)).ι
      = G.pullbackWindowSnd N hkill i j ≫
        ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
          ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U)).ι := by
    rw [← cancel_mono (G.gluePatch N hkill j).U.ι]
    simp only [Category.assoc, AffineChartPatch.windowCrossIso_hom_ι]
    rw [G.pullbackWindowFst_ι_assoc N hkill i j, G.pullbackWindowSnd_ι_assoc N hkill i j]
    exact pullback.condition
  calc pullback.fst (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι ≫
        G.gluedQuotientLeg N hkill i
      = G.pullbackWindowFst N hkill i j ≫
          ((G.gluePatch N hkill i).U.ι ⁻¹ᵁ
            ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U)).ι ≫
          G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
          G.gluedQuotientι N hkill i := by
        rw [gluedQuotientLeg, ← G.pullbackWindowFst_ι_assoc N hkill i j]
    _ = G.pullbackWindowFst N hkill i j ≫
          (G.gluePatch N hkill i).restrictedπ (G.glueW_stable N hkill i j)
            inf_le_left ≫
          ((G.gluePatch N hkill i).imageOpens (G.glueW_stable N hkill i j)
            inf_le_left).ι ≫
          G.gluedQuotientι N hkill i := by
        rw [← (G.gluePatch N hkill i).restrictedπ_ι_assoc
          (G.glueW_stable N hkill i j) inf_le_left]
    _ = G.pullbackWindowFst N hkill i j ≫
          (G.gluePatch N hkill i).restrictedπ (G.glueW_stable N hkill i j)
            inf_le_left ≫
          G.glueT N hkill i j ≫
          ((G.gluePatch N hkill j).imageOpens (G.glueW_stable N hkill j i)
            inf_le_left).ι ≫
          G.gluedQuotientι N hkill j := by
        have hglue := (G.quotientGlueData N hkill).glue_condition i j
        rw [show (G.quotientGlueData N hkill).t i j = G.glueT N hkill i j from rfl,
          show (G.quotientGlueData N hkill).f j i
            = ((G.gluePatch N hkill j).imageOpens (G.glueW_stable N hkill j i)
              inf_le_left).ι from rfl,
          show (G.quotientGlueData N hkill).f i j
            = ((G.gluePatch N hkill i).imageOpens (G.glueW_stable N hkill i j)
              inf_le_left).ι from rfl,
          show (G.quotientGlueData N hkill).ι j = G.gluedQuotientι N hkill j from rfl,
          show (G.quotientGlueData N hkill).ι i = G.gluedQuotientι N hkill i from rfl]
          at hglue
        exact congrArg (fun m : ((G.gluePatch N hkill i).imageOpens
            (G.glueW_stable N hkill i j) inf_le_left).toScheme ⟶
            G.gluedQuotient N hkill =>
          G.pullbackWindowFst N hkill i j ≫
            (G.gluePatch N hkill i).restrictedπ (G.glueW_stable N hkill i j)
              inf_le_left ≫ m) hglue.symm
    _ = G.pullbackWindowFst N hkill i j ≫
          ((G.gluePatch N hkill i).windowCrossIso (G.gluePatch N hkill j)
            inf_le_left inf_le_right).hom ≫
          (G.gluePatch N hkill j).U.toScheme.homOfLE
            (Scheme.Hom.preimage_mono (G.gluePatch N hkill j).U.ι
              (le_inf inf_le_right inf_le_left)) ≫
          (G.gluePatch N hkill j).restrictedπ (G.glueW_stable N hkill j i)
            inf_le_left ≫
          ((G.gluePatch N hkill j).imageOpens (G.glueW_stable N hkill j i)
            inf_le_left).ι ≫
          G.gluedQuotientι N hkill j := by
        rw [glueT, (G.gluePatch N hkill i).restrictedπ_glueTransition_assoc
            (G.gluePatch N hkill j) (G.glueW_stable N hkill i j)
            (G.glueW_stable N hkill j i) inf_le_left inf_le_right
            (le_inf inf_le_right inf_le_left) inf_le_left]
    _ = G.pullbackWindowFst N hkill i j ≫
          ((G.gluePatch N hkill i).windowCrossIso (G.gluePatch N hkill j)
            inf_le_left inf_le_right).hom ≫
          (G.gluePatch N hkill j).U.toScheme.homOfLE
            (Scheme.Hom.preimage_mono (G.gluePatch N hkill j).U.ι
              (le_inf inf_le_right inf_le_left)) ≫
          ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
            ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U)).ι ≫
          G.localQuotientOpenπ (G.gluePatch N hkill j).hstable ≫
          G.gluedQuotientι N hkill j := by
        rw [(G.gluePatch N hkill j).restrictedπ_ι_assoc
          (G.glueW_stable N hkill j i) inf_le_left]
    _ = G.pullbackWindowFst N hkill i j ≫
          ((G.gluePatch N hkill i).windowCrossIso (G.gluePatch N hkill j)
            inf_le_left inf_le_right).hom ≫
          ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
            ((G.gluePatch N hkill i).U ⊓ (G.gluePatch N hkill j).U)).ι ≫
          G.localQuotientOpenπ (G.gluePatch N hkill j).hstable ≫
          G.gluedQuotientι N hkill j := by
        rw [Scheme.homOfLE_ι_assoc]
    _ = G.pullbackWindowSnd N hkill i j ≫
          ((G.gluePatch N hkill j).U.ι ⁻¹ᵁ
            ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U)).ι ≫
          G.localQuotientOpenπ (G.gluePatch N hkill j).hstable ≫
          G.gluedQuotientι N hkill j := by
        rw [reassoc_of% hkey]
    _ = pullback.snd (G.gluePatch N hkill i).U.ι (G.gluePatch N hkill j).U.ι ≫
          G.gluedQuotientLeg N hkill j := by
        rw [gluedQuotientLeg, ← G.pullbackWindowSnd_ι_assoc N hkill i j]

/-- **The quotient projection**: the per-patch quotient legs glued over the C3f cover. -/
noncomputable def gluedQuotientπ : E.E ⟶ G.gluedQuotient N hkill :=
  (G.glueCover N hkill).glueMorphisms (G.gluedQuotientLeg N hkill)
    (G.gluedQuotientLeg_compat N hkill)

@[reassoc]
theorem ι_gluedQuotientπ (i : ↥E.E) :
    (G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill
      = G.gluedQuotientLeg N hkill i :=
  (G.glueCover N hkill).ι_glueMorphisms _ _ i

/-! ### The universal property of the glued quotient -/

section Desc

variable {Y : Scheme.{u}} (f : E.E ⟶ Y) (hf : G.IsInvariant f)

include f hf

/-- Chart restrictions of invariant morphisms coequalize the restricted pair. -/
theorem restricted_coequalizes (i : ↥E.E) :
    G.restrictedAction (G.gluePatch N hkill i).hstable ≫
        ((G.gluePatch N hkill i).U.ι ≫ f)
      = G.restrictedProj (G.gluePatch N hkill i).U ≫
        ((G.gluePatch N hkill i).U.ι ≫ f) := by
  have hactι : G.restrictedAction (G.gluePatch N hkill i).hstable ≫
      (G.gluePatch N hkill i).U.ι
      = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
        G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hprι : G.restrictedProj (G.gluePatch N hkill i).U ≫
      (G.gluePatch N hkill i).U.ι
      = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
        G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  calc G.restrictedAction (G.gluePatch N hkill i).hstable ≫
        ((G.gluePatch N hkill i).U.ι ≫ f)
      = (G.restrictedAction (G.gluePatch N hkill i).hstable ≫
          (G.gluePatch N hkill i).U.ι) ≫ f := (Category.assoc _ _ _).symm
    _ = ((G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          G.translationAction.left) ≫ f := congrArg (· ≫ f) hactι
    _ = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          (G.translationAction.left ≫ f) := Category.assoc _ _ _
    _ = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          (G.actionProj.left ≫ f) :=
        congrArg ((G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫ ·)
          hf.coequalizes
    _ = ((G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          G.actionProj.left) ≫ f := (Category.assoc _ _ _).symm
    _ = (G.restrictedProj (G.gluePatch N hkill i).U ≫
          (G.gluePatch N hkill i).U.ι) ≫ f := (congrArg (· ≫ f) hprι).symm
    _ = G.restrictedProj (G.gluePatch N hkill i).U ≫
          ((G.gluePatch N hkill i).U.ι ≫ f) := Category.assoc _ _ _

/-- The per-patch descent leg of an invariant morphism. -/
noncomputable def gluedDescLeg (i : ↥E.E) :
    G.localQuotientOpen (G.gluePatch N hkill i).hstable ⟶ Y :=
  (G.gluePatch N hkill i).descLocalQuotientOpenπ ((G.gluePatch N hkill i).U.ι ≫ f)
    (G.restricted_coequalizes N hkill f hf i)

/-- The descent legs agree across the glue transitions (V-level compatibility). -/
theorem gluedDescLeg_glueT (i j : ↥E.E) :
    ((G.gluePatch N hkill i).imageOpens (G.glueW_stable N hkill i j) inf_le_left).ι ≫
        G.gluedDescLeg N hkill f hf i
      = G.glueT N hkill i j ≫
        ((G.gluePatch N hkill j).imageOpens (G.glueW_stable N hkill j i)
          inf_le_left).ι ≫
        G.gluedDescLeg N hkill f hf j := by
  refine (G.gluePatch N hkill i).restrictedπ_hom_ext
    (G.glueW_stable N hkill i j) inf_le_left ?_
  rw [(G.gluePatch N hkill i).restrictedπ_ι_assoc (G.glueW_stable N hkill i j)
    inf_le_left]
  rw [gluedDescLeg, (G.gluePatch N hkill i).localQuotientOpenπ_descLocalQuotientOpenπ]
  rw [glueT, (G.gluePatch N hkill i).restrictedπ_glueTransition_assoc
    (G.gluePatch N hkill j) (G.glueW_stable N hkill i j) (G.glueW_stable N hkill j i)
    inf_le_left inf_le_right (le_inf inf_le_right inf_le_left) inf_le_left]
  rw [(G.gluePatch N hkill j).restrictedπ_ι_assoc (G.glueW_stable N hkill j i)
    inf_le_left]
  rw [gluedDescLeg, (G.gluePatch N hkill j).localQuotientOpenπ_descLocalQuotientOpenπ]
  rw [Scheme.homOfLE_ι_assoc, ← Category.assoc,
    AffineChartPatch.windowCrossIso_hom_ι_assoc]
  rw [Category.assoc]

/-- The descent legs are compatible over the quotient cover's pullbacks. -/
theorem gluedDescLeg_pullback_compat (i j : ↥E.E) :
    pullback.fst ((G.quotientGlueData N hkill).ι i) ((G.quotientGlueData N hkill).ι j) ≫
        G.gluedDescLeg N hkill f hf i
      = pullback.snd _ _ ≫ G.gluedDescLeg N hkill f hf j := by
  have hlim := (G.quotientGlueData N hkill).vPullbackConeIsLimit i j
  have hm1 := hlim.fac
    (PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    WalkingCospan.left
  have hm2 := hlim.fac
    (PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    WalkingCospan.right
  simp only [Scheme.GlueData.vPullbackCone, PullbackCone.mk_π_app] at hm1 hm2
  set m := hlim.lift (PullbackCone.mk
    (pullback.fst ((G.quotientGlueData N hkill).ι i) ((G.quotientGlueData N hkill).ι j))
    (pullback.snd ((G.quotientGlueData N hkill).ι i) ((G.quotientGlueData N hkill).ι j))
    pullback.condition) with hmdef
  have hV := G.gluedDescLeg_glueT N hkill f hf i j
  exact (congrArg (· ≫ G.gluedDescLeg N hkill f hf i) hm1.symm).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (m ≫ ·) hV).trans
    (((congrArg (m ≫ ·) (Category.assoc _ _ _).symm).trans
      (Category.assoc _ _ _).symm).trans
    (congrArg (· ≫ G.gluedDescLeg N hkill f hf j) hm2))))

/-- **The descended morphism**: an invariant morphism factors through the glued
quotient. -/
noncomputable def gluedQuotientDesc : G.gluedQuotient N hkill ⟶ Y :=
  (G.quotientGlueData N hkill).openCover.glueMorphisms
    (fun i => G.gluedDescLeg N hkill f hf i)
    (fun i j => G.gluedDescLeg_pullback_compat N hkill f hf i j)

@[reassoc]
theorem gluedQuotientι_gluedQuotientDesc (i : ↥E.E) :
    G.gluedQuotientι N hkill i ≫ G.gluedQuotientDesc N hkill f hf
      = G.gluedDescLeg N hkill f hf i :=
  (G.quotientGlueData N hkill).openCover.ι_glueMorphisms _ _ i

/-- **The factorization**: the descended morphism recovers `f` through the quotient
projection. -/
theorem gluedQuotientπ_gluedQuotientDesc :
    G.gluedQuotientπ N hkill ≫ G.gluedQuotientDesc N hkill f hf = f := by
  refine (G.glueCover N hkill).hom_ext _ _ fun i => ?_
  calc (G.gluePatch N hkill i).U.ι ≫
        G.gluedQuotientπ N hkill ≫ G.gluedQuotientDesc N hkill f hf
      = ((G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill) ≫
          G.gluedQuotientDesc N hkill f hf := (Category.assoc _ _ _).symm
    _ = G.gluedQuotientLeg N hkill i ≫ G.gluedQuotientDesc N hkill f hf :=
        congrArg (· ≫ G.gluedQuotientDesc N hkill f hf) (G.ι_gluedQuotientπ N hkill i)
    _ = G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
          (G.gluedQuotientι N hkill i ≫ G.gluedQuotientDesc N hkill f hf) :=
        Category.assoc _ _ _
    _ = G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
          G.gluedDescLeg N hkill f hf i :=
        congrArg (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫ ·)
          (G.gluedQuotientι_gluedQuotientDesc N hkill f hf i)
    _ = (G.gluePatch N hkill i).U.ι ≫ f :=
        (G.gluePatch N hkill i).localQuotientOpenπ_descLocalQuotientOpenπ _ _

/-- **Uniqueness of the descent.** -/
theorem gluedQuotientDesc_unique {h' : G.gluedQuotient N hkill ⟶ Y}
    (hh : G.gluedQuotientπ N hkill ≫ h' = f) :
    h' = G.gluedQuotientDesc N hkill f hf := by
  refine (G.quotientGlueData N hkill).openCover.hom_ext _ _ fun i => ?_
  refine (G.gluePatch N hkill i).localQuotientOpenπ_hom_ext ?_
  calc G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
        (G.gluedQuotientι N hkill i ≫ h')
      = ((G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill) ≫ h' :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ h') (G.ι_gluedQuotientπ N hkill i).symm)
    _ = (G.gluePatch N hkill i).U.ι ≫ f := by rw [Category.assoc, hh]
    _ = G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
          G.gluedDescLeg N hkill f hf i :=
        ((G.gluePatch N hkill i).localQuotientOpenπ_descLocalQuotientOpenπ _ _).symm
    _ = G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
          (G.gluedQuotientι N hkill i ≫ G.gluedQuotientDesc N hkill f hf) :=
        (congrArg (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫ ·)
          (G.gluedQuotientι_gluedQuotientDesc N hkill f hf i)).symm

/-- **The universal property of the glued quotient** (`[HG-C4c-2]` payoff): every
invariant morphism factors uniquely through the quotient projection. -/
theorem gluedQuotient_existsUnique_lift :
    ∃! h : G.gluedQuotient N hkill ⟶ Y, G.gluedQuotientπ N hkill ≫ h = f :=
  ⟨G.gluedQuotientDesc N hkill f hf, G.gluedQuotientπ_gluedQuotientDesc N hkill f hf,
    fun h' hh => G.gluedQuotientDesc_unique N hkill f hf hh⟩

end Desc

/-- The structure morphism itself is invariant (points are over-morphisms). -/
theorem isInvariant_structure : G.IsInvariant E.π :=
  fun _ _ x t _ => (x + t).2.trans x.2.symm

/-- **The structure morphism of the glued quotient over the base.** -/
noncomputable def gluedQuotientS : G.gluedQuotient N hkill ⟶ S :=
  G.gluedQuotientDesc N hkill E.π (G.isInvariant_structure)

/-- The glued quotient projection is a morphism over `S`. -/
theorem gluedQuotientπ_gluedQuotientS :
    G.gluedQuotientπ N hkill ≫ G.gluedQuotientS N hkill = E.π :=
  G.gluedQuotientπ_gluedQuotientDesc N hkill E.π (G.isInvariant_structure)

/-- The preimage cover of the action object by the patch windows. -/
noncomputable def glueActionCover : (Over.mk G.π ⊗ E.asOver).left.OpenCover :=
  Scheme.Cover.mkOfCovers (↥E.E)
    (fun i => (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).toScheme)
    (fun i => (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι)
    (fun q => ⟨G.actionProj.left.base q, by
      have hq : q ∈ Set.range
          ⇑(G.actionProj.left ⁻¹ᵁ
            (G.gluePatch N hkill (G.actionProj.left.base q)).U).ι := by
        rw [Scheme.Opens.range_ι]
        exact G.mem_gluePatch N hkill (G.actionProj.left.base q)
      obtain ⟨y, hy⟩ := hq
      exact ⟨y, hy⟩⟩)

/-- **The glued projection coequalizes the translation pair**: checked on the preimage
cover, where it is the per-patch coequalization. -/
theorem gluedQuotientπ_coequalizes :
    G.translationAction.left ≫ G.gluedQuotientπ N hkill
      = G.actionProj.left ≫ G.gluedQuotientπ N hkill := by
  refine (G.glueActionCover N hkill).hom_ext _ _ fun i => ?_
  have hcact : G.restrictedAction (G.gluePatch N hkill i).hstable ≫
      (G.gluePatch N hkill i).U.ι
      = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
        G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcpr : G.restrictedProj (G.gluePatch N hkill i).U ≫
      (G.gluePatch N hkill i).U.ι
      = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
        G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  calc (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
        G.translationAction.left ≫ G.gluedQuotientπ N hkill
      = ((G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          G.translationAction.left) ≫ G.gluedQuotientπ N hkill :=
        (Category.assoc _ _ _).symm
    _ = (G.restrictedAction (G.gluePatch N hkill i).hstable ≫
          (G.gluePatch N hkill i).U.ι) ≫ G.gluedQuotientπ N hkill :=
        (congrArg (· ≫ G.gluedQuotientπ N hkill) hcact).symm
    _ = G.restrictedAction (G.gluePatch N hkill i).hstable ≫
          ((G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill) :=
        Category.assoc _ _ _
    _ = G.restrictedAction (G.gluePatch N hkill i).hstable ≫
          G.gluedQuotientLeg N hkill i :=
        congrArg (G.restrictedAction (G.gluePatch N hkill i).hstable ≫ ·)
          (G.ι_gluedQuotientπ N hkill i)
    _ = (G.restrictedAction (G.gluePatch N hkill i).hstable ≫
          G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) ≫
          G.gluedQuotientι N hkill i := (Category.assoc _ _ _).symm
    _ = (G.restrictedProj (G.gluePatch N hkill i).U ≫
          G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) ≫
          G.gluedQuotientι N hkill i :=
        congrArg (· ≫ G.gluedQuotientι N hkill i)
          (restrictedAction_localQuotientOpenπ G (G.gluePatch N hkill i).hstable)
    _ = G.restrictedProj (G.gluePatch N hkill i).U ≫ G.gluedQuotientLeg N hkill i :=
        Category.assoc _ _ _
    _ = G.restrictedProj (G.gluePatch N hkill i).U ≫
          ((G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill) :=
        (congrArg (G.restrictedProj (G.gluePatch N hkill i).U ≫ ·)
          (G.ι_gluedQuotientπ N hkill i)).symm
    _ = (G.restrictedProj (G.gluePatch N hkill i).U ≫
          (G.gluePatch N hkill i).U.ι) ≫ G.gluedQuotientπ N hkill :=
        (Category.assoc _ _ _).symm
    _ = ((G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          G.actionProj.left) ≫ G.gluedQuotientπ N hkill :=
        congrArg (· ≫ G.gluedQuotientπ N hkill) hcpr
    _ = (G.actionProj.left ⁻¹ᵁ (G.gluePatch N hkill i).U).ι ≫
          G.actionProj.left ≫ G.gluedQuotientπ N hkill := Category.assoc _ _ _

/-- **The glued projection is invariant** (pin-5 form, via the backward bridge). -/
theorem isInvariant_gluedQuotientπ : G.IsInvariant (G.gluedQuotientπ N hkill) :=
  IsInvariant.of_coequalizes (G.gluedQuotientπ_coequalizes N hkill)

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
