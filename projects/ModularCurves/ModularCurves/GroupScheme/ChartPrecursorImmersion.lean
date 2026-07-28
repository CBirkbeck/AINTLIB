/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.ChartBridges
import ModularCurves.GroupScheme.ActPairImmersion
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The chart precursor is a closed immersion (`[HG-C2]` geometric heart)

`Spec` of the Galois precursor `β = productMap includeLeft chartCoaction : C⊗C → C⊗G`
is conjugate, under the chart tensor identification and the `(U,U)`-Künneth, to the
**chart action pair** `⟨pr, act⟩ : pr⁻¹U ⟶ U ×_V U` (`chartTensorIso_hom_spec_precursor`).
The remaining crux `isClosedImmersion_chartActPair` is the stable-chart restriction of the
proven `isClosedImmersion_actPair_left` (battle plan: `decomposition-c2-heart.md`, step 4).
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1600000

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

namespace AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : FiniteLocallyFreeSubgroup E}
  (P : G.AffineChartPatch)

/-- The `(U,U)`-Künneth comparison at the `Spec` level (mirror of `kunnethToSpec`). -/
noncomputable def uuToSpec :
    pullback P.chartToBase P.chartToBase
      ≅ pullback (Spec.map (E.π.appLE P.V P.U P.hover))
          (Spec.map (E.π.appLE P.V P.U P.hover)) := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  exact asIso (pullback.map P.chartToBase P.chartToBase _ _
    P.U.toSpecΓ P.U.toSpecΓ P.V.toSpecΓ
    (Scheme.Opens.toSpecΓ_SpecMap_appLE E.π P.V P.U P.hover).symm
    (Scheme.Opens.toSpecΓ_SpecMap_appLE E.π P.V P.U P.hover).symm)

/-- The `(U,U)`-chart fibre product is the `Spec` of the chart-ring tensor square. -/
noncomputable def uuSpecIso :
    pullback P.chartToBase P.chartToBase
      ≅ Spec (.of (P.chartRing ⊗[P.baseRing] P.chartRing)) :=
  P.uuToSpec ≪≫ pullbackSpecIso P.baseRing P.chartRing P.chartRing

@[reassoc]
theorem uuSpecIso_inv_fst :
    P.uuSpecIso.inv ≫ pullback.fst P.chartToBase P.chartToBase
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          P.chartRing →+* P.chartRing ⊗[P.baseRing] P.chartRing)) ≫ P.hU.isoSpec.inv := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  have h1 : P.uuToSpec.inv ≫ pullback.fst P.chartToBase P.chartToBase
      = pullback.fst (Spec.map (E.π.appLE P.V P.U P.hover))
          (Spec.map (E.π.appLE P.V P.U P.hover)) ≫ P.hU.isoSpec.inv := by
    rw [Iso.inv_comp_eq]
    have hfst : P.uuToSpec.hom ≫ pullback.fst _ _
        = pullback.fst P.chartToBase P.chartToBase ≫ P.U.toSpecΓ := by
      rw [uuToSpec]
      exact pullback.lift_fst _ _ _
    rw [← Category.assoc, hfst, Category.assoc, ← P.hU.isoSpec_hom, Iso.hom_inv_id,
      Category.comp_id]
  calc P.uuSpecIso.inv ≫ pullback.fst P.chartToBase P.chartToBase
      = (pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫
          (P.uuToSpec.inv ≫ pullback.fst P.chartToBase P.chartToBase) := by
        rw [uuSpecIso, Iso.trans_inv, Category.assoc]
    _ = (pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫
          (pullback.fst (Spec.map (E.π.appLE P.V P.U P.hover))
            (Spec.map (E.π.appLE P.V P.U P.hover)) ≫ P.hU.isoSpec.inv) :=
        congrArg ((pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫ ·) h1
    _ = ((pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫
          pullback.fst (Spec.map (E.π.appLE P.V P.U P.hover))
            (Spec.map (E.π.appLE P.V P.U P.hover))) ≫ P.hU.isoSpec.inv :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          P.chartRing →+* P.chartRing ⊗[P.baseRing] P.chartRing)) ≫ P.hU.isoSpec.inv :=
        congrArg (· ≫ P.hU.isoSpec.inv)
          (pullbackSpecIso_inv_fst P.baseRing P.chartRing P.chartRing)

@[reassoc]
theorem uuSpecIso_inv_snd :
    P.uuSpecIso.inv ≫ pullback.snd P.chartToBase P.chartToBase
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing]
            P.chartRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫ P.hU.isoSpec.inv := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  have h1 : P.uuToSpec.inv ≫ pullback.snd P.chartToBase P.chartToBase
      = pullback.snd (Spec.map (E.π.appLE P.V P.U P.hover))
          (Spec.map (E.π.appLE P.V P.U P.hover)) ≫ P.hU.isoSpec.inv := by
    rw [Iso.inv_comp_eq]
    have hsnd : P.uuToSpec.hom ≫ pullback.snd _ _
        = pullback.snd P.chartToBase P.chartToBase ≫ P.U.toSpecΓ := by
      rw [uuToSpec]
      exact pullback.lift_snd _ _ _
    rw [← Category.assoc, hsnd, Category.assoc, ← P.hU.isoSpec_hom, Iso.hom_inv_id,
      Category.comp_id]
  calc P.uuSpecIso.inv ≫ pullback.snd P.chartToBase P.chartToBase
      = (pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫
          (P.uuToSpec.inv ≫ pullback.snd P.chartToBase P.chartToBase) := by
        rw [uuSpecIso, Iso.trans_inv, Category.assoc]
    _ = (pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫
          (pullback.snd (Spec.map (E.π.appLE P.V P.U P.hover))
            (Spec.map (E.π.appLE P.V P.U P.hover)) ≫ P.hU.isoSpec.inv) :=
        congrArg ((pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫ ·) h1
    _ = ((pullbackSpecIso P.baseRing P.chartRing P.chartRing).inv ≫
          pullback.snd (Spec.map (E.π.appLE P.V P.U P.hover))
            (Spec.map (E.π.appLE P.V P.U P.hover))) ≫ P.hU.isoSpec.inv :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing]
            P.chartRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫ P.hU.isoSpec.inv :=
        congrArg (· ≫ P.hU.isoSpec.inv)
          (pullbackSpecIso_inv_snd P.baseRing P.chartRing P.chartRing)

/-- The two restricted legs agree over the base patch. -/
theorem restrictedProj_chartToBase :
    G.restrictedProj P.U ≫ P.chartToBase
      = G.restrictedAction P.hstable ≫ P.chartToBase := by
  rw [← cancel_mono P.V.ι]
  have hcact : G.restrictedAction P.hstable ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcpr : G.restrictedProj P.U ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hw : G.translationAction.left ≫ E.π = G.actionProj.left ≫ E.π := by
    have h1 := Over.w G.translationAction
    have h2 := Over.w G.actionProj
    exact h1.trans h2.symm
  calc (G.restrictedProj P.U ≫ P.chartToBase) ≫ P.V.ι
      = G.restrictedProj P.U ≫ P.chartToBase ≫ P.V.ι := Category.assoc _ _ _
    _ = G.restrictedProj P.U ≫ P.U.ι ≫ E.π :=
        congrArg (G.restrictedProj P.U ≫ ·) P.chartToBase_comp_ι
    _ = ((G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left) ≫ E.π :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.π) hcpr)
    _ = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left ≫ E.π :=
        Category.assoc _ _ _
    _ = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left ≫ E.π :=
        congrArg ((G.actionProj.left ⁻¹ᵁ P.U).ι ≫ ·) hw.symm
    _ = ((G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left) ≫ E.π :=
        (Category.assoc _ _ _).symm
    _ = (G.restrictedAction P.hstable ≫ P.U.ι) ≫ E.π :=
        congrArg (· ≫ E.π) hcact.symm
    _ = G.restrictedAction P.hstable ≫ P.U.ι ≫ E.π := Category.assoc _ _ _
    _ = G.restrictedAction P.hstable ≫ P.chartToBase ≫ P.V.ι :=
        (congrArg (G.restrictedAction P.hstable ≫ ·) P.chartToBase_comp_ι).symm
    _ = (G.restrictedAction P.hstable ≫ P.chartToBase) ≫ P.V.ι :=
        (Category.assoc _ _ _).symm

/-- **The chart action pair** `⟨pr, act⟩ : pr⁻¹U ⟶ U ×_V U`. -/
noncomputable def chartActPair :
    (G.actionProj.left ⁻¹ᵁ P.U).toScheme ⟶ pullback P.chartToBase P.chartToBase :=
  pullback.lift (G.restrictedProj P.U) (G.restrictedAction P.hstable)
    P.restrictedProj_chartToBase

@[reassoc]
theorem chartActPair_fst :
    P.chartActPair ≫ pullback.fst P.chartToBase P.chartToBase = G.restrictedProj P.U :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem chartActPair_snd :
    P.chartActPair ≫ pullback.snd P.chartToBase P.chartToBase
      = G.restrictedAction P.hstable :=
  pullback.lift_snd _ _ _

/-- **The conjugation**: under the chart tensor identification and the `(U,U)`-Künneth,
`Spec` of the Galois precursor is the chart action pair. -/
theorem chartTensorIso_hom_spec_precursor :
    P.chartTensorIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap
          (Algebra.TensorProduct.includeLeft
            (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
          P.chartCoaction).toRingHom) ≫ P.uuSpecIso.inv
      = P.chartActPair := by
  set β := (Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.includeLeft
      (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
    P.chartCoaction).toRingHom with hβ
  have key_incL : β.comp (Algebra.TensorProduct.includeLeftRingHom :
        P.chartRing →+* P.chartRing ⊗[P.baseRing] P.chartRing)
      = (Algebra.TensorProduct.includeLeftRingHom :
        P.chartRing →+* P.chartRing ⊗[P.baseRing] P.groupRing) := by
    ext b
    simp [hβ, Algebra.TensorProduct.productMap_apply_tmul]
  have key_incR : β.comp (Algebra.TensorProduct.includeRight :
        P.chartRing →ₐ[P.baseRing]
          P.chartRing ⊗[P.baseRing] P.chartRing).toRingHom
      = P.chartCoaction.toRingHom := by
    ext b
    simp only [hβ, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [P.uuSpecIso_inv_fst, P.chartActPair_fst]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom β)), ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, key_incL]
    rw [show (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        P.chartRing →+* P.chartRing ⊗[P.baseRing] P.groupRing))
      = CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft :
        P.chartRing →ₐ[P.baseRing]
          P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom) from rfl]
    rw [← Category.assoc, P.chartTensorIso_hom_specMap_includeLeft, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp only [Category.assoc]
    rw [P.uuSpecIso_inv_snd, P.chartActPair_snd]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom β)), ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, key_incR]
    rw [← Category.assoc, P.chartTensorIso_hom_specMap_chartCoaction, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

/-- The product window of the chart in the ambient square. -/
noncomputable def productOpen : (E.asOver ⊗ E.asOver).left.Opens :=
  (fst E.asOver E.asOver).left ⁻¹ᵁ P.U ⊓ (snd E.asOver E.asOver).left ⁻¹ᵁ P.U

/-- **Stability absorbs the action side**: the action pair pulls the product window back
to the plain chart window. -/
theorem actPair_left_preimage_productOpen :
    G.actPair.left ⁻¹ᵁ P.productOpen = G.actionProj.left ⁻¹ᵁ P.U := by
  rw [productOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage]
  have h1 : G.actPair.left ≫ (fst E.asOver E.asOver).left = G.translationAction.left :=
    congrArg Over.Hom.left (G.actPair_fst)
  have h2 : G.actPair.left ≫ (snd E.asOver E.asOver).left = G.actionProj.left :=
    congrArg Over.Hom.left (G.actPair_snd)
  rw [h1, h2]
  exact inf_eq_right.mpr P.hstable

/-- The first chart leg of the product window. -/
noncomputable def productOpenFst : P.productOpen.toScheme ⟶ P.U.toScheme :=
  IsOpenImmersion.lift P.U.ι (P.productOpen.ι ≫ (fst E.asOver E.asOver).left) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : P.productOpen.ι.base w ∈ P.productOpen := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact Set.mem_range_self w
    exact Set.mem_of_eq_of_mem (Scheme.Hom.comp_apply _ _ _) hw.1)

@[reassoc]
theorem productOpenFst_ι :
    P.productOpenFst ≫ P.U.ι = P.productOpen.ι ≫ (fst E.asOver E.asOver).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The second chart leg of the product window. -/
noncomputable def productOpenSnd : P.productOpen.toScheme ⟶ P.U.toScheme :=
  IsOpenImmersion.lift P.U.ι (P.productOpen.ι ≫ (snd E.asOver E.asOver).left) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : P.productOpen.ι.base w ∈ P.productOpen := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact Set.mem_range_self w
    exact Set.mem_of_eq_of_mem (Scheme.Hom.comp_apply _ _ _) hw.2)

@[reassoc]
theorem productOpenSnd_ι :
    P.productOpenSnd ≫ P.U.ι = P.productOpen.ι ≫ (snd E.asOver E.asOver).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The two window legs agree over the base patch. -/
theorem productOpenFst_chartToBase :
    P.productOpenFst ≫ P.chartToBase = P.productOpenSnd ≫ P.chartToBase := by
  rw [← cancel_mono P.V.ι]
  have hw : (fst E.asOver E.asOver).left ≫ E.π = (snd E.asOver E.asOver).left ≫ E.π :=
    (Over.w (fst E.asOver E.asOver)).trans (Over.w (snd E.asOver E.asOver)).symm
  calc (P.productOpenFst ≫ P.chartToBase) ≫ P.V.ι
      = P.productOpenFst ≫ P.chartToBase ≫ P.V.ι := Category.assoc _ _ _
    _ = P.productOpenFst ≫ P.U.ι ≫ E.π :=
        congrArg (P.productOpenFst ≫ ·) P.chartToBase_comp_ι
    _ = (P.productOpenFst ≫ P.U.ι) ≫ E.π := (Category.assoc _ _ _).symm
    _ = (P.productOpen.ι ≫ (fst E.asOver E.asOver).left) ≫ E.π :=
        congrArg (· ≫ E.π) P.productOpenFst_ι
    _ = P.productOpen.ι ≫ (fst E.asOver E.asOver).left ≫ E.π := Category.assoc _ _ _
    _ = P.productOpen.ι ≫ (snd E.asOver E.asOver).left ≫ E.π :=
        congrArg (P.productOpen.ι ≫ ·) hw
    _ = (P.productOpen.ι ≫ (snd E.asOver E.asOver).left) ≫ E.π :=
        (Category.assoc _ _ _).symm
    _ = (P.productOpenSnd ≫ P.U.ι) ≫ E.π :=
        (congrArg (· ≫ E.π) P.productOpenSnd_ι).symm
    _ = P.productOpenSnd ≫ P.U.ι ≫ E.π := Category.assoc _ _ _
    _ = P.productOpenSnd ≫ P.chartToBase ≫ P.V.ι :=
        (congrArg (P.productOpenSnd ≫ ·) P.chartToBase_comp_ι).symm
    _ = (P.productOpenSnd ≫ P.chartToBase) ≫ P.V.ι := (Category.assoc _ _ _).symm

/-- The comparison from the product window to the chart square. -/
noncomputable def productOpenToSquare :
    P.productOpen.toScheme ⟶ pullback P.chartToBase P.chartToBase :=
  pullback.lift P.productOpenFst P.productOpenSnd P.productOpenFst_chartToBase

/-- Maps into the ambient square are determined by the two projections. -/
theorem tensorLeft_hom_ext {T : Scheme.{u}} {g h : T ⟶ (E.asOver ⊗ E.asOver).left}
    (h1 : g ≫ (fst E.asOver E.asOver).left = h ≫ (fst E.asOver E.asOver).left)
    (h2 : g ≫ (snd E.asOver E.asOver).left = h ≫ (snd E.asOver E.asOver).left) :
    g = h := by
  have hgh : g ≫ (E.asOver ⊗ E.asOver).hom = h ≫ (E.asOver ⊗ E.asOver).hom := by
    have hw : (E.asOver ⊗ E.asOver).hom
        = (fst E.asOver E.asOver).left ≫ E.asOver.hom :=
      (Over.w (fst E.asOver E.asOver)).symm
    rw [hw, ← Category.assoc, h1, Category.assoc]
  have hext : (Over.homMk g rfl :
        Over.mk (g ≫ (E.asOver ⊗ E.asOver).hom) ⟶ E.asOver ⊗ E.asOver)
      = Over.homMk h hgh.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext (by exact h1)
    · exact Over.OverMorphism.ext (by exact h2)
  exact congrArg CommaMorphism.left hext

/-- The first ambient leg of the chart square. -/
noncomputable def ambientLegFst :
    Over.mk (pullback.fst P.chartToBase P.chartToBase ≫ P.U.ι ≫ E.π) ⟶ E.asOver :=
  Over.homMk (pullback.fst P.chartToBase P.chartToBase ≫ P.U.ι) (Category.assoc _ _ _)

/-- The second ambient leg of the chart square. -/
noncomputable def ambientLegSnd :
    Over.mk (pullback.fst P.chartToBase P.chartToBase ≫ P.U.ι ≫ E.π) ⟶ E.asOver :=
  Over.homMk (pullback.snd P.chartToBase P.chartToBase ≫ P.U.ι) (by
    show (pullback.snd P.chartToBase P.chartToBase ≫ P.U.ι) ≫ E.π
      = pullback.fst P.chartToBase P.chartToBase ≫ P.U.ι ≫ E.π
    rw [Category.assoc, ← P.chartToBase_comp_ι, ← Category.assoc,
      ← pullback.condition, Category.assoc, P.chartToBase_comp_ι, ← Category.assoc,
      Category.assoc])

/-- The chart square, mapped into the ambient square. -/
noncomputable def squareToAmbient :
    pullback P.chartToBase P.chartToBase ⟶ (E.asOver ⊗ E.asOver).left :=
  (CartesianMonoidalCategory.lift P.ambientLegFst P.ambientLegSnd).left

@[reassoc]
theorem squareToAmbient_fst :
    P.squareToAmbient ≫ (fst E.asOver E.asOver).left
      = pullback.fst P.chartToBase P.chartToBase ≫ P.U.ι :=
  congrArg CommaMorphism.left
    (CartesianMonoidalCategory.lift_fst P.ambientLegFst P.ambientLegSnd)

@[reassoc]
theorem squareToAmbient_snd :
    P.squareToAmbient ≫ (snd E.asOver E.asOver).left
      = pullback.snd P.chartToBase P.chartToBase ≫ P.U.ι :=
  congrArg CommaMorphism.left
    (CartesianMonoidalCategory.lift_snd P.ambientLegFst P.ambientLegSnd)

/-- The chart square lands in the product window. -/
noncomputable def squareToProductOpen :
    pullback P.chartToBase P.chartToBase ⟶ P.productOpen.toScheme :=
  IsOpenImmersion.lift P.productOpen.ι P.squareToAmbient (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    constructor
    · show (fst E.asOver E.asOver).left.base (P.squareToAmbient.base p) ∈ P.U
      have h := ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
        (fun m : pullback P.chartToBase P.chartToBase ⟶ E.E => m.base p)
        P.squareToAmbient_fst)).trans (Scheme.Hom.comp_apply _ _ _)
      refine Set.mem_of_eq_of_mem (by exact h) ?_
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    · show (snd E.asOver E.asOver).left.base (P.squareToAmbient.base p) ∈ P.U
      have h := ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
        (fun m : pullback P.chartToBase P.chartToBase ⟶ E.E => m.base p)
        P.squareToAmbient_snd)).trans (Scheme.Hom.comp_apply _ _ _)
      refine Set.mem_of_eq_of_mem (by exact h) ?_
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _)

@[reassoc]
theorem squareToProductOpen_ι :
    P.squareToProductOpen ≫ P.productOpen.ι = P.squareToAmbient :=
  IsOpenImmersion.lift_fac _ _ _

/-- The window comparison is an isomorphism. -/
instance : IsIso P.productOpenToSquare := by
  refine ⟨P.squareToProductOpen, ?_, ?_⟩
  · rw [← cancel_mono P.productOpen.ι, Category.assoc, P.squareToProductOpen_ι,
      Category.id_comp]
    refine tensorLeft_hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (P.productOpenToSquare ≫ ·)
        P.squareToAmbient_fst).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ P.U.ι) (pullback.lift_fst _ _ _))).trans P.productOpenFst_ι))
    · exact (Category.assoc _ _ _).trans ((congrArg (P.productOpenToSquare ≫ ·)
        P.squareToAmbient_snd).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ P.U.ι) (pullback.lift_snd _ _ _))).trans P.productOpenSnd_ι))
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp,
        show P.productOpenToSquare ≫ pullback.fst P.chartToBase P.chartToBase
          = P.productOpenFst from pullback.lift_fst _ _ _]
      rw [← cancel_mono P.U.ι]
      exact (Category.assoc _ _ _).trans ((congrArg (P.squareToProductOpen ≫ ·)
        P.productOpenFst_ι).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (fst E.asOver E.asOver).left) P.squareToProductOpen_ι)).trans
        P.squareToAmbient_fst))
    · rw [Category.assoc, Category.id_comp,
        show P.productOpenToSquare ≫ pullback.snd P.chartToBase P.chartToBase
          = P.productOpenSnd from pullback.lift_snd _ _ _]
      rw [← cancel_mono P.U.ι]
      exact (Category.assoc _ _ _).trans ((congrArg (P.squareToProductOpen ≫ ·)
        P.productOpenSnd_ι).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (snd E.asOver E.asOver).left) P.squareToProductOpen_ι)).trans
        P.squareToAmbient_snd))

/-- **The restriction factorization**: the chart action pair is the product-window
restriction of the ambient action pair, through the window comparison and the factor
swap (the ambient pair is `⟨act, pr⟩`, the chart pair `⟨pr, act⟩`). -/
theorem chartActPair_factorization :
    P.chartActPair
      = (Over.mk G.π ⊗ E.asOver).left.homOfLE
          (le_of_eq P.actPair_left_preimage_productOpen.symm) ≫
        (G.actPair.left ∣_ P.productOpen) ≫ P.productOpenToSquare ≫
        (pullbackSymmetry P.chartToBase P.chartToBase).hom := by
  have hcact : G.restrictedAction P.hstable ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left := by
    rw [restrictedAction]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hcpr : G.restrictedProj P.U ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left := by
    rw [restrictedProj]
    exact Scheme.Hom.resLE_comp_ι _ _
  have hres : (G.actPair.left ∣_ P.productOpen) ≫ P.productOpen.ι
      = (G.actPair.left ⁻¹ᵁ P.productOpen).ι ≫ G.actPair.left :=
    morphismRestrict_ι _ _
  have hOL : (Over.mk G.π ⊗ E.asOver).left.homOfLE
        (le_of_eq P.actPair_left_preimage_productOpen.symm) ≫
        (G.actPair.left ⁻¹ᵁ P.productOpen).ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι :=
    Scheme.homOfLE_ι _ _
  apply pullback.hom_ext
  · rw [P.chartActPair_fst, ← cancel_mono P.U.ι]
    have hPOS : P.productOpenToSquare ≫ pullback.snd P.chartToBase P.chartToBase
        = P.productOpenSnd := pullback.lift_snd _ _ _
    have hAP2 : G.actPair.left ≫ (snd E.asOver E.asOver).left = G.actionProj.left :=
      congrArg Over.Hom.left G.actPair_snd
    simp only [Category.assoc]
    rw [pullbackSymmetry_hom_comp_fst_assoc, reassoc_of% hPOS, P.productOpenSnd_ι]
    refine hcpr.trans ?_
    exact ((congrArg ((Over.mk G.π ⊗ E.asOver).left.homOfLE
        (le_of_eq P.actPair_left_preimage_productOpen.symm) ≫ ·)
        (((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (snd E.asOver E.asOver).left) hres)).trans
          ((Category.assoc _ _ _).trans
          (congrArg ((G.actPair.left ⁻¹ᵁ P.productOpen).ι ≫ ·) hAP2)))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ G.actionProj.left) hOL))).symm
  · rw [P.chartActPair_snd, ← cancel_mono P.U.ι]
    have hPOF : P.productOpenToSquare ≫ pullback.fst P.chartToBase P.chartToBase
        = P.productOpenFst := pullback.lift_fst _ _ _
    have hAP1 : G.actPair.left ≫ (fst E.asOver E.asOver).left
        = G.translationAction.left :=
      congrArg Over.Hom.left G.actPair_fst
    simp only [Category.assoc]
    rw [pullbackSymmetry_hom_comp_snd_assoc, reassoc_of% hPOF, P.productOpenFst_ι]
    refine hcact.trans ?_
    exact ((congrArg ((Over.mk G.π ⊗ E.asOver).left.homOfLE
        (le_of_eq P.actPair_left_preimage_productOpen.symm) ≫ ·)
        (((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (fst E.asOver E.asOver).left) hres)).trans
          ((Category.assoc _ _ _).trans
          (congrArg ((G.actPair.left ⁻¹ᵁ P.productOpen).ι ≫ ·) hAP1)))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ G.translationAction.left) hOL))).symm

/-- **`[HG-C2]` geometric heart, closed**: the chart action pair is a closed immersion —
the product-window restriction of `isClosedImmersion_actPair_left`, conjugated by the
window comparison and the factor swap. -/
theorem isClosedImmersion_chartActPair : IsClosedImmersion P.chartActPair := by
  haveI hCI : IsClosedImmersion G.actPair.left := isClosedImmersion_actPair_left G
  haveI : IsIso ((Over.mk G.π ⊗ E.asOver).left.homOfLE
      (le_of_eq P.actPair_left_preimage_productOpen.symm)) := by
    refine ⟨(Over.mk G.π ⊗ E.asOver).left.homOfLE
      (le_of_eq P.actPair_left_preimage_productOpen), ?_, ?_⟩
    · rw [Scheme.homOfLE_homOfLE]
      exact Scheme.homOfLE_rfl _ _
    · rw [Scheme.homOfLE_homOfLE]
      exact Scheme.homOfLE_rfl _ _
  rw [P.chartActPair_factorization]
  infer_instance

/-- **The `Spec` of the Galois precursor is a closed immersion** — conjugate of the chart
action pair. -/
theorem spec_precursor_isClosedImmersion :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft
          (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
        P.chartCoaction).toRingHom)) := by
  have hconj := P.chartTensorIso_hom_spec_precursor
  have hrw : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft
          (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
        P.chartCoaction).toRingHom)
      = P.chartTensorIso.inv ≫ P.chartActPair ≫ P.uuSpecIso.hom := by
    rw [← hconj]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hrw]
  haveI := P.isClosedImmersion_chartActPair
  infer_instance

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
