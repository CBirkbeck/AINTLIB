/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.ChartBridges

/-!
# The chart precursor is a closed immersion (`[HG-C2]` geometric heart)

`Spec` of the Galois precursor `β = productMap includeLeft chartCoaction : C⊗C → C⊗G`
is conjugate, under the chart tensor identification and the `(U,U)`-Künneth, to the
**chart action pair** `⟨pr, act⟩ : pr⁻¹U ⟶ U ×_V U` (`chartTensorIso_hom_spec_precursor`).
The remaining crux `isClosedImmersion_chartActPair` is the stable-chart restriction of the
proven `isClosedImmersion_actPair_left` (battle plan: `decomposition-c2-heart.md`, step 4).
-/

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

/-- **`[HG-C2]` FINAL CRUX (sharpened)**: the chart action pair is a closed immersion —
the stable-chart restriction of `isClosedImmersion_actPair_left`
(`decomposition-c2-heart.md`, step 4). -/
theorem isClosedImmersion_chartActPair : IsClosedImmersion P.chartActPair := by
  sorry

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
