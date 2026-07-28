/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.StableCharts
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The chart geometry bridges (`[HG-C4b]`)

The `Spec`-level identifications of the chart co-action and projection legs with the
restricted translation pair, through the Künneth chart isomorphisms — relocated upstream
of the quotient construction so the `[HG-C2]` precursor-immersion proof can consume them.

* `spec_coactionRing_isoSpec_inv`, `spec_includeRight_isoSpec_inv`,
  `spec_includeLeft_group_isoSpec_inv`, `chartPullbackIso_inv_restrictedProj`,
  `chartSpecIso_inv_snd` — the raw leg bridges.
* `specSwapIso`, `chartTensorIso` and its two leg lemmas — the chart-first assembly
  (consumed by the glue kernel-pair transport and the precursor immersion).
-/

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

/-! ### `[HG-C4b]` — the geometry bridge, coaction leg -/

/-- **The coaction leg of the geometry bridge**: the `Spec` of the ring-level chart
co-action, composed back to the chart, is the scheme-level chart co-action morphism
(`chartCoactionSpec` = Künneth ≫ restricted action). Affine `isoSpec` naturality applied
to `coactionRing_eq_appTop`. -/
theorem spec_coactionRing_isoSpec_inv :
    Spec.map P.coactionRing ≫ P.hU.isoSpec.inv = P.chartCoactionSpec := by
  haveI : IsAffine P.U.toScheme := P.hU
  have hnat := Scheme.isoSpec_inv_naturality (X := Spec (.of
      (P.groupRing ⊗[P.baseRing] P.chartRing))) (Y := P.U.toScheme) P.chartCoactionSpec
  -- unfold the affine-open `isoSpec` into the scheme-level one
  have hiso : P.hU.isoSpec.inv
      = (Scheme.Spec.mapIso P.U.topIso.symm.op).inv ≫ P.U.toScheme.isoSpec.inv := by
    rw [IsAffineOpen.isoSpec, Iso.trans_inv]
    rfl
  rw [coactionRing_eq_appTop, Spec.map_comp, Spec.map_comp, hiso]
  simp only [Category.assoc, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv]
  -- cancel the `topIso` conjugation
  have htop : Spec.map P.U.topIso.inv ≫ Spec.map P.U.topIso.hom.op.unop = 𝟙 _ := by
    rw [← Spec.map_comp]
    show Spec.map (P.U.topIso.hom ≫ P.U.topIso.inv) = _
    rw [Iso.hom_inv_id, Spec.map_id]
  -- assemble: the `ΓSpecIso` factor is the inverse of `(Spec _).isoSpec.inv`
  rw [show Spec.map P.U.topIso.hom.op.unop = Spec.map P.U.topIso.hom from rfl] at htop
  calc Spec.map (Scheme.ΓSpecIso _).hom ≫ Spec.map P.chartCoactionSpec.appTop ≫
        Spec.map P.U.topIso.inv ≫ Spec.map P.U.topIso.hom ≫ P.U.toScheme.isoSpec.inv
      = Spec.map (Scheme.ΓSpecIso _).hom ≫ Spec.map P.chartCoactionSpec.appTop ≫
        P.U.toScheme.isoSpec.inv := by
        rw [← Category.assoc (Spec.map P.U.topIso.inv), htop, Category.id_comp]
    _ = Spec.map (Scheme.ΓSpecIso _).hom ≫ (Spec (.of
          (P.groupRing ⊗[P.baseRing] P.chartRing))).isoSpec.inv ≫ P.chartCoactionSpec := by
        rw [hnat]
    _ = P.chartCoactionSpec := by
        rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
          Category.id_comp]

/-- **The projection leg of the geometry bridge**: the `Spec` of `includeRight`
(`b ↦ 1 ⊗ b`, into the group-first tensor), composed back to the chart, is the restricted
projection in the Künneth identifications. Five-link chase: `pullbackSpecIso_inv_snd`,
the `kunnethToSpec` comparison square, `pullbackToPatchLevel`'s identity chart leg,
`pullbackToVLevel`'s second-projection compatibility, and
`pullbackRestrictIsoRestrict`'s morphism-restrict identification. -/
theorem spec_includeRight_isoSpec_inv :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫
      P.hU.isoSpec.inv
      = P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ G.restrictedProj P.U := by
  haveI : IsAffine P.U.toScheme := P.hU
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  haveI := P.isIso_toSpecΓ_groupOpen
  -- link 1: `pullbackSpecIso.inv ≫ snd = Spec.map includeRight`
  have h1 : (pullbackSpecIso P.baseRing P.groupRing P.chartRing).inv ≫ pullback.snd _ _
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) :=
    pullbackSpecIso_inv_snd _ _ _
  -- link 2: `kunnethToSpec.inv ≫ snd = snd ≫ (Spec-side second leg)⁻¹` — from the
  -- comparison square `kunnethToSpec ≫ snd' = snd ≫ U.toSpecΓ`
  have h2 : P.kunnethToSpec.hom ≫
      pullback.snd (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
        (Spec.map (E.π.appLE P.V P.U P.hover))
      = pullback.snd P.groupToBase P.chartToBase ≫ P.U.toSpecΓ := by
    rw [kunnethToSpec]
    exact pullback.lift_snd _ _ _
  -- link 3: `pullbackToPatchLevel` has identity chart leg
  have h3 : P.pullbackToPatchLevel.hom ≫ pullback.snd P.groupToBase P.chartToBase
      = pullback.snd (pullback.snd G.π P.V.ι) P.chartToBase := by
    simp only [pullbackToPatchLevel, asIso_hom, pullback.lift_snd, Category.comp_id]
  -- link 4: `pullbackToVLevel.inv ≫ snd = snd` (congrHom has identity legs; pasting iso)
  have h4 : P.pullbackToVLevel.inv ≫ pullback.snd G.π (P.U.ι ≫ E.π)
      = pullback.snd (pullback.snd G.π P.V.ι) P.chartToBase := by
    rw [pullbackToVLevel, Iso.trans_inv, Iso.symm_inv, Iso.symm_inv, Category.assoc]
    have hc : (pullback.congrHom rfl P.chartToBase_comp_ι).hom ≫
        pullback.snd G.π (P.U.ι ≫ E.π) = pullback.snd G.π (P.chartToBase ≫ P.V.ι) := by
      simp only [pullback.congrHom, asIso_hom, pullback.lift_snd, Category.comp_id]
    rw [hc]
    exact pullbackLeftPullbackSndIso_hom_snd G.π P.V.ι P.chartToBase
  -- link 5: the chart Künneth carries the second projection to the restricted projection
  have h5 : (G.chartPullbackIso P.U).inv ≫ G.restrictedProj P.U
      = pullback.snd G.π (P.U.ι ≫ E.π) := by
    rw [chartPullbackIso, Iso.trans_inv, Category.assoc]
    have hres : (G.restrictedDomainIso P.U).inv ≫ G.restrictedProj P.U
        = pullback.snd G.actionProj.left P.U.ι := by
      rw [restrictedDomainIso, Iso.symm_inv, restrictedProj]
      rw [show G.actionProj.left.resLE P.U (G.actionProj.left ⁻¹ᵁ P.U) le_rfl
          = G.actionProj.left ∣_ P.U from Scheme.Hom.resLE_eq_morphismRestrict _]
      exact pullbackRestrictIsoRestrict_hom_morphismRestrict G.actionProj.left P.U
    rw [hres]
    exact pullbackLeftPullbackSndIso_inv_snd_snd G.π E.π P.U.ι
  -- assembly: chase the second projection through the whole Künneth chain
  have hchase : P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ G.restrictedProj P.U
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫
        inv P.U.toSpecΓ := by
    rw [h5, chartSpecIso, Iso.trans_inv, Category.assoc, kunnethSpecIso, Iso.trans_inv,
      chartKunnethSchemeIso, Iso.trans_inv, Category.assoc, Category.assoc]
    rw [h4]
    -- `pullbackToPatchLevel.inv ≫ snd = snd` from the hom-side identity `h3`
    have h3' : P.pullbackToPatchLevel.inv ≫
        pullback.snd (pullback.snd G.π P.V.ι) P.chartToBase
        = pullback.snd P.groupToBase P.chartToBase := by
      rw [← h3, Iso.inv_hom_id_assoc]
    rw [h3']
    -- `kunnethToSpec.inv ≫ snd = Spec-snd ≫ (toSpecΓ)⁻¹` from the hom-side square `h2`
    have h2' : P.kunnethToSpec.inv ≫ pullback.snd P.groupToBase P.chartToBase
        = pullback.snd (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
            (Spec.map (E.π.appLE P.V P.U P.hover)) ≫ inv P.U.toSpecΓ :=
      (IsIso.eq_comp_inv _).mpr (by
        rw [Category.assoc, ← h2, Iso.inv_hom_id_assoc])
    -- `h1`, retyped at the `appLE` spelling of the `Spec` legs (definitional)
    have h1' : (pullbackSpecIso P.baseRing P.groupRing P.chartRing).inv ≫
        pullback.snd (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
          (Spec.map (E.π.appLE P.V P.U P.hover))
        = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) := h1
    rw [h2', ← Category.assoc, h1']
  rw [hchase]
  congr 1
  exact (IsIso.inv_eq_of_hom_inv_id P.hU.isoSpec.hom_inv_id).symm

/-- **The group leg of the geometry bridge** (the `fst`-mirror of
`spec_includeRight_isoSpec_inv`): the `Spec` of the group-side inclusion
`includeLeftRingHom : A → A ⊗ B`, composed to `G` through the group-patch chart, is the first
projection in the Künneth identifications. Same five links with the `fst` leaf lemmas
(`pullbackSpecIso_inv_fst`, `pullbackLeftPullbackSndIso_hom_fst`,
`pullbackRestrictIsoRestrict_inv_fst`). -/
theorem spec_includeLeft_group_isoSpec_inv :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing)) ≫
      P.isAffineOpen_groupOpen.isoSpec.inv ≫ P.groupOpen.ι
      = P.chartSpecIso.inv ≫ pullback.fst G.π (P.U.ι ≫ E.π) := by
  haveI : IsAffine P.U.toScheme := P.hU
  haveI : IsAffine P.groupOpen.toScheme := P.isAffineOpen_groupOpen
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  haveI := P.isIso_toSpecΓ_groupOpen
  -- link 1: `pullbackSpecIso.inv ≫ fst = Spec.map includeLeftRingHom`
  have h1 : (pullbackSpecIso P.baseRing P.groupRing P.chartRing).inv ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing)) :=
    pullbackSpecIso_inv_fst _ _ _
  have h1' : (pullbackSpecIso P.baseRing P.groupRing P.chartRing).inv ≫
      pullback.fst (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
        (Spec.map (E.π.appLE P.V P.U P.hover))
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing)) := h1
  -- link 2: the `kunnethToSpec` comparison square, `fst` side
  have h2 : P.kunnethToSpec.hom ≫
      pullback.fst (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
        (Spec.map (E.π.appLE P.V P.U P.hover))
      = pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.toSpecΓ := by
    rw [kunnethToSpec]
    exact pullback.lift_fst _ _ _
  have h2' : P.kunnethToSpec.inv ≫ pullback.fst P.groupToBase P.chartToBase
      = pullback.fst (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
          (Spec.map (E.π.appLE P.V P.U P.hover)) ≫ inv P.groupOpen.toSpecΓ :=
    (IsIso.eq_comp_inv _).mpr (by
      rw [Category.assoc, ← h2, Iso.inv_hom_id_assoc])
  -- link 3: `pullbackToPatchLevel`'s group leg is the restrict iso
  have h3 : P.pullbackToPatchLevel.hom ≫ pullback.fst P.groupToBase P.chartToBase
      = pullback.fst (pullback.snd G.π P.V.ι) P.chartToBase ≫
        (pullbackRestrictIsoRestrict G.π P.V).hom := by
    simp only [pullbackToPatchLevel, asIso_hom, pullback.lift_fst]
  have h3' : P.pullbackToPatchLevel.inv ≫ pullback.fst (pullback.snd G.π P.V.ι) P.chartToBase
      = pullback.fst P.groupToBase P.chartToBase ≫
        (pullbackRestrictIsoRestrict G.π P.V).inv :=
    (Iso.eq_comp_inv (pullbackRestrictIsoRestrict G.π P.V)).mpr (by
      rw [Category.assoc, ← h3, Iso.inv_hom_id_assoc])
  -- link 4: `pullbackToVLevel.inv ≫ fst = fst ≫ fst` (congrHom identity legs; pasting iso)
  have h4 : P.pullbackToVLevel.inv ≫ pullback.fst G.π (P.U.ι ≫ E.π)
      = pullback.fst (pullback.snd G.π P.V.ι) P.chartToBase ≫ pullback.fst G.π P.V.ι := by
    rw [pullbackToVLevel, Iso.trans_inv, Iso.symm_inv, Iso.symm_inv, Category.assoc]
    have hc : (pullback.congrHom rfl P.chartToBase_comp_ι).hom ≫
        pullback.fst G.π (P.U.ι ≫ E.π) = pullback.fst G.π (P.chartToBase ≫ P.V.ι) := by
      simp only [pullback.congrHom, asIso_hom, pullback.lift_fst, Category.comp_id]
    rw [hc]
    exact pullbackLeftPullbackSndIso_hom_fst G.π P.V.ι P.chartToBase
  -- link 5: the restrict iso feeds the group-patch inclusion
  have h5 : (pullbackRestrictIsoRestrict G.π P.V).inv ≫ pullback.fst G.π P.V.ι
      = P.groupOpen.ι :=
    pullbackRestrictIsoRestrict_inv_fst G.π P.V
  -- assembly
  rw [chartSpecIso, Iso.trans_inv, Category.assoc, kunnethSpecIso, Iso.trans_inv,
    chartKunnethSchemeIso, Iso.trans_inv, Category.assoc, Category.assoc]
  rw [h4, ← Category.assoc (P.pullbackToPatchLevel.inv), h3', Category.assoc, h5,
    ← Category.assoc (P.kunnethToSpec.inv), h2']
  have hInv : P.isAffineOpen_groupOpen.isoSpec.inv = inv P.groupOpen.toSpecΓ :=
    (IsIso.inv_eq_of_hom_inv_id P.isAffineOpen_groupOpen.isoSpec.hom_inv_id).symm
  exact (congrArg (fun m => Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing)) ≫ m ≫ P.groupOpen.ι)
      hInv).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun m => (m ≫ inv P.groupOpen.toSpecΓ) ≫ P.groupOpen.ι) h1'.symm).trans <|
        congrArg (· ≫ P.groupOpen.ι) (Category.assoc _ _ _)

/-- The chart Künneth carries the second projection to the restricted projection
(standalone export of the in-proof identification). -/
theorem chartPullbackIso_inv_restrictedProj :
    (G.chartPullbackIso P.U).inv ≫ G.restrictedProj P.U
      = pullback.snd G.π (P.U.ι ≫ E.π) := by
  rw [chartPullbackIso, Iso.trans_inv, Category.assoc]
  have hres : (G.restrictedDomainIso P.U).inv ≫ G.restrictedProj P.U
      = pullback.snd G.actionProj.left P.U.ι := by
    rw [restrictedDomainIso, Iso.symm_inv, restrictedProj]
    rw [show G.actionProj.left.resLE P.U (G.actionProj.left ⁻¹ᵁ P.U) le_rfl
        = G.actionProj.left ∣_ P.U from Scheme.Hom.resLE_eq_morphismRestrict _]
    exact pullbackRestrictIsoRestrict_hom_morphismRestrict G.actionProj.left P.U
  rw [hres]
  exact pullbackLeftPullbackSndIso_inv_snd_snd G.π E.π P.U.ι

/-- The raw second-projection form of the chart-side bridge leg. -/
theorem chartSpecIso_inv_snd :
    P.chartSpecIso.inv ≫ pullback.snd G.π (P.U.ι ≫ E.π)
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫
        P.hU.isoSpec.inv :=
  (congrArg (P.chartSpecIso.inv ≫ ·) P.chartPullbackIso_inv_restrictedProj.symm).trans
    P.spec_includeRight_isoSpec_inv.symm

/-- The tensor-swap spectrum isomorphism between the two Künneth orders. -/
noncomputable def specSwapIso :
    (Spec (.of (P.groupRing ⊗[P.baseRing] P.chartRing)) : Scheme.{u})
      ≅ Spec (.of (P.chartRing ⊗[P.baseRing] P.groupRing)) where
  hom := Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.comm P.baseRing P.chartRing P.groupRing).toAlgHom.toRingHom))
  inv := Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).toAlgHom.toRingHom))
  hom_inv_id := (Spec.map_comp _ _).symm.trans (by
    rw [show CommRingCat.ofHom
        ((Algebra.TensorProduct.comm P.baseRing P.groupRing
          P.chartRing).toAlgHom.toRingHom) ≫
        CommRingCat.ofHom
        ((Algebra.TensorProduct.comm P.baseRing P.chartRing
          P.groupRing).toAlgHom.toRingHom) = 𝟙 _ from by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      show (Algebra.TensorProduct.comm P.baseRing P.chartRing P.groupRing)
        ((Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing) x) = x
      rw [← Algebra.TensorProduct.comm_symm]
      exact (Algebra.TensorProduct.comm P.baseRing P.chartRing
        P.groupRing).apply_symm_apply x]
    exact Spec.map_id _)
  inv_hom_id := (Spec.map_comp _ _).symm.trans (by
    rw [show CommRingCat.ofHom
        ((Algebra.TensorProduct.comm P.baseRing P.chartRing
          P.groupRing).toAlgHom.toRingHom) ≫
        CommRingCat.ofHom
        ((Algebra.TensorProduct.comm P.baseRing P.groupRing
          P.chartRing).toAlgHom.toRingHom) = 𝟙 _ from by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      show (Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing)
        ((Algebra.TensorProduct.comm P.baseRing P.chartRing P.groupRing) x) = x
      rw [← Algebra.TensorProduct.comm_symm]
      exact (Algebra.TensorProduct.comm P.baseRing P.groupRing
        P.chartRing).apply_symm_apply x]
    exact Spec.map_id _)

/-- The chart identification of the restricted-action object with the spectrum of the
chart-first Künneth tensor. -/
noncomputable def chartTensorIso :
    (G.actionProj.left ⁻¹ᵁ P.U).toScheme
      ≅ Spec (.of (P.chartRing ⊗[P.baseRing] P.groupRing)) :=
  G.chartPullbackIso P.U ≪≫ P.chartSpecIso ≪≫ P.specSwapIso

/-- The chart tensor identification carries the chart co-action to the restricted
action (composed C4b bridge, action leg). -/
@[reassoc]
theorem chartTensorIso_hom_specMap_chartCoaction :
    P.chartTensorIso.hom ≫ Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom)
      = G.restrictedAction P.hstable ≫ P.hU.isoSpec.hom := by
  have hswap : Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom)
      = P.specSwapIso.inv ≫ Spec.map P.coactionRing := by
    show _ = Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.comm P.baseRing P.groupRing
        P.chartRing).toAlgHom.toRingHom)) ≫ Spec.map P.coactionRing
    rw [← Spec.map_comp]
    rfl
  have hbridge : Spec.map P.coactionRing = P.chartCoactionSpec ≫ P.hU.isoSpec.hom :=
    (Iso.comp_inv_eq P.hU.isoSpec).mp P.spec_coactionRing_isoSpec_inv
  rw [hswap, chartTensorIso, hbridge, chartCoactionSpec]
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The chart tensor identification carries the trivial co-action to the restricted
projection (composed C4b bridge, projection leg). -/
@[reassoc]
theorem chartTensorIso_hom_specMap_includeLeft :
    P.chartTensorIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft :
          P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom)
      = G.restrictedProj P.U ≫ P.hU.isoSpec.hom := by
  have hswap : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom)
      = P.specSwapIso.inv ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            P.chartRing →ₐ[P.baseRing]
              P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) := by
    show _ = Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.comm P.baseRing P.groupRing
        P.chartRing).toAlgHom.toRingHom)) ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
  have hbridge : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom)
      = (P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ G.restrictedProj P.U) ≫
        P.hU.isoSpec.hom :=
    (Iso.comp_inv_eq P.hU.isoSpec).mp
      ((congrArg (P.chartSpecIso.inv ≫ ·) P.chartPullbackIso_inv_restrictedProj).trans
        P.chartSpecIso_inv_snd).symm
  rw [hswap, chartTensorIso, hbridge]
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]


end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
