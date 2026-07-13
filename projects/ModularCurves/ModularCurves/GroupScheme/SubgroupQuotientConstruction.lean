/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.GroupRingFree
import ModularCurves.GroupScheme.StableChartData
import ModularCurves.ForMathlib.HopfGaloisQuotient

/-!
# The subgroup-scheme quotient, per-patch layer (`[HG-C4a]`)

The first brick of the `[HG-C4]` glue (design: board v10.184-G0). For an affine chart patch
`P` with free group ring, the categorical quotient of the chart by the translation action is
the affine scheme of the co-invariants of the chart co-action:
`P.localQuotient := Spec (coinvariants P.chartCoaction)`, with quotient map
`P.localQuotientπ := isoSpec ≫ specEqualizerπ`. Its universal property is
`existsUnique_lift_of_isHopfGalois` applied to the M6 Hopf–Galois datum
(`isHopfGalois_chartCoaction`), whose lone `Module.Free` hypothesis is supplied around every
point of `E` by `[HG-C3f]` (`exists_affineChartPatch_free`).

The geometry bridge (invariant morphisms coequalize the chart pair — `[HG-C4b]`) and the
two-stage glue (`[HG-C4c]`) consume this layer.
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

namespace AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : FiniteLocallyFreeSubgroup E}
  (P : G.AffineChartPatch)

section LocalQuotient

variable [Module.Free P.baseRing P.groupRing]

/-- **`[HG-C4a]` — the per-patch quotient**: the affine scheme of the co-invariants of the
chart co-action. -/
noncomputable def localQuotient : Scheme.{u} :=
  Spec (CommRingCat.of (coinvariants P.chartCoaction))

/-- The per-patch quotient map: the chart, identified with the `Spec` of its sections,
mapped to the co-invariants spectrum. -/
noncomputable def localQuotientπ : P.U.toScheme ⟶ P.localQuotient :=
  P.hU.isoSpec.hom ≫
    specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft

/-- **The per-patch universal property** (`existsUnique_lift_of_isHopfGalois` at the M6
datum): every morphism out of the chart that coequalizes the chart pair
`(Spec chartCoaction, Spec includeLeft)` factors uniquely through the per-patch quotient. -/
theorem localQuotient_existsUnique_lift {Y : Scheme.{u}} (f : P.U.toScheme ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom) ≫ P.hU.isoSpec.inv ≫ f
        = Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft :
              P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom) ≫
          P.hU.isoSpec.inv ≫ f) :
    ∃! g : P.localQuotient ⟶ Y, P.localQuotientπ ≫ g = f := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_lift_of_isHopfGalois P.chartCoaction
    P.isHopfGalois_chartCoaction (P.hU.isoSpec.inv ≫ f) hf
  refine ⟨g, ?_, fun g' hg' => ?_⟩
  · show (P.hU.isoSpec.hom ≫
        specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft) ≫ g = f
    exact (Category.assoc _ _ _).trans
      ((congrArg (P.hU.isoSpec.hom ≫ ·) hg).trans (P.hU.isoSpec.hom_inv_id_assoc f))
  · refine huniq g' ?_
    have hg'' : (P.hU.isoSpec.hom ≫
        specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft) ≫ g' = f := hg'
    have hA : P.hU.isoSpec.hom ≫
        specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft ≫ g' = f :=
      (Category.assoc _ _ _).symm.trans hg''
    show specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft ≫ g'
        = P.hU.isoSpec.inv ≫ f
    exact (P.hU.isoSpec.inv_hom_id_assoc _).symm.trans (congrArg (P.hU.isoSpec.inv ≫ ·) hA)

end LocalQuotient

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

/-- **`[HG-C4b]` — invariant morphisms coequalize the chart pair.** For a `G`-invariant
`f : E ⟶ Y`, the chart restriction `U.ι ≫ f` satisfies the algebraic coequalization
hypothesis of the per-patch universal property: restrict `IsInvariant.coequalizes` to the
chart (the `resLE` square), then transport both legs through the geometry bridge
(`spec_coactionRing_isoSpec_inv`, `spec_includeRight_isoSpec_inv`), peeling the common
tensor-swap factor (`Spec.map` of `Algebra.TensorProduct.comm`, an isomorphism). -/
theorem coequalizes_of_isInvariant {Y : Scheme.{u}} {f : E.E ⟶ Y} (hf : G.IsInvariant f) :
    Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom) ≫ P.hU.isoSpec.inv ≫ (P.U.ι ≫ f)
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft :
            P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom) ≫
        P.hU.isoSpec.inv ≫ (P.U.ι ≫ f) := by
  -- geometric coequalization on the chart, from global invariance
  have hco := hf.coequalizes
  have hactι : G.restrictedAction P.hstable ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left :=
    Scheme.Hom.resLE_comp_ι _ _
  have hprι : G.restrictedProj P.U ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.actionProj.left :=
    Scheme.Hom.resLE_comp_ι _ _
  have hgeo : G.restrictedAction P.hstable ≫ (P.U.ι ≫ f)
      = G.restrictedProj P.U ≫ (P.U.ι ≫ f) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ f) hactι).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((G.actionProj.left ⁻¹ᵁ P.U).ι ≫ ·) hco).trans <|
            (Category.assoc _ _ _).symm.trans <|
              (congrArg (· ≫ f) hprι.symm).trans (Category.assoc _ _ _)
  -- the two swap decompositions: `chartCoaction = comm ∘ coactionRing`,
  -- `includeLeft = comm ∘ includeRight`
  have hswap₁ : Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom)
      = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).toAlgHom.toRingHom)) ≫
        Spec.map P.coactionRing := by
    rw [← Spec.map_comp]
    rfl
  have hswap₂ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom)
      = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).toAlgHom.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
  rw [hswap₁, hswap₂, Category.assoc, Category.assoc]
  congr 1
  -- both sides through the geometry bridge, term-mode (the transparency-safe idiom):
  -- reassociate to expose the bridged composites, apply the two legs, connect by `hgeo`
  have hA : (Spec.map P.coactionRing ≫ P.hU.isoSpec.inv) ≫ (P.U.ι ≫ f)
      = P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫
          (G.restrictedAction P.hstable ≫ (P.U.ι ≫ f)) :=
    (congrArg (· ≫ (P.U.ι ≫ f)) P.spec_coactionRing_isoSpec_inv).trans <|
      (Category.assoc _ _ _).trans <|
        congrArg (P.chartSpecIso.inv ≫ ·) (Category.assoc _ _ _)
  have hB : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫
        P.hU.isoSpec.inv) ≫ (P.U.ι ≫ f)
      = P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫
          (G.restrictedProj P.U ≫ (P.U.ι ≫ f)) :=
    (congrArg (· ≫ (P.U.ι ≫ f)) P.spec_includeRight_isoSpec_inv).trans <|
      (Category.assoc _ _ _).trans <|
        congrArg (P.chartSpecIso.inv ≫ ·) (Category.assoc _ _ _)
  exact (Category.assoc _ _ _).symm.trans <|
    hA.trans <|
      (congrArg (fun m => P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ m) hgeo).trans <|
        hB.symm.trans (Category.assoc _ _ _)

/-! ### `[HG-C4c]` transition data: two nested patches -/

section Transition

variable (Q : G.AffineChartPatch) (hUQ : Q.U ≤ P.U) (hVQ : Q.V ≤ P.V)

/-- Base-ring restriction between nested patches. -/
noncomputable def resBase : P.baseRing ⟶ Q.baseRing :=
  S.presheaf.map (homOfLE hVQ).op

/-- Chart-ring restriction between nested patches. -/
noncomputable def resChart : P.chartRing ⟶ Q.chartRing :=
  E.E.presheaf.map (homOfLE hUQ).op

/-- Group-ring restriction between nested patches. -/
noncomputable def resGroup : P.groupRing ⟶ Q.groupRing :=
  G.G.presheaf.map (homOfLE (Scheme.Hom.preimage_mono G.π hVQ)).op

/-- The chart-restriction `appLE` exchange square on the `E`-side. -/
theorem resChart_appLE :
    (E.π.appLE P.V P.U P.hover) ≫ P.resChart Q hUQ
      = P.resBase Q hVQ ≫ (E.π.appLE Q.V Q.U Q.hover) := by
  rw [resChart, resBase, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- The group-restriction `appLE` exchange square on the `G`-side. -/
theorem resGroup_appLE :
    (G.π.appLE P.V P.groupOpen le_rfl) ≫ P.resGroup Q hVQ
      = P.resBase Q hVQ ≫ (G.π.appLE Q.V Q.groupOpen le_rfl) := by
  rw [resGroup, resBase, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- **The tensor comparison of the transition** (`T` of `mem_coinvariants_of_map`): the
ring map `B_P ⊗[R_P] A_P ⟶ B_Q ⊗[R_Q] A_Q` induced by the three restrictions, via the
universal property of the tensor product (commutativity supplies the `Commute`s). -/
noncomputable def transitionTensor :
    (P.chartRing ⊗[P.baseRing] P.groupRing) →+* (Q.chartRing ⊗[Q.baseRing] Q.groupRing) :=
  letI : Algebra P.baseRing (Q.chartRing ⊗[Q.baseRing] Q.groupRing) :=
    ((algebraMap Q.baseRing (Q.chartRing ⊗[Q.baseRing] Q.groupRing)).comp
      (P.resBase Q hVQ).hom).toAlgebra
  letI fB : P.chartRing →ₐ[P.baseRing] (Q.chartRing ⊗[Q.baseRing] Q.groupRing) :=
    { toRingHom := (Algebra.TensorProduct.includeLeft :
          Q.chartRing →ₐ[Q.baseRing] Q.chartRing ⊗[Q.baseRing] Q.groupRing).toRingHom.comp
        (P.resChart Q hUQ).hom
      commutes' := fun r => by
        have h := congrArg (fun m => (CommRingCat.Hom.hom m) r) (P.resChart_appLE Q hUQ hVQ)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
        show (Algebra.TensorProduct.includeLeft :
            Q.chartRing →ₐ[Q.baseRing] Q.chartRing ⊗[Q.baseRing] Q.groupRing)
          ((P.resChart Q hUQ).hom ((E.π.appLE P.V P.U P.hover).hom r)) = _
        rw [h]
        rfl }
  letI fA : P.groupRing →ₐ[P.baseRing] (Q.chartRing ⊗[Q.baseRing] Q.groupRing) :=
    { toRingHom := (Algebra.TensorProduct.includeRight :
          Q.groupRing →ₐ[Q.baseRing] Q.chartRing ⊗[Q.baseRing] Q.groupRing).toRingHom.comp
        (P.resGroup Q hVQ).hom
      commutes' := fun r => by
        have h := congrArg (fun m => (CommRingCat.Hom.hom m) r) (P.resGroup_appLE Q hVQ)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
        show Algebra.TensorProduct.includeRight ((P.resGroup Q hVQ).hom
          ((G.π.appLE P.V P.groupOpen le_rfl).hom r)) = _
        rw [h]
        exact (Algebra.TensorProduct.includeRight (R := Q.baseRing) (A := Q.chartRing)
          (B := Q.groupRing)).commutes ((P.resBase Q hVQ).hom r) }
  (Algebra.TensorProduct.lift (R := P.baseRing) (S := P.baseRing) (A := P.chartRing)
    (B := P.groupRing) (C := Q.chartRing ⊗[Q.baseRing] Q.groupRing)
    fB fA (fun _ _ => Commute.all _ _)).toRingHom

/-- The transition tensor carries `b ⊗ 1` to `(res b) ⊗ 1` — the `hT1` input of
`mem_coinvariants_of_map`. -/
theorem transitionTensor_tmul_one (b : P.chartRing) :
    P.transitionTensor Q hUQ hVQ (b ⊗ₜ[P.baseRing] 1)
      = (P.resChart Q hUQ).hom b ⊗ₜ[Q.baseRing] 1 := by
  letI : Algebra P.baseRing (Q.chartRing ⊗[Q.baseRing] Q.groupRing) :=
    ((algebraMap Q.baseRing (Q.chartRing ⊗[Q.baseRing] Q.groupRing)).comp
      (P.resBase Q hVQ).hom).toAlgebra
  simp only [transitionTensor, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- **The group-first tensor comparison of the transition** (the order used by the
Künneth/`chartSpecIso` side): `A_P ⊗[R_P] B_P ⟶ A_Q ⊗[R_Q] B_Q` induced by the three
restrictions. -/
noncomputable def transitionTensorA :
    (P.groupRing ⊗[P.baseRing] P.chartRing) →+* (Q.groupRing ⊗[Q.baseRing] Q.chartRing) :=
  letI : Algebra P.baseRing (Q.groupRing ⊗[Q.baseRing] Q.chartRing) :=
    ((algebraMap Q.baseRing (Q.groupRing ⊗[Q.baseRing] Q.chartRing)).comp
      (P.resBase Q hVQ).hom).toAlgebra
  letI fA : P.groupRing →ₐ[P.baseRing] (Q.groupRing ⊗[Q.baseRing] Q.chartRing) :=
    { toRingHom := (Algebra.TensorProduct.includeLeft :
          Q.groupRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom.comp
        (P.resGroup Q hVQ).hom
      commutes' := fun r => by
        have h := congrArg (fun m => (CommRingCat.Hom.hom m) r) (P.resGroup_appLE Q hVQ)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
        show (Algebra.TensorProduct.includeLeft :
            Q.groupRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing)
          ((P.resGroup Q hVQ).hom ((G.π.appLE P.V P.groupOpen le_rfl).hom r)) = _
        rw [h]
        rfl }
  letI fB : P.chartRing →ₐ[P.baseRing] (Q.groupRing ⊗[Q.baseRing] Q.chartRing) :=
    { toRingHom := (Algebra.TensorProduct.includeRight :
          Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom.comp
        (P.resChart Q hUQ).hom
      commutes' := fun r => by
        have h := congrArg (fun m => (CommRingCat.Hom.hom m) r) (P.resChart_appLE Q hUQ hVQ)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
        show Algebra.TensorProduct.includeRight ((P.resChart Q hUQ).hom
          ((E.π.appLE P.V P.U P.hover).hom r)) = _
        rw [h]
        exact (Algebra.TensorProduct.includeRight (R := Q.baseRing) (A := Q.groupRing)
          (B := Q.chartRing)).commutes ((P.resBase Q hVQ).hom r) }
  (Algebra.TensorProduct.lift (R := P.baseRing) (S := P.baseRing) (A := P.groupRing)
    (B := P.chartRing) (C := Q.groupRing ⊗[Q.baseRing] Q.chartRing)
    fA fB (fun _ _ => Commute.all _ _)).toRingHom

/-- The A-first transition on the group leg: `T_A (a ⊗ 1) = res a ⊗ 1`. -/
theorem transitionTensorA_tmul_one (a : P.groupRing) :
    P.transitionTensorA Q hUQ hVQ (a ⊗ₜ[P.baseRing] 1)
      = (P.resGroup Q hVQ).hom a ⊗ₜ[Q.baseRing] 1 := by
  letI : Algebra P.baseRing (Q.groupRing ⊗[Q.baseRing] Q.chartRing) :=
    ((algebraMap Q.baseRing (Q.groupRing ⊗[Q.baseRing] Q.chartRing)).comp
      (P.resBase Q hVQ).hom).toAlgebra
  simp only [transitionTensorA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- The A-first transition on the chart leg: `T_A (1 ⊗ b) = 1 ⊗ res b`. -/
theorem transitionTensorA_one_tmul (b : P.chartRing) :
    P.transitionTensorA Q hUQ hVQ ((1 : P.groupRing) ⊗ₜ[P.baseRing] b)
      = (1 : Q.groupRing) ⊗ₜ[Q.baseRing] (P.resChart Q hUQ).hom b := by
  letI : Algebra P.baseRing (Q.groupRing ⊗[Q.baseRing] Q.chartRing) :=
    ((algebraMap Q.baseRing (Q.groupRing ⊗[Q.baseRing] Q.chartRing)).comp
      (P.resBase Q hVQ).hom).toAlgebra
  simp only [transitionTensorA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- `isoSpec`-window naturality on the group patches: restricting sections corresponds to
the window inclusion of the group opens. -/
theorem specMap_resGroup_isoSpec_inv :
    Spec.map (P.resGroup Q hVQ) ≫ P.isAffineOpen_groupOpen.isoSpec.inv
      = Q.isAffineOpen_groupOpen.isoSpec.inv ≫
        Scheme.homOfLE _ (Scheme.Hom.preimage_mono G.π hVQ) := by
  haveI : IsAffine P.groupOpen.toScheme := P.isAffineOpen_groupOpen
  haveI : IsAffine Q.groupOpen.toScheme := Q.isAffineOpen_groupOpen
  haveI := P.isIso_toSpecΓ_groupOpen
  haveI := Q.isIso_toSpecΓ_groupOpen
  have hnat := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map Q.groupOpen P.groupOpen
    (Scheme.Hom.preimage_mono G.π hVQ)
  have hInvP : P.isAffineOpen_groupOpen.isoSpec.inv = inv P.groupOpen.toSpecΓ :=
    (IsIso.inv_eq_of_hom_inv_id P.isAffineOpen_groupOpen.isoSpec.hom_inv_id).symm
  have hInvQ : Q.isAffineOpen_groupOpen.isoSpec.inv = inv Q.groupOpen.toSpecΓ :=
    (IsIso.inv_eq_of_hom_inv_id Q.isAffineOpen_groupOpen.isoSpec.hom_inv_id).symm
  rw [hInvP, hInvQ, IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact hnat

/-- `isoSpec`-window naturality on the charts. -/
theorem specMap_resChart_isoSpec_inv :
    Spec.map (P.resChart Q hUQ) ≫ P.hU.isoSpec.inv
      = Q.hU.isoSpec.inv ≫ E.E.homOfLE hUQ := by
  haveI : IsAffine P.U.toScheme := P.hU
  haveI : IsAffine Q.U.toScheme := Q.hU
  haveI := P.isIso_toSpecΓ_U
  haveI := Q.isIso_toSpecΓ_U
  have hnat := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map Q.U P.U hUQ
  have hInvP : P.hU.isoSpec.inv = inv P.U.toSpecΓ :=
    (IsIso.inv_eq_of_hom_inv_id P.hU.isoSpec.hom_inv_id).symm
  have hInvQ : Q.hU.isoSpec.inv = inv Q.U.toSpecΓ :=
    (IsIso.inv_eq_of_hom_inv_id Q.hU.isoSpec.hom_inv_id).symm
  rw [hInvP, hInvQ, IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact hnat

/-- The scheme-level window between the ambient chart pullbacks of nested patches. -/
noncomputable def pullbackWindow :
    pullback G.π (Q.U.ι ≫ E.π) ⟶ pullback G.π (P.U.ι ≫ E.π) :=
  pullback.map G.π (Q.U.ι ≫ E.π) G.π (P.U.ι ≫ E.π) (𝟙 G.G) (E.E.homOfLE hUQ) (𝟙 S)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Category.assoc, Scheme.homOfLE_ι])

/-- **`K` — the two-patch Künneth comparison**: the `Spec` of the transition tensor
intertwines the two chart identifications with the ambient pullback window. Proof by
`pullback.hom_ext`, chasing each projection through the per-patch bridge legs, the
transition-tensor laws, the `isoSpec`-window naturality, and `homOfLE_ι`. -/
theorem spec_transitionTensorA_chartSpecIso_inv :
    Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫ P.chartSpecIso.inv
      = Q.chartSpecIso.inv ≫ P.pullbackWindow Q hUQ := by
  -- ring-level leg exchanges (elementwise from the transition-tensor laws)
  have hringF : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing) ≫
        CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)
      = P.resGroup Q hVQ ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing) := by
    ext a
    exact P.transitionTensorA_tmul_one Q hUQ hVQ a
  have hringS : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom ≫
        CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)
      = P.resChart Q hUQ ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom := by
    ext b
    exact P.transitionTensorA_one_tmul Q hUQ hVQ b
  -- their `Spec` forms
  have hSpecF : Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing))
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing)) ≫
        Spec.map (P.resGroup Q hVQ) :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hringF).trans (Spec.map_comp _ _))
  have hSpecS : Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom)
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom) ≫
        Spec.map (P.resChart Q hUQ) :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hringS).trans (Spec.map_comp _ _))
  apply pullback.hom_ext
  · -- first projections
    have hpwf : P.pullbackWindow Q hUQ ≫ pullback.fst G.π (P.U.ι ≫ E.π)
        = pullback.fst G.π (Q.U.ι ≫ E.π) := by
      simp only [pullbackWindow, pullback.lift_fst, Category.comp_id]
    calc (Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
          P.chartSpecIso.inv) ≫ pullback.fst G.π (P.U.ι ≫ E.π)
        = Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
            (P.chartSpecIso.inv ≫ pullback.fst G.π (P.U.ι ≫ E.π)) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing)) ≫
            P.isAffineOpen_groupOpen.isoSpec.inv ≫ P.groupOpen.ι :=
          congrArg (Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫ ·)
            (P.spec_includeLeft_group_isoSpec_inv).symm
      _ = (Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              P.groupRing →+* P.groupRing ⊗[P.baseRing] P.chartRing))) ≫
            P.isAffineOpen_groupOpen.isoSpec.inv ≫ P.groupOpen.ι :=
          (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing)) ≫
            Spec.map (P.resGroup Q hVQ)) ≫
            P.isAffineOpen_groupOpen.isoSpec.inv ≫ P.groupOpen.ι :=
          congrArg (· ≫ P.isAffineOpen_groupOpen.isoSpec.inv ≫ P.groupOpen.ι) hSpecF
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing)) ≫
            (Spec.map (P.resGroup Q hVQ) ≫ P.isAffineOpen_groupOpen.isoSpec.inv) ≫
            P.groupOpen.ι := by
          simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing)) ≫
            (Q.isAffineOpen_groupOpen.isoSpec.inv ≫
              Scheme.homOfLE _ (Scheme.Hom.preimage_mono G.π hVQ)) ≫ P.groupOpen.ι :=
          congrArg (fun m => Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom :
                Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing)) ≫ m ≫ P.groupOpen.ι)
            (P.specMap_resGroup_isoSpec_inv Q hVQ)
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              Q.groupRing →+* Q.groupRing ⊗[Q.baseRing] Q.chartRing)) ≫
            Q.isAffineOpen_groupOpen.isoSpec.inv ≫ Q.groupOpen.ι := by
          simp only [Category.assoc, Scheme.homOfLE_ι]
      _ = Q.chartSpecIso.inv ≫ pullback.fst G.π (Q.U.ι ≫ E.π) :=
          Q.spec_includeLeft_group_isoSpec_inv
      _ = Q.chartSpecIso.inv ≫ P.pullbackWindow Q hUQ ≫ pullback.fst G.π (P.U.ι ≫ E.π) :=
          congrArg (Q.chartSpecIso.inv ≫ ·) hpwf.symm
      _ = (Q.chartSpecIso.inv ≫ P.pullbackWindow Q hUQ) ≫
            pullback.fst G.π (P.U.ι ≫ E.π) := (Category.assoc _ _ _).symm
  · -- second projections
    have hpws : P.pullbackWindow Q hUQ ≫ pullback.snd G.π (P.U.ι ≫ E.π)
        = pullback.snd G.π (Q.U.ι ≫ E.π) ≫ E.E.homOfLE hUQ := by
      simp only [pullbackWindow, pullback.lift_snd]
    calc (Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
          P.chartSpecIso.inv) ≫ pullback.snd G.π (P.U.ι ≫ E.π)
        = Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
            (P.chartSpecIso.inv ≫ pullback.snd G.π (P.U.ι ≫ E.π)) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom) ≫
            P.hU.isoSpec.inv :=
          congrArg (Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫ ·)
            P.chartSpecIso_inv_snd
      _ = (Spec.map (CommRingCat.ofHom (P.transitionTensorA Q hUQ hVQ)) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              P.chartRing →ₐ[P.baseRing] P.groupRing ⊗[P.baseRing] P.chartRing).toRingHom)) ≫
            P.hU.isoSpec.inv := (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom) ≫
            Spec.map (P.resChart Q hUQ)) ≫ P.hU.isoSpec.inv :=
          congrArg (· ≫ P.hU.isoSpec.inv) hSpecS
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom) ≫
            (Spec.map (P.resChart Q hUQ) ≫ P.hU.isoSpec.inv) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom) ≫
            (Q.hU.isoSpec.inv ≫ E.E.homOfLE hUQ) :=
          congrArg (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom) ≫ ·)
            (P.specMap_resChart_isoSpec_inv Q hUQ)
      _ = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              Q.chartRing →ₐ[Q.baseRing] Q.groupRing ⊗[Q.baseRing] Q.chartRing).toRingHom) ≫
            Q.hU.isoSpec.inv) ≫ E.E.homOfLE hUQ := (Category.assoc _ _ _).symm
      _ = (Q.chartSpecIso.inv ≫ pullback.snd G.π (Q.U.ι ≫ E.π)) ≫ E.E.homOfLE hUQ :=
          congrArg (· ≫ E.E.homOfLE hUQ) Q.chartSpecIso_inv_snd.symm
      _ = Q.chartSpecIso.inv ≫ pullback.snd G.π (Q.U.ι ≫ E.π) ≫ E.E.homOfLE hUQ :=
          Category.assoc _ _ _
      _ = Q.chartSpecIso.inv ≫ P.pullbackWindow Q hUQ ≫ pullback.snd G.π (P.U.ι ≫ E.π) :=
          congrArg (Q.chartSpecIso.inv ≫ ·) hpws.symm
      _ = (Q.chartSpecIso.inv ≫ P.pullbackWindow Q hUQ) ≫
            pullback.snd G.π (P.U.ι ≫ E.π) := (Category.assoc _ _ _).symm

/-- **`W'` — the ambient window under the chart Künneth**: the pullback window corresponds
to the opens window of the restricted-action domains. Compared after the (mono) domain
inclusion, then by `hom_ext` on the ambient `G ×_S E` via the pasting-iso projection laws. -/
theorem pullbackWindow_chartPullbackIso_inv :
    P.pullbackWindow Q hUQ ≫ (G.chartPullbackIso P.U).inv
      = (G.chartPullbackIso Q.U).inv ≫
        Scheme.homOfLE _ (Scheme.Hom.preimage_mono G.actionProj.left hUQ) := by
  have hcpι : ∀ (R : G.AffineChartPatch),
      (G.chartPullbackIso R.U).inv ≫ (G.actionProj.left ⁻¹ᵁ R.U).ι
        = (pullbackLeftPullbackSndIso G.π E.π R.U.ι).inv ≫
          pullback.fst G.actionProj.left R.U.ι := by
    intro R
    rw [chartPullbackIso, Iso.trans_inv, Category.assoc]
    congr 1
    rw [restrictedDomainIso, Iso.symm_inv]
    exact pullbackRestrictIsoRestrict_hom_ι G.actionProj.left R.U
  rw [← cancel_mono ((G.actionProj.left ⁻¹ᵁ P.U).ι)]
  rw [Category.assoc, hcpι P, Category.assoc]
  rw [show Scheme.homOfLE _ (Scheme.Hom.preimage_mono G.actionProj.left hUQ) ≫
      (G.actionProj.left ⁻¹ᵁ P.U).ι = (G.actionProj.left ⁻¹ᵁ Q.U).ι from
    Scheme.homOfLE_ι _ _]
  rw [hcpι Q]
  -- both sides now live in the ambient `G ×_S E`: compare projections
  apply pullback.hom_ext
  · -- to `G`
    calc (P.pullbackWindow Q hUQ ≫ (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv ≫
          pullback.fst G.actionProj.left P.U.ι) ≫ pullback.fst G.π E.π
        = P.pullbackWindow Q hUQ ≫ (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv ≫
          pullback.fst G.actionProj.left P.U.ι ≫ pullback.fst G.π E.π := by
          simp only [Category.assoc]
      _ = P.pullbackWindow Q hUQ ≫ pullback.fst G.π (P.U.ι ≫ E.π) :=
          congrArg (P.pullbackWindow Q hUQ ≫ ·)
            (pullbackLeftPullbackSndIso_inv_fst G.π E.π P.U.ι)
      _ = pullback.fst G.π (Q.U.ι ≫ E.π) := by
          simp only [pullbackWindow, pullback.lift_fst, Category.comp_id]
      _ = ((pullbackLeftPullbackSndIso G.π E.π Q.U.ι).inv ≫
            pullback.fst G.actionProj.left Q.U.ι) ≫ pullback.fst G.π E.π :=
          ((Category.assoc _ _ _).trans
            (pullbackLeftPullbackSndIso_inv_fst G.π E.π Q.U.ι)).symm
  · -- to `E`
    calc (P.pullbackWindow Q hUQ ≫ (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv ≫
          pullback.fst G.actionProj.left P.U.ι) ≫ pullback.snd G.π E.π
        = P.pullbackWindow Q hUQ ≫ (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv ≫
          pullback.fst G.actionProj.left P.U.ι ≫ pullback.snd G.π E.π := by
          simp only [Category.assoc]
      _ = P.pullbackWindow Q hUQ ≫ pullback.snd G.π (P.U.ι ≫ E.π) ≫ P.U.ι :=
          congrArg (P.pullbackWindow Q hUQ ≫ ·)
            (pullbackLeftPullbackSndIso_inv_fst_snd G.π E.π P.U.ι)
      _ = (pullback.snd G.π (Q.U.ι ≫ E.π) ≫ E.E.homOfLE hUQ) ≫ P.U.ι := by
          rw [← Category.assoc]
          congr 1
          simp only [pullbackWindow, pullback.lift_snd]
      _ = pullback.snd G.π (Q.U.ι ≫ E.π) ≫ Q.U.ι := by
          rw [Category.assoc, Scheme.homOfLE_ι]
      _ = ((pullbackLeftPullbackSndIso G.π E.π Q.U.ι).inv ≫
            pullback.fst G.actionProj.left Q.U.ι) ≫ pullback.snd G.π E.π :=
          ((Category.assoc _ _ _).trans
            (pullbackLeftPullbackSndIso_inv_fst_snd G.π E.π Q.U.ι)).symm

/-- **The geometric window square, action leg**: the restricted actions of nested patches
commute with the window inclusions (`resLE` composition laws). -/
theorem homOfLE_restrictedAction :
    Scheme.homOfLE _ (Scheme.Hom.preimage_mono G.actionProj.left hUQ) ≫
        G.restrictedAction P.hstable
      = G.restrictedAction Q.hstable ≫ E.E.homOfLE hUQ :=
  (Scheme.Hom.map_resLE G.translationAction.left P.hstable
      (Scheme.Hom.preimage_mono G.actionProj.left hUQ)).trans
    (Scheme.Hom.resLE_map G.translationAction.left Q.hstable hUQ).symm

/-- **The geometric window square, projection leg**. -/
theorem homOfLE_restrictedProj :
    Scheme.homOfLE _ (Scheme.Hom.preimage_mono G.actionProj.left hUQ) ≫
        G.restrictedProj P.U
      = G.restrictedProj Q.U ≫ E.E.homOfLE hUQ :=
  (Scheme.Hom.map_resLE G.actionProj.left le_rfl
      (Scheme.Hom.preimage_mono G.actionProj.left hUQ)).trans
    (Scheme.Hom.resLE_map G.actionProj.left le_rfl hUQ).symm

end Transition

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
