/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteAffineImageProjective
import ModularCurves.ForMathlib.FiniteProperClosureCover

/-!
# Chow covers of Noetherian schemes over affine bases

Given a finite affine open cover with dense common intersection, this file assembles the
chartwise projective compactifications into a proper-surjective cover. It first covers the
scheme-theoretic image of the common open, then composes with its proper-surjective closed
inclusion into the original scheme.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover

noncomputable section

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} [Finite ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
variable [IsNoetherian X] [LocallyOfFinitePresentation xπ]

omit [Finite ι] in
/-- The common open of a finite affine cover of a Noetherian scheme is Noetherian. -/
lemma commonOpen_isNoetherian : IsNoetherian (commonOpen U).toScheme := by
  haveI : IsLocallyNoetherian (commonOpen U).toScheme := inferInstance
  haveI : NoetherianSpace X := inferInstance
  haveI : NoetherianSpace (commonOpen U).toScheme :=
    (commonOpen U).ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : CompactSpace (commonOpen U).toScheme := inferInstance
  exact IsNoetherian.mk

private abbrev p : ∀ i, projectiveObj xπ U hU i ⟶ Spec (.of R) :=
  projectiveπ xπ U hU

private abbrev j : ∀ i, (chart U i).toScheme ⟶ projectiveObj xπ U hU i :=
  projectiveOpen xπ U hU

private abbrev q : (commonOpen U).toScheme ⟶ Spec (.of R) :=
  (commonOpen U).ι ≫ xπ

private abbrev g : ∀ i, (commonOpen U).toScheme ⟶ (chart U i).toScheme :=
  toChart U

private abbrev coordinates :
    ∀ i, (commonOpen U).toScheme ⟶ projectiveObj xπ U hU i :=
  fun i ↦ g U i ≫ j xπ U hU i

omit [Finite ι] in
/-- Every common-open coordinate commutes with the structure maps to the affine base. -/
lemma coordinates_comp_p (i : ι) :
    coordinates xπ U hU i ≫ p xπ U hU i = q xπ U := by
  simp only [coordinates, p, j, q, g, Category.assoc,
    projectiveOpen_comp_projectiveπ, chartπ, imageπ,
    toChart_chartι_assoc, Scheme.Hom.toImage_imageι_assoc]

private abbrev hf : ∀ i, coordinates xπ U hU i ≫ p xπ U hU i = q xπ U :=
  coordinates_comp_p xπ U hU

/-- The union of the inverse-image charts in the finite proper closure. -/
noncomputable abbrev chowOpen :
    (FiniteProperClosure.obj (p xπ U hU) (q xπ U)
      (coordinates xπ U hU) (hf xπ U hU)).Opens := by
  letI : ∀ i, IsOpenImmersion (j xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  exact FiniteProperClosure.chartUnion (p xπ U hU) (j xπ U hU)
    (q xπ U) (g U) (hf xπ U hU)

/-- The source scheme of the chosen Chow cover. -/
noncomputable abbrev chowObj : Scheme.{u} := (chowOpen xπ U hU).toScheme

/-- The finite proper closure containing the chosen Chow source as an open subscheme. -/
noncomputable abbrev chowAmbient : Scheme.{u} :=
  FiniteProperClosure.obj (p xπ U hU) (q xπ U)
    (coordinates xπ U hU) (hf xπ U hU)

/-- The structure morphism of the finite proper closure. -/
noncomputable def chowAmbientπ : chowAmbient xπ U hU ⟶ Spec (.of R) :=
  FiniteProperClosure.π (p xπ U hU) (q xπ U)
    (coordinates xπ U hU) (hf xπ U hU)

/-- The chosen Chow source as an open subscheme of its finite proper closure. -/
noncomputable def chowImmersion : chowObj xπ U hU ⟶ chowAmbient xπ U hU :=
  (chowOpen xπ U hU).ι

/-- The ambient finite closure is proper over the affine base. -/
lemma chowAmbientπ_isProper : IsProper (chowAmbientπ xπ U hU) :=
  FiniteProperClosure.π_isProper (p xπ U hU) (q xπ U)
    (coordinates xπ U hU) (hf xπ U hU)
    (projectiveπ_isProper xπ U hU)

/-- The Chow source is open in its ambient finite closure. -/
lemma chowImmersion_isOpenImmersion : IsOpenImmersion (chowImmersion xπ U hU) := by
  unfold chowImmersion
  infer_instance

omit [Finite ι] in
/-- Each image chart structure map agrees with its projective compactification. -/
lemma chartι_comp_imageπ (i : ι) :
    (chart U i).ι ≫ imageπ xπ U =
      j xπ U hU i ≫ p xπ U hU i := by
  exact (projectiveOpen_comp_projectiveπ xπ U hU i).symm

omit [Finite ι] [IsNoetherian X] in
/-- The common open has the same map to the image through every pulled-back chart. -/
lemma toChart_chartι_eq (i k : ι) :
    g U i ≫ (chart U i).ι = g U k ≫ (chart U k).ι := by
  rw [toChart_chartι, toChart_chartι]

/-- The glued map from the finite proper closure chart union to the scheme-theoretic image. -/
noncomputable def chowMap [IsSeparated xπ] : chowObj xπ U hU ⟶ obj U := by
  letI : ∀ i, IsOpenImmersion (j xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : IsSeparated (imageπ xπ U) := by infer_instance
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact
      (FiniteProperClosure.diagonal (p xπ U hU) (q xπ U)
        (coordinates xπ U hU) (hf xπ U hU)) := by infer_instance
  exact FiniteProperClosure.chartUnionToTarget
    (p xπ U hU) (j xπ U hU) (q xπ U) (g U) (hf xπ U hU)
    (fun i ↦ (chart U i).ι) (imageπ xπ U)
    (chartι_comp_imageπ xπ U hU) (toChart_chartι_eq U)

/-- The map to the scheme-theoretic image commutes with the two structure morphisms to the
affine base. -/
lemma chowMap_comp_imageπ [IsSeparated xπ] :
    chowMap xπ U hU ≫ imageπ xπ U =
      chowImmersion xπ U hU ≫ chowAmbientπ xπ U hU := by
  letI : ∀ i, IsOpenImmersion (j xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : IsSeparated (imageπ xπ U) := by infer_instance
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact
      (FiniteProperClosure.diagonal (p xπ U hU) (q xπ U)
        (coordinates xπ U hU) (hf xπ U hU)) := by infer_instance
  unfold chowMap chowImmersion chowAmbientπ
  exact FiniteProperClosure.chartUnionToTarget_comp
    (p xπ U hU) (j xπ U hU) (q xπ U) (g U) (hf xπ U hU)
    (fun i ↦ (chart U i).ι) (imageπ xπ U)
    (chartι_comp_imageπ xπ U hU) (toChart_chartι_eq U)

/-- The glued map to the scheme-theoretic image is proper. -/
lemma chowMap_isProper [IsSeparated xπ] (hcover : ⨆ i, U i = ⊤) :
    IsProper (chowMap xπ U hU) := by
  letI : ∀ i, IsOpenImmersion (j xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : IsSeparated (imageπ xπ U) := by infer_instance
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact
      (FiniteProperClosure.diagonal (p xπ U hU) (q xπ U)
        (coordinates xπ U hU) (hf xπ U hU)) := by infer_instance
  have hcover' : ⨆ i, ((chart U i).ι).opensRange = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using iSup_chart_eq_top U hcover
  exact FiniteProperClosure.chartUnionToTarget_isProper
    (p xπ U hU) (j xπ U hU) (q xπ U) (g U) (hf xπ U hU)
    (fun i ↦ (chart U i).ι) (imageπ xπ U)
    (chartι_comp_imageπ xπ U hU) (toChart_chartι_eq U)
    (projectiveπ_isProper xπ U hU) hcover'

/-- The glued map to the scheme-theoretic image is surjective once a chart index is chosen. -/
lemma chowMap_surjective [IsSeparated xπ] (hcover : ⨆ i, U i = ⊤) (i : ι) :
    Surjective (chowMap xπ U hU) := by
  letI : ∀ i, IsOpenImmersion (j xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : IsSeparated (imageπ xπ U) := by infer_instance
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact
      (FiniteProperClosure.diagonal (p xπ U hU) (q xπ U)
        (coordinates xπ U hU) (hf xπ U hU)) := by infer_instance
  haveI : IsSchemeTheoreticallyDominant (g U i ≫ (chart U i).ι) := by
    rw [toChart_chartι]
    exact toImage_isSchemeTheoreticallyDominant U
  have hcover' : ⨆ i, ((chart U i).ι).opensRange = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using iSup_chart_eq_top U hcover
  exact FiniteProperClosure.chartUnionToTarget_surjective
    (p xπ U hU) (j xπ U hU) (q xπ U) (g U) (hf xπ U hU)
    (fun i ↦ (chart U i).ι) (imageπ xπ U)
    (chartι_comp_imageπ xπ U hU) (toChart_chartι_eq U)
    (projectiveπ_isProper xπ U hU) hcover' i

/-- The chosen Chow cover mapped back to the original Noetherian scheme. -/
noncomputable def chowToTarget [IsSeparated xπ] : chowObj xπ U hU ⟶ X :=
  chowMap xπ U hU ≫ inclusion U

/-- The chosen Chow cover square over the affine base commutes. -/
@[reassoc (attr := simp)]
lemma chowToTarget_comp_xπ [IsSeparated xπ] :
    chowToTarget xπ U hU ≫ xπ =
      chowImmersion xπ U hU ≫ chowAmbientπ xπ U hU := by
  unfold chowToTarget
  rw [Category.assoc]
  exact chowMap_comp_imageπ xπ U hU

/-- The chosen Chow cover is proper over the original scheme. -/
lemma chowToTarget_isProper [IsSeparated xπ] (hcover : ⨆ i, U i = ⊤) :
    IsProper (chowToTarget xπ U hU) := by
  letI : IsProper (chowMap xπ U hU) := chowMap_isProper xπ U hU hcover
  letI : LocallyOfFinitePresentation (inclusion U) := by infer_instance
  letI : IsProper (inclusion U) := {}
  unfold chowToTarget
  infer_instance

/-- A dense common intersection makes the chosen Chow cover surjective over the original
scheme. -/
lemma chowToTarget_surjective [IsSeparated xπ] (hcover : ⨆ i, U i = ⊤)
    (hDense : Dense ((commonOpen U : X.Opens) : Set X)) (i : ι) :
    Surjective (chowToTarget xπ U hU) := by
  letI : Surjective (chowMap xπ U hU) :=
    chowMap_surjective xπ U hU hcover i
  letI : Surjective (inclusion U) := inclusion_surjective U hDense
  unfold chowToTarget
  infer_instance

end

end AlgebraicGeometry.Scheme.FiniteAffineImageCover
