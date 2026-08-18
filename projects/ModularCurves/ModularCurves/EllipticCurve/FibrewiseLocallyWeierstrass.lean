/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafNeighborhoodHOne
import ModularCurves.EllipticCurve.PoleSheafWeierstrassComparison
import ModularCurves.Moduli.EngineDescent

/-!
# Fibrewise elliptic families are locally Weierstrass (FLW-6)

The two final comparison theorems of the fibrewise-elliptic versus locally-Weierstrass
campaign (codex handover 2026-07-29 §3):

* `FibrewiseElliptic.locallyWeierstrass` — a smooth proper fibrewise elliptic family is
  Zariski-locally on the base a projective Weierstrass model;
* `locallyWeierstrass_iff_abstractConditions` — the definitional comparison.

Assembly: per point, the Cartier producer
(`exists_affineBaseChange_sectionCartierGenerator`) gives an affine `V ∋ s` with a
principal zero-section ideal on the `V`-restricted family; `[FLW-2b]`'s
`exists_mem_basicOpen_pointedIso_poleOneBasis` gives a basic open of `V` where the direct
stage family carries `H¹(𝒪([0])) = 0` and a normalized rank-one first-pole basis; the
Cartier data restricts to the basic open and crosses the pointed identification; the
`n = 1` comparison `sectionPoleSheafPower_locallyWeierstrass_of_CartierGenerator` then
produces the Weierstrass presentation, which `LocallyWeierstrass.of_iso_over` carries back
to the restricted family and pullback-composition carries up to the original base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `isoSpec` intertwines the global-sections identification of an open immersion's
image with the scheme-level image identification. -/
private theorem isoSpec_appIso_bridge {S : Scheme.{u}} (W : S.affineOpens)
    (U' : W.1.toScheme.affineOpens) :
    U'.2.isoSpec.hom ≫ Spec.map (W.1.ι.appIso U'.1).hom =
      (W.1.ι.isoImage U'.1).hom ≫
        (U'.2.image_of_isOpenImmersion W.1.ι).isoSpec.hom := by
  have hVle : U'.1 ≤ W.1.ι ⁻¹ᵁ (W.1.ι ''ᵁ U'.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq W.1.ι U'.1).symm
  have happLE : (W.1.ι.appIso U'.1).hom =
      W.1.ι.appLE (W.1.ι ''ᵁ U'.1) U'.1 hVle :=
    Scheme.Hom.appIso_hom' W.1.ι U'.1
  rw [happLE,
    isoSpec_appLE_bridge W.1.ι ⟨W.1.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion W.1.ι⟩
      U' hVle]
  congr 1
  rw [← cancel_mono (W.1.ι ''ᵁ U'.1).ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]

/-- **(chart lift)** A Weierstrass chart of the restriction of a pointed family to an
affine open lifts to a Weierstrass chart of the family itself. Tools per the board
`[FLW-6] chart-lift factorization`: `Scheme.Hom.isoImage` (+ `isoImage_hom_ι`),
`Scheme.Hom.appIso`, `IsAffineOpen.image_of_isOpenImmersion`, `WeierstrassCurve.map`
(elliptic instance), `projModelBaseChangeOf` + `isPullback_projModelBaseChangeOf`,
`isoSpec_appLE_bridge`, and the `IsPullback.of_iso`/`isoPullback` choreography of
`exists_pointedIso_direct_pullback`. -/
private theorem lw_point_of_baseChange_affineOpen
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    (W : S.affineOpens) {s : S} (hs : s ∈ W.1)
    (hpt : ∃ (U' : W.1.toScheme.affineOpens) (_ : (⟨s, hs⟩ : W.1.toScheme) ∈ U'.1)
      (Wc : WeierstrassCurve Γ(W.1.toScheme, U'.1)),
      Wc.IsElliptic ∧
      ∃ e : pullback (pullback.snd π W.1.ι) U'.1.ι ≅ projModel Wc,
        e.hom ≫ projModelπ Wc =
          pullback.snd (pullback.snd π W.1.ι) U'.1.ι ≫ U'.2.isoSpec.hom ∧
        (U'.2.isoSpec.inv ≫ pullback.lift (U'.1.ι ≫ sectionBaseChange z hz W.1.ι)
            (𝟙 _) (by
              rw [Category.assoc, sectionBaseChange_snd, Category.comp_id,
                Category.id_comp])) ≫ e.hom = projModelZero Wc) :
    ∃ (U : S.affineOpens) (_ : s ∈ U.1) (Wc : WeierstrassCurve Γ(S, U.1)),
      Wc.IsElliptic ∧
      ∃ e : pullback π U.1.ι ≅ projModel Wc,
        e.hom ≫ projModelπ Wc = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) ≫ e.hom =
          projModelZero Wc := by
  classical
  obtain ⟨U', hsU', Wc, hell, e₁, heπ, hez⟩ := hpt
  haveI : IsAffine W.1.toScheme := W.2
  -- the image affine open, the ring identification, and the transported curve
  refine ⟨⟨W.1.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion W.1.ι⟩,
    ⟨⟨s, hs⟩, hsU', rfl⟩, Wc.map (W.1.ι.appIso U'.1).inv.hom, inferInstance, ?_⟩
  set U : S.affineOpens :=
    ⟨W.1.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion W.1.ι⟩ with hU
  have hmap : (Wc.map (W.1.ι.appIso U'.1).inv.hom).map
      (W.1.ι.appIso U'.1).hom.hom = Wc := by
    rw [WeierstrassCurve.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id,
      CommRingCat.hom_id, WeierstrassCurve.map_id]
  set β := projModelBaseChangeOf (W.1.ι.appIso U'.1).hom.hom
    (Wc.map (W.1.ι.appIso U'.1).inv.hom) Wc hmap with hβdef
  have hβsq := isPullback_projModelBaseChangeOf (W.1.ι.appIso U'.1).hom.hom
    (Wc.map (W.1.ι.appIso U'.1).inv.hom) Wc hmap
  haveI : IsIso (Spec.map (CommRingCat.ofHom (W.1.ι.appIso U'.1).hom.hom)) := by
    have : CommRingCat.ofHom (W.1.ι.appIso U'.1).hom.hom =
        (W.1.ι.appIso U'.1).hom := rfl
    rw [this]
    infer_instance
  haveI : IsIso β := by
    rw [show β = hβsq.isoPullback.hom ≫ pullback.fst _ _ from
      hβsq.isoPullback_hom_fst.symm]
    infer_instance
  -- the scheme-level identification of the two restricted total spaces
  set eIm := W.1.ι.isoImage U'.1 with heIm
  have hι : U'.1.ι ≫ W.1.ι = eIm.hom ≫ U.1.ι :=
    (Scheme.Hom.isoImage_hom_ι W.1.ι U'.1).symm
  set ψ₁ := pullbackLeftPullbackSndIso π W.1.ι U'.1.ι with hψ₁
  set ψ₂ := pullback.congrHom (rfl : π = π) hι with hψ₂
  set ψ₃ := (pullbackLeftPullbackSndIso π U.1.ι eIm.hom).symm with hψ₃
  haveI : IsIso (pullback.fst (pullback.snd π U.1.ι) eIm.hom) := inferInstance
  set ψ₄ := asIso (pullback.fst (pullback.snd π U.1.ι) eIm.hom) with hψ₄
  -- the two shared bridge identities
  have hVle : U'.1 ≤ W.1.ι ⁻¹ᵁ U.1 :=
    le_of_eq (Scheme.Hom.preimage_image_eq W.1.ι U'.1).symm
  have hbridge : U'.2.isoSpec.hom ≫
      Spec.map (W.1.ι.appIso U'.1).hom =
      eIm.hom ≫ U.2.isoSpec.hom :=
    isoSpec_appIso_bridge W U'
  have hψ₄snd : ψ₄.inv ≫ pullback.snd (pullback.snd π U.1.ι) eIm.hom =
      pullback.snd π U.1.ι ≫ eIm.inv := by
    rw [← cancel_mono eIm.hom, Category.assoc, Category.assoc,
      ← pullback.condition, ← Category.assoc, hψ₄]
    simp
  have hofHom : CommRingCat.ofHom (W.1.ι.appIso U'.1).hom.hom =
      (W.1.ι.appIso U'.1).hom := rfl
  have hψ₂snd : ψ₂.inv ≫ pullback.snd π (U'.1.ι ≫ W.1.ι) =
      pullback.snd π (eIm.hom ≫ U.1.ι) := by
    rw [hψ₂]
    simp only [pullback.congrHom_inv]
    rw [pullback.lift_snd, Category.comp_id]
  have hψ₃snd : ψ₃.inv ≫ pullback.snd π (eIm.hom ≫ U.1.ι) =
      pullback.snd (pullback.snd π U.1.ι) eIm.hom := by
    rw [hψ₃, Iso.symm_inv]
    exact pullbackLeftPullbackSndIso_hom_snd π U.1.ι eIm.hom
  have hψ₂fst : ψ₂.inv ≫ pullback.fst π (U'.1.ι ≫ W.1.ι) =
      pullback.fst π (eIm.hom ≫ U.1.ι) := by
    rw [hψ₂]
    simp only [pullback.congrHom_inv]
    rw [pullback.lift_fst, Category.comp_id]
  have hψ₃fst : ψ₃.inv ≫ pullback.fst π (eIm.hom ≫ U.1.ι) =
      pullback.fst (pullback.snd π U.1.ι) eIm.hom ≫ pullback.fst π U.1.ι := by
    rw [hψ₃, Iso.symm_inv]
    exact pullbackLeftPullbackSndIso_hom_fst π U.1.ι eIm.hom
  have hψ₄fst : ψ₄.inv ≫ pullback.fst (pullback.snd π U.1.ι) eIm.hom = 𝟙 _ := by
    rw [hψ₄]
    exact IsIso.inv_hom_id _
  have hbridge' : U.2.isoSpec.inv ≫ eIm.inv =
      Spec.map (W.1.ι.appIso U'.1).inv ≫ U'.2.isoSpec.inv := by
    rw [← cancel_mono (eIm.hom ≫ U.2.isoSpec.hom)]
    have hR : (Spec.map (W.1.ι.appIso U'.1).inv ≫ U'.2.isoSpec.inv) ≫
        eIm.hom ≫ U.2.isoSpec.hom = 𝟙 _ := by
      rw [← hbridge, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp,
        Iso.hom_inv_id, Spec.map_id]
    rw [hR]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  refine ⟨ψ₄.symm ≪≫ ψ₃.symm ≪≫ ψ₂.symm ≪≫ ψ₁.symm ≪≫ e₁ ≪≫ asIso β, ?_, ?_⟩
  · -- π-compatibility: chase the second projection down the iso chain
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    have hβw : β ≫ projModelπ (Wc.map (W.1.ι.appIso U'.1).inv.hom) =
        projModelπ Wc ≫ Spec.map (W.1.ι.appIso U'.1).hom := by
      rw [← hofHom]
      exact hβsq.w
    rw [hβw, reassoc_of% heπ, hbridge]
    rw [hψ₁, reassoc_of% (pullbackLeftPullbackSndIso_inv_snd_snd π W.1.ι U'.1.ι)]
    rw [reassoc_of% hψ₂snd]
    rw [reassoc_of% hψ₃snd, reassoc_of% hψ₄snd]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  · -- zero-section compatibility
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    -- the zero section transports along the base-change square
    have hβzero : projModelZero Wc ≫ β =
        Spec.map (W.1.ι.appIso U'.1).hom ≫
          projModelZero (Wc.map (W.1.ι.appIso U'.1).inv.hom) := by
      have htrans : ∀ {R : Type u} [inst : CommRing R]
          (W₁ W₂ : WeierstrassCurve R) (h : W₁ = W₂),
          projModelZero W₁ ≫ eqToHom (congrArg projModel h) = projModelZero W₂ := by
        rintro R _ W₁ W₂ rfl
        simp
      rw [hβdef, projModelBaseChangeOf, ← Category.assoc,
        htrans _ _ hmap.symm]
      letI : Algebra ↑Γ(S, U.1) ↑Γ(W.1.toScheme, U'.1) :=
        (W.1.ι.appIso U'.1).hom.hom.toAlgebra
      have halg : algebraMap ↑Γ(S, U.1) ↑Γ(W.1.toScheme, U'.1) =
          (W.1.ι.appIso U'.1).hom.hom := rfl
      have := projModelZero_baseChange
        (R := ↑Γ(S, U.1)) (R' := ↑Γ(W.1.toScheme, U'.1))
        (Wc.map (W.1.ι.appIso U'.1).inv.hom)
      rw [halg] at this
      exact this
    -- the section lift transports along the pullback chain
    have hlift : U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) ≫
          ψ₄.inv ≫ ψ₃.inv ≫ ψ₂.inv ≫ ψ₁.inv =
        Spec.map (W.1.ι.appIso U'.1).inv ≫ U'.2.isoSpec.inv ≫
          pullback.lift (U'.1.ι ≫ sectionBaseChange z hz W.1.ι) (𝟙 _)
            (by rw [Category.assoc, sectionBaseChange_snd, Category.comp_id,
              Category.id_comp]) := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · -- component into the total space `E`
          simp only [Category.assoc, hψ₁]
          rw [pullbackLeftPullbackSndIso_inv_fst π W.1.ι U'.1.ι,
            hψ₂fst, hψ₃fst, reassoc_of% hψ₄fst]
          rw [pullback.lift_fst, pullback.lift_fst_assoc]
          simp only [Category.assoc]
          rw [sectionBaseChange_fst z hz W.1.ι]
          rw [show U.2.isoSpec.inv ≫ U.1.ι ≫ z =
              (U.2.isoSpec.inv ≫ eIm.inv) ≫ (eIm.hom ≫ U.1.ι) ≫ z from by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]]
          rw [hbridge', ← hι]
          simp only [Category.assoc]
        · -- component into the intermediate base `W`
          simp only [Category.assoc, hψ₁]
          rw [pullbackLeftPullbackSndIso_inv_fst_snd π W.1.ι U'.1.ι,
            reassoc_of% hψ₂snd, reassoc_of% hψ₃snd, reassoc_of% hψ₄snd,
            pullback.lift_snd_assoc, Category.id_comp,
            pullback.lift_fst_assoc]
          simp only [Category.assoc]
          rw [sectionBaseChange_snd z hz W.1.ι, Category.comp_id]
          rw [reassoc_of% hbridge']
      · -- component into `U'`
        simp only [Category.assoc, hψ₁]
        rw [pullbackLeftPullbackSndIso_inv_snd_snd π W.1.ι U'.1.ι,
          hψ₂snd, hψ₃snd, hψ₄snd,
          pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd,
          Category.comp_id]
        exact hbridge'
    rw [reassoc_of% hlift, reassoc_of% hez, hβzero,
      ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

/-- **(FLW-6, affine case)** A smooth proper fibrewise elliptic family over an affine
base is locally Weierstrass. -/
theorem FibrewiseElliptic.locallyWeierstrass_of_isAffine
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S} [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (hproper : IsProper π)
    (h : FibrewiseElliptic π z hz) :
    LocallyWeierstrass π z hz := by
  haveI : IsSeparated π := inferInstance
  intro s
  -- (a) an affine neighbourhood carrying a Cartier generator of the section ideal
  obtain ⟨V, hsV, U, hUtop, r, hspan, hnzd⟩ :=
    exists_affineBaseChange_sectionCartierGenerator hsm z hz s
  haveI : IsAffine V.1.toScheme := V.2
  haveI : IsProper (pullback.snd π V.1.ι) :=
    MorphismProperty.pullback_snd _ _ hproper
  have hsmV : SmoothOfRelativeDimension 1 (pullback.snd π V.1.ι) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π V.1.ι) hsm
  have hV : FibrewiseElliptic (pullback.snd π V.1.ι)
      (sectionBaseChange z hz V.1.ι) (sectionBaseChange_snd z hz V.1.ι) :=
    h.baseChange V.1.ι
  -- (b) the basic open with the pole package, the pointed identification, `H¹ = 0`,
  -- and the normalized rank-one basis
  obtain ⟨a, hmem, E', π'', z'', hz'', hproper'', hsm'', h'', hiso,
    hH1, bOne, hbOne⟩ :=
    FibrewiseElliptic.exists_mem_basicOpen_pointedIso_poleOneBasis hsmV
      (sectionBaseChange z hz V.1.ι) (sectionBaseChange_snd z hz V.1.ι) hV ⟨s, hsV⟩
  haveI := hproper''
  -- names for the basic-open leg
  set ιa : (V.1.toScheme.basicOpen a).toScheme ⟶ V.1.toScheme :=
    (V.1.toScheme.basicOpen a).ι with hιa
  haveI : IsAffineOpen (V.1.toScheme.basicOpen a) :=
    (isAffineOpen_top V.1.toScheme).basicOpen a
  haveI : IsAffine (V.1.toScheme.basicOpen a).toScheme :=
    ‹IsAffineOpen (V.1.toScheme.basicOpen a)›
  -- (c) restrict the Cartier data along the basic open
  set g' : pullback (pullback.snd π V.1.ι) ιa ⟶ pullback π V.1.ι :=
    pullback.fst (pullback.snd π V.1.ι) ιa with hg'
  have hU₁aff : IsAffineOpen (g' ⁻¹ᵁ U.1) :=
    IsAffineOpen.preimage_pullback_fst (pullback.snd π V.1.ι) ιa U.2
  set U₁ : (pullback (pullback.snd π V.1.ι) ιa).affineOpens :=
    ⟨g' ⁻¹ᵁ U.1, hU₁aff⟩ with hU₁
  set za : (V.1.toScheme.basicOpen a).toScheme ⟶
      pullback (pullback.snd π V.1.ι) ιa :=
    sectionBaseChange (sectionBaseChange z hz V.1.ι)
      (sectionBaseChange_snd z hz V.1.ι) ιa with hza
  have hzatop : za ⁻¹ᵁ U₁.1 = ⊤ := by
    have hcomp : za ≫ g' = ιa ≫ sectionBaseChange z hz V.1.ι :=
      sectionBaseChange_fst _ _ _
    rw [hU₁]
    rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hUtop]
    ext x
    simp
  set r₁ : Γ(pullback (pullback.snd π V.1.ι) ιa, U₁.1) :=
    affinePullbackSection g' U₁ U le_rfl r with hr₁
  have hker₁ : za.ker = (sectionBaseChange z hz V.1.ι).ker.comap g' :=
    RelEffCartierDiv.ker_sectionBaseChange (sectionBaseChange z hz V.1.ι)
      (sectionBaseChange_snd z hz V.1.ι) ιa
  have hspan₁ : za.ker.ideal U₁ = Ideal.span {r₁} := by
    rw [hker₁]
    exact ideal_comap_affineOpens_span _ g' U₁ U le_rfl r hspan
  have hnzd₁ : r₁ ∈ nonZeroDivisors Γ(pullback (pullback.snd π V.1.ι) ιa, U₁.1) :=
    affinePullbackSection_mem_nonZeroDivisors g' U₁ U le_rfl hnzd
  -- (d) cross the Cartier data to the direct family along the pointed identification
  obtain ⟨eC, hCπ, hCz⟩ := hiso
  haveI : IsIso eC.hom := inferInstance
  have hU₂aff : IsAffineOpen (eC.hom ⁻¹ᵁ U₁.1) := U₁.2.preimage eC.hom
  set U₂ : E'.affineOpens := ⟨eC.hom ⁻¹ᵁ U₁.1, hU₂aff⟩ with hU₂
  have hz''U₂ : z'' ⁻¹ᵁ U₂.1 = ⊤ := by
    rw [hU₂]
    rw [← Scheme.Hom.comp_preimage, hCz, hzatop]
  set r₂ : Γ(E', U₂.1) := affinePullbackSection eC.hom U₂ U₁ le_rfl r₁ with hr₂
  have hker₂ : z''.ker = za.ker.comap eC.hom := by
    haveI : IsClosedImmersion
        (za ≫ pullback.snd (pullback.snd π V.1.ι) ιa) := by
      rw [sectionBaseChange_snd]
      infer_instance
    haveI : IsClosedImmersion za :=
      IsClosedImmersion.of_comp za (pullback.snd (pullback.snd π V.1.ι) ιa)
    have hsq : z'' ≫ eC.hom = 𝟙 _ ≫ za := by
      rw [Category.id_comp, hCz]
    have hlift_fst : pullback.lift z'' (𝟙 _) hsq ≫ pullback.fst eC.hom za = z'' :=
      pullback.lift_fst _ _ _
    haveI : IsIso (pullback.snd eC.hom za) :=
      inferInstance
    haveI : IsIso (pullback.lift z'' (𝟙 _) hsq) := by
      have hsnd : pullback.lift z'' (𝟙 _) hsq ≫ pullback.snd eC.hom za = 𝟙 _ :=
        pullback.lift_snd _ _ _
      exact (IsIso.of_isIso_fac_right hsnd)
    rw [← hlift_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hspan₂ : z''.ker.ideal U₂ = Ideal.span {r₂} := by
    rw [hker₂]
    exact ideal_comap_affineOpens_span _ eC.hom U₂ U₁ le_rfl r₁ hspan₁
  have hnzd₂ : r₂ ∈ nonZeroDivisors Γ(E', U₂.1) :=
    affinePullbackSection_mem_nonZeroDivisors eC.hom U₂ U₁ le_rfl hnzd₁
  -- (e) the Weierstrass comparison on the direct family
  have hLW'' : LocallyWeierstrass π'' z'' hz'' :=
    sectionPoleSheafPower_locallyWeierstrass_of_CartierGenerator hsm'' z'' hz'' h''
      U₂ hz''U₂ r₂ hspan₂ hnzd₂ hH1 bOne hbOne
  -- (f) transport back to the basic-open family through the pointed identification
  have hLWa : LocallyWeierstrass (pullback.snd (pullback.snd π V.1.ι) ιa) za
      (sectionBaseChange_snd (sectionBaseChange z hz V.1.ι)
        (sectionBaseChange_snd z hz V.1.ι) ιa) := by
    refine LocallyWeierstrass.of_iso_over hLW'' eC.symm ?_ ?_
    · rw [Iso.symm_hom, ← hCπ, Iso.inv_hom_id_assoc]
    · rw [Iso.symm_hom, ← hCz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- (g) lift the chart twice: basic open → V, then V → S
  refine lw_point_of_baseChange_affineOpen (hz := hz) V hsV ?_
  exact lw_point_of_baseChange_affineOpen
    (hz := sectionBaseChange_snd z hz V.1.ι)
    (S := V.1.toScheme) ⟨V.1.toScheme.basicOpen a, ‹_›⟩ hmem
    (hLWa ⟨⟨s, hsV⟩, hmem⟩)

/-- **(FLW final 1, handover §3)** A smooth proper fibrewise elliptic family is locally
Weierstrass. -/
theorem FibrewiseElliptic.locallyWeierstrass
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    (hsm : SmoothOfRelativeDimension 1 π) (hproper : IsProper π)
    (h : FibrewiseElliptic π z hz) :
    LocallyWeierstrass π z hz := by
  intro s
  -- an affine open of the base around the point
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s)
      (isOpen_univ (X := S))
  let Vaff : S.affineOpens := ⟨V, hVaff⟩
  haveI : IsAffine Vaff.1.toScheme := hVaff
  haveI : IsProper (pullback.snd π Vaff.1.ι) :=
    MorphismProperty.pullback_snd _ _ hproper
  have hsmV : SmoothOfRelativeDimension 1 (pullback.snd π Vaff.1.ι) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π Vaff.1.ι) hsm
  have hV : FibrewiseElliptic (pullback.snd π Vaff.1.ι)
      (sectionBaseChange z hz Vaff.1.ι)
      (sectionBaseChange_snd z hz Vaff.1.ι) :=
    h.baseChange Vaff.1.ι
  exact lw_point_of_baseChange_affineOpen Vaff hsV
    (FibrewiseElliptic.locallyWeierstrass_of_isAffine hsmV inferInstance hV ⟨s, hsV⟩)

/-- **(FLW final 2, handover §3)** A pointed family is locally Weierstrass exactly when
it is smooth of relative dimension one, proper, and fibrewise elliptic. -/
theorem locallyWeierstrass_iff_abstractConditions
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S} :
    LocallyWeierstrass π z hz ↔
      SmoothOfRelativeDimension 1 π ∧ IsProper π ∧ FibrewiseElliptic π z hz := by
  constructor
  · intro hLW
    exact ⟨RouteA.smoothOfRelativeDimension_of_locallyWeierstrass hLW,
      RouteA.isProper_of_locallyWeierstrass hLW, hLW.fibrewiseElliptic⟩
  · rintro ⟨hsm, hproper, h⟩
    exact FibrewiseElliptic.locallyWeierstrass hsm hproper h

end ModularCurves
