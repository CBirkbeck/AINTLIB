/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Naturality of `Proj.fromOfGlobalSections` under `Proj.map`

A morphism `X ⟶ Proj ℬ` out of a scheme is built by `Proj.fromOfGlobalSections ℬ f hf` from a
ring hom `f : B →+* Γ(X, ⊤)` whose image of the irrelevant ideal generates the unit ideal.
For a graded ring hom `g : 𝒜 →+*ᵍ ℬ` (with the irrelevant-ideal hypothesis of `Proj.map`),
composing with the contravariant `Proj.map g` precomposes the coordinate reader `f` by `g`:
`fromOfGlobalSections ℬ f hf ≫ Proj.map g hg = fromOfGlobalSections 𝒜 (f ∘ g) hf'`.

Geometrically: rescaling the homogeneous coordinates does not move a point, so a point of
`Proj ℬ` given by `f`, pushed through `Proj.map g`, is the point of `Proj 𝒜` read off by `f ∘ g`.

This is the scheme-level input for identifying `Proj`-endomorphisms of a Weierstrass model on
the section at infinity (T-W7.0b, `negModelHom_zero`).

## Main results

* `Proj.fromOfGlobalSections_map`: naturality under a target-side `Proj.map`.
* `Proj.fromOfGlobalSections_comp`: naturality under source precomposition.
* `Proj.toBasicOpenOfGlobalSections_map`: the per-chart form it is glued from.
* `Proj.irrelevant_map_comp_toRingHom_eq_top`: the hypothesis transport supplying the
  irrelevant-ideal condition on `f ∘ g` from the one on `f`.

AINTLIB ModularCurves (T-W7.0b infrastructure); upstream candidate.
-/

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj Limits

namespace AlgebraicGeometry.Proj

universe u

variable {A B : Type u} {σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {X : Scheme.{u}}

/-- Hypothesis transport for `fromOfGlobalSections_map`: if `f` sends `ℬ`'s irrelevant ideal
to a generating set and the graded hom `g` covers (`ℬ₊ ≤ 𝒜₊.map g`), then `f ∘ g` sends
`𝒜`'s irrelevant ideal to a generating set. -/
lemma irrelevant_map_comp_toRingHom_eq_top {C : Type u} [CommRing C]
    (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g)
    (f : B →+* C) (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hf, ← Ideal.map_map]
  refine Ideal.map_mono ?_
  have h := toIdeal_le_toIdeal_iff.mpr hg
  rwa [HomogeneousIdeal.toIdeal_map] at h

/-- The per-chart form of `fromOfGlobalSections_map`: on the basic open `D(g t)`, the point
map `toBasicOpenOfGlobalSections ℬ f` followed by `Proj.map g` agrees with
`toBasicOpenOfGlobalSections 𝒜 (f ∘ g)`. -/
lemma toBasicOpenOfGlobalSections_map
    (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g)
    (f : B →+* Γ(X, ⊤)) {t : A} {d : ℕ} (hdpos : 0 < d) (ht : t ∈ 𝒜 d) :
    toBasicOpenOfGlobalSections ℬ f (rfl : f (g t) = f (g t)) hdpos (g.map_mem ht) ≫
        (basicOpen ℬ (g t)).ι ≫ map g hg =
      toBasicOpenOfGlobalSections 𝒜 (f.comp g.toRingHom) rfl hdpos ht ≫ (basicOpen 𝒜 t).ι := by
  simp only [toBasicOpenOfGlobalSections, Category.assoc, basicOpenIsoSpec_inv_ι,
    basicOpenIsoSpec_inv_ι_assoc, RingHom.comp_apply, GradedRingHom.coe_toRingHom]
  rw [awayι_comp_map g hg hdpos t ht, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  refine congrArg (· ≫ awayι 𝒜 t ht hdpos) (congrArg Spec.map (congrArg CommRingCat.ofHom ?_))
  ext y
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    GradedRingHom.coe_toRingHom]

/-- **Naturality of `Proj.fromOfGlobalSections` under `Proj.map`.** For a graded ring hom
`g : 𝒜 →+*ᵍ ℬ`, composing the point map `fromOfGlobalSections ℬ f` with the (contravariant)
`Proj.map g` precomposes the coordinate reader `f` by `g`. -/
theorem fromOfGlobalSections_map
    (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g)
    (f : B →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤) :
    fromOfGlobalSections ℬ f hf ≫ map g hg =
      fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (f.comp g.toRingHom) hf').hom_ext _ _ fun s ↦ ?_
  obtain ⟨i, r, hi, hr⟩ := s
  have eL : (X.basicOpen (f (g.toRingHom r))).ι ≫ fromOfGlobalSections ℬ f hf =
      toBasicOpenOfGlobalSections ℬ f rfl hi (g.map_mem hr) ≫ (basicOpen ℬ (g.toRingHom r)).ι := by
    rw [← fromOfGlobalSections_resLE ℬ f hf hi (g.map_mem hr), Scheme.Hom.resLE_comp_ι]
  have eR : (X.basicOpen ((f.comp g.toRingHom) r)).ι ≫
      fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hf' =
      toBasicOpenOfGlobalSections 𝒜 (f.comp g.toRingHom) rfl hi hr ≫ (basicOpen 𝒜 r).ι := by
    rw [← fromOfGlobalSections_resLE 𝒜 (f.comp g.toRingHom) hf' hi hr, Scheme.Hom.resLE_comp_ι]
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  show (X.basicOpen (f (g.toRingHom r))).ι ≫ fromOfGlobalSections ℬ f hf ≫ map g hg =
       (X.basicOpen ((f.comp g.toRingHom) r)).ι ≫ fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hf'
  rw [reassoc_of% eL, eR]
  exact toBasicOpenOfGlobalSections_map g hg f hi hr

section SourceNaturality

variable {Y : Scheme.{u}}

private noncomputable def sourceBasicOpenTopRestriction
    (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    Γ(X, ⊤) →+* Γ((X.basicOpen r).toScheme, ⊤) :=
  (X.basicOpen r).topIso.inv.hom.comp
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom

private lemma sourceBasicOpenTopRestriction_isUnit
    (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    IsUnit (sourceBasicOpenTopRestriction X r r) := by
  exact (AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
    X.toRingedSpace r).map (X.basicOpen r).topIso.inv.hom

private lemma basicOpen_ι_appTop
    (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (X.basicOpen r).ι.appTop =
      CommRingCat.ofHom (sourceBasicOpenTopRestriction X r) := by
  apply CommRingCat.hom_ext
  rw [Scheme.Opens.ι_appTop]
  simp only [sourceBasicOpenTopRestriction,
    Scheme.Opens.topIso_inv]
  change (X.presheaf.map _).hom =
    (X.presheaf.map _ ≫ X.presheaf.map _).hom
  rw [← Functor.map_comp]
  congr 1

private lemma basicOpen_toSpecAway
    (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    let ρ := sourceBasicOpenTopRestriction X r
    let ψ := Localization.awayLift ρ r
      (sourceBasicOpenTopRestriction_isUnit X r)
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen r)).inv ≫
          X.toSpecΓ ∣_ PrimeSpectrum.basicOpen r ≫
        (basicOpenIsoSpecAway r).hom =
      (X.basicOpen r).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ψ) := by
  dsimp only
  let ρ := sourceBasicOpenTopRestriction X r
  let ψ := Localization.awayLift ρ r
    (sourceBasicOpenTopRestriction_isUnit X r)
  have hψ : ψ.comp
      (algebraMap Γ(X, ⊤) (Localization.Away r)) = ρ := by
    simpa only [ψ] using
      IsLocalization.Away.lift_comp
        (S := Localization.Away r) (g := ρ) (x := r)
          (sourceBasicOpenTopRestriction_isUnit X r)
  have hspec :
      Spec.map (CommRingCat.ofHom ψ) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, ⊤) (Localization.Away r))) =
        Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  rw [← cancel_mono
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (Localization.Away r))))]
  slice_lhs 3 4 =>
    rw [basicOpenIsoSpecAway_hom_SpecMap]
  slice_lhs 2 3 =>
    rw [morphismRestrict_ι X.toSpecΓ
      (PrimeSpectrum.basicOpen r :
        (Spec (CommRingCat.of Γ(X, ⊤))).Opens)]
  slice_lhs 1 2 =>
    rw [Scheme.isoOfEq_inv_ι]
  change (X.basicOpen r).ι ≫ X.toSpecΓ =
    (X.basicOpen r).toScheme.toSpecΓ ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, ⊤) (Localization.Away r))))
  calc
    (X.basicOpen r).ι ≫ X.toSpecΓ =
        (X.basicOpen r).toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom ρ) := by
      have hρ := basicOpen_ι_appTop X r
      rw [Scheme.toSpecΓ_naturality, hρ]
      rfl
    _ = (X.basicOpen r).toScheme.toSpecΓ ≫
          (Spec.map (CommRingCat.ofHom ψ) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap Γ(X, ⊤)
                (Localization.Away r)))) := by
      exact (congrArg
        ((X.basicOpen r).toScheme.toSpecΓ ≫ ·) hspec).symm

private noncomputable def sourceAwayMap
    {C D : Type u} [CommRing C] [CommRing D]
    (f : C →+* D) (t : C) :
    Localization.Away t →+* Localization.Away (f t) :=
  IsLocalization.map (M := Submonoid.powers t)
    (T := Submonoid.powers (f t))
    (Localization.Away (f t)) f (by
      rw [← Submonoid.map_le_iff_le_comap,
        Submonoid.map_powers])

private lemma toBasicOpenOfGlobalSections_chart
    (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ}
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    let ρ := sourceBasicOpenTopRestriction X (f t)
    let ψ := Localization.awayLift ρ (f t)
      (sourceBasicOpenTopRestriction_isUnit X (f t))
    let μ := sourceAwayMap f t
    toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫
        (basicOpenIsoSpec 𝒜 t hd h0d).hom =
      (X.basicOpen (f t)).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (ψ.comp (μ.comp
            (algebraMap (Away 𝒜 t)
              (Localization.Away t))))) := by
  dsimp only
  simp only [toBasicOpenOfGlobalSections, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% basicOpen_toSpecAway]
  have hspec :
      Spec.map (CommRingCat.ofHom
          (Localization.awayLift
            (sourceBasicOpenTopRestriction X (f t)) (f t)
              (sourceBasicOpenTopRestriction_isUnit X (f t)))) ≫
        Spec.map (CommRingCat.ofHom
          ((IsLocalization.map (M := Submonoid.powers t)
            (T := Submonoid.powers (f t))
              (Localization.Away (f t)) f (by
                rw [← Submonoid.map_le_iff_le_comap,
                  Submonoid.map_powers])).comp
            (algebraMap (Away 𝒜 t)
              (Localization.Away t)))) =
      Spec.map (CommRingCat.ofHom
        ((Localization.awayLift
          (sourceBasicOpenTopRestriction X (f t)) (f t)
            (sourceBasicOpenTopRestriction_isUnit X (f t))).comp
          ((sourceAwayMap f t).comp
            (algebraMap (Away 𝒜 t)
              (Localization.Away t))))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact congrArg
    ((X.basicOpen (f t)).toScheme.toSpecΓ ≫ ·) hspec

private lemma sourceBasicOpenTopRestriction_naturality
    (g : Y ⟶ X) (r : Γ(X, ⊤)) :
    let gD := g.resLE (X.basicOpen r)
      (Y.basicOpen (g.appTop.hom r))
      (Scheme.preimage_basicOpen_top g r).ge
    gD.appTop.hom.comp
        (sourceBasicOpenTopRestriction X r) =
      (sourceBasicOpenTopRestriction Y (g.appTop.hom r)).comp
        g.appTop.hom := by
  dsimp only
  have hcomp := Scheme.Hom.resLE_comp_ι g
    (Scheme.preimage_basicOpen_top g r).ge
  have happ := congrArg Scheme.Hom.appTop hcomp
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    basicOpen_ι_appTop, basicOpen_ι_appTop] at happ
  exact congrArg CommRingCat.Hom.hom happ

private lemma sourceAwayMap_comp_algebraMap
    {C : Type u} [CommRing C] (f : A →+* C) (t : A) :
    (sourceAwayMap f t).comp
        (algebraMap A (Localization.Away t)) =
      (algebraMap C (Localization.Away (f t))).comp f := by
  unfold sourceAwayMap
  exact IsLocalization.map_comp _

private lemma awayLift_naturality
    (g : Y ⟶ X) (r : Γ(X, ⊤)) :
    let gD := g.resLE (X.basicOpen r)
      (Y.basicOpen (g.appTop.hom r))
      (Scheme.preimage_basicOpen_top g r).ge
    let ρX := sourceBasicOpenTopRestriction X r
    let ρY := sourceBasicOpenTopRestriction Y (g.appTop.hom r)
    let ψX := Localization.awayLift ρX r
      (sourceBasicOpenTopRestriction_isUnit X r)
    let ψY := Localization.awayLift ρY (g.appTop.hom r)
      (sourceBasicOpenTopRestriction_isUnit Y (g.appTop.hom r))
    let ν := sourceAwayMap g.appTop.hom r
    gD.appTop.hom.comp ψX = ψY.comp ν := by
  dsimp only
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  calc
    ((g.resLE (X.basicOpen r)
          (Y.basicOpen (g.appTop.hom r))
          (Scheme.preimage_basicOpen_top g r).ge).appTop.hom.comp
          (Localization.awayLift
            (sourceBasicOpenTopRestriction X r) r
              (sourceBasicOpenTopRestriction_isUnit X r))).comp
          (algebraMap Γ(X, ⊤) (Localization.Away r)) =
        (g.resLE (X.basicOpen r)
          (Y.basicOpen (g.appTop.hom r))
          (Scheme.preimage_basicOpen_top g r).ge).appTop.hom.comp
          (sourceBasicOpenTopRestriction X r) := by
            rw [RingHom.comp_assoc,
              IsLocalization.Away.lift_comp]
    _ = (sourceBasicOpenTopRestriction Y
          (g.appTop.hom r)).comp g.appTop.hom :=
      sourceBasicOpenTopRestriction_naturality g r
    _ = (Localization.awayLift
            (sourceBasicOpenTopRestriction Y (g.appTop.hom r))
            (g.appTop.hom r)
            (sourceBasicOpenTopRestriction_isUnit Y
              (g.appTop.hom r))).comp
          ((algebraMap Γ(Y, ⊤)
            (Localization.Away (g.appTop.hom r))).comp
              g.appTop.hom) := by
        rw [← RingHom.comp_assoc,
          IsLocalization.Away.lift_comp]
    _ = (Localization.awayLift
            (sourceBasicOpenTopRestriction Y (g.appTop.hom r))
            (g.appTop.hom r)
            (sourceBasicOpenTopRestriction_isUnit Y
              (g.appTop.hom r))).comp
          ((sourceAwayMap g.appTop.hom r).comp
            (algebraMap Γ(X, ⊤) (Localization.Away r))) := by
        rw [sourceAwayMap_comp_algebraMap]
    _ = ((Localization.awayLift
            (sourceBasicOpenTopRestriction Y (g.appTop.hom r))
            (g.appTop.hom r)
            (sourceBasicOpenTopRestriction_isUnit Y
              (g.appTop.hom r))).comp
          (sourceAwayMap g.appTop.hom r)).comp
            (algebraMap Γ(X, ⊤)
              (Localization.Away r)) := by
        rw [RingHom.comp_assoc]

private lemma sourceAwayMap_comp
    (g : Y ⟶ X) (f : A →+* Γ(X, ⊤)) (t : A) :
    (sourceAwayMap g.appTop.hom (f t)).comp
        (sourceAwayMap f t) =
      sourceAwayMap (g.appTop.hom.comp f) t := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  calc
    ((sourceAwayMap g.appTop.hom (f t)).comp
        (sourceAwayMap f t)).comp
          (algebraMap A (Localization.Away t)) =
      (sourceAwayMap g.appTop.hom (f t)).comp
        ((sourceAwayMap f t).comp
          (algebraMap A (Localization.Away t))) := by
            rw [RingHom.comp_assoc]
    _ = (sourceAwayMap g.appTop.hom (f t)).comp
          ((algebraMap Γ(X, ⊤)
            (Localization.Away (f t))).comp f) := by
        rw [sourceAwayMap_comp_algebraMap]
    _ = ((sourceAwayMap g.appTop.hom (f t)).comp
          (algebraMap Γ(X, ⊤)
            (Localization.Away (f t)))).comp f := by
        rw [RingHom.comp_assoc]
    _ = ((algebraMap Γ(Y, ⊤)
          (Localization.Away (g.appTop.hom (f t)))).comp
            g.appTop.hom).comp f := by
        rw [sourceAwayMap_comp_algebraMap]
    _ = (algebraMap Γ(Y, ⊤)
          (Localization.Away (g.appTop.hom (f t)))).comp
            (g.appTop.hom.comp f) := by
        rw [RingHom.comp_assoc]
    _ = (sourceAwayMap (g.appTop.hom.comp f) t).comp
          (algebraMap A (Localization.Away t)) := by
        rw [sourceAwayMap_comp_algebraMap]
        rfl

private lemma toBasicOpenOfGlobalSections_comp_source
    (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    g.resLE (X.basicOpen (f t))
          (Y.basicOpen (g.appTop.hom (f t)))
          (Scheme.preimage_basicOpen_top g (f t)).ge ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      toBasicOpenOfGlobalSections 𝒜
        (g.appTop.hom.comp f) rfl h0d hd := by
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t hd h0d).hom]
  simp only [Category.assoc]
  rw [toBasicOpenOfGlobalSections_chart,
    toBasicOpenOfGlobalSections_chart]
  let gD := g.resLE (X.basicOpen (f t))
    (Y.basicOpen (g.appTop.hom (f t)))
    (Scheme.preimage_basicOpen_top g (f t)).ge
  let ψX := Localization.awayLift
    (sourceBasicOpenTopRestriction X (f t)) (f t)
    (sourceBasicOpenTopRestriction_isUnit X (f t))
  let ψY := Localization.awayLift
    (sourceBasicOpenTopRestriction Y (g.appTop.hom (f t)))
    (g.appTop.hom (f t))
    (sourceBasicOpenTopRestriction_isUnit Y (g.appTop.hom (f t)))
  let μX := sourceAwayMap f t
  let μY := sourceAwayMap (g.appTop.hom.comp f) t
  let ν := sourceAwayMap g.appTop.hom (f t)
  let α := algebraMap (Away 𝒜 t) (Localization.Away t)
  have hψ : gD.appTop.hom.comp ψX = ψY.comp ν := by
    simpa only [gD, ψX, ψY, ν] using
      awayLift_naturality g (f t)
  have hμ : ν.comp μX = μY := by
    simpa only [ν, μX, μY] using
      sourceAwayMap_comp g f t
  have hθ :
      gD.appTop.hom.comp (ψX.comp (μX.comp α)) =
        ψY.comp (μY.comp α) := by
    calc
      gD.appTop.hom.comp (ψX.comp (μX.comp α)) =
          (gD.appTop.hom.comp ψX).comp
            (μX.comp α) := by
              rw [RingHom.comp_assoc]
      _ = (ψY.comp ν).comp (μX.comp α) := by
        rw [hψ]
      _ = ψY.comp ((ν.comp μX).comp α) := by
        rw [RingHom.comp_assoc, RingHom.comp_assoc]
      _ = ψY.comp (μY.comp α) := by
        rw [hμ]
  have hspec :
      Spec.map gD.appTop ≫
          Spec.map (CommRingCat.ofHom
            (ψX.comp (μX.comp α))) =
        Spec.map (CommRingCat.ofHom
          (ψY.comp (μY.comp α))) := by
    have hcat :
        CommRingCat.ofHom (ψX.comp (μX.comp α)) ≫
            gD.appTop =
          CommRingCat.ofHom (ψY.comp (μY.comp α)) := by
      apply CommRingCat.hom_ext
      exact hθ
    calc
      Spec.map gD.appTop ≫
          Spec.map (CommRingCat.ofHom
            (ψX.comp (μX.comp α))) =
        Spec.map
          (CommRingCat.ofHom (ψX.comp (μX.comp α)) ≫
            gD.appTop) := by
              rw [Spec.map_comp]
              rfl
      _ = Spec.map (CommRingCat.ofHom
          (ψY.comp (μY.comp α))) :=
        congrArg Spec.map hcat
  rw [show g.resLE (X.basicOpen (f t))
      (Y.basicOpen (g.appTop.hom (f t)))
      (Scheme.preimage_basicOpen_top g (f t)).ge = gD by rfl]
  rw [reassoc_of% Scheme.toSpecΓ_naturality gD]
  exact congrArg
    ((Y.basicOpen (g.appTop.hom (f t))).toScheme.toSpecΓ ≫ ·)
      hspec

/-- `Proj.fromOfGlobalSections` is natural under precomposition by an
arbitrary source morphism. -/
theorem fromOfGlobalSections_comp
    (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
      (g.appTop.hom.comp f) = ⊤) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜
    (g.appTop.hom.comp f) hf').hom_ext _ _ fun s ↦ ?_
  obtain ⟨i, r, hi, hr⟩ := s
  let DX := X.basicOpen (f r)
  let DY := Y.basicOpen ((g.appTop.hom.comp f) r)
  let gD := g.resLE DX DY
    (Scheme.preimage_basicOpen_top g (f r)).ge
  have hfactor : DY.ι ≫ g = gD ≫ DX.ι := by
    exact (Scheme.Hom.resLE_comp_ι g
      (Scheme.preimage_basicOpen_top g (f r)).ge).symm
  have hX :
      DX.ι ≫ fromOfGlobalSections 𝒜 f hf =
        toBasicOpenOfGlobalSections 𝒜 f rfl hi hr ≫
          (basicOpen 𝒜 r).ι := by
    rw [← fromOfGlobalSections_resLE 𝒜 f hf hi hr,
      Scheme.Hom.resLE_comp_ι]
  have hY :
      DY.ι ≫ fromOfGlobalSections 𝒜
          (g.appTop.hom.comp f) hf' =
        toBasicOpenOfGlobalSections 𝒜
            (g.appTop.hom.comp f) rfl hi hr ≫
          (basicOpen 𝒜 r).ι := by
    rw [← fromOfGlobalSections_resLE 𝒜
      (g.appTop.hom.comp f) hf' hi hr,
      Scheme.Hom.resLE_comp_ι]
  have hchart :
      gD ≫ toBasicOpenOfGlobalSections 𝒜 f rfl hi hr =
        toBasicOpenOfGlobalSections 𝒜
          (g.appTop.hom.comp f) rfl hi hr := by
    simpa only [DX, DY, gD, RingHom.comp_apply] using
      toBasicOpenOfGlobalSections_comp_source
        (𝒜 := 𝒜) g f hi hr
  simp only [openCoverOfMapIrrelevantEqTop,
    Scheme.openCoverOfIsOpenCover_f]
  show DY.ι ≫ g ≫ fromOfGlobalSections 𝒜 f hf =
    DY.ι ≫ fromOfGlobalSections 𝒜
      (g.appTop.hom.comp f) hf'
  calc
    DY.ι ≫ g ≫ fromOfGlobalSections 𝒜 f hf =
        gD ≫ DX.ι ≫ fromOfGlobalSections 𝒜 f hf := by
      simpa only [Category.assoc] using
        congrArg (· ≫ fromOfGlobalSections 𝒜 f hf) hfactor
    _ = gD ≫
        (toBasicOpenOfGlobalSections 𝒜 f rfl hi hr ≫
          (basicOpen 𝒜 r).ι) := by
      rw [hX]
    _ = (gD ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hi hr) ≫
          (basicOpen 𝒜 r).ι := by
      rw [Category.assoc]
    _ = toBasicOpenOfGlobalSections 𝒜
          (g.appTop.hom.comp f) rfl hi hr ≫
        (basicOpen 𝒜 r).ι := by
      rw [hchart]
    _ = DY.ι ≫ fromOfGlobalSections 𝒜
          (g.appTop.hom.comp f) hf' :=
      hY.symm

end SourceNaturality

end AlgebraicGeometry.Proj
