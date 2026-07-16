/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The fibre rank of a fibre product of finite flat morphisms

**[KM-W0 / F3-prodrank] ForMathlib brick (mathlib-PR shape — belongs next to
`Scheme.Hom.finrank_pullback_snd`).** For finite flat `f : X ⟶ S`, `g : Y ⟶ S`:

`(pullback.fst f g ≫ f).finrank s = f.finrank s * g.finrank s`.

mathlib's `finrank` API keeps its affine auxiliary (`IsAffine.finrank`) and the
chart-reduction lemmas PRIVATE, so we rebuild the short private layer here verbatim
(FlatRank.lean:56–115) and then prove the product formula in the same style: reduce to
the affine auxiliary over a chart, identify the product's global sections with the
tensor product through the pushout square of the pullback, and finish with
`Module.rankAtStalk_tensorProduct`.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

universe u

noncomputable section

namespace ModularCurves

variable {X Y S T : Scheme.{u}}

/-- Rebuild of mathlib's private `IsAffine.finrank`: the rank of `f : X ⟶ S` at `s`,
`S` affine, through the global-sections ring map. -/
def affineFinrank [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  f.appTop.hom.finrank (S.isoSpec.hom s)

/-- Rebuild of mathlib's private `IsAffine.finrank_of_isPullback`. -/
lemma affineFinrank_of_isPullback [IsAffine S] [IsAffine T] (f : X ⟶ S)
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g t = s) :
    affineFinrank f' t = affineFinrank f s := by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [affineFinrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t),
    ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality]
  rfl

/-- Rebuild of mathlib's private `IsAffine.finrank_snd`. -/
lemma affineFinrank_snd [IsAffine S] [IsAffine T] (f : X ⟶ S)
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    affineFinrank (pullback.snd f g) x = affineFinrank f (g x) :=
  affineFinrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl

/-- Rebuild of mathlib's private `Scheme.Hom.finrank_eq_finrank_snd_of_isAffine`. -/
lemma finrank_eq_affineFinrank_snd (f : X ⟶ S) (g : T ⟶ S) [IsAffine T] (t : T)
    [Flat f] [IsFinite f] :
    f.finrank (g t) = affineFinrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  trans affineFinrank (pullback.snd (pullback.snd f g) (u ≫ pullback.snd _ _)) z
  · refine (affineFinrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_).symm
    · exact pullback.map _ _ _ _ (pullback.fst f g) (u ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact u ≫ pullback.fst _ _
    · apply IsPullback.map_fst_comp_fst_snd_comp_fst
    · exact hyl
  · simp_rw [← hyr]
    exact affineFinrank_snd (pullback.snd f g) (u ≫ pullback.snd _ _) z

/-- **[F3-prodrank-spec] (affine case)** Over `Spec R`, the rank of the fibre product of
two finite flat Specs is the product of the ranks — `pullbackSpecIso` + tensor rank. -/
theorem finrank_pullback_comp_fst_spec (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Flat R A]
    [Module.Finite R B] [Module.Flat R B] (p : PrimeSpectrum R) :
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))).finrank p
    = Module.rankAtStalk A p * Module.rankAtStalk B p := by
  have hcomp : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      = (pullbackSpecIso R A B).hom
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TensorProduct R A B))) := by
    rw [← pullbackSpecIso_hom_fst']
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hcomp]
  haveI hTfin : Module.Finite R (TensorProduct R A B) := inferInstance
  haveI hTflat : Module.Flat R (TensorProduct R A B) := inferInstance
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (TensorProduct R A B)))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr hTflat
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (TensorProduct R A B)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hTfin
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank
    (RingHom.finite_algebraMap.mpr hTfin) (RingHom.flat_algebraMap_iff.mpr hTflat)]
  have hfin := congrFun (RingHom.finrank_algebraMap (R := R) (S := TensorProduct R A B)) p
  rw [show (CommRingCat.ofHom (algebraMap R (TensorProduct R A B))).hom
      = algebraMap R (TensorProduct R A B) from rfl, hfin]
  have := congrFun (Module.rankAtStalk_tensorProduct (R := R) (M := A) B) p
  rw [this, Pi.mul_apply]

/-- The Spec-level product formula, transported from the algebraMap form: for
`φ : R ⟶ A`, `ψ : R ⟶ B` finite flat, the rank of `Spec A ×_Spec R Spec B` over
`Spec R` multiplies. -/
lemma finrank_pullback_comp_fst_specMap {R A B : CommRingCat.{u}} (φ : R ⟶ A) (ψ : R ⟶ B)
    (hφ₁ : φ.hom.Finite) (hφ₂ : φ.hom.Flat) (hψ₁ : ψ.hom.Finite) (hψ₂ : ψ.hom.Flat)
    (p : Spec R) :
    (pullback.fst (Spec.map φ) (Spec.map ψ) ≫ Spec.map φ).finrank p
      = (Spec.map φ).finrank p * (Spec.map ψ).finrank p := by
  algebraize [φ.hom, ψ.hom]
  haveI hMA : Module.Finite ↑R ↑A := hφ₁
  haveI hFA : Module.Flat ↑R ↑A := hφ₂
  haveI hMB : Module.Finite ↑R ↑B := hψ₁
  haveI hFB : Module.Flat ↑R ↑B := hψ₂
  have hφ : φ = CommRingCat.ofHom (algebraMap R A) := rfl
  have hψ : ψ = CommRingCat.ofHom (algebraMap R B) := rfl
  rw [hφ, hψ]
  rw [ModularCurves.finrank_pullback_comp_fst_spec R A B p]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank
      (by rw [← hφ]; exact hφ₁) (by rw [← hφ]; exact hφ₂),
    Scheme.Hom.finrank_SpecMap_eq_finrank
      (by rw [← hψ]; exact hψ₁) (by rw [← hψ]; exact hψ₂)]
  rw [show (CommRingCat.ofHom (algebraMap ↑R ↑A)).hom = algebraMap ↑R ↑A from rfl,
    show (CommRingCat.ofHom (algebraMap ↑R ↑B)).hom = algebraMap ↑R ↑B from rfl,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]

/-- The product formula over an affine base, general affine sources: conjugate both
legs to literal Spec morphisms through `isoSpec` and apply the Spec-level formula. -/
lemma finrank_pullback_comp_fst_of_spec {R : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [Flat f] [IsFinite f] [Flat g] [IsFinite g]
    (p : Spec R) :
    (pullback.fst f g ≫ f).finrank p = f.finrank p * g.finrank p := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  haveI hφf : Flat (Spec.map φ) := by
    rw [hφ, MorphismProperty.cancel_left_of_respectsIso @Flat]; infer_instance
  haveI hφi : IsFinite (Spec.map φ) := by
    rw [hφ, MorphismProperty.cancel_left_of_respectsIso @IsFinite]; infer_instance
  haveI hψf : Flat (Spec.map ψ) := by
    rw [hψ, MorphismProperty.cancel_left_of_respectsIso @Flat]; infer_instance
  haveI hψi : IsFinite (Spec.map ψ) := by
    rw [hψ, MorphismProperty.cancel_left_of_respectsIso @IsFinite]; infer_instance
  -- the finrank transports of the legs
  have h1 : f.finrank p = (Spec.map φ).finrank p := by
    rw [hφ]
    exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.inv f) p).symm
  have h2 : g.finrank p = (Spec.map ψ).finrank p := by
    rw [hψ]
    exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.inv g) p).symm
  -- the comparison map between the pullbacks
  have hsq1 : Spec.map φ ≫ 𝟙 (Spec R) = X.isoSpec.inv ≫ f := by
    rw [Category.comp_id, hφ]
  have hsq2 : Spec.map ψ ≫ 𝟙 (Spec R) = Y.isoSpec.inv ≫ g := by
    rw [Category.comp_id, hψ]
  haveI : IsIso (pullback.map (Spec.map φ) (Spec.map ψ) f g X.isoSpec.inv Y.isoSpec.inv
      (𝟙 (Spec R)) hsq1 hsq2) := by infer_instance
  have hcomp : pullback.map (Spec.map φ) (Spec.map ψ) f g X.isoSpec.inv Y.isoSpec.inv
        (𝟙 (Spec R)) hsq1 hsq2 ≫ (pullback.fst f g ≫ f)
      = pullback.fst (Spec.map φ) (Spec.map ψ) ≫ Spec.map φ := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, ← hφ]
  have h3 : (pullback.fst f g ≫ f).finrank p
      = (pullback.fst (Spec.map φ) (Spec.map ψ) ≫ Spec.map φ).finrank p := by
    haveI : Flat (pullback.fst f g ≫ f) :=
      MorphismProperty.comp_mem _ _ _
        (MorphismProperty.pullback_fst (P := @Flat) _ _ ‹_›) ‹_›
    haveI : IsFinite (pullback.fst f g ≫ f) :=
      MorphismProperty.comp_mem _ _ _
        (MorphismProperty.pullback_fst (P := @IsFinite) _ _ ‹_›) ‹_›
    rw [← hcomp]
    exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso _ _) p).symm
  rw [h1, h2, h3]
  exact finrank_pullback_comp_fst_specMap φ ψ
    (IsFinite.SpecMap_iff φ |>.mp hφi) (Flat.SpecMap_iff.mp hφf)
    (IsFinite.SpecMap_iff ψ |>.mp hψi) (Flat.SpecMap_iff.mp hψf) p

/-- **The fibre-product rank formula** (mathlib-PR shape — belongs next to
`Scheme.Hom.finrank_pullback_snd`): for finite flat `f g` over any base,
`deg (X ×_S Y → S) = deg X · deg Y` pointwise. -/
theorem finrank_pullback_comp_fst {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [IsFinite f] [Flat g] [IsFinite g] (s : S) :
    (pullback.fst f g ≫ f).finrank s = f.finrank s * g.finrank s := by
  haveI : Flat (pullback.fst f g ≫ f) :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.pullback_fst (P := @Flat) _ _ ‹_›) ‹_›
  haveI : IsFinite (pullback.fst f g ≫ f) :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.pullback_fst (P := @IsFinite) _ _ ‹_›) ‹_›
  obtain ⟨R, i, hi, s', rfl⟩ := S.exists_Spec_apply_eq s
  haveI hfRf : Flat (pullback.snd f i) :=
    MorphismProperty.pullback_snd (P := @Flat) _ _ ‹_›
  haveI hfRi : IsFinite (pullback.snd f i) :=
    MorphismProperty.pullback_snd (P := @IsFinite) _ _ ‹_›
  haveI hgRf : Flat (pullback.snd g i) :=
    MorphismProperty.pullback_snd (P := @Flat) _ _ ‹_›
  haveI hgRi : IsFinite (pullback.snd g i) :=
    MorphismProperty.pullback_snd (P := @IsFinite) _ _ ‹_›
  -- the comparison square: the product of restrictions is the restriction of the product
  have hpb : IsPullback
      (pullback.map (pullback.snd f i) (pullback.snd g i) f g
        (pullback.fst f i) (pullback.fst g i) i
        pullback.condition.symm pullback.condition.symm)
      (pullback.fst (pullback.snd f i) (pullback.snd g i) ≫ pullback.snd f i)
      (pullback.fst f g ≫ f) i := by
    have weq : pullback.map (pullback.snd f i) (pullback.snd g i) f g
          (pullback.fst f i) (pullback.fst g i) i
          pullback.condition.symm pullback.condition.symm ≫ (pullback.fst f g ≫ f)
        = (pullback.fst (pullback.snd f i) (pullback.snd g i) ≫ pullback.snd f i) ≫ i := by
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc,
        pullback.condition (f := f) (g := i)]
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk weq
      (fun s => pullback.lift
        (pullback.lift (s.fst ≫ pullback.fst f g) s.snd
          (by rw [Category.assoc]; exact s.condition))
        (pullback.lift (s.fst ≫ pullback.snd f g) s.snd
          (by rw [Category.assoc, ← pullback.condition (f := f) (g := g)]
              exact s.condition))
        (by rw [pullback.lift_snd, pullback.lift_snd]))
      (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
    · -- fac_left : lift ≫ map = s.fst
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · -- fac_right : lift ≫ (fstQ ≫ fR) = s.snd
      rw [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · -- uniqueness
      apply pullback.hom_ext <;> [apply pullback.hom_ext; apply pullback.hom_ext] <;>
        simp only [← hm₁, ← hm₂, Category.assoc, pullback.lift_fst, pullback.lift_snd]
      exact congrArg (m ≫ ·)
        (pullback.condition (f := pullback.snd f i) (g := pullback.snd g i)).symm

  rw [← Scheme.Hom.finrank_pullback_snd f i s', ← Scheme.Hom.finrank_pullback_snd g i s',
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb s']
  exact finrank_pullback_comp_fst_of_spec (pullback.snd f i) (pullback.snd g i) s'

end ModularCurves
