/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `Spec` of an away-localization is the basic open (ForMathlib, c4.2a)

`specBasicOpenIsoAway` : `Spec (Localization.Away f) ≅ (Spec A).basicOpen f` as schemes.

Mathlib knows both halves — `Spec.map (algebraMap A (Localization.Away f))` is an open immersion,
and `PrimeSpectrum.localization_away_comap_range` computes its range as the basic open — but does
not package the resulting isomorphism. This is the adapter that turns a morphism defined on
`Spec (Localization.Away f)` into one defined on the open subscheme `D(f)`, which is what gluing
along a basic-open cover needs.

Upstream candidate.
-/

open AlgebraicGeometry CategoryTheory

/-- A basic open of `Spec A`, *as a `Scheme.Opens`*.

The type ascription `(PrimeSpectrum.basicOpen f : (Spec A).Opens)` does not elaborate — the
projection `.ι` is attempted at the pre-coercion type `TopologicalSpace.Opens (PrimeSpectrum A)`.
Naming the open once, with its `Scheme.Opens` type declared, is the fix. -/
abbrev specBasicOpen (A : CommRingCat) (f : A) : (Spec A).Opens := PrimeSpectrum.basicOpen f

/-- `D(f · g) = D(f) ⊓ D(g)`, at `Scheme.Opens` type. -/
lemma specBasicOpen_mul (A : CommRingCat) (f g : A) :
    specBasicOpen A (f * g) = specBasicOpen A f ⊓ specBasicOpen A g :=
  PrimeSpectrum.basicOpen_mul f g

/-- `D(f · g) ≤ D(f)`, at `Scheme.Opens` type. Stated once, with `A` a *variable*: applying
`PrimeSpectrum.basicOpen_mul_le_left` directly at a concrete `A` forces the defeq
`(Spec A).Opens ≡ Opens (PrimeSpectrum A)`, which unfolds `A` and can blow up `whnf`. -/
lemma specBasicOpen_mul_le_left (A : CommRingCat) (f g : A) :
    specBasicOpen A (f * g) ≤ specBasicOpen A f :=
  PrimeSpectrum.basicOpen_mul_le_left f g

/-- `D(f · g) ≤ D(g)`, at `Scheme.Opens` type. -/
lemma specBasicOpen_mul_le_right (A : CommRingCat) (f g : A) :
    specBasicOpen A (f * g) ≤ specBasicOpen A g :=
  PrimeSpectrum.basicOpen_mul_le_right f g

/-- `Spec` of an away-localization is (isomorphic to) the corresponding basic open. -/
noncomputable def specBasicOpenIsoAway (A : CommRingCat) (f : A) :
    Spec (CommRingCat.of (Localization.Away f)) ≅ (specBasicOpen A f).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
    (specBasicOpen A f).ι <| by
      rw [Scheme.Opens.range_ι]
      exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f

/-- `specBasicOpenIsoAway` is the isomorphism factoring the localization map through `D(f)`. -/
@[reassoc (attr := simp)]
lemma specBasicOpenIsoAway_hom_ι (A : CommRingCat) (f : A) :
    (specBasicOpenIsoAway A f).hom ≫ (specBasicOpen A f).ι =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Under `specBasicOpenIsoAway`, the inclusion `D(f * g) ⊆ D(f)` of basic opens is `Spec` of the
localization map `Localization.Away f → Localization.Away (f * g)`.

Proved by cancelling the monomorphism `D(f).ι`: both sides then compute the structure map of
`Localization.Away (f * g)` over `A`, one by `specBasicOpenIsoAway_hom_ι`, the other by
`IsLocalization.Away.awayToAwayRight_eq`. -/
lemma specBasicOpenIsoAway_hom_homOfLE (A : CommRingCat) (f g : A) :
    (specBasicOpenIsoAway A (f * g)).hom ≫
        (Spec A).homOfLE (specBasicOpen_mul_le_left A f g) =
      Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.awayToAwayRight (S := Localization.Away f) f g)) ≫
        (specBasicOpenIsoAway A f).hom := by
  rw [← cancel_mono (specBasicOpen A f).ι, Category.assoc,
    Scheme.homOfLE_ι, specBasicOpenIsoAway_hom_ι, Category.assoc, specBasicOpenIsoAway_hom_ι,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (RingHom.ext fun a =>
    (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away f) f g a)).symm

/-- The mirror of `specBasicOpenIsoAway_hom_homOfLE` for the inclusion `D(f * g) ⊆ D(g)`. -/
lemma specBasicOpenIsoAway_hom_homOfLE' (A : CommRingCat) (f g : A) :
    (specBasicOpenIsoAway A (f * g)).hom ≫
        (Spec A).homOfLE (specBasicOpen_mul_le_right A f g) =
      Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.awayToAwayLeft (S := Localization.Away g) g f)) ≫
        (specBasicOpenIsoAway A g).hom := by
  rw [← cancel_mono (specBasicOpen A g).ι, Category.assoc,
    Scheme.homOfLE_ι, specBasicOpenIsoAway_hom_ι, Category.assoc, specBasicOpenIsoAway_hom_ι,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (RingHom.ext fun a =>
    (IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away g) g f a)).symm

/-- The `inv`-side form of `specBasicOpenIsoAway_hom_homOfLE`: restricting a morphism defined on
`D(f)` along `D(f · g) ⊆ D(f)` corresponds to base-changing it along `Away f → Away (f · g)`. -/
@[reassoc]
lemma homOfLE_specBasicOpenIsoAway_inv (A : CommRingCat) (f g : A) :
    (Spec A).homOfLE (specBasicOpen_mul_le_left A f g) ≫ (specBasicOpenIsoAway A f).inv =
      (specBasicOpenIsoAway A (f * g)).inv ≫ Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.awayToAwayRight (S := Localization.Away f) f g)) := by
  rw [← cancel_epi (specBasicOpenIsoAway A (f * g)).hom, ← Category.assoc,
    specBasicOpenIsoAway_hom_homOfLE, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- The `D(f · g) ⊆ D(g)` mirror of `homOfLE_specBasicOpenIsoAway_inv`. -/
@[reassoc]
lemma homOfLE_specBasicOpenIsoAway_inv' (A : CommRingCat) (f g : A) :
    (Spec A).homOfLE (specBasicOpen_mul_le_right A f g) ≫ (specBasicOpenIsoAway A g).inv =
      (specBasicOpenIsoAway A (f * g)).inv ≫ Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.awayToAwayLeft (S := Localization.Away g) g f)) := by
  rw [← cancel_epi (specBasicOpenIsoAway A (f * g)).hom, ← Category.assoc,
    specBasicOpenIsoAway_hom_homOfLE', Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- **(the gluing transport)** Two morphisms defined on the basic opens `D(b)`, `D(c)` of `Spec A`,
pulled back along `f : X ⟶ Spec A`, agree on `f ⁻¹ᵁ D(b · c)` as soon as their base changes to
`Localization.Away (b · c)` agree.

Everything here is stated for *variable* `X`, `Y`, `A`. That is deliberate: instantiated at a
concrete scheme (a pullback of `Proj` charts, say) the `rw`s below would force `whnf` to unfold
`Limits.pullback`, `MvPolynomial` and quotient carriers, and blow the heartbeat budget. As a
general lemma it is instantiated by application, and no unfolding ever happens. -/
lemma homOfLE_morphismRestrict_agree {X Y : Scheme} (A : CommRingCat) (f : X ⟶ Spec A) (b c : A)
    (Fb : Spec (CommRingCat.of (Localization.Away b)) ⟶ Y)
    (Fc : Spec (CommRingCat.of (Localization.Away c)) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
          (S := Localization.Away b) (P := Localization.Away (b * c)) b c)) ≫ Fb =
        Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft
          (S := Localization.Away c) (P := Localization.Away (b * c)) c b)) ≫ Fc) :
    X.homOfLE (f.preimage_mono (specBasicOpen_mul_le_left A b c)) ≫
        ((f ∣_ specBasicOpen A b) ≫ (specBasicOpenIsoAway A b).inv ≫ Fb) =
      X.homOfLE (f.preimage_mono (specBasicOpen_mul_le_right A b c)) ≫
        ((f ∣_ specBasicOpen A c) ≫ (specBasicOpenIsoAway A c).inv ≫ Fc) := by
  have hb := (morphismRestrict_homOfLE f (specBasicOpen A (b * c)) (specBasicOpen A b)
    (specBasicOpen_mul_le_left A b c)).symm
  have hc := (morphismRestrict_homOfLE f (specBasicOpen A (b * c)) (specBasicOpen A c)
    (specBasicOpen_mul_le_right A b c)).symm
  conv_lhs => rw [← Category.assoc, hb]
  conv_rhs => rw [← Category.assoc, hc]
  simp only [Category.assoc]
  rw [homOfLE_specBasicOpenIsoAway_inv_assoc, homOfLE_specBasicOpenIsoAway_inv'_assoc, h]

set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
/-- **(gluing along an `iSup` cover)** The `hf` obligation of `Scheme.OpenCover.glueMorphisms` for
the cover `Scheme.Opens.iSupOpenCover U` is exactly pairwise agreement on the intersections
`U k ⊓ U l`: the pullback of two `homOfLE`s IS the intersection (`isPullback_opens_inf_le`).

As with `homOfLE_morphismRestrict_agree`, this is stated over variable `X`, `Y`, so that no
concrete scheme is ever unfolded. -/
lemma glueMorphisms_hf_of_agree {X : Scheme} {J : Type*} (U : J → X.Opens) {Y : Scheme}
    (F : ∀ k, (U k).toScheme ⟶ Y)
    (h : ∀ k l, X.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ F k =
      X.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ F l) (x y : J) :
    pullback.fst ((Scheme.Opens.iSupOpenCover U).f x) ((Scheme.Opens.iSupOpenCover U).f y) ≫ F x =
      pullback.snd _ _ ≫ F y := by
  have hP := isPullback_opens_inf_le (le_iSup U x) (le_iSup U y)
  show pullback.fst (X.homOfLE (le_iSup U x)) (X.homOfLE (le_iSup U y)) ≫ F x =
    pullback.snd _ _ ≫ F y
  rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  exact h x y

/-- **(variable-scheme bridge)** For an open immersion `f`, restricting `(f.isoImage (⨆ U)).inv ≫ g`
to the `k`-th image piece gives `(f.isoImage (U k)).inv` composed with the `k`-th cover inclusion.

Stated over variable schemes on purpose: instantiated at a concrete `Proj` chart-product, the
`isoImage` naturality rewrites (`isoImage_hom_homOfLE`) drive `whnf` into the pullback carrier and
blow the heartbeat budget. As a general lemma it is applied, never unfolded. -/
lemma homOfLE_isoImage_inv_iSup {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] {J : Type*}
    (U : J → X.Opens) (k : J) {Z : Scheme} (g : (⨆ i, U i).toScheme ⟶ Z) :
    Y.homOfLE (f.image_mono (le_iSup U k)) ≫ (f.isoImage (⨆ i, U i)).inv ≫ g =
      (f.isoImage (U k)).inv ≫ (Scheme.Opens.iSupOpenCover U).f k ≫ g := by
  rw [← cancel_epi (f.isoImage (U k)).hom, Iso.hom_inv_id_assoc, ← Category.assoc,
    Scheme.Hom.isoImage_hom_homOfLE f (U k) (⨆ i, U i) (le_iSup U k), Category.assoc,
    Iso.hom_inv_id_assoc]
  rfl

/-- **(variable-scheme σ-immersion identity)** For an open immersion `p : X ⟶ Z`, an iso `e : X ≅ Y`
and an open `U : Y.Opens`, the chain `isoImage.inv ≫ (e.hom ∣_ U) ≫ U.ι ≫ e.inv ≫ p` collapses to
the image inclusion `(p ''ᵁ (e.hom ⁻¹ᵁ U)).ι`. Stated over variable schemes so instantiation at a
concrete `Proj` chart-product never drives `whnf` into the pullback carrier. -/
lemma isoImage_inv_morphismRestrict_ι {X Y Z : Scheme} (p : X ⟶ Z) [IsOpenImmersion p]
    (e : X ≅ Y) (U : Y.Opens) :
    (p.isoImage (e.hom ⁻¹ᵁ U)).inv ≫ (e.hom ∣_ U) ≫ U.ι ≫ e.inv ≫ p =
      (p ''ᵁ (e.hom ⁻¹ᵁ U)).ι := by
  rw [morphismRestrict_ι_assoc, ← Category.assoc _ e.inv, Iso.hom_inv_id, Category.id_comp,
    Scheme.Hom.isoImage_inv_ι]

/-- Two `Spec.map`-factorizations that agree on the composite base map agree as morphisms.

The barrier around the composite: stated over **variable** rings `A B D E`, the only unfold
the elaborator sees is the trivial `Spec.map (a ≫ b) = Spec.map b ≫ Spec.map a`. Instantiated at a
concrete localization tower (`E` a triple `Localization.Away`), the conclusion still matches by
structure — `Spec.map ?b ≫ Spec.map ?a ≫ ?rest` — so `isDefEq` never unfolds `E`. Combining the two
`Spec.map`s *at the concrete tower* instead (`rw [← Spec.map_comp_assoc]` on the goal) forces a
defeq through `E` and blows the heartbeat budget; routing through this lemma keeps it under 5k. -/
lemma spec_map_comp_congr {A B D E : CommRingCat} {X : Scheme}
    (a : A ⟶ B) (b : B ⟶ E) (a' : A ⟶ D) (b' : D ⟶ E)
    (rest : Spec A ⟶ X) (h : a ≫ b = a' ≫ b') :
    Spec.map b ≫ Spec.map a ≫ rest = Spec.map b' ≫ Spec.map a' ≫ rest := by
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, h]

/-- An open immersion's image functor preserves binary intersections. (`f ''ᵁ` is injective with
`f ⁻¹ᵁ` as a partial inverse, so it respects `⊓`.) Upstream candidate. -/
lemma Scheme.Hom.image_inf {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (U V : X.Opens) :
    f ''ᵁ (U ⊓ V) = f ''ᵁ U ⊓ f ''ᵁ V := by
  calc f ''ᵁ (U ⊓ V)
      = f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ U) ⊓ f ⁻¹ᵁ (f ''ᵁ V)) := by
        rw [Scheme.Hom.preimage_image_eq, Scheme.Hom.preimage_image_eq]
    _ = f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ U ⊓ f ''ᵁ V)) := by rw [Scheme.Hom.preimage_inf]
    _ = f.opensRange ⊓ (f ''ᵁ U ⊓ f ''ᵁ V) := Scheme.Hom.image_preimage_eq_opensRange_inf _ _
    _ = f ''ᵁ U ⊓ f ''ᵁ V :=
        inf_eq_right.mpr (le_trans inf_le_left (Scheme.Hom.image_le_opensRange f U))
