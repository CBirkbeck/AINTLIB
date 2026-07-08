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
        (Spec A).homOfLE (PrimeSpectrum.basicOpen_mul_le_left f g) =
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
        (Spec A).homOfLE (PrimeSpectrum.basicOpen_mul_le_right f g) =
      Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.awayToAwayLeft (S := Localization.Away g) g f)) ≫
        (specBasicOpenIsoAway A g).hom := by
  rw [← cancel_mono (specBasicOpen A g).ι, Category.assoc,
    Scheme.homOfLE_ι, specBasicOpenIsoAway_hom_ι, Category.assoc, specBasicOpenIsoAway_hom_ι,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (RingHom.ext fun a =>
    (IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away g) g f a)).symm
