/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.SpecQuotientIso
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# A closed immersion of finite locally free schemes of equal rank is an isomorphism (YFULL γ)

Over an **affine** base `S`, a closed immersion `j : X ⟶ Y` between schemes finite, flat,
and locally of finite presentation over `S` whose global-section `Γ(S)`-modules `Γ(Y)`,
`Γ(X)` have equal rank at every prime is an isomorphism. This is the scheme form of the
same-degree effective-Cartier-divisor equality (a subdivisor of equal degree is the whole
divisor).

Over an affine base both `X` and `Y` are affine (finite over affine), so `j` transports to
`Spec` of its (surjective) global-sections comorphism, and
`isIso_SpecMap_of_surjective_of_flat_rankAtStalk_eq` applies.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- `finrank` is compatible with restriction to an open of the target (`morphismRestrict` is
a base change along the open immersion). -/
-- `private`: `ForMathlib/FinrankComp.lean` carries a copy of this under the same name,
-- and both modules are imported together. Only this file uses this copy.
private lemma Scheme.Hom.finrank_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [Flat f] [IsFinite f] (u : ↥U) :
    (f ∣_ U).finrank u = f.finrank (U.ι.base u) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict f U).flip u

/-- `finrank` is transported by post-composition with an isomorphism of the target. -/
-- `private`: `ForMathlib/FinrankComp.lean` carries a copy of this under the same name,
-- and both modules are imported together. Only this file uses this copy.
private lemma Scheme.Hom.finrank_comp_right_of_isIso {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (e : Y ⟶ Z)
    [IsIso e] [Flat φ] [IsFinite φ] (y : Y) :
    φ.finrank y = (φ ≫ e).finrank (e.base y) := by
  haveI : Flat (φ ≫ e) := MorphismProperty.comp_mem _ _ _ ‹Flat φ› inferInstance
  haveI : IsFinite (φ ≫ e) := MorphismProperty.comp_mem _ _ _ ‹IsFinite φ› inferInstance
  have h : IsPullback (𝟙 X) φ (φ ≫ e) e :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Scheme.Hom.finrank_of_isPullback (𝟙 X) φ (φ ≫ e) e h y

set_option backward.isDefEq.respectTransparency.types false in
/-- Over an affine base, the scheme-`finrank` of a finite flat morphism equals the stalkwise
rank of its global sections as an algebra over the base. -/
lemma Scheme.Hom.finrank_eq_rankAtStalk_isAffineBase {Y S : Scheme.{u}} [IsAffine S]
    [IsAffine Y] (g : Y ⟶ S) [Flat g] [IsFinite g] (p : PrimeSpectrum ↑Γ(S, ⊤)) :
    letI : Algebra ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := (g.appTop).hom.toAlgebra
    g.finrank (S.isoSpec.inv.base p) = Module.rankAtStalk (R := ↑Γ(S, ⊤)) ↑Γ(Y, ⊤) p := by
  letI : Algebra ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := (g.appTop).hom.toAlgebra
  haveI : Module.Finite ↑Γ(S, ⊤) ↑Γ(Y, ⊤) :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite g)).2
  haveI : Module.Flat ↑Γ(S, ⊤) ↑Γ(Y, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) g inferInstance
  haveI hfin : (g.appTop).hom.Finite := (inferInstance : Module.Finite ↑Γ(S, ⊤) ↑Γ(Y, ⊤))
  haveI hflt : (g.appTop).hom.Flat := (inferInstance : Module.Flat ↑Γ(S, ⊤) ↑Γ(Y, ⊤))
  haveI : Flat (Spec.map (g.appTop)) := by rw [Flat.SpecMap_iff]; exact hflt
  haveI : IsFinite (Spec.map (g.appTop)) := by rw [IsFinite.SpecMap_iff]; exact hfin
  haveI : Flat (Spec.map (g.appTop) ≫ S.isoSpec.inv) :=
    MorphismProperty.comp_mem _ _ _ ‹Flat (Spec.map (g.appTop))› inferInstance
  haveI : IsFinite (Spec.map (g.appTop) ≫ S.isoSpec.inv) :=
    MorphismProperty.comp_mem _ _ _ ‹IsFinite (Spec.map (g.appTop))› inferInstance
  -- `g` factors as `isoSpec.hom ≫ Spec.map g.appTop ≫ isoSpec.inv`
  have hg : g = Y.isoSpec.hom ≫ Spec.map (g.appTop) ≫ S.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  -- transport finrank across the two isos
  have e1 : g.finrank = (Spec.map (g.appTop) ≫ S.isoSpec.inv).finrank := by
    conv_lhs => rw [hg]
    exact Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.hom _
  have e2 := Scheme.Hom.finrank_comp_right_of_isIso (Spec.map (g.appTop)) S.isoSpec.inv p
  have e3 : (Spec.map (g.appTop)).finrank p =
      Module.rankAtStalk (R := ↑Γ(S, ⊤)) ↑Γ(Y, ⊤) p :=
    Scheme.Hom.finrank_SpecMap_algebraMap ↑Γ(S, ⊤) ↑Γ(Y, ⊤) p
  rw [e1, ← e2, e3]

end AlgebraicGeometry

namespace ModularCurves

set_option backward.isDefEq.respectTransparency.types false in
/-- A closed immersion `j : X ⟶ Y` of schemes finite flat locally-of-finite-presentation over
an **affine** base `S`, whose `Γ(S)`-modules `Γ(Y)` and `Γ(X)` have equal rank at every prime,
is an isomorphism. -/
theorem isIso_of_isClosedImmersion_of_rankAtStalk_eq_isAffineBase
    {X Y S : Scheme.{u}} [IsAffine S] (g : Y ⟶ S) (j : X ⟶ Y)
    [IsClosedImmersion j] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [IsFinite (j ≫ g)] [Flat (j ≫ g)] [LocallyOfFinitePresentation (j ≫ g)]
    (h : letI : Algebra ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := (g.appTop).hom.toAlgebra
         letI : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤) := (j ≫ g).appTop.hom.toAlgebra
         ∀ p : PrimeSpectrum ↑Γ(S, ⊤),
           Module.rankAtStalk (R := ↑Γ(S, ⊤)) ↑Γ(Y, ⊤) p =
             Module.rankAtStalk (R := ↑Γ(S, ⊤)) ↑Γ(X, ⊤) p) :
    IsIso j := by
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  haveI : IsAffine X := isAffine_of_isAffineHom (j ≫ g)
  letI : Algebra ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := (g.appTop).hom.toAlgebra
  letI : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤) := (j ≫ g).appTop.hom.toAlgebra
  haveI : Module.Finite ↑Γ(S, ⊤) ↑Γ(Y, ⊤) :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite g)).2
  haveI : Module.Flat ↑Γ(S, ⊤) ↑Γ(Y, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) g inferInstance
  haveI : Module.Finite ↑Γ(S, ⊤) ↑Γ(X, ⊤) :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite (j ≫ g))).2
  haveI : Module.Flat ↑Γ(S, ⊤) ↑Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) (j ≫ g) inferInstance
  have hsurj : Function.Surjective (j.appTop).hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (f := j)).2
  have hcompat : ∀ r : ↑Γ(S, ⊤),
      (j.appTop).hom (algebraMap ↑Γ(S, ⊤) ↑Γ(Y, ⊤) r) = algebraMap ↑Γ(S, ⊤) ↑Γ(X, ⊤) r :=
    fun r => rfl
  have hspec := isIso_SpecMap_of_surjective_of_flat_rankAtStalk_eq (R₀ := ↑Γ(S, ⊤))
    (R := ↑Γ(Y, ⊤)) (S := ↑Γ(X, ⊤)) h (j.appTop).hom hcompat hsurj
  refine (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms Scheme)
    (arrowIsoSpecΓOfIsAffine j)).mpr ?_
  exact hspec

/-- **Same-degree closed immersion is an isomorphism (affine base, `finrank` form).** A closed
immersion `j : X ⟶ Y` of finite flat lfp schemes over an affine base `S`, whose scheme-ranks
over `S` agree everywhere, is an isomorphism. -/
theorem isIso_of_isClosedImmersion_of_finrank_eq_isAffineBase
    {X Y S : Scheme.{u}} [IsAffine S] (g : Y ⟶ S) (j : X ⟶ Y)
    [IsClosedImmersion j] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [IsFinite (j ≫ g)] [Flat (j ≫ g)] [LocallyOfFinitePresentation (j ≫ g)]
    (h : ∀ s : S, (j ≫ g).finrank s = g.finrank s) : IsIso j := by
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  haveI : IsAffine X := isAffine_of_isAffineHom (j ≫ g)
  apply isIso_of_isClosedImmersion_of_rankAtStalk_eq_isAffineBase g j
  intro p
  rw [← Scheme.Hom.finrank_eq_rankAtStalk_isAffineBase g p,
    ← Scheme.Hom.finrank_eq_rankAtStalk_isAffineBase (j ≫ g) p]
  exact (h (S.isoSpec.inv.base p)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- **Same-degree closed immersion is an isomorphism (general base).** A closed immersion
`j : X ⟶ Y` between schemes finite, flat, and locally of finite presentation over `S`, whose
scheme-ranks over `S` agree everywhere, is an isomorphism. Reduces to the affine-base case on
the preimages of an affine cover of `S`. -/
theorem isIso_of_isClosedImmersion_of_finrank_eq
    {X Y S : Scheme.{u}} (g : Y ⟶ S) (j : X ⟶ Y)
    [IsClosedImmersion j] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [IsFinite (j ≫ g)] [Flat (j ≫ g)] [LocallyOfFinitePresentation (j ≫ g)]
    (h : ∀ s : S, (j ≫ g).finrank s = g.finrank s) : IsIso j := by
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun i => g ⁻¹ᵁ (S.affineCover.f i).opensRange) ?cover]
  case cover =>
    rw [← Scheme.Hom.preimage_iSup, Scheme.OpenCover.iSup_opensRange, Scheme.Hom.preimage_top]
  intro i
  rw [MorphismProperty.isomorphisms.iff]
  set W : S.Opens := (S.affineCover.f i).opensRange with hW
  haveI : IsAffine W := isAffineOpen_opensRange _
  haveI : IsClosedImmersion (j ∣_ (g ⁻¹ᵁ W)) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsClosedImmersion j) _
  haveI : IsFinite (g ∣_ W) := IsZariskiLocalAtTarget.restrict (inferInstance : IsFinite g) _
  haveI : Flat (g ∣_ W) := IsZariskiLocalAtTarget.restrict (inferInstance : Flat g) _
  haveI : LocallyOfFinitePresentation (g ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : LocallyOfFinitePresentation g) _
  have hcomp : (j ∣_ (g ⁻¹ᵁ W)) ≫ (g ∣_ W) = (j ≫ g) ∣_ W := (morphismRestrict_comp j g W).symm
  haveI : IsFinite ((j ∣_ (g ⁻¹ᵁ W)) ≫ (g ∣_ W)) := by
    rw [hcomp]; exact IsZariskiLocalAtTarget.restrict (inferInstance : IsFinite (j ≫ g)) _
  haveI : Flat ((j ∣_ (g ⁻¹ᵁ W)) ≫ (g ∣_ W)) := by
    rw [hcomp]; exact IsZariskiLocalAtTarget.restrict (inferInstance : Flat (j ≫ g)) _
  haveI : LocallyOfFinitePresentation ((j ∣_ (g ⁻¹ᵁ W)) ≫ (g ∣_ W)) := by
    rw [hcomp]; exact IsZariskiLocalAtTarget.restrict
      (inferInstance : LocallyOfFinitePresentation (j ≫ g)) _
  refine isIso_of_isClosedImmersion_of_finrank_eq_isAffineBase (g ∣_ W) (j ∣_ (g ⁻¹ᵁ W)) ?_
  intro s
  rw [hcomp, Scheme.Hom.finrank_morphismRestrict g W s]
  exact (Scheme.Hom.finrank_morphismRestrict (j ≫ g) W s).trans (h (W.ι.base s))

end ModularCurves
