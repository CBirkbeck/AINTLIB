/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ProjectiveSpaceCoefficientBaseChange
import ModularCurves.ForMathlib.RelativeProjectiveAffineRestriction

/-!
# Relative projective space over an affine base

Relative projective space over an affine open is ordinary projective space over the ring of
sections of that open. The comparison commutes with both the structural projection and the map to
projective space over the original coefficient ring.
-/

open CategoryTheory Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- The coefficient map associated to an affine open of a scheme over an affine base. -/
def affineOpenCoefficientMap
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (U : S.Opens) (hU : IsAffineOpen U) :
    CommRingCat.of k ⟶ CommRingCat.of Γ(S, U) :=
  Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ s)

/-- Absolute projective space after coefficient extension is the corresponding relative
projective space. -/
def coefficientRelativeProjectiveIso
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (d : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R) ≅
      relativeProjectiveScheme
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) d :=
  (MvPolynomial.isPullback_coefficientMap k R d).isoPullback ≪≫
    pullbackSymmetry
      (MvPolynomial.homogeneousProjπ
        (R := k) (σ := Fin (d + 1)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- The coefficient-relative comparison commutes with projection to the extended base. -/
@[reassoc]
lemma coefficientRelativeProjectiveIso_hom_relativeProjectiveToBase
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (d : ℕ) :
    (coefficientRelativeProjectiveIso k R d).hom ≫
        relativeProjectiveToBase
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) d =
      MvPolynomial.homogeneousProjπ
        (R := R) (σ := Fin (d + 1)) := by
  simp [coefficientRelativeProjectiveIso]

/-- The coefficient-relative comparison commutes with projection to the original projective
space. -/
@[reassoc]
lemma coefficientRelativeProjectiveIso_hom_relativeProjectiveToProjective
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (d : ℕ) :
    (coefficientRelativeProjectiveIso k R d).hom ≫
        relativeProjectiveToProjective
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) d =
      MvPolynomial.coefficientMap (algebraMap k R) d := by
  simp [coefficientRelativeProjectiveIso]

/-- Replacing an affine base by its canonical spectrum presentation induces an isomorphism of
relative projective spaces. -/
def relativeProjectiveAffineBaseIso
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    relativeProjectiveScheme (U.ι ≫ s) d ≅
      relativeProjectiveScheme
        (Spec.map (affineOpenCoefficientMap s U hU)) d :=
  asIso
    (pullback.map
      (U.ι ≫ s)
      (MvPolynomial.homogeneousProjπ
        (R := k) (σ := Fin (d + 1)))
      (Spec.map (affineOpenCoefficientMap s U hU))
      (MvPolynomial.homogeneousProjπ
        (R := k) (σ := Fin (d + 1)))
      hU.isoSpec.hom
      (𝟙 _)
      (𝟙 _)
      (by
        simp only [Category.comp_id, affineOpenCoefficientMap,
          Spec.map_preimage, Iso.hom_inv_id_assoc])
      (by simp))

/-- The affine-base comparison commutes with projection to the spectrum presentation. -/
@[reassoc]
lemma relativeProjectiveAffineBaseIso_hom_relativeProjectiveToBase
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeProjectiveAffineBaseIso s d U hU).hom ≫
        relativeProjectiveToBase
          (Spec.map (affineOpenCoefficientMap s U hU)) d =
      relativeProjectiveToBase (U.ι ≫ s) d ≫ hU.isoSpec.hom := by
  change
    (relativeProjectiveAffineBaseIso s d U hU).hom ≫
        pullback.fst
          (Spec.map (affineOpenCoefficientMap s U hU))
          (MvPolynomial.homogeneousProjπ
            (R := k) (σ := Fin (d + 1))) =
      pullback.fst
          (U.ι ≫ s)
          (MvPolynomial.homogeneousProjπ
            (R := k) (σ := Fin (d + 1))) ≫
        hU.isoSpec.hom
  simp [relativeProjectiveAffineBaseIso, pullback.map,
    pullback.lift_fst]

/-- The affine-base comparison leaves the projective projection unchanged. -/
@[reassoc]
lemma relativeProjectiveAffineBaseIso_hom_relativeProjectiveToProjective
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeProjectiveAffineBaseIso s d U hU).hom ≫
        relativeProjectiveToProjective
          (Spec.map (affineOpenCoefficientMap s U hU)) d =
      relativeProjectiveToProjective (U.ι ≫ s) d := by
  simp only [relativeProjectiveAffineBaseIso, asIso_hom,
    relativeProjectiveToProjective, pullback.map]
  rw [pullback.lift_snd]
  simp

/-- Relative projective space over an affine open, expressed as ordinary projective space over
the open's section ring. -/
def relativeProjectiveAffineIso
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    relativeProjectiveScheme (U.ι ≫ s) d ≅
      Proj
        (MvPolynomial.homogeneousSubmodule
          (Fin (d + 1)) Γ(S, U)) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact relativeProjectiveAffineBaseIso s d U hU ≪≫
    (coefficientRelativeProjectiveIso k Γ(S, U) d).symm

private lemma coefficientRelativeProjectiveIso_inv_homogeneousProjπ
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (d : ℕ) :
    (coefficientRelativeProjectiveIso k R d).inv ≫
        MvPolynomial.homogeneousProjπ
          (R := R) (σ := Fin (d + 1)) =
      relativeProjectiveToBase
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) d := by
  rw [← cancel_epi (coefficientRelativeProjectiveIso k R d).hom]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact
    (coefficientRelativeProjectiveIso_hom_relativeProjectiveToBase
      k R d).symm

private lemma coefficientRelativeProjectiveIso_inv_coefficientMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (d : ℕ) :
    (coefficientRelativeProjectiveIso k R d).inv ≫
        MvPolynomial.coefficientMap (algebraMap k R) d =
      relativeProjectiveToProjective
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) d := by
  rw [← cancel_epi (coefficientRelativeProjectiveIso k R d).hom]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact
    (coefficientRelativeProjectiveIso_hom_relativeProjectiveToProjective
      k R d).symm

/-- The affine-projective comparison commutes with projection to the affine spectrum. -/
@[reassoc]
lemma relativeProjectiveAffineIso_hom_homogeneousProjπ
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (relativeProjectiveAffineIso s d U hU).hom ≫
        MvPolynomial.homogeneousProjπ
          (R := Γ(S, U)) (σ := Fin (d + 1)) =
      relativeProjectiveToBase (U.ι ≫ s) d ≫ hU.isoSpec.hom := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  change
    ((relativeProjectiveAffineBaseIso s d U hU).hom ≫
        (coefficientRelativeProjectiveIso k Γ(S, U) d).inv) ≫
      MvPolynomial.homogeneousProjπ
        (R := Γ(S, U)) (σ := Fin (d + 1)) =
    relativeProjectiveToBase (U.ι ≫ s) d ≫ hU.isoSpec.hom
  rw [Category.assoc,
    coefficientRelativeProjectiveIso_inv_homogeneousProjπ]
  exact relativeProjectiveAffineBaseIso_hom_relativeProjectiveToBase
    s d U hU

/-- The affine-projective comparison followed by coefficient extension is the original
relative-projective projection. -/
@[reassoc]
lemma relativeProjectiveAffineIso_hom_coefficientMap
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (relativeProjectiveAffineIso s d U hU).hom ≫
        MvPolynomial.coefficientMap
          (algebraMap k Γ(S, U)) d =
      relativeProjectiveToProjective (U.ι ≫ s) d := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  change
    ((relativeProjectiveAffineBaseIso s d U hU).hom ≫
        (coefficientRelativeProjectiveIso k Γ(S, U) d).inv) ≫
      MvPolynomial.coefficientMap
        (algebraMap k Γ(S, U)) d =
    relativeProjectiveToProjective (U.ι ≫ s) d
  rw [Category.assoc,
    coefficientRelativeProjectiveIso_inv_coefficientMap]
  exact relativeProjectiveAffineBaseIso_hom_relativeProjectiveToProjective
    s d U hU

end AlgebraicGeometry
