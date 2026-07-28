/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveAffineFactorization
import ModularCurves.ForMathlib.RelativeProjectiveFactorizationChoice

/-!
# Chosen relative projective maps over affine opens

The chosen embedding of a relative projective factorization restricts to an affine base open
without changing its projective dimension. After the affine-base comparison, this gives a fixed
closed embedding into ordinary projective space over the open's section ring.
-/

open CategoryTheory Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Restriction of relative projective space commutes with projection to the original projective
space. -/
@[reassoc]
lemma relativeProjectiveRestrictIso_hom_relativeProjectiveToProjective
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) (d : ℕ) (U : S.Opens) :
    (relativeProjectiveRestrictIso s d U).hom ≫
        relativeProjectiveToProjective (U.ι ≫ s) d =
      ((relativeProjectiveToBase s d) ⁻¹ᵁ U).ι ≫
        relativeProjectiveToProjective s d := by
  simp [relativeProjectiveRestrictIso]
  rw [← Category.assoc, pullbackRestrictIsoRestrict_inv_fst]

namespace IsRelativeProjectiveFactorization

variable {k : Type u} [CommRing k] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of k)} {f : X ⟶ S}

/-- The ambient open above a base open for the chosen relative projective embedding. -/
def chosenRestrictionAmbientOpen
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    (relativeProjectiveScheme s h.chosenDimension).Opens :=
  relativeProjectiveToBase s h.chosenDimension ⁻¹ᵁ U

/-- The inverse image of a base open agrees with the inverse image of the corresponding ambient
projective open. -/
lemma chosenRestrictionSourcePreimage
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    f ⁻¹ᵁ U =
      h.chosenEmbedding ⁻¹ᵁ h.chosenRestrictionAmbientOpen U := by
  rw [chosenRestrictionAmbientOpen, ← Scheme.Hom.comp_preimage,
    h.chosenEmbedding_relativeProjectiveToBase]

/-- The source-open identification induced by the chosen factorization equation. -/
def chosenRestrictionSourceIso
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    (f ⁻¹ᵁ U).toScheme ≅
      (h.chosenEmbedding ⁻¹ᵁ
        h.chosenRestrictionAmbientOpen U).toScheme :=
  X.isoOfEq (h.chosenRestrictionSourcePreimage U)

/-- The chosen relative projective embedding restricted to a base open. -/
def chosenRestrictedEmbedding
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶
      relativeProjectiveScheme (U.ι ≫ s) h.chosenDimension :=
  ((h.chosenRestrictionSourceIso U).hom ≫
      morphismRestrict h.chosenEmbedding
        (h.chosenRestrictionAmbientOpen U)) ≫
    (relativeProjectiveRestrictIso
      s h.chosenDimension U).hom

/-- The chosen restricted embedding remains a closed immersion. -/
lemma chosenRestrictedEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    IsClosedImmersion (h.chosenRestrictedEmbedding U) := by
  letI : IsClosedImmersion h.chosenEmbedding :=
    h.chosenEmbedding_isClosedImmersion
  have hSource :
      IsClosedImmersion (h.chosenRestrictionSourceIso U).hom :=
    inferInstance
  have hRestrict : IsClosedImmersion
      (morphismRestrict h.chosenEmbedding
        (h.chosenRestrictionAmbientOpen U)) :=
    inferInstance
  have hAmbient :
      IsClosedImmersion
      (relativeProjectiveRestrictIso
        s h.chosenDimension U).hom :=
    inferInstance
  have hFirst : IsClosedImmersion
      ((h.chosenRestrictionSourceIso U).hom ≫
        morphismRestrict h.chosenEmbedding
          (h.chosenRestrictionAmbientOpen U)) :=
    @IsClosedImmersion.comp _ _ _ _ _ hSource hRestrict
  dsimp only [chosenRestrictedEmbedding]
  exact @IsClosedImmersion.comp _ _ _ _ _ hFirst hAmbient

attribute [local instance] chosenRestrictedEmbedding_isClosedImmersion

/-- Projection of the chosen restricted embedding recovers the restricted morphism. -/
@[reassoc]
lemma chosenRestrictedEmbedding_relativeProjectiveToBase
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    h.chosenRestrictedEmbedding U ≫
        relativeProjectiveToBase
          (U.ι ≫ s) h.chosenDimension =
      morphismRestrict f U := by
  dsimp only [chosenRestrictedEmbedding, chosenRestrictionAmbientOpen]
  rw [Category.assoc, Category.assoc,
    relativeProjectiveRestrictIso_hom_relativeProjectiveToBase]
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  change
    (h.chosenRestrictionSourceIso U).hom ≫
        morphismRestrict h.chosenEmbedding
            (h.chosenRestrictionAmbientOpen U) ≫
          (h.chosenRestrictionAmbientOpen U).ι ≫
        relativeProjectiveToBase s h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ f
  simp only [morphismRestrict_ι_assoc]
  dsimp only [chosenRestrictionSourceIso]
  simp only [Scheme.isoOfEq_hom_ι_assoc]
  rw [h.chosenEmbedding_relativeProjectiveToBase]

/-- Projection of the chosen restricted embedding to the original projective space is the
restriction of the chosen projective map. -/
@[reassoc]
lemma chosenRestrictedEmbedding_relativeProjectiveToProjective
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    h.chosenRestrictedEmbedding U ≫
        relativeProjectiveToProjective
          (U.ι ≫ s) h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ h.chosenProjectiveMap := by
  dsimp only [chosenRestrictedEmbedding, chosenRestrictionAmbientOpen]
  rw [Category.assoc, Category.assoc,
    relativeProjectiveRestrictIso_hom_relativeProjectiveToProjective]
  change
    (h.chosenRestrictionSourceIso U).hom ≫
        morphismRestrict h.chosenEmbedding
            (h.chosenRestrictionAmbientOpen U) ≫
          (h.chosenRestrictionAmbientOpen U).ι ≫
        relativeProjectiveToProjective s h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ h.chosenEmbedding ≫
        relativeProjectiveToProjective s h.chosenDimension
  simp only [morphismRestrict_ι_assoc]
  dsimp only [chosenRestrictionSourceIso]
  simp only [Scheme.isoOfEq_hom_ι_assoc]

/-- The chosen closed embedding into projective space over an affine open's section ring. -/
def chosenAffineProjectiveEmbedding
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (f ⁻¹ᵁ U).toScheme ⟶
      Proj
        (MvPolynomial.homogeneousSubmodule
          (Fin (h.chosenDimension + 1)) Γ(S, U)) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact h.chosenRestrictedEmbedding U ≫
    (relativeProjectiveAffineIso
      s h.chosenDimension U hU).hom

/-- The chosen affine projective embedding is a closed immersion. -/
lemma chosenAffineProjectiveEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    IsClosedImmersion (h.chosenAffineProjectiveEmbedding U hU) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [chosenAffineProjectiveEmbedding]
  infer_instance

attribute [local instance]
  chosenAffineProjectiveEmbedding_isClosedImmersion

/-- The chosen affine projective embedding recovers the restricted structural map. -/
@[reassoc]
lemma chosenAffineProjectiveEmbedding_homogeneousProjπ
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    h.chosenAffineProjectiveEmbedding U hU ≫
        MvPolynomial.homogeneousProjπ
          (R := Γ(S, U))
          (σ := Fin (h.chosenDimension + 1)) =
      morphismRestrict f U ≫ hU.isoSpec.hom := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [chosenAffineProjectiveEmbedding]
  rw [Category.assoc,
    relativeProjectiveAffineIso_hom_homogeneousProjπ]
  rw [← Category.assoc,
    h.chosenRestrictedEmbedding_relativeProjectiveToBase]

/-- Coefficient extension of the chosen affine projective embedding is the restricted original
chosen projective map. -/
@[reassoc]
lemma chosenAffineProjectiveEmbedding_coefficientMap
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    h.chosenAffineProjectiveEmbedding U hU ≫
        MvPolynomial.coefficientMap
          (algebraMap k Γ(S, U))
          h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ h.chosenProjectiveMap := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [chosenAffineProjectiveEmbedding]
  rw [Category.assoc,
    relativeProjectiveAffineIso_hom_coefficientMap]
  exact h.chosenRestrictedEmbedding_relativeProjectiveToProjective U

end IsRelativeProjectiveFactorization

end AlgebraicGeometry
