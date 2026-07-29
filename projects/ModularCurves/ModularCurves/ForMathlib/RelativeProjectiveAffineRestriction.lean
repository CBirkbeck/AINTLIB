/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveFactorization

/-!
# Restricting relative projective factorizations

Relative projective space commutes with restriction to an open subscheme of its base. Consequently,
a relative projective factorization restricts to every base open.
-/

open CategoryTheory Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Restricting relative projective space to an open of its base gives relative projective space
over that open. -/
def relativeProjectiveRestrictIso
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) (U : S.Opens) :
    ((relativeProjectiveToBase s d) ⁻¹ᵁ U).toScheme ≅
      relativeProjectiveScheme (U.ι ≫ s) d :=
  (pullbackRestrictIsoRestrict (relativeProjectiveToBase s d) U).symm ≪≫
    pullbackSymmetry (relativeProjectiveToBase s d) U.ι ≪≫
      pullbackRightPullbackFstIso
        s
        (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)))
        U.ι

/-- The relative-projective restriction isomorphism commutes with projection to the open base. -/
@[reassoc]
lemma relativeProjectiveRestrictIso_hom_relativeProjectiveToBase
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) (U : S.Opens) :
    (relativeProjectiveRestrictIso s d U).hom ≫
        relativeProjectiveToBase (U.ι ≫ s) d =
      morphismRestrict (relativeProjectiveToBase s d) U := by
  simp [relativeProjectiveRestrictIso, morphismRestrict]

namespace IsRelativeProjectiveFactorization

variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}

/-- A relative projective factorization restricts to every open subscheme of its base. -/
lemma restrict (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) :
    IsRelativeProjectiveFactorization (U.ι ≫ s) (morphismRestrict f U) := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  let V : (relativeProjectiveScheme s d).Opens :=
    relativeProjectiveToBase s d ⁻¹ᵁ U
  have hpreimage : f ⁻¹ᵁ U = i ⁻¹ᵁ V := by
    dsimp only [V]
    rw [← Scheme.Hom.comp_preimage, hif]
  let e : (f ⁻¹ᵁ U).toScheme ≅ (i ⁻¹ᵁ V).toScheme :=
    X.isoOfEq hpreimage
  let j : (f ⁻¹ᵁ U).toScheme ⟶ relativeProjectiveScheme (U.ι ≫ s) d :=
    e.hom ≫ morphismRestrict i V ≫ (relativeProjectiveRestrictIso s d U).hom
  have hj : IsClosedImmersion j := by
    dsimp only [j]
    infer_instance
  refine ⟨d, j, hj, ?_⟩
  dsimp only [j]
  rw [Category.assoc, Category.assoc,
    relativeProjectiveRestrictIso_hom_relativeProjectiveToBase]
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  change
    e.hom ≫ morphismRestrict i V ≫ V.ι ≫ relativeProjectiveToBase s d =
      (f ⁻¹ᵁ U).ι ≫ f
  simp only [morphismRestrict_ι_assoc]
  dsimp only [e]
  simp only [Scheme.isoOfEq_hom_ι_assoc]
  rw [hif]

end IsRelativeProjectiveFactorization

end AlgebraicGeometry
