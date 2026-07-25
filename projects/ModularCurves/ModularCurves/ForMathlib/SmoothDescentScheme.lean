/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.EtaleSmoothDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Scheme-level descent of relative-dimension-one smoothness

**[T-YR-6 (c1), interface]** If `p : Z ⟶ Y` is a finite étale surjective cover of
an affine scheme `Y` over an affine noetherian base, and `Z` is standard smooth of
relative dimension one over the base, then `Y` is smooth of relative dimension one.

This is the form consumed by the `Y(ρ̄)` smoothness leaf: `Z` is the Legendre-anchored
ρ-quotient (`rhoLegendre_carrier_smooth`) and `Y` is the representing curve.
-/

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- (Implementation) The `Spec` of the global-sections map of a morphism of affine
schemes is surjective when the morphism is. -/
theorem surjective_specMap_appTop {Y Z : Scheme.{u}} (p : Z ⟶ Y)
    [IsAffine Y] [IsAffine Z] [Surjective p] :
    Function.Surjective (Spec.map (p.appTop)).base := by
  have hp : Spec.map (p.appTop) = Z.isoSpec.inv ≫ p ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality p, Iso.inv_hom_id_assoc]
  rw [hp]
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
  exact (Y.isoSpec.hom.homeomorph.surjective.comp
    ‹Surjective p›.1).comp Z.isoSpec.inv.homeomorph.surjective

/-- **[T-YR-6 (c1), scheme interface]** Relative-dimension-one smoothness descends
along a finite étale surjective cover of an affine scheme. -/
theorem smoothOfRelativeDimension_one_of_finite_etale_surjective_cover
    {S Y Z : Scheme.{u}} [IsAffine S] [IsAffine Y] [IsNoetherianRing Γ(S, ⊤)]
    (sY : Y ⟶ S) (p : Z ⟶ Y) [IsFinite p] [Etale p] [Surjective p]
    (hZ : RingHom.IsStandardSmoothOfRelativeDimension 1 ((p ≫ sY).appTop).hom) :
    SmoothOfRelativeDimension 1 sY := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  letI : Algebra Γ(Y, ⊤) Γ(Z, ⊤) := (p.appTop).hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := (sY.appTop).hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Z, ⊤) := ((p ≫ sY).appTop).hom.toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(Z, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show ((p ≫ sY).appTop).hom x = (p.appTop).hom ((sY.appTop).hom x)
    rw [Scheme.Hom.comp_appTop]
    rfl
  haveI hfin : Module.Finite Γ(Y, ⊤) Γ(Z, ⊤) :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := p)).mp ‹IsFinite p›).2
  haveI het : Algebra.Etale Γ(Y, ⊤) Γ(Z, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := p)).mp ‹Etale p›
  haveI hff : Module.FaithfullyFlat Γ(Y, ⊤) Γ(Z, ⊤) :=
    Module.FaithfullyFlat.of_comap_surjective (surjective_specMap_appTop p)
  haveI hss : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(S, ⊤) Γ(Z, ⊤) := hZ
  exact (HasRingHomProperty.iff_of_isAffine
    (P := @SmoothOfRelativeDimension 1) (f := sY)).mpr
    (Algebra.locally_isStandardSmoothOfRelativeDimension_one_of_etale_faithfullyFlat
      Γ(S, ⊤) Γ(Y, ⊤) Γ(Z, ⊤))


section Carrier

/-- (Implementation) The global-sections map of `Spec φ` is `φ` up to the `Γ ∘ Spec`
identification, so it inherits `φ`'s standard smoothness. -/
theorem isStandardSmoothOfRelativeDimension_specMap_appTop {n : ℕ}
    {k R : CommRingCat.{u}} (φ : k ⟶ R)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension n φ.hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n ((Spec.map φ).appTop).hom := by
  have he : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso k).hom ≫ φ ≫ (Scheme.ΓSpecIso R).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [he]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
    (Scheme.ΓSpecIso k).commRingCatIsoToRingEquiv
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _
      (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv hφ)

/-- **[T-YR-6 carrier, ring form]** If `Z` is affine and étale over `Spec R`, and `R` is
standard smooth of relative dimension `n` over `k`, then the global-sections map of
`Z ⟶ Spec k` is standard smooth of relative dimension `n`. -/
theorem isStandardSmoothOfRelativeDimension_appTop_of_etale_over_spec {n : ℕ}
    {k R : CommRingCat.{u}} (φ : k ⟶ R) {Z : Scheme.{u}} (q : Z ⟶ Spec R)
    [IsAffine Z] [Etale q]
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension n φ.hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n ((q ≫ Spec.map φ).appTop).hom := by
  have het : RingHom.Etale (q.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := q)).mp ‹Etale q›
  letI : Algebra Γ(Spec R, ⊤) Γ(Z, ⊤) := (q.appTop).hom.toAlgebra
  haveI : Algebra.Etale Γ(Spec R, ⊤) Γ(Z, ⊤) := het
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (q.appTop).hom :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  have := h0.comp (isStandardSmoothOfRelativeDimension_specMap_appTop φ hφ)
  rw [Scheme.Hom.comp_appTop]
  simpa using this

end Carrier

end AlgebraicGeometry

end
