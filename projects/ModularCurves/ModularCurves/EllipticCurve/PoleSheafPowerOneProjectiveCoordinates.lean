/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleSheafPowerOneProjectiveBaseChange
import ModularCurves.EllipticCurve.PoleSheafProjectiveCoordinates
import ModularCurves.ForMathlib.PrescribedLocalizedBasis

/-!
# The prescribed first basis vector for projective pole sections

On a principal neighbourhood of every base prime, the canonical first-pole section is
the unique vector of a basis of the rank-one first pole-section module.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Around every prime of the affine base, the canonical section of `O([0])` is the unique
vector of a basis of its projectively presented base-section module on a principal
neighbourhood. -/
theorem FibrewiseElliptic.exists_sectionPoleSheafPowerOne_projectiveClosed_away_basis
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    (p : Ideal Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) [p.IsPrime] :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz 1
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let P := Scheme.Modules.baseSections π M
    ∃ a : B, a ∉ p ∧
      ∃ b : Module.Basis (Fin 1) (Localization.Away a)
          (LocalizedModule.Away a P),
        b 0 = LocalizedModule.mkLinearMap (.powers a) P
          (sectionPoleSheafPowerOneSection π z hz) := by
  dsimp only
  let S := Spec (.of R)
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz 1
  let B := Γ(S, (⊤ : S.Opens))
  let P := Scheme.Modules.baseSections π M
  let x : P := sectionPoleSheafPowerOneSection π z hz
  obtain ⟨hfinite, hprojective, hrank⟩ :=
    h.sectionPoleSheafPower_projectiveClosed_baseSections_data
      f hsm z hz (n := 1) (by simp)
  letI : Module.Finite B P := hfinite
  letI : Module.Projective B P := hprojective
  letI : Module.FinitePresentation B P :=
    Module.finitePresentation_of_projective B P
  letI : Module.Flat B P := inferInstance
  have hrankp : Module.rankAtStalk (R := B) P ⟨p, inferInstance⟩ = 1 := by
    rw [hrank]
  let T := Spec (.of p.ResidueField)
  let t : T ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap B p.ResidueField)) ≫ S.isoSpec.inv
  let K := Γ(T, (⊤ : T.Opens))
  letI : Algebra B K := t.appTop.hom.toAlgebra
  have hKfield : IsField K :=
    (Scheme.ΓSpecIso (.of p.ResidueField)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField p.ResidueField)
  letI : Field K := hKfield.toField
  have hcomp :
      t.appTop ≫ (Scheme.ΓSpecIso (.of p.ResidueField)).hom =
        CommRingCat.ofHom (algebraMap B p.ResidueField) := by
    dsimp only [t]
    rw [Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    have hΓ : (Scheme.ΓSpecIso (.of B)).hom = S.isoSpec.hom.appTop := by
      exact (Scheme.toSpecΓ_appTop S).symm
    rw [hΓ, ← Category.assoc,
      ← Scheme.Hom.comp_appTop S.isoSpec.hom S.isoSpec.inv,
      S.isoSpec.hom_inv_id]
    simp
  have happly (r : B) :
      (Scheme.ΓSpecIso (.of p.ResidueField)).hom.hom
          (algebraMap B K r) =
        algebraMap B p.ResidueField r := by
    change ((t.appTop ≫
      (Scheme.ΓSpecIso (.of p.ResidueField)).hom).hom) r =
        (CommRingCat.ofHom (algebraMap B p.ResidueField)).hom r
    rw [hcomp]
  have hker : RingHom.ker (algebraMap B K) = p := by
    apply Ideal.ext
    intro r
    change (algebraMap B K r = 0) ↔ r ∈ p
    constructor
    · intro hr
      apply Ideal.algebraMap_residueField_eq_zero.mp
      rw [← happly, hr, map_zero]
    · intro hr
      apply (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of p.ResidueField)).hom).1
      rw [map_zero, happly,
        Ideal.algebraMap_residueField_eq_zero.mpr hr]
  letI : Nonempty T := inferInstance
  have hgeom :=
    h.sectionPoleSheafPowerOne_projectiveClosed_baseSectionsBaseChange_ne_zero
      f hsm z hz t
  have hxK : (1 : K) ⊗ₜ[B] x ≠ (0 : K ⊗[B] P) := by
    intro hxzero
    apply hgeom
    rw [hxzero, map_zero]
  exact Module.FinitePresentation.exists_notMem_basis_singleton_of_field_ne_zero
    p x hrankp hker hxK

end ModularCurves
