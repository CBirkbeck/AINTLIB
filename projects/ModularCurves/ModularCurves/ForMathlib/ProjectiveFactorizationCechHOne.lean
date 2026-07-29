/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveFactorizationCechFinite
import ModularCurves.ForMathlib.SchemeModuleCechTwoAffineCover
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechHOneFinite

/-!
# Degree-one Cech finiteness from a projective factorization

Over a Noetherian affine base, a finite-type quasicoherent module on a
projectively factored scheme has finite native Cech homology in degree one
for every finite affine open cover.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsProjectiveFactorization

open TopCat TopCat.Sheaf

/-- A finite-type quasicoherent module on a projectively factored scheme has
finite native Cech homology in degree one on every finite affine cover. -/
theorem baseModuleCech_homology_one_module_finite_of_affine_openCover
    {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    {f : X ⟶ Spec (.of R)}
    (hf : AlgebraicGeometry.IsProjectiveFactorization f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {κ : Type u} [Finite κ]
    (V : κ → X.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i)) :
    Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (((cechComplexFunctor V).obj
        (Scheme.Modules.baseModuleTopSheaf f M).obj).homology 1) := by
  letI : IsProper f := hf.isProper
  letI : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨d, i, hi, _, hfinite⟩ :=
    hf.exists_orderedBaseCechHomologyFinite M
  letI : IsClosedImmersion i := hi
  let U := fun j =>
    i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
      (R := R) (σ := Fin (d + 1)) j
  have hU : IsOpenCover U :=
    i.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top
        (R := R) (σ := Fin (d + 1)))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen
      (R := R) j).preimage i
  letI : Module.Finite
      Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((Scheme.Modules.orderedBaseCechComplex f M U).homology 1) :=
    hfinite 1
  letI : Module.Finite
      Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((Scheme.Modules.baseCechComplex f M U).homology 1) :=
    Scheme.Modules.baseCechComplex_homology_one_module_finite_of_orderedBaseCechComplex
      f M U
  letI : Module.Finite
      Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (((cechComplexFunctor U).obj
        (Scheme.Modules.baseModuleTopSheaf f M).obj).homology 1) := by
    change Module.Finite
      Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((Scheme.Modules.baseCechComplex f M U).homology 1)
    infer_instance
  apply
    Scheme.Modules.baseModuleCech_homology_one_module_finite_of_affine_openCovers
      f M U hU hUaff V hV hVaff

end AlgebraicGeometry.IsProjectiveFactorization
