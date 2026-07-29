/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Kernels of isomorphic cochain complexes

Transport the concrete linear kernel of the first differential across an
isomorphism of cochain complexes of modules.
-/

open CategoryTheory

universe u v

namespace HomologicalComplex

private noncomputable def kernelZeroMap
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) :
    LinearMap.ker (K.d 0 1).hom →ₗ[R]
      LinearMap.ker (L.d 0 1).hom where
  toFun x := ⟨(f.f 0).hom x.1, by
    change ((f.f 0 ≫ L.d 0 1).hom) x.1 = 0
    rw [f.comm]
    change (f.f 1).hom ((K.d 0 1).hom x.1) = 0
    rw [x.2, map_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    exact (f.f 0).hom.map_smul r x.1

/-- Two cochain maps which are inverse in degree zero induce an equivalence between
the kernels of the first differentials. -/
noncomputable def kernelZeroLinearEquivOfHom
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ K)
    (hfg : f.f 0 ≫ g.f 0 = 𝟙 _)
    (hgf : g.f 0 ≫ f.f 0 = 𝟙 _) :
    LinearMap.ker (K.d 0 1).hom ≃ₗ[R]
      LinearMap.ker (L.d 0 1).hom :=
  LinearEquiv.ofLinear (kernelZeroMap f) (kernelZeroMap g)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom hgf x.1)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom hfg x.1)

/-- The kernel equivalence induced by inverse cochain maps is given by the
degree-zero component of the forward map. -/
theorem kernelZeroLinearEquivOfHom_coe
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ K)
    (hfg : f.f 0 ≫ g.f 0 = 𝟙 _)
    (hgf : g.f 0 ≫ f.f 0 = 𝟙 _)
    (x : LinearMap.ker (K.d 0 1).hom) :
    (kernelZeroLinearEquivOfHom f g hfg hgf x).1 =
      (f.f 0).hom x.1 := by
  rfl

/-- The inverse kernel equivalence induced by inverse cochain maps is given by
the degree-zero component of the inverse map. -/
theorem kernelZeroLinearEquivOfHom_symm_coe
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ K)
    (hfg : f.f 0 ≫ g.f 0 = 𝟙 _)
    (hgf : g.f 0 ≫ f.f 0 = 𝟙 _)
    (x : LinearMap.ker (L.d 0 1).hom) :
    ((kernelZeroLinearEquivOfHom f g hfg hgf).symm x).1 =
      (g.f 0).hom x.1 := by
  rfl

/-- An isomorphism of cochain complexes of modules identifies the kernels of
their first differentials. -/
noncomputable def kernelZeroIsoOfIso
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (e : K ≅ L) :
    ModuleCat.of R (LinearMap.ker (K.d 0 1).hom) ≅
      ModuleCat.of R (LinearMap.ker (L.d 0 1).hom) :=
  let eSc : K.sc' 0 0 1 ≅ L.sc' 0 0 1 :=
    (shortComplexFunctor' (ModuleCat.{v} R) (.up ℕ) 0 0 1).mapIso e
  (K.sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
    ShortComplex.cyclesMapIso eSc ≪≫
    (L.sc' 0 0 1).moduleCatCyclesIso

/-- The kernel equivalence induced by a cochain-complex isomorphism commutes with the
inclusions into degree zero. -/
@[reassoc]
theorem kernelZeroIsoOfIso_hom_subtype
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (e : K ≅ L) :
    (kernelZeroIsoOfIso e).hom ≫
        ModuleCat.ofHom (LinearMap.ker (L.d 0 1).hom).subtype =
      ModuleCat.ofHom (LinearMap.ker (K.d 0 1).hom).subtype ≫ e.hom.f 0 := by
  apply ModuleCat.hom_ext
  ext x
  simp [kernelZeroIsoOfIso]
  let eSc := (shortComplexFunctor' (ModuleCat.{v} R) (.up ℕ) 0 0 1).mapIso e
  have hcomp :
      (((K.sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
          ShortComplex.cyclesMapIso eSc ≪≫
          (L.sc' 0 0 1).moduleCatCyclesIso).hom ≫
        (L.sc' 0 0 1).moduleCatLeftHomologyData.i) =
      (K.sc' 0 0 1).moduleCatLeftHomologyData.i ≫ e.hom.f 0 := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [(L.sc' 0 0 1).moduleCatCyclesIso_hom_i]
    change (K.sc' 0 0 1).moduleCatCyclesIso.inv ≫
        ShortComplex.cyclesMap eSc.hom ≫ (L.sc' 0 0 1).iCycles =
      (K.sc' 0 0 1).moduleCatLeftHomologyData.i ≫ eSc.hom.τ₂
    rw [ShortComplex.cyclesMap_i]
    rw [(K.sc' 0 0 1).moduleCatCyclesIso_inv_iCycles_assoc]
  exact ConcreteCategory.congr_hom hcomp x

end HomologicalComplex
