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

end HomologicalComplex
