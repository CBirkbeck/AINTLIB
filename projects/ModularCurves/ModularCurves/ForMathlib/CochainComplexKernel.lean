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
