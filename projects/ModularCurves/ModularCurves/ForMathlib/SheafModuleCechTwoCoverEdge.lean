/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverExact
import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdgeModule

/-!
# Horizontal edge of the module-valued two-cover Cech bicomplex

The horizontal edge from the native Cech complex for the outer family is a
degree-one quasi-isomorphism when the inner family covers and its native Cech
complex on the zeroth outer Cech term is exact in degree one.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)

/-- The horizontal edge of the module-valued two-cover Cech bicomplex is a
degree-one quasi-isomorphism under the one required native Cech exactness
condition. -/
theorem moduleCechTwoCoverHorizontalEdge_quasiIsoAt_one
    (hV : ⨆ i, V i = ⊤)
    (hrow : ((cechComplexFunctor V).obj
      (moduleCechTerm F U 0).obj).ExactAt 1) :
    QuasiIsoAt
      ((moduleCechTwoCoverBicomplex F U V).totalUpNatHorizontalEdge
        ((cechComplexFunctor U).obj F.obj)
        (moduleCechTwoCoverHorizontalAugmentation F U V)
        (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
        (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)) 1 := by
  letI : Mono (moduleCechTwoCoverHorizontalAugmentation F U V 1) :=
    moduleCechTwoCoverHorizontalAugmentation_mono F U V 1 hV
  letI : Mono (moduleCechTwoCoverHorizontalAugmentation F U V 2) :=
    moduleCechTwoCoverHorizontalAugmentation_mono F U V 2 hV
  exact
    HomologicalComplex₂.totalUpNatHorizontalEdge_quasiIsoAt_one_module
      (moduleCechTwoCoverBicomplex F U V)
      ((cechComplexFunctor U).obj F.obj)
      (moduleCechTwoCoverHorizontalAugmentation F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)
      (moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
        F U V 0 hV)
      (moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
        F U V 1 hV)
      (moduleCechTwoCover_row_exactAt_one F U V 0 hrow)

end TopCat.Sheaf
