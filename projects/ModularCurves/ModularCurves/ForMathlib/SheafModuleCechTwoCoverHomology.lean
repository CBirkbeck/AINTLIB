/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverEdge
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverVerticalEdge

/-!
# Degree-one homology comparison for two open covers

The horizontal and vertical edge maps from the native Cech complexes for two
open covers have the same target, namely the total complex of the
coefficient-preserving double-Cech bicomplex. When both edge maps are
quasi-isomorphisms in degree one, this identifies the two native degree-one
homology modules.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)

/-- The positive-degree homology isomorphism between two native Cech
complexes, obtained by composing their edge isomorphisms to the common total
complex. -/
noncomputable def moduleCechTwoCoverHomologySuccIso
    (hU : ⨆ i, U i = ⊤)
    (hV : ⨆ i, V i = ⊤)
    (n : ℕ)
    (hrow_n : ∀ q p, q + p = n → 0 < p →
      ((cechComplexFunctor V).obj
        (moduleCechTerm F U q).obj).ExactAt p)
    (hrow_succ : ∀ q p, q + p = n + 1 → 0 < p →
      ((cechComplexFunctor V).obj
        (moduleCechTerm F U q).obj).ExactAt p)
    (hcol_n : ∀ p q, p + q = n → 0 < q →
      ∀ i : Fin (p + 1) → κ,
        (moduleCechShortComplexApp F U (q - 1)
          (∏ᶜ fun k : Fin (p + 1) => V (i k))).Exact)
    (hcol_succ : ∀ p q, p + q = n + 1 → 0 < q →
      ∀ i : Fin (p + 1) → κ,
        (moduleCechShortComplexApp F U (q - 1)
          (∏ᶜ fun k : Fin (p + 1) => V (i k))).Exact) :
    ((cechComplexFunctor V).obj F.obj).homology (n + 1) ≅
      ((cechComplexFunctor U).obj F.obj).homology (n + 1) := by
  let hEdge :=
    (moduleCechTwoCoverBicomplex F U V).totalUpNatHorizontalEdge
      ((cechComplexFunctor U).obj F.obj)
      (moduleCechTwoCoverHorizontalAugmentation F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)
  let vEdge :=
    (moduleCechTwoCoverBicomplex F U V).totalUpNatVerticalEdge
      ((cechComplexFunctor V).obj F.obj)
      (moduleCechTwoCoverVerticalAugmentation F U V).f
      (moduleCechTwoCoverVerticalAugmentation_comm F U V)
      (moduleCechTwoCoverVerticalAugmentation_comp_d F U V)
  letI : QuasiIsoAt hEdge (n + 1) :=
    moduleCechTwoCoverHorizontalEdge_quasiIsoAt_succ
      F U V hV n hrow_n hrow_succ
  letI : QuasiIsoAt vEdge (n + 1) :=
    moduleCechTwoCoverVerticalEdge_quasiIsoAt_succ
      F U V hU n hcol_n hcol_succ
  exact isoOfQuasiIsoAt vEdge (n + 1) ≪≫
    (isoOfQuasiIsoAt hEdge (n + 1)).symm

/-- The degree-one homology isomorphism between two native Cech complexes,
obtained by composing their edge isomorphisms to the common total complex. -/
noncomputable def moduleCechTwoCoverHomologyOneIso
    (hU : ⨆ i, U i = ⊤)
    (hV : ⨆ i, V i = ⊤)
    (hrow : ((cechComplexFunctor V).obj
      (moduleCechTerm F U 0).obj).ExactAt 1)
    (hcol : ∀ i : Fin 1 → κ,
      (moduleCechShortComplexApp F U 0
        (∏ᶜ fun k : Fin 1 => V (i k))).Exact) :
    ((cechComplexFunctor V).obj F.obj).homology 1 ≅
      ((cechComplexFunctor U).obj F.obj).homology 1 := by
  let hEdge :=
    (moduleCechTwoCoverBicomplex F U V).totalUpNatHorizontalEdge
      ((cechComplexFunctor U).obj F.obj)
      (moduleCechTwoCoverHorizontalAugmentation F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)
  let vEdge :=
    (moduleCechTwoCoverBicomplex F U V).totalUpNatVerticalEdge
      ((cechComplexFunctor V).obj F.obj)
      (moduleCechTwoCoverVerticalAugmentation F U V).f
      (moduleCechTwoCoverVerticalAugmentation_comm F U V)
      (moduleCechTwoCoverVerticalAugmentation_comp_d F U V)
  letI : QuasiIsoAt hEdge 1 :=
    moduleCechTwoCoverHorizontalEdge_quasiIsoAt_one F U V hV hrow
  letI : QuasiIsoAt vEdge 1 :=
    moduleCechTwoCoverVerticalEdge_quasiIsoAt_one F U V hU hcol
  exact isoOfQuasiIsoAt vEdge 1 ≪≫
    (isoOfQuasiIsoAt hEdge 1).symm

/-- The two native Cech complexes are exact in degree one simultaneously
under the hypotheses of the two-cover comparison. -/
theorem moduleCechTwoCover_exactAt_one_iff
    (hU : ⨆ i, U i = ⊤)
    (hV : ⨆ i, V i = ⊤)
    (hrow : ((cechComplexFunctor V).obj
      (moduleCechTerm F U 0).obj).ExactAt 1)
    (hcol : ∀ i : Fin 1 → κ,
      (moduleCechShortComplexApp F U 0
        (∏ᶜ fun k : Fin 1 => V (i k))).Exact) :
    ((cechComplexFunctor V).obj F.obj).ExactAt 1 ↔
      ((cechComplexFunctor U).obj F.obj).ExactAt 1 := by
  let hEdge :=
    (moduleCechTwoCoverBicomplex F U V).totalUpNatHorizontalEdge
      ((cechComplexFunctor U).obj F.obj)
      (moduleCechTwoCoverHorizontalAugmentation F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)
  let vEdge :=
    (moduleCechTwoCoverBicomplex F U V).totalUpNatVerticalEdge
      ((cechComplexFunctor V).obj F.obj)
      (moduleCechTwoCoverVerticalAugmentation F U V).f
      (moduleCechTwoCoverVerticalAugmentation_comm F U V)
      (moduleCechTwoCoverVerticalAugmentation_comp_d F U V)
  letI : QuasiIsoAt hEdge 1 :=
    moduleCechTwoCoverHorizontalEdge_quasiIsoAt_one F U V hV hrow
  letI : QuasiIsoAt vEdge 1 :=
    moduleCechTwoCoverVerticalEdge_quasiIsoAt_one F U V hU hcol
  exact (exactAt_iff_of_quasiIsoAt vEdge 1).trans
    (exactAt_iff_of_quasiIsoAt hEdge 1).symm

/-- Finite generation of native Cech homology in degree one is independent of
the chosen cover under the hypotheses of the two-cover comparison. -/
theorem moduleCechTwoCover_homology_one_module_finite
    (hU : ⨆ i, U i = ⊤)
    (hV : ⨆ i, V i = ⊤)
    (hrow : ((cechComplexFunctor V).obj
      (moduleCechTerm F U 0).obj).ExactAt 1)
    (hcol : ∀ i : Fin 1 → κ,
      (moduleCechShortComplexApp F U 0
        (∏ᶜ fun k : Fin 1 => V (i k))).Exact)
    [Module.Finite R (((cechComplexFunctor U).obj F.obj).homology 1)] :
    Module.Finite R (((cechComplexFunctor V).obj F.obj).homology 1) :=
  Module.Finite.equiv
    (moduleCechTwoCoverHomologyOneIso F U V hU hV hrow hcol).symm.toLinearEquiv

end TopCat.Sheaf
