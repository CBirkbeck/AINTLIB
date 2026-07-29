/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechNativeDegreeExact
import ModularCurves.ForMathlib.SheafModuleCechSectionsExact
import ModularCurves.ForMathlib.TotalComplexUpNatVerticalEdgeModule

/-!
# Vertical edge of the module-valued two-cover Cech bicomplex

The outer cover gives exactness of the two augmented low columns and
monicity of the vertical augmentation. Exactness at the next outer Cech
degree remains an explicit acyclicity input on the degree-zero inner tuple
opens.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)

attribute [local instance] moduleCechSheafPreadditive

private theorem moduleCechAugmentation_hom_comp :
    (moduleCechAugmentation F U).hom ≫
        (moduleCechDifferential F U 0).hom = 0 :=
  congrArg (fun f => f.hom) (moduleCechAugmentation_comp F U)

/-- A vertical column of the two-cover bicomplex, augmented by the native
Cech complex for the inner family. -/
noncomputable def moduleCechTwoCoverVerticalAugmentedShortComplex
    (p : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    ((moduleCechTwoCoverVerticalAugmentation F U V).f p)
    (((moduleCechTwoCoverBicomplex F U V).d 0 1).f p)
    (moduleCechTwoCoverVerticalAugmentation_comp_d F U V p)

/-- Every augmented vertical column is exact when the outer family is an
open cover. -/
theorem moduleCechTwoCoverVerticalAugmentedShortComplex_exact
    (p : ℕ) (hU : ⨆ i, U i = ⊤) :
    (moduleCechTwoCoverVerticalAugmentedShortComplex F U V p).Exact := by
  rw [moduleCechTwoCoverVerticalAugmentedShortComplex]
  change (moduleNativeCechMapShortComplex
    (moduleCechAugmentation F U).hom
    (moduleCechDifferential F U 0).hom
    (moduleCechAugmentation_hom_comp F U) V p).Exact
  apply moduleNativeCechMapShortComplex_exact
  intro i
  exact moduleCechAugmentedShortComplexApp_exact F U
    (∏ᶜ fun k : Fin (p + 1) => V (i k)) hU

/-- Every vertical augmentation is monic when the outer family is an open
cover. -/
theorem moduleCechTwoCoverVerticalAugmentation_mono
    (p : ℕ) (hU : ⨆ i, U i = ⊤) :
    Mono ((moduleCechTwoCoverVerticalAugmentation F U V).f p) := by
  change Mono (((cechComplexFunctor V).map
    (moduleCechAugmentation F U).hom).f p)
  apply moduleNativeCechMap_mono
  intro i
  exact moduleCechAugmentation_app_mono F U
    (∏ᶜ fun k : Fin (p + 1) => V (i k)) hU

/-- Two consecutive module-valued sheaf Cech differentials, evaluated on an
arbitrary open. -/
noncomputable def moduleCechShortComplexApp
    (n : ℕ) (W : Opens X) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    ((moduleCechDifferential F U n).hom.app (op W))
    ((moduleCechDifferential F U (n + 1)).hom.app (op W))
    (congrArg (fun f => f.hom.app (op W))
      (moduleCechDifferential_comp F U n))

/-- Pointwise degree-one exactness on the degree-zero inner tuple opens is
the degree-one column condition in the two-cover bicomplex. -/
theorem moduleCechTwoCover_col_exactAt_one
    (hcol : ∀ i : Fin 1 → κ,
      (moduleCechShortComplexApp F U 0
        (∏ᶜ fun k : Fin 1 => V (i k))).Exact) :
    (ShortComplex.mk
      (((moduleCechTwoCoverBicomplex F U V).d 0 1).f 0)
      (((moduleCechTwoCoverBicomplex F U V).d 1 2).f 0)
      ((moduleCechTwoCoverBicomplex F U V).d_f_comp_d_f
        0 1 2 0)).Exact := by
  change (moduleNativeCechMapShortComplex
    (moduleCechDifferential F U 0).hom
    (moduleCechDifferential F U 1).hom
    (congrArg (fun f => f.hom)
      (moduleCechDifferential_comp F U 0)) V 0).Exact
  apply moduleNativeCechMapShortComplex_exact
  intro i
  exact hcol i

/-- Pointwise exactness of an arbitrary positive outer Cech differential pair
on the degree-`p` inner tuple opens is the corresponding column condition in
the two-cover bicomplex. -/
theorem moduleCechTwoCover_col_exactAt
    (p q : ℕ) (hq : 0 < q)
    (hcol : ∀ i : Fin (p + 1) → κ,
      (moduleCechShortComplexApp F U (q - 1)
        (∏ᶜ fun k : Fin (p + 1) => V (i k))).Exact) :
    (ShortComplex.mk
      (((moduleCechTwoCoverBicomplex F U V).d (q - 1) q).f p)
      (((moduleCechTwoCoverBicomplex F U V).d q (q + 1)).f p)
      ((moduleCechTwoCoverBicomplex F U V).d_f_comp_d_f
        (q - 1) q (q + 1) p)).Exact := by
  cases q with
  | zero => omega
  | succ q =>
      rw [Nat.add_sub_cancel]
      simp only [moduleCechTwoCoverBicomplex_d_f,
        moduleCechComplex_d]
      change (moduleNativeCechMapShortComplex
        (moduleCechDifferential F U q).hom
        (moduleCechDifferential F U (q + 1)).hom
        (congrArg (fun f => f.hom)
          (moduleCechDifferential_comp F U q)) V p).Exact
      apply moduleNativeCechMapShortComplex_exact
      intro i
      exact hcol i

/-- The vertical edge of the module-valued two-cover bicomplex is a
degree-one quasi-isomorphism under the one required pointwise Cech exactness
condition. -/
theorem moduleCechTwoCoverVerticalEdge_quasiIsoAt_one
    (hU : ⨆ i, U i = ⊤)
    (hcol : ∀ i : Fin 1 → κ,
      (moduleCechShortComplexApp F U 0
        (∏ᶜ fun k : Fin 1 => V (i k))).Exact) :
    QuasiIsoAt
      ((moduleCechTwoCoverBicomplex F U V).totalUpNatVerticalEdge
        ((cechComplexFunctor V).obj F.obj)
        (moduleCechTwoCoverVerticalAugmentation F U V).f
        (moduleCechTwoCoverVerticalAugmentation_comm F U V)
        (moduleCechTwoCoverVerticalAugmentation_comp_d F U V)) 1 := by
  letI : Mono
      ((moduleCechTwoCoverVerticalAugmentation F U V).f 1) :=
    moduleCechTwoCoverVerticalAugmentation_mono F U V 1 hU
  letI : Mono
      ((moduleCechTwoCoverVerticalAugmentation F U V).f 2) :=
    moduleCechTwoCoverVerticalAugmentation_mono F U V 2 hU
  exact
    HomologicalComplex₂.totalUpNatVerticalEdge_quasiIsoAt_one_module
      (moduleCechTwoCoverBicomplex F U V)
      ((cechComplexFunctor V).obj F.obj)
      (moduleCechTwoCoverVerticalAugmentation F U V).f
      (moduleCechTwoCoverVerticalAugmentation_comm F U V)
      (moduleCechTwoCoverVerticalAugmentation_comp_d F U V)
      (moduleCechTwoCoverVerticalAugmentedShortComplex_exact
        F U V 0 hU)
      (moduleCechTwoCoverVerticalAugmentedShortComplex_exact
        F U V 1 hU)
      (moduleCechTwoCover_col_exactAt_one F U V hcol)

/-- The vertical edge of the module-valued two-cover Cech bicomplex is a
quasi-isomorphism in every positive degree when the required pointwise outer
Cech differential pairs are exact on the two adjacent antidiagonals. -/
theorem moduleCechTwoCoverVerticalEdge_quasiIsoAt_succ
    (hU : ⨆ i, U i = ⊤)
    (n : ℕ)
    (hcol_n : ∀ p q, p + q = n → 0 < q →
      ∀ i : Fin (p + 1) → κ,
        (moduleCechShortComplexApp F U (q - 1)
          (∏ᶜ fun k : Fin (p + 1) => V (i k))).Exact)
    (hcol_succ : ∀ p q, p + q = n + 1 → 0 < q →
      ∀ i : Fin (p + 1) → κ,
        (moduleCechShortComplexApp F U (q - 1)
          (∏ᶜ fun k : Fin (p + 1) => V (i k))).Exact) :
    QuasiIsoAt
      ((moduleCechTwoCoverBicomplex F U V).totalUpNatVerticalEdge
        ((cechComplexFunctor V).obj F.obj)
        (moduleCechTwoCoverVerticalAugmentation F U V).f
        (moduleCechTwoCoverVerticalAugmentation_comm F U V)
        (moduleCechTwoCoverVerticalAugmentation_comp_d F U V))
      (n + 1) := by
  letI : Mono
      ((moduleCechTwoCoverVerticalAugmentation F U V).f (n + 1)) :=
    moduleCechTwoCoverVerticalAugmentation_mono F U V (n + 1) hU
  letI : Mono
      ((moduleCechTwoCoverVerticalAugmentation F U V).f (n + 2)) :=
    moduleCechTwoCoverVerticalAugmentation_mono F U V (n + 2) hU
  apply
    HomologicalComplex₂.totalUpNatVerticalEdge_quasiIsoAt_succ_module
      (moduleCechTwoCoverBicomplex F U V)
      ((cechComplexFunctor V).obj F.obj)
      (moduleCechTwoCoverVerticalAugmentation F U V).f
      (moduleCechTwoCoverVerticalAugmentation_comm F U V)
      (moduleCechTwoCoverVerticalAugmentation_comp_d F U V)
      n
      (moduleCechTwoCoverVerticalAugmentedShortComplex_exact
        F U V n hU)
      (moduleCechTwoCoverVerticalAugmentedShortComplex_exact
        F U V (n + 1) hU)
  · intro p q hpq hq
    exact moduleCechTwoCover_col_exactAt F U V p q hq
      (hcol_n p q hpq hq)
  · intro p q hpq hq
    exact moduleCechTwoCover_col_exactAt F U V p q hq
      (hcol_succ p q hpq hq)

end TopCat.Sheaf
