/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechTopExact
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverBicomplex

/-!
# Exact augmented rows of the module-valued two-cover Cech bicomplex

The horizontal augmentation is the top-sections Cech augmentation precomposed
with the top-sections comparison isomorphism. Thus the sheaf condition gives
exactness at the start of every horizontal row while retaining the coefficient
ring action. Exactness in the next Cech degree remains an explicit acyclicity
input.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)

/-- A horizontal row of the two-cover bicomplex, augmented by the native Cech
complex for the outer family. -/
noncomputable def moduleCechTwoCoverHorizontalAugmentedShortComplex
    (q : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (moduleCechTwoCoverHorizontalAugmentation F U V q)
    (((moduleCechTwoCoverBicomplex F U V).X q).d 0 1)
    (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V q)

/-- The augmented horizontal row is the top-sections augmented native Cech
short complex of the corresponding outer Cech term. -/
noncomputable def moduleCechTwoCoverHorizontalAugmentedShortComplexIso
    (q : ℕ) :
    moduleCechTwoCoverHorizontalAugmentedShortComplex F U V q ≅
      moduleCechTopSectionsNativeShortComplex
        (moduleCechTerm F U q) V :=
  ShortComplex.isoMk
    (moduleCechTermTopSectionsIso F U q).symm
    (Iso.refl _)
    (Iso.refl _)
    (by
      change
        (moduleCechTermTopSectionsIso F U q).inv ≫
            moduleCechTopSectionsAugmentation
              (moduleCechTerm F U q) V =
          ((moduleCechTermTopSectionsIso F U q).inv ≫
            moduleCechTopSectionsAugmentation
              (moduleCechTerm F U q) V) ≫ 𝟙 _
      rw [Category.comp_id])
    (by
      simp [moduleCechTwoCoverHorizontalAugmentedShortComplex,
        moduleCechTopSectionsNativeShortComplex])

/-- Every augmented horizontal row is exact when the inner family is an open
cover. -/
theorem moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
    (q : ℕ) (hV : ⨆ i, V i = ⊤) :
    (moduleCechTwoCoverHorizontalAugmentedShortComplex F U V q).Exact := by
  exact ShortComplex.exact_of_iso
    (moduleCechTwoCoverHorizontalAugmentedShortComplexIso F U V q).symm
    (moduleCechTopSectionsNativeShortComplex_exact
      (moduleCechTerm F U q) V hV)

/-- Every horizontal augmentation is monic when the inner family is an open
cover. -/
theorem moduleCechTwoCoverHorizontalAugmentation_mono
    (q : ℕ) (hV : ⨆ i, V i = ⊤) :
    Mono (moduleCechTwoCoverHorizontalAugmentation F U V q) := by
  apply mono_comp'
  · infer_instance
  · exact moduleCechTopSectionsAugmentation_mono
      (moduleCechTerm F U q) V hV

/-- Native degree-one Cech exactness for an outer Cech term is exactly the
degree-one row condition in the two-cover bicomplex. -/
theorem moduleCechTwoCover_row_exactAt_one
    (q : ℕ)
    (h : ((cechComplexFunctor V).obj
      (moduleCechTerm F U q).obj).ExactAt 1) :
    (ShortComplex.mk
      (((moduleCechTwoCoverBicomplex F U V).X q).d 0 1)
      (((moduleCechTwoCoverBicomplex F U V).X q).d 1 2)
      (((moduleCechTwoCoverBicomplex F U V).X q).d_comp_d 0 1 2)).Exact := by
  apply (HomologicalComplex.exactAt_iff'
    ((moduleCechTwoCoverBicomplex F U V).X q)
      0 1 2 (by simp) (by simp)).1
  exact h

end TopCat.Sheaf
