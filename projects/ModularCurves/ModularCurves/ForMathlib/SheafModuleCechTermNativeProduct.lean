/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import ModularCurves.ForMathlib.SheafModuleCechNativeDegreeExact
import ModularCurves.ForMathlib.SheafModuleCechSectionsDifferential

/-!
# Native Cech complexes of module-valued sheaf Cech terms

Every degree of the native Cech complex of a module-valued sheaf Cech term
is the product of the corresponding degrees for its
restriction-pushforward factors. Consequently, degree-one exactness for all
factors implies degree-one exactness for the product term.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)

/-- Projection from a degree of the native Cech complex of a sheaf Cech
term to the corresponding degree for each restriction-pushforward factor. -/
noncomputable def moduleCechTermNativeProjectionLinearMap
    (q p : ℕ) :
    ((cechComplexFunctor V).obj (moduleCechTerm F U q).obj).X p →ₗ[R]
      ((i : Fin (q + 1) → ι) →
        ((cechComplexFunctor V).obj
          (moduleCechTermFactor F U q i).obj).X p) :=
  LinearMap.pi fun i =>
    (((cechComplexFunctor V).map
      (Pi.π (moduleCechTermFactor F U q) i).hom).f p).hom

theorem moduleCechTermNativeProjectionLinearMap_apply
    (q p : ℕ)
    (x : ((cechComplexFunctor V).obj
      (moduleCechTerm F U q).obj).X p)
    (i : Fin (q + 1) → ι) :
    moduleCechTermNativeProjectionLinearMap F U V q p x i =
      ((cechComplexFunctor V).map
        (Pi.π (moduleCechTermFactor F U q) i).hom).f p x :=
  rfl

theorem moduleCechTermNativeProjectionLinearMap_injective
    (q p : ℕ) :
    Function.Injective
      (moduleCechTermNativeProjectionLinearMap F U V q p) := by
  intro x y hxy
  apply (moduleNativeCechDegreeLinearEquiv
    (moduleCechTerm F U q).obj V p).injective
  funext j
  apply (moduleCechTermSectionsLinearEquiv F U q
    (∏ᶜ fun k : Fin (p + 1) => V (j k))).injective
  funext i
  rw [moduleCechTermSectionsLinearEquiv_apply,
    moduleCechTermSectionsLinearEquiv_apply]
  have hij := congrFun hxy i
  have hj := congrArg
    (fun z => moduleNativeCechDegreeLinearEquiv
      (moduleCechTermFactor F U q i).obj V p z j) hij
  calc
    _ = (moduleCechTermFactorSectionsIso F U q
          (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom
        (moduleNativeCechDegreeLinearEquiv
          (moduleCechTermFactor F U q i).obj V p
          (((cechComplexFunctor V).map
            (Pi.π (moduleCechTermFactor F U q) i).hom).f p x) j) :=
      congrArg
        (fun s => (moduleCechTermFactorSectionsIso F U q
          (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom s)
        (moduleNativeCechDegreeLinearEquiv_map
          (Pi.π (moduleCechTermFactor F U q) i).hom V p x j).symm
    _ = (moduleCechTermFactorSectionsIso F U q
          (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom
        (moduleNativeCechDegreeLinearEquiv
          (moduleCechTermFactor F U q i).obj V p
          (((cechComplexFunctor V).map
            (Pi.π (moduleCechTermFactor F U q) i).hom).f p y) j) :=
      congrArg
        (fun s => (moduleCechTermFactorSectionsIso F U q
          (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom s) hj
    _ = _ :=
      congrArg
        (fun s => (moduleCechTermFactorSectionsIso F U q
          (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom s)
        (moduleNativeCechDegreeLinearEquiv_map
          (Pi.π (moduleCechTermFactor F U q) i).hom V p y j)

theorem moduleCechTermNativeProjectionLinearMap_surjective
    (q p : ℕ) :
    Function.Surjective
      (moduleCechTermNativeProjectionLinearMap F U V q p) := by
  intro z
  let localSection (j : Fin (p + 1) → κ) :
      (moduleCechTerm F U q).obj.obj
        (op (∏ᶜ fun k : Fin (p + 1) => V (j k))) :=
    (moduleCechTermSectionsLinearEquiv F U q
      (∏ᶜ fun k : Fin (p + 1) => V (j k))).symm
        (fun i =>
          (moduleCechTermFactorSectionsIso F U q
            (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom
              (moduleNativeCechDegreeLinearEquiv
                (moduleCechTermFactor F U q i).obj V p (z i) j))
  let x :=
    (moduleNativeCechDegreeLinearEquiv
      (moduleCechTerm F U q).obj V p).symm localSection
  refine ⟨x, ?_⟩
  funext i
  apply (moduleNativeCechDegreeLinearEquiv
    (moduleCechTermFactor F U q i).obj V p).injective
  funext j
  rw [moduleCechTermNativeProjectionLinearMap_apply]
  calc
    _ = (Pi.π (moduleCechTermFactor F U q) i).hom.app
          (op (∏ᶜ fun k : Fin (p + 1) => V (j k)))
        ((moduleNativeCechDegreeLinearEquiv
          (moduleCechTerm F U q).obj V p x) j) :=
      moduleNativeCechDegreeLinearEquiv_map
        (Pi.π (moduleCechTermFactor F U q) i).hom V p x j
    _ = _ := by
      apply (ModuleCat.mono_iff_injective
        (moduleCechTermFactorSectionsIso F U q
          (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom).mp inferInstance
      rw [← moduleCechTermSectionsLinearEquiv_apply]
      change
        moduleCechTermSectionsLinearEquiv F U q
            (∏ᶜ fun k : Fin (p + 1) => V (j k))
            ((moduleNativeCechDegreeLinearEquiv
              (moduleCechTerm F U q).obj V p x) j) i =
            (moduleCechTermFactorSectionsIso F U q
            (∏ᶜ fun k : Fin (p + 1) => V (j k)) i).hom
            (moduleNativeCechDegreeLinearEquiv
              (moduleCechTermFactor F U q i).obj V p (z i) j)
      dsimp only [x]
      rw [(moduleNativeCechDegreeLinearEquiv
        (moduleCechTerm F U q).obj V p).apply_symm_apply]
      rw [(moduleCechTermSectionsLinearEquiv F U q
        (∏ᶜ fun k : Fin (p + 1) => V (j k))).apply_symm_apply]

/-- The projection to the native Cech complexes of the
restriction-pushforward factors is a linear equivalence in every degree. -/
noncomputable def moduleCechTermNativeProjectionLinearEquiv
    (q p : ℕ) :
    ((cechComplexFunctor V).obj (moduleCechTerm F U q).obj).X p ≃ₗ[R]
      ((i : Fin (q + 1) → ι) →
        ((cechComplexFunctor V).obj
          (moduleCechTermFactor F U q i).obj).X p) :=
  LinearEquiv.ofBijective
    (moduleCechTermNativeProjectionLinearMap F U V q p)
    ⟨moduleCechTermNativeProjectionLinearMap_injective F U V q p,
      moduleCechTermNativeProjectionLinearMap_surjective F U V q p⟩

@[simp]
theorem moduleCechTermNativeProjectionLinearEquiv_apply
    (q p : ℕ)
    (x : ((cechComplexFunctor V).obj
      (moduleCechTerm F U q).obj).X p) :
    moduleCechTermNativeProjectionLinearEquiv F U V q p x =
      moduleCechTermNativeProjectionLinearMap F U V q p x :=
  rfl

/-- Positive-degree exactness for the native Cech complex of every
restriction-pushforward factor implies exactness in the same degree for their
sheaf product. -/
theorem moduleCechTerm_cech_exactAt_succ_of_factors
    (q n : ℕ)
    (h : ∀ i : Fin (q + 1) → ι,
      ((cechComplexFunctor V).obj
        (moduleCechTermFactor F U q i).obj).ExactAt (n + 1)) :
    ((cechComplexFunctor V).obj
      (moduleCechTerm F U q).obj).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff'
      _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro y hy
  change
    (((cechComplexFunctor V).obj
      (moduleCechTerm F U q).obj).d (n + 1) (n + 2)).hom y = 0 at hy
  have hpreimage : ∀ i : Fin (q + 1) → ι,
      ∃ x : ((cechComplexFunctor V).obj
          (moduleCechTermFactor F U q i).obj).X n,
        (((cechComplexFunctor V).obj
          (moduleCechTermFactor F U q i).obj).d n (n + 1)).hom x =
          moduleCechTermNativeProjectionLinearMap
            F U V q (n + 1) y i := by
    intro i
    have hi := h i
    rw [HomologicalComplex.exactAt_iff'
        _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hi
    apply hi
    calc
      _ = (((cechComplexFunctor V).map
            (Pi.π (moduleCechTermFactor F U q) i).hom).f
              (n + 2)).hom
          ((((cechComplexFunctor V).obj
            (moduleCechTerm F U q).obj).d
              (n + 1) (n + 2)).hom y) := by
        exact ConcreteCategory.congr_hom
          (((cechComplexFunctor V).map
            (Pi.π (moduleCechTermFactor F U q) i).hom).comm
              (n + 1) (n + 2)) y
      _ = (((cechComplexFunctor V).map
            (Pi.π (moduleCechTermFactor F U q) i).hom).f
              (n + 2)).hom 0 :=
        congrArg _ hy
      _ = 0 := map_zero _
  choose x hx using hpreimage
  let x' := (moduleCechTermNativeProjectionLinearEquiv
    F U V q n).symm x
  refine ⟨x', ?_⟩
  apply (moduleCechTermNativeProjectionLinearEquiv
    F U V q (n + 1)).injective
  funext i
  change
    moduleCechTermNativeProjectionLinearMap F U V q (n + 1)
        ((((cechComplexFunctor V).obj
          (moduleCechTerm F U q).obj).d n (n + 1)).hom x') i =
      moduleCechTermNativeProjectionLinearMap F U V q (n + 1) y i
  have hcoord := congrFun
    ((moduleCechTermNativeProjectionLinearEquiv
      F U V q n).apply_symm_apply x) i
  rw [moduleCechTermNativeProjectionLinearEquiv_apply] at hcoord
  calc
    _ = (((cechComplexFunctor V).obj
          (moduleCechTermFactor F U q i).obj).d n (n + 1)).hom
        (moduleCechTermNativeProjectionLinearMap F U V q n x' i) := by
      exact ConcreteCategory.congr_hom
        (((cechComplexFunctor V).map
          (Pi.π (moduleCechTermFactor F U q) i).hom).comm
            n (n + 1)).symm x'
    _ = (((cechComplexFunctor V).obj
          (moduleCechTermFactor F U q i).obj).d n (n + 1)).hom (x i) :=
      congrArg _ hcoord
    _ = _ := hx i

/-- Degree-one exactness for the native Cech complex of every
restriction-pushforward factor implies degree-one exactness for their sheaf
product. -/
theorem moduleCechTerm_cech_exactAt_one_of_factors
    (q : ℕ)
    (h : ∀ i : Fin (q + 1) → ι,
      ((cechComplexFunctor V).obj
        (moduleCechTermFactor F U q i).obj).ExactAt 1) :
    ((cechComplexFunctor V).obj
      (moduleCechTerm F U q).obj).ExactAt 1 := by
  simpa using moduleCechTerm_cech_exactAt_succ_of_factors
    F U V q 0 h

end TopCat.Sheaf
