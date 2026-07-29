/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechTermNativeProduct
import ModularCurves.ForMathlib.SchemeModuleCechRestrict

/-!
# Native Cech complexes of restriction-pushforward factors

The native Cech complex of one restriction-pushforward factor is naturally
isomorphic to the original module-valued sheaf Cech complex evaluated on
the indexing open of that factor.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)

/-- Sections of one restriction-pushforward factor on a tuple intersection
are sections of the original sheaf on the intersection with its indexing
open. -/
noncomputable def moduleCechFixedFactorSectionsIso
    (q : ℕ) (i : Fin (q + 1) → ι) (A : Opens X) :
    (moduleCechTermFactor F U q i).obj.obj (op (⊤ ⊓ A)) ≅
      F.obj.obj
        (op ((∏ᶜ fun k : Fin (q + 1) => U (i k)) ⊓ A)) :=
  moduleCechTermFactorSectionsIso F U q (⊤ ⊓ A) i ≪≫
    F.obj.mapIso (eqToIso (congrArg op (by
      simp only [top_inf_eq]
      rw [inf_comm])))

/-- The fixed-factor section comparison commutes with restriction between
tuple intersections. -/
theorem moduleCechFixedFactorSectionsIso_naturality
    (q : ℕ) (i : Fin (q + 1) → ι)
    {A B : Opens X} (h : A ≤ B) :
    (moduleCechTermFactor F U q i).obj.map
          (homOfLE (inf_le_inf_left ⊤ h)).op ≫
        (moduleCechFixedFactorSectionsIso F U q i A).hom =
      (moduleCechFixedFactorSectionsIso F U q i B).hom ≫
        F.obj.map (homOfLE (inf_le_inf_left
          (∏ᶜ fun k : Fin (q + 1) => U (i k)) h)).op := by
  change (F.obj.map _ ≫ F.obj.map _) ≫ F.obj.map _ =
    (F.obj.map _ ≫ F.obj.map _) ≫ F.obj.map _
  simp only [← F.obj.map_comp, Category.assoc]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

private noncomputable def moduleCechFixedFactorSourceLinearEquiv
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ) :
    (moduleCechSectionsComplex
      (moduleCechTermFactor F U q i) V ⊤).X p ≃ₗ[R]
      ((j : Fin (p + 1) → κ) →
        (moduleCechTermFactor F U q i).obj.obj
          (op (⊤ ⊓ ∏ᶜ fun k : Fin (p + 1) => V (j k)))) :=
  moduleCechTermSectionsLinearEquiv
    (moduleCechTermFactor F U q i) V p ⊤

private noncomputable def moduleCechFixedFactorCoordinateLinearEquiv
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ) :
    ((j : Fin (p + 1) → κ) →
        (moduleCechTermFactor F U q i).obj.obj
          (op (⊤ ⊓ ∏ᶜ fun k : Fin (p + 1) => V (j k)))) ≃ₗ[R]
      ((j : Fin (p + 1) → κ) →
        F.obj.obj (op ((∏ᶜ fun k : Fin (q + 1) => U (i k)) ⊓
          ∏ᶜ fun k : Fin (p + 1) => V (j k)))) :=
  LinearEquiv.piCongrRight fun j =>
    (moduleCechFixedFactorSectionsIso F U q i
      (∏ᶜ fun k : Fin (p + 1) => V (j k))).toLinearEquiv

private noncomputable def moduleCechFixedFactorTargetLinearEquiv
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ) :
    ((j : Fin (p + 1) → κ) →
        F.obj.obj (op ((∏ᶜ fun k : Fin (q + 1) => U (i k)) ⊓
          ∏ᶜ fun k : Fin (p + 1) => V (j k)))) ≃ₗ[R]
      (moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k))).X p :=
  (moduleCechTermSectionsLinearEquiv F V p
    (∏ᶜ fun k : Fin (q + 1) => U (i k))).symm

/-- The degreewise linear comparison from the evaluated Cech complex of a
fixed restriction-pushforward factor to the original sheaf evaluated on the
factor's indexing open. -/
noncomputable def moduleCechFixedFactorSectionsLinearEquiv
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ) :
    (moduleCechSectionsComplex
      (moduleCechTermFactor F U q i) V ⊤).X p ≃ₗ[R]
      (moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k))).X p :=
  ((moduleCechFixedFactorSourceLinearEquiv F U V q i p).trans
    (moduleCechFixedFactorCoordinateLinearEquiv F U V q i p)).trans
      (moduleCechFixedFactorTargetLinearEquiv F U V q i p)

/-- Coordinate formula for the fixed-factor degreewise comparison. -/
theorem moduleCechFixedFactorSectionsLinearEquiv_apply
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ)
    (x : (moduleCechSectionsComplex
      (moduleCechTermFactor F U q i) V ⊤).X p)
    (j : Fin (p + 1) → κ) :
    moduleCechTermSectionsLinearEquiv F V p
        (∏ᶜ fun k : Fin (q + 1) => U (i k))
        (moduleCechFixedFactorSectionsLinearEquiv F U V q i p x) j =
      (moduleCechFixedFactorSectionsIso F U q i
        (∏ᶜ fun k : Fin (p + 1) => V (j k))).hom
        (moduleCechTermSectionsLinearEquiv
          (moduleCechTermFactor F U q i) V p ⊤ x j) := by
  change
    moduleCechTermSectionsLinearEquiv F V p
        (∏ᶜ fun k : Fin (q + 1) => U (i k))
        ((moduleCechTermSectionsLinearEquiv F V p
          (∏ᶜ fun k : Fin (q + 1) => U (i k))).symm
          ((moduleCechFixedFactorCoordinateLinearEquiv
            F U V q i p)
            (moduleCechFixedFactorSourceLinearEquiv
              F U V q i p x))) j = _
  rw [(moduleCechTermSectionsLinearEquiv F V p
    (∏ᶜ fun k : Fin (q + 1) => U (i k))).apply_symm_apply]
  rfl

noncomputable def moduleCechFixedFactorSectionsComplexComponentIso
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ) :
    (moduleCechSectionsComplex
      (moduleCechTermFactor F U q i) V ⊤).X p ≅
      (moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k))).X p :=
  (moduleCechFixedFactorSectionsLinearEquiv F U V q i p).toModuleIso

/-- The fixed-factor degreewise comparison commutes with the Cech
differential. -/
theorem moduleCechFixedFactorSectionsLinearEquiv_d
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ)
    (x : (moduleCechSectionsComplex
      (moduleCechTermFactor F U q i) V ⊤).X p) :
    moduleCechFixedFactorSectionsLinearEquiv F U V q i (p + 1)
        (((moduleCechSectionsComplex
          (moduleCechTermFactor F U q i) V ⊤).d p (p + 1)).hom x) =
      ((moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k))).d p (p + 1)).hom
        (moduleCechFixedFactorSectionsLinearEquiv F U V q i p x) := by
  apply (moduleCechTermSectionsLinearEquiv F V (p + 1)
    (∏ᶜ fun k : Fin (q + 1) => U (i k))).injective
  funext j
  rw [moduleCechFixedFactorSectionsLinearEquiv_apply,
    moduleCechSectionsComplex_d, moduleCechSectionsComplex_d]
  have hsource :=
    moduleCechDifferential_apply
      (moduleCechTermFactor F U q i) V p ⊤ x j
  have htarget :=
    moduleCechDifferential_apply F V p
      (∏ᶜ fun k : Fin (q + 1) => U (i k))
      (moduleCechFixedFactorSectionsLinearEquiv F U V q i p x) j
  let sourceTerm (k : Fin (p + 2)) :=
    (-1 : ℤ) ^ (k : ℕ) •
      (moduleCechTermFactor F U q i).obj.map
        (homOfLE (inf_le_inf_left ⊤
          (leOfHom (((FormalCoproduct.mk _ V).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ j)))).op
        (moduleCechTermSectionsLinearEquiv
          (moduleCechTermFactor F U q i) V p ⊤ x
            (j ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  let targetTerm (k : Fin (p + 2)) :=
    (-1 : ℤ) ^ (k : ℕ) •
      F.obj.map (homOfLE (inf_le_inf_left
        (∏ᶜ fun a : Fin (q + 1) => U (i a))
        (leOfHom (((FormalCoproduct.mk _ V).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ j)))).op
        (moduleCechTermSectionsLinearEquiv F V p
          (∏ᶜ fun a : Fin (q + 1) => U (i a))
          (moduleCechFixedFactorSectionsLinearEquiv F U V q i p x)
          (j ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  let sourceSum := ∑ k : Fin (p + 2), sourceTerm k
  let targetSum := ∑ k : Fin (p + 2), targetTerm k
  change _ = sourceSum at hsource
  change _ = targetSum at htarget
  have hmiddle :
      (moduleCechFixedFactorSectionsIso F U q i
        (∏ᶜ fun k : Fin (p + 2) => V (j k))).hom sourceSum =
        targetSum := by
      dsimp only [sourceSum, targetSum]
      calc
        _ = ∑ k : Fin (p + 2),
            (moduleCechFixedFactorSectionsIso F U q i
              (∏ᶜ fun a : Fin (p + 2) => V (j a))).hom.hom
                (sourceTerm k) :=
          map_sum
            (moduleCechFixedFactorSectionsIso F U q i
              (∏ᶜ fun a : Fin (p + 2) => V (j a))).hom.hom
            sourceTerm Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp only [sourceTerm, targetTerm]
          calc
            _ = (-1 : ℤ) ^ (k : ℕ) •
                (moduleCechFixedFactorSectionsIso F U q i
                  (∏ᶜ fun a : Fin (p + 2) => V (j a))).hom.hom
                  ((moduleCechTermFactor F U q i).obj.map
                    (homOfLE (inf_le_inf_left ⊤
                      (leOfHom (((FormalCoproduct.mk _ V).mapPower
                        (SimplexCategory.δ k).toOrderHom.toFun).φ j)))).op
                    (moduleCechTermSectionsLinearEquiv
                      (moduleCechTermFactor F U q i) V p ⊤ x
                        (j ∘ (SimplexCategory.δ k).toOrderHom.toFun))) :=
              map_zsmul
                (moduleCechFixedFactorSectionsIso F U q i
                  (∏ᶜ fun a : Fin (p + 2) => V (j a))).hom.hom
                ((-1 : ℤ) ^ (k : ℕ)) _
            _ = _ := by
              apply congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
              rw [moduleCechFixedFactorSectionsLinearEquiv_apply]
              exact ConcreteCategory.congr_hom
                (moduleCechFixedFactorSectionsIso_naturality F U q i
                  (leOfHom (((FormalCoproduct.mk _ V).mapPower
                    (SimplexCategory.δ k).toOrderHom.toFun).φ j)))
                (moduleCechTermSectionsLinearEquiv
                  (moduleCechTermFactor F U q i) V p ⊤ x
                    (j ∘
                      (SimplexCategory.δ k).toOrderHom.toFun))
  have hleft := congrArg
    (fun y => (moduleCechFixedFactorSectionsIso F U q i
      (∏ᶜ fun k : Fin (p + 2) => V (j k))).hom y)
    hsource
  exact hleft.trans (hmiddle.trans htarget.symm)

/-- Evaluating the Cech complex of one restriction-pushforward factor on
the top open gives the original sheaf Cech complex evaluated on the
factor's indexing open. -/
noncomputable def moduleCechFixedFactorSectionsComplexIso
    (q : ℕ) (i : Fin (q + 1) → ι) :
    moduleCechSectionsComplex
        (moduleCechTermFactor F U q i) V ⊤ ≅
      moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k)) :=
  HomologicalComplex.Hom.isoOfComponents
    (moduleCechFixedFactorSectionsComplexComponentIso F U V q i) (by
      intro p p' hp
      simp only [ComplexShape.up_Rel] at hp
      subst p'
      apply ModuleCat.hom_ext
      ext x
      exact (moduleCechFixedFactorSectionsLinearEquiv_d
        F U V q i p x).symm)

/-- The native Cech complex of a fixed restriction-pushforward factor is
the original sheaf Cech complex evaluated on the factor's indexing open. -/
noncomputable def moduleCechFixedFactorNativeSectionsComplexIso
    (q : ℕ) (i : Fin (q + 1) → ι) :
    ((cechComplexFunctor V).obj
        (moduleCechTermFactor F U q i).obj) ≅
      moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k)) :=
  (moduleCechTopSectionsComplexIso
      (moduleCechTermFactor F U q i) V).symm ≪≫
    moduleCechFixedFactorSectionsComplexIso F U V q i

/-- Exactness for a fixed factor is equivalent to exactness of the original
sheaf Cech complex evaluated on its indexing open, in every degree. -/
theorem moduleCechFixedFactorNative_exactAt_iff
    (q : ℕ) (i : Fin (q + 1) → ι) (p : ℕ) :
    ((cechComplexFunctor V).obj
        (moduleCechTermFactor F U q i).obj).ExactAt p ↔
      (moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k))).ExactAt p := by
  constructor
  · intro h
    exact h.of_iso
      (moduleCechFixedFactorNativeSectionsComplexIso F U V q i)
  · intro h
    exact h.of_iso
      (moduleCechFixedFactorNativeSectionsComplexIso F U V q i).symm

/-- Degree-one exactness for a fixed factor is equivalent to degree-one
exactness of the original sheaf Cech complex evaluated on its indexing
open. -/
theorem moduleCechFixedFactorNative_exactAt_one_iff
    (q : ℕ) (i : Fin (q + 1) → ι) :
    ((cechComplexFunctor V).obj
        (moduleCechTermFactor F U q i).obj).ExactAt 1 ↔
      (moduleCechSectionsComplex F V
        (∏ᶜ fun k : Fin (q + 1) => U (i k))).ExactAt 1 :=
  moduleCechFixedFactorNative_exactAt_iff F U V q i 1

/-- Exactness of an evaluated Cech short complex on a factor's indexing open
implies native exactness in the corresponding positive degree for that
factor. -/
theorem moduleCechFixedFactorNative_exactAt_succ_of_app_exact
    (q : ℕ) (i : Fin (q + 1) → ι) (n : ℕ)
    (h : (moduleCechShortComplexApp F V n
      (∏ᶜ fun k : Fin (q + 1) => U (i k))).Exact) :
    ((cechComplexFunctor V).obj
      (moduleCechTermFactor F U q i).obj).ExactAt (n + 1) := by
  apply (moduleCechFixedFactorNative_exactAt_iff
    F U V q i (n + 1)).2
  exact (moduleCechShortComplexApp_exact_iff_sectionsComplex_exactAt
    F V (∏ᶜ fun k : Fin (q + 1) => U (i k)) n).1 h

/-- Exactness of the evaluated Cech short complex on a factor's indexing
open implies native degree-one exactness for that factor. -/
theorem moduleCechFixedFactorNative_exactAt_one_of_app_exact
    (q : ℕ) (i : Fin (q + 1) → ι)
    (h : (moduleCechShortComplexApp F V 0
      (∏ᶜ fun k : Fin (q + 1) => U (i k))).Exact) :
    ((cechComplexFunctor V).obj
      (moduleCechTermFactor F U q i).obj).ExactAt 1 :=
  moduleCechFixedFactorNative_exactAt_succ_of_app_exact
    F U V q i 0 h

end TopCat.Sheaf
