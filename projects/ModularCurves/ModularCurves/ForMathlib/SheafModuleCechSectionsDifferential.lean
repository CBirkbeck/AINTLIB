/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import ModularCurves.ForMathlib.SheafModuleCechTopSections

/-!
# Differentials on sections of module-valued sheaf Cech complexes

The arbitrary-open section comparison for a module-valued sheaf Cech term
identifies its cofaces and differential with the usual tuple-deletion
restrictions.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X)

attribute [local instance] moduleCechSheafPreadditive

/-- The concrete linear equivalence underlying the arbitrary-open section
comparison for a module-valued sheaf Cech term. -/
noncomputable def moduleCechTermSectionsLinearEquiv
    (n : ℕ) (W : Opens X) :
    (moduleCechTerm F U n).obj.obj (op W) ≃ₗ[R]
      ((i : Fin (n + 1) → ι) →
        F.obj.obj
          (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))) :=
  (moduleCechTermSectionsIso F U n W ≪≫
    ModuleCat.piIsoPi _).toLinearEquiv

/-- A tuple component of the concrete section comparison is the
corresponding sheaf-product projection followed by restriction. -/
theorem moduleCechTermSectionsLinearEquiv_apply
    (n : ℕ) (W : Opens X)
    (x : (moduleCechTerm F U n).obj.obj (op W))
    (i : Fin (n + 1) → ι) :
    moduleCechTermSectionsLinearEquiv F U n W x i =
      (moduleCechTermFactorSectionsIso F U n W i).hom
        ((Pi.π (moduleCechTermFactor F U n) i).hom.app (op W) x) := by
  change
    (ModuleCat.piIsoPi _).hom
        ((moduleCechTermSectionsIso F U n W).hom x) i = _
  rw [ModuleCat.piIsoPi_hom_ker_subtype_apply]
  exact ConcreteCategory.congr_hom
    (moduleCechTermSectionsIso_hom_π F U n W i) x

/-- On sections over an arbitrary open, a module-valued sheaf Cech coface
deletes one tuple entry and restricts. -/
theorem moduleCechCoface_apply
    (n : ℕ) (W : Opens X)
    (x : (moduleCechTerm F U n).obj.obj (op W))
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    moduleCechTermSectionsLinearEquiv F U (n + 1) W
        ((moduleCechCoface F U n k).hom.app (op W) x) i =
      F.obj.map (homOfLE (inf_le_inf_left W
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
        (moduleCechTermSectionsLinearEquiv F U n W x
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [moduleCechTermSectionsLinearEquiv_apply,
    moduleCechTermSectionsLinearEquiv_apply]
  let h :
      (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
        ∏ᶜ fun a : Fin (n + 1) =>
          U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
    leOfHom (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i)
  have hcoface :
      moduleCechCoface F U n k ≫
          Pi.π (moduleCechTermFactor F U (n + 1)) i =
        Pi.π (moduleCechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          moduleCechTermFactorRestriction F h := by
    unfold moduleCechCoface moduleCechTerm
    exact Pi.lift_π _ i
  have hcomponent :
      (Pi.π (moduleCechTermFactor F U (n + 1)) i).hom.app (op W)
          ((moduleCechCoface F U n k).hom.app (op W) x) =
        (moduleCechTermFactorRestriction F h).hom.app (op W)
          ((Pi.π (moduleCechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app
              (op W) x) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op W)) hcoface) x
  rw [hcomponent]
  change (F.obj.map _ ≫ F.obj.map _) _ =
    (F.obj.map _ ≫ F.obj.map _) _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _))) _

private theorem moduleSheaf_sum_apply_finset
    {A B : Sheaf (ModuleCat.{u} R) X}
    {κ : Type*} (s : Finset κ) (f : κ → (A ⟶ B))
    (W : (Opens X)ᵒᵖ) (x : A.obj.obj W) :
    (∑ i ∈ s, f i).hom.app W x =
      ∑ i ∈ s, (f i).hom.app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (f a).hom.app W x +
        (∑ i ∈ s, f i).hom.app W x = _
      rw [ih]

private theorem moduleSheaf_sum_apply
    {A B : Sheaf (ModuleCat.{u} R) X}
    {κ : Type*} [Fintype κ] (f : κ → (A ⟶ B))
    (W : (Opens X)ᵒᵖ) (x : A.obj.obj W) :
    (∑ i, f i).hom.app W x = ∑ i, (f i).hom.app W x :=
  moduleSheaf_sum_apply_finset Finset.univ f W x

/-- On sections over an arbitrary open, the module-valued sheaf Cech
differential is the alternating sum of tuple-deletion restrictions. -/
theorem moduleCechDifferential_apply
    (n : ℕ) (W : Opens X)
    (x : (moduleCechTerm F U n).obj.obj (op W))
    (i : Fin (n + 2) → ι) :
    moduleCechTermSectionsLinearEquiv F U (n + 1) W
        ((moduleCechDifferential F U n).hom.app (op W) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (homOfLE (inf_le_inf_left W
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
          (moduleCechTermSectionsLinearEquiv F U n W x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [moduleCechDifferential]
  calc
    _ = moduleCechTermSectionsLinearEquiv F U (n + 1) W
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) •
            moduleCechCoface F U n k).hom.app (op W) x) i :=
      congrArg
        (fun y => moduleCechTermSectionsLinearEquiv
          F U (n + 1) W y i)
        (moduleSheaf_sum_apply _ (op W) x)
    _ = (∑ k : Fin (n + 2),
        moduleCechTermSectionsLinearEquiv F U (n + 1) W
          (((-1 : ℤ) ^ (k : ℕ) •
            moduleCechCoface F U n k).hom.app (op W) x)) i := by
      rw [map_sum]
    _ = ∑ k : Fin (n + 2),
        moduleCechTermSectionsLinearEquiv F U (n + 1) W
          (((-1 : ℤ) ^ (k : ℕ) •
            moduleCechCoface F U n k).hom.app (op W) x) i :=
      Finset.sum_apply i Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      change moduleCechTermSectionsLinearEquiv F U (n + 1) W
          ((-1 : ℤ) ^ (k : ℕ) •
            ((moduleCechCoface F U n k).hom.app (op W) x)) i = _
      rw [map_zsmul, Pi.smul_apply, moduleCechCoface_apply]
      exact congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
        (ConcreteCategory.congr_hom
          (congrArg F.obj.map (Subsingleton.elim _ _))
          (moduleCechTermSectionsLinearEquiv F U n W x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)))

end TopCat.Sheaf
