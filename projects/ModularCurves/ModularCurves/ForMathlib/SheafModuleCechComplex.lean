/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic
import ModularCurves.ForMathlib.TopCatSheafRestrict

/-!
# Sheaf-level Cech complexes with module coefficients

This file specializes the sheaf-level Cech construction to sheaves valued in
modules over a fixed ring. The resulting complex retains the coefficient-ring
action needed by the two-cover comparison.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X) (n : ℕ)

noncomputable local instance moduleCechSheafPreadditive :
    Preadditive (Sheaf (ModuleCat.{u} R) X) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology X) (ModuleCat.{u} R)))

/-- The restriction-pushforward factor in a module-valued sheaf Cech term. -/
noncomputable abbrev moduleCechTermFactor
    (i : Fin (n + 1) → ι) :
    Sheaf (ModuleCat.{u} R) X :=
  (restrict (ModuleCat R)
      (∏ᶜ fun k : Fin (n + 1) => U (i k)).isOpenEmbedding ⋙
    pushforward (ModuleCat R)
      (∏ᶜ fun k : Fin (n + 1) => U (i k)).inclusion').obj F

/-- Degree `n` of the module-valued sheaf Cech complex. -/
noncomputable def moduleCechTerm : Sheaf (ModuleCat.{u} R) X :=
  ∏ᶜ moduleCechTermFactor F U n

private theorem moduleCechTermFactorRestrictionLE
    {A B : Opens X} (h : A ≤ B) (V : Opens X) :
    A.isOpenEmbedding.functor.obj ((Opens.map A.inclusion').obj V) ≤
      B.isOpenEmbedding.functor.obj ((Opens.map B.inclusion').obj V) := by
  simpa only [Opens.functor_map_eq_inf] using inf_le_inf_left V h

/-- Restriction from the factor for `B` to the factor for a smaller open `A`. -/
noncomputable def moduleCechTermFactorRestriction
    {A B : Opens X} (h : A ≤ B) :
    (restrict (ModuleCat R) B.isOpenEmbedding ⋙
        pushforward (ModuleCat R) B.inclusion').obj F ⟶
      (restrict (ModuleCat R) A.isOpenEmbedding ⋙
        pushforward (ModuleCat R) A.inclusion').obj F :=
  ObjectProperty.homMk
    { app := fun V =>
        F.obj.map
          (homOfLE (moduleCechTermFactorRestrictionLE h V.unop)).op
      naturality := by
        intro V W f
        change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        rfl }

private theorem moduleCechTupleLE
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i)

/-- The module-valued sheaf Cech coface deleting the `k`th tuple entry. -/
noncomputable def moduleCechCoface (k : Fin (n + 2)) :
    moduleCechTerm F U n ⟶ moduleCechTerm F U (n + 1) :=
  Pi.lift (fun i : Fin (n + 2) → ι =>
    Pi.π (moduleCechTermFactor F U n)
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      moduleCechTermFactorRestriction F
        (moduleCechTupleLE U n k i))

/-- The alternating differential on module-valued sheaf Cech terms. -/
noncomputable def moduleCechDifferential :
    moduleCechTerm F U n ⟶ moduleCechTerm F U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    moduleCechCoface F U n k

/-- The presheaf assigning to an open the pushforward of the restriction of
`F` to that open. -/
noncomputable def moduleCechFactorPresheaf :
    (Opens X)ᵒᵖ ⥤ Sheaf (ModuleCat.{u} R) X where
  obj A :=
    (restrict (ModuleCat R) A.unop.isOpenEmbedding ⋙
      pushforward (ModuleCat R) A.unop.inclusion').obj F
  map f := moduleCechTermFactorRestriction F (leOfHom f.unop)
  map_id A := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ = 𝟙 _
    rw [← F.obj.map_id]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ = F.obj.map _ ≫ F.obj.map _
    rw [← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The sheaf-level Cech complex retaining its `R`-module coefficients. -/
noncomputable def moduleCechComplex :
    CochainComplex (Sheaf (ModuleCat.{u} R) X) ℕ :=
  (cechComplexFunctor U).obj (moduleCechFactorPresheaf F)

@[simp]
theorem moduleCechComplex_X (n : ℕ) :
    (moduleCechComplex F U).X n = moduleCechTerm F U n :=
  rfl

private theorem nativeCoface_eq_moduleCechCoface
    (n : ℕ) (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj
        (moduleCechFactorPresheaf F)).δ k =
      moduleCechCoface F U n k := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  rfl

/-- The native differential is the alternating sum of module-valued cofaces. -/
theorem moduleCechComplex_d (n : ℕ) :
    (moduleCechComplex F U).d n (n + 1) =
      moduleCechDifferential F U n := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj
      (moduleCechFactorPresheaf F)).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  refine (CochainComplex.of_d _ _ n).trans ?_
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    moduleCechDifferential]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (nativeCoface_eq_moduleCechCoface F U n k)

/-- Consecutive module-valued sheaf Cech differentials compose to zero. -/
theorem moduleCechDifferential_comp (n : ℕ) :
    moduleCechDifferential F U n ≫
        moduleCechDifferential F U (n + 1) = 0 := by
  rw [← moduleCechComplex_d F U n,
    ← moduleCechComplex_d F U (n + 1)]
  exact (moduleCechComplex F U).d_comp_d n (n + 1) (n + 2)

end TopCat.Sheaf
