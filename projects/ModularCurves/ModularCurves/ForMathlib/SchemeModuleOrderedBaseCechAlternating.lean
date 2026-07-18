/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechComparison

/-!
# Alternating extension of ordered Cech cochains

This file constructs the alternating degreewise section from the bounded Cech complex indexed by
strictly increasing tuples to the native Cech complex indexed by all tuples. Restricting the
alternating extension back to increasing tuples is the identity.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Reindex native Cech cochains by a permutation of tuple positions. -/
noncomputable def baseCechPermutationF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (baseCechComplex π M U).X n ⟶ (baseCechComplex π M U).X n :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M)).map
        ((FormalCoproduct.mk _ U).mapPower σ).op

theorem baseCechPermutationF_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1) → ι) :
    baseCechPermutationF π M U n σ ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) (i ∘ σ) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower σ).φ i).op := by
  change (Pi.lift fun j : Fin (n + 1) → ι =>
      Pi.π (fun k : Fin (n + 1) → ι => baseCechFactor π M U n k) (j ∘ σ) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower σ).φ j).op) ≫ _ = _
  exact Pi.lift_π _ i

theorem baseCechXIsoPi_hom_comp_proj
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechXIsoPi π M U n).hom ≫
        ModuleCat.ofHom
          (LinearMap.proj i :
            (∀ j : Fin (n + 1) → ι, baseCechFactor π M U n j) →ₗ[
              Γ(S, (⊤ : S.Opens))] baseCechFactor π M U n i) =
      Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i := by
  exact ModuleCat.piIsoPi_hom_ker_subtype _ i

theorem orderedBaseCechZeroExtendLinearMap_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : orderedBaseCechTerm π M U n) (i : Fin (n + 1) → ι) :
    orderedBaseCechZeroExtendLinearMap π M U n x i =
      if h : StrictMono i then x ⟨i, h⟩ else 0 := by
  rfl

theorem orderedToBaseCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ ≠ 1) :
    orderedToBaseCechZeroExtensionF π M U n ≫
        baseCechPermutationF π M U n σ ≫
          baseCechToOrderedF π M U n = 0 := by
  apply (cancel_epi (orderedBaseCechObjectIsoPi π M U n).inv).1
  apply (cancel_mono (orderedBaseCechObjectIsoPi π M U n).hom).1
  rw [comp_zero, zero_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi : ¬ StrictMono (i.1 ∘ σ) := by
    intro h
    have hmono : Monotone σ := fun a b hab =>
      i.2.le_iff_le.mp (h.monotone hab)
    exact hσ ((Equiv.Perm.monotone_iff σ).mp hmono)
  have hcomp :
      (orderedBaseCechObjectIsoPi π M U n).inv ≫
        orderedToBaseCechZeroExtensionF π M U n ≫
            baseCechPermutationF π M U n σ ≫
              baseCechToOrderedF π M U n ≫
                (orderedBaseCechObjectIsoPi π M U n).hom ≫
                  ModuleCat.ofHom (LinearMap.proj i) = 0 := by
    rw [orderedBaseCechObjectIsoPi_hom_comp_proj π M U n i,
      baseCechToOrderedF_comp_π π M U n i,
      baseCechPermutationF_comp_π π M U n σ i.1]
    let e := Pi.π (fun j : Fin (n + 1) → ι =>
      baseCechFactor π M U n j) (i.1 ∘ σ)
    let r : baseCechFactor π M U n (i.1 ∘ σ) ⟶
        baseCechFactor π M U n i.1 :=
      (baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower σ).φ i.1).op
    change (orderedBaseCechObjectIsoPi π M U n).inv ≫
      orderedToBaseCechZeroExtensionF π M U n ≫ e ≫ r = 0
    rw [orderedToBaseCechZeroExtensionF]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hprefix :
        ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n) ≫
            (baseCechXIsoPi π M U n).inv ≫ e = 0 := by
      dsimp only [e]
      rw [baseCechXIsoPi_inv_comp_proj π M U n (i.1 ∘ σ)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change orderedBaseCechZeroExtendLinearMap π M U n y (i.1 ∘ σ) = 0
      rw [orderedBaseCechZeroExtendLinearMap_apply, dif_neg hi]
    let a := ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n)
    calc
      a ≫ ((baseCechXIsoPi π M U n).inv ≫ (e ≫ r)) =
          a ≫ (((baseCechXIsoPi π M U n).inv ≫ e) ≫ r) :=
        congrArg (fun q => a ≫ q)
          (Category.assoc (baseCechXIsoPi π M U n).inv e r).symm
      _ = (a ≫ ((baseCechXIsoPi π M U n).inv ≫ e)) ≫ r :=
        (Category.assoc a ((baseCechXIsoPi π M U n).inv ≫ e) r).symm
      _ = 0 := by rw [hprefix, zero_comp]
  have hx := ConcreteCategory.congr_hom hcomp x
  exact hx

/-- Alternating extension from increasing tuples to all tuples. -/
noncomputable def orderedToBaseCechAlternatingF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechObject π M U n ⟶ (baseCechComplex π M U).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
    (orderedToBaseCechZeroExtensionF π M U n ≫
      baseCechPermutationF π M U n σ)

theorem baseCechPermutationF_one
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    baseCechPermutationF π M U n 1 = 𝟙 _ := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M))
  change F.map
        ((FormalCoproduct.mk _ U).mapPower (id : Fin (n + 1) → Fin (n + 1))).op = _
  rw [FormalCoproduct.mapPower_id]
  exact F.map_id _

theorem orderedToBaseCechAlternatingF_comp_baseCechToOrderedF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedToBaseCechAlternatingF π M U n ≫
      baseCechToOrderedF π M U n = 𝟙 _ := by
  rw [orderedToBaseCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single 1]
  · simp [baseCechPermutationF_one,
      orderedToBaseCechZeroExtensionF_comp_baseCechToOrderedF]
  · intro σ hσ hne
    rw [zsmul_comp]
    simp [orderedToBaseCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
      π M U n σ hne]
  · simp

end

end AlgebraicGeometry.Scheme.Modules
