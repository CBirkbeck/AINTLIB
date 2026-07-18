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

theorem baseCechPermutationF_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ τ : Equiv.Perm (Fin (n + 1))) :
    baseCechPermutationF π M U n σ ≫
        baseCechPermutationF π M U n τ =
      baseCechPermutationF π M U n (σ.trans τ) := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
        (baseModulePresheaf π M))
  change F.map ((FormalCoproduct.mk _ U).mapPower σ).op ≫
      F.map ((FormalCoproduct.mk _ U).mapPower τ).op =
    F.map ((FormalCoproduct.mk _ U).mapPower (σ.trans τ)).op
  rw [← F.map_comp, ← op_comp]
  congr 1

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

theorem orderedToBaseCechZeroExtensionF_comp_π_of_not_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : ¬ StrictMono i) :
    orderedToBaseCechZeroExtensionF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i = 0 := by
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  change orderedToBaseCechZeroExtensionF π M U n ≫ p = 0
  have hlinear :
      ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n) ≫
          (baseCechXIsoPi π M U n).inv ≫ p = 0 := by
    dsimp only [p]
    rw [baseCechXIsoPi_inv_comp_proj]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change orderedBaseCechZeroExtendLinearMap π M U n x i = 0
    rw [orderedBaseCechZeroExtendLinearMap_apply, dif_neg hi]
  rw [orderedToBaseCechZeroExtensionF]
  simp only [Category.assoc, hlinear, comp_zero]

theorem orderedToBaseCechZeroExtensionF_comp_π_of_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    orderedToBaseCechZeroExtensionF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor π M U n j.1) ⟨i, hi⟩ := by
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  let q : orderedBaseCechObject π M U n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) ⟨i, hi⟩
  have hp : baseCechToOrderedF π M U n ≫ q = p := by
    dsimp only [p, q]
    exact baseCechToOrderedF_comp_π π M U n ⟨i, hi⟩
  change orderedToBaseCechZeroExtensionF π M U n ≫ p = q
  calc
    orderedToBaseCechZeroExtensionF π M U n ≫ p =
        orderedToBaseCechZeroExtensionF π M U n ≫
          (baseCechToOrderedF π M U n ≫ q) :=
      congrArg (orderedToBaseCechZeroExtensionF π M U n ≫ ·) hp.symm
    _ = (orderedToBaseCechZeroExtensionF π M U n ≫
          baseCechToOrderedF π M U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      rw [orderedToBaseCechZeroExtensionF_comp_baseCechToOrderedF,
        Category.id_comp]

/-- Alternating extension from increasing tuples to all tuples. -/
noncomputable def orderedToBaseCechAlternatingF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechObject π M U n ⟶ (baseCechComplex π M U).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
    (orderedToBaseCechZeroExtensionF π M U n ≫
      baseCechPermutationF π M U n σ)

theorem orderedToBaseCechAlternatingF_comp_permutation
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    orderedToBaseCechAlternatingF π M U n ≫
        baseCechPermutationF π M U n τ =
      (Equiv.Perm.sign τ : ℤ) •
        orderedToBaseCechAlternatingF π M U n := by
  rw [orderedToBaseCechAlternatingF, sum_comp, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [zsmul_comp, Category.assoc, baseCechPermutationF_comp,
    Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
  rw [show σ.trans τ = τ * σ by rfl]
  rw [Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]

theorem orderedToBaseCechAlternatingF_comp_π_of_not_injective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : ¬ Function.Injective i) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i = 0 := by
  let e : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  change orderedToBaseCechAlternatingF π M U n ≫ e = 0
  rw [orderedToBaseCechAlternatingF, sum_comp]
  apply Finset.sum_eq_zero
  intro σ _
  rw [zsmul_comp, Category.assoc, baseCechPermutationF_comp_π]
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n (i ∘ σ) :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) (i ∘ σ)
  let r : baseCechFactor π M U n (i ∘ σ) ⟶
      baseCechFactor π M U n i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
  change (Equiv.Perm.sign σ : ℤ) •
    (orderedToBaseCechZeroExtensionF π M U n ≫ p ≫ r) = 0
  have hmono : ¬ StrictMono (i ∘ σ) := by
    intro h
    apply hi
    intro a b hab
    apply σ.symm.injective
    apply h.injective
    simpa using hab
  have hz :
      orderedToBaseCechZeroExtensionF π M U n ≫ p = 0 := by
    dsimp only [p]
    exact orderedToBaseCechZeroExtensionF_comp_π_of_not_strictMono
      π M U n (i ∘ σ) hmono
  have hpost :
      orderedToBaseCechZeroExtensionF π M U n ≫ (p ≫ r) = 0 := by
    calc
      orderedToBaseCechZeroExtensionF π M U n ≫ (p ≫ r) =
          (orderedToBaseCechZeroExtensionF π M U n ≫ p) ≫ r :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hz, zero_comp]
  rw [hpost, smul_zero]

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

theorem orderedToBaseCechAlternatingF_comp_π_of_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor π M U n j.1) ⟨i, hi⟩ := by
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  let q : orderedBaseCechObject π M U n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) ⟨i, hi⟩
  have hp : baseCechToOrderedF π M U n ≫ q = p := by
    dsimp only [p, q]
    exact baseCechToOrderedF_comp_π π M U n ⟨i, hi⟩
  change orderedToBaseCechAlternatingF π M U n ≫ p = q
  calc
    orderedToBaseCechAlternatingF π M U n ≫ p =
        orderedToBaseCechAlternatingF π M U n ≫
          (baseCechToOrderedF π M U n ≫ q) :=
      congrArg (orderedToBaseCechAlternatingF π M U n ≫ ·) hp.symm
    _ = (orderedToBaseCechAlternatingF π M U n ≫
          baseCechToOrderedF π M U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      rw [orderedToBaseCechAlternatingF_comp_baseCechToOrderedF,
        Category.id_comp]

theorem orderedToBaseCechAlternatingF_comp_π_of_injective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : Function.Injective i) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        (Pi.π (fun j : OrderedCechIndex ι n =>
          baseCechFactor π M U n j.1)
            ⟨i ∘ Tuple.sort i,
              (Tuple.monotone_sort i).strictMono_of_injective
                (hi.comp (Tuple.sort i).injective)⟩ ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower (Tuple.sort i)).φ i).op) := by
  let s := Tuple.sort i
  have hs : StrictMono (i ∘ s) :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp s.injective)
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  let q : orderedBaseCechObject π M U n ⟶
      baseCechFactor π M U n (i ∘ s) :=
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) ⟨i ∘ s, hs⟩
  let r : baseCechFactor π M U n (i ∘ s) ⟶
      baseCechFactor π M U n i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower s).φ i).op
  change orderedToBaseCechAlternatingF π M U n ≫ p =
    (Equiv.Perm.sign s : ℤ) • (q ≫ r)
  rw [orderedToBaseCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single s]
  · rw [zsmul_comp, Category.assoc, baseCechPermutationF_comp_π]
    let ps : (baseCechComplex π M U).X n ⟶
        baseCechFactor π M U n (i ∘ s) :=
      Pi.π (fun j : Fin (n + 1) → ι =>
        baseCechFactor π M U n j) (i ∘ s)
    have hz :
        orderedToBaseCechZeroExtensionF π M U n ≫ ps = q := by
      dsimp only [ps, q]
      exact orderedToBaseCechZeroExtensionF_comp_π_of_strictMono
        π M U n (i ∘ s) hs
    change (Equiv.Perm.sign s : ℤ) •
      (orderedToBaseCechZeroExtensionF π M U n ≫ (ps ≫ r)) =
        (Equiv.Perm.sign s : ℤ) • (q ≫ r)
    have hpost :
        orderedToBaseCechZeroExtensionF π M U n ≫ (ps ≫ r) = q ≫ r := by
      calc
        orderedToBaseCechZeroExtensionF π M U n ≫ (ps ≫ r) =
            (orderedToBaseCechZeroExtensionF π M U n ≫ ps) ≫ r :=
          (Category.assoc _ _ _).symm
        _ = q ≫ r := congrArg (· ≫ r) hz
    exact congrArg ((Equiv.Perm.sign s : ℤ) • ·) hpost
  · intro σ _ hne
    rw [zsmul_comp, Category.assoc, baseCechPermutationF_comp_π]
    have hmono : ¬ StrictMono (i ∘ σ) := by
      intro h
      apply hne
      apply Equiv.ext
      intro x
      apply hi
      exact congrFun
        (Tuple.comp_sort_eq_comp_iff_monotone.mpr h.monotone) x
    have hz := orderedToBaseCechZeroExtensionF_comp_π_of_not_strictMono
      π M U n (i ∘ σ) hmono
    let rσ : baseCechFactor π M U n (i ∘ σ) ⟶
        baseCechFactor π M U n i :=
      (baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
    let pσ : (baseCechComplex π M U).X n ⟶
        baseCechFactor π M U n (i ∘ σ) :=
      Pi.π (fun j : Fin (n + 1) → ι =>
        baseCechFactor π M U n j) (i ∘ σ)
    change (Equiv.Perm.sign σ : ℤ) •
      (orderedToBaseCechZeroExtensionF π M U n ≫ (pσ ≫ rσ)) = 0
    have hpost :
        orderedToBaseCechZeroExtensionF π M U n ≫ (pσ ≫ rσ) = 0 := by
      calc
        orderedToBaseCechZeroExtensionF π M U n ≫ (pσ ≫ rσ) =
            (orderedToBaseCechZeroExtensionF π M U n ≫ pσ) ≫ rσ :=
          (Category.assoc _ _ _).symm
        _ = 0 := by
          dsimp only [pσ]
          rw [hz, zero_comp]
    rw [hpost, smul_zero]
  · simp

theorem orderedToBaseCechAlternatingF_comp_d_comp_π_of_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : StrictMono i) :
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i =
      orderedBaseCechDifferential π M U n ≫
        orderedToBaseCechAlternatingF π M U (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i := by
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) j) i
  let q : orderedBaseCechObject π M U (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : OrderedCechIndex ι (n + 1) =>
      baseCechFactor π M U (n + 1) j.1) ⟨i, hi⟩
  have hp : baseCechToOrderedF π M U (n + 1) ≫ q = p := by
    dsimp only [p, q]
    exact baseCechToOrderedF_comp_π π M U (n + 1) ⟨i, hi⟩
  have ha : orderedToBaseCechAlternatingF π M U (n + 1) ≫ p = q := by
    dsimp only [p, q]
    exact orderedToBaseCechAlternatingF_comp_π_of_strictMono
      π M U (n + 1) i hi
  change orderedToBaseCechAlternatingF π M U n ≫
      (baseCechComplex π M U).d n (n + 1) ≫ p =
    orderedBaseCechDifferential π M U n ≫
      orderedToBaseCechAlternatingF π M U (n + 1) ≫ p
  calc
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫ p =
      orderedToBaseCechAlternatingF π M U n ≫
        ((baseCechComplex π M U).d n (n + 1) ≫
          baseCechToOrderedF π M U (n + 1)) ≫ q := by
        rw [Category.assoc, hp]
    _ = orderedToBaseCechAlternatingF π M U n ≫
        (baseCechToOrderedF π M U n ≫
          orderedBaseCechDifferential π M U n) ≫ q := by
      rw [baseCechComplex_d_comp_baseCechToOrderedF]
    _ = (orderedToBaseCechAlternatingF π M U n ≫
          baseCechToOrderedF π M U n) ≫
        orderedBaseCechDifferential π M U n ≫ q := by
      simp only [Category.assoc]
    _ = orderedBaseCechDifferential π M U n ≫ q := by
      rw [orderedToBaseCechAlternatingF_comp_baseCechToOrderedF,
        Category.id_comp]
    _ = orderedBaseCechDifferential π M U n ≫
        orderedToBaseCechAlternatingF π M U (n + 1) ≫ p := by
      rw [ha]

end

end AlgebraicGeometry.Scheme.Modules
