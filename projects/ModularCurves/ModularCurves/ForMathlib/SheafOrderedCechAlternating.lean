import Mathlib.Data.Fin.Tuple.Sort
import ModularCurves.ForMathlib.SheafOrderedCechComparison
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# Degreewise alternating extension of ordered sheaf Cech cochains

This file constructs the alternating extension from increasing tuples to all
tuples and proves that restriction back to increasing tuples is the identity.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

private noncomputable def cechToOrderedProductF (n : ℕ) :
    (∏ᶜ cechTermFactor F U n) ⟶
      ∏ᶜ orderedCechTermFactor F U n :=
  Pi.lift (fun i : OrderedCechIndex ι n =>
    Pi.π (cechTermFactor F U n) i.1)

private theorem cechToOrderedF_eq (n : ℕ) :
    cechToOrderedF F U n = cechToOrderedProductF F U n :=
  rfl

private theorem cechToOrderedProductF_comp_π (n : ℕ)
    (i : OrderedCechIndex ι n) :
    cechToOrderedProductF F U n ≫
        Pi.π (orderedCechTermFactor F U n) i =
      Pi.π (cechTermFactor F U n) i.1 :=
  Pi.lift_π _ i

/-- Extend ordered Cech cochains by zero on tuples that are not strictly
increasing. -/
noncomputable def orderedToCechZeroExtensionF (n : ℕ) :
    (∏ᶜ orderedCechTermFactor F U n) ⟶
      ∏ᶜ cechTermFactor F U n :=
  Pi.lift fun i : Fin (n + 1) → ι =>
    if h : StrictMono i then
      Pi.π (orderedCechTermFactor F U n) ⟨i, h⟩
    else 0

theorem orderedToCechZeroExtensionF_comp_π_of_strictMono (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    orderedToCechZeroExtensionF F U n ≫
        Pi.π (cechTermFactor F U n) i =
      Pi.π (orderedCechTermFactor F U n) ⟨i, hi⟩ := by
  change
    Pi.lift (fun j : Fin (n + 1) → ι =>
      if h : StrictMono j then
        Pi.π (orderedCechTermFactor F U n) ⟨j, h⟩
      else 0) ≫ Pi.π (cechTermFactor F U n) i = _
  rw [Pi.lift_π, dif_pos hi]

theorem orderedToCechZeroExtensionF_comp_π_of_not_strictMono
    (n : ℕ) (i : Fin (n + 1) → ι) (hi : ¬ StrictMono i) :
    orderedToCechZeroExtensionF F U n ≫
        Pi.π (cechTermFactor F U n) i = 0 := by
  change
    Pi.lift (fun j : Fin (n + 1) → ι =>
      if h : StrictMono j then
        Pi.π (orderedCechTermFactor F U n) ⟨j, h⟩
      else 0) ≫ Pi.π (cechTermFactor F U n) i = 0
  rw [Pi.lift_π, dif_neg hi]

/-- Reindex native sheaf Cech cochains by a permutation of tuple positions. -/
noncomputable def cechPermutationF (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∏ᶜ cechTermFactor F U n) ⟶
      ∏ᶜ cechTermFactor F U n :=
  Pi.lift fun i : Fin (n + 1) → ι =>
    Pi.π (cechTermFactor F U n) (i ∘ σ) ≫
      cechTermFactorRestriction F
        (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ i))

omit [LinearOrder ι] in
theorem cechPermutationF_comp_π (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1) → ι) :
    cechPermutationF F U n σ ≫
        Pi.π (cechTermFactor F U n) i =
      Pi.π (cechTermFactor F U n) (i ∘ σ) ≫
        cechTermFactorRestriction F
          (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ i)) := by
  change
    (Pi.lift fun j : Fin (n + 1) → ι =>
      Pi.π (cechTermFactor F U n) (j ∘ σ) ≫
        cechTermFactorRestriction F
          (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ j))) ≫ _ = _
  exact Pi.lift_π _ i

omit [LinearOrder ι] in
private theorem cechPermutationF_one (n : ℕ) :
    cechPermutationF F U n 1 = 𝟙 _ := by
  unfold cechPermutationF
  apply Pi.hom_ext
  intro i
  rw [Category.id_comp, Pi.lift_π]
  change
    Pi.π (cechTermFactor F U n) i ≫
        cechTermFactorRestriction F
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (1 : Equiv.Perm (Fin (n + 1)))).φ i)) =
      Pi.π (cechTermFactor F U n) i
  rw [← Category.comp_id (Pi.π (cechTermFactor F U n) i)]
  congr 1
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change F.obj.map _ = 𝟙 _
  rw [← F.obj.map_id]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- Alternating extension from increasing tuples to all tuples. -/
noncomputable def orderedToCechAlternatingF (n : ℕ) :
    (∏ᶜ orderedCechTermFactor F U n) ⟶
      ∏ᶜ cechTermFactor F U n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
    (orderedToCechZeroExtensionF F U n ≫ cechPermutationF F U n σ)

private theorem orderedToCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ ≠ 1) :
    orderedToCechZeroExtensionF F U n ≫ cechPermutationF F U n σ ≫
        cechToOrderedProductF F U n =
      (0 : (∏ᶜ orderedCechTermFactor F U n) ⟶
        ∏ᶜ orderedCechTermFactor F U n) := by
  apply Pi.hom_ext
  intro i
  have hi : ¬ StrictMono (i.1 ∘ σ) := by
    intro h
    have hmono : Monotone σ := fun a b hab =>
      i.2.le_iff_le.mp (h.monotone hab)
    exact hσ ((Equiv.Perm.monotone_iff σ).mp hmono)
  let p : (∏ᶜ orderedCechTermFactor F U n) ⟶
      orderedCechTermFactor F U n i :=
    Pi.π (orderedCechTermFactor F U n) i
  let q : (∏ᶜ cechTermFactor F U n) ⟶
      cechTermFactor F U n i.1 :=
    Pi.π (cechTermFactor F U n) i.1
  let qσ : (∏ᶜ cechTermFactor F U n) ⟶
      cechTermFactor F U n (i.1 ∘ σ) :=
    Pi.π (cechTermFactor F U n) (i.1 ∘ σ)
  let r : cechTermFactor F U n (i.1 ∘ σ) ⟶
      cechTermFactor F U n i.1 :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ i.1))
  have hp : cechToOrderedProductF F U n ≫ p = q :=
    cechToOrderedProductF_comp_π F U n i
  have hσp : cechPermutationF F U n σ ≫ q = qσ ≫ r :=
    cechPermutationF_comp_π F U n σ i.1
  have hz : orderedToCechZeroExtensionF F U n ≫ qσ = 0 :=
    orderedToCechZeroExtensionF_comp_π_of_not_strictMono F U n _ hi
  calc
    (orderedToCechZeroExtensionF F U n ≫
        cechPermutationF F U n σ ≫ cechToOrderedProductF F U n) ≫ p =
      orderedToCechZeroExtensionF F U n ≫
        (cechPermutationF F U n σ ≫
          (cechToOrderedProductF F U n ≫ p)) := by simp only [Category.assoc]
    _ = orderedToCechZeroExtensionF F U n ≫
        (cechPermutationF F U n σ ≫ q) := by rw [hp]
    _ = orderedToCechZeroExtensionF F U n ≫ (qσ ≫ r) := by rw [hσp]
    _ = (orderedToCechZeroExtensionF F U n ≫ qσ) ≫ r :=
      (Category.assoc _ _ _).symm
    _ = 0 := by rw [hz, zero_comp]
    _ = 0 ≫ p := zero_comp.symm

private theorem orderedToCechZeroExtensionF_comp_cechToOrderedProductF
    (n : ℕ) :
    orderedToCechZeroExtensionF F U n ≫
      cechToOrderedProductF F U n =
        𝟙 (∏ᶜ orderedCechTermFactor F U n) := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, cechToOrderedProductF_comp_π, Category.id_comp]
  exact orderedToCechZeroExtensionF_comp_π_of_strictMono
    F U n i.1 i.2

/-- Alternating extension followed by the product projection is the identity. -/
private theorem orderedToCechAlternatingF_comp_cechToOrderedProductF (n : ℕ) :
    orderedToCechAlternatingF F U n ≫ cechToOrderedProductF F U n =
      𝟙 (∏ᶜ orderedCechTermFactor F U n) := by
  rw [orderedToCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single 1]
  · rw [Equiv.Perm.sign_one, Units.val_one, one_zsmul,
      cechPermutationF_one, Category.comp_id,
      orderedToCechZeroExtensionF_comp_cechToOrderedProductF]
  · intro σ _ hσ
    rw [zsmul_comp]
    simp [orderedToCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
      F U n σ hσ]
  · simp

/-- Alternating extension followed by projection to ordered tuples is the
identity in every degree. -/
theorem orderedToCechAlternatingF_comp_cechToOrderedF (n : ℕ) :
    orderedToCechAlternatingF F U n ≫ cechToOrderedF F U n = 𝟙 _ := by
  rw [cechToOrderedF_eq]
  exact orderedToCechAlternatingF_comp_cechToOrderedProductF F U n

end TopCat.Sheaf
