import ModularCurves.ForMathlib.SheafCechSheafComplex
import ModularCurves.ForMathlib.SheafOrderedCechSheafDifferential

/-!
# The ordered sheaf-level Cech complex

This file proves that consecutive ordered sheaf-level Cech differentials
compose to zero and packages them as a cochain complex.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

private noncomputable def orderedSheafCechFormalObject (n : ℕ) :
    FormalCoproduct (Opens X) where
  I := OrderedCechIndex ι n
  obj i := ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)

private noncomputable def orderedSheafCechFace (n : ℕ)
    (k : Fin (n + 2)) :
    orderedSheafCechFormalObject U (n + 1) ⟶
      orderedSheafCechFormalObject U n where
  f i := i.delete k
  φ i := (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)

private theorem orderedSheafCechFace_comp (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    orderedSheafCechFace U (n + 1) j.succ ≫
        orderedSheafCechFace U n i =
      orderedSheafCechFace U (n + 1) i.castSucc ≫
        orderedSheafCechFace U n j := by
  let V : FormalCoproduct (Opens X) := FormalCoproduct.mk _ U
  have hmap :
      V.mapPower (SimplexCategory.δ j.succ).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ i).toOrderHom.toFun =
        V.mapPower (SimplexCategory.δ i.castSucc).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ j).toOrderHom.toFun := by
    rw [← FormalCoproduct.mapPower_comp,
      ← FormalCoproduct.mapPower_comp]
    congr 1
    exact funext (ConcreteCategory.congr_hom
      (SimplexCategory.δ_comp_δ hij))
  let hf :
      (orderedSheafCechFace U (n + 1) j.succ ≫
          orderedSheafCechFace U n i).f =
        (orderedSheafCechFace U (n + 1) i.castSucc ≫
          orderedSheafCechFace U n j).f :=
    funext fun k => OrderedCechIndex.delete_delete k hij
  apply FormalCoproduct.hom_ext hf
  intro k
  have hk := ((FormalCoproduct.hom_ext_iff _ _).1 hmap).2 k.1
  change
    ((V.mapPower (SimplexCategory.δ j.succ).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ i).toOrderHom.toFun).φ k.1 ≫
        eqToHom _) =
      (V.mapPower (SimplexCategory.δ i.castSucc).toOrderHom.toFun ≫
        V.mapPower (SimplexCategory.δ j).toOrderHom.toFun).φ k.1
  simpa only using hk

private theorem orderedCechCoface_eq_map (n : ℕ)
    (k : Fin (n + 2)) :
    orderedCechCoface F U n k =
      ((FormalCoproduct.evalOp (Opens X)
        (Sheaf AddCommGrpCat.{u} X)).obj
          (cechFactorPresheaf F)).map
        (orderedSheafCechFace U n k).op :=
  rfl

private theorem orderedCechCoface_comp (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    orderedCechCoface F U n i ≫
        orderedCechCoface F U (n + 1) j.succ =
      orderedCechCoface F U n j ≫
        orderedCechCoface F U (n + 1) i.castSucc := by
  let G := ((FormalCoproduct.evalOp (Opens X)
    (Sheaf AddCommGrpCat.{u} X)).obj (cechFactorPresheaf F))
  rw [orderedCechCoface_eq_map, orderedCechCoface_eq_map,
    orderedCechCoface_eq_map, orderedCechCoface_eq_map]
  change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
  rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp,
    orderedSheafCechFace_comp U n hij]

private theorem orderedCechCoface_comp' (n : ℕ)
    {i : Fin (n + 3)} {j : Fin (n + 2)} (hij : i ≤ j.castSucc) :
    orderedCechCoface F U n
          (i.castLT (lt_of_le_of_lt hij j.is_lt)) ≫
        orderedCechCoface F U (n + 1) j.succ =
      orderedCechCoface F U n j ≫
        orderedCechCoface F U (n + 1) i := by
  have hle : i.castLT (lt_of_le_of_lt hij j.is_lt) ≤ j := by
    rw [Fin.le_iff_val_le_val] at hij ⊢
    exact hij
  simpa using orderedCechCoface_comp F U n hle

/-- Consecutive ordered sheaf-level Cech differentials compose to zero. -/
theorem orderedCechDifferential_comp (n : ℕ) :
    orderedCechDifferential F U n ≫
      orderedCechDifferential F U (n + 1) = 0 := by
  dsimp [orderedCechDifferential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 3) × Fin (n + 2)
  let T : Finset P := {ij : P | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ T → P := fun ij hij =>
    (ij.2.succ, Fin.castLT ij.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right
        (Fin.is_lt ij.2)))
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by
      simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      apply mul_comm
    · rw [orderedCechCoface_comp' F U n]
      simpa [T] using! hij

/-- The ordered sheaf-level Cech cochain complex. -/
noncomputable def orderedCechComplex :
    CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  CochainComplex.of (orderedCechTerm F U)
    (orderedCechDifferential F U)
    (orderedCechDifferential_comp F U)

@[simp]
theorem orderedCechComplex_X (n : ℕ) :
    (orderedCechComplex F U).X n = orderedCechTerm F U n :=
  rfl

@[simp]
theorem orderedCechComplex_d (n : ℕ) :
    (orderedCechComplex F U).d n (n + 1) =
      orderedCechDifferential F U n := by
  simp [orderedCechComplex]

end TopCat.Sheaf
