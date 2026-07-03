import LeanModularForms.Issues.Issue55

/-!
# A congruence subgroup that is not self-dual, carrying a self-dual form

This file constructs a concrete example separating three properties of a subgroup of
`SL(2, ℤ)` and a modular form on it. The subgroup `Γ` is the preimage, modulo `3`, of the
stabilizer of the line spanned by `(1, 1)`. It is a congruence subgroup but is not self-dual,
yet the discriminant cusp form `Δ` restricted to it is self-dual.

## Main definitions

* `IssueExample.Γ`: the subgroup of `SL(2, ℤ)` whose reduction mod `3` fixes the sum
  `γ 0 0 + γ 0 1` and `γ 1 0 + γ 1 1`.
* `IssueExample.Δ`: the discriminant cusp form restricted from `SL(2, ℤ)` to `Γ`.

## Main results

* `IssueExample.result`: `Γ` is a congruence subgroup, `Γ` is not self-dual, and `Δ` is
  self-dual.
-/

open ModularForm UpperHalfPlane MatrixGroups ComplexConjugate
open CongruenceSubgroup Pointwise Subgroup
open Matrix Matrix.SpecialLinearGroup Complex
open scoped MatrixGroups ModularForm Real

private lemma eta_neg_conj (z : UpperHalfPlane) :
    conj (ModularForm.eta (-(conj (z : ℂ)))) = ModularForm.eta (z : ℂ) := by
  have hz' : (-(conj (z : ℂ))) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa using z.2
  have hprod := (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable hz').map_tprod
    (starRingEnd ℂ) Complex.continuous_conj
  rw [ModularForm.eta, map_mul, hprod, ModularForm.eta]
  simp [ModularForm.eta_q, Function.Periodic.qParam, ← Complex.exp_conj, map_ofNat]

namespace IssueExample

/-- The subgroup of `SL(2, ℤ)` whose reduction modulo `3` stabilizes the line
spanned by `(1, 1)`. -/
def Γ : Subgroup SL(2, ℤ) where
  carrier := {γ | (γ 0 0 + γ 0 1 : ZMod 3) = (γ 1 0 + γ 1 1 : ZMod 3)}
  one_mem' := by norm_num
  mul_mem' := by
    intro A B hA hB
    change ((A * B) 0 0 + (A * B) 0 1 : ZMod 3) =
      ((A * B) 1 0 + (A * B) 1 1 : ZMod 3)
    have hA' : (A 0 0 : ZMod 3) + (A 0 1 : ZMod 3) =
        (A 1 0 : ZMod 3) + (A 1 1 : ZMod 3) := hA
    have hB' : (B 0 0 : ZMod 3) + (B 0 1 : ZMod 3) =
        (B 1 0 : ZMod 3) + (B 1 1 : ZMod 3) := hB
    simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
    linear_combination ((B 0 0 : ZMod 3) + (B 0 1 : ZMod 3)) * hA' +
      ((A 1 1 : ZMod 3) - (A 0 1 : ZMod 3)) * hB'
  inv_mem' := by
    intro A hA
    change ((A⁻¹) 0 0 + (A⁻¹) 0 1 : ZMod 3) =
      ((A⁻¹) 1 0 + (A⁻¹) 1 1 : ZMod 3)
    have hA' : (A 0 0 : ZMod 3) + (A 0 1 : ZMod 3) =
        (A 1 0 : ZMod 3) + (A 1 1 : ZMod 3) := hA
    rw [SL2_inv_expl A]
    simp only [Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_neg]
    linear_combination -hA'

theorem mem_Γ (γ : SL(2, ℤ)) : γ ∈ Γ ↔ (γ 0 0 + γ 0 1 : ZMod 3) = (γ 1 0 + γ 1 1 : ZMod 3) :=
  Iff.rfl

theorem Γ_isCongruenceSubgroup : CongruenceSubgroup.IsCongruenceSubgroup Γ := by
  refine ⟨3, by norm_num, ?_⟩
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  change (γ 0 0 + γ 0 1 : ZMod 3) = (γ 1 0 + γ 1 1 : ZMod 3)
  simp [hγ]

theorem Γ_not_isSelfDual :
    ¬ Subgroup.IsSelfDual (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  let γ : SL(2, ℤ) := ⟨!![0, 1; -1, -1], by norm_num [Matrix.det_fin_two_of]⟩
  let γJ : SL(2, ℤ) := ⟨!![0, -1; 1, -1], by norm_num [Matrix.det_fin_two_of]⟩
  have hγΓ : γ ∈ Γ := by
    change ((0 : ZMod 3) + (1 : ZMod 3) = (-1 : ZMod 3) + (-1 : ZMod 3))
    decide
  have hγJ_not : γJ ∉ Γ := by
    change ¬ ((0 : ZMod 3) + (-1 : ZMod 3) = (1 : ZMod 3) + (-1 : ZMod 3))
    decide
  have hJinv : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J :=
    inv_eq_of_mul_eq_one_right <| by simpa [sq] using UpperHalfPlane.J_sq
  have hmapγJ : mapGL ℝ γJ = UpperHalfPlane.J * mapGL ℝ γ * UpperHalfPlane.J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [γ, γJ, UpperHalfPlane.J, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_two]
  have hdual_mem : UpperHalfPlane.J * mapGL ℝ γ * UpperHalfPlane.J ∈
      Subgroup.dual (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.dual, hJinv]
    simpa [ConjAct.toConjAct_smul, hJinv] using
      Subgroup.smul_mem_pointwise_smul (mapGL ℝ γ) (ConjAct.toConjAct UpperHalfPlane.J)
        (Γ : Subgroup (GL (Fin 2) ℝ)) (Subgroup.mem_map.mpr ⟨γ, hγΓ, rfl⟩)
  have hnot_mem : UpperHalfPlane.J * mapGL ℝ γ * UpperHalfPlane.J ∉
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    intro hmem
    obtain ⟨δ, hδΓ, hδ⟩ := Subgroup.mem_map.mp hmem
    have hδ_eq : δ = γJ := mapGL_injective (by rw [hδ, ← hmapγJ])
    exact hγJ_not (hδ_eq ▸ hδΓ)
  intro hself
  exact hnot_mem (by simpa [hself.isSelfDual] using hdual_mem)

theorem Γ_le_SL : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := Subgroup.map_le_range (mapGL ℝ) Γ

/-- The discriminant cusp form, restricted from the full modular group to `Γ`. -/
noncomputable def Δ : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  CuspForm.restrictSubgroup Γ_le_SL CuspForm.discriminant

theorem Δ_isSelfDual : ModularFormClass.isSelfDual Δ := by
  ext z
  rw [ModularFormClass.dual_explicit]
  change conj (ModularForm.discriminant (ofComplex (-(conj (z : ℂ))))) =
    ModularForm.discriminant z
  have hz' : 0 < (-(conj (z : ℂ))).im := by simpa using z.2
  simp [ModularForm.discriminant, ofComplex_apply_of_im_pos hz', map_pow, eta_neg_conj]

/-- The concrete example: `Γ` is congruence and not self-dual, while `Δ` is self-dual. -/
theorem result : IsCongruenceSubgroup Γ ∧ ¬ Subgroup.IsSelfDual Γ ∧ ModularFormClass.isSelfDual Δ :=
  ⟨Γ_isCongruenceSubgroup, Γ_not_isSelfDual, Δ_isSelfDual⟩

end IssueExample
