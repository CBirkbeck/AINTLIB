/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module
public import LeanModularForms.Modularforms.DimGenCongLevels.FiniteDimensional
public import LeanModularForms.Modularforms.DimGenCongLevels.Auxiliary

/-!
# Norm reduction for `q`-coefficients

This file sets up the group-theoretic data and auxiliary factors used in the norm argument for
`dim_gen_cong_levels`. In particular, it defines the cusp width at `∞` for a finite-index
subgroup and the product `restProd` of the nontrivial slash translates which appears in the
norm formula.

## Main definitions
* `G`: a subgroup of `SL(2, ℤ)` viewed as a subgroup of `GL(2, ℝ)`.
* `Q`: the coset space indexing the factors in the norm product.
* `cuspWidth`: the strict cusp width at `∞`.
* `restProd`: the product of nontrivial slash translates appearing in the norm formula.
-/

namespace SpherePacking.ModularForms.NormReduction

open scoped MatrixGroups
open UpperHalfPlane

noncomputable section
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- View a subgroup `Γ ≤ SL(2,ℤ)` as a subgroup of `GL(2,ℝ)` via the standard coercion. -/
@[expose, reducible] public def G (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  (Γ : Subgroup (GL (Fin 2) ℝ))

/-- The quotient indexing the factors in the norm product. -/
@[expose, reducible] public def Q (Γ : Subgroup SL(2, ℤ)) : Type :=
  𝒮ℒ ⧸ ((G Γ).subgroupOf 𝒮ℒ)

/-- `G Γ` is an arithmetic subgroup when `Γ` has finite index. -/
public lemma instIsArithmetic (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    (G Γ).IsArithmetic := by
  simpa [G] using (Subgroup.isArithmetic_iff_finiteIndex (Γ := Γ)).2 ⟨hΓ⟩

/-- The strict width at `∞` for the subgroup `G Γ`. -/
public noncomputable def cuspWidth : ℝ := (G Γ).strictWidthInfty

/-- The cusp width `cuspWidth` is positive. -/
public lemma cuspWidth_pos (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    0 < cuspWidth (Γ := Γ) := by
  letI := instIsArithmetic Γ hΓ
  simpa [cuspWidth] using Subgroup.strictWidthInfty_pos (𝒢 := G Γ)

/-- The cusp width belongs to the strict period set of `G Γ`. -/
public lemma cuspWidth_mem_strictPeriods (Γ : Subgroup SL(2, ℤ)) :
    cuspWidth (Γ := Γ) ∈ (G Γ).strictPeriods := by
  simpa [cuspWidth] using Subgroup.strictWidthInfty_mem_strictPeriods (𝒢 := G Γ)

/-- The cusp width belongs to the strict period set of the full level-one group `𝒮ℒ`. -/
public lemma cuspWidth_mem_strictPeriods_levelOne (Γ : Subgroup SL(2, ℤ)) :
    cuspWidth (Γ := Γ) ∈ ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  have hle : G Γ ≤ 𝒮ℒ := by
    simpa [G] using Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) (H := Γ)
  exact Subgroup.mem_strictPeriods_iff.2 <| hle <|
    Subgroup.mem_strictPeriods_iff.1 (cuspWidth_mem_strictPeriods (Γ := Γ))

section BoundedFactors

lemma quotientFunc_isBoundedAtImInfty
    (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) (f : ModularForm (G Γ) k) (q : Q Γ) :
    IsBoundedAtImInfty (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) := by
  have : (G Γ).IsArithmetic := instIsArithmetic Γ hΓ
  refine Quotient.inductionOn q fun ⟨_, ⟨γ, rfl⟩⟩ ↦ ?_
  rw [SlashInvariantForm.quotientFunc_mk]
  simpa only [map_inv, ModularForm.SL_slash, Matrix.SpecialLinearGroup.mapGL,
    MonoidHom.coe_comp, Function.comp_apply, algebraMap_int_eq] using
    ModularFormClass.bdd_at_infty_slash (f := f) (Γ := G Γ) (k := k) (g := γ⁻¹)

/-- The product of all nontrivial quotient factors appearing in the norm formula.

This is the product of `SlashInvariantForm.quotientFunc` over `Q Γ`, excluding the identity coset.
-/
@[expose] public noncomputable def restProd (Γ : Subgroup SL(2, ℤ))
    [(G Γ).IsFiniteRelIndex 𝒮ℒ] (f : ModularForm (G Γ) k) : ℍ → ℂ := by
  let _ : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  let _ : DecidableEq (Q Γ) := Classical.decEq _
  exact (Finset.univ.erase (⟦(1 : 𝒮ℒ)⟧ : Q Γ)).prod fun q ↦
    SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q

/-- The product `restProd` is bounded at `Im z → ∞`. -/
public lemma restProd_isBoundedAtImInfty (Γ : Subgroup SL(2, ℤ))
    [(G Γ).IsFiniteRelIndex 𝒮ℒ] (hΓ : Subgroup.index Γ ≠ 0) (f : ModularForm (G Γ) k) :
    IsBoundedAtImInfty (restProd (k := k) (Γ := Γ) f) := by
  have : (G Γ).IsArithmetic := instIsArithmetic Γ hΓ
  let _ : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  let _ : DecidableEq (Q Γ) := Classical.decEq _
  simpa [IsBoundedAtImInfty, restProd] using
    Filter.BoundedAtFilter.prod (l := atImInfty)
      (s := Finset.univ.erase (⟦(1 : 𝒮ℒ)⟧ : Q Γ)) fun q _ ↦ by
      simpa [IsBoundedAtImInfty] using quotientFunc_isBoundedAtImInfty (k := k) Γ hΓ f q

end BoundedFactors

end

end SpherePacking.ModularForms.NormReduction
