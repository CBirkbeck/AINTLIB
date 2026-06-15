/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import LeanModularForms.Modularforms.IsCuspForm
public import LeanModularForms.Modularforms.DimGenCongLevels.Basic
public import LeanModularForms.Modularforms.DimGenCongLevels.NormReduction
public import LeanModularForms.Modularforms.DimGenCongLevels.FiniteDimensional
public import LeanModularForms.Modularforms.DimGenCongLevels.NormTransfer

@[expose] public section

/-!
# Dimension formulas for level-one modular forms

This file is a thin wrapper around mathlib's level-one dimension formula
(`ModularForm.dimension_level_one`) and the related finite-dimensionality results.
Mathlib now states these for the `GL`-side subgroup `𝒮ℒ`; the project still uses the
`SL`-side notation `Γ(1)` extensively, so we transport the rank statements along the
identification `↑Γ(1) = 𝒮ℒ` (`CongruenceSubgroup.Gamma_one_coe_eq_SL`) via
`ModularForm.mcast` / `CuspForm.mcast`-based `LinearEquiv`s.

## Main results

* `modularFormGammaOneEquivSL`, `cuspFormGammaOneEquivSL`: linear equivalences carrying
  the project's `Γ(1)`-indexed spaces to mathlib's `𝒮ℒ`-indexed ones.
* `cuspform_weight_lt_12_zero`, `IsCuspForm_weight_lt_eq_zero`: weight-`< 12` cusp form
  vanishing (used by `Modularforms/ThetaDerivIdentities.lean`,
  `Modularforms/JacobiTheta.lean`).
* `CuspForms_iso_Modforms`: the division-by-`Δ` isomorphism for `Γ(1)`, transported from
  `CuspForm.discriminantEquiv` (used by `Modularforms/JacobiTheta.lean`).
* `weight_four_one_dimensional`, `weight_six_one_dimensional`, `weight_eight_one_dimensional`:
  one-dimensionality of low even-weight spaces (used in `Modularforms/RamanujanIdentities.lean`).
* `dim_gen_cong_levels`: finite-dimensionality for any finite-index congruence subgroup,
  via mathlib's `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance and the norm-reduction
  injection.
-/

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-! ### Transport equivalences between `Γ(1)` and `𝒮ℒ` -/

/-- Linear equivalence between `Γ(1)`-modular forms and `𝒮ℒ`-modular forms, transported via
`ModularForm.mcast` along the equality `↑Γ(1) = 𝒮ℒ`. -/
def modularFormGammaOneEquivSL (k : ℤ) : ModularForm Γ(1) k ≃ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun f := ModularForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  invFun f := ModularForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma modularFormGammaOneEquivSL_apply (k : ℤ) (f : ModularForm Γ(1) k) (z : ℍ) :
    modularFormGammaOneEquivSL k f z = f z := rfl

/-- Linear equivalence between `Γ(1)`-cusp forms and `𝒮ℒ`-cusp forms, transported via
`CuspForm.mcast` along the equality `↑Γ(1) = 𝒮ℒ`. -/
def cuspFormGammaOneEquivSL (k : ℤ) : CuspForm Γ(1) k ≃ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun f := CuspForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  invFun f := CuspForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma cuspFormGammaOneEquivSL_apply (k : ℤ) (f : CuspForm Γ(1) k) (z : ℍ) :
    cuspFormGammaOneEquivSL k f z = f z := rfl

/-! ### Weight-`< 12` cusp forms vanish -/

/-- The space of `Γ(1)` cusp forms of weight `k < 12` has rank zero. -/
lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) :
    Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  rw [LinearEquiv.rank_eq (cuspFormGammaOneEquivSL k)]
  exact CuspForm.rank_eq_zero_of_weight_lt_twelve hk

lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2 := CuspForm_to_ModularForm_coe _ _ f hf
  ext z
  have hz := congr_fun (congr_arg (fun x ↦ x.1) hfc2) z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
    toSlashInvariantForm_coe] at hz
  rw [ModularForm.zero_apply, ← hz,
    rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero k hk)
      (IsCuspForm_to_CuspForm Γ(1) k f hf)]
  simp only [CuspForm.zero_apply]

/-! ### The `CuspForm Γ(1) k ≃ₗ ModularForm Γ(1) (k-12)` isomorphism -/

/-- Division by the discriminant yields a linear equivalence between `Γ(1)`-cusp forms of
weight `k` and `Γ(1)`-modular forms of weight `k - 12`. This is the project's wrapper around
mathlib's `CuspForm.discriminantEquiv` (stated for `𝒮ℒ`). -/
def CuspForms_iso_Modforms (k : ℤ) :
    CuspForm Γ(1) k ≃ₗ[ℂ] ModularForm Γ(1) (k - 12) :=
  (cuspFormGammaOneEquivSL k).trans
    (CuspForm.discriminantEquiv.trans (modularFormGammaOneEquivSL (k - 12)).symm)

/-! ### Low even weights are one-dimensional -/

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 := by
  rw [LinearEquiv.rank_eq (modularFormGammaOneEquivSL 4)]
  exact ModularForm.levelOne_weight_four_rank_one

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 := by
  rw [LinearEquiv.rank_eq (modularFormGammaOneEquivSL 6)]
  exact ModularForm.levelOne_weight_six_rank_one

/-- For even `k` with `3 ≤ k < 12`, the space of `Γ(1)` modular forms of weight `k` is
one-dimensional. -/
lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [LinearEquiv.rank_eq (modularFormGammaOneEquivSL (k : ℤ))]
  have hdim := ModularForm.dimension_level_one k hk2
  have hdiv : k / 12 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hk3)
  by_cases hmod : k ≡ 2 [MOD 12]
  · have hk2' : k = 2 := by
      have h12 : k % 12 = 2 % 12 := hmod
      have hk' : k = k % 12 := (Nat.mod_eq_of_lt hk3).symm
      omega
    omega
  · rw [hdim, if_neg hmod, hdiv]
    norm_cast

/-! ### Finite-dimensionality for arbitrary finite-index congruence subgroups -/

open SpherePacking.ModularForms.NormReduction in
private lemma dim_gen_cong_levels_eq_of_coeff_eq_zero {k : ℤ} {Γ : Subgroup SL(2, ℤ)}
    [Γ.FiniteIndex] {N : ℕ}
    (hNinj : Function.Injective fun (f : ModularForm 𝒮ℒ (k * Nat.card (Q Γ)))
      (n : Fin N) ↦ (qExpansion (cuspWidth (Γ := Γ)) f).coeff n) (f g : ModularForm (G Γ) k)
    (hcoeff : ∀ m < N, (qExpansion (cuspWidth (Γ := Γ)) (⇑(f - g))).coeff m = 0) : f = g := by
  have hcoeff_norm : ∀ m < N,
      (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ (f - g))).coeff m = 0 := fun m hm ↦
    SpherePacking.ModularForms.NormReduction.qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero
      (Γ := Γ) (k := k) (f := (f - g)) (N := N) (n := m) hm hcoeff
  have hfun :
      (fun n : Fin N ↦ (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ (f - g))).coeff n) =
        fun n : Fin N ↦
          (qExpansion (cuspWidth (Γ := Γ)) (0 : ModularForm 𝒮ℒ (k * Nat.card (Q Γ)))).coeff n := by
    ext n
    simpa [qExpansion_zero (cuspWidth (Γ := Γ))] using hcoeff_norm (n : ℕ) n.isLt
  have hnorm : ModularForm.norm 𝒮ℒ (f - g) = (0 : ModularForm 𝒮ℒ (k * Nat.card (Q Γ))) :=
    hNinj hfun
  have hsub : (f - g : ModularForm (G Γ) k) = 0 :=
    (coe_eq_zero_iff (f - g)).mp <|
      (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := (f - g)) (k := k)).1 (by simpa using hnorm)
  simpa [sub_eq_zero] using hsub

open SpherePacking.ModularForms.NormReduction in
lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  by_cases hkneg : k < 0
  · exact SpherePacking.ModularForms.finiteDimensional_modularForm_neg_weight Γ hΓ k hkneg
  by_cases hk0 : k = 0
  · subst hk0
    exact SpherePacking.ModularForms.finiteDimensional_modularForm_weight_zero Γ hΓ
  haveI : Γ.FiniteIndex := ⟨hΓ⟩
  let GΓ : Subgroup (GL (Fin 2) ℝ) := SpherePacking.ModularForms.NormReduction.G Γ
  let h : ℝ := SpherePacking.ModularForms.NormReduction.cuspWidth (Γ := Γ)
  have hh : 0 < h := SpherePacking.ModularForms.NormReduction.cuspWidth_pos (Γ := Γ) hΓ
  have hperΓ : h ∈ GΓ.strictPeriods :=
    SpherePacking.ModularForms.NormReduction.cuspWidth_mem_strictPeriods (Γ := Γ)
  have hperSL : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simpa [h] using
      SpherePacking.ModularForms.NormReduction.cuspWidth_mem_strictPeriods_levelOne (Γ := Γ)
  haveI : GΓ.IsArithmetic :=
    SpherePacking.ModularForms.NormReduction.instIsArithmetic (Γ := Γ) hΓ
  haveI : GΓ.IsFiniteRelIndex 𝒮ℒ := Subgroup.IsArithmetic.isFiniteRelIndexSL (𝒢 := GΓ)
  let w : ℤ := k * Nat.card (SpherePacking.ModularForms.NormReduction.Q Γ)
  haveI : FiniteDimensional ℂ (ModularForm 𝒮ℒ w) := inferInstance
  obtain ⟨N, hNinj⟩ :=
    SpherePacking.ModularForms.exists_qCoeff_injective
      (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (k := w) (h := h) hh hperSL
  let trunc : ModularForm GΓ k →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun f n ↦ (qExpansion h f).coeff n
      map_add' f g := by ext n; simp [ModularForm.qExpansion_add hh hperΓ f g]
      map_smul' a f := by ext n; simp [ModularForm.qExpansion_smul hh hperΓ a f] }
  have htrunc_inj : Function.Injective trunc := by
    intro f g hfg
    refine dim_gen_cong_levels_eq_of_coeff_eq_zero hNinj f g fun m hm ↦ ?_
    have hsub : trunc (f - g) = 0 := by
      rw [trunc.map_sub, hfg, sub_self]
    have := congrArg (fun t : Fin N → ℂ ↦ t ⟨m, hm⟩) hsub
    simpa [trunc] using this
  haveI : FiniteDimensional ℂ (Fin N → ℂ) := by infer_instance
  simpa using (FiniteDimensional.of_injective trunc htrunc_inj)
