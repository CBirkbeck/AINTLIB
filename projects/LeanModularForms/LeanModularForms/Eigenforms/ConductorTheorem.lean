/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.LevelRaise

/-!
# Miyake Theorem 4.6.4 — Conductor theorem

This file develops the conductor theorem of Miyake §4.6.4.

> Let `g` be a level-`Γ₁(N)` weight-`k` cusp form lying in the Nebentypus
> eigenspace `cuspFormCharSpace k χ.toUnitHom`, whose `q`-expansion is
> supported only on multiples of `l`. Then:
>
>  * if `l * χ.conductor ∣ N`, then `χ` factors as `χ = changeLevel _ χ_low`
>    for a unique `χ_low : DirichletCharacter ℂ (N / l)`, and there is a
>    level-`N/l` cusp form `g'` in `cuspFormCharSpace k χ_low.toUnitHom`
>    with `g = levelRaise (N/l) l k g'`;
>  * otherwise (`l * χ.conductor ∤ N`), `g = 0`.

The main results are `conductor_theorem_dichotomy` /
`conductor_theorem_dichotomy_cuspForm` and their strengthened variants
`conductor_theorem_dichotomy_strong` / `conductor_theorem_dichotomy_cuspForm_strong`.

## Reference

* Miyake, *Modular Forms*, Theorem 4.6.4.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CuspForm

open scoped MatrixGroups ModularForm Pointwise Manifold

noncomputable section

namespace HeckeRing.GL2

variable {N : ℕ} {k : ℤ}

/-- The modular `T = [[1, 1], [0, 1]]` matrix lies in `Γ₁(N)` for every level. -/
lemma ModularGroup_T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.coe_T]

private lemma dvd_lower_left_of_dvd_of_mem_Gamma0
    {l N : ℕ} (h_dvd : l ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (l : ℤ) ∣ γ.val 1 0 :=
  (Int.natCast_dvd_natCast.mpr h_dvd).trans
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma0_mem).mp hγ))

/-- Case A conductor-lowering bridge, level-raised form: if
`g ∈ modFormCharSpace k χ.toUnitHom` factors as `⇑g = levelRaiseFun l k f` and
`l ∣ N`, then for every `γ ∈ Γ₀(N)`, with `γ̃ = α_l γ α_l⁻¹`,
`levelRaiseFun l k (f ∣[k] mapGL ℝ γ̃) = (χ d_γ) • levelRaiseFun l k f`. -/
lemma conductor_slash_levelRaise_eq (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    levelRaiseFun l k (f ∣[k] (mapGL ℝ
        (levelRaiseConjOfDvd l γ
          (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ))
        : GL (Fin 2) ℝ)) =
      (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • levelRaiseFun l k f := by
  have h_neb := (modFormCharSpace_iff_nebentypus k χ.toUnitHom g).mp hg_char ⟨γ, hγ⟩
  rwa [hg_eq, slash_mapGL_levelRaiseFun] at h_neb

/-- Scalar multiplication commutes with the level-raise operator:
`c • levelRaiseFun l k f = levelRaiseFun l k (c • f)`. -/
lemma smul_levelRaiseFun (l : ℕ) [NeZero l] (k : ℤ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    c • levelRaiseFun l k f = levelRaiseFun l k (c • f) := by
  funext τ; simp [levelRaiseFun_apply, smul_eq_mul]

/-- Unlifted Case A conductor-lowering bridge: same hypotheses as
`conductor_slash_levelRaise_eq`, with the un-rescaled Nebentypus identity for
`f`, namely `f ∣[k] mapGL ℝ γ̃ = (χ d_γ) • f` where `γ̃ = α_l γ α_l⁻¹`. -/
lemma conductor_slash_eq (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    f ∣[k] (mapGL ℝ
        (levelRaiseConjOfDvd l γ
          (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ))
        : GL (Fin 2) ℝ) =
      (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f := by
  have h_lifted := conductor_slash_levelRaise_eq l N h_dvd k χ f g hg_char hg_eq γ hγ
  rw [smul_levelRaiseFun] at h_lifted
  exact levelRaiseFun_injective l k h_lifted

/-- Inverse formula for the level-raise: from `⇑g = levelRaiseFun l k f`,
recover `f` as the precomposition of `g` with the inverse `α_l⁻¹`-action,
`f τ = g (α_l⁻¹ • τ)`. -/
lemma fun_eq_apply_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg : g = levelRaiseFun l k f) (τ : UpperHalfPlane) :
    f τ = g ((levelRaiseMatrix l)⁻¹ • τ) := by
  rw [hg, levelRaiseFun_apply, smul_smul, mul_inv_cancel (levelRaiseMatrix l), one_smul]

/-- Functional equality version of `fun_eq_apply_levelRaiseMatrix_inv_smul`:
`f = (fun τ => g (α_l⁻¹ • τ))`. -/
lemma fun_eq_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg : g = levelRaiseFun l k f) :
    f = fun τ ↦ g ((levelRaiseMatrix l)⁻¹ • τ) :=
  funext (fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg)

/-- Positive determinant of `(levelRaiseMatrix l)⁻¹`: the inverse has det
`1 / l > 0`. -/
lemma levelRaiseMatrix_inv_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)⁻¹ : ℝ) := by
  rw [show (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)⁻¹ : ℝˣ) =
      (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l))⁻¹ from
        map_inv Matrix.GeneralLinearGroup.det _, Units.val_inv_eq_inv_val]
  exact inv_pos.mpr (levelRaiseMatrix_det_pos l)

/-- Holomorphy inheritance: if `g : ℍ → ℂ` is holomorphic and
`g = levelRaiseFun l k f`, then `f` is also holomorphic on `ℍ`. -/
lemma mdifferentiable_of_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ)
    (hg_diff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hg_eq : g = levelRaiseFun l k f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  rw [fun_eq_levelRaiseMatrix_inv_smul l k f g hg_eq]
  exact hg_diff.comp
    (UpperHalfPlane.mdifferentiable_smul (levelRaiseMatrix_inv_det_pos l))

/-- The Case A lowered character: when `χ` factors through level `N/l`,
this is the unique `χ_low : DirichletCharacter ℂ (N/l)` with
`χ = changeLevel _ χ_low`. -/
noncomputable def loweredCharacter {N : ℕ} {l : ℕ} {χ : DirichletCharacter ℂ N}
    (hfac : χ.FactorsThrough (N / l)) : DirichletCharacter ℂ (N / l) :=
  hfac.χ₀

/-- `loweredCharacter hfac` re-raises to `χ` along the canonical level-change. -/
lemma changeLevel_loweredCharacter {N : ℕ} {l : ℕ} {χ : DirichletCharacter ℂ N}
    (hfac : χ.FactorsThrough (N / l)) :
    DirichletCharacter.changeLevel hfac.dvd (loweredCharacter hfac) = χ :=
  hfac.eq_changeLevel.symm

/-- The unit-group hom of `χ_low` agrees with `χ.toUnitHom` after composition
with the unit-group reduction `(ZMod N)ˣ → (ZMod (N/l))ˣ`:
`χ.toUnitHom = χ_low.toUnitHom ∘ ZMod.unitsMap (N/l ∣ N)`. -/
lemma toUnitHom_loweredCharacter {N : ℕ} {l : ℕ} {χ : DirichletCharacter ℂ N}
    (hfac : χ.FactorsThrough (N / l)) :
    χ.toUnitHom = (loweredCharacter hfac).toUnitHom.comp (ZMod.unitsMap hfac.dvd) := by
  conv_lhs => rw [← changeLevel_loweredCharacter hfac]
  exact DirichletCharacter.changeLevel_toUnitHom (χ := loweredCharacter hfac) hfac.dvd

private def slashStabilizerOfFun (k : ℤ) (f : UpperHalfPlane → ℂ) :
    Subgroup SL(2, ℤ) where
  carrier := { γ | f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f }
  one_mem' := by
    change f ∣[k] (mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = f
    rw [map_one, SlashAction.slash_one]
  mul_mem' := fun {a b} ha hb ↦ by
    change f ∣[k] (mapGL ℝ (a * b) : GL (Fin 2) ℝ) = f
    rw [map_mul, SlashAction.slash_mul, ha, hb]
  inv_mem' := fun {a} ha ↦ by
    change f ∣[k] (mapGL ℝ a⁻¹ : GL (Fin 2) ℝ) = f
    have h_mul := SlashAction.slash_mul k (mapGL ℝ a) (mapGL ℝ a⁻¹) f
    rw [show (mapGL ℝ a : GL (Fin 2) ℝ) * mapGL ℝ a⁻¹ = 1 by
        rw [← map_mul, mul_inv_cancel, map_one],
      SlashAction.slash_one, ha] at h_mul
    exact h_mul.symm

/-- Given the period-1 hypothesis `f ∣[k] T = f`, the slash by every integer
power of `T` is also trivial: `f ∣[k] T^j = f` for all `j : ℤ`. -/
lemma slash_T_zpow_eq_self_of_slash_T_eq (k : ℤ) (f : UpperHalfPlane → ℂ)
    (hf : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) (j : ℤ) :
    f ∣[k] (mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) = f :=
  zpow_mem (show ModularGroup.T ∈ slashStabilizerOfFun k f from hf) j

/-- Slash bridge for T-conjugates of the α_l-conjugation image: under the
Case A hypotheses plus the period-1 hypothesis `f ∣[k] T = f`, the slash
identity for `f` extends to all matrices `T^i · γ̃ · T^j` with
`γ̃ = α_l γ α_l⁻¹` (`γ ∈ Γ₀(N)`), giving
`f ∣[k] (T^i · γ̃ · T^j) = (χ d_γ) • f`. -/
lemma conductor_slash_T_conj_eq (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    (i j : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    f ∣[k] (mapGL ℝ
        (ModularGroup.T ^ i *
          levelRaiseConjOfDvd l γ
            (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ) *
          ModularGroup.T ^ j) : GL (Fin 2) ℝ) =
      (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f := by
  set gtilde := levelRaiseConjOfDvd l γ (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ)
  rw [show mapGL ℝ (ModularGroup.T ^ i * gtilde * ModularGroup.T ^ j) =
        mapGL ℝ (ModularGroup.T ^ i) * mapGL ℝ gtilde * mapGL ℝ (ModularGroup.T ^ j) from
      by simp [map_mul],
    SlashAction.slash_mul, SlashAction.slash_mul,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf_period i,
    conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq γ hγ]
  have hσ_T : UpperHalfPlane.σ
      (mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos
      (show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ (ModularGroup.T ^ j))).val by
        rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num)]
  rw [ModularForm.smul_slash, hσ_T, ContinuousAlgEquiv.refl_apply,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf_period j]

/-- Slash invariance of `f` under `Γ₁(N/l)`: under the Case A hypotheses
including `χ.FactorsThrough (N/l)`, the function `f` transforms trivially
under the slash action of `mapGL ℝ δ` for every `δ ∈ Γ₁(N/l)`. -/
lemma conductor_slash_eq_self_of_mem_Gamma1_div (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h_fac : χ.FactorsThrough (N / l)) (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma1 (N / l)) :
    f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = f := by
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd δ (Gamma1_in_Gamma0 _ hδ)
  rw [hfact, conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period i j γ hγ]
  suffices h_char : χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) = 1 by
    rw [h_char, Units.val_one, one_smul]
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  have h_red : ZMod.unitsMap h_fac.dvd (Gamma0MapUnits ⟨γ, hγ⟩) = 1 := by
    apply Units.ext
    simp only [Units.val_one, ZMod.unitsMap_val, Gamma0MapUnits_val]
    rw [show Gamma0Map N ⟨γ, hγ⟩ = ((γ.val 1 1 : ℤ) : ZMod N) from rfl,
      ZMod.cast_intCast h_fac.dvd, hdiag]
    push_cast
    rw [Gamma1_mem] at hδ
    obtain ⟨_, hd_one, hc_zero⟩ := hδ
    rw [hd_one, hc_zero, zero_mul, sub_zero]
  rw [h_red, map_one]

/-- The action of `(levelRaiseMatrix l)⁻¹` on `ℍ` scales the underlying
ℂ-coordinate by `1/l`: `(α_l⁻¹ • z).coe = z.coe / l`. -/
lemma coe_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (z : UpperHalfPlane) :
    (((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane) : ℂ) = (↑z : ℂ) / (l : ℂ) := by
  have h_coe_eq : (((levelRaiseMatrix l) • ((levelRaiseMatrix l)⁻¹ • z) :
      UpperHalfPlane) : ℂ) = ((z : UpperHalfPlane) : ℂ) := by
    rw [smul_smul, mul_inv_cancel, one_smul]
  rw [coe_levelRaiseMatrix_smul] at h_coe_eq
  rwa [eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne l) : (l : ℂ) ≠ 0), mul_comm]

/-- The conjugation factor `σ` for `(levelRaiseMatrix l)⁻¹` is the
identity (positive determinant `1/l`). -/
lemma σ_levelRaiseMatrix_inv (l : ℕ) [NeZero l] :
    UpperHalfPlane.σ ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) = ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ
  rw [if_pos (levelRaiseMatrix_inv_det_pos l)]

/-- Inverse-slash equation: `g ∣[k] α_l⁻¹ = (l^(1-k)) • f`. -/
lemma slash_inv_eq_smul_of_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg_eq : g = levelRaiseFun l k f) :
    g ∣[k] ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) = ((l : ℂ) ^ (1 - k)) • f := by
  rw [hg_eq]
  change (((l : ℂ) ^ (1 - k)) • (f ∣[k] (levelRaiseMatrix l : GL (Fin 2) ℝ))) ∣[k]
      ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) = ((l : ℂ) ^ (1 - k)) • f
  rw [ModularForm.smul_slash, σ_levelRaiseMatrix_inv, ContinuousAlgEquiv.refl_apply,
    ← SlashAction.slash_mul,
    show (levelRaiseMatrix l : GL (Fin 2) ℝ) * (levelRaiseMatrix l)⁻¹ = 1
      from mul_inv_cancel _, SlashAction.slash_one]

/-- Slash-by-SL reduction: for any `A : SL(2, ℤ)`,
`f ∣[k] mapGL ℝ A = (l^(k-1)) • g ∣[k] ((levelRaiseMatrix l)⁻¹ * mapGL ℝ A)`. -/
lemma slash_eq_of_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (hg_eq : g = levelRaiseFun l k f) (A : SL(2, ℤ)) :
    f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ) =
      ((l : ℂ) ^ (k - 1)) •
        (g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
          (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  have hf_eq : f = ((l : ℂ) ^ (k - 1)) •
      (g ∣[k] ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ)) := by
    rw [slash_inv_eq_smul_of_levelRaiseFun_eq l k f g hg_eq, smul_smul,
      ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne l) : (l : ℂ) ≠ 0),
      show k - 1 + (1 - k) = 0 by ring, zpow_zero, one_smul]
  conv_lhs => rw [hf_eq]
  have hσA : UpperHalfPlane.σ (mapGL ℝ A : GL (Fin 2) ℝ) = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos (show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ A)).val by
      rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num)]
  rw [ModularForm.smul_slash, hσA, ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul]

private lemma levelRaiseMatrix_inv_apply_one_zero (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 0 = 0 := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

private lemma levelRaiseMatrix_inv_apply_one_one (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 1 = 1 := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

private lemma levelRaiseMatrix_inv_apply_zero_zero (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 0 = (l : ℝ)⁻¹ := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

private lemma levelRaiseMatrix_inv_apply_zero_one (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 1 = 0 := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

private lemma levelRaiseMatrix_inv_mul_mapGL_apply_one_zero (l : ℕ) [NeZero l]
    (A : SL(2, ℤ)) :
    (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) 1 0 =
      (A.val 1 0 : ℝ) := by
  rw [show (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) 1 0 =
      (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val *
        (mapGL ℝ A : GL (Fin 2) ℝ).val) 1 0 from rfl,
    Matrix.mul_apply, Fin.sum_univ_two, levelRaiseMatrix_inv_apply_one_zero,
    levelRaiseMatrix_inv_apply_one_one, zero_mul, one_mul, zero_add]
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

private lemma levelRaiseMatrix_inv_mul_mapGL_apply_zero_zero (l : ℕ) [NeZero l]
    (A : SL(2, ℤ)) :
    (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) 0 0 =
      (A.val 0 0 : ℝ) / (l : ℝ) := by
  rw [show (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) 0 0 =
      (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val *
        (mapGL ℝ A : GL (Fin 2) ℝ).val) 0 0 from rfl,
    Matrix.mul_apply, Fin.sum_univ_two, levelRaiseMatrix_inv_apply_zero_zero,
    levelRaiseMatrix_inv_apply_zero_one, zero_mul, add_zero,
    show ((mapGL ℝ A : GL (Fin 2) ℝ)) 0 0 = (A.val 0 0 : ℝ) by
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]]
  ring

private lemma gcd_levelRaise_first_col_ne_zero (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0) : ℤ) ≠ 0 := by
  intro hgcd
  rw [gcd_eq_zero_iff] at hgcd
  obtain ⟨ha, hlc⟩ := hgcd
  rcases mul_eq_zero.mp hlc with h | h
  · exact Nat.cast_ne_zero.mpr (NeZero.ne l) h
  · have hdet : A.val.det = 1 := A.property
    rw [Matrix.det_fin_two, ha, h] at hdet
    norm_num at hdet

/-- The `SL(2, ℤ)` cusp witness whose `mapGL ℝ`-image acts on `∞` to give the same
point as `(α_l)⁻¹ * mapGL ℝ A`. -/
noncomputable def cuspWitnessLevelRaiseInv (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    SL(2, ℤ) :=
  Classical.choose <|
    (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (gcd_levelRaise_first_col_ne_zero l A)).exists_SL2_col 0

private lemma cuspWitnessLevelRaiseInv_first_col (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (cuspWitnessLevelRaiseInv l A) 0 0 =
        A.val 0 0 / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) ∧
    (cuspWitnessLevelRaiseInv l A) 1 0 =
        ((l : ℤ) * A.val 1 0) / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) :=
  Classical.choose_spec
    ((isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (gcd_levelRaise_first_col_ne_zero l A)).exists_SL2_col 0)

private lemma mapGL_cuspWitnessLevelRaiseInv_apply_one_zero (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 1 0 =
      ((((l : ℤ) * A.val 1 0) / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) : ℤ) : ℝ) := by
  rw [show (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 1 0 =
        (algebraMap ℤ ℝ) ((cuspWitnessLevelRaiseInv l A).val 1 0) by
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix],
    (cuspWitnessLevelRaiseInv_first_col l A).2]
  simp

private lemma mapGL_cuspWitnessLevelRaiseInv_apply_zero_zero (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 0 0 =
      ((A.val 0 0 / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) : ℤ) : ℝ) := by
  rw [show (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 0 0 =
        (algebraMap ℤ ℝ) ((cuspWitnessLevelRaiseInv l A).val 0 0) by
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix],
    (cuspWitnessLevelRaiseInv_first_col l A).1]
  simp

open OnePoint in
private lemma mapGL_cuspWitnessLevelRaiseInv_smul_infty_eq (l : ℕ) [NeZero l]
    (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) =
      (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) • ∞ := by
  set d : ℤ := gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)
  have hd_real_ne : (d : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (gcd_levelRaise_first_col_ne_zero l A)
  rw [OnePoint.smul_infty_eq_ite, OnePoint.smul_infty_eq_ite,
    mapGL_cuspWitnessLevelRaiseInv_apply_one_zero,
    mapGL_cuspWitnessLevelRaiseInv_apply_zero_zero,
    levelRaiseMatrix_inv_mul_mapGL_apply_one_zero,
    levelRaiseMatrix_inv_mul_mapGL_apply_zero_zero,
    show (((A.val 0 0) / d : ℤ) : ℝ) = (A.val 0 0 : ℝ) / (d : ℝ) from
      Int.cast_div (gcd_dvd_left _ _) hd_real_ne,
    show ((((l : ℤ) * A.val 1 0) / d : ℤ) : ℝ) = ((l : ℝ) * A.val 1 0) / (d : ℝ) by
      rw [Int.cast_div (gcd_dvd_right _ _) hd_real_ne]; push_cast; ring]
  by_cases hc : (A.val 1 0 : ℝ) = 0
  · rw [if_pos (by rw [hc, mul_zero, zero_div] : ((l : ℝ) * (A.val 1 0 : ℝ)) / (d : ℝ) = 0),
      if_pos hc]
  · rw [if_neg (div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne l)) hc) hd_real_ne),
      if_neg hc]
    field_simp

open OnePoint in
/-- The cusp `(α_l⁻¹ * mapGL ℝ A) • ∞` is a cusp of any arithmetic subgroup
`Γ : Subgroup (GL (Fin 2) ℝ)`. -/
lemma isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty
    (l : ℕ) [NeZero l] (A : SL(2, ℤ))
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] :
    IsCusp ((((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
      (mapGL ℝ A : GL (Fin 2) ℝ)) • ∞) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨cuspWitnessLevelRaiseInv l A, (mapGL_cuspWitnessLevelRaiseInv_smul_infty_eq l A).symm⟩

/-- Slash zero-at-`i∞` reduction: for any `A : SL(2, ℤ)`, the zero-at-`i∞` of
`f ∣[k] mapGL ℝ A` is equivalent to the zero-at-`i∞` of
`g ∣[k] (α_l⁻¹ * mapGL ℝ A)`. -/
lemma isZeroAtImInfty_slash_iff_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg_eq : g = levelRaiseFun l k f) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
        (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) ↔
      UpperHalfPlane.IsZeroAtImInfty
        (g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
          (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  rw [slash_eq_of_levelRaiseFun_eq l k f g hg_eq A]
  have hc_norm_pos : 0 < ‖((l : ℂ) ^ (k - 1))‖ := by
    rw [norm_pos_iff]; exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne l))
  rw [UpperHalfPlane.isZeroAtImInfty_iff, UpperHalfPlane.isZeroAtImInfty_iff]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · obtain ⟨A_im, hbound⟩ := h (ε * ‖((l : ℂ) ^ (k - 1))‖) (mul_pos hε hc_norm_pos)
    refine ⟨A_im, fun τ hτ ↦ ?_⟩
    have h := hbound τ hτ
    rw [Pi.smul_apply, smul_eq_mul, norm_mul] at h
    rwa [mul_comm, ← le_div_iff₀ hc_norm_pos, mul_div_assoc, div_self hc_norm_pos.ne',
      mul_one] at h
  · obtain ⟨A_im, hbound⟩ := h (ε / ‖((l : ℂ) ^ (k - 1))‖) (div_pos hε hc_norm_pos)
    refine ⟨A_im, fun τ hτ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    have h := hbound τ hτ
    rwa [le_div_iff₀ hc_norm_pos, mul_comm] at h

open OnePoint in
/-- Zero-at-`i∞` of `g ∣[k] (α_l⁻¹ * mapGL ℝ A)` for `g : CuspForm`. -/
lemma isZeroAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL (l N : ℕ) [NeZero l] [NeZero N]
    (k : ℤ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
      (⇑g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
        (mapGL ℝ A : GL (Fin 2) ℝ))) :=
  CuspFormClass.zero_at_cusps g
    (isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty l A ((Gamma1 N).map (mapGL ℝ))) _ rfl

/-- All-SL2 zero-at-`i∞` for `f`: `IsZeroAtImInfty (f ∣[k] mapGL ℝ A)` for
every `A : SL(2, ℤ)`. -/
lemma isZeroAtImInfty_slash_mapGL_of_levelRaiseFun_eq (l N : ℕ) [NeZero l] [NeZero N]
    (k : ℤ) (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_eq : ⇑g = levelRaiseFun l k f) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) := by
  rw [isZeroAtImInfty_slash_iff_levelRaiseFun_eq l k f ⇑g hg_eq A]
  exact isZeroAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL l N k g A

open OnePoint in
/-- All-cusp vanishing theorem: the candidate lower-level form `f` vanishes at
every cusp of `(Gamma1 (N/l)).map (mapGL ℝ)`. -/
theorem zero_at_cusps_of_levelRaiseFun_eq (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (k : ℤ) (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_eq : ⇑g = levelRaiseFun l k f) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 (N / l)).map (mapGL ℝ))) :
    OnePoint.IsZeroAt c f k := by
  haveI : NeZero (N / l) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) h_dvd) (Nat.pos_of_neZero l)).ne'⟩
  have hc_SL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
  rw [OnePoint.isZeroAt_iff_exists_SL2Z hc_SL]
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc_SL
  refine ⟨γ, hγ.symm, ?_⟩
  rw [ModularForm.SL_slash]
  exact isZeroAtImInfty_slash_mapGL_of_levelRaiseFun_eq l N k f g hg_eq γ

/-- A cusp form is canonically a modular form via the inclusion
`c.IsZeroAt → c.IsBoundedAt`. -/
def cuspFormToModularForm {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (g : CuspForm Γ k) :
    ModularForm Γ k where
  toFun := g.toFun
  slash_action_eq' := g.slash_action_eq'
  holo' := g.holo'
  bdd_at_cusps' hc := fun M hM ↦ (g.zero_at_cusps' hc M hM).isBoundedAtImInfty

@[simp]
lemma cuspFormToModularForm_coe {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (g : CuspForm Γ k) :
    ⇑(cuspFormToModularForm g) = ⇑g := rfl

/-- A cusp form lies in the modular-form Nebentypus eigenspace iff it lies in
the cusp-form Nebentypus eigenspace. -/
lemma cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
    {N : ℕ} [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    cuspFormToModularForm g ∈ modFormCharSpace k χ₀ ↔
      g ∈ cuspFormCharSpace k χ₀ := by
  rw [modFormCharSpace_iff_nebentypus, cuspFormCharSpace_iff_nebentypus]
  simp [cuspFormToModularForm_coe]

/-- Case A lowered cusp form bundle: under the Case A hypotheses with
`g : CuspForm`, the candidate function `f` bundles into a `CuspForm` at the
lowered level `(Gamma1 (N/l)).map (mapGL ℝ)`. -/
noncomputable def conductorTheoremCaseA_cuspForm (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h_fac : χ.FactorsThrough (N / l)) (f : UpperHalfPlane → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k where
  toFun := f
  slash_action_eq' γ hγ_mem := by
    obtain ⟨δ, hδ_mem, hδ_eq⟩ := Subgroup.mem_map.mp hγ_mem
    rw [← hδ_eq]
    exact conductor_slash_eq_self_of_mem_Gamma1_div l N h_dvd k χ h_fac f
      (cuspFormToModularForm g)
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char) hg_eq hf_period δ hδ_mem
  holo' := mdifferentiable_of_levelRaiseFun_eq l k f ⇑g (CuspFormClass.holo g) hg_eq
  zero_at_cusps' hc := zero_at_cusps_of_levelRaiseFun_eq l N h_dvd k f g hg_eq hc

/-- The bundled `conductorTheoremCaseA_cuspForm` has underlying function `f`. -/
@[simp]
lemma conductorTheoremCaseA_cuspForm_apply (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (k : ℤ) (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    ⇑(conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g hg_char hg_eq hf_period) = f :=
  rfl

/-- Unit extraction from `¬ FactorsThrough`: if `χ : DirichletCharacter ℂ N`
does not factor through level `d`, there is a unit `u : (ZMod N)ˣ` with
`ZMod.unitsMap hd u = 1` and `χ.toUnitHom u ≠ 1`. -/
lemma exists_unit_of_not_factorsThrough {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 ∧ χ.toUnitHom u ≠ 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨u, hu_ker, hu_chi⟩ := SetLike.not_le_iff_exists.mp h_not_fac
  exact ⟨u, MonoidHom.mem_ker.mp hu_ker, hu_chi ∘ MonoidHom.mem_ker.mpr⟩

private lemma natCast_eq_mul_natCast_div {l N : ℕ} (h_dvd : l ∣ N) :
    (N : ℤ) = (l : ℤ) * ((N / l : ℕ) : ℤ) := by
  rw [mul_comm]; exact mod_cast (Nat.div_mul_cancel h_dvd).symm

/-- Algebraic two-multiplier contradiction: if `f ∣[k] M` is both `c₁ • f` and
`c₂ • f` for two distinct scalars, then `f = 0`. -/
lemma fun_eq_zero_of_two_multipliers (k : ℤ) (f : UpperHalfPlane → ℂ) (M : GL (Fin 2) ℝ)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) (h₁ : f ∣[k] M = c₁ • f) (h₂ : f ∣[k] M = c₂ • f) : f = 0 := by
  have h_diff : (c₁ - c₂) • f = 0 := by rw [sub_smul, h₁.symm.trans h₂, sub_self]
  exact (smul_eq_zero.mp h_diff).resolve_left (sub_ne_zero.mpr hne)

/-- Controlled `Γ₀(N)` lift of `u : (ZMod N)ˣ`: the Bezout-style matrix
`!![a, b; N, e]` with `a = (u⁻¹ : ZMod N).val`, `e = (u : ZMod N).val`, and
`b = (a*e - 1) / N`. -/
noncomputable def gamma0LiftLowerLeftN (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ↥(Gamma0 N) := by
  let e : ℤ := ((u.val : ZMod N).val : ℤ)
  let a : ℤ := ((u⁻¹.val : ZMod N).val : ℤ)
  have h_ae : ((a * e : ℤ) : ZMod N) = 1 := by
    show (((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ)) : ℤ) : ZMod N) = 1
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have h_dvd : (N : ℤ) ∣ (a * e - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show ((a : ZMod N) * (e : ZMod N) - 1 : ZMod N) = ((a * e : ℤ) : ZMod N) - 1 by
        push_cast; ring, h_ae]
    ring
  let b : ℤ := (a * e - 1) / (N : ℤ)
  refine ⟨⟨!![a, b; (N : ℤ), e], ?det⟩, ?gamma0⟩
  · rw [Matrix.det_fin_two_of]
    show a * e - b * (N : ℤ) = 1
    linarith [Int.ediv_mul_cancel h_dvd]
  · rw [Gamma0_mem]
    show (((N : ℤ) : ℤ) : ZMod N) = 0
    simp

/-- The `(1, 0)` entry of `gamma0LiftLowerLeftN N u` equals `N`. -/
@[simp]
lemma gamma0LiftLowerLeftN_lower_left (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 : ℤ) = (N : ℤ) := rfl

/-- The `(1, 1)` entry of `gamma0LiftLowerLeftN N u` is `(u : ZMod N).val`. -/
@[simp]
lemma gamma0LiftLowerLeftN_lower_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1 : ℤ) =
      ((u.val : ZMod N).val : ℤ) := rfl

/-- The `(0, 0)` entry of `gamma0LiftLowerLeftN N u` is `(u⁻¹ : ZMod N).val`. -/
@[simp]
lemma gamma0LiftLowerLeftN_upper_left (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 0 : ℤ) =
      ((u⁻¹.val : ZMod N).val : ℤ) := rfl

/-- `Gamma0MapUnits` of the controlled lift recovers the original unit. -/
@[simp]
lemma gamma0LiftLowerLeftN_Gamma0MapUnits (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    Gamma0MapUnits (gamma0LiftLowerLeftN N u) = u := by
  apply Units.ext
  change ((((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1 : ℤ)) : ZMod N) = (u : ZMod N)
  rw [gamma0LiftLowerLeftN_lower_right]
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- Case B slash relation with controlled lift: under `¬ χ.FactorsThrough (N/l)`,
there exist `u : (ZMod N)ˣ` (lifted via `gamma0LiftLowerLeftN` with `γ_u.val 1 0 = N`),
`δ ∈ Γ₁(N/l)` and `c : ℂ` with `c ≠ 1` such that `f ∣[k] mapGL ℝ δ = c • f`. -/
lemma case_B_slash_relation_with_controlled_lift (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h_not_fac : ¬ χ.FactorsThrough (N / l)) (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f) :
    ∃ (u : (ZMod N)ˣ),
      ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u = 1 ∧
      χ.toUnitHom u ≠ 1 ∧
      ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 : ℤ) = (N : ℤ) ∧
      f ∣[k]
        (mapGL ℝ
          (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
            (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
              (gamma0LiftLowerLeftN N u).property))
        : GL (Fin 2) ℝ) =
        (χ.toUnitHom u : ℂ) • f := by
  obtain ⟨u, hu_ker, hu_chi⟩ :=
    exists_unit_of_not_factorsThrough ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ h_not_fac
  refine ⟨u, hu_ker, hu_chi, gamma0LiftLowerLeftN_lower_left N u, ?_⟩
  have h_slash := conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq
    (gamma0LiftLowerLeftN N u : SL(2, ℤ)) (gamma0LiftLowerLeftN N u).property
  rwa [show Gamma0MapUnits ⟨(gamma0LiftLowerLeftN N u : SL(2, ℤ)),
      (gamma0LiftLowerLeftN N u).property⟩ = u from
    gamma0LiftLowerLeftN_Gamma0MapUnits N u] at h_slash

/-- Multiplicative character separation in the kernel: given `u : (ZMod N)ˣ`
and `χ` not factoring through level `d`, there is a kernel element `v` (with
`ZMod.unitsMap hd v = 1`) such that `χ.toUnitHom (u * v) ≠ χ.toUnitHom u`. -/
lemma exists_kernel_unit_with_char_shift {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ v : (ZMod N)ˣ, ZMod.unitsMap hd v = 1 ∧ χ.toUnitHom (u * v) ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_unit_of_not_factorsThrough hd h_not_fac
  refine ⟨v, hv_ker, fun h ↦ hv_chi <| mul_left_cancel <|
    show χ.toUnitHom u * χ.toUnitHom v = χ.toUnitHom u * 1 by rw [← map_mul, h, mul_one]⟩

/-- Coset character separation: under `¬ χ.FactorsThrough d`, for any
`u : (ZMod N)ˣ` there exists `u' : (ZMod N)ˣ` in the same `ZMod.unitsMap hd`-coset
as `u` with `χ.toUnitHom u' ≠ χ.toUnitHom u`. -/
lemma exists_alt_unit_in_coset_with_char_separation {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ.toUnitHom u' ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_kernel_unit_with_char_shift hd h_not_fac u
  exact ⟨u * v, by rw [map_mul, hv_ker, mul_one], hv_chi⟩

/-- Generalized integer-shift bridge: if two units `u, u'` lie in the same
`ZMod.unitsMap hd`-coset, then `(N/l) ∣ (u.val.val - u'.val.val)` in `ℤ`. -/
lemma natCast_val_sub_dvd_of_unitsMap_eq {N l : ℕ} [NeZero N] [NeZero l] (h_dvd : l ∣ N)
    (u u' : (ZMod N)ˣ)
    (h_eq : ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u =
            ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u') :
    ((N / l : ℕ) : ℤ) ∣ (((u : ZMod N).val : ℤ) - ((u' : ZMod N).val : ℤ)) := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  have h_cast_eq : ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) := by
    have hh := congr_arg Units.val h_eq
    rwa [ZMod.unitsMap_val, ZMod.unitsMap_val] at hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val (u : ZMod N), ZMod.natCast_val (u' : ZMod N),
    show (ZMod.cast ((u : ZMod N) : ZMod N) : ZMod (N / l)) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) from rfl,
    show (ZMod.cast ((u' : ZMod N) : ZMod N) : ZMod (N / l)) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) from rfl, h_cast_eq]
  ring

/-- The `(0, 1)` entry of the controlled lift `gamma0LiftLowerLeftN N u` is
the Bezout coefficient `b = (a*e - 1) / N` (where `a = u⁻¹.val.val`,
`e = u.val.val`). -/
@[simp]
lemma gamma0LiftLowerLeftN_upper_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1 : ℤ) =
      (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
        (N : ℤ) := rfl

private lemma t_factor_matrix_identity {l Nl i j a a' e e' b b' : ℤ} (hNl : Nl ≠ 0)
    (h_i : i * Nl = a - a') (h_j : j * Nl = e - e')
    (h_det : a * e - b * (l * Nl) = 1) (h_det' : a' * e' - b' * (l * Nl) = 1) :
    (!![a, l * b; Nl, e] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), i; 0, 1] * !![a', l * b'; Nl, e'] * !![(1 : ℤ), j; 0, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · lia
  · apply mul_left_cancel₀ hNl
    linear_combination -h_det + h_det' + (-e' - Nl * j) * h_i + (-a) * h_j
  · lia

private lemma N_dvd_inv_val_mul_val_sub_one (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (N : ℤ) ∣ (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    show u⁻¹.val * u.val = 1 by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
  ring

private lemma controlled_lift_det_identity (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) -
      ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) / (N : ℤ)) * (N : ℤ) =
        1 := by
  linarith [Int.ediv_mul_cancel (N_dvd_inv_val_mul_val_sub_one N u)]

private lemma levelRaiseConjOfDvd_gamma0LiftLowerLeftN_val (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (u : (ZMod N)ˣ) :
    (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
        (gamma0LiftLowerLeftN N u).property)).val =
      (!![((u⁻¹.val : ZMod N).val : ℤ),
          (l : ℤ) * ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
            (N : ℤ));
          ((N / l : ℕ) : ℤ), ((u.val : ZMod N).val : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) := by
  change (Matrix.of !![(gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 0,
      (l : ℤ) * (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1;
      (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 / l,
      (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1] : Matrix _ _ ℤ) = _
  have h_div_eq : (N : ℤ) / (l : ℤ) = ((N / l : ℕ) : ℤ) := by
    rw [natCast_eq_mul_natCast_div h_dvd,
      Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne l))]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      gamma0LiftLowerLeftN_upper_left, gamma0LiftLowerLeftN_upper_right,
      gamma0LiftLowerLeftN_lower_left, gamma0LiftLowerLeftN_lower_right, h_div_eq]

/-- Explicit T-factor with character separation: under `¬ χ.FactorsThrough (N/l)`
and given a unit `u`, there are integers `(i, j)` and a separating unit `u'`
in the same `unitsMap`-coset as `u` with `χ.toUnitHom u' ≠ χ.toUnitHom u` and
`levelRaiseConjOfDvd l γ_u = T^i · levelRaiseConjOfDvd l γ' · T^j`, where
`γ_u = gamma0LiftLowerLeftN N u` and `γ' = gamma0LiftLowerLeftN N u'`. -/
theorem exists_T_factor_with_char_separation (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (u : (ZMod N)ˣ) :
    ∃ (i j : ℤ) (u' : (ZMod N)ˣ),
      χ.toUnitHom u' ≠ χ.toUnitHom u ∧
      levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
        (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
          (gamma0LiftLowerLeftN N u).property) =
      (ModularGroup.T : SL(2, ℤ)) ^ i *
        levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u' : SL(2, ℤ))
          (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
            (gamma0LiftLowerLeftN N u').property) *
        (ModularGroup.T : SL(2, ℤ)) ^ j := by
  obtain ⟨u', hu'_coset, hu'_chi⟩ :=
    exists_alt_unit_in_coset_with_char_separation
      ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ h_not_fac u
  set a₀ : ℤ := ((u⁻¹.val : ZMod N).val : ℤ)
  set e₀ : ℤ := ((u.val : ZMod N).val : ℤ)
  set a₀' : ℤ := ((u'⁻¹.val : ZMod N).val : ℤ)
  set e₀' : ℤ := ((u'.val : ZMod N).val : ℤ)
  set b₀ : ℤ := (a₀ * e₀ - 1) / (N : ℤ)
  set b₀' : ℤ := (a₀' * e₀' - 1) / (N : ℤ)
  set Nl : ℤ := ((N / l : ℕ) : ℤ)
  have h_dvd_a : Nl ∣ (a₀ - a₀') := by
    apply natCast_val_sub_dvd_of_unitsMap_eq h_dvd u⁻¹ u'⁻¹
    rw [map_inv, map_inv, hu'_coset]
  set i : ℤ := (a₀ - a₀') / Nl
  set j : ℤ := (e₀ - e₀') / Nl
  refine ⟨i, j, u', hu'_chi, ?_⟩
  have hN_eq : (N : ℤ) = (l : ℤ) * Nl := natCast_eq_mul_natCast_div h_dvd
  have hNl_ne : Nl ≠ 0 := by
    show ((N / l : ℕ) : ℤ) ≠ 0
    exact mod_cast (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) h_dvd)
      (Nat.pos_of_neZero l)).ne'
  have h_det_u : a₀ * e₀ - b₀ * ((l : ℤ) * Nl) = 1 := by
    rw [← hN_eq]; exact controlled_lift_det_identity N u
  have h_det_u' : a₀' * e₀' - b₀' * ((l : ℤ) * Nl) = 1 := by
    rw [← hN_eq]; exact controlled_lift_det_identity N u'
  have h_mat_id :
      (!![a₀, (l : ℤ) * b₀; Nl, e₀] : Matrix (Fin 2) (Fin 2) ℤ) =
        !![(1 : ℤ), i; 0, 1] * !![a₀', (l : ℤ) * b₀'; Nl, e₀'] *
          !![(1 : ℤ), j; 0, 1] :=
    t_factor_matrix_identity hNl_ne (Int.ediv_mul_cancel h_dvd_a)
      (Int.ediv_mul_cancel
        (natCast_val_sub_dvd_of_unitsMap_eq h_dvd u u' hu'_coset.symm))
      h_det_u h_det_u'
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
  rwa [levelRaiseConjOfDvd_gamma0LiftLowerLeftN_val l N h_dvd u,
    levelRaiseConjOfDvd_gamma0LiftLowerLeftN_val l N h_dvd u']

/-- Case B vanishing theorem: under `¬ χ.FactorsThrough (N/l)` plus the period-1
hypothesis on `f`, the candidate lower-level form `f` vanishes. -/
theorem conductorTheoremCaseB_vanishing (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (k : ℤ) (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    f = 0 := by
  obtain ⟨u, _, _, _, h_slash⟩ :=
    case_B_slash_relation_with_controlled_lift l N h_dvd k χ h_not_fac f g hg_char hg_eq
  obtain ⟨i, j, u', hu'_chi, h_mat_id⟩ :=
    exists_T_factor_with_char_separation l N h_dvd χ h_not_fac u
  have h_slash_alt := conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period
    i j (gamma0LiftLowerLeftN N u' : SL(2, ℤ)) (gamma0LiftLowerLeftN N u').property
  rw [gamma0LiftLowerLeftN_Gamma0MapUnits, ← h_mat_id] at h_slash_alt
  exact fun_eq_zero_of_two_multipliers k f _
    (fun h ↦ hu'_chi.symm (Units.ext h)) h_slash h_slash_alt

private lemma unitsMap_Gamma0MapUnits_lift_eq_of_diag (l N : ℕ) [NeZero N] [NeZero (N / l)]
    (h_dvd : l ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (γ'_pkg : ↥(Gamma0 (N / l)))
    (j : ℤ) (hdiag : γ.val 1 1 =
      (γ'_pkg : SL(2, ℤ)).val 1 1 - (γ'_pkg : SL(2, ℤ)).val 1 0 * j) :
    ZMod.unitsMap (⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ : (N / l) ∣ N)
        (Gamma0MapUnits ⟨γ, hγ⟩) =
      Gamma0MapUnits γ'_pkg := by
  apply Units.ext
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  have hLHS_eq : (ZMod.unitsMap hNl_dvd_N (Gamma0MapUnits ⟨γ, hγ⟩)).val =
      (((γ.val 1 1 : ℤ)) : ZMod (N / l)) := by
    rw [ZMod.unitsMap_val]
    exact ZMod.cast_intCast hNl_dvd_N (γ.val 1 1)
  rw [hLHS_eq]
  change (((γ.val 1 1 : ℤ)) : ZMod (N / l)) =
    (((γ'_pkg : SL(2, ℤ)).val 1 1 : ℤ) : ZMod (N / l))
  rw [hdiag]
  have h10_zero : (((γ'_pkg : SL(2, ℤ)).val 1 0 : ℤ) : ZMod (N / l)) = 0 := by
    have hγ' := γ'_pkg.property
    rwa [Gamma0_mem] at hγ'
  push_cast
  rw [h10_zero]
  ring

/-- Lowered character space membership for the cusp-form Case A bundle: the
bundle `conductorTheoremCaseA_cuspForm` lies in
`cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom`. -/
theorem conductorTheoremCaseA_cuspForm_mem_cuspFormCharSpace (l N : ℕ) [NeZero l] [NeZero N]
    [NeZero (N / l)] (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h_fac : χ.FactorsThrough (N / l)) (f : UpperHalfPlane → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g hg_char hg_eq hf_period ∈
      cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom := by
  rw [cuspFormCharSpace_iff_nebentypus]
  intro γ'_pkg
  rw [conductorTheoremCaseA_cuspForm_apply]
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd γ'_pkg.val γ'_pkg.property
  rw [hfact, conductor_slash_T_conj_eq l N h_dvd k χ f (cuspFormToModularForm g)
    ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      k χ.toUnitHom g).mpr hg_char) hg_eq hf_period i j γ hγ]
  congr 2
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  congr 1
  exact unitsMap_Gamma0MapUnits_lift_eq_of_diag l N h_dvd γ hγ γ'_pkg j hdiag

/-- Strengthened cusp-form dichotomy: the cusp-form analogue of
`conductor_theorem_dichotomy_strong`. -/
theorem conductor_theorem_dichotomy_cuspForm_strong (l N : ℕ) [NeZero l] [NeZero N]
    [NeZero (N / l)] (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom) (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ h_fac : χ.FactorsThrough (N / l),
      ∃ F : CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k,
        F ∈ cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom ∧ ⇑F = f) ∨ f = 0 := by
  classical
  by_cases h_fac : χ.FactorsThrough (N / l)
  · exact .inl ⟨h_fac,
      conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g hg_char hg_eq hf_period,
      conductorTheoremCaseA_cuspForm_mem_cuspFormCharSpace l N h_dvd k χ h_fac f g hg_char
        hg_eq hf_period,
      conductorTheoremCaseA_cuspForm_apply l N h_dvd k χ h_fac f g hg_char hg_eq hf_period⟩
  · exact .inr <| conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f
      (cuspFormToModularForm g)
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace k χ.toUnitHom
        g).mpr hg_char) hg_eq hf_period

end HeckeRing.GL2

end

