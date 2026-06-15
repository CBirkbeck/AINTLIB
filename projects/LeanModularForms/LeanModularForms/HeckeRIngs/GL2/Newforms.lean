/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms umbrella (Phase 6)

This file collects the newform-theory development following Diamond–Shurman
§§5.6–5.8 and Atkin–Lehner [AL70]. It re-exports the eigenform/newform
structures, predicates and old/new submodules of `Newforms.Basic` (through
`Newforms.CoeffSeq` and `Newforms.MainLemma`, which also provide the
Atkin–Lehner main lemma), together with the supporting level-raising,
character-decomposition, Petersson, dimension-formula and L-function theory.

It also proves `exists_levelRaise_preimage_of_coeff_support_multiples`: a cusp
form on `Γ₁(N)` whose `q`-expansion is supported on multiples of `l ∣ N` is the
level-raise of a `T`-invariant function.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §§5.6–5.8
* [AL70] Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970)
* [Miy] Miyake, *Modular Forms*, §4.6
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

private lemma levelRaiseMatrix_inv_smul_vadd_one_eq {l : ℕ} [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l)⁻¹ • ((1 : ℝ) +ᵥ τ) : UpperHalfPlane) =
      ((1 : ℝ) / (l : ℝ)) +ᵥ ((levelRaiseMatrix l)⁻¹ • τ) := by
  apply UpperHalfPlane.ext
  simp only [coe_levelRaiseMatrix_inv_smul, UpperHalfPlane.coe_vadd]
  push_cast
  ring

private lemma smul_qParam_pow_shift_eq {l : ℕ} [NeZero l] {c : ℕ → ℂ}
    (hc : ∀ n : ℕ, ¬ l ∣ n → c n = 0) (σ : UpperHalfPlane) (n : ℕ) :
    c n • Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) ^ n =
      c n • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n := by
  have hqP :
      Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) =
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) := by
    simp only [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  by_cases hln : l ∣ n
  · obtain ⟨m, rfl⟩ := hln
    rw [hqP, mul_pow, pow_mul (Complex.exp _) l m,
      (Complex.isPrimitiveRoot_exp l (NeZero.ne l)).pow_eq_one, one_pow, mul_one]
  · rw [hc n hln, zero_smul, zero_smul]

private lemma levelRaisePreimage_slash_T_eq {N : ℕ} [NeZero N] {l : ℕ} [NeZero l] {k : ℤ}
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n → (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0) :
    (fun τ ↦ (⇑g : UpperHalfPlane → ℂ) ((levelRaiseMatrix l)⁻¹ • τ)) ∣[k]
        (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) =
      fun τ ↦ (⇑g : UpperHalfPlane → ℂ) ((levelRaiseMatrix l)⁻¹ • τ) := by
  funext τ
  change ((fun τ' ↦ (⇑g : UpperHalfPlane → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
      (ModularGroup.T : SL(2, ℤ))) τ = (⇑g : UpperHalfPlane → ℂ) ((levelRaiseMatrix l)⁻¹ • τ)
  rw [modular_slash_T_apply]
  set σ : UpperHalfPlane := (levelRaiseMatrix l)⁻¹ • τ
  rw [levelRaiseMatrix_inv_smul_vadd_one_eq τ]
  set σ' : UpperHalfPlane := ((1 : ℝ) / (l : ℝ)) +ᵥ σ
  have h1_period := one_mem_strictPeriods_Gamma1_map N
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨((Gamma1 N).map (mapGL ℝ)).isCusp_of_mem_strictPeriods one_pos h1_period⟩
  have key := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g h1_period) (ModularFormClass.holo g)
    (ModularFormClass.bdd_at_infty g)
  have Hσ' := key σ'
  rw [funext (smul_qParam_pow_shift_eq hg_supp σ)] at Hσ'
  exact ((key σ).unique Hσ').symm

/-- A cusp form on `Γ₁(N)` whose `q`-expansion is supported on multiples of `l ∣ N` is the
level-raise of a function invariant under the weight-`k` slash action of `T`. -/
theorem exists_levelRaise_preimage_of_coeff_support_multiples {N : ℕ} [NeZero N] {l : ℕ}
    [NeZero l] (_hl : 1 < l) (_hlN : l ∣ N) {k : ℤ} (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n → (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0) :
    ∃ f : UpperHalfPlane → ℂ, (⇑g : UpperHalfPlane → ℂ) = levelRaiseFun l k f ∧
      f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f := by
  refine ⟨fun τ ↦ (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ), ?_,
    levelRaisePreimage_slash_T_eq g hg_supp⟩
  funext τ
  rw [levelRaiseFun_apply, ← mul_smul, inv_mul_cancel, one_smul]

end HeckeRing.GL2
