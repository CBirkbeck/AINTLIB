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
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: character decomposition, the `Newform` structure, and the Main Lemma

Character-space decomposition of the old/new subspaces, the `Newform` structure (DS Def 5.8.1),
primitive forms, the eigenvalue-as-Fourier-coefficient identity, and the Atkin-Lehner Main Lemma
(DS Thm 5.7.1) with its uniqueness corollary.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

section CharSpaceDecomposition

/-- **`diamondOpCuspHom`-invariance of `cuspFormsOld N k`.** -/
lemma diamondOpCuspHom_preserves_cuspFormsOld
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsOld N k) :
    diamondOpCuspHom k d f ∈ cuspFormsOld N k :=
  diamondOp_preserves_cuspFormsOld d f hf

/-- **`diamondOpCuspHom`-invariance of `cuspFormsNew N k`.** -/
lemma diamondOpCuspHom_preserves_cuspFormsNew
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNew N k) :
    diamondOpCuspHom k d f ∈ cuspFormsNew N k :=
  diamondOp_preserves_cuspFormsNew d f hf

/-- **Finsupp-indexed character decomposition of a newform subspace element.**
Every `f ∈ cuspFormsNew N k` is a finitely-supported sum of Nebentypus
components, each simultaneously in `cuspFormsNew N k` and in its character
subspace. -/
theorem exists_finsupp_charSpace_of_cuspFormsNew (k : ℤ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y ↦ y) = f :=
  exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k (cuspFormsNew N k)
    diamondOpCuspHom_preserves_cuspFormsNew hf

end CharSpaceDecomposition

/-- A **newform** of level Γ₁(N) and weight k: a cusp form that is
1. an eigenform (common eigenfunction of all T_n with (n,N)=1)
2. in the new subspace
3. normalised: a_1(f) = 1

By Atkin-Lehner uniqueness (DS Theorem 5.8.2), newforms are uniquely determined
by their Hecke eigenvalues away from the level. -/
@[ext]
structure Newform (N : ℕ) [NeZero N] (k : ℤ)
    extends Eigenform N k where
  /-- The form is in the new subspace. -/
  isNew : toCuspForm ∈ cuspFormsNewExtended N k
  /-- Normalisation at the **canonical Fourier period** (`h = 1`): the first
  Fourier coefficient is `1`, i.e. `a₁ = 1` (the Diamond–Shurman / Miyake
  normalisation). -/
  isNorm : (UpperHalfPlane.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

/-- The **conductor** of a `Newform N k` is the smallest level at which `f`
arises as a `Newform`; for a bundled `Newform N k` this is `N` itself. -/
noncomputable def Newform.conductor (_f : Newform N k) : ℕ := N

private lemma qExpansion_one_coeff_one_smul_of_norm
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_norm : (UpperHalfPlane.qExpansion (1 : ℝ) f.toModularForm').coeff 1 = 1)
    (c : ℂ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (c • f)).coeff 1 = c := by
  change (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(c • f : CuspForm _ k))).coeff 1 = c
  rw [show (⇑(c • f : CuspForm _ k) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, smul_eq_mul, h_norm, mul_one]

lemma qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_char : f.toModularForm' ∈ modFormCharSpace k χ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n f)).coeff 1 =
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n := by
  rw [show (⇑(heckeT_n_cusp k n f) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k n f).toModularForm' from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl, heckeT_n_cusp_toModularForm']
  have h := fourierCoeff_heckeT_n_period_one (N := N) k n hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simpa only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] using h

/-- For a `Newform` `f` in the character eigenspace `modFormCharSpace k χ`, the
eigenvalue at `n` (coprime to `N`) equals the `n`-th canonical Fourier
coefficient of `f` (period `h = 1`). -/
theorem Newform.eigenvalue_eq_coeff (f : Newform N k) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue n =
      (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  rw [← qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff n.val hn χ f.toCuspForm hf_char,
    f.isEigen n hn]
  exact (qExpansion_one_coeff_one_smul_of_norm f.toCuspForm f.isNorm _).symm

/-- **The Main Lemma** (DS Theorem 5.7.1, Atkin-Lehner [AL70]):
If `f ∈ S_k(Γ₁(N))` has Fourier expansion `f(τ) = Σ aₙ qⁿ` with `aₙ = 0`
whenever `(n, N) = 1`, then `f` is an oldform.

This is the technical heart of the newform theory; the full proof requires the
spectral theorem for Hecke operators and the Petersson adjoint formula. -/
theorem mainLemma
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  -- Decompose `f = f_old + f_new`; for each eigenform `g ∈ cuspFormsNew` with
  -- eigenvalue `λ_n ≠ 0`, the adjoint relation gives `⟨f, g⟩ = λ_n⁻¹ ⟨T_n f, g⟩`,
  -- which vanishes since `a_n(f) = 0` for coprime `n`, forcing `f_new = 0`.  The
  -- inputs (`exists_simultaneous_eigenform_basis`, `heckeT_n_adjoint`) are not yet
  -- available, so the conclusion is left unproved.
  sorry

end HeckeRing.GL2
