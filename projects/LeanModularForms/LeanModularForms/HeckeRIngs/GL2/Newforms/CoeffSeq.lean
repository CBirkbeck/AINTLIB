/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma

/-!
# Newforms: minimal coefficient-sequence API

This file is the slim survivor of the original `CoeffSeq.lean` after the
Fricke + bad-prime + L-series chain was quarantined.  Only the three
identifiers consumed outside `Newforms/` survive:

* `Newform.isNormalisedEigenform` — period-1 normalised-eigenform witness
  at the `ModularForm` level
* `Newform.eigenvalue_coprime_mul` — coprime multiplicativity of
  eigenvalues `λ_{mn} = λ_m · λ_n`
* `Newform.dirichletLift` — the canonical lift of a Newform character to
  a Mathlib `DirichletCharacter ℂ N`
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The underlying modular form of a `Newform` is a period-1 normalised
eigenform (`IsNormalisedEigenform_one`) at the `ModularForm` level. -/
theorem Newform.isNormalisedEigenform (f : Newform N k) :
    IsNormalisedEigenform_one k f.toCuspForm.toModularForm' := by
  refine ⟨?_, ?_⟩
  · intro n' hn'
    haveI : NeZero n'.val := ⟨n'.pos.ne'⟩
    refine ⟨f.eigenvalue n', ?_⟩
    have h_lift : (heckeT_n_cusp k n'.val f.toCuspForm).toModularForm' =
        (f.eigenvalue n' • f.toCuspForm).toModularForm' := by rw [f.isEigen n' hn']
    rw [heckeT_n_cusp_toModularForm'] at h_lift
    exact h_lift
  · exact f.isNorm

/-- **Coprime multiplicativity of eigenvalues**: if `f` is a newform in the
character eigenspace `modFormCharSpace k χ` and `gcd(m, n) = 1`, then
`λ_{mn} = λ_m · λ_n`. -/
theorem Newform.eigenvalue_coprime_mul (f : Newform N k) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (hn : Nat.Coprime n.val N)
    (hmn : Nat.Coprime m.val n.val) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ =
      f.eigenvalue m * f.eigenvalue n := by
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have hmn_N : Nat.Coprime (m.val * n.val) N := hm.mul_left hn
  rw [Newform.eigenvalue_eq_coeff f ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩
        hmn_N χ hf_char,
      Newform.eigenvalue_eq_coeff f m hm χ hf_char,
      Newform.eigenvalue_eq_coeff f n hn χ hf_char]
  change (UpperHalfPlane.qExpansion (1 : ℝ)
        f.toCuspForm.toModularForm').coeff (m.val * n.val) =
      (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff m.val *
      (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff n.val
  have h := eigenform_coeff_multiplicative_one k m n hm hn χ hf_char
    f.isNormalisedEigenform
  have hgcd : Nat.gcd m.val n.val = 1 := hmn
  rw [hgcd, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
  exact h.symm

/-- **Dirichlet character lift.**  The Newform character
`χ : (ZMod N)ˣ →* ℂˣ` lifts to a Mathlib `DirichletCharacter ℂ N` via
the canonical extension by zero on non-units (`MulChar.ofUnitHom`). -/
noncomputable def Newform.dirichletLift (χ : (ZMod N)ˣ →* ℂˣ) :
    DirichletCharacter ℂ N := MulChar.ofUnitHom χ

end HeckeRing.GL2
