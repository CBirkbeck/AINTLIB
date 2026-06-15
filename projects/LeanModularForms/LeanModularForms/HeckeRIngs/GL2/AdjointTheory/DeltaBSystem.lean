/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.SummandAdjoint

/-!
# Hecke adjoint theory: DS-standard `δ_b` representative system.

Third module of the split of `AdjointTheoryPetersson`. Covers the T128
DS-standard `δ_b` representative-system helpers and the associated
fundamental-domain swap machinery.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

/-! ### T128 DS-standard `δ_b` representative-system helpers

The `δ_b ∈ Γ₁(N)` matrix realizing `γ₀ · T_p_upper(b) = T_p_lower · δ_b` for
`γ₀ = adjointGamma0Rep`.  These are the candidates for a complete
representative system of `H_L \ Γ₁(N)` where
`H_L := Γ₁(N) ∩ T_p_lower⁻¹ · Γ₁(N) · T_p_lower`. -/

noncomputable def gamma0_T_p_upper_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (b : ℤ) - Int.gcdB p N;
      (N : ℤ), (N : ℤ) * b + (p : ℤ) * Int.gcdA p N],
    by
      have hbez := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
      rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
      rw [Matrix.det_fin_two_of]; linarith⟩

theorem gamma0_T_p_upper_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) :
    gamma0_T_p_upper_Gamma1_factor N p hpN b ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have hbez := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  have hN_zmod : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have hpgcdA_mod : ((p : ZMod N) : ZMod N) * ((Int.gcdA p N : ℤ) : ZMod N) = 1 := by
    have := congr_arg ((↑) : ℤ → ZMod N) hbez.symm
    push_cast at this
    rw [hN_zmod, zero_mul, add_zero] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · change ((1 : ℤ) : ZMod N) = 1
    push_cast; rfl
  · change (((N : ℤ) * b + (p : ℤ) * Int.gcdA p N : ℤ) : ZMod N) = 1
    push_cast
    rw [hN_zmod]
    simp only [zero_mul, zero_add]
    exact hpgcdA_mod
  · change (((N : ℤ) : ℤ) : ZMod N) = 0
    push_cast
    exact ZMod.natCast_self N

theorem mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (b : ℕ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  have hbez : (Int.gcdA p N : ℤ) * p + (Int.gcdB p N : ℤ) * N = 1 := by
    have h := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at h
    linarith
  have h_gamma0_mat : (((mapGL ℝ : SL(2, ℤ) →* _)
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -((Int.gcdB p N : ℤ) : ℝ); (N : ℝ), ((Int.gcdA p N : ℤ) : ℝ)] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [adjointGamma0Rep, mapGL_coe_matrix, algebraMap_int_eq, Matrix.of_apply]
  have h_Tu_mat : ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  have h_Tl_mat : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  have h_delta_mat : (((mapGL ℝ : SL(2, ℤ) →* _)
      (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), ((b : ℝ) - ((Int.gcdB p N : ℤ) : ℝ));
         (N : ℝ), ((N : ℝ) * b + (p : ℝ) * ((Int.gcdA p N : ℤ) : ℝ))] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [mapGL_coe_matrix, gamma0_T_p_upper_Gamma1_factor, algebraMap_int_eq,
        Matrix.of_apply]
  show ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : GL (Fin 2) ℝ).val i j =
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ)).val i j
  rw [Units.val_mul, Units.val_mul, h_gamma0_mat, h_Tu_mat, h_Tl_mat, h_delta_mat]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;> ring

theorem mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) := by
  have h_M_infty_eq : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, ← mul_assoc,
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp hpN 0,
    mul_assoc, ← map_mul]

theorem gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0 ∈
      Gamma1 N :=
  mul_mem (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN 0)
    (M_infty_Gamma1_factor_mem_Gamma1 N p hpN 0)

private noncomputable def ds_p_plus_one_family_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Option (Fin p) → SL(2, ℤ)
  | none => gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0
  | some b => gamma0_T_p_upper_Gamma1_factor N p hpN b.val

private theorem ds_p_plus_one_family_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (i : Option (Fin p)) :
    ds_p_plus_one_family_Gamma1_factor N p hpN i ∈ Gamma1 N := by
  match i with
  | none =>
    exact gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
      N p hpN
  | some b =>
    exact gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b.val

private theorem mapGL_gamma0_mul_ds_family_eq_T_p_lower_mul_mapGL_factor
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) := by
  match i with
  | none =>
    exact mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp hpN
  | some b =>
    exact mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp hpN b.val

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma UpperHalfPlane_smul_eq_of_matrix_smul_eq
    (α β : GL (Fin 2) ℝ) (hα : 0 < α.det.val) (hβ : 0 < β.det.val)
    (c : ℝ) (hc : c ≠ 0)
    (hMat : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • (β : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    α • τ = β • τ := by
  rw [UpperHalfPlane.ext_iff,
      UpperHalfPlane.coe_smul_of_det_pos hα,
      UpperHalfPlane.coe_smul_of_det_pos hβ]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  have h00 : (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h01 : (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h10 : (α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h11 : (α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  rw [show ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) by
    exact_mod_cast h00,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) by
      exact_mod_cast h01,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) by
      exact_mod_cast h10,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) by
      exact_mod_cast h11]
  have hc_ne_zero : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h_num : (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (τ : ℂ) +
      (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      (c : ℂ) * (((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (τ : ℂ) +
        ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) := by ring
  have h_den : (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (τ : ℂ) +
      (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      (c : ℂ) * (((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (τ : ℂ) +
        ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) := by ring
  rw [h_num, h_den, mul_div_mul_left _ _ hc_ne_zero]

/-- The real image `mapGL ℝ γ` of `γ ∈ SL₂(ℤ)` has unit determinant. -/
private theorem mapGL_SL_det_val_eq_one (γ : SL(2, ℤ)) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ).det.val = 1 := by
  show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
  rw [show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Int.castRingHom ℝ).mapMatrix γ.val) by rw [mapGL_coe_matrix]; rfl,
    ← RingHom.map_det, γ.property, map_one]

/-- The real image `glMap (T_p_lower p hp)` has positive determinant `(= p)`. -/
private theorem glMap_T_p_lower_det_val_pos (p : ℕ) (hp : 0 < p) :
    0 < (glMap (T_p_lower p hp) : GL (Fin 2) ℝ).det.val :=
  glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp)

/-- The real image `glMap (T_p_upper p hp b)` has positive determinant `(= p)`. -/
private theorem glMap_T_p_upper_det_val_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val :=
  glMap_det_pos_of_rat_det_pos _ (T_p_upper_det_pos p hp b)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_T_p_upper_smul_eq_shift_smul
    (p : ℕ) (hp : 0 < p) (b : ℕ) (τ : ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • τ =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • τ := by
  have h_det_pos_LHS : 0 <
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos (glMap_T_p_lower_det_val_pos p hp)
      (glMap_T_p_upper_det_val_pos p hp b)
  have h_det_pos_RHS : 0 <
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) :
        GL (Fin 2) ℝ).det.val := by
    rw [mapGL_SL_det_val_eq_one]; exact one_pos
  refine UpperHalfPlane_smul_eq_of_matrix_smul_eq _ _ h_det_pos_LHS h_det_pos_RHS
    (p : ℝ) (by exact_mod_cast hp.ne') ?_ τ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glMap, T_p_lower, T_p_upper, mapGL_coe_matrix, shiftSL_loc,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul,
      algebraMap_int_eq, Matrix.smul_apply] <;>
    ring

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (τ : ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)) • τ =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • τ := by
  have h_M_infty_eq : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, ← mul_assoc, mul_smul]
  rw [T_p_lower_mul_T_p_upper_smul_eq_shift_smul p hp 0]
  show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc ((0 : ℕ) : ℤ))
    : GL (Fin 2) ℝ) • _ = _
  rw [show shiftSL_loc ((0 : ℕ) : ℤ) = (1 : SL(2, ℤ)) by
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shiftSL_loc, Matrix.of_apply]]
  simp [MonoidHom.map_one, one_smul]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma smul_set_eq_of_smul_eq
    {α β : GL (Fin 2) ℝ} (hsmul : ∀ τ : ℍ, α • τ = β • τ) (S : Set ℍ) :
    α • S = β • S := by
  ext τ
  refine ⟨?_, ?_⟩ <;> rintro ⟨σ, hσ, rfl⟩
  · exact ⟨σ, hσ, (hsmul σ).symm⟩
  · exact ⟨σ, hσ, hsmul σ⟩

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul
    (p : ℕ) (hp : 0 < p) (b : ℕ) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • S :=
  smul_set_eq_of_smul_eq (T_p_lower_mul_T_p_upper_smul_eq_shift_smul p hp b) S

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_M_infty_smul_set_eq_M_infty_Gamma1_factor_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • S :=
  smul_set_eq_of_smul_eq
    (T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul (N := N) p hp hpN) S

private noncomputable def T_p_lower_tile_family
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Option (Fin p) → SL(2, ℤ)
  | none => M_infty_Gamma1_factor N p hpN 0
  | some b => shiftSL_loc (b.val : ℤ)

private noncomputable def Hecke_rep_family
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    Option (Fin p) → GL (Fin 2) ℝ
  | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
  | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_smul_Hecke_FD_eq_iUnion_tile
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp hpN i • S) =
    ⋃ i : Option (Fin p),
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i ↦ ?_
  match i with
  | none =>
    show (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • S
    rw [← mul_smul]
    exact T_p_lower_mul_M_infty_smul_set_eq_M_infty_Gamma1_factor_smul
      (N := N) p hp hpN S
  | some b =>
    show (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) • S) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (shiftSL_loc (b.val : ℤ)) : GL (Fin 2) ℝ) • S
    rw [← mul_smul]
    exact T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul p hp b.val S

open UpperHalfPlane in
/-- Pointwise AM-GM bound for the Petersson integrand: the off-diagonal product
is controlled by the average of the two diagonal products. -/
private lemma norm_petersson_le_half_add_diag (a b : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k a b τ‖ ≤ (‖petersson k a a τ‖ + ‖petersson k b b τ‖) / 2 := by
  simp only [petersson, norm_mul, Complex.norm_conj]
  have h_im_nn : (0 : ℝ) ≤ ‖((τ.im : ℂ) ^ k)‖ := norm_nonneg _
  nlinarith [mul_nonneg (sq_nonneg (‖a τ‖ - ‖b τ‖)) h_im_nn,
    sq_nonneg (‖a τ‖ - ‖b τ‖), norm_nonneg (a τ), norm_nonneg (b τ), h_im_nn]

open UpperHalfPlane MeasureTheory ConjAct Pointwise in
/-- Integrability of `petersson f (g ∣[k] glMap σ)` over any finite-measure set.
The translated form `g ∣[k] glMap σ` is a cusp form for the arithmetic conjugate
group, giving a global self-bound; AM-GM then yields a uniform integrand bound,
which combines with the finite measure of `S`. -/
lemma integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (σ : GL (Fin 2) ℚ)
    {S : Set ℍ} (hS : μ_hyp S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f
      (⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ)) τ) S μ_hyp := by
  haveI hArith : (toConjAct (glMap σ : GL (Fin 2) ℝ)⁻¹ •
      ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) σ⁻¹
    have h_inv : (((σ⁻¹ : GL (Fin 2) ℚ).map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) =
        (glMap σ : GL (Fin 2) ℝ)⁻¹ := by rw [map_inv]; rfl
    rwa [h_inv] at h
  let g_tr : CuspForm
      (toConjAct (glMap σ : GL (Fin 2) ℝ)⁻¹ • ((Gamma1 N).map (mapGL ℝ))) k :=
    CuspForm.translate g (glMap σ : GL (Fin 2) ℝ)
  have h_gtr_coe : (⇑g_tr : ℍ → ℂ) = ⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ) := rfl
  obtain ⟨C_f, hC_f⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f f
  obtain ⟨C_gtr, hC_gtr⟩ := CuspFormClass.petersson_bounded_left k _ g_tr g_tr
  have h_AM_GM : ∀ τ, ‖petersson k ⇑f
      (⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ)) τ‖ ≤ (C_f + C_gtr) / 2 := fun τ ↦ by
    rw [← h_gtr_coe]
    have hh := norm_petersson_le_half_add_diag (k := k) ⇑f ⇑g_tr τ
    linarith [hC_f τ, hC_gtr τ, hh]
  refine IntegrableOn.of_bound hS ?_ ((C_f + C_gtr) / 2) (ae_of_all _ h_AM_GM)
  refine (petersson_continuous k (ModularFormClass.continuous f.toModularForm') ?_
    ).aestronglyMeasurable.restrict
  rw [← h_gtr_coe]; exact ModularFormClass.continuous g_tr

/-! ### Named Prop bundles for tile-union hypotheses.

The aggregate `petN_*_per_alpha_HeckeFD_form` theorems below reuse a handful of long
hypothesis clusters (`Pairwise AEDisjoint`, `NullMeasurableSet`, `IntegrableOn`) across
many sites. Bundling them as named `Prop`s shrinks the signatures from ~75-line
multi-cluster forms to a few lines each. Each named Prop is `rfl`-equal to its inline
form. -/

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

open UpperHalfPlane ModularGroup MeasureTheory in

private lemma heckeT_p_cusp_comm_diamondOp_private
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (d : (ZMod N)ˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_p_cusp k p hp hpN (diamondOp_cusp k d g) =
      diamondOp_cusp k d (heckeT_p_cusp k p hp hpN g) := by
  apply CuspForm.ext; intro τ
  show ((heckeT_p k p hp hpN) (diamondOp k d g.toModularForm')).toFun τ =
    ((diamondOp k d) (heckeT_p k p hp hpN g.toModularForm')).toFun τ
  have h := LinearMap.congr_fun
    (heckeT_p_comm_diamondOp (N := N) k p hp hpN d) g.toModularForm'
  simp only [LinearMap.comp_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ)
    h.symm

/-! ### W5a-2 `hFD` — the Hecke-tile fundamental-domain identification

The `p+1` det-`p` Hecke tiles `β_i • Γ₁-FD` (`β_none = M_∞`, `β_(some b) = T_p_upper(b)`)
tile `Γ_p(A)\ℍ` (`A = diag(p,1)`).  Proven by transporting the conjugate-group FD on
`A • D = ⋃_i γ_i • Γ₁-FD` (det-1 Γ₁-tiles, `DeltaB:700`) back by `A⁻¹` (`smul_of_eq_conjAct`).
-/

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Each Hecke-tile translate `γ_i = T_p_lower_tile_family i` lies in `Γ₁(N)`:
`none ↦ M_∞-factor`, `some b ↦ shiftSL_loc b`. -/
private lemma T_p_lower_tile_family_mem_Gamma1
    (p : ℕ) (hpN : Nat.Coprime p N) (i : Option (Fin p)) :
    T_p_lower_tile_family N p hpN i ∈ Gamma1 N := by
  match i with
  | none => exact M_infty_Gamma1_factor_mem_Gamma1 N p hpN 0
  | some b =>
    rw [show T_p_lower_tile_family N p hpN (some b) = shiftSL_loc (b.val : ℤ) from rfl,
      Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL_loc]

open Pointwise ConjAct in
/-- **PSL-conjugation bridge.** If `A' : GL(2,ℝ)⁺` and `x, y : SL(2,ℤ)` satisfy the GL-level
conjugation identity `A' · (mapGL ℝ x) · A'⁻¹ = mapGL ℝ y`, then conjugating the projective
image `SL2Z_to_PSL2R x` by `g = GLPos_to_PSL_R_term A'` gives `SL2Z_to_PSL2R y`.  The
determinant normalization in `GLPos_to_SLR` cancels under conjugation, so the `SL(2, ℝ)`
representatives of both sides have *equal matrices*. -/
private lemma toConjAct_GLPos_smul_SL2Z_to_PSL2R
    (A' : GL(2, ℝ)⁺) (x y : SL(2, ℤ))
    (hxy : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) * (A' : GL (Fin 2) ℝ)⁻¹ =
      (mapGL ℝ y : GL (Fin 2) ℝ)) :
    ConjAct.toConjAct (GLPos_to_PSL_R_term A') • (SL2Z_to_PSL2R x) = SL2Z_to_PSL2R y := by
  have hdpos : 0 < ((A' : GL (Fin 2) ℝ).det.val : ℝ) := A'.property
  set c : ℝ := (Real.sqrt ((A' : GL (Fin 2) ℝ).det.val))⁻¹ with hc_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def, ne_eq, inv_eq_zero]
    exact (Real.sqrt_pos.mpr hdpos).ne'
  -- The `SL(2, ℝ)` representative of `g`.
  set s : SL(2, ℝ) := GLPos_to_SLR A' with hs_def
  set mx : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) x with hmx_def
  set my : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) y with hmy_def
  -- `s.val = c • A'.val` as matrices.
  have hs_val : (s : Matrix (Fin 2) (Fin 2) ℝ) =
      c • ((A' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  -- Matrix forms of `mx, my` via the `mapGL`/`map` compatibility.
  have hmx_val : (mx : Matrix (Fin 2) (Fin 2) ℝ) =
      ((mapGL ℝ x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
    (Matrix.SpecialLinearGroup.mapGL_coe_matrix x).symm
  have hmy_val : (my : Matrix (Fin 2) (Fin 2) ℝ) =
      ((mapGL ℝ y : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
    (Matrix.SpecialLinearGroup.mapGL_coe_matrix y).symm
  -- Reduce the GL conjugation identity `hxy` to the inverse-free `A · mx = my · A`.
  have hAxyA : ((A' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (mx : Matrix (Fin 2) (Fin 2) ℝ) =
      (my : Matrix (Fin 2) (Fin 2) ℝ) *
        ((A' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hxy' : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) =
        (mapGL ℝ y : GL (Fin 2) ℝ) * (A' : GL (Fin 2) ℝ) := by
      rw [← hxy]; group
    have := congrArg (fun u : GL (Fin 2) ℝ ↦ (u : Matrix (Fin 2) (Fin 2) ℝ)) hxy'
    simpa only [Matrix.GeneralLinearGroup.coe_mul, hmx_val, hmy_val] using this
  -- The `SL(2, ℝ)` conjugation identity, proven inverse-free via `s · mx = my · s`.
  have hSmul : s * mx = my * s := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hlhs : (↑(s * mx) : Matrix (Fin 2) (Fin 2) ℝ) =
        c • (((A' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (mx : Matrix _ _ ℝ)) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hs_val, Matrix.smul_mul]
    have hrhs : (↑(my * s) : Matrix (Fin 2) (Fin 2) ℝ) =
        c • ((my : Matrix _ _ ℝ) * ((A' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hs_val, Matrix.mul_smul]
    rw [hlhs, hrhs, hAxyA]
  have hSLeq : s * mx * s⁻¹ = my := by
    rw [hSmul, mul_assoc, mul_inv_cancel, mul_one]
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  show (GLPos_to_PSL_R_term A') * (SL2Z_to_PSL2R x) * (GLPos_to_PSL_R_term A')⁻¹ =
      SL2Z_to_PSL2R y
  -- Descend the `SL(2, ℝ)` identity `hSLeq` through the projection `SL(2, ℝ) → PSL(2, ℝ)`.
  have hproj : (GLPos_to_PSL_R_term A') * (SL2Z_to_PSL2R x) * (GLPos_to_PSL_R_term A')⁻¹ =
      ((s * mx * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) := by
    rw [GLPos_to_PSL_R_term, SL2Z_to_PSL2R_apply]
    rfl
  rw [hproj, hSLeq, SL2Z_to_PSL2R_apply]

open UpperHalfPlane Pointwise in
/-- The det-`1` `GL`-action tile `(mapGL ℝ γ) • S` equals the `PSL`-action tile
`SL2Z_to_PSL2R γ • S` for `γ : SL(2, ℤ)`. -/
private lemma mapGL_smul_set_eq_SL2Z_to_PSL2R_smul (γ : SL(2, ℤ)) (S : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) • S =
      (SL2Z_to_PSL2R γ : PSL(2, ℝ)) • S := by
  ext τ
  simp only [Set.mem_smul_set]
  refine ⟨?_, ?_⟩ <;> rintro ⟨y, hy, rfl⟩ <;>
    exact ⟨y, hy, by rw [SL2Z_to_PSL2R_smul]; rfl⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- **(α) PSL-level containment.** For `α : GL (Fin 2) ℚ` with positive real determinant and
`g = GLPos_to_PSL_R_term ⟨α.map (Rat.castHom ℝ), _⟩`, the conjugate group
`K = toConjAct g • (Γ_p(α)).map SL2Z_to_PSL2R` is contained in `Γ₁(N).map SL2Z_to_PSL2R`.
(`K = α(α⁻¹Γ₁α ∩ Γ₁)α⁻¹ = Γ₁ ∩ αΓ₁α⁻¹ ≤ Γ₁`, via `Gamma_p_α_conjBy_spec` through the bridge.) -/
private lemma toConjAct_GLPos_Gamma_p_α_le_Gamma1_map
    (α : GL (Fin 2) ℚ) (hα : 0 < ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ).det.val) :
    (ConjAct.toConjAct (GLPos_to_PSL_R_term ⟨(α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ), hα⟩) •
        ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) : Subgroup PSL(2, ℝ)) ≤
      ((Gamma1 N).map SL2Z_to_PSL2R) := by
  set A' : GL(2, ℝ)⁺ := ⟨(α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ), hα⟩ with hA'_def
  set g : PSL(2, ℝ) := GLPos_to_PSL_R_term A' with hg_def
  intro z hz
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
    ConjAct.ofConjAct_toConjAct, inv_inv] at hz
  -- `g⁻¹ z g ∈ Γ_p(α).map`, so it is `SL2Z_to_PSL2R x` for some `x ∈ Γ_p(α)`.
  obtain ⟨x, hx_mem, hx_eq⟩ := Subgroup.mem_map.mp hz
  -- The conjugation witness `y = conjBy x ∈ Γ₁`, with `A' · mapGL x · A'⁻¹ = mapGL y`.
  set y : SL(2, ℤ) := (Gamma_p_α_conjBy α ⟨x, hx_mem⟩ : SL(2, ℤ)) with hy_def
  have hy_mem : y ∈ Gamma1 N := (Gamma_p_α_conjBy α ⟨x, hx_mem⟩).property
  have hconj_gl : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) *
      (A' : GL (Fin 2) ℝ)⁻¹ = (mapGL ℝ y : GL (Fin 2) ℝ) := by
    rw [hy_def, Gamma_p_α_conjBy_spec α ⟨x, hx_mem⟩]
  -- `z = g · SL2Z_to_PSL2R x · g⁻¹ = SL2Z_to_PSL2R y`.
  have hbridge := toConjAct_GLPos_smul_SL2Z_to_PSL2R A' x y hconj_gl
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← hg_def, hx_eq] at hbridge
  have hz_eq : z = SL2Z_to_PSL2R y := by
    rw [← hbridge]; group
  rw [hz_eq]
  exact Subgroup.mem_map_of_mem SL2Z_to_PSL2R hy_mem

open CongruenceSubgroup Pointwise ConjAct in
/-- **Forward conjugation fact.** For `x ∈ Γ_p(A) = Γ₁ ∩ Γ₀(p)`, the conjugate
`y = A·x·A⁻¹ = [[x₀₀, p·x₀₁], [x₁₀/p, x₁₁]]` has `y₀₁ = p·x₀₁ ≡ 0 mod p`, so `y ∈ Γ⁰(p)`.
This is the "upper-triangular mod p" half of the adjoint-side membership. -/
private lemma Gamma_p_α_conjBy_mem_Gamma_up
    (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (x : Gamma_p_α (N := N) (T_p_lower p hp.pos)) :
    (Gamma_p_α_conjBy (T_p_lower p hp.pos) x : SL(2, ℤ)) ∈ Gamma_up p := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set y : SL(2, ℤ) := (Gamma_p_α_conjBy (T_p_lower p hp.pos) x : SL(2, ℤ)) with hy_def
  -- The `(0,1)` entry of `y = A·x·A⁻¹` is `p · x₀₁` over ℝ, hence `p ∣ y₀₁`.
  have hentry : ((y.val 0 1 : ℤ) : ℝ) = (p : ℝ) * ((x.val.val 0 1 : ℤ) : ℝ) := by
    have h1 : ((mapGL ℝ y : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![((x.val.val 0 0 : ℤ) : ℝ), (p : ℝ) * ((x.val.val 0 1 : ℤ) : ℝ);
           ((x.val.val 1 0 : ℤ) : ℝ) / (p : ℝ), ((x.val.val 1 1 : ℤ) : ℝ)] := by
      rw [hy_def, Gamma_p_α_conjBy_spec (T_p_lower p hp.pos) x]
      exact conj_T_p_lower_real_val p hp.pos x.val
    have h01 := congrFun (congrFun h1 0) 1
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix] at h01
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h01
  rw [Gamma_up_mem]
  have hdvd : (p : ℤ) ∣ y.val 0 1 := by
    have hcast : (y.val 0 1 : ℤ) = x.val.val 0 1 * (p : ℤ) := by
      have : ((y.val 0 1 : ℤ) : ℝ) = ((x.val.val 0 1 * (p : ℤ) : ℤ) : ℝ) := by
        rw [hentry]; push_cast; ring
      exact_mod_cast this
    exact ⟨x.val.val 0 1, by rw [hcast]; ring⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
  exact_mod_cast hdvd

open CongruenceSubgroup Pointwise ConjAct in
/-- Determinant of the conjugate-back matrix `[[y₀₀, j], [p·y₁₀, y₁₁]]` for `y ∈ SL(2,ℤ)` and
`j` satisfying `y₀₁ = p·j`. -/
private lemma conjBack_matrix_det
    (p : ℕ) {y : SL(2, ℤ)} {j : ℤ} (hj : y.val 0 1 = (p : ℤ) * j) :
    (!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  have hydet : y.val 0 0 * y.val 1 1 - y.val 0 1 * y.val 1 0 = 1 := by
    have := y.property; rw [Matrix.det_fin_two] at this; linarith [this]
  have hprod : j * ((p : ℤ) * y.val 1 0) = y.val 0 1 * y.val 1 0 := by rw [hj]; ring
  rw [hprod]; exact hydet

open CongruenceSubgroup Pointwise ConjAct in
/-- The conjugate-back matrix `x = [[y₀₀, j], [p·y₁₀, y₁₁]]` belongs to `Γ₁(N)` whenever `y` does.
The diagonal of `x` matches that of `y`, and `x₁₀ = p·y₁₀ ≡ 0 mod N`. -/
private lemma conjBack_matrix_mem_Gamma1
    (p : ℕ) {y : SL(2, ℤ)} {j : ℤ} (hj : y.val 0 1 = (p : ℤ) * j)
    (hy₁ : y ∈ Gamma1 N) :
    (⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1], conjBack_matrix_det p hj⟩ :
      SL(2, ℤ)) ∈ Gamma1 N := by
  obtain ⟨hy00, hy11, hy10⟩ := (Gamma1_mem N y).mp hy₁
  refine (Gamma1_mem N _).mpr ⟨?_, ?_, ?_⟩
  · show (((!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1
    simp only [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact hy00
  · show (((!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1
    simp only [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact hy11
  · show (((!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
    simp only [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast; rw [hy10, mul_zero]

open CongruenceSubgroup Pointwise ConjAct in
/-- The conjugation identity `A · mapGL x · A⁻¹ = mapGL y` for the conjugate-back matrix
`x = [[y₀₀, j], [p·y₁₀, y₁₁]]` with `y₀₁ = p·j`, where `A = T_p_lower p`. -/
private lemma conjBack_matrix_conj_eq
    (p : ℕ) (hp : Nat.Prime p) {y : SL(2, ℤ)} {j : ℤ} (hj : y.val 0 1 = (p : ℤ) * j) :
    ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ (⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1],
            conjBack_matrix_det p hj⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)⁻¹ =
      (mapGL ℝ y : GL (Fin 2) ℝ) := by
  set x : SL(2, ℤ) :=
    ⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1], conjBack_matrix_det p hj⟩
  apply Units.ext
  rw [show ((mapGL ℝ x : GL (Fin 2) ℝ)) =
      toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) x) from rfl,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    conj_T_p_lower_real_val p hp.pos x, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [x, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hj, hpR]

open CongruenceSubgroup Pointwise ConjAct in
/-- **Backward conjugation witness.** For `y ∈ Γ₁ ∩ Γ⁰(p)` (so `p ∣ y₀₁`), the matrix
`x = A⁻¹·y·A = [[y₀₀, y₀₁/p], [p·y₁₀, y₁₁]]` is an integral `Γ_p(A)`-element with
`A·(mapGL x)·A⁻¹ = mapGL y`.  This realizes every `Γ₁ ∩ Γ⁰(p)` element as a conjugate. -/
private lemma exists_Gamma_p_α_conj_eq_of_mem_Gamma_up
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {y : SL(2, ℤ)} (hy₁ : y ∈ Gamma1 N) (hyU : y ∈ Gamma_up p) :
    ∃ x ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
          (mapGL ℝ x : GL (Fin 2) ℝ) *
          ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)⁻¹ =
        (mapGL ℝ y : GL (Fin 2) ℝ) := by
  have hdvd : (p : ℤ) ∣ y.val 0 1 := by
    have := (Gamma_up_mem (p := p) (A := y)).mp hyU
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨j, hj⟩ := hdvd
  set x : SL(2, ℤ) :=
    ⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1], conjBack_matrix_det p hj⟩ with hx_def
  have hx_mem₁ : x ∈ Gamma1 N := conjBack_matrix_mem_Gamma1 (N := N) p hj hy₁
  have hx_mem : x ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) := by
    rw [mem_Gamma_p_α_T_p_lower p hp.pos hpN]
    refine ⟨hx_mem₁, ?_⟩
    show (p : ℤ) ∣ x.val 1 0
    simp only [hx_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨y.val 1 0, rfl⟩
  exact ⟨x, hx_mem, conjBack_matrix_conj_eq p hp hj⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- **The adjoint-side subgroup identity.** `K = toConjAct g • Γ_p(A).map = (Γ₁ ∩ Γ⁰(p)).map`.
Conjugating the lower-triangular group `Γ_p(A) = Γ₁ ∩ Γ₀(p)` by `A = diag(p,1)` produces the
upper-triangular group `Γ₁ ∩ Γ⁰(p)` at the `SL(2, ℤ)` level, transported to `PSL(2, ℝ)` via
the projective-conjugation bridge `toConjAct_GLPos_smul_SL2Z_to_PSL2R`. -/
private lemma toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    (ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R) :
        Subgroup PSL(2, ℝ)) =
      ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R) := by
  set A' : GL(2, ℝ)⁺ := ⟨glMap (T_p_lower p hp.pos),
    glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩ with hA'_def
  have hA'_val : (A' : GL (Fin 2) ℝ) = (T_p_lower p hp.pos).map (Rat.castHom ℝ) := rfl
  apply le_antisymm
  · -- `K ≤ (Γ₁ ∩ Γ⁰(p)).map`: each `z = g·SL2Z_to_PSL2R(x)·g⁻¹ = SL2Z_to_PSL2R(conjBy x)`,
    -- and `conjBy x ∈ Γ₁ ∩ Γ⁰(p)`.
    intro z hz
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hz
    obtain ⟨x, hx_mem, hx_eq⟩ := Subgroup.mem_map.mp hz
    set y : SL(2, ℤ) := (Gamma_p_α_conjBy (T_p_lower p hp.pos) ⟨x, hx_mem⟩ : SL(2, ℤ)) with hy_def
    have hy_mem₁ : y ∈ Gamma1 N := (Gamma_p_α_conjBy (T_p_lower p hp.pos) ⟨x, hx_mem⟩).property
    have hy_memU : y ∈ Gamma_up p :=
      Gamma_p_α_conjBy_mem_Gamma_up p hp hpN ⟨x, hx_mem⟩
    have hconj_gl : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) *
        (A' : GL (Fin 2) ℝ)⁻¹ = (mapGL ℝ y : GL (Fin 2) ℝ) := by
      rw [hy_def, Gamma_p_α_conjBy_spec (T_p_lower p hp.pos) ⟨x, hx_mem⟩, hA'_val]
    have hbridge := toConjAct_GLPos_smul_SL2Z_to_PSL2R A' x y hconj_gl
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← hg, hx_eq] at hbridge
    have hz_eq : z = SL2Z_to_PSL2R y := by rw [← hbridge]; group
    rw [hz_eq]
    exact Subgroup.mem_map_of_mem SL2Z_to_PSL2R (Subgroup.mem_inf.mpr ⟨hy_mem₁, hy_memU⟩)
  · -- `(Γ₁ ∩ Γ⁰(p)).map ≤ K`: each `SL2Z_to_PSL2R(y)` with `y ∈ Γ₁ ∩ Γ⁰(p)` is `g·SL2Z_to_PSL2R(x)·g⁻¹`.
    intro z hz
    obtain ⟨y, hy_mem, hy_eq⟩ := Subgroup.mem_map.mp hz
    obtain ⟨hy₁, hyU⟩ := Subgroup.mem_inf.mp hy_mem
    obtain ⟨x, hx_mem, hconj⟩ := exists_Gamma_p_α_conj_eq_of_mem_Gamma_up p hp hpN hy₁ hyU
    have hconj_gl : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) *
        (A' : GL (Fin 2) ℝ)⁻¹ = (mapGL ℝ y : GL (Fin 2) ℝ) := by rw [hA'_val]; exact hconj
    have hbridge := toConjAct_GLPos_smul_SL2Z_to_PSL2R A' x y hconj_gl
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← hg] at hbridge
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv, ← hy_eq, ← hbridge]
    have : g⁻¹ * (g * SL2Z_to_PSL2R x * g⁻¹) * g = SL2Z_to_PSL2R x := by group
    rw [this]
    exact Subgroup.mem_map_of_mem SL2Z_to_PSL2R hx_mem

open CongruenceSubgroup in
/-- The kernel `±I = center SL(2, ℤ)` lies in `Γ⁰(p)` (scalar matrices have zero
upper-right entry).  This is the `±I`-absorption fact that makes the `SL(2, ℤ) → PSL(2, ℝ)`
quotient transport work for *all* `N` (not just `N > 2`). -/
private lemma center_le_Gamma_up (p : ℕ) : Subgroup.center SL(2, ℤ) ≤ Gamma_up p := by
  intro c hc
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
  obtain ⟨r, _, hr⟩ := hc
  rw [Gamma_up_mem]
  have : (c.val 0 1 : ℤ) = 0 := by
    rw [← hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne]; decide
  rw [this]; simp

open CongruenceSubgroup in
omit [NeZero N] in
/-- **`±I`-absorption.** For `w ∈ Γ₁(N)`, `SL2Z_to_PSL2R w ∈ (Γ₁ ∩ Γ⁰(p)).map` iff
`w ∈ Γ₁ ∩ Γ⁰(p)`.  The forward direction uses `center SL(2, ℤ) ≤ Γ⁰(p)` to absorb the
`±I` ambiguity of the projection. -/
private lemma SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff
    (p : ℕ) {w : SL(2, ℤ)} (hw : w ∈ Gamma1 N) :
    SL2Z_to_PSL2R w ∈ ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R) ↔
      w ∈ Gamma1 N ⊓ Gamma_up p := by
  constructor
  · intro hmem
    -- `w ∈ comap SL2Z_to_PSL2R (map SL2Z_to_PSL2R (Γ₁⊓Γ⁰)) = (Γ₁⊓Γ⁰) ⊔ ker`.
    have hcomap : w ∈ (Gamma1 N ⊓ Gamma_up p) ⊔ SL2Z_to_PSL2R.ker := by
      rw [← Subgroup.comap_map_eq]; exact hmem
    -- `(Γ₁⊓Γ⁰) ⊔ ker ≤ Γ⁰(p)` since both `Γ₁⊓Γ⁰ ≤ Γ⁰` and `ker = center ≤ Γ⁰`.
    have hsub : (Gamma1 N ⊓ Gamma_up p) ⊔ SL2Z_to_PSL2R.ker ≤ Gamma_up p := by
      rw [sup_le_iff]
      exact ⟨inf_le_right, ker_SL2Z_to_PSL2R ▸ center_le_Gamma_up p⟩
    exact Subgroup.mem_inf.mpr ⟨hw, hsub hcomap⟩
  · exact fun hmem ↦ Subgroup.mem_map_of_mem SL2Z_to_PSL2R hmem

open CongruenceSubgroup Pointwise ConjAct in
/-- **The adjoint-side coset count.** `[G : K.subgroupOf G] = [Γ₁(N) : Γ₁(N) ∩ Γ⁰(p)] = p + 1`.
The `SL(2, ℤ)`-coset space `Γ₁ ⧸ (Γ₁ ∩ Γ⁰(p))` maps bijectively to the `PSL(2, ℝ)`-coset space
`G ⧸ (K.subgroupOf G)` via `SL2Z_to_PSL2R` (the `±I`-absorption lemma), so the cardinalities
agree, and the `SL`-level count is `p + 1` (`Gamma_up_relIndex_Gamma1`). -/
private lemma card_quotient_K_subgroupOf_G
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    Nat.card (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
          ).subgroupOf ((Gamma1 N).map SL2Z_to_PSL2R))) = p + 1 := by
  -- Rewrite `K = (Γ₁ ∩ Γ⁰(p)).map` and reduce to the `SL`-level relative index.
  rw [toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map p hp hpN g hg]
  -- Bijection `Γ₁ ⧸ (Γ₁⊓Γ⁰).subgroupOf Γ₁ → G ⧸ (Γ₁⊓Γ⁰).map.subgroupOf G`.
  have hbij : ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R).relIndex
      ((Gamma1 N).map SL2Z_to_PSL2R) = (Gamma1 N ⊓ Gamma_up p).relIndex (Gamma1 N) := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
      (Quotient.lift (fun a : Gamma1 N ↦
        (QuotientGroup.mk ⟨SL2Z_to_PSL2R (a : SL(2, ℤ)),
          Subgroup.mem_map_of_mem SL2Z_to_PSL2R a.2⟩ :
          ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R).subgroupOf
              ((Gamma1 N).map SL2Z_to_PSL2R))) ?_) ?_))
    · -- well-defined
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
      rw [← map_inv, ← map_mul]
      exact (SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff p
        ((Gamma1 N).mul_mem ((Gamma1 N).inv_mem a.2) b.2)).mpr hab
    · constructor
      · -- injective
        intro x y hxy
        induction x using QuotientGroup.induction_on with | _ a => ?_
        induction y using QuotientGroup.induction_on with | _ b => ?_
        have hxy' : (QuotientGroup.mk ⟨SL2Z_to_PSL2R (a : SL(2, ℤ)),
            Subgroup.mem_map_of_mem SL2Z_to_PSL2R a.2⟩ :
            ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)) =
            QuotientGroup.mk ⟨SL2Z_to_PSL2R (b : SL(2, ℤ)),
              Subgroup.mem_map_of_mem SL2Z_to_PSL2R b.2⟩ := hxy
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy' ⊢
        simp only [InvMemClass.coe_inv, MulMemClass.coe_mul] at hxy' ⊢
        rw [← map_inv, ← map_mul] at hxy'
        exact (SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff p
          ((Gamma1 N).mul_mem ((Gamma1 N).inv_mem a.2) b.2)).mp hxy'
      · -- surjective
        intro y
        induction y using QuotientGroup.induction_on with | _ z => ?_
        obtain ⟨w, hw_mem, hw_eq⟩ := Subgroup.mem_map.mp z.2
        refine ⟨QuotientGroup.mk ⟨w, hw_mem⟩, ?_⟩
        show QuotientGroup.mk _ = QuotientGroup.mk z
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
        rw [← hw_eq, inv_mul_cancel]
        exact Subgroup.one_mem _
  rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, hbij, inf_comm,
    Subgroup.inf_relIndex_right]
  exact Gamma_up_relIndex_Gamma1 p hp hpN

open CongruenceSubgroup in
/-- For distinct `Fin p` tiles `b₁ ≠ b₂`, the product `shiftSL_loc b₁ · shiftSL_loc b₂⁻¹` is
not in `Γ⁰(p)`: its `(0,1)`-entry is `b₁ - b₂` with `0 < |b₁ - b₂| < p`. -/
private lemma T_p_lower_tile_some_some_notMem_Gamma_up
    (p : ℕ) (hp : Nat.Prime p) {b₁ b₂ : Fin p} (hb : b₁ ≠ b₂) :
    ((shiftSL_loc (b₁.val : ℤ) * (shiftSL_loc (b₂.val : ℤ))⁻¹).val 0 1 : ZMod p) ≠ 0 := by
  have hne : (b₁ : ℤ) ≠ (b₂ : ℤ) := by
    simp only [ne_eq, Nat.cast_inj]; exact fun h ↦ hb (by rw [Fin.ext_iff.mpr h])
  have hentry : ((shiftSL_loc (b₁.val : ℤ) * (shiftSL_loc (b₂.val : ℤ))⁻¹).val 0 1 : ℤ) =
      (b₁.val : ℤ) - (b₂.val : ℤ) := by
    simp only [shiftSL_loc, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [hentry, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have hlt : |(b₁.val : ℤ) - (b₂.val : ℤ)| < p := by
    rw [abs_lt]; constructor <;> [have := b₂.isLt; have := b₁.isLt] <;> omega
  have hb' : (b₁.val : ℤ) - (b₂.val : ℤ) ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨c, hc⟩ := hdvd
  have hcabs : 1 ≤ |c| := Int.one_le_abs (by rintro rfl; simp at hc; exact hb' hc)
  rw [hc, abs_mul, Nat.abs_cast] at hlt
  nlinarith [hlt, hcabs, hp.pos]

open CongruenceSubgroup in
/-- For a `some/none` tile pair, `shiftSL_loc b₁ · M_∞⁻¹` has `(0,1)`-entry
`-1 + b₁·(a·p) ≡ -1 (mod p)`, hence is not in `Γ⁰(p)`. -/
private lemma T_p_lower_tile_some_none_notMem_Gamma_up [NeZero N]
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b₁ : Fin p) :
    ((shiftSL_loc (b₁.val : ℤ) * (M_infty_Gamma1_factor N p hpN 0)⁻¹).val 0 1 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hentry : ((shiftSL_loc (b₁.val : ℤ) * (M_infty_Gamma1_factor N p hpN 0)⁻¹).val 0 1 : ℤ) =
      -1 + (b₁.val : ℤ) * ((aInvOfCoprime N p hpN : ℤ) * p) := by
    simp only [M_infty_Gamma1_factor, shiftSL_loc, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast; ring
  rw [hentry]; push_cast
  rw [show ((b₁.val : ZMod p) * ((aInvOfCoprime N p hpN : ZMod p) * (p : ZMod p))) = 0 by
    rw [ZMod.natCast_self, mul_zero, mul_zero], add_zero]
  exact (neg_ne_zero.mpr one_ne_zero)

open CongruenceSubgroup in
/-- For a `none/some` tile pair, `M_∞ · shiftSL_loc b₂⁻¹` has `(0,1)`-entry
`1 - a·p·b₂ ≡ 1 (mod p)`, hence is not in `Γ⁰(p)`. -/
private lemma T_p_lower_tile_none_some_notMem_Gamma_up [NeZero N]
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b₂ : Fin p) :
    ((M_infty_Gamma1_factor N p hpN 0 * (shiftSL_loc (b₂.val : ℤ))⁻¹).val 0 1 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hentry : ((M_infty_Gamma1_factor N p hpN 0 * (shiftSL_loc (b₂.val : ℤ))⁻¹).val 0 1 : ℤ) =
      1 - (aInvOfCoprime N p hpN : ℤ) * p * (b₂.val : ℤ) := by
    simp only [M_infty_Gamma1_factor, shiftSL_loc, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast; ring
  rw [hentry]; push_cast
  rw [show ((aInvOfCoprime N p hpN : ZMod p) * (p : ZMod p) * (b₂.val : ZMod p)) = 0 by
    rw [ZMod.natCast_self, mul_zero, zero_mul], sub_zero]
  exact one_ne_zero

open CongruenceSubgroup in
/-- **`p`-adic distinctness of the geometric reps.** For distinct tiles `i ≠ j`, the
upper-right entry of `γ_i · γ_j⁻¹` is *not* `≡ 0 mod p`, so `γ_i·γ_j⁻¹ ∉ Γ⁰(p)`.  Concretely:
`shiftSL_loc b₁ · shiftSL_loc b₂⁻¹` has `(0,1) = b₁ - b₂` (`0 < |b₁-b₂| < p`); the `M_∞` reps
give `(0,1) ≡ ±1 mod p`.  This is the `p`-adic separation of the `T_p` coset representatives.
The four cases are dispatched into per-case helpers. -/
private lemma T_p_lower_tile_family_inv_mul_notMem_Gamma_up
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {i j : Option (Fin p)} (hij : i ≠ j) :
    T_p_lower_tile_family N p hpN i * (T_p_lower_tile_family N p hpN j)⁻¹ ∉ Gamma_up p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [Gamma_up_mem]
  match i, j with
  | some b₁, some b₂ =>
    rw [show T_p_lower_tile_family N p hpN (some b₁) = shiftSL_loc (b₁.val : ℤ) from rfl,
      show T_p_lower_tile_family N p hpN (some b₂) = shiftSL_loc (b₂.val : ℤ) from rfl]
    exact T_p_lower_tile_some_some_notMem_Gamma_up p hp (fun h ↦ hij (by rw [h]))
  | some b₁, none =>
    rw [show T_p_lower_tile_family N p hpN (some b₁) = shiftSL_loc (b₁.val : ℤ) from rfl,
      show T_p_lower_tile_family N p hpN none = M_infty_Gamma1_factor N p hpN 0 from rfl]
    exact T_p_lower_tile_some_none_notMem_Gamma_up p hp hpN b₁
  | none, some b₂ =>
    rw [show T_p_lower_tile_family N p hpN none = M_infty_Gamma1_factor N p hpN 0 from rfl,
      show T_p_lower_tile_family N p hpN (some b₂) = shiftSL_loc (b₂.val : ℤ) from rfl]
    exact T_p_lower_tile_none_some_notMem_Gamma_up p hp hpN b₂
  | none, none => exact (hij rfl).elim

open CongruenceSubgroup Pointwise ConjAct in
/-- **(β) The complete transversal.** The `p+1` det-`1` reps `r i = SL2Z_to_PSL2R γ_i`
(`γ_i = T_p_lower_tile_family i ∈ Γ₁`) have their inverses `(r i)⁻¹` representing *all* the
left cosets `G ⧸ (K.subgroupOf G)` bijectively, where `G = Γ₁.map` and `K = toConjAct g •
Γ_p(A).map = (Γ₁ ∩ Γ⁰(p)).map` is the adjoint-side conjugate.

PROOF (via `Nat.bijective_iff_injective_and_card`, both leaves discharged):
* **card** `Nat.card (G ⧸ (K.subgroupOf G)) = p + 1` (`card_quotient_K_subgroupOf_G`): with
  `K = (Γ₁ ∩ Γ⁰(p)).map` (`toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map`),
  the `SL`-coset space `Γ₁ ⧸ (Γ₁∩Γ⁰(p))` maps bijectively onto `G ⧸ (K.subgroupOf G)` via
  `SL2Z_to_PSL2R` (`±I`-absorption), and the `SL`-count is `[Γ₁:Γ₁∩Γ⁰(p)] = p+1`
  (`Gamma_up_relIndex_Gamma1`, the upper mirror of `relIndex_Gamma_p_α_T_p_lower`).
  NB: the naive `relIndex_pointwise_smul` chain `K.relIndex G = Γp.relIndex (g⁻¹•G)` is a
  TRAP — `g` does not normalize `G = Γ₁.map`; the index is computed via the Fricke conjugate
  `Γ⁰(p) = S·Γ₀(p)·S⁻¹` instead.
* **injectivity** of `i ↦ ⟦(r i)⁻¹⟧`: distinct tiles give `r_i·r_j⁻¹ = SL2Z_to_PSL2R(γ_i·γ_j⁻¹)
  ∉ K`, since `γ_i·γ_j⁻¹ ∉ Γ⁰(p)` (`T_p_lower_tile_family_inv_mul_notMem_Gamma_up`: the upper
  reps differ by `(0,1)`-entries `b₁-b₂` resp. `≡ ±1 mod p`), through the `±I`-absorption
  membership characterization.

This is the residual covering-combinatorics gap of the W5 build (a clean restatement of
Miyake 4.5.6 on the adjoint side). -/
private theorem T_p_lower_tile_transversal_bijective
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    Function.Bijective
      (fun i : Option (Fin p) ↦
        (QuotientGroup.mk
          ((⟨SL2Z_to_PSL2R (T_p_lower_tile_family N p hpN i),
              Subgroup.mem_map_of_mem SL2Z_to_PSL2R (T_p_lower_tile_family_mem_Gamma1 p hpN i)⟩ :
            ((Gamma1 N).map SL2Z_to_PSL2R))⁻¹) :
          ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
              ).subgroupOf ((Gamma1 N).map SL2Z_to_PSL2R)))) := by
  set G : Subgroup PSL(2, ℝ) := (Gamma1 N).map SL2Z_to_PSL2R with hG_def
  set K : Subgroup PSL(2, ℝ) :=
    ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
    with hK_def
  set r : Option (Fin p) → G := fun i ↦
    ⟨SL2Z_to_PSL2R (T_p_lower_tile_family N p hpN i),
      Subgroup.mem_map_of_mem SL2Z_to_PSL2R (T_p_lower_tile_family_mem_Gamma1 p hpN i)⟩
    with hr_def
  -- The codomain `G ⧸ (K.subgroupOf G)` is finite of cardinality `p + 1`.
  have hcard : Nat.card (G ⧸ (K.subgroupOf G)) = p + 1 :=
    card_quotient_K_subgroupOf_G p hp hpN g hg
  haveI : Finite (G ⧸ (K.subgroupOf G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · -- Injectivity: `⟦(r i)⁻¹⟧ = ⟦(r j)⁻¹⟧ → r_i·r_j⁻¹ ∈ K → γ_i·γ_j⁻¹ ∈ Γ⁰(p)`, contradiction.
    intro i j hij
    by_contra hne
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, inv_inv] at hij
    -- `(r i)·(r j)⁻¹ ∈ K`, i.e. `SL2Z_to_PSL2R (γ_i·γ_j⁻¹) ∈ K`.
    have hmem : SL2Z_to_PSL2R (T_p_lower_tile_family N p hpN i *
        (T_p_lower_tile_family N p hpN j)⁻¹) ∈ K := by
      have : ((r i * (r j)⁻¹ : G) : PSL(2, ℝ)) =
          SL2Z_to_PSL2R (T_p_lower_tile_family N p hpN i *
            (T_p_lower_tile_family N p hpN j)⁻¹) := by
        rw [hr_def]
        simp only [MulMemClass.coe_mul, InvMemClass.coe_inv]
        rw [map_mul, map_inv]
      rwa [← this]
    -- Rewrite `K = (Γ₁ ∩ Γ⁰(p)).map` and apply `±I`-absorption.
    rw [hK_def, toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map p hp hpN g hg,
      SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff p
        ((Gamma1 N).mul_mem (T_p_lower_tile_family_mem_Gamma1 p hpN i)
          ((Gamma1 N).inv_mem (T_p_lower_tile_family_mem_Gamma1 p hpN j)))] at hmem
    exact T_p_lower_tile_family_inv_mul_notMem_Gamma_up p hp hpN hne (Subgroup.mem_inf.mp hmem).2
  · -- Cardinality match: `Fintype.card (Option (Fin p)) = p + 1 = Nat.card (G ⧸ K.subgroupOf G)`.
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Base fundamental domain for `G = (Γ₁ N).map SL2Z_to_PSL2R` is `Gamma1_fundDomain_PSL N`.
This is `isFundamentalDomain_Gamma1_PSL_R` after rewriting the map. -/
private lemma isFundamentalDomain_Gamma1_map_PSL_R :
    IsFundamentalDomain ((Gamma1 N).map SL2Z_to_PSL2R)
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  rw [map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R]
  exact isFundamentalDomain_Gamma1_PSL_R

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- The tile sets agree: `SL2Z_to_PSL2R γ_i • Γ₁-FD = (mapGL ℝ γ_i) • Γ₁-FD` for the
`T_p_lower_tile_family` reps `γ_i`. -/
private lemma iUnion_tile_family_smul_PSL_eq_iUnion_mapGL_smul
    (p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (⋃ i : Option (Fin p),
        (SL2Z_to_PSL2R (T_p_lower_tile_family N p hpN i) : PSL(2, ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) =
      ⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (T_p_lower_tile_family N p hpN i) :
          GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ) := by
  refine Set.iUnion_congr fun i ↦ ?_
  rw [mapGL_smul_set_eq_SL2Z_to_PSL2R_smul]

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **W5a covering crux (Step I of the `hFD` descent).** The `A`-conjugate of `D`, namely
`A • D = ⋃_i γ_i • Γ₁-FD` (det-1 `Γ₁`-tiles, `γ_i = T_p_lower_tile_family i`, `DeltaB:700`),
is a fundamental domain for the conjugate group `K = toConjAct g • Γ_p(A).map`
(`g = GLPos_to_PSL_R_term ⟨A, _⟩`, `A = diag(p,1)`).

Proved via `IsFundamentalDomain.iUnion_smul_of_transversal` (PLN, PROVEN) with `G = Γ₁.map`,
`s = Γ₁-FD`, `H = K.subgroupOf G`, `r i = SL2Z_to_PSL2R γ_i`, using (α) the containment
`K ≤ Γ₁.map` (`toConjAct_GLPos_Gamma_p_α_le_Gamma1_map`) and (β) the transversal bijection
`e : Option(Fin p) ≃ G ⧸ H`, `e i = ⟦(r i)⁻¹⟧` (`T_p_lower_tile_transversal_bijective`), then
the `subgroupOf → subgroup` transport (FDT:860-pattern `image_of_equiv` + `subgroupOfEquivOfLe`)
and the action-matching `mapGL_smul_set_eq_SL2Z_to_PSL2R_smul`. -/
private theorem iUnion_T_p_lower_tile_family_isFundamentalDomain_conj
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    IsFundamentalDomain
      ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) :
        Subgroup PSL(2, ℝ))
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i •
          (Gamma1_fundDomain_PSL N : Set ℍ)))
      μ_hyp := by
  rw [T_p_lower_smul_Hecke_FD_eq_iUnion_tile p hp.pos hpN,
    ← iUnion_tile_family_smul_PSL_eq_iUnion_mapGL_smul (N := N) p hpN]
  set K : Subgroup PSL(2, ℝ) :=
    ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
    with hK_def
  set G : Subgroup PSL(2, ℝ) := (Gamma1 N).map SL2Z_to_PSL2R with hG_def
  have hKG : K ≤ G := by
    rw [hK_def, hG_def, hg]
    exact toConjAct_GLPos_Gamma_p_α_le_Gamma1_map (N := N)
      (T_p_lower p hp.pos) (glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos))
  set r : Option (Fin p) → G := fun i ↦
    ⟨SL2Z_to_PSL2R (T_p_lower_tile_family N p hpN i),
      Subgroup.mem_map_of_mem SL2Z_to_PSL2R (T_p_lower_tile_family_mem_Gamma1 p hpN i)⟩
    with hr_def
  set e : Option (Fin p) ≃ G ⧸ (K.subgroupOf G) :=
    Equiv.ofBijective _ (T_p_lower_tile_transversal_bijective p hp hpN g hg) with he_def
  have hbase : IsFundamentalDomain G (Gamma1_fundDomain_PSL N) μ_hyp :=
    isFundamentalDomain_Gamma1_map_PSL_R (N := N)
  have htool : IsFundamentalDomain (K.subgroupOf G)
      (⋃ i, (r i : PSL(2, ℝ)) • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp :=
    hbase.iUnion_smul_of_transversal e (fun i ↦ rfl)
  have htrans := htool.image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    (Subgroup.subgroupOfEquivOfLe hKG).symm.toEquiv (fun _ _ ↦ rfl)
  simp only [Equiv.coe_refl, Set.image_id] at htrans
  exact htrans

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **W5a-2 `hFD` — the Hecke-tile fundamental-domain identification.** The `p+1` det-`p`
Hecke tiles `D = ⋃_i β_i • Γ₁-FD` (`β_none = M_∞`, `β_(some b) = T_p_upper(b)`) form a
fundamental domain for `Γ_p(A) = A⁻¹Γ₁A ∩ Γ₁` (`A = diag(p,1)`), at the `PSL(2, ℝ)` level.

Proven by transporting the conjugate-group fundamental domain on `A • D = ⋃_i γ_i • Γ₁-FD`
(det-1 `Γ₁`-tiles, `T_p_lower_smul_Hecke_FD_eq_iUnion_tile`) back by `A⁻¹`, via
`IsFundamentalDomain.smul_of_eq_conjAct` (`toConjAct g⁻¹ • (toConjAct g • Γ_p(A).map) =
Γ_p(A).map`) using `g⁻¹ • (A • D) = D` (`GLPos_to_PSL_R_term_smul_set`).  The conjugate-group
FD on `A • D` is `iUnion_T_p_lower_tile_family_isFundamentalDomain_conj` (the W5a covering crux).

This is exactly the hypothesis `hFD` of `aggregate_D_petersson_eq_Gamma_p_A_fundDomain`
(ConcreteFamily.lean), modulo the `⋃ i ∈ univ ↔ ⋃ i` biUnion/iUnion shape handled there. -/
theorem isFundamentalDomain_Hecke_tiles_Gamma_p_α
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R))
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  set A : GL (Fin 2) ℝ := glMap (T_p_lower p hp.pos) with hA_def
  have hApos : 0 < A.det.val := glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)
  set A' : GL(2, ℝ)⁺ := ⟨A, hApos⟩ with hA'_def
  set g : PSL(2, ℝ) := GLPos_to_PSL_R_term A' with hg_def
  set D : Set ℍ := ⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i •
    (Gamma1_fundDomain_PSL N : Set ℍ) with hD_def
  -- The goal's `match`-tiling is definitionally the `Hecke_rep_family` tiling `D`.
  have hD_eq : (⋃ i : Option (Fin p),
      (match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) = D := by
    rw [hD_def]; refine Set.iUnion_congr fun i ↦ ?_; cases i <;> rfl
  rw [hD_eq]
  -- Step (I): a FD for the conjugate group `toConjAct g • Γ_p(A).map` on `A • D`.
  have hI : IsFundamentalDomain
      ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) :
        Subgroup PSL(2, ℝ))
      (A • D) μ_hyp :=
    iUnion_T_p_lower_tile_family_isFundamentalDomain_conj p hp hpN g hg_def
  -- Step (II): conjugate by `g⁻¹` to descend to `Γ_p(A).map` on `g⁻¹ • (A • D) = D`.
  have hconj : ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R) =
      ConjAct.toConjAct g⁻¹ •
        (ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) := by
    rw [smul_smul, ConjAct.toConjAct_inv, inv_mul_cancel, one_smul]
  have hII := hI.smul_of_eq_conjAct (g := g⁻¹) hconj
  -- `g⁻¹ • (A • D) = D`.
  have hset : g⁻¹ • (A • D) = D := by
    have hgA : (A • D : Set ℍ) = g • D := (GLPos_to_PSL_R_term_smul_set A' D).symm
    rw [hgA, inv_smul_smul]
  rwa [hset] at hII

/-! ### `Γ_p(A)\Γ₁` transversal from the `ds_p_plus_one_family` factors (W5a trace side)

The `ds_p_plus_one_family_Gamma1_factor` matrices (the `Γ₁`-factors in the per-class
double-coset identity `mapGL γ₀ · Hecke_rep_i = A · mapGL (ds_factor_i)`) form a complete
right-`Γ_p(A)`-transversal inside `Γ₁(N)`. Distinctness reduces to the `(1,0)`-entry of
`ds_factor_i · ds_factor_j⁻¹` being a non-multiple of `p` (the `Γ₀(p)` condition). -/

/-- `N` is a non-zero unit in `ZMod p` for `p` prime coprime to `N`. -/
private lemma natCast_N_ne_zero_in_zmod_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    ((N : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have hd : p ∣ N := by exact_mod_cast hdvd
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hpN (dvd_refl p) hd)

/-- `N * N` is non-zero in `ZMod p` for `p` prime coprime to `N`. -/
private lemma N_mul_N_ne_zero_in_zmod_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (N : ZMod p) * (N : ZMod p) ≠ 0 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hN0 := natCast_N_ne_zero_in_zmod_p (N := N) p hp hpN
  rw [show ((N : ZMod p) * (N : ZMod p)) = (((N : ℤ) * (N : ℤ) : ℤ) : ZMod p) by push_cast; ring,
    Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  rcases hpZ.dvd_mul.mp h with h | h
  · exact hN0 (by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h)
  · exact hN0 (by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h)

/-- Explicit `ℤ`-matrix form of `γ₀(0) · M_∞(0)`, used in the `none` branches of the
`ds_p_plus_one_family_Gamma1_factor` distinctness analysis. -/
private lemma gamma0_T_p_upper_zero_mul_M_infty_zero_val
    (p : ℕ) (hpN : Nat.Coprime p N) :
    ((gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0).val :
        Matrix (Fin 2) (Fin 2) ℤ) =
      !![(aInvOfCoprime N p hpN : ℤ) * p - (Int.gcdB p N) * ((N : ℤ) * mIdxOfCoprime N p hpN),
         1 - (Int.gcdB p N);
         (N : ℤ) * ((aInvOfCoprime N p hpN : ℤ) * p) +
           (p : ℤ) * (Int.gcdA p N) * ((N : ℤ) * mIdxOfCoprime N p hpN),
         (N : ℤ) + (p : ℤ) * (Int.gcdA p N)] := by
  simp only [gamma0_T_p_upper_Gamma1_factor, M_infty_Gamma1_factor,
    Matrix.SpecialLinearGroup.coe_mul]
  ext ii jj
  fin_cases ii <;> fin_cases jj <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;> ring

open CongruenceSubgroup in
/-- `some/some` case of `ds_p_plus_one_family_Gamma1_factor_inv_mul_notMem_Gamma0`:
`(1,0)`-entry of the product is `N²·(b₂-b₁)`; `p ∤ N` and `|b₂-b₁| < p` block
divisibility by `p`. -/
private lemma ds_p_plus_one_family_Gamma1_factor_some_some_notMem_Gamma0 [NeZero N]
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) {b₁ b₂ : Fin p} (hb : b₁ ≠ b₂) :
    ((ds_p_plus_one_family_Gamma1_factor N p hpN (some b₁) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN (some b₂))⁻¹).val 1 0 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpN_dvd : ¬ (p : ℤ) ∣ (N : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact natCast_N_ne_zero_in_zmod_p (N := N) p hp hpN
  have hne : b₁.val ≠ b₂.val := fun h ↦ hb (by rw [Fin.ext_iff.mpr h])
  have hentry : ((ds_p_plus_one_family_Gamma1_factor N p hpN (some b₁) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN (some b₂))⁻¹).val 1 0 : ℤ) =
      (N : ℤ) * (N : ℤ) * ((b₂.val : ℤ) - (b₁.val : ℤ)) := by
    show ((gamma0_T_p_upper_Gamma1_factor N p hpN b₁.val *
      (gamma0_T_p_upper_Gamma1_factor N p hpN b₂.val)⁻¹).val 1 0 : ℤ) = _
    simp only [gamma0_T_p_upper_Gamma1_factor, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [hentry, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  rcases hpZ.dvd_mul.mp hdvd with h2 | hdiff
  · exact (hpZ.dvd_mul.mp h2).elim hpN_dvd hpN_dvd
  · have hlt : |(b₂.val : ℤ) - (b₁.val : ℤ)| < p := by
      rw [abs_lt]; constructor <;> [have := b₁.isLt; have := b₂.isLt] <;> omega
    have hne0 : (b₂.val : ℤ) - (b₁.val : ℤ) ≠ 0 :=
      sub_ne_zero.mpr fun h ↦ hne (by exact_mod_cast h.symm)
    obtain ⟨c, hc⟩ := hdiff
    have hcabs : 1 ≤ |c| := Int.one_le_abs (by rintro rfl; simp at hc; exact hne0 hc)
    rw [hc, abs_mul, Nat.abs_cast] at hlt
    nlinarith [hlt, hcabs, hp.pos]

/-- `some/none` case: `(1,0)`-entry equals `N²` in `ZMod p`; `N²` is a unit since
`p ∤ N`. -/
private lemma ds_p_plus_one_family_Gamma1_factor_some_none_notMem_Gamma0 [NeZero N]
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b₁ : Fin p) :
    ((ds_p_plus_one_family_Gamma1_factor N p hpN (some b₁) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN none)⁻¹).val 1 0 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hentry : (((ds_p_plus_one_family_Gamma1_factor N p hpN (some b₁) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN none)⁻¹).val 1 0 : ℤ) : ZMod p) =
      (N : ZMod p) * (N : ZMod p) := by
    show (((gamma0_T_p_upper_Gamma1_factor N p hpN b₁.val *
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0)⁻¹).val 1 0 : ℤ) : ZMod p) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      gamma0_T_p_upper_zero_mul_M_infty_zero_val (N := N) p hpN]
    simp only [gamma0_T_p_upper_Gamma1_factor, Matrix.SpecialLinearGroup.coe_mk,
      Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    rw [show ((p : ZMod p)) = 0 from ZMod.natCast_self p]
    ring
  rw [hentry]
  exact N_mul_N_ne_zero_in_zmod_p (N := N) p hp hpN

/-- `none/some` case: `(1,0)`-entry equals `-N²` in `ZMod p`; `-N²` is a unit since
`p ∤ N`. -/
private lemma ds_p_plus_one_family_Gamma1_factor_none_some_notMem_Gamma0 [NeZero N]
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b₂ : Fin p) :
    ((ds_p_plus_one_family_Gamma1_factor N p hpN none *
      (ds_p_plus_one_family_Gamma1_factor N p hpN (some b₂))⁻¹).val 1 0 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hentry : (((ds_p_plus_one_family_Gamma1_factor N p hpN none *
      (ds_p_plus_one_family_Gamma1_factor N p hpN (some b₂))⁻¹).val 1 0 : ℤ) : ZMod p) =
      -((N : ZMod p) * (N : ZMod p)) := by
    show (((gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0 *
      (gamma0_T_p_upper_Gamma1_factor N p hpN b₂.val)⁻¹).val 1 0 : ℤ) : ZMod p) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      gamma0_T_p_upper_zero_mul_M_infty_zero_val (N := N) p hpN]
    simp only [gamma0_T_p_upper_Gamma1_factor, Matrix.SpecialLinearGroup.coe_mk,
      Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    rw [show ((p : ZMod p)) = 0 from ZMod.natCast_self p]
    ring
  rw [hentry]
  exact neg_ne_zero.mpr (N_mul_N_ne_zero_in_zmod_p (N := N) p hp hpN)

/-- **`p`-adic distinctness of the `ds_factor` reps.** Distinct indices `i ≠ j` give
`ds_factor_i · ds_factor_j⁻¹ ∉ Γ₀(p)`, since the `(1,0)`-entry is either
`N²(b₂-b₁)` (some-some; `p ∤ N²(b₂-b₁)`), `N²` (some-none), or `-N²` (none-some) in
`ZMod p`; in each case `N²` is a unit since `p ∤ N`.  Dispatched into three per-case
helpers; the four-way `match` produces only one-line `exact` calls. -/
private lemma ds_p_plus_one_family_Gamma1_factor_inv_mul_notMem_Gamma0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {i j : Option (Fin p)} (hij : i ≠ j) :
    ds_p_plus_one_family_Gamma1_factor N p hpN i *
      (ds_p_plus_one_family_Gamma1_factor N p hpN j)⁻¹ ∉ Gamma0 p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [Gamma0_mem]
  match i, j with
  | some b₁, some b₂ =>
    exact ds_p_plus_one_family_Gamma1_factor_some_some_notMem_Gamma0 p hp hpN
      (fun h ↦ hij (by rw [h]))
  | some b₁, none =>
    exact ds_p_plus_one_family_Gamma1_factor_some_none_notMem_Gamma0 p hp hpN b₁
  | none, some b₂ =>
    exact ds_p_plus_one_family_Gamma1_factor_none_some_notMem_Gamma0 p hp hpN b₂
  | none, none => exact (hij rfl).elim

open CongruenceSubgroup in
/-- A `Γ_p(A)`-slash-invariant function has its slash constant on left `Γ_p(A)`-cosets: if
`a · b⁻¹ ∈ Γ_p(A)` then `G ∣ a = G ∣ b`. -/
private lemma slash_eq_of_inv_mul_mem_Gamma_p_α
    (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (G : UpperHalfPlane → ℂ)
    (hG : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos), G ∣[k] (γ : SL(2, ℤ)) = G)
    {a b : SL(2, ℤ)} (hab : a * b⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos)) :
    G ∣[k] (a : SL(2, ℤ)) = G ∣[k] (b : SL(2, ℤ)) := by
  have hslash := hG _ hab
  rw [show G ∣[k] (a : SL(2, ℤ)) = (G ∣[k] (a * b⁻¹ : SL(2, ℤ))) ∣[k] (b : SL(2, ℤ)) by
    rw [← SlashAction.slash_mul, show (a * b⁻¹) * b = a by group], hslash]

open CongruenceSubgroup in
/-- The `ds_p_plus_one_family` reps are pairwise distinct modulo left-`Γ_p(A)`: if
`ds_factor_i · ds_factor_j⁻¹ ∈ Γ_p(A)` then `i = j`. -/
private lemma ds_p_plus_one_family_inv_mul_mem_Gamma_p_α_iff
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {i j : Option (Fin p)}
    (hmem : ds_p_plus_one_family_Gamma1_factor N p hpN i *
      (ds_p_plus_one_family_Gamma1_factor N p hpN j)⁻¹ ∈
        Gamma_p_α (N := N) (T_p_lower p hp.pos)) : i = j := by
  by_contra hij
  rw [Gamma_p_α_T_p_lower_eq_inf p hp.pos hpN, Subgroup.mem_inf] at hmem
  exact ds_p_plus_one_family_Gamma1_factor_inv_mul_notMem_Gamma0 p hp hpN hij hmem.2

open CongruenceSubgroup Classical in
/-- The transversal map `i ↦ ⟦q'.out · ds_factor_i⁻¹⟧` lands in the fiber
`{q : SL ⧸ Γ_p(A) | [q] = q'}`. -/
private lemma ds_p_plus_one_family_traceSlash_eq_mem_fib
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) (i : Option (Fin p)) :
    (QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) :
          SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)) ∈
      (Finset.univ.filter
        (fun q ↦ slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q')) := by
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [slGamma_p_αToGamma1_mk]
  conv_rhs => rw [← q'.out_eq]
  rw [QuotientGroup.eq, show ((q'.out : SL(2, ℤ)) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN i)⁻¹)⁻¹ * q'.out =
      (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ)) by group]
  exact ds_p_plus_one_family_Gamma1_factor_mem_Gamma1 N p hpN i

open CongruenceSubgroup Classical in
/-- The transversal map `i ↦ ⟦q'.out · ds_factor_i⁻¹⟧` is injective: distinct indices give
distinct cosets in `SL ⧸ Γ_p(A)`. -/
private lemma ds_p_plus_one_family_traceSlash_eq_inj
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) {i₁ i₂ : Option (Fin p)}
    (hii : (QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i₁ : SL(2, ℤ))⁻¹) :
          SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)) =
        QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
          (ds_p_plus_one_family_Gamma1_factor N p hpN i₂ : SL(2, ℤ))⁻¹)) :
    i₁ = i₂ := by
  apply ds_p_plus_one_family_inv_mul_mem_Gamma_p_α_iff p hp hpN
  rw [QuotientGroup.eq] at hii
  rwa [show ((q'.out : SL(2, ℤ)) * (ds_p_plus_one_family_Gamma1_factor N p hpN i₁)⁻¹)⁻¹ *
      ((q'.out : SL(2, ℤ)) * (ds_p_plus_one_family_Gamma1_factor N p hpN i₂)⁻¹) =
      ds_p_plus_one_family_Gamma1_factor N p hpN i₁ *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i₂)⁻¹ by group] at hii

open CongruenceSubgroup Classical in
/-- The connecting-element slash identity: with `e i = ⟦q'.out · ds_factor_i⁻¹⟧`, the slash by
`((e i).out)⁻¹ · q'.out` equals the slash by `ds_factor_i`, using `Γ_p(A)`-invariance of `G`. -/
private lemma ds_p_plus_one_family_traceSlash_eq_conn
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (G : UpperHalfPlane → ℂ)
    (hG : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos), G ∣[k] (γ : SL(2, ℤ)) = G)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) (i : Option (Fin p)) :
    G ∣[k] (((QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) :
          SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)).out : SL(2, ℤ))⁻¹ *
          (q'.out : SL(2, ℤ))) =
      G ∣[k] (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ)) := by
  refine slash_eq_of_inv_mul_mem_Gamma_p_α p hp hpN G hG ?_
  have hquot : (QuotientGroup.mk ((QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) :
          SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)).out) :
      SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)) =
      QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) := by
    rw [QuotientGroup.out_eq']
  rw [QuotientGroup.eq] at hquot
  rw [show (((QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) :
          SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)).out : SL(2, ℤ))⁻¹ *
        (q'.out : SL(2, ℤ))) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹ =
      ((QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) :
          SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)).out)⁻¹ *
        ((q'.out : SL(2, ℤ)) *
          (ds_p_plus_one_family_Gamma1_factor N p hpN i)⁻¹) by group]
  exact hquot

open CongruenceSubgroup Classical in
/-- **(A) The complete `Γ_p(A)\Γ₁` transversal.** The map `i ↦ ⟦q'.out · ds_factor_i⁻¹⟧`
into the fiber `{q : SL ⧸ Γ_p(A) | [q] = q' in SL ⧸ Γ₁}` is a bijection onto the fiber
`Finset` (which has `p + 1` elements). The forward direction is built from the `Γ₁`-membership
of the `ds_factor` reps; injectivity is `ds_p_plus_one_family_inv_mul_mem_Gamma_p_α_iff`;
surjectivity follows by cardinality (`slGamma_p_αToGamma1_fiberCard_T_p_lower`). -/
private lemma ds_p_plus_one_family_traceSlash_eq
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (G : UpperHalfPlane → ℂ)
    (hG : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos), G ∣[k] (γ : SL(2, ℤ)) = G)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos) G q' =
      ∑ i : Option (Fin p), G ∣[k] (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ)) := by
  classical
  rw [traceSlash_Gamma_p_α]
  set fib : Finset (SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)) :=
    Finset.univ.filter (fun q ↦ slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q')
    with hfib_def
  set e : Option (Fin p) → SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos) := fun i ↦
    QuotientGroup.mk ((q'.out : SL(2, ℤ)) *
      (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))⁻¹) with he_def
  have he_mem : ∀ i, e i ∈ fib := fun i ↦
    ds_p_plus_one_family_traceSlash_eq_mem_fib (N := N) p hp hpN q' i
  have he_inj : ∀ i₁ i₂, e i₁ = e i₂ → i₁ = i₂ := fun i₁ i₂ hii ↦
    ds_p_plus_one_family_traceSlash_eq_inj (N := N) p hp hpN q' hii
  have he_conn : ∀ i, G ∣[k] (((e i).out : SL(2, ℤ))⁻¹ * (q'.out : SL(2, ℤ))) =
      G ∣[k] (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ)) := fun i ↦
    ds_p_plus_one_family_traceSlash_eq_conn (N := N) (k := k) p hp hpN G hG q' i
  have hcard : fib.card = Fintype.card (Option (Fin p)) := by
    rw [hfib_def, Fintype.card_option, Fintype.card_fin,
      ← slGamma_p_αToGamma1_fiberCard_T_p_lower p hp hpN,
      ← slGamma_p_αToGamma1_fiberCard_eq (N := N) (T_p_lower p hp.pos) q']
    congr 1; ext q; simp
  refine (Finset.sum_bij (fun (i : Option (Fin p)) _ ↦ e i) (fun i _ ↦ he_mem i)
    (fun i₁ _ i₂ _ h ↦ he_inj i₁ i₂ h) ?_ (fun i _ ↦ (he_conn i).symm)).symm
  intro b hb
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (fun i (_ : i ∈ Finset.univ) ↦ e i)
    (fun i _ ↦ he_mem i) (fun i₁ i₂ _ _ h ↦ he_inj i₁ i₂ h)
    (by rw [hcard]; exact le_of_eq (Finset.card_univ).symm)
  obtain ⟨a, ha, hab⟩ := hsurj b hb
  exact ⟨a, ha, hab.symm⟩

open CongruenceSubgroup in
/-- **(B) per-class double-coset identity.** Slashing `g ∣ A` (`A = glMap T_p_lower`) by the
transversal element `ds_factor_i` equals slashing `⟨p⟩⁻¹ g` by the Hecke representative
`Hecke_rep_i` (`glMap (T_p_upper b)` or `glMap M_∞`). This is the form-level realization of
DS Lemma 5.5.1(c): the matrix identity `A · ds_factor_i = γ₀ · Hecke_rep_i` (`γ₀ =
adjointGamma0Rep ∈ Γ₀(N)`, whose slash IS the `⟨p⟩⁻¹` diamond) transports the slash. -/
private lemma slash_T_p_lower_slash_ds_eq_diamond_inv_slash_Hecke_rep
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (i : Option (Fin p)) :
    (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k]
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ)) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) := by
  have hdiam : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) : UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    show (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g : UpperHalfPlane → ℂ) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [ModularForm.SL_slash,
    show (((ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) from rfl,
    ← SlashAction.slash_mul,
    ← mapGL_gamma0_mul_ds_family_eq_T_p_lower_mul_mapGL_factor N p hp.pos hpN i,
    SlashAction.slash_mul, hdiam]

open CongruenceSubgroup in
/-- **(A)+(B) assembled.** The transversal sum of `(g ∣ A) ∣ ds_factor_i` reassembles, via the
per-class double-coset identity and `heckeT_p_fun_eq_coset_sum` (applied to `⟨p⟩⁻¹ g`), into the
adjoint Hecke operator `⇑(⟨p⟩⁻¹ (T_p g))`. -/
private lemma ds_traceSlash_sum_eq_diamond_inv_heckeT_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ i : Option (Fin p),
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k]
        (ds_p_plus_one_family_Gamma1_factor N p hpN i : SL(2, ℤ))) =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ (heckeT_p_cusp k p hp hpN g)) := by
  simp_rw [slash_T_p_lower_slash_ds_eq_diamond_inv_slash_Hecke_rep p hp hpN g]
  rw [Fintype.sum_option]
  -- RHS: `⟨p⟩⁻¹ (T_p g) = T_p (⟨p⟩⁻¹ g)`, expanded via `heckeT_p_fun_eq_coset_sum`.
  rw [← heckeT_p_cusp_comm_diamondOp_private p hp hpN (ZMod.unitOfCoprime p hpN)⁻¹ g]
  show _ = (heckeT_p k p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm').toFun
  rw [show ((heckeT_p k p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm').toFun :
      UpperHalfPlane → ℂ) =
      heckeT_p_fun k p hp hpN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm'
      from rfl,
    heckeT_p_fun_eq_coset_sum k hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm']
  rw [show heckeT_p_ut k p hp.pos
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [add_comm, Finset.sum_range fun b ↦
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' ∣[k]
      (T_p_upper p hp.pos b : GL (Fin 2) ℚ)]
  rfl

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **TRACE LEAF support lemma (form-level, non-circular).** The partial trace of `g ∣ A`
(`A = glMap T_p_lower`) over the `Γ_p(A)`-fiber above any base coset `q₀` equals the adjoint
Hecke operator `⟨p⟩⁻¹ (T_p g)`. This packages (A) the `ds_p_plus_one_family` transversal of
`Γ_p(A)\Γ₁` and (B) the per-class double-coset slash identity into the DS 5.5.3 trace identity,
mentioning neither `petersson` nor `heckeT_p_adjoint`. -/
theorem ds_traceSlash_Gamma_p_α_T_p_lower_eq_diamond_inv_heckeT_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀ =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ (heckeT_p_cusp k p hp hpN g)) := by
  have hG_slash : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
        ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
    intro γ hγ
    rw [ModularForm.SL_slash,
      show (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) from rfl]
    exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ
  rw [ds_p_plus_one_family_traceSlash_eq p hp hpN
    (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) hG_slash q₀,
    ds_traceSlash_sum_eq_diamond_inv_heckeT_p p hp hpN g]

end HeckeRing.GL2
