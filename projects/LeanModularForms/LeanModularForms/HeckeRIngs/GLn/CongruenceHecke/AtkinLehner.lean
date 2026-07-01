/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Props

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Atkin–Lehner involution

The Atkin–Lehner anti-involution `ι(g) = w · gᵀ · w⁻¹` with `w = diag(1, N)`,
which preserves `Γ₀(N)` and `Δ₀(N)` and fixes every diagonal double coset.
Via Shimura Prop 3.8 this yields commutativity of `𝕋 (Γ₀(N)) ℤ`.

## Main results

* `Gamma0_content_quotient`: a `Δ₀(N)` matrix with content `d` factors as `d` times
  a primitive `Δ₀(N)`-matrix.
* `Gamma0_two_sided_coprime_rep_prim`: two-sided `Γ₀(N)`-clearing producing a
  representative whose `(0,0)` entry is coprime to a target factor of the determinant.
* `instCommRing_Gamma0`: the Hecke ring `𝕋 (Γ₀(N)) ℤ` is commutative.
* `Gamma0_pair_HeckeAlgebra_mul_comm`: the commutativity statement for the Hecke
  ring of `Γ₀(N)` (Shimura Prop 3.8).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

private noncomputable def wN (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  diagMat 2 (![1, N])

private lemma wN_pos (N : ℕ) [NeZero N] : ∀ i : Fin 2, 0 < (![1, N]) i := by
  intro i; fin_cases i <;> simp [NeZero.pos]

private lemma wN_val (N : ℕ) [NeZero N] :
    (↑(wN N) : Matrix (Fin 2) (Fin 2) ℚ) =
    Matrix.diagonal (![1, (N : ℚ)]) := by
  simp [wN, wN_pos N]

private noncomputable def Gamma0_AL_hom (N : ℕ) [NeZero N] :
    GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (wN N * (GL_transposeEquiv 2 g).unop * (wN N)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul]
    have h1 : (GL_transposeEquiv 2 (a * b)).unop =
        (GL_transposeEquiv 2 b).unop * (GL_transposeEquiv 2 a).unop := by
      rw [map_mul]; rfl
    rw [h1]; group

private lemma Gamma0_AL_involutive (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ) :
    (Gamma0_AL_hom N (Gamma0_AL_hom N g).unop).unop = g := by
  simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
  have h_tr : (GL_transposeEquiv 2 (wN N * (GL_transposeEquiv 2 g).unop * (wN N)⁻¹)).unop =
      (GL_transposeEquiv 2 (wN N)⁻¹).unop *
      (GL_transposeEquiv 2 (GL_transposeEquiv 2 g).unop).unop *
      (GL_transposeEquiv 2 (wN N)).unop := by
    rw [map_mul, map_mul]
    simp only [MulOpposite.unop_mul]; group
  have h_wN : (GL_transposeEquiv 2 (wN N)).unop = wN N :=
    diagMat_GL_transpose_eq 2 _ (wN_pos N)
  rw [h_tr, GL_transposeEquiv_involutive, h_wN]
  have h_inv : (GL_transposeEquiv 2 (wN N)⁻¹).unop = (wN N)⁻¹ := by
    rw [map_inv, MulOpposite.unop_inv, h_wN]
  rw [h_inv]; group

private lemma Gamma0_AL_map_H (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).H) :
    (Gamma0_AL_hom N g).unop ∈ (Gamma0_pair N).H := by
  simp only [Gamma0_pair] at hg ⊢
  change _ ∈ Subgroup.map (mapGL ℚ) (CongruenceSubgroup.Gamma0 N)
  rw [Subgroup.mem_map] at hg ⊢
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [CongruenceSubgroup.Gamma0_mem] at hσ_mem
  set A := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hA_def
  have hA_det : A.det = 1 := σ.2
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσ_mem
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![A 0 0, c'], ![↑N * A 0 1, A 1 1]]
  have hB_det : B.det = 1 := by
    simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    rw [hA_det] at this
    linarith [show c' * (↑N * A 0 1) = A 0 1 * A 1 0 by rw [hc']; ring]
  set τ : SpecialLinearGroup (Fin 2) ℤ := ⟨B, hB_det⟩
  refine ⟨τ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (↑(B 1 0) : ZMod N) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [B, Matrix.cons_val_one, Matrix.of_apply]
    exact dvd_mul_right _ _
  · simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
    suffices h : (mapGL ℚ) τ * wN N =
        wN N * MulOpposite.unop ((GL_transposeEquiv 2) ((mapGL ℚ) σ)) by
      rwa [eq_mul_inv_iff_mul_eq]
    apply Units.ext; ext i j
    simp only [GeneralLinearGroup.coe_mul, GL_transposeEquiv_val, wN_val,
      mapGL_coe_matrix, algebraMap_int_eq, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.diagonal, Matrix.transpose_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> norm_num [τ, B, hc', hA_def]
    · exact_mod_cast show c' * ↑N = A 1 0 by rw [hc']; ring
    · ring

private lemma Gamma0_AL_map_Δ (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ) :
    (Gamma0_AL_hom N g).unop ∈ (Gamma0_pair N).Δ := by
  simp only [Gamma0_pair] at hg ⊢
  change _ ∈ Delta0_submonoid N
  obtain ⟨_, hdet_pos, A, hA, hAN, hAco⟩ := hg
  obtain ⟨c', hc'⟩ := hAN
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![A 0 0, c'], ![↑N * A 0 1, A 1 1]]
  have hB_det : B.det = A.det := by
    simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    linarith [show c' * (↑N * A 0 1) = A 0 1 * A 1 0 by rw [hc']; ring]
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  have hB_det_pos : 0 < B.det := hB_det ▸ hA_det_pos
  have hB_ne : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [det_intMat_cast]; exact_mod_cast hB_det_pos.ne'
  set g' : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero _ hB_ne
  have hg'_eq : (Gamma0_AL_hom N g).unop = g' := by
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
    suffices h : g' * wN N =
        wN N * MulOpposite.unop ((GL_transposeEquiv 2) g) by
      rw [← h]; group
    apply Units.ext; ext i j
    simp only [GeneralLinearGroup.coe_mul, GL_transposeEquiv_val, wN_val,
      Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
      Fin.sum_univ_two, hA, g', GeneralLinearGroup.mkOfDetNeZero]
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.map_apply]
    · exact_mod_cast show c' * ↑N = A 1 0 by rw [hc']; ring
    · ring
  rw [hg'_eq]
  have hval : (↑g' : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ) := rfl
  have hdet_g' : 0 < (↑g' : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [hval, det_intMat_cast 2]; exact_mod_cast hB_det_pos
  refine ⟨⟨B, hval⟩, hdet_g', B, hval, ?_, ?_⟩
  · simp only [B, Matrix.cons_val_one, Matrix.of_apply]
    exact dvd_mul_right _ _
  · simp only [B, Matrix.cons_val_zero, Matrix.of_apply]
    exact hAco

private noncomputable def Gamma0_antiInvolution (N : ℕ) [NeZero N] :
    AntiInvolution (Gamma0_pair N) where
  toFun := Gamma0_AL_hom N
  involutive := Gamma0_AL_involutive N
  map_H := Gamma0_AL_map_H N
  map_Δ := Gamma0_AL_map_Δ N

private lemma Gamma0_AL_bar_det (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ) :
    ((Gamma0_antiInvolution N).bar g : Matrix (Fin 2) (Fin 2) ℚ).det =
    (g : Matrix (Fin 2) (Fin 2) ℚ).det := by
  show ((Gamma0_AL_hom N g).unop : GL (Fin 2) ℚ).val.det = g.val.det
  simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
    Units.val_mul, Matrix.det_mul, GL_transposeEquiv_val, MulOpposite.unop_op,
    Matrix.det_transpose]
  have h1 : (wN N : GL (Fin 2) ℚ).val.det * ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]; simp
  rw [mul_right_comm, h1, one_mul]

private lemma snf_first_dvd_entry₂ (M : Matrix (Fin 2) (Fin 2) ℤ)
    (d : Fin 2 → ℤ) (hd_div : d 0 ∣ d 1)
    (L R : SpecialLinearGroup (Fin 2) ℤ)
    (hLR : (L : Matrix (Fin 2) (Fin 2) ℤ) * M * (R : Matrix _ _ ℤ) = Matrix.diagonal d)
    (i j : Fin 2) : d 0 ∣ M i j := by
  have hRR : (R : Matrix _ _ ℤ) * (R⁻¹).val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; simp
  have hLM : L.val * M = Matrix.diagonal d * (R⁻¹).val := by
    have h1 : L.val * M = (L.val * M * R.val) * (R⁻¹).val := by
      rw [Matrix.mul_assoc (L.val * M), hRR, Matrix.mul_one]
    rw [h1, hLR]
  have h_row : ∀ k l, L.val k 0 * M 0 l + L.val k 1 * M 1 l =
      d k * (R⁻¹).val k l := by
    intro k l; have h := congr_fun₂ hLM k l
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    convert h using 1
    simp only [Matrix.diagonal_apply]; fin_cases k <;> simp
  have hd0 : ∀ l, d 0 ∣ L.val 0 0 * M 0 l + L.val 0 1 * M 1 l :=
    fun l ↦ ⟨_, h_row 0 l⟩
  have hd1 : ∀ l, d 0 ∣ L.val 1 0 * M 0 l + L.val 1 1 * M 1 l :=
    fun l ↦ (h_row 1 l) ▸ hd_div.mul_right _
  have hdet_L : L.val 0 0 * L.val 1 1 - L.val 0 1 * L.val 1 0 = 1 := by
    have := L.prop; rwa [Matrix.det_fin_two] at this
  have h_M0 : ∀ l, d 0 ∣ M 0 l := fun l ↦ by
    have : L.val 1 1 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) -
        L.val 0 1 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) =
        (L.val 0 0 * L.val 1 1 - L.val 0 1 * L.val 1 0) * M 0 l := by ring
    rw [show M 0 l = L.val 1 1 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) -
        L.val 0 1 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) by rw [this, hdet_L, one_mul]]
    exact dvd_sub (dvd_mul_of_dvd_right (hd0 l) _) (dvd_mul_of_dvd_right (hd1 l) _)
  have h_M1 : ∀ l, d 0 ∣ M 1 l := fun l ↦ by
    have : L.val 0 0 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) -
        L.val 1 0 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) =
        (L.val 0 0 * L.val 1 1 - L.val 0 1 * L.val 1 0) * M 1 l := by ring
    rw [show M 1 l = L.val 0 0 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) -
        L.val 1 0 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) by rw [this, hdet_L, one_mul]]
    exact dvd_sub (dvd_mul_of_dvd_right (hd1 l) _) (dvd_mul_of_dvd_right (hd0 l) _)
  fin_cases i
  · exact h_M0 j
  · exact h_M1 j

private lemma Gamma0_AL_in_DC_bad (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ)
    (m : ℕ) (hm_pos : 0 < m) (k : ℕ) (hm_dvd : m ∣ N ^ k)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  rw [DoubleCoset.doubleCoset_eq_of_mem (shimura_prop_3_33 N m hm_pos k hm_dvd g hg hdet)]
  exact shimura_prop_3_33 N m hm_pos k hm_dvd ((Gamma0_antiInvolution N).bar g)
    (Gamma0_AL_map_Δ N g hg) (Gamma0_AL_bar_det N g ▸ hdet)

private lemma dvd_snf_first_of_dvd_entries (M : Matrix (Fin 2) (Fin 2) ℤ) (d : ℤ)
    (dvec : Fin 2 → ℤ) (L R : SpecialLinearGroup (Fin 2) ℤ)
    (hSNF : (L : Matrix (Fin 2) (Fin 2) ℤ) * M * (R : Matrix _ _ ℤ) = Matrix.diagonal dvec)
    (hd : ∀ i j, d ∣ M i j) : d ∣ dvec 0 := by
  have h := congr_fun₂ hSNF 0 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ite_true] at h
  rw [← h]
  exact dvd_add
    (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right (hd 0 0) _)
      (dvd_mul_of_dvd_right (hd 1 0) _)) _)
    (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right (hd 0 1) _)
      (dvd_mul_of_dvd_right (hd 1 1) _)) _)

private lemma snf_mutual_dvd_eq (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (dA dB : Fin 2 → ℤ) (hdA_pos : ∀ i, 0 < dA i) (hdB_pos : ∀ i, 0 < dB i)
    (LA RA LB RB : SpecialLinearGroup (Fin 2) ℤ)
    (hSNF_A : (LA : Matrix (Fin 2) (Fin 2) ℤ) * A * (RA : Matrix _ _ ℤ) = Matrix.diagonal dA)
    (hSNF_B : (LB : Matrix (Fin 2) (Fin 2) ℤ) * B * (RB : Matrix _ _ ℤ) = Matrix.diagonal dB)
    (hB_det : B.det = A.det)
    (hdA_B : ∀ i j, dA 0 ∣ B i j) (hdB_A : ∀ i j, dB 0 ∣ A i j) :
    ((LB⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix _ _ ℤ) * (LA : Matrix _ _ ℤ) * A *
      ((RA : Matrix _ _ ℤ) *
        ((RB⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix _ _ ℤ)) = B := by
  have h_d0 : dA 0 = dB 0 :=
    le_antisymm
      (Int.le_of_dvd (hdB_pos 0) (dvd_snf_first_of_dvd_entries B (dA 0) dB LB RB hSNF_B hdA_B))
      (Int.le_of_dvd (hdA_pos 0) (dvd_snf_first_of_dvd_entries A (dB 0) dA LA RA hSNF_A hdB_A))
  have hprod_A : dA 0 * dA 1 = A.det := by
    have h := congr_arg Matrix.det hSNF_A
    simp only [Matrix.det_mul, LA.prop, RA.prop, one_mul, mul_one,
      Matrix.det_diagonal, Fin.prod_univ_two] at h; linarith
  have hprod_B : dB 0 * dB 1 = B.det := by
    have h := congr_arg Matrix.det hSNF_B
    simp only [Matrix.det_mul, LB.prop, RB.prop, one_mul, mul_one,
      Matrix.det_diagonal, Fin.prod_univ_two] at h; linarith
  have h_d1 : dA 1 = dB 1 :=
    mul_left_cancel₀ (ne_of_gt (hdA_pos 0))
      (show dA 0 * dA 1 = dA 0 * dB 1 by rw [hprod_A, h_d0, hprod_B, hB_det])
  have h_diag : Matrix.diagonal dA = Matrix.diagonal dB := by
    congr 1; ext k; fin_cases k <;> assumption
  have hLL : (LB⁻¹ : SpecialLinearGroup (Fin 2) ℤ).val * LB.val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel]; simp
  have hRR : RB.val * (RB⁻¹ : SpecialLinearGroup (Fin 2) ℤ).val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; simp
  calc (LB⁻¹ : SpecialLinearGroup (Fin 2) ℤ).val * LA.val * A * (RA.val * (RB⁻¹).val)
      = (LB⁻¹).val * (LA.val * A * RA.val) * (RB⁻¹).val := by simp only [Matrix.mul_assoc]
    _ = (LB⁻¹).val * Matrix.diagonal dB * (RB⁻¹).val := by rw [hSNF_A, h_diag]
    _ = (LB⁻¹).val * (LB.val * B * RB.val) * (RB⁻¹).val := by rw [hSNF_B]
    _ = B := by
        simp only [Matrix.mul_assoc]
        rw [show (LB⁻¹).val * (LB.val * (B * (RB.val * (RB⁻¹).val))) =
            (LB⁻¹).val * (LB.val * (B * 1)) by rw [hRR]]
        rw [Matrix.mul_one, ← Matrix.mul_assoc (LB⁻¹).val, hLL, Matrix.one_mul]

private lemma bar_val_eq_swap (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (c₀ : ℤ) (hc₀ : A 1 0 = ↑N * c₀) :
    (↑((Gamma0_antiInvolution N).bar g) : Matrix (Fin 2) (Fin 2) ℚ) =
      (Matrix.of ![![A 0 0, c₀], ![↑N * A 0 1, A 1 1]]).map (Int.cast : ℤ → ℚ) := by
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![A 0 0, c₀], ![↑N * A 0 1, A 1 1]]
  have hB_det : B.det = A.det := by
    simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    linarith [show c₀ * (↑N * A 0 1) = A 0 1 * A 1 0 by rw [hc₀]; ring]
  have hA_det_ne : A.det ≠ 0 := by
    have hg_ne : (g : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero g
    rw [hA, det_intMat_cast] at hg_ne; exact_mod_cast hg_ne
  have hB_ne : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [det_intMat_cast]; exact_mod_cast hB_det ▸ hA_det_ne
  set g' : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero _ hB_ne
  have hg'_eq : (Gamma0_antiInvolution N).bar g = g' := by
    show (Gamma0_AL_hom N g).unop = g'
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
    suffices h : g' * wN N = wN N * MulOpposite.unop ((GL_transposeEquiv 2) g) by
      rw [← h]; group
    apply Units.ext; ext i j
    simp only [GeneralLinearGroup.coe_mul, GL_transposeEquiv_val, wN_val,
      Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
      Fin.sum_univ_two, hA, g', GeneralLinearGroup.mkOfDetNeZero]
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.map_apply]
    · exact_mod_cast show c₀ * ↑N = A 1 0 by rw [hc₀]; ring
    · ring
  rw [hg'_eq]; rfl

private lemma dvd_swap_entries (A : Matrix (Fin 2) (Fin 2) ℤ) (N e c₀ : ℤ)
    (hc₀ : A 1 0 = N * c₀) (he : ∀ i j, e ∣ A i j) (heN : IsCoprime e N) :
    ∀ i j, e ∣ (Matrix.of ![![A 0 0, c₀], ![N * A 0 1, A 1 1]] :
      Matrix (Fin 2) (Fin 2) ℤ) i j := by
  intro i j; fin_cases i <;> fin_cases j
  · simpa using he 0 0
  · simpa using heN.dvd_of_dvd_mul_left (hc₀ ▸ he 1 0)
  · simpa using dvd_mul_of_dvd_right (he 0 1) _
  · simpa using he 1 1

private lemma gl_eq_of_intMat_eq (g h : GL (Fin 2) ℚ)
    (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (h : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ))
    (P Q : SpecialLinearGroup (Fin 2) ℤ)
    (hPQ : (P : Matrix (Fin 2) (Fin 2) ℤ) * A * (Q : Matrix _ _ ℤ) = B) :
    h = mapGL ℚ P * g * mapGL ℚ Q := by
  apply Units.ext; ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two, hA,
    mapGL_coe_matrix, algebraMap_int_eq]
  have hcast := congr_fun₂
    (congr_arg (fun M : Matrix _ _ ℤ ↦ M.map (Int.cast : ℤ → ℚ)) hPQ) i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two, Int.cast_add,
    Int.cast_mul] at hcast
  simp only [SpecialLinearGroup.map, MonoidHom.coe_mk,
    OneHom.coe_mk, RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply]
  rw [hB] at *; simp only [Matrix.map_apply] at hcast ⊢
  linarith

private lemma bar_eq_SL2_conj (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1) :
    ∃ P Q : SpecialLinearGroup (Fin 2) ℤ,
      (Gamma0_antiInvolution N).bar g = mapGL ℚ P * g * mapGL ℚ Q := by
  obtain ⟨c₀, hc₀⟩ := hAN
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![A 0 0, c₀], ![↑N * A 0 1, A 1 1]] with hB_def
  have hB_det : B.det = A.det := by
    simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    linarith [show c₀ * (↑N * A 0 1) = A 0 1 * A 1 0 by rw [hc₀]; ring]
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]; exact hg.2.1
  obtain ⟨dA, hdA_pos, hdA_div, LA, RA, hSNF_A⟩ :=
    exists_divchain_diagonal_of_posdet 2 A hA_det_pos
  obtain ⟨dB, hdB_pos, hdB_div, LB, RB, hSNF_B⟩ :=
    exists_divchain_diagonal_of_posdet 2 B (hB_det ▸ hA_det_pos)
  have hdA_A : ∀ i j, dA 0 ∣ A i j :=
    snf_first_dvd_entry₂ A dA (hdA_div 0 (by omega)) LA RA hSNF_A
  have hdB_B : ∀ i j, dB 0 ∣ B i j :=
    snf_first_dvd_entry₂ B dB (hdB_div 0 (by omega)) LB RB hSNF_B
  have hAco_isCop : IsCoprime (A 0 0) (↑N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hAco
  have hB00 : B 0 0 = A 0 0 := by simp [B, Matrix.of_apply, Matrix.cons_val_zero]
  have hdA_B : ∀ i j, dA 0 ∣ B i j := by
    rw [hB_def]
    exact dvd_swap_entries A ↑N (dA 0) c₀ hc₀ hdA_A
      (hAco_isCop.of_isCoprime_of_dvd_left (hdA_A 0 0))
  have hcB : B 1 0 = ↑N * A 0 1 := by simp [B, Matrix.of_apply, Matrix.cons_val_one]
  have hswap : (Matrix.of ![![B 0 0, A 0 1], ![↑N * B 0 1, B 1 1]] :
      Matrix (Fin 2) (Fin 2) ℤ) = A := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [B, hc₀, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdB_A : ∀ i j, dB 0 ∣ A i j := fun i j ↦ by
    have h := dvd_swap_entries B ↑N (dB 0) (A 0 1) hcB hdB_B
      (hAco_isCop.of_isCoprime_of_dvd_left (hB00 ▸ hdB_B 0 0)) i j
    rwa [hswap] at h
  have h_int := snf_mutual_dvd_eq A B dA dB hdA_pos hdB_pos LA RA LB RB hSNF_A hSNF_B
    hB_det hdA_B hdB_A
  rw [← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_mul] at h_int
  exact ⟨LB⁻¹ * LA, RA * RB⁻¹, gl_eq_of_intMat_eq g ((Gamma0_antiInvolution N).bar g) A B
    hA (bar_val_eq_swap N g A hA c₀ hc₀) (LB⁻¹ * LA) (RA * RB⁻¹) h_int⟩

private lemma Gamma0_AL_in_DC_coprime (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (hdet_coprime : Int.gcd A.det N = 1) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  set a_sub : (Gamma0_pair N).Δ := ⟨g, hg⟩
  set b_sub : (Gamma0_pair N).Δ := ⟨(Gamma0_antiInvolution N).bar g, Gamma0_AL_map_Δ N g hg⟩
  have ha_cop : CoprimeDet N a_sub := fun A' hA' ↦ by
    have : A' = A := by
      ext i j; have h := congr_fun₂ (hA'.symm.trans hA) i j
      simp only [Matrix.map_apply] at h; exact_mod_cast h
    rw [this]; exact hdet_coprime
  have hb_cop : CoprimeDet N b_sub := fun B hB_eq ↦ by
    have hBdet : B.det = A.det := by
      have h1 := det_intMat_cast 2 B; rw [← hB_eq, Gamma0_AL_bar_det, hA, det_intMat_cast] at h1
      exact_mod_cast h1.symm
    rw [hBdet]; exact hdet_coprime
  have h_coset_eq : cosetMap N ⟦a_sub⟧ = cosetMap N ⟦b_sub⟧ := by
    obtain ⟨P, Q, hPQ⟩ := bar_eq_SL2_conj N g hg A hA hAN hAco
    change (⟦Delta0_inclusion N a_sub⟧ : HeckeCoset (GL_pair 2)) =
      ⟦Delta0_inclusion N b_sub⟧
    rw [HeckeCoset.eq_iff]
    symm; apply DoubleCoset.doubleCoset_eq_of_mem
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨mapGL ℚ P, coe_mem_SLnZ 2 _, mapGL ℚ Q, coe_mem_SLnZ 2 _, hPQ⟩
  have h_Gamma0_eq := shimura_prop_3_31 N a_sub b_sub ha_cop hb_cop h_coset_eq
  rw [HeckeCoset.eq_iff] at h_Gamma0_eq
  rw [DoubleCoset.doubleCoset_eq_of_mem (show g ∈ DoubleCoset.doubleCoset g _ _ from
    DoubleCoset.mem_doubleCoset_self _ _ g), h_Gamma0_eq]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

private lemma entry_clear_prime (A : Matrix (Fin 2) (Fin 2) ℤ) (N : ℤ)
    (p : ℕ) (hp : p.Prime) (hpN : ¬((p : ℤ) ∣ N))
    (hprim : ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)) :
    ∃ l t : ℤ, ¬((p : ℤ) ∣ (A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1))) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases ha : (p : ℤ) ∣ A 0 0
  · by_cases hc : (p : ℤ) ∣ A 1 0
    · by_cases hb : (p : ℤ) ∣ A 0 1
      · have hd : ¬((p : ℤ) ∣ A 1 1) := fun hd ↦ hprim ⟨ha, hb, hc, hd⟩
        refine ⟨1, 1, fun h ↦ hd ?_⟩
        have h1 : (p : ℤ) ∣ A 0 0 + A 1 0 + N * A 0 1 :=
          dvd_add (dvd_add ha hc) (dvd_mul_of_dvd_right hb _)
        have h2 := dvd_sub h h1
        rw [show A 0 0 + 1 * A 1 0 + N * 1 * (A 0 1 + 1 * A 1 1) -
          (A 0 0 + A 1 0 + N * A 0 1) = N * A 1 1 by ring] at h2
        exact (hp'.dvd_mul.mp h2).resolve_left hpN
      · refine ⟨0, 1, fun h ↦ hb ?_⟩
        have h1 := dvd_sub h ha
        rw [show A 0 0 + 0 * A 1 0 + N * 1 * (A 0 1 + 0 * A 1 1) - A 0 0 =
          N * A 0 1 by ring] at h1
        exact (hp'.dvd_mul.mp h1).resolve_left hpN
    · refine ⟨1, 0, fun h ↦ hc ?_⟩
      have h1 := dvd_sub h ha
      rwa [show A 0 0 + 1 * A 1 0 + N * 0 * (A 0 1 + 1 * A 1 1) - A 0 0 =
        A 1 0 by ring] at h1
  · exact ⟨0, 0, by rwa [show A 0 0 + 0 * A 1 0 + N * 0 * (A 0 1 + 0 * A 1 1) =
      A 0 0 by ring]⟩

private lemma f_congr_mod (p : ℕ) (l l' t t' a b c₀ d N : ℤ)
    (hl : (p : ℤ) ∣ (l - l')) (ht : (p : ℤ) ∣ (t - t')) :
    (p : ℤ) ∣ ((a + l * c₀ + N * t * (b + l * d)) -
      (a + l' * c₀ + N * t' * (b + l' * d))) := by
  have hlt : (p : ℤ) ∣ (l * t - l' * t') := by
    rw [show l * t - l' * t' = (l - l') * t + l' * (t - t') by ring]
    exact dvd_add (dvd_mul_of_dvd_left hl _) (dvd_mul_of_dvd_right ht _)
  rw [show a + l * c₀ + N * t * (b + l * d) - (a + l' * c₀ + N * t' * (b + l' * d)) =
    (l - l') * c₀ + N * ((t - t') * b + (l * t - l' * t') * d) by ring]
  exact dvd_add (dvd_mul_of_dvd_left hl _)
    (dvd_mul_of_dvd_right (dvd_add (dvd_mul_of_dvd_left ht _) (dvd_mul_of_dvd_left hlt _)) _)

/-- Content quotient: given integer matrix `A` with positive det, `N | A 1 0`,
`gcd(A 0 0, N) = 1`, and content `d` dividing all entries, produce primitive
quotient `A₀ = A/d` preserving the Δ₀(N) properties. -/
lemma Gamma0_content_quotient (N : ℕ) [NeZero N]
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA_det_pos : 0 < A.det)
    (hAN : (N : ℤ) ∣ A 1 0)
    (hAco : Int.gcd (A 0 0) N = 1)
    (d : ℕ) (hd_pos : 0 < d)
    (hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j)
    (hd_is_gcd : d = Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
                    (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs)) :
    ∃ (A₀ : Matrix (Fin 2) (Fin 2) ℤ),
      (∀ i j, A i j = ↑d * A₀ i j) ∧
      0 < A₀.det ∧
      (N : ℤ) ∣ A₀ 1 0 ∧
      Int.gcd (A₀ 0 0) N = 1 ∧
      (∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A₀ 0 0 ∧ (p : ℤ) ∣ A₀ 0 1 ∧
        (p : ℤ) ∣ A₀ 1 0 ∧ (p : ℤ) ∣ A₀ 1 1)) := by
  set A₀ : Matrix (Fin 2) (Fin 2) ℤ := fun i j ↦ A i j / d
  have hA_eq : ∀ i j, A i j = ↑d * A₀ i j := fun i j ↦ by
    simp only [A₀]; rw [mul_comm]; exact (Int.ediv_mul_cancel (hd_dvd i j)).symm
  have hdet_eq : A.det = ↑d ^ 2 * A₀.det := by
    simp only [Matrix.det_fin_two]; rw [hA_eq 0 0, hA_eq 0 1, hA_eq 1 0, hA_eq 1 1]; ring
  have hd_Nco : Int.gcd (d : ℤ) N = 1 := by
    apply Nat.eq_one_of_dvd_one; rw [← hAco]
    exact Nat.dvd_gcd
      (Int.natAbs_dvd_natAbs.mpr ((Int.gcd_dvd_left (d : ℤ) N).trans (hd_dvd 0 0)))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (d : ℤ) N))
  refine ⟨A₀, hA_eq, ?_, ?_, ?_, ?_⟩
  · exact (mul_pos_iff.mp (hdet_eq ▸ hA_det_pos)).elim (fun ⟨_, r⟩ ↦ r)
      (fun ⟨l, _⟩ ↦ absurd l (not_lt.mpr (sq_nonneg (d : ℤ))))
  · exact (Int.isCoprime_iff_gcd_eq_one.mpr hd_Nco).symm.dvd_of_dvd_mul_left
      (hA_eq 1 0 ▸ hAN)
  · exact Int.isCoprime_iff_gcd_eq_one.mp
      ((Int.isCoprime_iff_gcd_eq_one.mpr (hA_eq 0 0 ▸ hAco)).of_isCoprime_of_dvd_left
        (dvd_mul_left (A₀ 0 0) (↑d)))
  · intro q hq ⟨hq00, hq01, hq10, hq11⟩
    have hqd_nat : ∀ i j : Fin 2, q * d ∣ (A i j).natAbs := fun i j ↦ by
      have h : (↑q : ℤ) ∣ A₀ i j := by fin_cases i <;> fin_cases j <;> assumption
      rw [show (A i j).natAbs = ((↑d : ℤ) * A₀ i j).natAbs by rw [← hA_eq],
        Int.natAbs_mul, Int.natAbs_natCast]
      rw [mul_comm]; exact Nat.mul_dvd_mul_left d (Int.natAbs_dvd_natAbs.mpr h)
    have hqd_dvd_d : q * d ∣ d := by
      conv_rhs => rw [hd_is_gcd]
      exact Nat.dvd_gcd
        (Nat.dvd_gcd (hqd_nat 0 0) (hqd_nat 0 1))
        (Nat.dvd_gcd (hqd_nat 1 0) (hqd_nat 1 1))
    have : q ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by linarith [Nat.le_of_dvd hd_pos hqd_dvd_d]) hd_pos
    exact absurd hq.two_le (by omega)

private lemma int_dvd_sub_of_modEq_toNat (n p : ℕ) (x : ℤ) (hp_ne : (p : ℤ) ≠ 0)
    (h : Nat.ModEq p n (x % (p : ℤ)).toNat) : (p : ℤ) ∣ ((n : ℤ) - x) := by
  obtain ⟨a', ha'⟩ := Nat.modEq_iff_dvd.mp h
  obtain ⟨b', hb'⟩ : (p : ℤ) ∣ ((x % (p : ℤ)).toNat : ℤ) - x := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp_ne)]
    exact ⟨-(x / p), by rw [Int.emod_def]; ring⟩
  exact ⟨-a' + b', by linear_combination -ha' + hb'⟩

private lemma exists_coprime_entry (A : Matrix (Fin 2) (Fin 2) ℤ) (N : ℤ)
    (c : ℕ) (hc_pos : 0 < c)
    (hprim : ∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1))
    (hcN : ∀ (p : ℕ), p.Prime → (p : ℤ) ∣ ↑c → ¬((p : ℤ) ∣ N)) :
    ∃ l t : ℤ, Int.gcd (A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1)) ↑c = 1 := by
  have havoid : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ↑c →
      ∃ l t : ℤ, ¬((p : ℤ) ∣ (A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1))) :=
    fun p hp hpc ↦ entry_clear_prime A N p hp (hcN p hp hpc)
      (fun ⟨h1, h2, h3, h4⟩ ↦ hprim p hp ⟨h1, h2, h3, h4⟩)
  classical
  set wit : ℕ → ℤ × ℤ := fun p ↦
    if h : p.Prime ∧ (p : ℤ) ∣ ↑c
    then ⟨(havoid p h.1 h.2).choose, (havoid p h.1 h.2).choose_spec.choose⟩
    else ⟨0, 0⟩
  set aL : ℕ → ℕ := fun p ↦ ((wit p).1 % (p : ℤ)).toNat
  set aT : ℕ → ℕ := fun p ↦ ((wit p).2 % (p : ℤ)).toNat
  have hpw : (c.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact ((Nat.mem_primeFactors.mp hp).1).coprime_iff_not_dvd.mpr
      (fun h ↦ hpq (((Nat.mem_primeFactors.mp hq).1).eq_one_or_self_of_dvd p h |>.resolve_left
        ((Nat.mem_primeFactors.mp hp).1).one_lt.ne'))
  have hpnz : ∀ p ∈ c.primeFactors, (id p : ℕ) ≠ 0 :=
    fun p hp ↦ ((Nat.mem_primeFactors.mp hp).1).ne_zero
  obtain ⟨l₀, hl₀⟩ := Nat.chineseRemainderOfFinset aL id c.primeFactors hpnz hpw
  obtain ⟨t₀, ht₀⟩ := Nat.chineseRemainderOfFinset aT id c.primeFactors hpnz hpw
  refine ⟨↑l₀, ↑t₀, ?_⟩
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpc : (p : ℤ) ∣ ↑c := Int.natCast_dvd_natCast.mpr (Int.natCast_dvd_natCast.mp
    (dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right _ _)))
  have hp_mem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, Int.natCast_dvd_natCast.mp hpc, by omega⟩
  have hwit : wit p = ⟨(havoid p hp hpc).choose, (havoid p hp hpc).choose_spec.choose⟩ :=
    dif_pos ⟨hp, hpc⟩
  have hl_crt : Nat.ModEq p l₀ (aL p) := by simpa using hl₀ p hp_mem
  have ht_crt : Nat.ModEq p t₀ (aT p) := by simpa using ht₀ p hp_mem
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hcongr := f_congr_mod p ↑l₀ (wit p).1 ↑t₀ (wit p).2
    (A 0 0) (A 0 1) (A 1 0) (A 1 1) N
    (int_dvd_sub_of_modEq_toNat l₀ p (wit p).1 hp_ne hl_crt)
    (int_dvd_sub_of_modEq_toNat t₀ p (wit p).2 hp_ne ht_crt)
  rw [show (wit p).1 = (havoid p hp hpc).choose by rw [hwit],
      show (wit p).2 = (havoid p hp hpc).choose_spec.choose by rw [hwit]] at hcongr
  apply (havoid p hp hpc).choose_spec.choose_spec
  obtain ⟨k, hk⟩ := hcongr
  obtain ⟨m, hm⟩ := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left _ _)
  exact ⟨m - k, by linear_combination hm - hk⟩

private lemma mapGL_conj_val (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (P Q : SpecialLinearGroup (Fin 2) ℤ) :
    ((mapGL ℚ P) * g * (mapGL ℚ Q) : GL (Fin 2) ℚ).val =
      ((P : Matrix (Fin 2) (Fin 2) ℤ) * A * (Q : Matrix _ _ ℤ)).map
        (Int.cast : ℤ → ℚ) := by
  rw [Units.val_mul, Units.val_mul, mapGL_coe_matrix, mapGL_coe_matrix, hA]
  simp only [SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.mapMatrix_apply,
    algebraMap_int_eq, Int.coe_castRingHom, SpecialLinearGroup.coe_mk]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Int.cast_add, Int.cast_mul]

private lemma not_intCast_dvd_of_coprime (c N p : ℕ) (hp : p.Prime)
    (hc_cop : Nat.Coprime c N) (hpc : (p : ℤ) ∣ ↑c) : ¬((p : ℤ) ∣ ↑N) := by
  intro hpN
  have h1 := (hc_cop.coprime_dvd_right (Int.natCast_dvd_natCast.mp hpN)).coprime_dvd_left
    (Int.natCast_dvd_natCast.mp hpc)
  rw [Nat.Coprime, Nat.gcd_self] at h1; exact absurd h1 hp.one_lt.ne'

/-- Two-sided `Γ₀(N)` clearing for primitive matrices: given `g ∈ Δ₀(N)` with
`gcd(entries of A) = 1` and coprime-to-`N` target `c ∣ det`, find `γL, γR ∈ Γ₀(N)` such that
`γL * g * γR` has integer matrix `A'` with `gcd(A' 0 0, c) = 1`. -/
lemma Gamma0_two_sided_coprime_rep_prim (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (_hg : g ∈ (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (hprim : ∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1))
    (c : ℕ) (hc_pos : 0 < c) (hc_cop : Nat.Coprime c N) (_hc_dvd : (c : ℤ) ∣ A.det) :
    ∃ (γL γR : (Gamma0_pair N).H),
      let g' := (γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ)
      ∃ (A' : Matrix (Fin 2) (Fin 2) ℤ),
        (g' : Matrix (Fin 2) (Fin 2) ℚ) = A'.map (Int.cast : ℤ → ℚ) ∧
        (N : ℤ) ∣ A' 1 0 ∧ Int.gcd (A' 0 0) N = 1 ∧ Int.gcd (A' 0 0) c = 1 := by
  obtain ⟨l₀, t₀, hlt⟩ := exists_coprime_entry A ↑N c hc_pos hprim
    (fun p hp hpc ↦ not_intCast_dvd_of_coprime c N p hp hc_cop hpc)
  set L : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, l₀], ![0, 1]]
  have hL_det : L.det = 1 := by
    simp [L, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  set L_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨L, hL_det⟩
  set R : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![↑N * t₀, 1]]
  have hR_det : R.det = 1 := by
    simp [R, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  set R_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨R, hR_det⟩
  have hL_Gamma0 : L_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [L_sl, L, Matrix.of_apply, Matrix.cons_val_one]
  have hR_Gamma0 : R_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [R_sl, R, Matrix.of_apply, Matrix.cons_val_one]
  refine ⟨⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ hL_Gamma0⟩,
    ⟨mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ hR_Gamma0⟩, ?_⟩
  set A' := L * A * R
  have h00 : A' 0 0 = A 0 0 + l₀ * A 1 0 + (A 0 1 + l₀ * A 1 1) * (↑N * t₀) := by
    show (L * A * R) 0 0 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, L, R, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have h10 : A' 1 0 = A 1 0 + A 1 1 * (↑N * t₀) := by
    show (L * A * R) 1 0 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, L, R, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · exact mapGL_conj_val g A hA L_sl R_sl
  · rw [h10, show A 1 0 + A 1 1 * (↑N * t₀) = A 1 0 + ↑N * (A 1 1 * t₀) by ring]
    exact dvd_add hAN (dvd_mul_right _ _)
  · obtain ⟨k, hk⟩ := hAN
    rw [h00, hk, show A 0 0 + l₀ * (↑N * k) + (A 0 1 + l₀ * A 1 1) * (↑N * t₀) =
      A 0 0 + ↑N * (l₀ * k + (A 0 1 + l₀ * A 1 1) * t₀) by ring]
    rw [Int.gcd_add_mul_left_left]; exact hAco
  · rw [h00, show A 0 0 + l₀ * A 1 0 + (A 0 1 + l₀ * A 1 1) * (↑N * t₀) =
      A 0 0 + l₀ * A 1 0 + ↑N * t₀ * (A 0 1 + l₀ * A 1 1) by ring]
    exact hlt

private lemma Gamma0_AL_scalar_reduce (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (s : GL (Fin 2) ℚ)
    (hs_central : ∀ h : GL (Fin 2) ℚ, s * h = h * s)
    (hs_bar : (Gamma0_antiInvolution N).bar s = s)
    (h_prim : ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _)) :
    ((Gamma0_antiInvolution N).bar (s * g)) ∈
      DoubleCoset.doubleCoset (s * g) ((Gamma0_pair N).H : Set _)
        ((Gamma0_pair N).H : Set _) := by
  rw [AntiInvolution.bar_mul, hs_bar]
  rw [DoubleCoset.mem_doubleCoset] at h_prim ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, h_eq⟩ := h_prim
  exact ⟨γ₁, hγ₁, γ₂, hγ₂, by rw [h_eq]; simp only [mul_assoc, hs_central]⟩

private lemma Gamma0_AL_preserves_00 (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : g.val = A.map (Int.cast : ℤ → ℚ))
    (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : ((Gamma0_antiInvolution N).bar g : GL _ ℚ).val = B.map (Int.cast : ℤ → ℚ)) :
    B 0 0 = A 0 0 := by
  have h_bw : ((Gamma0_AL_hom N g).unop : GL _ ℚ).val * (wN N).val =
      (wN N).val * g.val.transpose := by
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
      Units.val_mul, GL_transposeEquiv_val]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel]; simp
  have h00 := congr_fun₂ h_bw 0 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, wN_val, Matrix.diagonal,
    Matrix.transpose_apply] at h00
  exact_mod_cast show (B 0 0 : ℚ) = (A 0 0 : ℚ) from
    (by rw [show (B 0 0 : ℚ) = (B.map (Int.cast : ℤ → ℚ)) 0 0 by
        simp [Matrix.map_apply], ← hB]
        simp only [AntiInvolution.bar, Gamma0_antiInvolution]
        simpa using h00 : (B 0 0 : ℚ) = g.val 0 0).trans
    (by rw [show (A 0 0 : ℚ) = (A.map (Int.cast : ℤ → ℚ)) 0 0 by
        simp [Matrix.map_apply], ← hA] : g.val 0 0 = (A 0 0 : ℚ))

private lemma Gamma0_AL_in_DC_of_gcd_a00_m_coprime (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ) (m : ℕ) (hm_pos : 0 < m)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (hdet_m : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ))
    (ham : Int.gcd (A 0 0) (m : ℤ) = 1) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  obtain ⟨_, _, B, hB, hBN, _⟩ := Gamma0_AL_map_Δ N g hg
  have hbar_det : (↑((Gamma0_antiInvolution N).bar g) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (m : ℚ) := by rw [Gamma0_AL_bar_det, hdet_m]
  rw [DoubleCoset.doubleCoset_eq_of_mem
    (shimura_prop_3_33_gen N m hm_pos g hg A hA hAN hdet_m ham)]
  exact shimura_prop_3_33_gen N m hm_pos ((Gamma0_antiInvolution N).bar g)
    (Gamma0_AL_map_Δ N g hg) B hB hBN hbar_det (Gamma0_AL_preserves_00 N g A hA B hB ▸ ham)

private lemma det_H_elem_eq_one (N : ℕ) [NeZero N] (γ : (Gamma0_pair N).H) :
    (γ : GL (Fin 2) ℚ).val.det = 1 := by
  obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γ.2
  rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast, σ.prop]

private lemma det_conj_H_eq (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ)
    (γL γR : (Gamma0_pair N).H) :
    ((γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ)).val.det = g.val.det := by
  simp only [Units.val_mul, Matrix.det_mul, det_H_elem_eq_one, one_mul, mul_one]

private lemma bar_mem_DC_of_bar_conj_mem (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ)
    (γL γR : (Gamma0_pair N).H)
    (h : ((Gamma0_antiInvolution N).bar ((γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ))) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _)) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  rw [show (Gamma0_antiInvolution N).bar ((γL : GL _ ℚ) * g * (γR : GL _ ℚ)) =
      (Gamma0_antiInvolution N).bar (γR : GL _ ℚ) *
      (Gamma0_antiInvolution N).bar g *
      (Gamma0_antiInvolution N).bar (γL : GL _ ℚ) by
    simp only [AntiInvolution.bar_mul]; group,
    DoubleCoset.mem_doubleCoset] at h
  obtain ⟨δ₁, hδ₁, δ₂, hδ₂, h_eq⟩ := h
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨((Gamma0_antiInvolution N).bar (γR : GL _ ℚ))⁻¹ * δ₁,
    (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem
      (Gamma0_AL_map_H N _ γR.2)) hδ₁,
    δ₂ * ((Gamma0_antiInvolution N).bar (γL : GL _ ℚ))⁻¹,
    (Gamma0_pair N).H.mul_mem hδ₂ ((Gamma0_pair N).H.inv_mem
      (Gamma0_AL_map_H N _ γL.2)),
    by calc (Gamma0_antiInvolution N).bar g
        = ((Gamma0_antiInvolution N).bar (γR : GL _ ℚ))⁻¹ *
          ((Gamma0_antiInvolution N).bar (γR : GL _ ℚ) *
            (Gamma0_antiInvolution N).bar g *
            (Gamma0_antiInvolution N).bar (γL : GL _ ℚ)) *
          ((Gamma0_antiInvolution N).bar (γL : GL _ ℚ))⁻¹ := by group
      _ = _ := by rw [h_eq]; group⟩

private lemma gcd_eq_one_of_factor_split (x : ℤ) (N m b c : ℕ)
    (hbc : m = b * c) (hb_dvd : b ∣ N ^ m)
    (hxN : Int.gcd x N = 1) (hxc : Int.gcd x c = 1) :
    Int.gcd x m = 1 := by
  rw [show (m : ℤ) = ↑b * ↑c by exact_mod_cast hbc]
  exact Int.isCoprime_iff_gcd_eq_one.mp (IsCoprime.mul_right
    (IsCoprime.of_isCoprime_of_dvd_right
      ((Int.isCoprime_iff_gcd_eq_one.mpr hxN).pow_right (n := m))
      (by exact_mod_cast hb_dvd))
    (Int.isCoprime_iff_gcd_eq_one.mpr hxc))

private lemma coprime_div_gcd_npow (N m : ℕ) (hm_pos : 0 < m) :
    Nat.Coprime (m / Nat.gcd m (N ^ m)) N := by
  set b := Nat.gcd m (N ^ m)
  set c := m / b
  have hbc : m = b * c := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m _)).symm
  rw [Nat.coprime_comm]; by_contra h_nc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h_nc
  have hpow : ∀ k, p ^ k ∣ m := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have hpk_Nm : p ^ k ∣ N ^ m :=
        (pow_dvd_pow_of_dvd (Nat.dvd_gcd_iff.mp hpg).1 k).trans
          (Nat.pow_dvd_pow N (by
            by_cases hk : k = 0; · simp [hk]
            · exact le_of_lt (lt_of_lt_of_le
                (Nat.lt_pow_self hp.one_lt) (Nat.le_of_dvd hm_pos ih))))
      rw [hbc]; exact mul_dvd_mul (Nat.dvd_gcd ih hpk_Nm) (Nat.dvd_gcd_iff.mp hpg).2
  exact absurd (Nat.le_of_dvd hm_pos (hpow (m + 1)))
    (not_le.mpr (lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ m))))

private lemma Gamma0_AL_in_DC_primitive (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (hprim : ∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]; exact hg.2.1
  set m := A.det.natAbs
  have hm_pos : 0 < m := Int.natAbs_pos.mpr (ne_of_gt hA_det_pos)
  have hdet_m : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ) := by
    rw [hA, det_intMat_cast]
    exact_mod_cast show A.det = (m : ℤ) from
      (Int.natAbs_of_nonneg (le_of_lt hA_det_pos)).symm
  by_cases h_cop : Int.gcd A.det N = 1
  · exact Gamma0_AL_in_DC_coprime N g hg A hA hAN hAco h_cop
  · set b := Nat.gcd m (N ^ m) with hb_def
    have hb_dvd_Npow : b ∣ N ^ m := Nat.gcd_dvd_right m _
    by_cases hbm : b = m
    · exact Gamma0_AL_in_DC_bad N g hg m hm_pos m (hbm ▸ hb_dvd_Npow) hdet_m
    by_cases ham : Int.gcd (A 0 0) (m : ℤ) = 1
    · exact Gamma0_AL_in_DC_of_gcd_a00_m_coprime N g hg m hm_pos A hA hAN hdet_m ham
    set c := m / b
    have hbc : m = b * c := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m _)).symm
    have hc_pos : 0 < c :=
      Nat.div_pos (Nat.le_of_dvd hm_pos (Nat.gcd_dvd_left m _))
        (Nat.pos_of_ne_zero (by intro h; rw [hb_def, Nat.gcd_eq_zero_iff] at h; omega))
    have hc_cop : Nat.Coprime c N := coprime_div_gcd_npow N m hm_pos
    have hc_dvd : (c : ℤ) ∣ A.det := by
      rw [show A.det = (m : ℤ) from (Int.natAbs_of_nonneg (le_of_lt hA_det_pos)).symm]
      exact_mod_cast show c ∣ m from ⟨b, by linarith [hbc]⟩
    obtain ⟨γL, γR, A', hA', hA'N, hA'Nco, hA'c⟩ :=
      Gamma0_two_sided_coprime_rep_prim N g hg A hA hAN hAco hprim c hc_pos hc_cop hc_dvd
    set g' := (γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ) with hg'_def
    have hg'_dc : g' ∈ DoubleCoset.doubleCoset g
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
      DoubleCoset.mem_doubleCoset.mpr ⟨γL, γL.2, γR, γR.2, rfl⟩
    have hg' : g' ∈ (Gamma0_pair N).Δ :=
      (Gamma0_pair N).Δ.mul_mem
        ((Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).h₀ γL.2) hg)
        ((Gamma0_pair N).h₀ γR.2)
    have h_bar_g'_dc := Gamma0_AL_in_DC_of_gcd_a00_m_coprime N g' hg' m hm_pos A' hA' hA'N
      ((det_conj_H_eq N g γL γR).trans hdet_m)
      (gcd_eq_one_of_factor_split _ N m b c hbc hb_dvd_Npow hA'Nco hA'c)
    apply bar_mem_DC_of_bar_conj_mem N g γL γR
    rw [← hg'_def, ← DoubleCoset.doubleCoset_eq_of_mem hg'_dc]; exact h_bar_g'_dc

private lemma Gamma0_AL_in_DC_of_smul (N : ℕ) [NeZero N] (g g₀ : GL (Fin 2) ℚ) (d : ℚ)
    (hd_pos : 0 < d) (hg_smul : g.val = d • g₀.val)
    (h_bar_g₀ : ((Gamma0_antiInvolution N).bar g₀) ∈
      DoubleCoset.doubleCoset g₀ ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _)) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  set s : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero
    (d • (1 : Matrix (Fin 2) (Fin 2) ℚ))
    (by simp; positivity)
  have hg_eq : g = s * g₀ := by
    apply Units.ext; show g.val = s.val * g₀.val
    rw [hg_smul]; ext i j
    simp only [s, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp
  have hs_central : ∀ h : GL (Fin 2) ℚ, s * h = h * s := by
    intro h; apply Units.ext
    show s.val * h.val = h.val * s.val
    ext i j; simp only [s, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hs_bar : (Gamma0_antiInvolution N).bar s = s := by
    show (Gamma0_AL_hom N s).unop = s
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
    suffices h : s * wN N = wN N * MulOpposite.unop ((GL_transposeEquiv 2) s) by
      rw [← h]; group
    apply Units.ext; ext i j
    simp only [s, GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.coe_mul,
      GL_transposeEquiv_val, wN_val, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.diagonal, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  rw [hg_eq]
  exact Gamma0_AL_scalar_reduce N g₀ s hs_central hs_bar h_bar_g₀

private lemma Gamma0_AL_in_doubleCoset (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset (g : GL (Fin 2) ℚ)
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  obtain ⟨_, _, A, hA, hAN, hAco⟩ := hg
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  set d := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
            (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
  have hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j := by
    intro i j; exact Int.natAbs_dvd_natAbs.mp (by
      fin_cases i <;> fin_cases j <;> simp only [d] <;> (
        exact Nat.dvd_trans (by first
          | exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
          | exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
          | exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
          | exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
          (dvd_refl _)))
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h ↦ by
    have h00 := hd_dvd 0 0; have h01 := hd_dvd 0 1
    have h10 := hd_dvd 1 0; have h11 := hd_dvd 1 1
    simp [h] at h00 h01 h10 h11
    have hdet0 : A.det = 0 := by rw [Matrix.det_fin_two]; simp [h00, h01, h10, h11]
    linarith)
  obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, hA₀_prim⟩ :=
    Gamma0_content_quotient N A hA_det_pos hAN hAco d hd_pos hd_dvd hd_def
  have hA₀_det_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [det_intMat_cast]; exact_mod_cast hA₀_det_pos.ne'
  set g₀ := GeneralLinearGroup.mkOfDetNeZero (A₀.map (Int.cast : ℤ → ℚ)) hA₀_det_ne
  have hA₀_val : (g₀ : Matrix _ _ ℚ) = A₀.map (Int.cast : ℤ → ℚ) := rfl
  have hg₀ : g₀ ∈ (Gamma0_pair N).Δ :=
    ⟨⟨A₀, rfl⟩, by rw [hA₀_val, det_intMat_cast]; exact_mod_cast hA₀_det_pos,
     A₀, rfl, hA₀N, hA₀co⟩
  have hg_scalar : g.val = (d : ℚ) • g₀.val := by
    ext i j; rw [hA, Matrix.smul_apply, hA₀_val, Matrix.map_apply, Matrix.map_apply]
    simp only [smul_eq_mul]; push_cast [hA₀_eq i j]; ring
  exact Gamma0_AL_in_DC_of_smul N g g₀ d (by exact_mod_cast hd_pos) hg_scalar
    (Gamma0_AL_in_DC_primitive N g₀ hg₀ A₀ hA₀_val hA₀N hA₀co hA₀_prim)

private lemma Gamma0_onHeckeCoset_eq (N : ℕ) [NeZero N]
    (D : HeckeCoset (Gamma0_pair N)) :
    (Gamma0_antiInvolution N).onHeckeCoset D = D := by
  rw [(HeckeCoset.mk_rep D).symm, AntiInvolution.onHeckeCoset_mk]
  exact HeckeCoset.eq_mk_of_mem (Gamma0_AL_in_doubleCoset N _ (HeckeCoset.rep D).2)

/-- `𝕋 (Gamma0_pair N) ℤ` is a commutative ring (Shimura Prop 3.8 for `Γ₀(N)`). -/
@[reducible]
noncomputable def instCommRing_Gamma0 (N : ℕ) [NeZero N] :
    CommRing (HeckeRing.𝕋 (Gamma0_pair N) ℤ) :=
  instCommRing_of_antiInvolution (Gamma0_antiInvolution N) (Gamma0_onHeckeCoset_eq N)

attribute [local instance] instCommRing_Gamma0

/-- Shimura Prop 3.8 for `Gamma0_pair N`: the Hecke algebra multiplication is
commutative. -/
theorem Gamma0_pair_HeckeAlgebra_mul_comm (N : ℕ) [NeZero N]
    (T₁ T₂ : HeckeRing.𝕋 (Gamma0_pair N) ℤ) : T₁ * T₂ = T₂ * T₁ :=
  mul_comm T₁ T₂

end HeckeRing.GLn
